module

public import CFSG.Quasithin.EmptyFaithful.A38c16Defs
public import CFSG.Quasithin.Background.Module
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.A38c16.Blocks

open scoped BigOperators

section Indep

variable {W : Type} [CommGroup W]

@[expose] noncomputable def blkFixCard (K Kp : Subgroup (MulAut W)) (M : Subgroup W)
    (F : Subgroup (↥K × ↥Kp)) : ℕ :=
  Nat.card {w : W // w ∈ M ∧ ∀ g ∈ F, ((g.1 : MulAut W) * (g.2 : MulAut W)) w = w}

theorem blkFixCard_eq_of_equivariant {K Kp : Subgroup (MulAut W)} {M N : Subgroup W}
    (hM : IsKSub K M) (hMp : IsKSub Kp M) (f : W → W)
    (hfN : ∀ v ∈ M, f v ∈ N) (hinj : ∀ v ∈ M, ∀ v' ∈ M, f v = f v' → v = v')
    (hsurj : ∀ n ∈ N, ∃ v ∈ M, f v = n)
    (hK : ∀ g ∈ K, ∀ v ∈ M, f (g v) = g (f v)) (hKp : ∀ g ∈ Kp, ∀ v ∈ M, f (g v) = g (f v))
    (F : Subgroup (↥K × ↥Kp)) : blkFixCard K Kp M F = blkFixCard K Kp N F := by
  have key : ∀ (g : ↥K × ↥Kp) (v : W), v ∈ M →
      f (((g.1 : MulAut W) * (g.2 : MulAut W)) v) =
        ((g.1 : MulAut W) * (g.2 : MulAut W)) (f v) := by
    intro g v hv
    rw [MulAut.mul_apply, MulAut.mul_apply, hK _ g.1.2 _ (hMp _ g.2.2 _ hv), hKp _ g.2.2 _ hv]
  unfold blkFixCard
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => (⟨f x.1, hfN _ x.2.1, fun g hg => ?_⟩ :
      {w : W // w ∈ N ∧ ∀ g ∈ F, ((g.1 : MulAut W) * (g.2 : MulAut W)) w = w})) ⟨?_, ?_⟩)
  · rw [← key g _ x.2.1, x.2.2 g hg]
  · intro x y hxy
    apply Subtype.ext
    exact hinj _ x.2.1 _ y.2.1 (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨v, hvM, hv⟩ := hsurj y.1 y.2.1
    refine ⟨⟨v, hvM, fun g hg => ?_⟩, Subtype.ext hv⟩
    have hmem : ((g.1 : MulAut W) * (g.2 : MulAut W)) v ∈ M := by
      rw [MulAut.mul_apply]; exact hM _ g.1.2 _ (hMp _ g.2.2 _ hvM)
    refine hinj _ hmem _ hvM ?_
    rw [key g v hvM, hv]
    exact y.2.2 g hg

@[expose] def Inv2 (K Kp : Subgroup (MulAut W)) (N : Subgroup W) : Prop := IsKSub K N ∧ IsKSub Kp N

theorem inv2_bot {K Kp : Subgroup (MulAut W)} : Inv2 K Kp ⊥ :=
  ⟨fun k _ v hv => by rw [Subgroup.mem_bot] at hv ⊢; rw [hv, map_one],
   fun k _ v hv => by rw [Subgroup.mem_bot] at hv ⊢; rw [hv, map_one]⟩

theorem inv2_sup {K Kp : Subgroup (MulAut W)} {N N' : Subgroup W} (h : Inv2 K Kp N)
    (h' : Inv2 K Kp N') : Inv2 K Kp (N ⊔ N') := by
  constructor
  · intro k hk v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup (h.1 k hk a ha) (h'.1 k hk b hb)
  · intro k hk v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup (h.2 k hk a ha) (h'.2 k hk b hb)

theorem inv2_inf {K Kp : Subgroup (MulAut W)} {N N' : Subgroup W} (h : Inv2 K Kp N)
    (h' : Inv2 K Kp N') : Inv2 K Kp (N ⊓ N') :=
  ⟨fun k hk v hv => ⟨h.1 k hk v hv.1, h'.1 k hk v hv.2⟩,
   fun k hk v hv => ⟨h.2 k hk v hv.1, h'.2 k hk v hv.2⟩⟩

theorem iSupIndep_of_sep {K Kp : Subgroup (MulAut W)} {I : Type*} [Finite I]
    (B : I → Subgroup W) (hne : ∀ i, B i ≠ ⊥) (hK : ∀ i, IsKSub K (B i))
    (hKp : ∀ i, IsKSub Kp (B i))
    (hmin : ∀ i, ∀ N : Subgroup W, N ≤ B i → IsKSub K N → IsKSub Kp N → N = ⊥ ∨ N = B i)
    (hsep : ∀ i j, i ≠ j → ∃ F : Subgroup (↥K × ↥Kp),
      blkFixCard K Kp (B i) F ≠ blkFixCard K Kp (B j) F) :
    iSupIndep B := by
  classical
  have : Fintype I := Fintype.ofFinite I
  have hinv : ∀ J : Finset I, Inv2 K Kp (J.sup B) := by
    intro J
    induction J using Finset.induction_on with
    | empty => simpa using inv2_bot
    | insert a J ha ih => rw [Finset.sup_insert]; exact inv2_sup ⟨hK a, hKp a⟩ ih
  have hsimp : ∀ i (N : Subgroup W), N ≤ B i → Inv2 K Kp N → N ≠ ⊥ → N = B i :=
    fun i N hN hI hN0 => (hmin i N hN hI.1 hI.2).resolve_left hN0
  intro j₀
  have hsupeq : (⨆ (j) (_ : j ≠ j₀), B j) = (Finset.univ.erase j₀).sup B := by
    apply le_antisymm
    · exact iSup₂_le fun j hj => Finset.le_sup (f := B) (by simp [hj])
    · exact Finset.sup_le fun j hj => le_iSup₂ (f := fun j (_ : j ≠ j₀) => B j) j (by simpa using hj)
  rw [hsupeq]
  by_contra hbad
  have hY : B j₀ ⊓ (Finset.univ.erase j₀).sup B ≠ ⊥ := fun h => hbad (disjoint_iff.mpr h)
  have hle : B j₀ ≤ (Finset.univ.erase j₀).sup B := by
    have := hsimp j₀ _ inf_le_left (inv2_inf ⟨hK j₀, hKp j₀⟩ (hinv _)) hY
    exact inf_eq_left.mp this
  obtain ⟨J, ⟨hj₀J, hJle⟩, hJmin⟩ := (InvImage.wf Finset.card wellFounded_lt).has_min
    {J : Finset I | j₀ ∉ J ∧ B j₀ ≤ J.sup B} ⟨Finset.univ.erase j₀, by simp, hle⟩
  have hJne : J.Nonempty := by
    rcases J.eq_empty_or_nonempty with rfl | h
    · exfalso
      simp at hJle
      exact hne j₀ hJle
    · exact h
  obtain ⟨i₀, hi₀⟩ := hJne
  have hji : j₀ ≠ i₀ := fun h => hj₀J (h ▸ hi₀)
  set J' := J.erase i₀ with hJ'
  set P := J'.sup B with hP
  have hnotle : ¬ B j₀ ≤ P := fun h =>
    hJmin J' ⟨fun hmem => hj₀J (Finset.mem_of_mem_erase hmem), h⟩
      (Finset.card_erase_lt_of_mem hi₀)
  have hdecomp : J.sup B = B i₀ ⊔ P := by
    have := Finset.sup_insert (s := J') (b := i₀) (f := B)
    rwa [hJ', Finset.insert_erase hi₀] at this
  have hdis1 : Disjoint (B j₀) P := by
    rw [disjoint_iff]
    by_contra h
    exact hnotle (inf_eq_left.mp (hsimp j₀ _ inf_le_left (inv2_inf ⟨hK j₀, hKp j₀⟩ (hinv J')) h))
  have hdis2 : Disjoint (B i₀) P := by
    rw [disjoint_iff]
    by_contra h
    have h1 : B i₀ ≤ P := inf_eq_left.mp
      (hsimp i₀ _ inf_le_left (inv2_inf ⟨hK i₀, hKp i₀⟩ (hinv J')) h)
    apply hnotle
    calc B j₀ ≤ J.sup B := hJle
      _ = B i₀ ⊔ P := hdecomp
      _ ≤ P := sup_le h1 le_rfl
  have hdec : ∀ b ∈ B j₀, ∃ x ∈ B i₀, ∃ z ∈ P, x * z = b := fun b hb => by
    have : b ∈ B i₀ ⊔ P := hdecomp ▸ hJle hb
    exact Subgroup.mem_sup.mp this
  choose! f hfmem z hzmem hfz using hdec
  have huniq : ∀ x ∈ B i₀, ∀ x' ∈ B i₀, ∀ y ∈ P, ∀ y' ∈ P, x * y = x' * y' → x = x' := by
    intro x hx x' hx' y hy y' hy' h
    have h1 : x'⁻¹ * x ∈ B i₀ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hx') hx
    have h2 : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h]
        _ = y' * y⁻¹ := by group
    have h3 : x'⁻¹ * x ∈ P := h2 ▸ Subgroup.mul_mem _ hy' (Subgroup.inv_mem _ hy)
    have := Subgroup.disjoint_def.mp hdis2 h1 h3
    exact (inv_mul_eq_one.mp this).symm
  have hequi : ∀ g : MulAut W, (∀ v ∈ B j₀, g v ∈ B j₀) → (∀ v ∈ B i₀, g v ∈ B i₀) →
      (∀ v ∈ P, g v ∈ P) → ∀ b ∈ B j₀, f (g b) = g (f b) := by
    intro g h1 h2 h3 b hb
    refine huniq _ (hfmem _ (h1 b hb)) _ (h2 _ (hfmem b hb)) _ (hzmem _ (h1 b hb)) _
      (h3 _ (hzmem b hb)) ?_
    rw [hfz _ (h1 b hb), ← map_mul, hfz b hb]
  have hhom : ∀ b ∈ B j₀, ∀ b' ∈ B j₀, f (b * b') = f b * f b' := by
    intro b hb b' hb'
    have hbb : b * b' ∈ B j₀ := Subgroup.mul_mem _ hb hb'
    refine huniq _ (hfmem _ hbb) _ (Subgroup.mul_mem _ (hfmem b hb) (hfmem b' hb')) _
      (hzmem _ hbb) _ (Subgroup.mul_mem _ (hzmem b hb) (hzmem b' hb')) ?_
    rw [hfz _ hbb]
    calc b * b' = (f b * z b) * (f b' * z b') := by rw [hfz b hb, hfz b' hb']
      _ = (f b * f b') * (z b * z b') := mul_mul_mul_comm _ _ _ _
  have hf1 : f 1 = 1 := by
    have := hhom 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at this
    exact mul_left_cancel (a := f 1) (by rw [mul_one]; exact this.symm)
  have hfinj : ∀ b ∈ B j₀, ∀ b' ∈ B j₀, f b = f b' → b = b' := by
    intro b hb b' hb' h
    have h1 : b * b'⁻¹ ∈ B j₀ := Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hb')
    have h2 : b * b'⁻¹ = z b * (z b')⁻¹ := by
      calc b * b'⁻¹ = (f b * z b) * (f b' * z b')⁻¹ := by rw [hfz b hb, hfz b' hb']
        _ = (f b * z b) * (f b * z b')⁻¹ := by rw [h]
        _ = z b * (z b')⁻¹ := by rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    have h3 : b * b'⁻¹ ∈ P := h2 ▸ Subgroup.mul_mem _ (hzmem b hb) (Subgroup.inv_mem _ (hzmem b' hb'))
    have := Subgroup.disjoint_def.mp hdis1 h1 h3
    exact mul_inv_eq_one.mp this
  let ff : ↥(B j₀) →* W := MonoidHom.mk' (fun b => f b) (fun a b => hhom a a.2 b b.2)
  have hKeq : ∀ g ∈ K, ∀ v ∈ B j₀, f (g v) = g (f v) := fun g hg v hv =>
    hequi g (hK j₀ g hg) (hK i₀ g hg) ((hinv J').1 g hg) v hv
  have hKpeq : ∀ g ∈ Kp, ∀ v ∈ B j₀, f (g v) = g (f v) := fun g hg v hv =>
    hequi g (hKp j₀ g hg) (hKp i₀ g hg) ((hinv J').2 g hg) v hv
  have hIm : ff.range = B i₀ := by
    have hle1 : ff.range ≤ B i₀ := by
      rintro _ ⟨b, rfl⟩
      exact hfmem b b.2
    have hne1 : ff.range ≠ ⊥ := by
      obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hne j₀)
      intro h0
      have : ff b ∈ ff.range := ⟨b, rfl⟩
      rw [h0, Subgroup.mem_bot] at this
      apply hb
      apply Subtype.ext
      exact hfinj _ b.2 _ (Subgroup.one_mem _) (by simpa [ff, hf1] using this)
    refine hsimp i₀ _ hle1 ⟨?_, ?_⟩ hne1
    · rintro g hg _ ⟨b, rfl⟩
      exact ⟨⟨g (b : W), hK j₀ g hg _ b.2⟩, by
        show f (g b) = g (f b)
        exact hKeq g hg b b.2⟩
    · rintro g hg _ ⟨b, rfl⟩
      exact ⟨⟨g (b : W), hKp j₀ g hg _ b.2⟩, by
        show f (g b) = g (f b)
        exact hKpeq g hg b b.2⟩
  have hfsurj : ∀ n ∈ B i₀, ∃ v ∈ B j₀, f v = n := by
    intro n hn
    rw [← hIm] at hn
    obtain ⟨b, hb⟩ := hn
    exact ⟨b, b.2, hb⟩
  obtain ⟨F, hF⟩ := hsep j₀ i₀ hji
  exact hF (blkFixCard_eq_of_equivariant (hK j₀) (hKp j₀) f hfmem hfinj hfsurj hKeq hKpeq F)

end Indep


section Orbit

variable {W : Type} [CommGroup W]

theorem prod_inj_of_iSupIndep {I : Type*} [Fintype I] (B : I → Subgroup W) (hind : iSupIndep B)
    (y y' : I → W) (hy : ∀ i, y i ∈ B i) (hy' : ∀ i, y' i ∈ B i)
    (h : ∏ i, y i = ∏ i, y' i) : y = y' := by
  have h1 : ∀ i ∈ (Finset.univ : Finset I), y i * (y' i)⁻¹ = 1 := by
    refine Subgroup.eq_one_of_noncommProd_eq_one_of_iSupIndep Finset.univ
      (fun i => y i * (y' i)⁻¹) (fun _ _ _ _ _ => Commute.all _ _) B hind
      (fun i _ => Subgroup.mul_mem _ (hy i) (Subgroup.inv_mem _ (hy' i))) ?_
    rw [Finset.noncommProd_eq_prod, Finset.prod_mul_distrib, Finset.prod_inv_distrib, h,
      mul_inv_cancel]
  funext i
  exact mul_inv_eq_one.mp (h1 i (Finset.mem_univ i))

theorem pairwise_commute_of_commGroup {I : Type*} (B : I → Subgroup W) :
    Pairwise fun i j : I => ∀ x y : W, x ∈ B i → y ∈ B j → Commute x y :=
  fun _ _ _ x y _ _ => Commute.all x y

theorem noncommPiCoprod_eq_prod {I : Type*} [Fintype I] (B : I → Subgroup W)
    (u : ∀ i, B i) :
    Subgroup.noncommPiCoprod (pairwise_commute_of_commGroup B) u = ∏ i, (u i : W) := by
  rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]

theorem exists_components {I : Type*} [Fintype I] (B : I → Subgroup W) {x : W}
    (hx : x ∈ ⨆ i, B i) : ∃ y : I → W, (∀ i, y i ∈ B i) ∧ ∏ i, y i = x := by
  have hr : (Subgroup.noncommPiCoprod (pairwise_commute_of_commGroup B)).range = ⨆ i, B i :=
    Subgroup.noncommPiCoprod_range
  rw [← hr] at hx
  obtain ⟨u, hu⟩ := hx
  exact ⟨fun i => (u i : W), fun i => (u i).2, by rw [← hu, noncommPiCoprod_eq_prod]⟩

theorem card_iSup_of_iSupIndep {I : Type*} [Fintype I] (B : I → Subgroup W) (hind : iSupIndep B) :
    Nat.card ↥(⨆ i, B i) = ∏ i, Nat.card ↥(B i) := by
  have hr : (Subgroup.noncommPiCoprod (pairwise_commute_of_commGroup B)).range = ⨆ i, B i :=
    Subgroup.noncommPiCoprod_range
  have hinj : Function.Injective (Subgroup.noncommPiCoprod (pairwise_commute_of_commGroup B)) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  rw [← hr, ← Nat.card_pi]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Orbit


section Orbit2

variable {W : Type} [CommGroup W]

theorem orbit_card_le [Finite W] {I : Type} [AddGroup I] [Fintype I]
    (B : I → Subgroup W) (hind : iSupIndep B)
    (A A₀ : Subgroup (MulAut W)) (d : ↥A → I)
    (hB : ∀ (a : ↥A) (i : I), ∀ v ∈ B i, (a : MulAut W) v ∈ B (i + d a))
    (hA₀ : ∀ a ∈ A₀, ∃ h : a ∈ A, d ⟨a, h⟩ = 0)
    (R : Finset I) (hR : ∀ p : I, ∃ r ∈ R, ∃ a : ↥A, p = r + d a) :
    Nat.card ↥((⨆ i, B i) ⊓ fixV A) ≤
      ∏ r ∈ R, Nat.card {w : W // w ∈ B r ∧ ∀ h ∈ A₀, h w = w} := by
  classical
  have hcomp : ∀ x : ↥((⨆ i, B i) ⊓ fixV A), ∃ y : I → W, (∀ i, y i ∈ B i) ∧ ∏ i, y i = x :=
    fun x => exists_components B (Subgroup.mem_inf.mp x.2).1
  choose y hyB hyprod using hcomp
  have hyeq : ∀ (x : ↥((⨆ i, B i) ⊓ fixV A)) (a : ↥A) (i : I),
      y x (i + d a) = (a : MulAut W) (y x i) := by
    intro x a i
    have hxfix : (a : MulAut W) (x : W) = x := (Subgroup.mem_inf.mp x.2).2 a a.2
    let y' : I → W := fun j => (a : MulAut W) (y x (j - d a))
    have hy'B : ∀ j, y' j ∈ B j := by
      intro j
      have := hB a (j - d a) _ (hyB x (j - d a))
      rwa [sub_add_cancel] at this
    have hprod : ∏ j, y' j = ∏ j, y x j := by
      calc ∏ j, y' j = ∏ i, (a : MulAut W) (y x i) :=
            Fintype.prod_equiv (Equiv.subRight (d a)) _ _ (fun j => rfl)
        _ = (a : MulAut W) (∏ i, y x i) := (map_prod (a : MulAut W) (fun i => y x i) _).symm
        _ = ∏ i, y x i := by rw [hyprod x]; exact hxfix
    have := congrFun (prod_inj_of_iSupIndep B hind y' (y x) hy'B (hyB x) hprod) (i + d a)
    simpa [y'] using this.symm
  have hyfix : ∀ x r, ∀ h ∈ A₀, h (y x r) = y x r := by
    intro x r h hh
    obtain ⟨hA, hd0⟩ := hA₀ h hh
    have := hyeq x ⟨h, hA⟩ r
    rw [hd0, add_zero] at this
    exact this.symm
  let Φ : ↥((⨆ i, B i) ⊓ fixV A) → (r : ↥R) → {w : W // w ∈ B r ∧ ∀ h ∈ A₀, h w = w} :=
    fun x r => ⟨y x r, hyB x r, hyfix x r⟩
  have hΦ : Function.Injective Φ := by
    intro x x' h
    have hr : ∀ r ∈ R, y x r = y x' r := fun r hr => congrArg Subtype.val (congrFun h ⟨r, hr⟩)
    have hyy : y x = y x' := by
      funext p
      obtain ⟨r, hrR, a, rfl⟩ := hR p
      rw [hyeq x a r, hyeq x' a r, hr r hrR]
    apply Subtype.ext
    rw [← hyprod x, ← hyprod x', hyy]
  calc Nat.card ↥((⨆ i, B i) ⊓ fixV A)
      ≤ Nat.card ((r : ↥R) → {w : W // w ∈ B r ∧ ∀ h ∈ A₀, h w = w}) :=
        Nat.card_le_card_of_injective Φ hΦ
    _ = ∏ r : ↥R, Nat.card {w : W // w ∈ B r ∧ ∀ h ∈ A₀, h w = w} := Nat.card_pi
    _ = ∏ r ∈ R, Nat.card {w : W // w ∈ B r ∧ ∀ h ∈ A₀, h w = w} := Finset.prod_coe_sort R (fun r => Nat.card {w : W // w ∈ B r ∧ ∀ h ∈ A₀, h w = w})

theorem card_mul_le_card_mul_inf [Finite W] (X C : Subgroup W) :
    Nat.card ↥X * Nat.card ↥C ≤ Nat.card W * Nat.card ↥(C ⊓ X) := by
  have h1 := Subgroup.relIndex_mul_card C X
  have h2 := Subgroup.relIndex_dvd_index_of_normal C X
  have h3 := Subgroup.card_mul_index C
  have h4 : C.relIndex X ≤ C.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2
  calc Nat.card ↥X * Nat.card ↥C = C.relIndex X * Nat.card ↥(C ⊓ X) * Nat.card ↥C := by rw [h1]
    _ ≤ C.index * Nat.card ↥(C ⊓ X) * Nat.card ↥C := by gcongr
    _ = Nat.card W * Nat.card ↥(C ⊓ X) := by rw [← h3]; ring

end Orbit2

theorem exists_transversal (Pi Q : AddSubgroup (ZMod 2 × ZMod 2)) :
    ∃ R : Finset (ZMod 2 × ZMod 2), (∀ r ∈ R, r ∈ Pi) ∧ ∀ p ∈ Pi, ∃! r, r ∈ R ∧ p - r ∈ Q := by
  classical
  let Q' : AddSubgroup ↥Pi := Q.addSubgroupOf Pi
  have : Fintype (↥Pi ⧸ Q') := Fintype.ofFinite _
  let rep : (↥Pi ⧸ Q') → ZMod 2 × ZMod 2 := fun c => ((Quotient.out c : ↥Pi) : ZMod 2 × ZMod 2)
  have hrep : ∀ c c' : ↥Pi ⧸ Q', rep c - rep c' ∈ Q → c = c' := by
    intro c c' h
    have h1 : (Quotient.out c : ↥Pi) - Quotient.out c' ∈ Q' := h
    have h2 : ((Quotient.out c : ↥Pi) : ↥Pi ⧸ Q') = ((Quotient.out c' : ↥Pi) : ↥Pi ⧸ Q') :=
      QuotientAddGroup.eq_iff_sub_mem.mpr h1
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hr
    exact (Quotient.out c : ↥Pi).2
  · intro p hp
    let c : ↥Pi ⧸ Q' := ((⟨p, hp⟩ : ↥Pi) : ↥Pi ⧸ Q')
    have hpc : p - rep c ∈ Q := by
      have h2 : ((⟨p, hp⟩ : ↥Pi) : ↥Pi ⧸ Q') = ((Quotient.out c : ↥Pi) : ↥Pi ⧸ Q') := by
        rw [QuotientAddGroup.out_eq']
      have h3 : (⟨p, hp⟩ : ↥Pi) - Quotient.out c ∈ Q' := QuotientAddGroup.eq_iff_sub_mem.mp h2
      exact h3
    refine ⟨rep c, ⟨Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, hpc⟩, ?_⟩
    rintro r ⟨hr, hq⟩
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hr
    have : c' = c := hrep c' c (by
      have h5 : rep c' - rep c = (p - rep c) - (p - rep c') := by abel
      rw [h5]
      exact Q.sub_mem hpc hq)
    rw [this]

end CFSG.Quasithin.A38c16.Blocks
