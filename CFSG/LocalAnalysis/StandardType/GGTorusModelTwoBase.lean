module

public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem map_add_of_conj {p k : ℕ} {G : Type} [Group G]
    (T : Multiplicative (Fin k → ZMod p) →* G) (hT : Function.Injective T)
    {w : G} {g : (Fin k → ZMod p) → Fin k → ZMod p}
    (hw : ∀ t, w * T (Multiplicative.ofAdd t) * w⁻¹ = T (Multiplicative.ofAdd (g t))) :
    ∀ a b, g (a + b) = g a + g b := by
  have hT' : Function.Injective fun t : Fin k → ZMod p => T (Multiplicative.ofAdd t) :=
    fun a b h => Multiplicative.ofAdd.injective (hT h)
  intro a b
  apply hT'
  calc T (Multiplicative.ofAdd (g (a + b)))
      = w * T (Multiplicative.ofAdd (a + b)) * w⁻¹ := (hw (a + b)).symm
    _ = w * (T (Multiplicative.ofAdd a) * T (Multiplicative.ofAdd b)) * w⁻¹ := by
          rw [ofAdd_add, map_mul]
    _ = (w * T (Multiplicative.ofAdd a) * w⁻¹) *
          (w * T (Multiplicative.ofAdd b) * w⁻¹) := by group
    _ = T (Multiplicative.ofAdd (g a)) * T (Multiplicative.ofAdd (g b)) := by rw [hw a, hw b]
    _ = T (Multiplicative.ofAdd (g a + g b)) := by rw [← map_mul, ← ofAdd_add]

private def mulAutOfAddFun {A : Type} [AddGroup A] (g : A → A)
    (hg : ∀ a b, g (a + b) = g a + g b) (hinv : ∀ a, g (g a) = a) :
    MulAut (Multiplicative A) where
  toFun x := Multiplicative.ofAdd (g (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (g (Multiplicative.toAdd x))
  left_inv x := by
    dsimp only
    rw [toAdd_ofAdd, hinv, ofAdd_toAdd]
  right_inv x := by
    dsimp only
    rw [toAdd_ofAdd, hinv, ofAdd_toAdd]
  map_mul' x y := by
    rw [toAdd_mul, hg, ofAdd_add]

private theorem mulAutOfAddFun_apply {A : Type} [AddGroup A] (g : A → A)
    (hg : ∀ a b, g (a + b) = g a + g b) (hinv : ∀ a, g (g a) = a) (x : Multiplicative A) :
    mulAutOfAddFun g hg hinv x = Multiplicative.ofAdd (g (Multiplicative.toAdd x)) := rfl

private theorem mulAutOfAddFun_ofAdd {A : Type} [AddGroup A] (g : A → A)
    (hg : ∀ a b, g (a + b) = g a + g b) (hinv : ∀ a, g (g a) = a) (a : A) :
    mulAutOfAddFun g hg hinv (Multiplicative.ofAdd a) = Multiplicative.ofAdd (g a) := rfl

private theorem mulAutOfAddFun_mul_self {A : Type} [AddGroup A] (g : A → A)
    (hg : ∀ a b, g (a + b) = g a + g b) (hinv : ∀ a, g (g a) = a) :
    mulAutOfAddFun g hg hinv * mulAutOfAddFun g hg hinv = 1 := by
  ext x
  obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective x
  rw [MulAut.mul_apply, mulAutOfAddFun_ofAdd, mulAutOfAddFun_ofAdd, hinv, MulAut.one_apply]

private theorem mulAut_congr_mul_self {M N : Type} [Group M] [Group N] (e : M ≃* N)
    {g : MulAut M} (h : g * g = 1) : MulAut.congr e g * MulAut.congr e g = 1 := by
  have hm : MulAut.congr e (g * g) = MulAut.congr e g * MulAut.congr e g :=
    map_mul (MulAut.congr e) g g
  rw [← hm, h]
  exact (MulAut.congr e).map_one

private theorem card_fix_mulAut_congr {M N : Type} [Group M] [Group N] (e : M ≃* N)
    (g : MulAut M) :
    Nat.card {x : N // MulAut.congr e g x = x} = Nat.card {y : M // g y = y} := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun x => ?_)
  change (e (g (e.symm x)) = x) ↔ (g (e.symm x) = e.symm x)
  constructor
  · intro h
    have h' := congrArg (fun z => e.symm z) h
    simpa using h'
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

private theorem card_fix_mulAutOfAddFun {p k : ℕ}
    (ε : Multiplicative (Fin k → ZMod p) ≃* (Fin k → Multiplicative (ZMod p)))
    {g : (Fin k → ZMod p) → Fin k → ZMod p}
    (hg : ∀ a b, g (a + b) = g a + g b) (hinv : ∀ x, g (g x) = x) :
    Nat.card {x : Fin k → Multiplicative (ZMod p) //
        MulAut.congr ε (mulAutOfAddFun g hg hinv) x = x}
      = Nat.card {t : Fin k → ZMod p // g t = t} := by
  rw [card_fix_mulAut_congr ε (mulAutOfAddFun g hg hinv)]
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun y => ?_)
  have hFy : mulAutOfAddFun g hg hinv y
      = Multiplicative.ofAdd (g (Multiplicative.toAdd y)) := mulAutOfAddFun_apply g hg hinv y
  have hy : y = Multiplicative.ofAdd (Multiplicative.toAdd y) := (ofAdd_toAdd y).symm
  rw [hFy, hy]
  simp only [toAdd_ofAdd]
  constructor
  · exact fun h => Multiplicative.ofAdd.injective h
  · intro h
    rw [h]

private theorem card_fix_conj {A : Type} (u : A ≃ A) (g : A → A) :
    Nat.card {t : A // u (g (u.symm t)) = t} = Nat.card {s : A // g s = s} := by
  refine Nat.card_congr (Equiv.subtypeEquiv u.symm fun t => ?_)
  constructor
  · intro h
    have h' := congrArg (fun z => u.symm z) h
    simpa using h'
  · intro h
    rw [h, Equiv.apply_symm_apply]

private theorem congr_mulAutOfAddFun_apply {p k : ℕ}
    (ε : Multiplicative (Fin k → ZMod p) ≃* (Fin k → Multiplicative (ZMod p)))
    {g : (Fin k → ZMod p) → Fin k → ZMod p}
    (hg : ∀ a b, g (a + b) = g a + g b) (hinv : ∀ a, g (g a) = a)
    (x : Fin k → Multiplicative (ZMod p)) :
    MulAut.congr ε (mulAutOfAddFun g hg hinv) x
      = ε (Multiplicative.ofAdd (g (Multiplicative.toAdd (ε.symm x)))) := by
  change ε (mulAutOfAddFun g hg hinv (ε.symm x)) = _
  rw [mulAutOfAddFun_apply]

private theorem image_fix_mulAutOfAddFun {p k : ℕ} {G : Type} [Group G]
    (T : Multiplicative (Fin k → ZMod p) →* G)
    (ε : Multiplicative (Fin k → ZMod p) ≃* (Fin k → Multiplicative (ZMod p)))
    {g : (Fin k → ZMod p) → Fin k → ZMod p}
    (hg : ∀ a b, g (a + b) = g a + g b) (hinv : ∀ a, g (g a) = a) :
    (T.comp ε.symm.toMonoidHom) ''
        {x : Fin k → Multiplicative (ZMod p) |
          MulAut.congr ε (mulAutOfAddFun g hg hinv) x = x}
      = SuSplitRootGen.torusFix T g := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : mulAutOfAddFun g hg hinv (ε.symm x) = ε.symm x := by
      have h := congrArg (fun z => ε.symm z) hx
      rw [congr_mulAutOfAddFun_apply, MulEquiv.symm_apply_apply] at h
      exact h
    have h2 : g (Multiplicative.toAdd (ε.symm x)) = Multiplicative.toAdd (ε.symm x) := by
      have h := congrArg Multiplicative.toAdd h1
      rw [mulAutOfAddFun_apply, toAdd_ofAdd] at h
      exact h
    refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd (ε.symm x)), ?_, ?_⟩
    · simpa using h2
    · simp [MonoidHom.comp_apply]
  · rintro ⟨t, ht, rfl⟩
    have ht' : g (Multiplicative.toAdd t) = Multiplicative.toAdd t := ht
    refine ⟨ε t, ?_, ?_⟩
    · show MulAut.congr ε (mulAutOfAddFun g hg hinv) (ε t) = ε t
      rw [congr_mulAutOfAddFun_apply, MulEquiv.symm_apply_apply, ht', ofAdd_toAdd]
    · simp [MonoidHom.comp_apply]

private theorem torusFix_conj {p k : ℕ} {G : Type} [Group G]
    (T : Multiplicative (Fin k → ZMod p) →* G) (n : G)
    (u : (Fin k → ZMod p) ≃ (Fin k → ZMod p))
    (hn : ∀ t, n * T (Multiplicative.ofAdd t) * n⁻¹ = T (Multiplicative.ofAdd (u t)))
    (g : (Fin k → ZMod p) → Fin k → ZMod p) :
    SuSplitRootGen.torusFix T (fun t => u (g (u.symm t)))
      = (MulAut.conj n) '' SuSplitRootGen.torusFix T g := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : g (u.symm (Multiplicative.toAdd t)) = u.symm (Multiplicative.toAdd t) := by
      have h := congrArg (fun z => u.symm z) ht
      simpa using h
    refine ⟨T (Multiplicative.ofAdd (u.symm (Multiplicative.toAdd t))),
      ⟨Multiplicative.ofAdd (u.symm (Multiplicative.toAdd t)), by simpa using ht', rfl⟩, ?_⟩
    rw [MulAut.conj_apply, hn (u.symm (Multiplicative.toAdd t)), Equiv.apply_symm_apply]
    simp
  · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    have ht' : g (Multiplicative.toAdd t) = Multiplicative.toAdd t := ht
    refine ⟨Multiplicative.ofAdd (u (Multiplicative.toAdd t)), ?_, ?_⟩
    · simpa using congrArg u ht'
    · rw [MulAut.conj_apply,
        show T t = T (Multiplicative.ofAdd (Multiplicative.toAdd t)) from by rw [ofAdd_toAdd],
        ← hn (Multiplicative.toAdd t)]

private theorem conj_mul_conj_of_add {p k : ℕ} {G : Type} [Group G]
    (T : Multiplicative (Fin k → ZMod p) →* G) (n : G)
    (u : (Fin k → ZMod p) ≃ (Fin k → ZMod p))
    (hn : ∀ t, n * T (Multiplicative.ofAdd t) * n⁻¹ = T (Multiplicative.ofAdd (u t)))
    {w : G} {g : (Fin k → ZMod p) → Fin k → ZMod p}
    (hw : ∀ t, w * T (Multiplicative.ofAdd t) * w⁻¹ = T (Multiplicative.ofAdd (g t)))
    (t : Fin k → ZMod p) :
    (n * w * n⁻¹) * T (Multiplicative.ofAdd t) * (n * w * n⁻¹)⁻¹
      = T (Multiplicative.ofAdd (u (g (u.symm t)))) := by
  have hkey : n⁻¹ * T (Multiplicative.ofAdd t) * n
      = T (Multiplicative.ofAdd (u.symm t)) := by
    have h := hn (u.symm t)
    rw [Equiv.apply_symm_apply] at h
    calc n⁻¹ * T (Multiplicative.ofAdd t) * n
        = n⁻¹ * (n * T (Multiplicative.ofAdd (u.symm t)) * n⁻¹) * n := by rw [h]
      _ = T (Multiplicative.ofAdd (u.symm t)) := by group
  have hwj := hw (u.symm t)
  have hnn := hn (g (u.symm t))
  calc (n * w * n⁻¹) * T (Multiplicative.ofAdd t) * (n * w * n⁻¹)⁻¹
      = n * (w * (n⁻¹ * T (Multiplicative.ofAdd t) * n) * w⁻¹) * n⁻¹ := by group
    _ = n * (w * T (Multiplicative.ofAdd (u.symm t)) * w⁻¹) * n⁻¹ := by rw [hkey]
    _ = n * T (Multiplicative.ofAdd (g (u.symm t))) * n⁻¹ := by rw [hwj]
    _ = T (Multiplicative.ofAdd (u (g (u.symm t)))) := hnn

private theorem isComponentOf_map_conj_torusFix {p k : ℕ} {G : Type} [Group G]
    (T : Multiplicative (Fin k → ZMod p) →* G) (n : G)
    (u : (Fin k → ZMod p) ≃ (Fin k → ZMod p))
    (hn : ∀ t, n * T (Multiplicative.ofAdd t) * n⁻¹ = T (Multiplicative.ofAdd (u t)))
    (g : (Fin k → ZMod p) → Fin k → ZMod p) {S : Subgroup G}
    (hS : IsComponentOf S (Subgroup.centralizer (SuSplitRootGen.torusFix T g))) :
    IsComponentOf (S.map (MulAut.conj n).toMonoidHom)
      (Subgroup.centralizer
        (SuSplitRootGen.torusFix T (fun t => u (g (u.symm t))))) := by
  have hmap : IsComponentOf (S.map (MulAut.conj n).toMonoidHom)
      ((Subgroup.centralizer (SuSplitRootGen.torusFix T g)).map
        (MulAut.conj n).toMonoidHom) :=
    isComponentOf_map_mulEquiv (MulAut.conj n) hS
  have hfix : SuSplitRootGen.torusFix T (fun t => u (g (u.symm t)))
      = (MulAut.conj n) '' SuSplitRootGen.torusFix T g :=
    torusFix_conj T n u hn g
  have hcent : (Subgroup.centralizer (SuSplitRootGen.torusFix T g)).map
        (MulAut.conj n).toMonoidHom
      = Subgroup.centralizer ((MulAut.conj n) '' SuSplitRootGen.torusFix T g) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      obtain ⟨c, hc, rfl⟩ := hz
      have h := congrArg (MulAut.conj n) (Subgroup.mem_centralizer_iff.mp hx c hc)
      simpa [map_mul] using h
    · intro hy
      refine ⟨n⁻¹ * y * n, ?_, ?_⟩
      · refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
        have h : (MulAut.conj n) c * y = y * (MulAut.conj n) c :=
          Subgroup.mem_centralizer_iff.mp hy ((MulAut.conj n) c) ⟨c, hc, rfl⟩
        have hc' : (MulAut.conj n) c = n * c * n⁻¹ := MulAut.conj_apply n c
        rw [hc'] at h
        calc c * (n⁻¹ * y * n)
            = n⁻¹ * (n * c * n⁻¹ * y) * n := by group
          _ = n⁻¹ * (y * (n * c * n⁻¹)) * n := by rw [h]
          _ = (n⁻¹ * y * n) * c := by group
      · change MulAut.conj n (n⁻¹ * y * n) = y
        rw [MulAut.conj_apply]
        group
  rw [hcent, ← hfix] at hmap
  exact hmap

private theorem injective_double_mulAut {p k : ℕ} {ι : Type}
    (ε : Multiplicative (Fin k → ZMod p) ≃* (Fin k → Multiplicative (ZMod p)))
    (f : ι → (Fin k → ZMod p) → Fin k → ZMod p)
    (u : (Fin k → ZMod p) ≃ (Fin k → ZMod p))
    (g : ι ⊕ ι → (Fin k → ZMod p) → Fin k → ZMod p)
    (hgl : ∀ i, g (Sum.inl i) = f i)
    (hgr : ∀ j, g (Sum.inr j) = fun t => u (f j (u.symm t)))
    (hadd : ∀ a, ∀ x y, g a (x + y) = g a x + g a y)
    (hinv : ∀ a, ∀ x, g a (g a x) = x)
    (hf : Function.Injective f)
    (hfu : ∀ i j, f i ≠ fun t => u (f j (u.symm t))) :
    Function.Injective fun a =>
      MulAut.congr ε (mulAutOfAddFun (g a) (hadd a) (hinv a)) := by
  intro a b hab
  have hgeq : g a = g b := by
    funext t
    have h := congrArg (fun m : MulAut (Fin k → Multiplicative (ZMod p)) =>
      m (ε (Multiplicative.ofAdd t))) hab
    rw [congr_mulAutOfAddFun_apply, congr_mulAutOfAddFun_apply] at h
    simp only [MulEquiv.symm_apply_apply, toAdd_ofAdd] at h
    have h2 := congrArg (fun z => Multiplicative.toAdd (ε.symm z)) h
    simpa using h2
  rcases a with i | i <;> rcases b with j | j
  · rw [hgl i, hgl j] at hgeq
    exact congrArg Sum.inl (hf hgeq)
  · rw [hgl i, hgr j] at hgeq
    exact absurd hgeq (hfu i j)
  · rw [hgr i, hgl j] at hgeq
    exact absurd hgeq.symm (hfu j i)
  · rw [hgr i, hgr j] at hgeq
    have hfij : f i = f j := by
      funext t
      have h := congrFun hgeq (u t)
      have h' := congrArg (fun z => u.symm z) h
      simpa using h'
    exact congrArg Sum.inr (hf hfij)

private theorem iSup_ne_double {ι : Type} {G : Type} [Group G]
    (S : ι → Subgroup G) (S' : ι ⊕ ι → Subgroup G) (e : MulAut G)
    (hS'inl : ∀ i, S' (Sum.inl i) = S i)
    (hS'inr : ∀ j, S' (Sum.inr j) = (S j).map e.toMonoidHom)
    (hgen : (⨆ i, S i) = ⊤) :
    ∀ a : ι ⊕ ι, (⨆ (b : ι ⊕ ι) (_ : b ≠ a), S' b) = ⊤ := by
  intro a
  rcases a with j | j
  · refine le_antisymm le_top ?_
    have htop : (⨆ c : ι, (S c).map e.toMonoidHom) = ⊤ := by
      rw [← Subgroup.map_iSup, hgen,
        Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    rw [← htop]
    refine iSup_le fun c => ?_
    exact le_iSup_of_le (Sum.inr c) (le_iSup_of_le (by simp) (le_of_eq (hS'inr c).symm))
  · refine le_antisymm le_top ?_
    rw [← hgen]
    refine iSup_le fun c => ?_
    exact le_iSup_of_le (Sum.inl c) (le_iSup_of_le (by simp) (le_of_eq (hS'inl c).symm))

theorem ggTorusModelAt_of_twoBase {p k : ℕ} {G : Type} [Group G] {E : Subgroup G}
    (T : Multiplicative (Fin k → ZMod p) →* G) (hT : Function.Injective T) (hTE : T.range = E)
    {ι : Type} [Nonempty ι] (w : ι → G) (f : ι → (Fin k → ZMod p) → Fin k → ZMod p)
    (S : ι → Subgroup G)
    (hw : ∀ i t, w i * T (Multiplicative.ofAdd t) * (w i)⁻¹ = T (Multiplicative.ofAdd (f i t)))
    (hinv : ∀ i t, f i (f i t) = t)
    (hfix : ∀ i, Nat.card {t // f i t = t} * p = p ^ k)
    (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i)
      (Subgroup.centralizer (SuSplitRootGen.torusFix T (f i))))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hgen : (⨆ i, S i) = ⊤)
    (n : G) (u : (Fin k → ZMod p) ≃ (Fin k → ZMod p))
    (hn : ∀ t, n * T (Multiplicative.ofAdd t) * n⁻¹ = T (Multiplicative.ofAdd (u t)))
    (hf : Function.Injective f)
    (hfu : ∀ i j, f i ≠ fun t => u (f j (u.symm t))) :
    GGTorusModelAt p E := by
  classical
  have hadd : ∀ i, ∀ a b, f i (a + b) = f i a + f i b :=
    fun i => map_add_of_conj T hT (hw i)
  have haddu : ∀ a b, u (a + b) = u a + u b := map_add_of_conj T hT hn
  have haddsu : ∀ a b, u.symm (a + b) = u.symm a + u.symm b := by
    intro a b
    apply u.injective
    rw [Equiv.apply_symm_apply, haddu, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let g : ι ⊕ ι → (Fin k → ZMod p) → Fin k → ZMod p := fun a =>
    match a with
    | Sum.inl i => f i
    | Sum.inr j => fun t => u (f j (u.symm t))
  have hgadd : ∀ a, ∀ x y, g a (x + y) = g a x + g a y := by
    intro a
    rcases a with i | j
    · exact hadd i
    · intro x y
      dsimp only [g]
      rw [haddsu, hadd j, haddu]
  have hginv : ∀ a, ∀ x, g a (g a x) = x := by
    intro a
    rcases a with i | j
    · exact hinv i
    · intro x
      dsimp only [g]
      rw [Equiv.symm_apply_apply, hinv j, Equiv.apply_symm_apply]
  let ε : Multiplicative (Fin k → ZMod p) ≃* (Fin k → Multiplicative (ZMod p)) :=
    MulEquiv.piMultiplicative (fun _ => ZMod p)
  let τ : (Fin k → Multiplicative (ZMod p)) →* G := T.comp ε.symm.toMonoidHom
  let s : ι ⊕ ι → MulAut (Fin k → Multiplicative (ZMod p)) := fun a =>
    MulAut.congr ε (mulAutOfAddFun (g a) (hgadd a) (hginv a))
  let S' : ι ⊕ ι → Subgroup G := fun a =>
    match a with
    | Sum.inl i => S i
    | Sum.inr j => (S j).map (MulAut.conj n).toMonoidHom
  let w' : ι ⊕ ι → G := fun a =>
    match a with
    | Sum.inl i => w i
    | Sum.inr j => n * w j * n⁻¹
  have hw'inl : ∀ i, w' (Sum.inl i) = w i := fun i => rfl
  have hw'inr : ∀ j, w' (Sum.inr j) = n * w j * n⁻¹ := fun j => rfl
  have hS'inl : ∀ i, S' (Sum.inl i) = S i := fun i => rfl
  have hS'inr : ∀ j, S' (Sum.inr j) = (S j).map (MulAut.conj n).toMonoidHom := fun j => rfl
  have hcardAenv : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
    rw [← Nat.card_congr ε.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin k → ZMod p) ≃ _),
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
  have hsapp : ∀ a (x : Fin k → Multiplicative (ZMod p)),
      s a x = ε (Multiplicative.ofAdd (g a (Multiplicative.toAdd (ε.symm x)))) :=
    fun a x => congr_mulAutOfAddFun_apply ε (hgadd a) (hginv a) x
  have hconj : ∀ a (t : Fin k → ZMod p),
      w' a * τ (ε (Multiplicative.ofAdd t)) * (w' a)⁻¹
        = τ (ε (Multiplicative.ofAdd (g a t))) := by
    intro a t
    rcases a with i | j
    · rw [hw'inl i]
      dsimp only [τ]
      simp only [MonoidHom.comp_apply, MulEquiv.symm_apply_apply]
      exact hw i t
    · rw [hw'inr j]
      dsimp only [τ]
      simp only [MonoidHom.comp_apply, MulEquiv.symm_apply_apply]
      exact conj_mul_conj_of_add T n u hn (hw j) t
  refine ⟨k, τ, ι ⊕ ι, w', s, S', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨Sum.inl (Classical.arbitrary ι)⟩
  · intro x y h
    exact ε.symm.injective (hT h)
  · rw [show τ.range = T.range from ?_, hTE]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ε.symm.surjective,
      ← MonoidHom.range_eq_map]
  · intro a x
    have hx : x = ε (Multiplicative.ofAdd (Multiplicative.toAdd (ε.symm x))) := by
      rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]
    rw [hx, hsapp a]
    dsimp only [τ]
    simp only [MulEquiv.symm_apply_apply, toAdd_ofAdd, MonoidHom.comp_apply]
    exact hconj a (Multiplicative.toAdd (ε.symm x))
  · intro a
    rw [show s a = MulAut.congr ε (mulAutOfAddFun (g a) (hgadd a) (hginv a)) from rfl]
    exact mulAut_congr_mul_self ε (g := mulAutOfAddFun (g a) (hgadd a) (hginv a))
      (mulAutOfAddFun_mul_self (g a) (hgadd a) (hginv a))
  · intro a
    rw [show s a = MulAut.congr ε (mulAutOfAddFun (g a) (hgadd a) (hginv a)) from rfl,
      card_fix_mulAutOfAddFun (g := g a) ε (hgadd a) (hginv a), hcardAenv]
    rcases a with i | j
    · rw [show g (Sum.inl i) = f i from rfl]
      exact hfix i
    · rw [show g (Sum.inr j) = (fun t => u (f j (u.symm t))) from rfl,
        card_fix_conj u (f j)]
      exact hfix j
  · exact injective_double_mulAut ε f u g (fun i => rfl) (fun j => rfl) hgadd hginv hf hfu
  · intro a
    rcases a with i | j
    · rw [hS'inl i, hw'inl i]
      exact hwS i
    · rw [hS'inr j, hw'inr j]
      have h := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom (hwS j)
      simpa [MulAut.conj_apply] using h
  · intro a
    rcases a with i | j
    · have hset : τ '' {x : Fin k → Multiplicative (ZMod p) | s (Sum.inl i) x = x}
          = SuSplitRootGen.torusFix T (f i) := by
        rw [show τ = T.comp ε.symm.toMonoidHom from rfl]
        exact image_fix_mulAutOfAddFun (g := g (Sum.inl i)) T ε
          (hgadd (Sum.inl i)) (hginv (Sum.inl i))
      rw [hset]
      exact hcomp i
    · have hset : τ '' {x : Fin k → Multiplicative (ZMod p) | s (Sum.inr j) x = x}
          = SuSplitRootGen.torusFix T (fun t => u (f j (u.symm t))) := by
        rw [show τ = T.comp ε.symm.toMonoidHom from rfl]
        exact image_fix_mulAutOfAddFun (g := g (Sum.inr j)) T ε
          (hgadd (Sum.inr j)) (hginv (Sum.inr j))
      rw [hS'inr j, hset]
      exact isComponentOf_map_conj_torusFix T n u hn (f j) (hcomp j)
  · intro a
    rcases a with i | j
    · rw [hS'inl i]
      exact hdvd i
    · rw [hS'inr j, Subgroup.card_map_of_injective (MulAut.conj n).injective]
      exact hdvd j
  · exact iSup_ne_double S S' (MulAut.conj n) hS'inl hS'inr hgen

end CFSG.StandardType

end
