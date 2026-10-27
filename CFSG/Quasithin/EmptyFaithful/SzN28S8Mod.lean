module

public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.EmptyFaithful.SzN28S8Grp
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.Quasithin.EmptyFaithful.SzN28H1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

open CFSG.Quasithin.G11 CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

structure S8Data (Γ A : Subgroup (GLV V)) (I I' : Submodule (ZMod 2) V) (x : GLV V) : Prop where
  A_le : A ≤ Γ
  A_normal : ∀ γ ∈ Γ, ∀ a ∈ A, γ * a * γ⁻¹ ∈ A
  A_min : ∀ N : Subgroup (GLV V), N ≤ Γ → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → N ≠ ⊥ → A ≤ N
  card_A : Nat.card A = 20160
  x_mem : x ∈ Γ
  x_sq : x * x = 1
  compl : IsCompl I I'
  I'_eq : I' = I.map (x : V →ₗ[ZMod 2] V)
  rank4 : Module.finrank (ZMod 2) I = 4
  A_inv_I : ∀ a ∈ A, ∀ i ∈ I, a i ∈ I
  faithful_I : ∀ a ∈ A, (∀ i ∈ I, a i = i) → a = 1
  outer : ∀ γ ∈ Γ, γ ∉ A → ∃ a ∈ A, γ = a * x

section Extraction

theorem s8Data_iso_of_concl8 {B : LinearMap.BilinForm (ZMod 2) V} {Γ X : Subgroup (GLV V)}
    (hXΓ : X ≤ Γ) (hXsq : ∀ x ∈ X, x * x = 1) (h8 : G112Concl8S8 B Γ X) :
    ∃ (A : Subgroup (GLV V)) (I I' : Submodule (ZMod 2) V) (x : GLV V), S8Data Γ A I I' x ∧
      x ∈ X ∧ ∀ w ∈ I, ∀ w' ∈ I, B w w' = 0 := by
  classical
  obtain ⟨-, ⟨e⟩, I, hI4, hIiso, hIinv, x, hxX, ⟨v, hvI, hxv⟩, hcompl⟩ := h8
  obtain ⟨A₀, hA₀n, hA₀card, hA₀s, hA₀min, hA₀comp, hA₀idx⟩ := perm8_normal_data e
  set A : Subgroup (GLV V) := A₀.map Γ.subtype with hA
  have hAle : A ≤ Γ := Subgroup.map_subtype_le A₀
  have hxΓ : x ∈ Γ := hXΓ hxX
  have hxsq : x * x = 1 := hXsq x hxX
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxsq
  have hAnorm : ∀ γ ∈ Γ, ∀ a ∈ A, γ * a * γ⁻¹ ∈ A := by
    intro γ hγ a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    exact ⟨⟨γ, hγ⟩ * a₀ * ⟨γ, hγ⟩⁻¹, hA₀n.conj_mem a₀ ha₀ ⟨γ, hγ⟩, rfl⟩
  have hAcard : Nat.card A = 20160 := by
    rw [hA, Subgroup.card_map_of_injective Γ.subtype_injective, hA₀card]
  have hAmin : ∀ N : Subgroup (GLV V), N ≤ Γ → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) →
      N ≠ ⊥ → A ≤ N := by
    intro N hNΓ hNn hN1
    let N₀ : Subgroup ↥Γ := N.subgroupOf Γ
    have hN₀n : N₀.Normal := ⟨fun n hn g => hNn g g.2 n hn⟩
    have hN₀1 : N₀ ≠ ⊥ := by
      intro h
      apply hN1
      rw [eq_bot_iff]
      intro n hn
      have h1 : (⟨n, hNΓ hn⟩ : ↥Γ) ∈ N₀ := hn
      rw [h, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
    have h2 := hA₀min N₀ hN₀n hN₀1
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
    exact h2 ha₀
  have hAcomp : A₀ ≤ genFittingLayer ↥Γ := le_sSup hA₀comp
  have hAI : ∀ a ∈ A, ∀ i ∈ I, a i ∈ I := fun a ha i hi =>
    hIinv a (Subgroup.map_mono hAcomp ha) i hi
  have hxA : x ∉ A := fun hx => hxv (hAI x hx v hvI)
  have hxx : ∀ w : V, x (x w) = w := fun w => by
    have := congrArg (fun f : GLV V => f w) hxsq
    simpa using this
  have hAne : ∀ a ∈ A, a ≠ 1 → ∃ b ∈ A, b ≠ 1 := fun a ha h => ⟨a, ha, h⟩
  have hone : (∀ a ∈ A, ∀ i ∈ I, a i = i) → False := by
    intro hall
    have hA1 : ∀ a ∈ A, a = 1 := by
      intro a ha
      apply LinearEquiv.ext
      intro w
      have hw : w ∈ I ⊔ I.map (x : V →ₗ[ZMod 2] V) := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨i, hi, i', hi', rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨j, hj, rfl⟩ := hi'
      have hxa : x * a * x ∈ A := by
        have h0 := hAnorm x hxΓ a ha
        rwa [hxinv] at h0
      have h1 := hall _ hxa j hj
      rw [map_add, hall a ha i hi]
      congr 1
      have h3 : x (a (x j)) = j := h1
      show a (x j) = x j
      calc a (x j) = x (x (a (x j))) := (hxx _).symm
        _ = x j := by rw [h3]
    have : Nat.card A = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
      rw [hA1 a a.2, hA1 b b.2]
    rw [hAcard] at this
    omega
  have hfaith : ∀ a ∈ A, (∀ i ∈ I, a i = i) → a = 1 := by
    have := hA₀s
    let KI : Subgroup ↥A₀ :=
      { carrier := {b | ∀ i ∈ I, (((b : ↥Γ) : GLV V)) i = i}
        mul_mem' := fun {b c} hb hc i hi => by
          show (((b : ↥Γ) : GLV V)) ((((c : ↥Γ) : GLV V)) i) = i
          rw [hc i hi, hb i hi]
        one_mem' := fun i _ => rfl
        inv_mem' := fun {b} hb i hi => by
          have h1 : (((b : ↥Γ) : GLV V)) i = i := hb i hi
          have h2 : ((((b : ↥Γ) : GLV V))⁻¹ * (((b : ↥Γ) : GLV V))) i = i := by
            rw [inv_mul_cancel]; rfl
          show ((((b : ↥Γ) : GLV V))⁻¹) i = i
          calc ((((b : ↥Γ) : GLV V))⁻¹) i
              = ((((b : ↥Γ) : GLV V))⁻¹) ((((b : ↥Γ) : GLV V)) i) := by rw [h1]
            _ = i := h2 }
    have hKIn : KI.Normal := ⟨fun b hb c i hi => by
      have hcinv : (((c : ↥Γ) : GLV V))⁻¹ ∈ A := ⟨((c⁻¹ : ↥A₀) : ↥Γ), (c⁻¹).2, rfl⟩
      have h1 := hAI _ hcinv i hi
      have h2 := hb _ h1
      show ((((c : ↥Γ) : GLV V)) * (((b : ↥Γ) : GLV V)) * (((c : ↥Γ) : GLV V))⁻¹) i = i
      have h3 : ((((c : ↥Γ) : GLV V)) * (((b : ↥Γ) : GLV V)) * (((c : ↥Γ) : GLV V))⁻¹) i =
          (((c : ↥Γ) : GLV V)) ((((b : ↥Γ) : GLV V)) ((((c : ↥Γ) : GLV V))⁻¹ i)) := rfl
      rw [h3, h2]
      have h4 : ((((c : ↥Γ) : GLV V)) * (((c : ↥Γ) : GLV V))⁻¹) i = i := by
        rw [mul_inv_cancel]; rfl
      exact h4⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top KI with hbot | htop
    · intro a ha hfix
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
      have hb : (⟨a₀, ha₀⟩ : ↥A₀) ∈ KI := fun i hi => hfix i hi
      rw [hbot, Subgroup.mem_bot] at hb
      have : a₀ = 1 := congrArg Subtype.val hb
      rw [this]
      rfl
    · exfalso
      refine hone fun a ha i hi => ?_
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
      have hb : (⟨a₀, ha₀⟩ : ↥A₀) ∈ KI := by rw [htop]; trivial
      exact hb i hi
  have houter : ∀ γ ∈ Γ, γ ∉ A → ∃ a ∈ A, γ = a * x := by
    intro γ hγ hγA
    have hg : (⟨γ, hγ⟩ : ↥Γ) ∉ A₀ := fun h => hγA ⟨_, h, rfl⟩
    have hh : (⟨x, hxΓ⟩ : ↥Γ) ∉ A₀ := fun h => hxA ⟨_, h, rfl⟩
    have h1 := hA₀idx _ _ hg hh
    refine ⟨Γ.subtype (⟨γ, hγ⟩ * ⟨x, hxΓ⟩⁻¹), ⟨_, h1, rfl⟩, ?_⟩
    show γ = γ * x⁻¹ * x
    group
  exact ⟨A, I, I.map (x : V →ₗ[ZMod 2] V), x,
    ⟨hAle, hAnorm, hAmin, hAcard, hxΓ, hxsq, hcompl, rfl, hI4, hAI, hfaith, houter⟩, hxX, hIiso⟩

theorem s8Data_of_concl8 {B : LinearMap.BilinForm (ZMod 2) V} {Γ X : Subgroup (GLV V)}
    (hXΓ : X ≤ Γ) (hXsq : ∀ x ∈ X, x * x = 1) (h8 : G112Concl8S8 B Γ X) :
    ∃ (A : Subgroup (GLV V)) (I I' : Submodule (ZMod 2) V) (x : GLV V), S8Data Γ A I I' x := by
  obtain ⟨A, I, I', x, hd, -, -⟩ := s8Data_iso_of_concl8 hXΓ hXsq h8
  exact ⟨A, I, I', x, hd⟩

end Extraction

theorem card_linearEquiv_four {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (hW : Module.finrank (ZMod 2) W = 4) : Nat.card (W ≃ₗ[ZMod 2] W) = 20160 := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 4) (ZMod 2) W := Module.finBasisOfFinrankEq (ZMod 2) W hW
  let e : GL (Fin 4) (ZMod 2) ≃* (W ≃ₗ[ZMod 2] W) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W)
  rw [← Nat.card_congr e.toEquiv]
  exact CFSG.GH74.Exceptional.card_GL_four_two

theorem exists_linearEquiv_moves {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (hW : 2 ≤ Module.finrank (ZMod 2) W) {i : W} (hi : i ≠ 0) :
    ∃ g : W ≃ₗ[ZMod 2] W, g i ≠ i := by
  have : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod 2) W, f i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hi ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) i).1 hall)
  have hpos : 0 < Module.finrank (ZMod 2) (LinearMap.ker f) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
      calc Module.finrank (ZMod 2) (LinearMap.range f) ≤ Module.finrank (ZMod 2) (ZMod 2) :=
            Submodule.finrank_le _
        _ = 1 := Module.finrank_self _
    omega
  obtain ⟨⟨v, hv⟩, hv0'⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hv0 : v ≠ 0 := fun h => hv0' (Subtype.ext h)
  have hfv : f v = 0 := hv
  refine ⟨LinearEquiv.transvection hfv, ?_⟩
  rw [LinearEquiv.transvection.apply]
  intro h
  have h1 : f i • v = 0 := by simpa using h
  have h2 : f i = 1 := by
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact key _ hf
  rw [h2, one_smul] at h1
  exact hv0 h1

namespace S8Data

variable {Γ A : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V} {x : GLV V}
  (d : S8Data Γ A I I' x)

include d in
theorem xx_apply (w : V) : x (x w) = w := by
  have := congrArg (fun f : GLV V => f w) d.x_sq
  simpa using this

include d in
theorem x_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right d.x_sq

include d in
theorem mem_I'_iff (w : V) : w ∈ I' ↔ x w ∈ I := by
  rw [d.I'_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    show x (x j) ∈ I
    rw [d.xx_apply]
    exact hj
  · intro h
    exact ⟨x w, h, d.xx_apply w⟩

include d in
theorem A_inv_I' : ∀ a ∈ A, ∀ i ∈ I', a i ∈ I' := by
  intro a ha i hi
  have hxa : x * a * x ∈ A := by
    have h0 := d.A_normal x d.x_mem a ha
    rwa [d.x_inv] at h0
  have h1 : x (a i) ∈ I := by
    have h2 := d.A_inv_I _ hxa (x i) ((d.mem_I'_iff i).1 hi)
    have h3 : (x * a * x) (x i) = x (a i) := by
      show x (a (x (x i))) = x (a i)
      rw [d.xx_apply]
    rwa [h3] at h2
  exact (d.mem_I'_iff _).2 h1

include d in
theorem faithful_I' : ∀ a ∈ A, (∀ i ∈ I', a i = i) → a = 1 := by
  intro a ha hfix
  have hxa : x * a * x ∈ A := by
    have h0 := d.A_normal x d.x_mem a ha
    rwa [d.x_inv] at h0
  have h1 : x * a * x = 1 := by
    apply d.faithful_I _ hxa
    intro j hj
    have hj' : x j ∈ I' := by
      rw [d.I'_eq]
      exact ⟨j, hj, rfl⟩
    show x (a (x j)) = j
    rw [hfix _ hj', d.xx_apply]
  calc a = (x * x) * a * (x * x) := by rw [d.x_sq]; group
    _ = x * (x * a * x) * x := by group
    _ = 1 := by rw [h1, mul_one, d.x_sq]

include d in
theorem rank4' : Module.finrank (ZMod 2) I' = 4 := by
  rw [d.I'_eq, LinearEquiv.finrank_map_eq x, d.rank4]

include d in
theorem exists_three : ∀ γ ∈ Γ, γ ≠ 1 → ∃ a b : V, γ a ≠ a ∧ γ b ≠ b ∧ γ a - a ≠ γ b - b := by
  intro γ hγ hγ1
  by_cases hγA : γ ∈ A
  · obtain ⟨i, hi, hγi⟩ : ∃ i ∈ I, γ i ≠ i := by
      by_contra hall
      push Not at hall
      exact hγ1 (d.faithful_I γ hγA hall)
    obtain ⟨i', hi', hγi'⟩ : ∃ i' ∈ I', γ i' ≠ i' := by
      by_contra hall
      push Not at hall
      exact hγ1 (d.faithful_I' γ hγA hall)
    refine ⟨i, i', hγi, hγi', fun h => hγi ?_⟩
    have h1 : γ i - i ∈ I := I.sub_mem (d.A_inv_I γ hγA i hi) hi
    have h2 : γ i' - i' ∈ I' := I'.sub_mem (d.A_inv_I' γ hγA i' hi') hi'
    have h3 : γ i - i ∈ I ⊓ I' := ⟨h1, h ▸ h2⟩
    rw [d.compl.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at h3
    exact h3
  · obtain ⟨a₀, ha₀, rfl⟩ := d.outer γ hγ hγA
    have hmap : ∀ j ∈ I, (a₀ * x) j ∈ I' := by
      intro j hj
      show a₀ (x j) ∈ I'
      exact d.A_inv_I' a₀ ha₀ (x j) (by rw [d.I'_eq]; exact ⟨j, hj, rfl⟩)
    have hinj : ∀ j ∈ I, (a₀ * x) j = j → j = 0 := by
      intro j hj h
      have h1 : j ∈ I ⊓ I' := ⟨hj, h ▸ hmap j hj⟩
      rwa [d.compl.inf_eq_bot, Submodule.mem_bot] at h1
    have : Module.Finite (ZMod 2) I := Module.finite_of_finrank_pos (by rw [d.rank4]; omega)
    let b := Module.finBasisOfFinrankEq (ZMod 2) I d.rank4
    have hb0 : ((b 0 : I) : V) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    have hb1 : ((b 1 : I) : V) ≠ 0 := fun h => b.ne_zero 1 (Subtype.ext h)
    have hb01 : ((b 0 : I) : V) ≠ ((b 1 : I) : V) := fun h =>
      absurd (b.injective (Subtype.ext h)) (by decide)
    refine ⟨(b 0 : I), (b 1 : I), fun h => hb0 (hinj _ (b 0).2 h), fun h => hb1 (hinj _ (b 1).2 h),
      fun h => ?_⟩
    have h' : (a₀ * x) (((b 0 : I) : V) - ((b 1 : I) : V)) = ((b 0 : I) : V) - ((b 1 : I) : V) := by
      rw [map_sub]
      have := sub_eq_sub_iff_sub_eq_sub.1 h
      exact this
    exact hb01 (sub_eq_zero.1 (hinj _ (I.sub_mem (b 0).2 (b 1).2) h'))

include d in
theorem surj_of_faithful {J : Submodule (ZMod 2) V} (hJ4 : Module.finrank (ZMod 2) J = 4)
    (hJinv : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J) (hfaith : ∀ a ∈ A, (∀ j ∈ J, a j = j) → a = 1) :
    ∀ g : J ≃ₗ[ZMod 2] J, ∃ a ∈ A, ∀ j : J, a (j : V) = ((g j : J) : V) := by
  classical
  have hcard := card_linearEquiv_four hJ4
  have hfin : Finite (J ≃ₗ[ZMod 2] J) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let f : ↥A → (J ≃ₗ[ZMod 2] J) := fun a =>
    LinearEquiv.ofLinearMap ((a : GLV V).toLinearMap.restrict (hJinv a a.2))
      (((a⁻¹ : ↥A) : GLV V).toLinearMap.restrict (hJinv _ (a⁻¹).2))
      (LinearMap.ext fun j => Subtype.ext (by
        have := congrArg (fun g : GLV V => g (j : V)) (mul_inv_cancel (a : GLV V))
        exact this))
      (LinearMap.ext fun j => Subtype.ext (by
        have := congrArg (fun g : GLV V => g (j : V)) (inv_mul_cancel (a : GLV V))
        exact this))
  have hf : ∀ a j, ((f a j : J) : V) = (a : GLV V) (j : V) := fun a j => rfl
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : ∀ j ∈ J, (a : GLV V) j = (b : GLV V) j := by
      intro j hj
      have := congrArg (fun g : J ≃ₗ[ZMod 2] J => ((g ⟨j, hj⟩ : J) : V)) hab
      simpa [hf] using this
    have h1 : ((a⁻¹ * b : ↥A) : GLV V) = 1 := by
      apply hfaith _ (a⁻¹ * b).2
      intro j hj
      show (a : GLV V)⁻¹ ((b : GLV V) j) = j
      rw [← hab' j hj]
      have := congrArg (fun g : GLV V => g j) (inv_mul_cancel (a : GLV V))
      exact this
    have h2 : a⁻¹ * b = 1 := Subtype.ext h1
    exact inv_mul_eq_one.1 h2
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hcard, d.card_A])
  intro g
  obtain ⟨a, ha⟩ := hbij.2 g
  exact ⟨a, a.2, fun j => by rw [← ha]; rfl⟩

end S8Data

structure TwoNat (A : Subgroup (GLV V)) (J J' : Submodule (ZMod 2) V) : Prop where
  compl : IsCompl J J'
  inv : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J
  inv' : ∀ a ∈ A, ∀ j ∈ J', a j ∈ J'
  rank : Module.finrank (ZMod 2) J = 4
  rank' : Module.finrank (ZMod 2) J' = 4
  faithful : ∀ a ∈ A, (∀ j ∈ J, a j = j) → a = 1
  faithful' : ∀ a ∈ A, (∀ j ∈ J', a j = j) → a = 1
  surj : ∀ g : J ≃ₗ[ZMod 2] J, ∃ a ∈ A, ∀ j : J, a (j : V) = ((g j : J) : V)
  surj' : ∀ g : J' ≃ₗ[ZMod 2] J', ∃ a ∈ A, ∀ j : J', a (j : V) = ((g j : J') : V)

theorem S8Data.twoNat {Γ A : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V} {x : GLV V}
    (d : S8Data Γ A I I' x) : TwoNat A I I' where
  compl := d.compl
  inv := d.A_inv_I
  inv' := d.A_inv_I'
  rank := d.rank4
  rank' := d.rank4'
  faithful := d.faithful_I
  faithful' := d.faithful_I'
  surj := d.surj_of_faithful d.rank4 d.A_inv_I d.faithful_I
  surj' := d.surj_of_faithful d.rank4' d.A_inv_I' d.faithful_I'

namespace TwoNat

variable {A : Subgroup (GLV V)} {J J' : Submodule (ZMod 2) V} (t : TwoNat A J J')

include t in
theorem symm : TwoNat A J' J where
  compl := t.compl.symm
  inv := t.inv'
  inv' := t.inv
  rank := t.rank'
  rank' := t.rank
  faithful := t.faithful'
  faithful' := t.faithful
  surj := t.surj'
  surj' := t.surj

include t in
theorem fix_comp {a : GLV V} (ha : a ∈ A) {j j' : V} (hj : j ∈ J) (hj' : j' ∈ J')
    (h : a (j + j') = j + j') : a j = j ∧ a j' = j' := by
  rw [map_add] at h
  have h1 : a j - j ∈ J := J.sub_mem (t.inv a ha j hj) hj
  have h2 : a j - j = -(a j' - j') := by
    have : a j + a j' = j + j' := h
    calc a j - j = (a j + a j') - (j + j') - (a j' - j') := by abel
      _ = -(a j' - j') := by rw [this]; abel
  have h3 : a j - j ∈ J ⊓ J' := ⟨h1, by
    rw [h2]; exact J'.neg_mem (J'.sub_mem (t.inv' a ha j' hj') hj')⟩
  rw [t.compl.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at h3
  refine ⟨h3, ?_⟩
  rw [h3] at h
  have : a j' = j' := by
    have h4 : j + a j' = j + j' := h
    exact add_left_cancel h4
  exact this

include t in
theorem fix_eq_zero_J {j : V} (hj : j ∈ J) (hfix : ∀ a ∈ A, a j = j) : j = 0 := by
  by_contra hj0
  have hne : (⟨j, hj⟩ : J) ≠ 0 := fun h => hj0 (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_linearEquiv_moves (by rw [t.rank]; omega) hne
  obtain ⟨a, ha, hag⟩ := t.surj g
  apply hg
  apply Subtype.ext
  have := hag ⟨j, hj⟩
  rw [← this]
  exact hfix a ha

include t in
theorem fix_eq_zero (u : V) (hu : ∀ a ∈ A, a u = u) : u = 0 := by
  have hu' : u ∈ J ⊔ J' := by rw [t.compl.sup_eq_top]; trivial
  obtain ⟨j, hj, j', hj', rfl⟩ := Submodule.mem_sup.1 hu'
  have h1 : ∀ a ∈ A, a j = j ∧ a j' = j' := fun a ha => t.fix_comp ha hj hj' (hu a ha)
  have h2 : j = 0 := t.fix_eq_zero_J hj fun a ha => (h1 a ha).1
  have h3 : j' = 0 := t.symm.fix_eq_zero_J hj' fun a ha => (h1 a ha).2
  rw [h2, h3, add_zero]

include t in
theorem coh_comp {K : Type*} [Group K] (σ : K →* GLV V)
    (hσ : ∀ k, σ k ∈ A) (hs : ∀ a ∈ A, ∃ k, σ k = a) (δ : K → V)
    (hδ : ∀ k l, δ (k * l) = δ k + σ k (δ l)) (hker : ∀ k, σ k = 1 → δ k = 0) :
    ∃ n : J, ∀ k, ((Submodule.projectionOnto J J' t.compl (δ k) : J) : V) =
      σ k (n : V) - (n : V) := by
  set p := Submodule.projectionOnto J J' t.compl with hp
  set q := Submodule.projectionOnto J' J t.compl.symm with hq
  have hp_add : ∀ w, (p w : V) + (q w : V) = w :=
    Submodule.projection_add_projection_eq_self t.compl
  have hpJ : ∀ j : J, p (j : V) = j := Submodule.projectionOnto_apply_left t.compl
  have hpJ' : ∀ j : J', p (j : V) = 0 := Submodule.projectionOnto_apply_right t.compl
  let θ : K →* Module.End (ZMod 2) J :=
    { toFun := fun k => ((σ k : GLV V) : V →ₗ[ZMod 2] V).restrict (t.inv (σ k) (hσ k))
      map_one' := LinearMap.ext fun j => Subtype.ext (by simp)
      map_mul' := fun k l => LinearMap.ext fun j => Subtype.ext (by simp) }
  have hθ_app : ∀ k (j : J), ((θ k j : J) : V) = σ k (j : V) := fun k j => rfl
  have hp_σ : ∀ k w, p (σ k w) = θ k (p w) := by
    intro k w
    have h1 : σ k w = ((θ k (p w) : J) : V) +
        ((⟨σ k (q w : V), t.inv' (σ k) (hσ k) _ (q w).2⟩ : J') : V) := by
      rw [hθ_app]
      show σ k w = σ k (p w : V) + σ k (q w : V)
      rw [← map_add, hp_add]
    rw [h1, map_add, hpJ, hpJ', add_zero]
  have hcoc : ∀ k l, p (δ (k * l)) = p (δ k) + θ k (p (δ l)) := by
    intro k l
    rw [hδ, map_add, hp_σ]
  have hker' : ∀ k, θ k = 1 → p (δ k) = 0 := by
    intro k hk
    have h1 : σ k = 1 := by
      apply t.faithful _ (hσ k)
      intro j hj
      have h2 := congrArg (fun f : Module.End (ZMod 2) J => ((f ⟨j, hj⟩ : J) : V)) hk
      simp only [Module.End.one_apply] at h2
      exact (hθ_app k ⟨j, hj⟩).symm.trans h2
    rw [hker k h1, map_zero]
  have hθs : ∀ g : J ≃ₗ[ZMod 2] J, ∃ k, θ k = (g : J →ₗ[ZMod 2] J) := by
    intro g
    obtain ⟨a, ha, hag⟩ := t.surj g
    obtain ⟨k, hk⟩ := hs a ha
    refine ⟨k, LinearMap.ext fun j => Subtype.ext ?_⟩
    rw [hθ_app, hk]
    exact hag j
  obtain ⟨n, hn⟩ := h1_four t.rank θ hθs (fun k => p (δ k)) hcoc hker'
  refine ⟨n, fun k => ?_⟩
  have := congrArg (fun z : J => (z : V)) (hn k)
  simpa [hθ_app] using this

include t in
theorem coh {K : Type*} [Group K] (σ : K →* GLV V)
    (hσ : ∀ k, σ k ∈ A) (hs : ∀ a ∈ A, ∃ k, σ k = a) (δ : K → V)
    (hδ : ∀ k l, δ (k * l) = δ k + σ k (δ l)) (hker : ∀ k, σ k = 1 → δ k = 0) :
    ∃ n : V, ∀ k, δ k = σ k n - n := by
  obtain ⟨n, hn⟩ := t.coh_comp σ hσ hs δ hδ hker
  obtain ⟨n', hn'⟩ := t.symm.coh_comp σ hσ hs δ hδ hker
  refine ⟨(n : V) + (n' : V), fun k => ?_⟩
  have h1 : ((Submodule.projectionOnto J J' t.compl (δ k) : J) : V) +
      ((Submodule.projectionOnto J' J t.compl.symm (δ k) : J') : V) = δ k :=
    Submodule.projection_add_projection_eq_self t.compl (δ k)
  have h2 := hn k
  have h3 := hn' k
  rw [← h1, h2]
  rw [h3]
  rw [map_add]
  abel

end TwoNat

end CFSG.Quasithin.SzN28
