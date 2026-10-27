module

public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem fixed_card_even {α : Type*} [Finite α] [DecidableEq α] (σ : Equiv.Perm α) (e : ℕ)
    (hσ : σ ^ (2 ^ e) = 1) (hα : Even (Nat.card α)) :
    Even (Nat.card (Function.fixedPoints σ)) := by
  haveI : Fintype α := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : Function.End α := ⇑σ
  have hf : f ^ 2 ^ e = 1 := by
    have h1 : (⇑(σ ^ 2 ^ e) : α → α) = ⇑(1 : Equiv.Perm α) := by rw [hσ]
    rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_one] at h1
    exact h1
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := e) hf
  have h3 : Nat.card (Function.fixedPoints σ) = Fintype.card ↑(Function.fixedPoints f) :=
    Nat.card_eq_fintype_card
  have hα' : Fintype.card α ≡ 0 [MOD 2] := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp hα)
  rw [h3]
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp (h2.symm.trans hα'))

theorem exists_fixed_of_card_two {V : Type*} [Group V] (Y : Subgroup V) (hY : Nat.card Y = 2)
    (S : Set (MulAut V)) (hinv : ∀ θ ∈ S, ∀ y ∈ Y, θ y ∈ Y) :
    ∃ y ∈ Y, y ≠ 1 ∧ ∀ θ ∈ S, θ y = y := by
  obtain ⟨y, hy1, huniq⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hY
  refine ⟨(y : V), y.2, fun h => hy1 (Subtype.ext h), fun θ hθ => ?_⟩
  have h1 : (⟨θ (y : V), hinv θ hθ y y.2⟩ : Y) ≠ 1 := by
    intro h
    apply hy1
    have h2 : θ (y : V) = 1 := congrArg Subtype.val h
    exact Subtype.ext ((MulEquiv.map_eq_one_iff θ).mp h2)
  exact congrArg Subtype.val (huniq _ h1)

theorem exists_fixed_of_commuting_two_element {V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV8 : Nat.card V = 8) (hXV : X ≤ normalizer (V : Set G)) {z : G}
    (hzV : z ∈ normalizer (V : Set G)) (e : ℕ)
    (hze : ∀ v ∈ V, z ^ (2 ^ e) * v = v * z ^ (2 ^ e))
    (hz1 : ∃ v ∈ V, z * v ≠ v * z)
    (hzX : ∀ x ∈ X, ∀ v ∈ V, z * (x * v * x⁻¹) * z⁻¹ = x * (z * v * z⁻¹) * x⁻¹) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ x ∈ X, x * v * x⁻¹ = v := by
  classical
  letI : CommGroup ↥V := { (inferInstance : Group ↥V) with
    mul_comm := fun a b => Subtype.ext (hV.comm a.2 b.2) }
  let σ : MulAut ↥V := V.normalizerMonoidHom ⟨z, hzV⟩
  have hσ : ∀ v : ↥V, ((σ v : ↥V) : G) = z * v * z⁻¹ := by intro v; simp [σ]
  let φ : ↥V →* ↥V := MonoidHom.mk' (fun v => v⁻¹ * σ v) (by
    intro a b
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _)
  have hφ : ∀ v : ↥V, φ v = v⁻¹ * σ v := fun v => rfl
  have hker : ∀ v : ↥V, v ∈ φ.ker ↔ σ v = v := by
    intro v
    rw [MonoidHom.mem_ker, hφ, inv_mul_eq_one]
    exact eq_comm
  let ρ : ∀ x : G, x ∈ X → MulAut ↥V := fun x hx => V.normalizerMonoidHom ⟨x, hXV hx⟩
  have hρ : ∀ (x : G) (hx : x ∈ X) (v : ↥V), ((ρ x hx v : ↥V) : G) = x * v * x⁻¹ := by
    intro x hx v; simp [ρ, hx]
  have hcomm : ∀ (x : G) (hx : x ∈ X) (v : ↥V), σ (ρ x hx v) = ρ x hx (σ v) := by
    intro x hx v
    apply Subtype.ext
    rw [hσ, hρ x hx, hρ x hx, hσ]
    exact hzX x hx v v.2
  have hσe : σ ^ (2 ^ e) = 1 := by
    have h1 : V.normalizerMonoidHom ((⟨z, hzV⟩ : normalizer (V : Set G)) ^ (2 ^ e)) =
        σ ^ (2 ^ e) := map_pow _ _ _
    rw [← h1]
    ext w
    simp
    exact mul_inv_eq_iff_eq_mul.mpr (hze w w.2)
  have hσperm : (MulAut.toPerm ↥V σ) ^ (2 ^ e) = 1 := by
    rw [← map_pow, hσe, map_one]
  have hfix : Nat.card φ.ker = Nat.card (Function.fixedPoints (MulAut.toPerm ↥V σ)) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => by rw [hker]; exact Iff.rfl))
  have hCeven : Even (Nat.card φ.ker) := by
    rw [hfix]
    exact fixed_card_even _ e hσperm (by rw [hV8]; decide)
  have hprod := Subgroup.card_ker_mul_card_range φ
  rw [hV8] at hprod
  have hR1 : Nat.card φ.range ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    obtain ⟨v, hv, hne⟩ := hz1
    have hmem : φ ⟨v, hv⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [h1, Subgroup.mem_bot, hφ, inv_mul_eq_one] at hmem
    apply hne
    have h2 := congrArg Subtype.val hmem
    rw [hσ] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2.symm
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.card φ.ker := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Nat.card φ.range := ⟨_, rfl⟩
  rw [← hc, ← hr] at hprod
  rw [← hc] at hCeven
  rw [← hr] at hR1
  have h24 : (c = 2 ∧ r = 4) ∨ (c = 4 ∧ r = 2) := by
    obtain ⟨m, hm⟩ := hCeven
    have hc8 : c ≤ 8 := Nat.le_of_dvd (by norm_num) ⟨r, hprod.symm⟩
    interval_cases c <;> omega
  let S : Set (MulAut ↥V) := {θ | ∃ (x : G) (hx : x ∈ X), θ = ρ x hx}
  have hfin : ∀ Y : Subgroup ↥V, Nat.card Y = 2 → (∀ θ ∈ S, ∀ y ∈ Y, θ y ∈ Y) →
      ∃ v ∈ V, v ≠ 1 ∧ ∀ x ∈ X, x * v * x⁻¹ = v := by
    intro Y hY hinv
    obtain ⟨y, -, hy1, hyfix⟩ := exists_fixed_of_card_two Y hY S hinv
    refine ⟨(y : G), y.2, fun h => hy1 (Subtype.ext h), fun x hx => ?_⟩
    have := hyfix (ρ x hx) ⟨x, hx, rfl⟩
    rw [← hρ x hx y, this]
  rcases h24 with ⟨hc2, -⟩ | ⟨-, hr2⟩
  · refine hfin φ.ker (by rw [← hc, hc2]) ?_
    rintro θ ⟨x, hx, rfl⟩ y hy
    rw [hker] at hy ⊢
    rw [hcomm x hx y, hy]
  · refine hfin φ.range (by rw [← hr, hr2]) ?_
    rintro θ ⟨x, hx, rfl⟩ _ ⟨v, rfl⟩
    refine ⟨ρ x hx v, ?_⟩
    rw [hφ, hφ, map_mul, map_inv, hcomm x hx v]

theorem exists_fixed_of_card_seven_of_index_le_three {X Y : Type*} [Group X] [Finite X]
    [MulAction X Y] [Finite Y] (hY : Nat.card Y = 7) (P : Subgroup X) (hP : P.index ≤ 3)
    (hPfix : ∀ p ∈ P, ∀ y : Y, p • y = y) : ∃ y : Y, ∀ x : X, x • y = y := by
  classical
  by_contra hno
  push Not at hno
  have hdvd : ∀ y : Y, (MulAction.stabilizer X y).index ∣ P.index := fun y =>
    Subgroup.index_dvd_of_le fun p hp => (MulAction.mem_stabilizer_iff).mpr (hPfix p hp y)
  have hne1 : ∀ y : Y, (MulAction.stabilizer X y).index ≠ 1 := by
    intro y h1
    rw [Subgroup.index_eq_one] at h1
    obtain ⟨x, hx⟩ := hno y
    exact hx ((MulAction.mem_stabilizer_iff).mp (h1 ▸ Subgroup.mem_top x))
  have hPpos : 0 < P.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hd : ∀ y : Y, (MulAction.stabilizer X y).index = P.index := by
    intro y
    have h1 := hdvd y
    have h2 := hne1 y
    have h3 : (MulAction.stabilizer X y).index ≤ P.index := Nat.le_of_dvd hPpos h1
    have h4 : 0 < (MulAction.stabilizer X y).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    interval_cases hP' : P.index <;> interval_cases hs : (MulAction.stabilizer X y).index <;> omega
  haveI : Fintype Y := Fintype.ofFinite Y
  haveI : Fintype (MulAction.orbitRel.Quotient X Y) := Fintype.ofFinite _
  have hsum : Nat.card Y = ∑ ω : MulAction.orbitRel.Quotient X Y,
      (MulAction.stabilizer X (Quotient.out ω)).index := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer X Y), Nat.card_sigma]
    rfl
  have h7 : 7 = Fintype.card (MulAction.orbitRel.Quotient X Y) * P.index := by
    rw [← hY, hsum]
    simp [hd]
  have hd7 : P.index ∣ 7 := ⟨_, by rw [mul_comm]; exact h7⟩
  have hP2 : 2 ≤ P.index := by
    by_contra hlt
    have : P.index = 1 := by omega
    obtain ⟨⟨y⟩, -⟩ := Nat.card_pos_iff.mp (by omega : 0 < Nat.card Y)
    exact hne1 y (by rw [hd y, this])
  interval_cases hP' : P.index <;> omega

theorem exists_fixed_of_relIndex_le_three {V X P : Subgroup G} (hV8 : Nat.card V = 8)
    (hXV : X ≤ normalizer (V : Set G)) (hP : P.relIndex X ≤ 3)
    (hPV : ∀ p ∈ P, ∀ v ∈ V, p * v = v * p) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ x ∈ X, x * v * x⁻¹ = v := by
  classical
  let ρ : ↥X →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hXV)
  have hρ : ∀ (x : ↥X) (v : ↥V), ((ρ x v : ↥V) : G) = (x : G) * v * (x : G)⁻¹ := by
    intro x v
    simp [ρ]
  letI : MulAction ↥X ↥V := MulAction.compHom ↥V ρ
  have hsmul : ∀ (x : ↥X) (v : ↥V), ((x • v : ↥V) : G) = (x : G) * v * (x : G)⁻¹ := hρ
  let S : SubMulAction ↥X ↥V :=
    { carrier := {v | v ≠ 1}
      smul_mem' := by
        intro x v hv h1
        apply hv
        change ρ x v = 1 at h1
        exact (MulEquiv.map_eq_one_iff (ρ x)).mp h1 }
  have hS : Nat.card S = 7 := by
    haveI : Fintype ↥V := Fintype.ofFinite _
    have h1 : Nat.card ↥S = Fintype.card {v : ↥V // ¬ v = 1} := by
      rw [← Nat.card_eq_fintype_card]; rfl
    rw [h1, Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hV8]
  obtain ⟨y, hy⟩ := exists_fixed_of_card_seven_of_index_le_three (X := ↥X) (Y := ↥S) hS
    (P.subgroupOf X) hP (by
      intro p hp y
      apply Subtype.ext
      apply Subtype.ext
      have h1 : ((p • (y : ↥V) : ↥V) : G) = (p : G) * (y : G) * (p : G)⁻¹ := hsmul p y
      have h2 : (p : G) ∈ P := hp
      have h3 := hPV p h2 y y.1.2
      change ((p • (y : ↥V) : ↥V) : G) = ((y : ↥V) : G)
      rw [h1, h3, mul_inv_cancel_right])
  refine ⟨((y : ↥V) : G), (y : ↥V).2, fun h => y.2 (Subtype.ext h), fun x hx => ?_⟩
  have h1 := congrArg (fun w : ↥S => (((w : ↥V)) : G)) (hy ⟨x, hx⟩)
  have h2 : ((((⟨x, hx⟩ : ↥X) • y : ↥S) : ↥V) : G) = x * ((y : ↥V) : G) * x⁻¹ := hsmul ⟨x, hx⟩ y
  simpa only [h2] using h1

end CFSG.LocalAnalysis.WeakClosure81

end
