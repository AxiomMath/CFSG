module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISpSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocle
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL34
public import CFSG.Quasithin.Background.E6EighteenB

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial

section Socle

variable {S : Type*} [Group S]

theorem map_fix_eq_inner_inf_centralizer (hZ : Subgroup.center S = ⊥) (α : MulAut S) :
    (Id2519.fixSubgroup α).map (MulAut.conj : S →* MulAut S) =
      inner S ⊓ Subgroup.centralizer ({α} : Set (MulAut S)) := by
  have hι := Id2519.conj_injective_of_center_bot hZ
  have hconj : ∀ y : S, α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := fun y => by
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  ext c
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨y, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyfix : α y = y := hy
    have := hconj y
    rw [hyfix] at this
    calc MulAut.conj y * α = (α * MulAut.conj y * α⁻¹) * α := by rw [this]
      _ = α * MulAut.conj y := by group
  · rintro ⟨⟨y, rfl⟩, hy⟩
    refine ⟨y, ?_, rfl⟩
    have hy' : MulAut.conj y ∈ Subgroup.centralizer ({α} : Set (MulAut S)) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    have h1 : MulAut.conj (α y) = MulAut.conj y := by
      rw [← hconj y]
      calc α * MulAut.conj y * α⁻¹ = (α * MulAut.conj y) * α⁻¹ := rfl
        _ = (MulAut.conj y * α) * α⁻¹ := by rw [hy']
        _ = MulAut.conj y := by group
    exact hι h1

theorem exists_socle_of_fix (hZ : Subgroup.center S = ⊥) {α : MulAut S}
    {B : Subgroup ↥(Id2519.fixSubgroup α)} (hB : CFSG.IsComponent B) :
    ∃ L : Subgroup (MulAut S), L ≤ inner S ∧
      CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({α} : Set (MulAut S))) ∧
      Nonempty (↥L ≃* ↥B) := by
  have hι := Id2519.conj_injective_of_center_bot hZ
  have hNeq := map_fix_eq_inner_inf_centralizer hZ α
  have hLN : (B.map (Id2519.fixSubgroup α).subtype).map (MulAut.conj : S →* MulAut S) ≤
      (Id2519.fixSubgroup α).map (MulAut.conj : S →* MulAut S) :=
    Subgroup.map_mono (Subgroup.map_subtype_le B)
  let ε : ↥(Id2519.fixSubgroup α) ≃*
      ↥((Id2519.fixSubgroup α).map (MulAut.conj : S →* MulAut S)) :=
    (Id2519.fixSubgroup α).equivMapOfInjective _ hι
  have key : B.map ε.toMonoidHom =
      ((B.map (Id2519.fixSubgroup α).subtype).map (MulAut.conj : S →* MulAut S)).subgroupOf
        ((Id2519.fixSubgroup α).map (MulAut.conj : S →* MulAut S)) := by
    ext n
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨(d : S), ⟨d, hd, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨d, hd, rfl⟩, hyn⟩
      refine ⟨d, hd, Subtype.ext ?_⟩
      exact hyn
  have hcomp : CFSG.Assembly.IsComponentOf
      ((B.map (Id2519.fixSubgroup α).subtype).map (MulAut.conj : S →* MulAut S))
      ((Id2519.fixSubgroup α).map (MulAut.conj : S →* MulAut S)) := by
    rw [isComponentOf_iff_isComponent_subgroupOf hLN, ← key]
    exact CFSG.LocalCores.isComponent_map_mulEquiv ε hB
  have hNa : (Id2519.fixSubgroup α).map (MulAut.conj : S →* MulAut S) ≤
      Subgroup.centralizer ({α} : Set (MulAut S)) := hNeq ▸ inf_le_right
  have hNnormal : (((Id2519.fixSubgroup α).map (MulAut.conj : S →* MulAut S)).subgroupOf
      (Subgroup.centralizer ({α} : Set (MulAut S)))).Normal := by
    rw [hNeq, Subgroup.inf_subgroupOf_right]
    have := inner_normal S
    infer_instance
  refine ⟨_, hLN.trans (hNeq ▸ inf_le_left), ⟨hcomp.1.trans hNa,
    Id2519.assemblySubnormal_of_normal hcomp.2.1 hNa hNnormal, hcomp.2.2⟩, ⟨?_⟩⟩
  exact (((B.map (Id2519.fixSubgroup α).subtype).equivMapOfInjective _ hι).symm).trans
    (B.equivMapOfInjective _ (Id2519.fixSubgroup α).subtype_injective).symm

theorem exists_noncomm_inner (hZ : Subgroup.center S = ⊥) {a b : S} (hab : a * b ≠ b * a) :
    ∃ x y : ↥(inner S), x * y ≠ y * x :=
  ⟨Id2519.innerEquiv hZ a, Id2519.innerEquiv hZ b, fun h => hab ((Id2519.innerEquiv hZ).injective
    (by rw [map_mul, map_mul]; exact h))⟩

theorem exists_a7_source {α : MulAut S} {B : Subgroup ↥(Id2519.fixSubgroup α)}
    (hB : IsA7Group ↥B) {L : Subgroup (MulAut S)} (eL : ↥L ≃* ↥B) :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 7)) :=
  (hB.of_mulEquiv eL.symm).1

end Socle

open CFSG.ComponentClassification.OuterAutomorphisms renaming inner → innGrp

theorem selector_data {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {a b : X}
    (hab : a * b ≠ b * a) {α : MulAut X} (hα : α * α = 1) (hne : α ≠ 1) :
    Subgroup.center X = ⊥ ∧ Finite (MulAut X) ∧ orderOf α = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Id2519.center_eq_bot_of_simple_nonab ⟨a, b, hab⟩, ?_, ?_⟩
  · exact Finite.of_injective (fun β : MulAut X => (β : X → X)) fun _ _ h =>
      MulEquiv.ext (congrFun h)
  · exact orderOf_eq_prime (by rw [pow_two]; exact hα) hne

theorem noA7Fix_psl3_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {f : ℕ}
    (hf3 : 3 ≤ f) (hmodel : Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 f) {a b : X}
    (hab : a * b ≠ b * a) :
    NoA7Fix X := by
  intro α hα hne hA
  obtain ⟨B, hBc, hB⟩ := hA
  obtain ⟨hZ, hfin, ha⟩ := selector_data hab hα hne
  obtain ⟨-, F, _, _, hF, ⟨φ0⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨L, hLW, hL, ⟨eL⟩⟩ := exists_socle_of_fix hZ hBc
  let φ : ↥(innGrp X) ≃* LinearFlag.projectiveSL 3 F :=
    (Id2519.innerEquiv hZ).symm.trans (φ0.trans (Id2519.projectiveSLEquivStatedProj 3 F).symm)
  have hWalt : ∀ m : ℕ, 5 ≤ m →
      IsEmpty (↥(innGrp X) ≃* alternatingGroup (Fin m)) := fun m hm =>
    ⟨fun e => (Id2519.projectiveSL_three_not_alternating hf3 hF m hm).false (φ.symm.trans e)⟩
  obtain ⟨ρ, -, -, -, -, -, hemp, -⟩ :=
    faithful_even_higher_linear_socle_small_source_involution_selector
      (Id2519.isSimpleGroup_inner hZ) (exists_noncomm_inner hZ hab)
      (Id2519.centralizer_inner_eq_bot_of_center_bot hZ) ha hLW hL Nat.prime_three
      (by norm_num) le_rfl (Or.inr (Or.inl (exists_a7_source hB eL))) hWalt
      (n := 3) (e := f) le_rfl (by omega) hF φ
  exact hemp.false (exists_a7_source hB eL).some

theorem noA7Fix_psu3_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {f : ℕ}
    (hf2 : 2 ≤ f) (hmodel : Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 2 f) {a b : X}
    (hab : a * b ≠ b * a) :
    NoA7Fix X := by
  intro α hα hne hA
  obtain ⟨B, hBc, hB⟩ := hA
  obtain ⟨hZ, hfin, ha⟩ := selector_data hab hα hne
  obtain ⟨-, F, _, _, hF, ⟨φ0⟩⟩ := hmodel
  obtain ⟨L, hLW, hL, ⟨eL⟩⟩ := exists_socle_of_fix hZ hBc
  have h : UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  let φ : ↥(innGrp X) ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3 :=
    (Id2519.innerEquiv hZ).symm.trans
      (φ0.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by norm_num)).symm)
  have hq : ¬ (3 = 3 ∧ 2 ^ f = 2) := fun ⟨_, h2⟩ => by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  obtain ⟨ρ, -, -, -, -, H₀, C, hC, -, θ, -, ρC, -, -, σ, -, -, Cl, hCl, hlet⟩ :=
    faithful_even_unitary_socle_small_source_involution_selector
      (Id2519.isSimpleGroup_inner hZ) (exists_noncomm_inner hZ hab)
      (Id2519.centralizer_inner_eq_bot_of_center_bot hZ) ha hLW hL Nat.prime_three
      (by norm_num) le_rfl (Or.inr (Or.inl (exists_a7_source hB eL))) h (n := 3) le_rfl hq φ
  obtain ⟨-, -, -, -, -, -, -, -, hrows, -⟩ := hlet
  rcases hrows with ⟨-, -, hp5, -⟩ | ⟨hn4, -⟩ | ⟨hn5, -⟩
  · omega
  · omega
  · omega

theorem noA7Fix_psp4_even
    {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {f : ℕ} (hf2 : 2 ≤ f)
    (hmodel : Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f)
    {a b : X} (hab : a * b ≠ b * a) : NoA7Fix X := by
  intro α hα hne hA
  obtain ⟨B, hBc, hB⟩ := hA
  obtain ⟨hZ, hfin, ha⟩ := selector_data hab hα hne
  obtain ⟨-, F, _, _, hF, ⟨φ0⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨L, hLW, hL, ⟨eL⟩⟩ := exists_socle_of_fix hZ hBc
  let φ : ↥(innGrp X) ≃*
      Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 F) :=
    (Id2519.innerEquiv hZ).symm.trans φ0
  obtain ⟨ρ, -, -, -, -, -, -, -, -, -, -, hemp, -⟩ :=
    faithful_even_symplectic_socle_small_source_involution_selector
      (Id2519.isSimpleGroup_inner hZ) (exists_noncomm_inner hZ hab)
      (Id2519.centralizer_inner_eq_bot_of_center_bot hZ) ha hLW hL Nat.prime_three
      (by norm_num) le_rfl (Or.inr (Or.inl (exists_a7_source hB eL)))
      (r := 2) (e := f) le_rfl (by omega) (by omega) hF φ
  exact hemp.false (exists_a7_source hB eL).some

theorem noA7Fix_psl3_four {X : Type} [Group X] [Finite X]
    (hmodel : Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 2 2) : NoA7Fix X := by
  open CFSG.ComponentClassification.PSL3Four in
  obtain ⟨e0⟩ := nonempty_equiv_of_stated X hmodel
  refine NoA7Fix.of_mulEquiv e0.symm ?_
  intro α hα hne hA
  obtain ⟨B, -, hB⟩ := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he, -⟩ := CFSG.ComponentClassification.PSL3Four.full_automorphism_action
  set τ : CFSG.ComponentClassification.PSL3Four.R := e.symm α with hτdef
  have hτe : e τ = α := e.apply_symm_apply α
  have hτ2 : τ * τ = 1 := by
    apply e.injective
    rw [map_mul, hτe, hα, map_one]
  have hτ1 : τ ≠ 1 := fun h1 => hne (by rw [← hτe, h1, map_one])
  have hord : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ2) hτ1
  set B' : Subgroup (Equiv.Perm (Fin 42)) :=
    ((B.map (Id2519.fixSubgroup α).subtype).map
      (CFSG.ComponentClassification.PSL3Four.S).subtype) with hB'def
  have hB'C : B' ≤ Subgroup.centralizer {(τ : Equiv.Perm (Fin 42))} ⊓
      CFSG.ComponentClassification.PSL3Four.S := by
    rintro _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      ((y : ↥(Id2519.fixSubgroup α)) : CFSG.ComponentClassification.PSL3Four.S).2⟩
    have hfix : α (y : CFSG.ComponentClassification.PSL3Four.S) = y := y.2
    have h := he τ (y : CFSG.ComponentClassification.PSL3Four.S)
    rw [hτe, hfix, Subgroup.coe_inv] at h
    calc (((y : ↥(Id2519.fixSubgroup α)) : CFSG.ComponentClassification.PSL3Four.S) :
          Equiv.Perm (Fin 42)) * τ =
        ((τ : Equiv.Perm (Fin 42)) * (y : CFSG.ComponentClassification.PSL3Four.S) *
          (τ : Equiv.Perm (Fin 42))⁻¹) * τ := by rw [← h]
      _ = τ * (y : CFSG.ComponentClassification.PSL3Four.S) := by group
  have hB'card : Nat.card ↥B' = Nat.card ↥B := by
    rw [hB'def, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hB2520 : 2520 ≤ Nat.card ↥B := Nat.le_of_dvd Nat.card_pos hB.dvd_card
  have hconj := Id2519.Tab.L34.isConj_r₂_of_card hord hB'C (by omega)
  have hC168 := Id2519.Tab.L34.card_cent_of_isConj hconj
  have := Subgroup.card_le_of_le hB'C
  omega

end E6

end CFSG.Quasithin
