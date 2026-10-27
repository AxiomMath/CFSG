module

public import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def diagElt (s : Fˣ) : SL(2, F) :=
  ⟨!![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

theorem diagElt_inv (s : Fˣ) : (diagElt s)⁻¹ = diagElt s⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagElt, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagElt_conj_upperElt (s : Fˣ) (t : F) :
    diagElt s * upperElt F t * (diagElt s)⁻¹ = upperElt F ((s : F) ^ 2 * t) := by
  rw [diagElt_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagElt, upperElt, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem diagElt_mem_normalizer (s : Fˣ) :
    diagElt s ∈ Subgroup.normalizer (upperUnipotent F : Set SL(2, F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [mem_upperUnipotent_iff, mem_upperUnipotent_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, diagElt_conj_upperElt s t⟩
  · rintro ⟨t, ht⟩
    refine ⟨((s⁻¹ : Fˣ) : F) ^ 2 * t, ?_⟩
    have h1 : g = (diagElt s)⁻¹ * upperElt F t * diagElt s := by
      rw [← ht]
      group
    rw [h1, ← diagElt_conj_upperElt s⁻¹ t, diagElt_inv, diagElt_inv, inv_inv]

variable [CharP F 2]

theorem upperElt_mul_self (t : F) : upperElt F t * upperElt F t = 1 := by
  rw [upperElt_mul, CharTwo.add_self_eq_zero, upperElt_zero]

theorem isElemAbelian_upperUnipotent : CFSG.Assembly.IsElemAbelian 2 (upperUnipotent F) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := (mem_upperUnipotent_iff F).mp x.2
    obtain ⟨t, ht⟩ := (mem_upperUnipotent_iff F).mp y.2
    simp only [Subgroup.coe_mul, hs, ht, upperElt_mul, add_comm]
  · obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff F).mp hx
    rw [sq, upperElt_mul_self]

theorem exists_conj_eq_of_mem_upperUnipotent [Finite F] {u v : SL(2, F)}
    (hu : u ∈ upperUnipotent F) (hv : v ∈ upperUnipotent F) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (upperUnipotent F : Set SL(2, F)), g * u * g⁻¹ = v := by
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff F).mp hu
  obtain ⟨t', rfl⟩ := (mem_upperUnipotent_iff F).mp hv
  have ht : t ≠ 0 := by
    rintro rfl
    exact hu1 (upperElt_zero F)
  have ht' : t' ≠ 0 := by
    rintro rfl
    exact hv1 (upperElt_zero F)
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (t' / t)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hr
    exact hr.elim ht' ht
  refine ⟨diagElt (Units.mk0 r hr0), diagElt_mem_normalizer _, ?_⟩
  rw [diagElt_conj_upperElt, Units.val_mk0, sq, ← hr, div_mul_cancel₀ t' ht]

theorem card_upperUnipotent_eq [Finite F] :
    Nat.card (upperUnipotent F) = 2 ^ (Nat.card SL(2, F)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  rw [← Nat.card_eq_fintype_card] at hm
  rw [card_upperUnipotent, CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hm]
  have hm1 : 1 ≤ (m : ℕ) := m.pos
  have hodd : Odd ((2 ^ (m : ℕ)) ^ 2 - 1) := by
    have he : Even ((2 ^ (m : ℕ)) ^ 2) := by
      rw [← pow_mul]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) he odd_one
  have h0 : (2 ^ (m : ℕ)) ^ 2 - 1 ≠ 0 := hodd.pos.ne'
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) h0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
    add_zero]

@[expose] noncomputable def sylowUpperUnipotent [Finite F] : Sylow 2 SL(2, F) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard (upperUnipotent F) card_upperUnipotent_eq

theorem coe_sylowUpperUnipotent [Finite F] :
    ((sylowUpperUnipotent : Sylow 2 SL(2, F)) : Subgroup SL(2, F)) = upperUnipotent F :=
  rfl

theorem isElemAbelian_transitive_map {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    {U : Subgroup G} (hU : CFSG.Assembly.IsElemAbelian 2 U)
    (htr : ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (U : Set G), g * u * g⁻¹ = v) :
    CFSG.Assembly.IsElemAbelian 2 (U.map φ.toMonoidHom) ∧
      ∀ u ∈ U.map φ.toMonoidHom, ∀ v ∈ U.map φ.toMonoidHom, u ≠ 1 → v ≠ 1 →
        ∃ g ∈ Subgroup.normalizer ((U.map φ.toMonoidHom : Subgroup G') : Set G'),
          g * u * g⁻¹ = v := by
  refine ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 2 φ.toMonoidHom U hU, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hu1 hv1
  have hu1' : u ≠ 1 := fun h => hu1 (by rw [h, map_one])
  have hv1' : v ≠ 1 := fun h => hv1 (by rw [h, map_one])
  obtain ⟨g, hg, hguv⟩ := htr u hu v hv hu1' hv1'
  refine ⟨φ g, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨g, hg, rfl⟩
  · change φ g * φ u * (φ g)⁻¹ = φ v
    rw [← map_inv, ← map_mul, ← map_mul, hguv]

theorem sylow_two_sl2 [Finite F] (S : Sylow 2 SL(2, F)) :
    CFSG.Assembly.IsElemAbelian 2 (S : Subgroup SL(2, F)) ∧ Nat.card S = Nat.card F ∧
      ∀ u ∈ (S : Subgroup SL(2, F)), ∀ v ∈ (S : Subgroup SL(2, F)), u ≠ 1 → v ≠ 1 →
        ∃ g ∈ Subgroup.normalizer ((S : Subgroup SL(2, F)) : Set SL(2, F)), g * u * g⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card S = Nat.card F := by
    rw [Sylow.card_eq_multiplicity, ← card_upperUnipotent_eq, card_upperUnipotent]
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq SL(2, F) (sylowUpperUnipotent : Sylow 2 SL(2, F)) S
  have hS : (S : Subgroup SL(2, F)) = (upperUnipotent F).map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul, coe_sylowUpperUnipotent]
    ext y
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  obtain ⟨h1, h2⟩ := isElemAbelian_transitive_map (MulAut.conj x) isElemAbelian_upperUnipotent
    fun u hu v hv hu1 hv1 => exists_conj_eq_of_mem_upperUnipotent hu hv hu1 hv1
  rw [hS]
  exact ⟨h1, by rw [← hS, hcard], h2⟩

theorem sylow_two_of_mulEquiv_sl2 [Finite F] {X : Type*} [Group X] (e : X ≃* SL(2, F))
    (S : Sylow 2 X) :
    CFSG.Assembly.IsElemAbelian 2 (S : Subgroup X) ∧ Nat.card S = Nat.card F ∧
      ∀ u ∈ (S : Subgroup X), ∀ v ∈ (S : Subgroup X), u ≠ 1 → v ≠ 1 →
        ∃ g ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), g * u * g⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  let S' : Sylow 2 SL(2, F) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS'coe : (S' : Subgroup SL(2, F)) = (S : Subgroup X).map e.toMonoidHom := rfl
  have hS : (S : Subgroup X) = (S' : Subgroup SL(2, F)).map e.symm.toMonoidHom := by
    rw [hS'coe, Subgroup.map_map]
    ext y
    simp
  obtain ⟨hS'1, hS'2, hS'3⟩ := sylow_two_sl2 S'
  obtain ⟨h1, h2⟩ := isElemAbelian_transitive_map e.symm hS'1 hS'3
  have hcard : Nat.card S = Nat.card F := by
    rw [← hS'2]
    exact (Nat.card_congr (e.subgroupMap (S : Subgroup X)).toEquiv).trans rfl
  rw [hS]
  exact ⟨h1, by rw [← hS, hcard], h2⟩

open CFSG.Assembly.RankThreeEven (projSL) in
theorem sylow_two_of_mulEquiv_projSL {m : ℕ} (hm : 1 ≤ m) {X : Type*} [Group X]
    (e : X ≃* projSL 2 (GaloisField 2 m)) (S : Sylow 2 X) :
    CFSG.Assembly.IsElemAbelian 2 (S : Subgroup X) ∧ Nat.card S = 2 ^ m ∧
      ∀ u ∈ (S : Subgroup X), ∀ v ∈ (S : Subgroup X), u ≠ 1 → v ≠ 1 →
        ∃ g ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), g * u * g⁻¹ = v := by
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  obtain ⟨ι⟩ := nonempty_sl2_mulEquiv_projSL hF
  obtain ⟨h1, h2, h3⟩ := sylow_two_of_mulEquiv_sl2 (e.trans ι.symm) S
  exact ⟨h1, by rw [h2, hF], h3⟩

end CFSG.RankThree.PartTwo.KFacts
