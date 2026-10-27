module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.CTP.SeitzLinearOuter
public import CFSG.RankThree.PartOne.KC.LinearPrimeSubfieldFixedGroup
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCLinComm
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

section Defs

variable {n : ℕ} {K : Type} [Field K]

@[expose] def slSub (n : ℕ) {K : Type} [Field K] (k : Subfield K) :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  (SpecialLinearGroup.map k.subtype).range

theorem mem_slSub {k : Subfield K} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ slSub n k ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ k := by
  constructor
  · rintro ⟨h, rfl⟩ i j
    exact ((h : Matrix (Fin n) (Fin n) k) i j).2
  · intro hg
    let M : Matrix (Fin n) (Fin n) k := fun i j => ⟨(g : Matrix (Fin n) (Fin n) K) i j, hg i j⟩
    have hM : k.subtype.mapMatrix M = (g : Matrix (Fin n) (Fin n) K) := rfl
    have hdet : M.det = 1 := by
      apply k.subtype.injective
      rw [map_one, RingHom.map_det, hM]
      exact g.2
    obtain ⟨h, hh⟩ : ∃ h : SpecialLinearGroup (Fin n) k, (h : Matrix (Fin n) (Fin n) k) = M :=
      ⟨⟨M, hdet⟩, rfl⟩
    exact ⟨h, Subtype.ext (by rw [SpecialLinearGroup.map_apply_coe, hh, hM])⟩

@[expose] def SubfieldPairSL (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ∀ (k : Subfield K) (p : ℕ), p.Prime → 5 ≤ p →
    Nat.card K = Nat.card k ^ p → ∀ A : GL (Fin n) K,
      (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k →
      Subgroup.closure ((slSub n k : Set (SpecialLinearGroup (Fin n) K)) ∪
        ((slSub n k).map (slConjugation n K A).toMonoidHom : Set (SpecialLinearGroup (Fin n) K))) =
          ⊤

end Defs

section Fixed

variable {n : ℕ} {K : Type} [Field K]

theorem range_linearSubfieldInclusion_eq_map (k : Subfield K) :
    (linearSubfieldInclusion n k).range = (slSub n k).map (proj n K) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective n k y
    exact ⟨SpecialLinearGroup.map k.subtype g, ⟨g, rfl⟩, (linearSubfieldInclusion_proj k g).symm⟩
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact ⟨proj n k g, linearSubfieldInclusion_proj k g⟩

theorem map_conjAut_range_linearSubfieldInclusion (k : Subfield K) (A : GL (Fin n) K) :
    ((linearSubfieldInclusion n k).range).map (conjAut n K A).toMonoidHom =
      ((slSub n k).map (slConjugation n K A).toMonoidHom).map (proj n K) := by
  rw [range_linearSubfieldInclusion_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem fixedSubgroup_fieldAut_eq_range_psl {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hnp : n < p)
    (hn3 : 3 ≤ n) [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {σ : K ≃+* K} (hσ : orderOf σ = p) :
    fixedSubgroup (fieldAut n K σ) =
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
  have hcopn : Nat.Coprime n p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hnp)).symm
  have h := (higher_linear_prime_subfield_fixed_group_and_full_centralizer Nat.prime_two hp
    (by omega) hf hn3 hcopn hK σ hσ).2.1
  exact SetLike.coe_injective h

theorem semilinearFixedSubfield_eq_of_orderOf {p : ℕ} [Finite K] [CharP K 2]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {σ τ : K ≃+* K} (hσ : orderOf σ = p)
    (hτ : orderOf τ = p) : semilinearFixedSubfield σ = semilinearFixedSubfield τ :=
  fixedField_eq_of_orderOf Nat.prime_two hf hK hσ hτ

theorem eq_one_of_central_range (hn3 : 3 ≤ n) (k : Subfield K) {x : projectiveSL n K}
    (hx : x ∈ (linearSubfieldInclusion n k).range)
    (hc : ∀ y ∈ (linearSubfieldInclusion n k).range, x * y = y * x) : x = 1 := by
  obtain ⟨x₀, rfl⟩ := hx
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  have hz : x₀ ∈ Subgroup.center (projectiveSL n k) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    rw [map_mul, map_mul]
    exact (hc _ ⟨g, rfl⟩).symm
  rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn3, Subgroup.mem_bot] at hz
  rw [hz, map_one]

end Fixed

section Main

variable {n : ℕ}

theorem fieldAutData_projectiveSL (hn3 : 3 ≤ n) (hpair : SubfieldPairSL n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hnp : n < p) {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) : FieldAutData (projectiveSL n K) p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
    have h1 := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) hd
    have h2 : Nat.gcd n (Nat.card K - 1) ≤ n := Nat.gcd_le_left _ (by omega)
    omega
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card Nat.prime_two hf hK
  refine fieldAutData_of_standard (linearAutGroup n K)
    {g | ∃ σ : K ≃+* K, orderOf σ = p ∧ g = fieldAut n K σ} ?_ ?_ ?_ ?_ ?_
  ·
    intro E hE hEc
    by_cases hEH : E ≤ innSL n K
    · obtain ⟨a, haE, ha1⟩ : ∃ a ∈ E, a ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
        rw [hbot, Subgroup.card_bot] at hEc
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      obtain ⟨g, rfl⟩ := hEH haE
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (map_one _)
    · have hAE : E ≤ (semilinPsi n K).range := fun a ha => by
        rw [range_semilinPsi]
        exact mem_semilinearAutGroup_of_pow_eq_one hn3 hp hp2
          (elemPow_eq_one_of_isElementaryAbelian a ha)
      have hcard := card_inf_inner_eq_prime hn3 hp hcop hcyc hAE hEc hEH
      have h1 : (E ⊓ innSL n K : Subgroup (MulAut (projectiveSL n K))) ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]
        exact hp.one_lt
      obtain ⟨⟨a, haE, haI⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
      obtain ⟨g, rfl⟩ := haI
      refine ⟨g, ?_, haE⟩
      rintro rfl
      exact ha1 (Subtype.ext (map_one _))
  ·
    intro α hα
    obtain ⟨hord, hout⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hαE := mem_semilinearAutGroup_of_pow_eq_one hn3 hp hp2 hαp
    have hαD : α ∉ linearAutGroup n K := fun hD => by
      obtain ⟨g, hg⟩ := inner_of_mem_linearAut_of_pow_eq_one hn3 hcop hD hαp
      exact hout g hg.symm
    obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
      CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two hf
        hn3 hK
    obtain ⟨-, σ, hσord, ⟨h, hhD, hαh⟩, -⟩ := hdesc p hp hp2 α hαE hαD hord
    exact ⟨h, hhD, fieldAut n K σ, ⟨σ, hσord, rfl⟩, hαh⟩
  ·
    rintro _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    rw [fixedSubgroup_fieldAut_eq_range_psl hp hp5 hnp hn3 hf hK hσ,
      fixedSubgroup_fieldAut_eq_range_psl hp hp5 hnp hn3 hf hK hτ,
      semilinearFixedSubfield_eq_of_orderOf hf hK hσ hτ]
  ·
    rintro _ ⟨σ, hσ, rfl⟩ _ x hx hcomm
    rw [fixedSubgroup_fieldAut_eq_range_psl hp hp5 hnp hn3 hf hK hσ] at hx hcomm
    exact eq_one_of_central_range hn3 _ hx hcomm
  ·
    rintro _ ⟨σ, hσ, rfl⟩ d hd hne
    left
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hd
    rw [fixedSubgroup_fieldAut_eq_range_psl hp hp5 hnp hn3 hf hK hσ] at hne ⊢
    set k := semilinearFixedSubfield σ with hk
    have hpf : p ∣ f ∧ Nat.card k = 2 ^ (f / p) :=
      card_semilinearFixedSubfield Nat.prime_two hf hK hσ
    have hcardK : Nat.card K = Nat.card k ^ p := by
      rw [hK, hpf.2, ← pow_mul, Nat.div_mul_cancel hpf.1]
    have hne' : (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k := by
      intro h
      apply hne
      rw [map_conjAut_range_linearSubfieldInclusion, h, range_linearSubfieldInclusion_eq_map]
    have hgen := hpair K inferInstance k p hp hp5 hcardK A hne'
    have h4 := congrArg (Subgroup.map (proj n K)) hgen
    rw [map_closure_union, Subgroup.map_top_of_surjective _ (proj_surjective n K)] at h4
    rw [map_conjAut_range_linearSubfieldInclusion, range_linearSubfieldInclusion_eq_map]
    exact h4

theorem extSeitzAtOuter_A_of_pair {m : ℕ} (hm2 : 2 ≤ m) (hm3 : m ≤ 3)
    (hpair : SubfieldPairSL (m + 1)) {q : TauCeti.PrimePower} (hq2 : q.p = 2) :
    ExtSeitzAtOuter (.A m q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hc hout
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  let e : K ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hchar : CharP (GaloisField q.p q.exponent) 2 := by
    rw [← hq2]
    infer_instance
  have hcard : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hq2]
  have hd : FieldAutData K p :=
    (fieldAutData_projectiveSL (by omega) hpair hp hp5 (by omega) (K := GaloisField q.p q.exponent)
      q.exponent_pos hcard).of_mulEquiv e hp
  left
  exact closure_fixUnion_eq_top_of_fieldAutData hnab hp hd E hc hout

end Main

end CFSG.RankThree.PartOne.CTP
