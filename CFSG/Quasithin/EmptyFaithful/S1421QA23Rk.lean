module

public import CFSG.Quasithin.EmptyFaithful.S1421QA21Bor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtB42ListFAux

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.QA21

namespace QA23

theorem normalizer_of_isPSL_two {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsPSL 2 2 n X)
    {U A : Subgroup X} (hU : IsSylowTwoOf U ⊤) (hUA : U ≤ A) (hA : A ≠ ⊤) :
    A ≤ Subgroup.normalizer (U : Set X) := by
  have hB := A5.C25.fusionIsBenderGroup_of_isPSL h
  have hs : IsSimpleGroup X := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hidx : ¬ 2 ∣ U.index := by
    have h2 : ¬ 2 ∣ U.relIndex ⊤ := hU.2.2
    rwa [Subgroup.relIndex_top_right] at h2
  let Q : Sylow 2 X := hU.2.1.toSylow hidx
  exact Bridge.Over.le_normalizer_of_bender hB Q (M := A) hUA hA

theorem mem_of_mem_sup_center {X : Type} [Group X] [Finite X] (hO2 : CFSG.pCore 2 X = ⊥)
    {U : Subgroup X} (hU : IsPGroup 2 U) {x : X} (hx : x ∈ U ⊔ Subgroup.center X) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : x ∈ U := by
  obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨j, hj⟩ := hU ⟨u, hu⟩
  have hu' : u ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcomm : Commute u z := Subgroup.mem_center_iff.mp hz u
  have h1 : (u * z) ^ 2 ^ (k + j) = 1 := by rw [pow_add, pow_mul, hxk, one_pow]
  have h2 : u ^ 2 ^ (k + j) = 1 := by rw [add_comm, pow_add, pow_mul, hu', one_pow]
  rw [hcomm.mul_pow, h2, one_mul] at h1
  have hord : orderOf z ∣ 2 ^ (k + j) := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hodd := B42ListF.odd_orderOf_of_mem_center hO2 hz
  rw [hi] at hodd
  have hi0 : i = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  have hz1 : z = 1 := orderOf_eq_one_iff.mp (by rw [hi, hi0, pow_zero])
  rw [hz1, mul_one]
  exact hu

theorem solvableOvergroupsNormalize_of_quotient_center {X : Type} [Group X] [Finite X]
    (hO2 : CFSG.pCore 2 X = ⊥) {U : Subgroup X} (hU : IsPGroup 2 U)
    (h : SolvableOvergroupsNormalize (X ⧸ Subgroup.center X)
      (U.map (QuotientGroup.mk' (Subgroup.center X)))) :
    SolvableOvergroupsNormalize X U := by
  intro A hUA hA a ha
  have hAs : Group.IsSolvable ↥(A.map (QuotientGroup.mk' (Subgroup.center X))) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.mk' (Subgroup.center X)).subgroupMap A)
      (MonoidHom.subgroupMap_surjective _ _)
  have h1 := h _ (Subgroup.map_mono hUA) hAs
  have key : ∀ b ∈ A, ∀ u ∈ U, b * u * b⁻¹ ∈ U := by
    intro b hb u hu
    have hb1 : QuotientGroup.mk' (Subgroup.center X) b ∈
        Subgroup.normalizer ((U.map (QuotientGroup.mk' (Subgroup.center X)) : Subgroup _) :
          Set (X ⧸ Subgroup.center X)) := h1 ⟨b, hb, rfl⟩
    have hu1 : QuotientGroup.mk' (Subgroup.center X) u ∈
        U.map (QuotientGroup.mk' (Subgroup.center X)) := ⟨u, hu, rfl⟩
    have hmem := (Subgroup.mem_normalizer_iff.mp hb1 _).mp hu1
    obtain ⟨u', hu', hu'e⟩ := hmem
    have hZ : u'⁻¹ * (b * u * b⁻¹) ∈ Subgroup.center X := by
      have hw : QuotientGroup.mk' (Subgroup.center X) (b * u * b⁻¹) =
          QuotientGroup.mk' (Subgroup.center X) u' := by
        rw [hu'e]
        simp only [map_mul, map_inv]
      have : QuotientGroup.mk' (Subgroup.center X) (u'⁻¹ * (b * u * b⁻¹)) = 1 := by
        rw [map_mul, map_inv, hw, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    have hxm : b * u * b⁻¹ ∈ U ⊔ Subgroup.center X := by
      have : b * u * b⁻¹ = u' * (u'⁻¹ * (b * u * b⁻¹)) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hu' hZ
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    refine mem_of_mem_sup_center hO2 hU hxm (k := k) ?_
    have hu2 : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [conj_pow, hu2]
    simp
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key a ha g hg, fun hg => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hg
  simpa [mul_assoc] using this

theorem solvableOvergroupsNormalize_of_typeB
    {X : Type} [Group X] [Finite X] (hO2 : CFSG.pCore 2 X = ⊥)
    (hB : ((∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n X) ∨ (∃ n : ℕ, 2 ≤ n ∧ IsPSp4 2 n X) ∨
        ∃ n : ℕ, 2 ≤ n ∧ IsG2 2 n X) ∨
      ∃ n : ℕ, 2 ≤ n ∧ IsPSL 3 2 n (X ⧸ Subgroup.center X))
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) : SolvableOvergroupsNormalize X U := by
  rcases hB with (⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩) | ⟨n, hn, h⟩
  · exact solvableOvergroupsNormalize_of_isPSL3 hn h hU
  · exact solvableOvergroupsNormalize_of_isPSp4 hn h hU
  · exact solvableOvergroupsNormalize_of_big3 hn (Or.inr (Or.inr h)) hU
  · refine solvableOvergroupsNormalize_of_quotient_center hO2 hU.2.1 ?_
    exact solvableOvergroupsNormalize_of_isPSL3 hn h
      (isSylowTwoOf_top_map_of_surjective hU _ (QuotientGroup.mk'_surjective _))

end QA23

end CFSG.Quasithin
