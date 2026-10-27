module

public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.GH74.Bender
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinBender
public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input

public section

namespace CFSG.Quasithin.Shult

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups

theorem exists_borel_of_fusionIsBenderGroup {K : Type} [Group K]
    [Finite K] (hK : fusionIsBenderGroup K) : ∃ q k : ℕ, fusionBenderBorel K q k := by
  rcases hK with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 m) := Finite.of_equiv K e.toEquiv
    exact ⟨2 ^ m, 1,
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
        m hm).map_mulEquiv e.symm⟩
  · have : Finite (PSU3 2 m) := Finite.of_equiv K e.toEquiv
    exact ⟨2 ^ m, 3,
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2
        m hm).map_mulEquiv e.symm⟩
  · have : Finite (Sz a) := Finite.of_equiv K e.toEquiv
    exact ⟨2 ^ (2 * a + 1), 2,
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4
        a ha).map_mulEquiv e.symm⟩

theorem isSolvable_normalizer_of_bender {K : Type} [Group K]
    [Finite K] (hK : fusionIsBenderGroup K) {W : Subgroup K} (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W) :
    Group.IsSolvable (Subgroup.normalizer (W : Set K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, k, hB⟩ := exists_borel_of_fusionIsBenderGroup hK
  obtain ⟨Q, hWQ⟩ := hW2.exists_le_sylow
  obtain ⟨hSE, ⟨D, hDcyc, -, -, hsup⟩, -⟩ := hB Q
  have hsolv := CFSG.QuasithinUnique.Unc25G2.BenderBorel.isSolvable_normalizer_of_sup_cyclic
    Q.isPGroup' hDcyc hsup
  have hle : Subgroup.normalizer (W : Set K) ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    intro n hn
    by_contra hnQ
    have hodd := hSE.2.2 n hnQ
    have hWB : W ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) ⊓
        (Subgroup.normalizer ((Q : Subgroup K) : Set K)).map (MulAut.conj n⁻¹).toMonoidHom := by
      intro w hw
      refine ⟨Subgroup.le_normalizer (hWQ hw), ?_⟩
      have hnw : n * w * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hn w).mp hw
      refine ⟨n * w * n⁻¹, Subgroup.le_normalizer (hWQ hnw), ?_⟩
      simp [mul_assoc]
    have hdvd := Subgroup.card_dvd_of_le hWB
    have hWodd : Odd (Nat.card W) := hodd.of_dvd_nat hdvd
    obtain ⟨j, hj⟩ := hW2.exists_card_eq
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hW (Subgroup.card_eq_one.mp (by simpa using hj))
    have : Even (Nat.card W) := by
      rw [hj]
      exact (Nat.even_pow.mpr ⟨even_two, hj0⟩)
    exact (Nat.not_even_iff_odd.mpr hWodd) this
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem isSolvable_outer_of_bender {K : Type} [Group K] [Finite K]
    (hK : fusionIsBenderGroup K) : Group.IsSolvable (Outer K) := by
  obtain ⟨n, i, e, h⟩ := isBenderGroup_iff_exists_benderType.mp
    (CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup hK)
  have h' := h
  cases h with
  | linear n hn e0 =>
    have hcyc := (BenderType.outer_linear h').1
    exact Group.isSolvable_of_comm (isMulCommutative_iff.mp hcyc.isMulCommutative)
  | suzuki a ha e0 =>
    have hcyc := (BenderType.outer_suzuki h').1
    exact Group.isSolvable_of_comm (isMulCommutative_iff.mp hcyc.isMulCommutative)
  | unitary n hn e0 =>
    obtain ⟨Dd, hDn, hDcyc, -, hQcyc, -⟩ := BenderType.outer_unitary h'
    have h1 : Group.IsSolvable Dd :=
      Group.isSolvable_of_comm (isMulCommutative_iff.mp hDcyc.isMulCommutative)
    have h2 : Group.IsSolvable (Outer K ⧸ Dd) :=
      Group.isSolvable_of_comm (isMulCommutative_iff.mp hQcyc.isMulCommutative)
    exact Group.isSolvable_of_ker_le_range Dd.subtype (QuotientGroup.mk' Dd)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

end CFSG.Quasithin.Shult
