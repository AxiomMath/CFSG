module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusRoot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaMinusLevi
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.OmegaMinusFlag
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2Map
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.NormalClosure
import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
open CFSG.RankThree.PartTwo.Sec18
open scoped MatrixGroups

private theorem commutator_range_eq_self_E16 {G H : Type} [Group G] [Group H] (f : G →* H)
    (hG : Group.IsPerfect G) : ⁅f.range, f.range⁆ = f.range := by
  have hperf : ⁅(⊤ : Subgroup G), ⊤⁆ = ⊤ := hG.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]

private theorem not_isPGroup_two_range_E16 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {H : Type} [Group H] (f : SL(2, K) →* H)
    (hf : Function.Injective f) : ¬ IsPGroup 2 ↥f.range := by
  intro hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  obtain ⟨fn, hcard⟩ : ∃ fn : ℕ, Nat.card K = 2 ^ fn := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hfn : fn ≠ 0 := by
    intro hfn0
    rw [hfn0, pow_zero] at hcard
    omega
  have hodd : Odd (orderOf g) := by
    rw [hord, hcard]
    exact Nat.Even.sub_odd (n := 1) (m := 2 ^ fn) (Nat.one_le_two_pow)
      (even_two.pow_of_ne_zero hfn) odd_one
  have hgt : 1 < orderOf g := by
    rw [hord]
    omega
  rw [IsPGroup.iff_orderOf] at hP
  obtain ⟨k, hk⟩ := hP ⟨f (plusDiagSL2 g), MonoidHom.mem_range.mpr ⟨plusDiagSL2 g, rfl⟩⟩
  rw [Subgroup.orderOf_mk, orderOf_injective f hf, orderOf_plusDiagSL2] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  have heven : Even (2 ^ k) := even_two.pow_of_ne_zero hk0
  have hoddk : Odd (2 ^ k) := hk ▸ hodd
  exact (Nat.not_even_iff_odd.mpr hoddk) heven

private theorem isQuasisimple_statedOmega_minus_E16 {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Open.IsQuasisimple ↥(StatedOmega (StatedQuadMinus (1 + 2) K b c)) := by
  obtain ⟨fn, hK⟩ : ∃ fn : ℕ, Nat.card K = 2 ^ fn := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨hsimple, hna, -⟩ := orthResDer_facts (K := K) (b := b) (c := c) (m := 2) hK
    (by norm_num) hirr
  haveI : IsSimpleGroup ↥(orthResDer K b c 2) := hsimple
  have hqs : CFSG.Open.IsQuasisimple ↥(orthResDer K b c 2) :=
    (orthMinus_isQuasisimple_of_simple hna).1
  exact CFSG.Open.IsQuasisimple.of_mulEquiv
    (orthResDerEquivStatedOmega (b := b) (c := c) 2).symm hqs

private theorem nonempty_bar2_hinf_tailQZero_E16 {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (Bar2 (Hinf (omegaMinusTailQZero K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus (1 + 2) K b c))) := by
  obtain ⟨φ₀, hφ₀⟩ := exists_mulEquiv_lineStab_map_eq_orthParab (b := b) (c := c) hirr 1
  let P : Subgroup ↥(StatedOmega (StatedQuadMinus (1 + 3) K b c)) :=
    lineStab (StatedOmega (StatedQuadMinus (1 + 3) K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1)
  let φ : ↥(StatedOmega (StatedQuadMinus (1 + 3) K b c)) ≃* OmegaMinusE K b c := φ₀
  have hφ : P.map φ.toMonoidHom = omegaMinusTailQZero K b c := hφ₀
  obtain ⟨e₁⟩ := nonempty_bar2_hinf_map φ P
  obtain ⟨e₂⟩ := nonempty_bar2_hinf_lineStab_statedOmegaMinus (b := b) (c := c) hirr 1
  rw [hφ] at e₁
  exact ⟨e₁.symm.trans e₂⟩

theorem isQuasisimple_bar2_hinf_omegaMinusTailQZero {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Open.IsQuasisimple (Bar2 (Hinf (omegaMinusTailQZero K b c))) := by
  obtain ⟨e⟩ := nonempty_bar2_hinf_tailQZero_E16 (K := K) (b := b) (c := c) hirr
  exact CFSG.Open.IsQuasisimple.of_mulEquiv e
    (isQuasisimple_statedOmega_minus_E16 (K := K) (b := b) (c := c) hirr)

theorem normal_closure_omegaMinusRoot {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : 4 ≤ Nat.card K)
    (N : Subgroup (OmegaMinusE K b c)) (hNK : N ≤ Hinf (omegaMinusTailQZero K b c))
    (hnorm : Hinf (omegaMinusTailQZero K b c) ≤ Subgroup.normalizer (N : Set (OmegaMinusE K b c)))
    (hX : omegaMinusRoot K b c ≤ N) : N = Hinf (omegaMinusTailQZero K b c) := by
  exact normal_closure_top_of_perfect (Hinf (omegaMinusTailQZero K b c))
    (commutator_inSubgroup_perfectResidual (omegaMinusTailQZero K b c))
    (isQuasisimple_bar2_hinf_omegaMinusTailQZero hirr)
    (omegaMinusRoot K b c)
    (omegaMinusRoot_le_hinf hK b c)
    (commutator_range_eq_self_E16 (omegaMinusRootHom K b c)
      (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK))
    (not_isPGroup_two_range_E16 hK (omegaMinusRootHom K b c)
      (omegaMinusRootHom_injective K b c))
    N hNK hnorm hX

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
