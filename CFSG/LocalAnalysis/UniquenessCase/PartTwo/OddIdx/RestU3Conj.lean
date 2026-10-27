module

import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

theorem oddIdxRest_su3_isCyclic {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hq3 : p ^ f % 3 = 1) (hf : f ≠ 0)
    (X : Subgroup (SU (unitaryInvolution F p f) 3)) (hX : IsPGroup 3 X) : IsCyclic X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp3 : 3 ≠ p := by
    rintro rfl
    rw [Nat.pow_mod, Nat.mod_self, zero_pow hf] at hq3
    simp at hq3
  have hre : ¬ 3 ∣ p ^ f + 1 := by omega
  let e := equivStatedSU hF 3
  have hX' : IsPGroup 3 (X.map e.toMonoidHom) := hX.map e.toMonoidHom
  obtain ⟨P, hP⟩ := hX'.exists_le_sylow
  have hcyc : IsCyclic (P : Subgroup (StatedSU 3 (p ^ f) F)) :=
    CFSG.ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow hF
      (by norm_num) hp3 hre P
  haveI : IsCyclic (P : Subgroup (StatedSU 3 (p ^ f) F)) := hcyc
  have hcyc' : IsCyclic (X.map e.toMonoidHom) := Subgroup.isCyclic_of_le hP
  exact (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective).isCyclic.mpr hcyc'

theorem oddIdxRest_su3_conj {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hq3 : p ^ f % 3 = 1) (hf : f ≠ 0)
    {N D : Subgroup (SU (unitaryInvolution F p f) 3)} (hD : Nat.card D = 3)
    (hnorm : Subgroup.normalizer (D : Set (SU (unitaryInvolution F p f) 3)) ≤ N) :
    ∃ (ω : Fˣ) (g : SU (unitaryInvolution F p f) 3), orderOf ω = 3 ∧
      Subgroup.normalizer ((Subgroup.zpowers (tSU hF ω) :
        Subgroup (SU (unitaryInvolution F p f) 3)) : Set (SU (unitaryInvolution F p f) 3)) ≤
          N.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.exists_orderOf_three hF hq3
  have hA₀ : Nat.card (Subgroup.zpowers (tSU hF ω)) = 3 := by
    rw [Nat.card_zpowers, orderOf_injective (tSU hF) (tSU_injective hF) ω, hω]
  have hcyc := oddIdxRest_su3_isCyclic hF hq3 hf
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.exists_conj_eq_of_card_eq_three
      hcyc hD hA₀
  refine ⟨ω, g, hω, ?_⟩
  rw [hg, ← Subgroup.map_equiv_normalizer_eq]
  exact Subgroup.map_mono hnorm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.OddIdx
