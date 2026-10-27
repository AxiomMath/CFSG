module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofCentS

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Cent

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
  CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [hℓ : Fact ℓ.Prime] {σ : K ≃+* K}

theorem map_triEmb_centS (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    Subgroup.map (triEmb K σ L)
        (centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
          Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
            Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) =
      ((thetaHom L).comp (Matrix.SpecialLinearGroup.map
        (RingHom.eqLocusField Fr (RingHom.id L)).subtype)).range := by
  have hℓp : ℓ.Prime := hℓ.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c) := fun c => by
    rw [hσ, hFr, map_pow]
  have hfixθ := twistHom_thetaConj σ Fr (RingHom.ext hcomm)
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hz
    have hFZ : Matrix.SpecialLinearGroup.map Fr Z = Z := by
      apply thetaHom_injective
      rw [← twistHom_thetaHom Fr hfixθ, hZ]
      exact triEmb_fixed Fr (RingHom.ext hcomm) z
    obtain ⟨Yk, hYk⟩ := exists_sl2_eqLocus Fr Z hFZ
    refine MonoidHom.mem_range.2 ⟨Yk, ?_⟩
    rw [MonoidHom.comp_apply, hYk, hZ]
  · intro hy
    obtain ⟨Y, rfl⟩ := MonoidHom.mem_range.1 hy
    have hmem : thetaHom L (Matrix.SpecialLinearGroup.map
        (RingHom.eqLocusField Fr (RingHom.id L)).subtype Y) ∈ (triEmb K σ L).range := by
      rw [triEmb_range hℓp hf hK hσ Fr hFr]
      refine Subgroup.mem_inf.2 ⟨thetaHom_mem_adjointGroup _, ?_⟩
      change twistHom TwistTag.D4 L Fr (thetaHom L _) = MonoidHom.id _ (thetaHom L _)
      rw [twistHom_thetaHom Fr hfixθ, map_frob_map_subtype]
      rfl
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hmem
    refine Subgroup.mem_map.2 ⟨x, mem_centralizer_of_triEmb_mem (L := L) ?_, hx⟩
    rw [hx]
    exact thetaHom_mem_thetaPair _

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Cent

end
