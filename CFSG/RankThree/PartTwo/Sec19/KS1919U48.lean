module

public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.RankThree.PartTwo.Sec19.KS1919U48Levi
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSU)

theorem ks1919U48 : KS1919U48 := by
  intro X _ _ ⟨e⟩ P hP B hBP hcomm hexp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 3 (GaloisField 2 (2 * 3)) :=
    ⟨Nat.prime_two, by norm_num, GaloisField.card 2 (2 * 3) (by norm_num)⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 2) (ε := 0)
  let ψ₀ : projSU 4 2 3 ≃* StatedProj (StatedSU 4 (2 ^ 3) (GaloisField 2 (2 * 3))) :=
    (MulEquiv.subgroupCongr
      (CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 4 2 3).symm).trans
      (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm
  let ψ : X ≃* hypPSU h 2 0 :=
    e.trans (ψ₀.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm)
  obtain ⟨hP', T, hT⟩ := Step1910Proof.isProperParabolic_map ψ hP
  have hcard : Nat.card (B.map ψ.toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective ψ.injective
  rw [← hcard]
  refine KS1919U48Proof.card_le_nine_of_le_parabolic h ⟨1, rfl⟩ hP' T hT _
    (Subgroup.map_mono hBP) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]

end CFSG.RankThree.PartTwo.Sec19
