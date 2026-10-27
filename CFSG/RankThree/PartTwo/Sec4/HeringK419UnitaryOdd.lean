module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofLieP
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofRankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open Matrix

namespace HeringUnitary

theorem pRank_projSL_four_le_two {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hq3 : p ^ f % 3 = 2) :
    CFSG.pRank 3 (projSL 4 (GaloisField p f) ⧸ Subgroup.center (projSL 4 (GaloisField p f))) ≤
      2 := by
  set F := GaloisField p f
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = p ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p f (by omega)]
  have hs : IsSimpleGroup (projSL 4 F) := by
    have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := F) 4 (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (Sec4.projSLEquivPSLn 4 F).isSimpleGroup
  exact Sec21.Item223CensusProof.pRank_le_two_of_card_le_nine fun B hB =>
    Sec4.card_le_of_projImage (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker hs (m := 4)
      (by norm_num) (fun c hc => by
        apply Sec4.pow_four_of_det_scalar
        have := congrArg Units.val (MonoidHom.mem_ker.mp hc)
        rwa [GeneralLinearGroup.val_det_apply] at this) (by norm_num)
      (fun P hPH hcomm hexp => by
        have : Finite P := Finite.of_injective _ Subtype.val_injective
        have h := Sec21.Item223CensusResProof.card_sq_le_of_card_mod_two hF hq3 P hcomm hexp
        rw [Fintype.card_fin] at h
        nlinarith) B hB

theorem pRank_projSU_four_le_two {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq3 : p ^ f % 3 = 1) :
    CFSG.pRank 3 (projSU 4 p f ⧸ Subgroup.center (projSU 4 p f)) ≤ 2 := by
  set F := GaloisField p (2 * f)
  have hF : Nat.card F = p ^ (2 * f) := GaloisField.card p (2 * f) (by omega)
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out hp3 hF
  have hs : IsSimpleGroup (projSU 4 p f) := by
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p f
      (by rw [hF, ← pow_mul, mul_comm]) 4 (by norm_num) (by
        intro h
        exact absurd (Prod.mk.inj h).1 (by norm_num))
    exact (Sec4.projSUEquivStatedProj 4 p f).isSimpleGroup
  exact Sec21.Item223CensusProof.pRank_le_two_of_card_le_nine fun B hB =>
    Sec4.card_le_of_projImage (Subgroup.closure {A : GL (Fin 4) F |
      GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f)))ᵀ *
        (A : Matrix (Fin 4) (Fin 4) F) = 1})
      hs (m := 4) (by norm_num)
      (fun c hc => Sec4.pow_four_of_det_scalar (Sec4.det_of_mem_closure_su _ hc))
      (by norm_num) (fun P hPH hcomm hexp => by
        have : Finite F := inferInstance
        have : Finite P := Finite.of_injective _ Subtype.val_injective
        have h := Sec21.Item223CensusResProof.card_sq_le_of_unitary_of_mod_one h3 hq3 P hcomm hexp
          fun x hx => Sec21.Item223CensusResProof.unitary_of_mem_closure_su (hPH hx)
        rw [Fintype.card_fin] at h
        nlinarith) B hB

theorem pRank_projSp_four_le_two {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    CFSG.pRank 3 (projSp 2 (GaloisField p 1) ⧸ Subgroup.center (projSp 2 (GaloisField p 1))) ≤
      2 := by
  set F := GaloisField p 1
  have hF : Nat.card F = p ^ 1 := GaloisField.card p 1 (by omega)
  have hs : IsSimpleGroup (projSp 2 F) := by
    have := CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr (by rw [hF, pow_one]; omega)))
    exact (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (CFSG.Assembly.LowTwoRank.StatedSp 2 F)).symm.isSimpleGroup
  exact Res417Three.pRank_projSp_two_le (by omega) le_rfl hs

end HeringUnitary

end CFSG.RankThree.PartTwo.Sec4
