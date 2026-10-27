module

public import Certificates.Certificate1037102
public import Certificates.Data.W4RowFi22
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Certificates
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem regIn_fi22P : RegIn 3510 fi22P [fi22A0P, fi22A1P] := by
  have gen : ∀ k < 2, ∃ g ∈ fi22P,
      PRep 3510 (fi22ChainGen k, invCand 3510 (fi22ChainGen k)) g := by
    intro k hk
    have hmem : fi22Chain.original.get ⟨k, hk⟩ ∈ fi22P :=
      Subgroup.subset_closure (schreier_vector_get_mem_toList fi22Chain.original ⟨k, hk⟩)
    rw [fi22Chain_original_get] at hmem
    refine ⟨fi22GenPerm k, hmem, ?_, ?_⟩
    · dsimp only
      exact rep_fi22Gen hk
    · dsimp only
      exact rep_inv_of_isInvA (rep_fi22Gen hk) (fi22Chain_check.2.1 k hk)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact gen 0 (by norm_num)
  · exact gen 1 (by norm_num)

theorem pRep_fi22RepP {k : ℕ}
    (hk : k < 6) : PRep 3510 (fi22RepP k) (fi22ExtRep k) :=
  PRep.of_sq (rep_fi22ExtRep hk) (Certificates.certificate1037102.1 k hk)

theorem fi22_ext_dihedral :
    (∃ c ∈ fi22P, orderOf (fi22ExtRep 0 * (c * fi22ExtRep 0 * c⁻¹)) = 13) ∧
      (∃ c ∈ fi22P, orderOf (fi22ExtRep 3 * (c * fi22ExtRep 3 * c⁻¹)) = 11) ∧
      ∃ c ∈ fi22P, orderOf (fi22ExtRep 5 * (c * fi22ExtRep 5 * c⁻¹)) = 11 :=
  Certificates.certificate1037102.2.1

theorem fi22_ext_five :
    ∃ c ∈ fi22P, orderOf (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) = 5 ∧
      ∃ g ∈ fi22P, g * (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) * g⁻¹ =
        (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) ^ 2 :=
  Certificates.certificate1037102.2.2.1

theorem fi22_ext_heisCfg
    {k : ℕ} (hk : k < 6) :
    ∃ (x y : Fin 3 → Equiv.Perm (Fin 3510)) (z : Equiv.Perm (Fin 3510)),
      (∀ i, x i ∈ fi22P) ∧ (∀ i, y i ∈ fi22P) ∧ z ∈ fi22P ∧ HeisCfg 3 3 x y z ∧
        (∀ i, y i ^ 3 = 1) ∧ fi22ExtRep k * x 0 * (fi22ExtRep k)⁻¹ = (x 0)⁻¹ :=
  Certificates.certificate1037102.2.2.2 k hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
