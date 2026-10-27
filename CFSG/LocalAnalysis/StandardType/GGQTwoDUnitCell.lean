module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXFacts
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDispY
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShape
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
import CFSG.LocalAnalysis.StandardType.GGQTwoDTablePFinal
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMember

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo


theorem ggQTwoCellInputOn_unitary {R : ℕ → Prop} (hR : ∀ m, R m → 7 ≤ m)
    (hL1 : GGQTwoL1Input) (hEA : GGQTwoEdgeAmbientInput) (hBal : GGLBalanceInput)
    (hT : GGTPNTransferBNoCorners) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) :
    GGQTwoCellInputOn R qtwoOrthL.compl := by
  classical
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hA3 : QTwoOrthAdjA3Stmt := qtwoOrthAdjA3_holds
  have hTP : GGNbrTablePNbrInputI1On GGRegimeDeletedUnitary1836 :=
    ggNbrTablePNbrInputI1On_delU_of_transfer hT
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM hL
  have hm : 7 ≤ m := hR m hRm
  obtain ⟨F0, hF0, hF0fin, hF0char, ψ, ε, hbase⟩ :=
    ggQTwoDUnit_base hRig hTBF hWI hcfg e' hm hM hL
  letI : Field F0 := hF0
  letI : Finite F0 := hF0fin
  letI : CharP F0 2 := hF0char
  obtain ⟨βL, ω, hcoords⟩ := ggQTwoDUnit_coords hTBF hWI hcfg e' (by omega) hM hbase
  have hBBs : B ≤ Bs := hcfg.1.1.1.2.1.1
  have hshape0 := ggQTwoDUnit_B_shape hcfg.1 (by omega) hbase
  have hshape' : ∃ a b : Fin m, a ≠ b ∧ (B = Bs ∨ ∀ s : ↥Bs,
      ((s : G) ∈ B ↔ βL (Additive.ofMul s) a = βL (Additive.ofMul s) b)) := by
    rcases hshape0 with hB | ⟨a, b, hab, hh⟩
    · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, Or.inl hB⟩
      intro h
      exact absurd (congrArg Fin.val h) (by norm_num)
    · exact ⟨a, b, hab, Or.inr (fun s => (hh s).trans
        (ggQTwoDUnit_shape_coords hcoords hbase.hyp.ker (by omega) s))⟩
  obtain ⟨a, b, hab, hshape⟩ := hshape'
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset (Fin m))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt (Finset.card_le_two (a := a) (b := b)) (by omega))
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hca, hcb⟩ := hc
  obtain ⟨α, -, hsign, g, hgJ, hgnorm, hconj⟩ := ggQTwoDUnit_conj hcoords hab
  let b' : ↥Bs := Additive.toMul (βL.symm (Pi.single c 1))
  have hb'coord : βL (Additive.ofMul b') = Pi.single c 1 := by
    simp only [b', ofMul_toMul, AddEquiv.apply_symm_apply]
  have hdel : QTwoUnitDel Bs βL a b c α g b' :=
    ⟨hab, hca, hcb, hsign, hgnorm, hconj, hb'coord⟩
  have hb'B : (b' : G) ∈ B := ggQTwoDUnit_mem_B hca hcb hBBs hshape hb'coord
  obtain ⟨Y, hJ₁Y, hJ₂Y, Φ, hΦF, hΦr, hΦZ⟩ :=
    ggQTwoDUnit_orthY hTP hRig hBal hEA hcfg hm hM hbase hcoords hdel hb'B
  refine ⟨qtwoDelX ψ c g, ?_, ?_, ?_⟩
  · exact ggQTwoDUnit_X_facts hA3 hL1 hEA hcfg hm hM hbase hcoords hdel
      (sup_le hJ₁Y hJ₂Y) Φ hΦF (by omega) hΦZ
  · exact ggQTwoDUnit_X_frame hm hbase hcoords hdel
  · exact ggQTwoDUnit_X_le_ggG0 hcfg hbase hgJ

theorem ggQTwoCellInput_unitary (hL1 : GGQTwoL1Input) (hEA : GGQTwoEdgeAmbientInput)
    (hBal : GGLBalanceInput) (hT : GGTPNTransferBNoCorners) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGQTwoCellInput qtwoOrthL.compl :=
  ggQTwoCellInputOn_unitary (fun _ h => h) hL1 hEA hBal hT hTBF hWI

end CFSG.StandardType.QTwo

end
