module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMOrder
public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxStep6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxFamily
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxNotG2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGLevTwoMain

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

section Witness

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
  {𝒦 : Finset (Subgroup G)}

theorem qTwoD_witness
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hx : x ∈ Bs)
    {ιL : Type} [Fintype ιL] {ML : CoxeterMatrix ιL} (hML : GGIsWeylMatrixAD ML)
    (hAL : GGWeylOfType 3 ML (ggAutomizer L Bs))
    (hfixL : ∀ a ∈ ggAutomizer L Bs, a ⟨x, hx⟩ = ⟨x, hx⟩)
    (hcard : Nat.card ↥Bs ≤ 3 ^ (Fintype.card ιL + 1))
    (hW : GGWeylReflectionGroup 3 (ggAInf 3 B Bs x L D J))
    (hSat : ∀ a ∈ ggAInf 3 B Bs x L D J, GGIsReflection 3 a → a ⟨x, hx⟩ = ⟨x, hx⟩ →
      (∃ g ∈ ggAInf 3 B Bs x L D J, ∃ r ∈ ggAutomizer L Bs, GGIsReflection 3 r ∧
        a = g * r * g⁻¹) → a ∈ ggAutomizer L Bs) :
    GGSecFiveInfWitness 3 B Bs x L D J := by
  have hcfg' := ggSecFiveRouteCfg'_of_routeCfg hcfg
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  have hBs : GGBstar 3 B Bs := hcfg.1.1.2.1
  refine ⟨hW, ?_⟩
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  obtain ⟨𝒮', h𝒮'sub, hcard', heq⟩ :=
    ggSecFiveLevTwoInput'_holds G 3 Bs Nat.prime_three (by decide) hBs.2.1 hNT
      (ggAInf 3 B Bs x L D J) (ggRM_ainf_le_induced)
      ι M hM (ggRM_not_G2 (Or.inl hML) hAL le_sup_left f) f hf
      ⟨x, hx⟩ (ggAutomizer L Bs) ιL ML le_sup_left hfixL
      (Or.inl hML) hAL hcard hSat
      (GGSecFiveNbrAutFamily 3 B Bs x D J) (by
        intro K hK
        obtain ⟨y, K₀, hNK, rfl⟩ := hK
        refine ⟨?_, ?_⟩
        · exact (le_iSup_of_le y (le_iSup_of_le K₀ (le_iSup_of_le hNK
            (le_rfl : ggAutomizer K₀ Bs ≤ ggAutomizer K₀ Bs)))).trans le_sup_right
        · exact hcfg'.2.1 y K₀ hNK)
  obtain ⟨𝒦', h𝒦', hjoin'⟩ := ggRM_nbrs_of_family 𝒮' h𝒮'sub hcard'
  refine ⟨𝒦', h𝒦', ?_⟩
  calc ggAutomizerJoin L Bs 𝒦'
      = ggAutomizer L Bs ⊔ ⨆ S ∈ 𝒮', S := hjoin'
    _ = ggAutomizer L Bs ⊔ ⨆ S ∈ GGSecFiveNbrAutFamily 3 B Bs x D J, S := heq.symm
    _ = ggAInf 3 B Bs x L D J := ggRM_ainf_eq_sup.symm

theorem qTwoD_rm2 (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hw : GGSecFiveInfWitness 3 B Bs x L D J) :
    ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
  ggRM_of_witness hcfg.2.2.2 hw

end Witness

end CFSG.StandardType.QTwo

end
