module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneCore
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneRankX
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneTail
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneTorus
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalAssembly
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Homocyclic
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneExist

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFieldCaseIOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J X : Subgroup G),
    GGFieldCase p B Bs x L D J X → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
      ∃ M R U U₁ : Subgroup G, GGFieldCaseData p Bs X M R U U₁ ∧
        ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1

theorem ggFieldCaseIOneInput_of_inputs_quot (hTBM : GGTableBModuleInput) (h43 : GGL43Input)
    (h44 : GGL44iiiInput) (h45 : GGL45IOneInput) (h46 : GGL46IOneInput) (h47 : GGL47IOneInput)
    (h48 : GGL48QuotIOneInput) : GGFieldCaseIOneInput := by
  intro G _ _ p B Bs x L D J X hFC hI1
  obtain ⟨hcfg, hbl5, hXN, hCX, hXn, hXp, hXC⟩ := hFC
  have hI := hcfg.1
  have : Fact p.Prime := ⟨hI.2.2.2.2.2.1.1⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hI.2.2.2.2.2.2.1.2.1
  have hFC : GGFieldCase p B Bs x L D J X := ⟨hcfg, hbl5, hXN, hCX, hXn, hXp, hXC⟩
  have hL43 := h43 G p B Bs x L D J X hFC
  have hL44 := ggL44i_of_ggL43 hBs hxBs hXN hXp hL43
  obtain ⟨B₂, hM⟩ := hTBM G p B Bs x L D J hcfg
  have hL44ii := ggL44ii_of_ggL43 hFC hM hL43 hL44
  obtain ⟨d, y, K, hK⟩ := h44 G p B Bs x L D J X B₂ hFC hM hL43 hL44 hL44ii
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hBsC : Bs ≤ Subgroup.centralizer (B₁ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact mul_comm_of_isElemAbelian hBs hc.1 hb
  obtain ⟨U, hUp, hBsU, hUC, hUmax⟩ := exists_maxPSubgroup_of_le (isPGroup_of_isElemAbelian hBs)
    hBsC
  have hsetup : GGL45Setup p Bs X U := ⟨hUC, hUp, hUmax, hBsU⟩
  have hd : d ∈ D ⊓ B₁ := hK.1 ▸ Subgroup.mem_zpowers d
  have hUK : U ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf (hUC.trans (Subgroup.centralizer_le_normalizer _))
      (le_normalizer_zpowers_of_le hd.2 hUC)).trans
      (hbl5 X hXN hCX hXn hXp hXC d hd hK.2.1 y K hK.2.2.1 hK.2.2.2.1)
  obtain ⟨U₁, hU₁, hNU₁⟩ :=
    h45 G p B Bs x L D J X B₂ d y K U hFC hI1 hM hL43 hL44 hL44ii hK hsetup hUK
  have hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ :=
    ⟨hFC, hM, hL43, hL44, hL44ii, hK, hsetup, hU₁, hNU₁⟩
  have hL46 := h46 G p B Bs x L D J X B₂ d y K U U₁ hS hI1
  obtain ⟨hab, -, hJU, hΩ₁, -, -⟩ := id hL46
  obtain ⟨R, hRp, hUR, hRM, hRmax⟩ := exists_maxPSubgroup_of_le (H := Subgroup.normalizer
    (B₁ : Set G)) hUp (hUC.trans (Subgroup.centralizer_le_normalizer _))
  have hRU : R ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_of_maxPSubgroup (hRM.trans (ggNormalizer_le_normalizer_centralizer B₁)) hRp hUR
      hUC hUmax
  have hrep := h47 G p B Bs x L D J X B₂ d y K U U₁ hS hI1 hL46 R hRp hRM hRmax hUR
  obtain ⟨⟨S, hSR⟩, -, -⟩ := ggL47 hRp hRmax hUR hRU hU₁.2.1 hab hJU hΩ₁ le_rfl hrep
  have hA := thompsonAbelianSubgroups_eq_of_replacement hRp hUR hU₁.2.1
    (hRU.trans (normalizer_le_normalizer_of_forall_eq hJU)) hab hJU hrep
  have hRsyl : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R := fun Q hQ hRQ => by
    subst hSR
    exact S.is_maximal' hQ hRQ
  obtain ⟨ψ, hψ⟩ := h48 G p B Bs x L D J X B₂ d y K U U₁ hS hI1 hL46 R hRp hRsyl hUR hA
  exact ⟨Subgroup.normalizer (B₁ : Set G), R, U, U₁,
    ⟨rfl, hRp, hRM, hRmax, hUR, hRU, hU₁.2.1, hab, hJU, hΩ₁, hrep⟩, ψ, hψ⟩

theorem ggProp41I1Input_of_input (h : GGFieldCaseIOneInput) : GGProp41I1Input := by
  intro G _ _ p B Bs x L D J hcfg hI1 hbl5 X hXN hCX hXn hXp
  by_contra hXC
  obtain ⟨M, R, U, U₁, hdata, ψ, hψ⟩ :=
    h G p B Bs x L D J X ⟨hcfg, hbl5, hXN, hCX, hXn, hXp, hXC⟩ hI1
  have hI := hcfg.1
  have hβ := hI.2.2.2.2.2.1
  have : Fact p.Prime := ⟨hβ.1⟩
  exact ggFieldCaseData_false hβ.2.1 hI.1 hI.2.1 hdata ψ hψ

theorem ggProp41I1Input_of_noBL5_iOne (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hnb : GGL44iiiNbrInput)
    (hmk : GGL44iiiMarkingInput) (h45 : GGL45IOneInput) (hcore : GGL46CoreIOneInput)
    (hcyc : GGL46CyclicIOneInput) (h48 : GGL48QuotIOneInput) : GGProp41I1Input :=
  ggProp41I1Input_of_input (ggFieldCaseIOneInput_of_inputs_quot hTBM
    (ggL43Input_of_inputs hTB hNN (ggL43ProdInput_of_hard hTBM (ggL43HardInput_of_tableB hTB hTBA)))
    (ggL44iiiInput_of_noBL5 hnb hmk) h45 (ggL46IOneInput_of_tableB hTB hNN hTBM hTBA hcore hcyc)
    (ggL47IOneInput_of_cyclic hcyc) h48)

end CFSG.StandardType

end
