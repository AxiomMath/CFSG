module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326NoComp
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompCent
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompOut
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

theorem comp_case_top (h1 : K326P1) (hO : SL3Out) (hG : SL3Gen) : K326CompCase := by
  intro G _ _ hK hc n hn P hP e hz M a ha ha2 hM hex
  obtain ⟨L, hL⟩ := hex
  have h : Hyp326 G n P := ⟨hK, hc, hn, hP, e, hz⟩
  have hS : ∀ L' : Subgroup G, CFSG.Open.IsComponentOf L' ⊤ → IsSL3pi ↥L' :=
    fun L' hL' => h1 G hK hc n hn P hP e hz L' hL'
  have hu : ∀ L₁ L₂ : Subgroup G, CFSG.Open.IsComponentOf L₁ ⊤ →
      CFSG.Open.IsComponentOf L₂ ⊤ → L₁ = L₂ :=
    fun L₁ L₂ h₁ h₂ => comp_unique h hS h₁ h₂
  have hLn : L.Normal := comp_normal hu hL
  have hSL : IsSL3pi ↥L := hS L hL
  have hN := normalizer_le_normalizer_jOf h
  have hNM : Subgroup.normalizer (jOf P : Set G) ≤ M := le_sup_left.trans hM
  have hCa : Subgroup.centralizer ({a} : Set G) ≤ M := le_sup_right.trans hM
  have hPM : P ≤ M := hN.1.trans hNM
  have hNPM : Subgroup.normalizer (P : Set G) ≤ M := hN.2.trans hNM
  have hCL : Subgroup.centralizer (L : Set G) ≤ M :=
    (comp_centralizer_le_pCore h hL (fun L' hL' => hu L' L hL' hL) hSL.card_center).trans
      ((pCore_le_sylow hP).trans hPM)
  have hLM : L ≤ M := comp_L_le hG h hLn hSL ha ha2 hPM hCa
  exact comp_top_of_le hO h hLn hSL hPM hLM hCL hNPM

theorem K326P2S_of_inputs (h1 : K326P1) (hO : SL3Out) (hG : SL3Gen) : K326P2S :=
  K326P2S_of_noComp (comp_case_top h1 hO hG)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
