module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32S2Defs
public import CFSG.Quasithin.Background.F918C9
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Vol2.Ch12Sec6L32Claim

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique S126

attribute [local instance] commGroupOfFact

theorem claim12_6_32_of_leaves (inp : Inputs32) (hKer : LeafKer) (hCen : LeafCenter)
    (hMod : LeafModule inp) (hNN : LeafNoNat) (hF7 : LeafF7) (hComm : LeafComm)
    (hBr : LeafBridge) : Claim12_6_32 := by
  intro G _ _ T L V _ F hH hZ H K hIs h1 h
  have c : Ctx32 T L V F H K := ⟨hH, hZ, hIs, h1, h⟩
  have hK₀ : conjClosure K T = K := h1.1
  have hh := h.toHypF98.toHypF91
  have hUQ : conjClosure F.V5 H ≤ pCoreOf 2 H := hh.conjClosure_Vp_le_pCoreOf
  have hQne : pCoreOf 2 H ≠ ⊥ := by
    intro hbot
    apply hh.V₁_ne_bot
    have : F.V1 ≤ pCoreOf 2 H := hh.V₁_le_Vp.trans ((le_conjClosure F.V5 H).trans hUQ)
    rw [hbot] at this
    exact le_bot_iff.1 this
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian hQne
  obtain ⟨hPSL, hZ3, hAlt2⟩ := hCen G T L V F H K c
  have hker := hKer G T V L F.V1 F.V5 H K h
  obtain ⟨I, hV₁I, hIU, hI, hKI, hZ3', hkerI, hcases⟩ :=
    hMod G T L V F H K h hSQ hK₀ hker hPSL hZ3 (fun h3 => (hAlt2 h3).1)
  obtain ⟨hHKT, hL1⟩ := hAlt2 hZ3'
  rcases hcases with ⟨hHI, hnat⟩ | ⟨t, htT, hnat, hinf, hsup⟩
  · exact (hNN inp.noff G T L V F H K c I hV₁I hIU hkerI hHI hnat).elim
  ·
    have hcomm := hComm G T L V F H K h (by rw [hK₀]; exact hL1)
    have hNoK : NoFFK (conjClosure K T ⊔ T) (pCoreOf 2 H) (conjClosure K T) := by
      rw [hK₀]
      exact fun W _ _ hW ρ hρQ hρK => inp.noff G T L V F hH hZ H K hIs h1 h W hW ρ hρQ hρK
    have h7 := hF7 G T V L F.V1 F.V5 H K h I hV₁I hIU (by rw [hK₀]; exact hI) hNoK
    have hV₁U : F.V1 ≤ conjClosure F.V5 H := hh.V₁_le_Vp.trans (le_conjClosure F.V5 H)
    have hIH : conjClosure I H = conjClosure F.V5 H :=
      eq_of_secImg_eq (A := Subgroup.normalizer (F.V1 : Set G)) (B := F.V1)
        (hV₁I.trans (le_conjClosure I H)) hV₁U (h.conjClosure_le_normalizer_V₁ hIU)
        (h.conjClosure_le_normalizer_V₁ (le_conjClosure F.V5 H)) (h7.trans hcomm)
    obtain ⟨t', ht', hinf', hsup', hnat'⟩ :=
      hBr G T L V F H K h I hV₁I hIU hIH ⟨t, htT, hnat, hinf, hsup⟩
    exact ⟨I, t', ht', hV₁I, hIU, hKI, hinf', hsup', hnat'⟩

end CFSG.Quasithin.H13.L1232S2
