module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinMemberETwistedE6Defs
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberOrthogonal
import CFSG.LocalAnalysis.StandardType.GGTBFixNbrXInnerWeyl

public noncomputable section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


theorem ggSecFiveJoinMemberAt_E_of_twistedE6E7
    (hTB : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput) (hTw : GGSecFiveTwistedE6E7MemberInput) :
    GGSecFiveJoinMemberAt GGIsWeylMatrixE := by
  classical
  have hWA : GGTBFixNbrXInput := ggTBFixNbrXInput_of_innerWeyl hWI
  intro G _ _ p B Bs x L D J 𝒦 hcfg hReg hARow hQTwo ι M e hpres hE hSix t n f ψ hψ hJoin
  rcases exists_selected_E_member_or_E7_source hTB hWA hL1 hRk1 hGen hOrb hL2 hPair hNbr
      hcfg hReg hARow hQTwo hpres hE hSix t n f ψ hψ hJoin with hSelected |
      ⟨hmark, q, _hq4, _hpq, sigma, hM, _hSource⟩
  · obtain ⟨r₀, hr₀A, hr₀C, t', n', f', lambda, hadm, hrank, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩ := hSelected
    exact ⟨r₀, hr₀A, hr₀C, L, Or.inl rfl, t', n', f', lambda, hadm, hrank, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩
  · obtain ⟨r₀, hr₀A, hr₀C, t', n', f', lambda, hadm, hrank, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩ :=
      hTw hTB hWI hL1 hRk1 hGen hOrb hL2 hPair hNbr
        G p B Bs x L D J 𝒦 hcfg hReg hARow hQTwo ι M e hpres ⟨sigma, hM⟩ hSix
        t n f ψ hψ hJoin hmark
    exact ⟨r₀, hr₀A, hr₀C, L, Or.inl rfl, t', n', f', lambda, hadm, hrank, hker, hrange,
      k, hk, hfin, hchar, delta, model, himage⟩

end CFSG.StandardType

end
