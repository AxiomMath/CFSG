module

public import CFSG.LocalAnalysis.StandardType.GGStdPosAutDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosAutWeyl
public import CFSG.LocalAnalysis.StandardType.GGStdPosRefl
public import CFSG.LocalAnalysis.StandardType.GGStdPosTagData
public import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerHolds

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType

private theorem ggStdPosAut_exists_pow_eq_one_ne_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) : ∃ ζ : (GaloisField 2 f)ˣ, ζ ^ p = 1 ∧ ζ ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, GaloisField.card 2 f (by omega)]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := (GaloisField 2 f)ˣ) p (hcard ▸ hpf)
  refine ⟨ζ, hζ ▸ pow_orderOf_eq_one ζ, fun h => hp.one_lt.ne' ?_⟩
  rw [← hζ, h, orderOf_one]

theorem ggKGPosNoTrivRootStmt_holds :
    GGKGPosNoTrivRootStmt := by
  intro G _ _ p Bs X t n f ψ hloc hstd
  obtain ⟨⟨hp, -, hadm, hrank⟩, ⟨hker, -, ht, hpf⟩, ⟨-, -, hC3⟩, -, -⟩ := hloc
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, x, C, O, hE⟩ := ggStdPos_bruhatData hrank ht
  obtain ⟨ζ, hζ, hζ1⟩ := ggStdPosAut_exists_pow_eq_one_ne_one hp hadm.2.1 hpf
  exact ggStdPos_noTrivRoot hct hext hBU hE hdiv ψ hker hstd hC3 hζ hζ1

theorem ggKGPosAutWeylStmt_holds :
    GGKGPosAutWeylStmt := by
  intro G _ _ p Bs X t n f ψ hloc hstd ν hν
  obtain ⟨⟨hp, hp2, hadm, hrank⟩, ⟨hker, hrange, ht, hpf⟩, ⟨hel, hN, hC3⟩, -, -⟩ := hloc
  obtain ⟨hdiv, ⟨nn, H, hct, hext, hBU⟩, x, C, O, hE⟩ := ggStdPos_bruhatData hrank ht
  obtain ⟨ζ, hζ, hζ1⟩ := ggStdPosAut_exists_pow_eq_one_ne_one hp hadm.2.1 hpf
  have h2 : 2 ≤ (ggU t n f).D.rank := by
    rw [lieUniversal_rank_eq_bnRank t n 2 f Nat.prime_two hadm hrank]
    omega
  subst hrange
  exact ggStdPos_exists_autWeyl hct hext hBU hE hdiv h2 hζ hζ1 hν
    (fun u i => (ggRootKerStmt_holds t n f hadm hrank ht p hp hp2 hpf ν hν u i).2) ψ hker hstd
    hN hel.2 hC3

theorem ggKGPosReflStmt_holds :
    GGKGPosReflStmt := by
  intro G _ _ p Bs X t n f ψ hloc hstd ν ε hν hε i
  obtain ⟨⟨hp, -, hadm, hrank⟩, ⟨hker, -, ht, -⟩, ⟨hel, -, -⟩, -, -⟩ := hloc
  obtain ⟨x, C, O, hE, hlin⟩ := ggRankOneModel_of_tag ht hadm hrank
  exact ggStdPos_isReflection hE hlin ψ hker hp hstd hel.2 hν ε hε i

end CFSG.StandardType

end
