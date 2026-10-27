module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDLowRank
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDMinusSplit
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDNsRows

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBTorRelD_holds :
    GGTBTorRelD := by
  intro p hp hp2 lab hlab hrow
  obtain ⟨tag, ℓ, n⟩ := lab
  obtain ⟨hn1, hlab'⟩ := hlab
  rcases hrow with ⟨htag, hpn, hodd⟩ | ⟨htag, hpn⟩
  · dsimp only at htag hpn hodd hn1
    subst htag
    have h3 : 3 ≤ ℓ := hlab'
    rcases Nat.lt_or_ge ℓ 5 with h | h
    · have hℓ : ℓ = 3 := by
        obtain ⟨j, hj⟩ := hodd
        omega
      subst hℓ
      exact largeEvenLabelAll_relD_D3 hp hp2 hpn
    · exact largeEvenLabelAll_relD_D_ns hp hp2 hn1 h hodd hpn
  · dsimp only at htag hpn hn1
    subst htag
    have h2 : 2 ≤ ℓ := hlab'
    rcases hpn with hpn | ⟨hpn, heven⟩
    · rcases (show ℓ = 2 ∨ ℓ = 3 ∨ 4 ≤ ℓ by omega) with h | h | h
      · subst h
        exact largeEvenLabelAll_relD_twD2 hp hp2 hn1 (Or.inl hpn)
      · subst h
        exact largeEvenLabelAll_relD_twD3 hp hp2 hn1 hpn
      · exact largeEvenLabelAll_relD_twD_split hp hp2 hn1 h hpn
    · rcases (show ℓ = 2 ∨ 4 ≤ ℓ by obtain ⟨j, hj⟩ := heven; omega) with h | h
      · subst h
        exact largeEvenLabelAll_relD_twD2 hp hp2 hn1 (Or.inr hpn)
      · exact largeEvenLabelAll_relD_twD_ns hp hp2 hn1 h heven hpn

end CFSG.StandardType
