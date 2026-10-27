module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem rckRPG_tag_trichotomy
    (t : StatedLieTag) (n f : ℕ)
    (hadm : StatedLieAdmissible t n 2 f) (hrank : 2 ≤ (ggU t n f).D.rank) :
    RCKClassicalTag t ∨ GGExcFive t := by
  rcases t with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_
  · exact Or.inl (by simp [RCKClassicalTag])
  · exact Or.inl (by simp [RCKClassicalTag])
  · exact Or.inl (by simp [RCKClassicalTag])
  · exact absurd hadm (by simp [StatedLieAdmissible])
  · exact Or.inl (by simp [RCKClassicalTag])
  · exact Or.inl (by simp [RCKClassicalTag])
  · exact absurd hrank (by simp [ggU, lieUniversal, trivialUniversal, SpecialLinear.rootDatum])
  · exact Or.inr (by simp [GGExcFive])
  · exact Or.inr (by simp [GGExcFive])
  · exact Or.inr (by simp [GGExcFive])
  · exact Or.inr (by simp [GGExcFive])
  · exact Or.inr (by simp [GGExcFive])
  · exact absurd hrank (by simp [ggU, lieUniversal, trivialUniversal, SpecialLinear.rootDatum])
  · exact absurd hrank (by simp [ggU, lieUniversal, trivialUniversal, SpecialLinear.rootDatum])
  · exact absurd hadm (by simp [StatedLieAdmissible])
  · exact absurd hrank (by simp [ggU, lieUniversal, trivialUniversal, SpecialLinear.rootDatum])
  · exact absurd hrank (by simp [ggU, lieUniversal, trivialUniversal, SpecialLinear.rootDatum])

theorem rckRootPosKnownFlag_of_at
    (hC : RCKRPAt RCKClassicalTag) (hE : RCKRPAt GGExcFive) :
    RCKRootPosKnownFlag := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L
  intro hpres hodd hprime hne2 habel hB1A hDB1 hcardD hAnorm hmarkG
    hnormJ hinf hpow hAnorm2 hrankA hbot hnormL hmarkL hcompJ hoddJ hLG0 hex hnotD hcompJL
    hisEmpty
  intro R Rm hRJ hRmJ hroot
  intro e heD hene K hcompK hJK hoddK
  unfold GGPresentsG0 at hpres
  have hadm : StatedLieAdmissible t n 2 f := hpres.1.1
  have hrank : 2 ≤ (ggU t n f).D.rank := hpres.1.2
  have hcfg : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e :=
    ⟨hpres, hodd, hprime, hne2, habel, hB1A, hDB1, hcardD, hAnorm, hmarkG,
      hnormJ, hinf, hpow, hAnorm2, hrankA, hbot, hnormL, hmarkL, hcompJ, hoddJ, hLG0, hex,
      hnotD, hcompJL, hisEmpty, hRJ, hRmJ, hroot, heD, hene, hcompK, hJK, hoddK⟩
  by_cases hcls : RCKClassicalTag t
  · exact hC X t n f ψ p G₀ A B₁ D J L R Rm K e hcls hcfg
  · by_cases hexc : GGExcFive t
    · exact hE X t n f ψ p G₀ A B₁ D J L R Rm K e hexc hcfg
    · exact absurd (rckRPG_tag_trichotomy t n f hadm hrank) (fun h => h.elim hcls hexc)

theorem rckRootPosKnownII_of_at
    (hC : RCKRPIIAt RCKClassicalTag) (hE : RCKRPIIAt GGExcFive) :
    RCKRootPosKnownII := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L
  intro hrow hpres hodd hprime hne2 habel hB1A hDB1 hcardD hAnorm hmarkG
    hnormJ hinf hpow hAnorm2 hrankA hbot hnormL hmarkL hcompJ hoddJ hLG0 hex hnotD hcompJL
    hisEmpty
  intro R Rm hRJ hRmJ hroot hcardR
  intro e heD hene K hcompK hJK hoddK
  unfold GGPresentsG0 at hpres
  have hadm : StatedLieAdmissible t n 2 f := hpres.1.1
  have hrank : 2 ≤ (ggU t n f).D.rank := hpres.1.2
  have hcfg : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e :=
    ⟨hpres, hodd, hprime, hne2, habel, hB1A, hDB1, hcardD, hAnorm, hmarkG,
      hnormJ, hinf, hpow, hAnorm2, hrankA, hbot, hnormL, hmarkL, hcompJ, hoddJ, hLG0, hex,
      hnotD, hcompJL, hisEmpty, hRJ, hRmJ, hroot, heD, hene, hcompK, hJK, hoddK⟩
  by_cases hcls : RCKClassicalTag t
  · exact hC X t n f ψ p G₀ A B₁ D J L R Rm K e hcls hrow hcardR hcfg
  · by_cases hexc : GGExcFive t
    · exact hE X t n f ψ p G₀ A B₁ D J L R Rm K e hexc hrow hcardR hcfg
    · exact absurd (rckRPG_tag_trichotomy t n f hadm hrank) (fun h => h.elim hcls hexc)

end CFSG.StandardType.RCKRP
