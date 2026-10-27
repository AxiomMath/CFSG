module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.QuasithinUnique (IsSylowTwoOf)

theorem k331At_of_overgroups {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup L)
    (h : ∀ T Y : Subgroup L, IsSylowTwoOf T ⊤ → T ≤ Y → Y ≠ ⊤ → ¬ 20160 ∣ Nat.card Y) :
    K331At L := by
  intro T hT K hK hTK
  by_cases hKtop : K = ⊤
  · exact Or.inl hKtop
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨hle, hP, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
    have hd : 20160 ∣ Nat.card K := dvd_card_of_isAlt_eight hK
    have hN : Subgroup.normalizer (K : Set L) ≠ ⊤ := by
      intro hN
      haveI : K.Normal := Subgroup.normalizer_eq_top_iff.mp hN
      rcases hs.eq_bot_or_eq_top_of_normal K with hb | ht
      · rw [hb, Subgroup.card_bot] at hd
        omega
      · exact hKtop ht
    exact h T _ ⟨hle, hP, hidx⟩ hTK hN
      (hd.trans (Subgroup.card_dvd_of_le Subgroup.le_normalizer))

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
