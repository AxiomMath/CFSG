module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

section MaxJoin

variable {G : Type} [Group G] [Finite G]

theorem ggAutomizerJoin_singleton (L Bs K : Subgroup G) :
    ggAutomizerJoin L Bs {K} = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
  simp only [ggAutomizerJoin, Finset.iSup_singleton]

theorem exists_ggMaximalJoin {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J) :
    ∃ 𝒦 : Finset (Subgroup G), GGMaximalJoin p B Bs x L D J 𝒦 := by
  let S : Set (Finset (Subgroup G)) :=
    {𝒦 | GGNbrSet p B x D J 𝒦 ∧ GGWeylReflectionGroup p (ggAutomizerJoin L Bs 𝒦)}
  have hSfin : S.Finite := by
    haveI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
    haveI : Fintype (Finset (Subgroup G)) := Finset.fintype
    haveI : Finite (Finset (Subgroup G)) := Fintype.finite inferInstance
    exact Set.toFinite S
  have hSne : S.Nonempty := by
    obtain ⟨y, K, hK⟩ := exists_ggNbr hR.1.1.2.2.2.2.2.2.2 hR.1.2.2
    refine ⟨{K}, ?_⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Finset.card_singleton]; omega
    · intro K' hK'
      rw [Finset.mem_singleton] at hK'
      subst hK'
      exact ⟨y, hK⟩
    · rw [ggAutomizerJoin_singleton]
      exact hR.2.2.2.2.1 y K hK (hW y K hK) (Or.inr hW)
  obtain ⟨𝒦, h𝒦S, hmax⟩ :=
    Set.exists_max_image S (fun 𝒦 => Nat.card (ggAutomizerJoin L Bs 𝒦)) hSfin hSne
  exact ⟨𝒦, h𝒦S.1, h𝒦S.2, fun 𝒦' h1 h2 => hmax 𝒦' ⟨h1, h2⟩⟩

end MaxJoin

end CFSG.StandardType

end
