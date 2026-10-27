module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecNS
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecIn
public import CFSG.Quasithin.Background.RonanE111Core

public section

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Quasithin CFSG.Quasithin.A1b

theorem nParam_le_of_allNS {Q : Type} [Group Q] [Finite Q] {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn : 1 ≤ n) (hE : EBound S (n : ℕ∞)) (hKQ : CFSG.SectionRank.IsKGroupCat Q)
    (hrk : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2)
    (hNS : AllNS S Q) {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) :
    E1.nParam (⊤ : Subgroup Q) ≤ (n : ℕ∞) :=
  RonanE111.nParam_le_of_hypT RonanE111.e111CoreT hn hT
    fun M N hN hNM hMsub _ hsimple hnab =>
      sectionBound hE hKQ hrk hT.2.1 hNM hsimple hnab
        (hNS _ hsimple hnab ⟨M, N, hN, hNM,
          Subgroup.IsSubnormal.trans hNM (Subgroup.Normal.isSubnormal hN) hMsub, hMsub,
          ⟨MulEquiv.refl _⟩⟩).some

end CFSG.Quasithin.H13.P31Sec
