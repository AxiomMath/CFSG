module

public import CFSG.RankThree.PartOne.N143.SectionRankBound
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.PartOne Subgroup

theorem _root_.CFSG.RankThree.PartOne.Census3.TheoremThreeList.of_mulEquiv {G H : Type} [Group G]
    [Group H] (e : G ≃* H) (h : Census3.TheoremThreeList G) : Census3.TheoremThreeList H := by
  have key : ∀ {X : Type} [Group X], Nonempty (G ≃* X) → Nonempty (H ≃* X) :=
    fun ⟨f⟩ => ⟨e.symm.trans f⟩
  have iso : ∀ {d : TauCeti.LieTypeIndex}, Census3.IsoLie G d → Census3.IsoLie H d :=
    fun ⟨hv, hf⟩ => ⟨hv, key hf⟩
  have i7 : Census3.ThmThreeItem7 G → Census3.ThmThreeItem7 H :=
    Or.imp (fun ⟨q, a, c⟩ => ⟨q, a, iso c⟩) <| Or.imp (fun ⟨m, c⟩ => ⟨m, iso c⟩) <|
      Or.imp (fun ⟨q, a, c⟩ => ⟨q, a, c.imp iso <| Or.imp iso <| Or.imp iso <| Or.imp iso <|
        Or.imp iso <| Or.imp iso iso⟩) <| Or.imp (fun ⟨m, c⟩ => ⟨m, iso c⟩) iso
  have i8 : Census3.ThmThreeItem8 G → Census3.ThmThreeItem8 H :=
    fun ⟨q, a, c⟩ => ⟨q, a, c.imp iso <| Or.imp iso iso⟩
  have i9 : Census3.ThmThreeItem9 G → Census3.ThmThreeItem9 H :=
    fun ⟨q, a, b, c⟩ => ⟨q, a, b, c.imp iso <| Or.imp iso <| Or.imp iso <| Or.imp iso <|
      Or.imp iso <| Or.imp iso iso⟩
  exact Or.imp (fun ⟨q, a, b, c⟩ => ⟨q, a, b, iso c⟩) (Or.imp (fun ⟨q, a, b, c⟩ =>
    ⟨q, a, b, c.imp iso iso⟩) (Or.imp iso (Or.imp (fun ⟨q, a, b, c⟩ =>
    ⟨q, a, b, c.imp iso <| Or.imp iso <| Or.imp iso iso⟩) (Or.imp (fun ⟨n, a, b, c⟩ =>
    ⟨n, a, b, key c⟩) (Or.imp (fun ⟨s, hs, c⟩ => ⟨s, hs, key c⟩) (Or.imp i7 (Or.imp i8 i9))))))) h

structure TheoremThreeListHyp (G : Type) [Group G] [Finite G] : Prop where
  isSimpleGroup : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kGroup : CFSG.IsKGroup G
  onList : Census3.TheoremThreeList G

namespace TheoremThreeListHyp

variable {G : Type} [Group G] [Finite G]

theorem exists_index (h : TheoremThreeListHyp G) : ∃ i : TauCeti.CFSGIndex, Nonempty (G ≃* i.Group) := by
  have : IsSimpleGroup G := h.isSimpleGroup
  let e : (⊤ : Subgroup G) ⧸ (⊥ : Subgroup (⊤ : Subgroup G)) ≃* G :=
    QuotientGroup.quotientBot.trans Subgroup.topEquiv
  have : IsSimpleGroup ((⊤ : Subgroup G) ⧸ (⊥ : Subgroup (⊤ : Subgroup G))) := e.isSimpleGroup
  obtain ⟨i, ⟨f⟩⟩ := h.kGroup ⊤ ⊥ this
  exact ⟨i, ⟨e.symm.trans f⟩⟩

end TheoremThreeListHyp

@[expose] def SectionListBound : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsKGroup L → CFSG.Assembly.evenRank L ≤ 3 →
    ∀ (H : Subgroup L) (M : Type) [Group M] [Finite M], CFSG.IsQuasisimple M → ∀ π : H →* M,
      Function.Surjective π →
        Census3.TheoremThreeList (M ⧸ center M) ∧
          ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ → ¬ ℓ ∣ Nat.card (center M)

namespace SectionListBound

theorem listHyp (h : SectionListBound) {L : Type} [Group L] [Finite L] (hK : CFSG.IsKGroup L)
    (he : CFSG.Assembly.evenRank L ≤ 3) (H : Subgroup L) {M : Type} [Group M] [Finite M]
    (hq : CFSG.IsQuasisimple M) (π : H →* M) (hπ : Function.Surjective π) :
    TheoremThreeListHyp (M ⧸ center M) := by
  have hMK : CFSG.IsKGroup M := isKGroup_of_section hK H π hπ
  exact ⟨hq.2.1, hq.2.2, CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hMK _,
    (h L hK he H M hq π hπ).1⟩

end SectionListBound

end CFSG.RankThree.PartOne.N143
