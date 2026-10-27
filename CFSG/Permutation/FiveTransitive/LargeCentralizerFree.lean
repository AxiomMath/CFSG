module

public import CFSG.Permutation.FiveTransitive.CentralFreeFixedBound
public import CFSG.Permutation.FiveTransitive.TwoGroupCosetFixedBound
public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement

public section

namespace CFSG

namespace FiveTransitive.LargeCentralizerFree

open MulAction NormalizerFixedComplement

theorem free
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (B : Subgroup (Normalizer Q)) (hB : IsPGroup 2 B)
    (n : ℕ) (hQ : n < Nat.card Q)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ n)
    (hcentral : ∀ b : B, ∀ q : Q, Commute b.val.val q.val)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1) :
    ∀ (b : B) (z : Domain (X := X) Q), b • z = z → b = 1 := by
  have hcard : Nat.card (Inside Q) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv
  have hbound (b : B) (hb : b ≠ 1) : (fixedBy X b.val).ncard ≤ n := by
    apply TwoGroupCosetFixedBound.fixed_le n ?_ B hB b hb
    intro t ht
    exact hmax t.val ((orderOf_injective (Normalizer Q).subtype Subtype.val_injective t).trans ht)
  have hcent (q : Inside Q) (b : B) : Commute q.val b.val := by
    exact Subtype.ext (hcentral b ⟨q.val.val, q.property⟩).symm.eq
  have hfreeI (q : Inside Q) (z : X) (hz : z ∉ fixedPoints Q X)
      (hfix : q.val • z = z) : q = 1 := by
    have he := hfree ⟨q.val.val, q.property⟩ z hz hfix
    exact Subtype.ext (Subtype.ext (congrArg (fun q : Q => q.val) he))
  have hall := CentralFreeFixedBound.semiregular B (Inside Q) (fixedPoints Q X) n
    (by omega) hbound hcent hfreeI
  intro b z hz
  exact hall b z.val z.property (congrArg Subtype.val hz)

end FiveTransitive.LargeCentralizerFree

end CFSG
