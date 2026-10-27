module

public import CFSG.Permutation.FiveTransitive.CentralizingThreeSwapPreimage
public import CFSG.Permutation.FiveTransitive.CentralizingThreeSwapCardBound

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicFullCentralizerCardBound

open MulAction FixedNormalizerAction

theorem card_le_four
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (Q : Subgroup G) (hcyclic : IsCyclic Q)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (himage : ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)).map
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤)
    (heven : ∀ g : G, Equiv.Perm.sign (toPerm g : Equiv.Perm X) = 1)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1) :
    Nat.card Q ≤ 4 := by
  classical
  let _ := Fintype.ofFinite (Fixed (X := X) Q)
  obtain ⟨e⟩ := (Function.Embedding.nonempty_iff_card_le (α := Fin 6)
    (β := Fixed (X := X) Q)).mpr (by simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_fin, hseven] using (by decide : 6 ≤ 7))
  obtain ⟨B, hB, _, hcentral, hmap, _⟩ :=
    CentralizingThreeSwapPreimage.exists_subgroup Q hcyclic S hS himage e
  have hle : Nat.card Q ≤ 7 := CentralizingThreeSwapCardBound.card_le_seven
    Q B hB e hmap (fun b => heven b.val.val) hmax (by
      intro b q
      exact (Subgroup.mem_centralizer_iff.mp (hcentral b.property) q.val q.property).symm) hfree
  have hQp : IsPGroup 2 Q := by rw [← hS]; exact S.isPGroup'.map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  by_cases hkle : k ≤ 2
  · interval_cases k <;> norm_num [hk]
  · have h8 : 8 ∣ Nat.card Q := by
      rw [hk]
      exact Nat.pow_dvd_pow 2 (by omega : 3 ≤ k)
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have := Nat.le_of_dvd hpos h8
    omega

end FiveTransitive.CyclicFullCentralizerCardBound

end CFSG
