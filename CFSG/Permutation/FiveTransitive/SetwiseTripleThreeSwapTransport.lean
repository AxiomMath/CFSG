module

public import CFSG.Permutation.FiveTransitive.SetwisePGroupSylowCorrection
public import CFSG.Permutation.FiveTransitive.CommutingTriplePreimageSylow
public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm

public section

namespace CFSG

namespace FiveTransitive.SetwiseTripleThreeSwapTransport

open MulAction FixedNormalizerAction

theorem exists_conjugate
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)] [DecidableEq (Fixed (X := X) Q)]
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
      (toPermHom (Normalizer Q) (Fixed (X := X) Q))))
    (H : Subgroup G) (hH : IsPGroup 2 H)
    (hpreserves : ∀ h : H, ∀ y : X, y ∈ fixedPoints Q X ↔ h.val • y ∈ fixedPoints Q X)
    (a x u : G) (haH : a ∈ H) (hxH : x ∈ H) (huH : u ∈ H)
    (ha : a ^ 2 = 1) (hx : x ^ 2 = 1) (hu : u ^ 2 = 1)
    (hax : Commute a x) (hau : Commute a u) (hxu : Commute x u)
    (hfa : ∀ y ∈ fixedPoints Q X, a • y = y)
    (hlocal : (fixedBy X x ∩ fixedPoints Q X).ncard = 5) :
    ∃ c : G, (∀ y : X, y ∈ fixedPoints Q X ↔ c • y ∈ fixedPoints Q X) ∧
      ∀ g ∈ ({a, x, u} : Set G), c * g * c⁻¹ ∈
        (SylowPreimageNormalizer.ambient
          (toPermHom (Normalizer Q) (Fixed (X := X) Q))
          (ThreeSwapTwoGroup.subgroup e) P).map (Normalizer Q).subtype := by
  obtain ⟨k, hk⟩ := SetwisePGroupSylowCorrection.exists_correction
    (fixedPoints Q X) S H hH hpreserves
  have hkN (h : H) : k.val * h.val * k.val⁻¹ ∈ Normalizer Q := by
    simpa only [hS] using (hk h).1
  let ψ : H →* Normalizer Q :=
    ((MulAut.conj k.val).toMonoidHom.comp H.subtype).codRestrict (Normalizer Q) hkN
  let aH : H := ⟨a, haH⟩
  let xH : H := ⟨x, hxH⟩
  let uH : H := ⟨u, huH⟩
  have hsquare (h : H) (hsq : h.val ^ 2 = 1) : (ψ h) ^ 2 = 1 := by
    rw [← map_pow, (show h ^ 2 = 1 from Subtype.ext hsq), map_one]
  have hcomm (h j : H) (hc : Commute h.val j.val) : Commute (ψ h) (ψ j) :=
    (show Commute h j from Subtype.ext hc.eq).map ψ
  have hact (h : H) (y : X) (hy : y ∈ fixedPoints Q X) :
      (ψ h).val • y = h.val • y := (hk h).2 y hy
  have hfa' : toPermHom (Normalizer Q) (Fixed (X := X) Q) (ψ aH) = 1 := by
    apply Equiv.ext
    intro y
    apply Subtype.ext
    exact (hact aH y.val (fixed_eq (X := X) Q ▸ y.property)).trans (hfa y.val (fixed_eq (X := X) Q ▸ y.property))
  have hinter : fixedBy X (ψ xH).val ∩ fixedPoints Q X = fixedBy X x ∩ fixedPoints Q X := by
    ext y
    constructor
    · intro hy
      exact ⟨(hact xH y hy.2).symm.trans hy.1, hy.2⟩
    · intro hy
      exact ⟨(hact xH y hy.2).trans hy.1, hy.2⟩
  have hfx : (toPermHom (Normalizer Q) (Fixed (X := X) Q) (ψ xH)).IsSwap :=
    (SevenFivePermutationSquare.isSwap_and_square hseven _
      ((FixedNormalizerLocalCard.fixed_card Q (ψ xH)).trans (by rw [hinter]; exact hlocal))).1
  obtain ⟨d, hd⟩ := CommutingTriplePreimageSylow.exists_conjugate
    (by simpa only [Nat.card_eq_fintype_card] using hseven) e
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (MonoidHom.range_eq_top.mp himage) P
    (ψ aH) (ψ xH) (ψ uH) (hsquare aH ha) (hsquare xH hx) (hsquare uH hu)
    (hcomm aH xH hax) (hcomm aH uH hau) (hcomm xH uH hxu) hfa' hfx
  refine ⟨d.val * k.val, ?_, ?_⟩
  · intro y
    have hkfix (z : X) (hz : z ∈ fixedPoints Q X) : k.val • z = z :=
      (mem_fixingSubgroup_iff G).mp k.property z hz
    constructor
    · intro hy
      rw [mul_smul, hkfix y hy]
      exact FixedSetNormalizerPerm.smul_mem_fixedPoints G X Q d.val d.property hy
    · intro hy
      have hky : k.val • y ∈ fixedPoints Q X := by
        have ht := FixedSetNormalizerPerm.smul_mem_fixedPoints G X Q d.val⁻¹ (d⁻¹).property hy
        simpa only [mul_smul, inv_smul_smul] using ht
      have hki := (mem_fixingSubgroup_iff G).mp
        ((fixingSubgroup G (fixedPoints Q X)).inv_mem k.property) (k.val • y) hky
      have he : y = k.val • y := by simpa only [inv_smul_smul] using hki
      rw [he]
      exact hky
  · intro g hg
    have hgin : g ∈ H := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl <;> assumption
    have hgen : ψ ⟨g, hgin⟩ ∈ Subgroup.closure ({ψ aH, ψ xH, ψ uH} : Set (Normalizer Q)) := by
      apply Subgroup.subset_closure
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      rcases hg with hg | hg | hg
      · left; congr 1; exact Subtype.ext hg
      · right; left; congr 1; exact Subtype.ext hg
      · right; right; congr 1; exact Subtype.ext hg
    have hm : d.val * (k.val * g * k.val⁻¹) * d.val⁻¹ ∈
        (SylowPreimageNormalizer.ambient
          (toPermHom (Normalizer Q) (Fixed (X := X) Q))
          (ThreeSwapTwoGroup.subgroup e) P).map (Normalizer Q).subtype :=
      ⟨d * ψ ⟨g, hgin⟩ * d⁻¹, hd _ hgen, rfl⟩
    convert hm using 1
    group

end FiveTransitive.SetwiseTripleThreeSwapTransport

end CFSG
