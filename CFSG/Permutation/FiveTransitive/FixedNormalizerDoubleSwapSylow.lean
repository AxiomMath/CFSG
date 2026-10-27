module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerCompatibleSylow
public import CFSG.Permutation.FiveTransitive.SevenDoubleSwapEmbedding
public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.FixedNormalizerDoubleSwapSylow

open MulAction FixedNormalizerAction

theorem exists_sylow
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (y : Normalizer Q) (hy : orderOf y.val = 2)
    (hlocal : (fixedBy X y.val ∩ fixedPoints Q X).ncard = 3) :
    ∃ (e : Fin 6 ↪ Fixed (X := X) Q)
      (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let V := ThreeSwapTwoGroup.subgroup e
      let B := SylowPreimageNormalizer.ambient f V P
      f y = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∧
      IsPGroup 2 B ∧ Inside Q ≤ B ∧ y ∈ B ∧ B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f = Subgroup.normalizer (V : Set _) ∧
      ∃ x z : B, f x.val = Equiv.swap (e 0) (e 1) ∧ f z.val = Equiv.swap (e 4) (e 5) := by
  classical
  let _ := Fintype.ofFinite (Fixed (X := X) Q)
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hyN : orderOf y = 2 := (Subgroup.orderOf_coe y).symm.trans hy
  have hy2 : y ^ 2 = 1 := hyN ▸ pow_orderOf_eq_one y
  obtain ⟨e, he⟩ := SevenDoubleSwapEmbedding.exists_embedding hseven (f y)
    (by rw [← map_pow, hy2, map_one]) ((FixedNormalizerLocalCard.fixed_card Q y).trans hlocal)
  have hQp : IsPGroup 2 Q := by rw [← hS]; exact S.isPGroup'.map _
  have hyp : IsPGroup 2 (Subgroup.zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hyN, pow_one])
  let R := Inside Q ⊔ Subgroup.zpowers y
  have hIp : IsPGroup 2 (Inside Q) := hQp.comap_subtype
  have hRp : IsPGroup 2 R := hIp.to_sup_of_normal_left hyp
  let A := R.map (Normalizer Q).subtype
  have hQA : Q ≤ A := by
    intro q hq
    exact ⟨⟨q, Q.le_normalizer hq⟩, (le_sup_left : Inside Q ≤ R) hq, rfl⟩
  have hyA : y.val ∈ A :=
    ⟨y, (le_sup_right : Subgroup.zpowers y ≤ R) (Subgroup.mem_zpowers y), rfl⟩
  have hyV : f y ∈ ThreeSwapTwoGroup.subgroup e := by
    rw [he]
    exact (ThreeSwapTwoGroup.subgroup e).mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  obtain ⟨P, hp, hIP, hyP, hm, hk, _, hn⟩ := FixedNormalizerCompatibleSylow.exists_with_element
    Q S hS himage (ThreeSwapTwoGroup.subgroup e) (ThreeSwapTwoGroup.isTwoGroup e).1
      A (hRp.map _) hQA y hyA hyV
  let B := SylowPreimageNormalizer.ambient f (ThreeSwapTwoGroup.subgroup e) P
  have h0 : Equiv.swap (e 0) (e 1) ∈ B.map f := by rw [hm]; exact Subgroup.subset_closure (by simp)
  have h2 : Equiv.swap (e 4) (e 5) ∈ B.map f := by rw [hm]; exact Subgroup.subset_closure (by simp)
  obtain ⟨x, hx, hxf⟩ := h0
  obtain ⟨z, hz, hzf⟩ := h2
  exact ⟨e, P, he, hp, hIP, hyP, hm, hk, hn, ⟨x, hx⟩, ⟨z, hz⟩, hxf, hzf⟩

end FiveTransitive.FixedNormalizerDoubleSwapSylow

end CFSG
