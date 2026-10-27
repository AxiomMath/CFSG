module

public import CFSG.Permutation.FiveTransitive.ThreeSwapCommutingActual
public import CFSG.Permutation.FiveTransitive.KernelImageGeneration

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.ThreeSwapElementaryActual

open MulAction FixedNormalizerAction

private theorem generated_elementary
    {G H : Type*} [Group G] [Group H] (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (f : Normalizer Q →* H) (B : Subgroup (Normalizer Q))
    (hk : B ⊓ f.ker = Inside Q)
    (x y z : Normalizer Q) (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B)
    (hxsq : x ^ 2 = 1) (hysq : y ^ 2 = 1) (hzsq : z ^ 2 = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z)
    (hm : B.map f = Subgroup.closure (f '' ({x, y, z} : Set (Normalizer Q)))) :
    ∃ a : Normalizer Q, a ∈ Inside Q ∧ orderOf a = 2 ∧
      Inside Q = Subgroup.zpowers a ∧
      B = Subgroup.closure ({a, x, y, z} : Set (Normalizer Q)) ∧
      (∀ g : B, g ^ 2 = 1) ∧ IsMulCommutative B := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨aQ, haQorder⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hQ])
  have haQne : aQ ≠ 1 := by intro h; rw [h, orderOf_one] at haQorder; omega
  let a : Normalizer Q := ⟨aQ.val, Q.le_normalizer aQ.property⟩
  have haI : a ∈ Inside Q := aQ.property
  have haorder : orderOf a = 2 := by
    calc
      orderOf a = orderOf (a : G) := (orderOf_injective (Normalizer Q).subtype Subtype.val_injective a).symm
      _ = orderOf aQ := orderOf_injective Q.subtype Subtype.val_injective aQ
      _ = 2 := haQorder
  have hagen : Inside Q = Subgroup.zpowers a := by
    apply le_antisymm _ (Subgroup.zpowers_le.mpr haI)
    intro q hq
    rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hQ aQ haQne
      (⟨q.val, hq⟩ : Q) with he | he
    · have he' : q = 1 := Subtype.ext (congrArg (fun t : Q => (t : G)) he)
      rw [he']; exact Subgroup.one_mem _
    · have he' : q = a := Subtype.ext (congrArg (fun t : Q => (t : G)) he)
      rw [he']; exact Subgroup.mem_zpowers a
  have hgen : B = Subgroup.closure ({a, x, y, z} : Set (Normalizer Q)) := by
    apply KernelImageGeneration.eq_closure_insert f B (Inside Q) hk a hagen
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl <;> assumption
    · exact hm
  have hac (g : Normalizer Q) : Commute a g := by
    apply Subtype.ext
    exact NormalizerTwoElementInvolution.central_of_card_two Q hQ g aQ
  have hc : ({a, x, y, z} : Set (Normalizer Q)).Pairwise Commute := by
    intro b hb c hc hbc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
    rcases hb with rfl | rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl
    all_goals first | exact Commute.refl _ | exact hac _ | exact (hac _).symm | exact hxy | exact hxy.symm | exact hxz | exact hxz.symm | exact hyz | exact hyz.symm
  have hasq : a ^ 2 = 1 := haorder ▸ pow_orderOf_eq_one a
  have hs : ∀ g ∈ ({a, x, y, z} : Set (Normalizer Q)), g ^ 2 = 1 := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> assumption
  obtain ⟨_, hall⟩ := ThreeSwapTwoGroup.closure_two_group _ hc hs
  have habel : IsMulCommutative (Subgroup.closure ({a, x, y, z} : Set (Normalizer Q))) :=
    Subgroup.isMulCommutative_closure hc
  refine ⟨a, haI, haorder, hagen, hgen, ?_, ?_⟩
  · rw [hgen]; exact hall
  · rw [hgen]; exact habel

theorem exists_elementary_lifts
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 2) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hQA : Q ≤ A)
    (x : Normalizer Q) (hxA : (x : G) ∈ A) (hx : orderOf (x : G) = 2)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (houtside : (fixedBy X x.val \ fixedPoints Q X).ncard = 2) :
    ∃ (e : Fin 6 ↪ Fixed (X := X) Q)
      (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let V := ThreeSwapTwoGroup.subgroup e
      let B := SylowPreimageNormalizer.ambient f V P
      f x = Equiv.swap (e 0) (e 1) ∧ IsPGroup 2 B ∧ Inside Q ≤ B ∧ x ∈ B ∧
      B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      (f.comp B.subtype).ker = (Inside Q).subgroupOf B ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f =
        Subgroup.normalizer (V : Set (Equiv.Perm (Fixed (X := X) Q))) ∧
      ∃ y z : B,
        f y.val = Equiv.swap (e 2) (e 3) ∧ f z.val = Equiv.swap (e 4) (e 5) ∧
        orderOf (x : G) = 2 ∧ orderOf (y.val : G) = 2 ∧ orderOf (z.val : G) = 2 ∧
        Commute (x : G) (y.val : G) ∧ Commute (x : G) (z.val : G) ∧
        Commute (y.val : G) (z.val : G) ∧
        (∀ q : Q, Commute (q : G) (x : G) ∧
          Commute (q : G) (y.val : G) ∧ Commute (q : G) (z.val : G)) ∧
        ∃ a : Normalizer Q, a ∈ Inside Q ∧ orderOf a = 2 ∧
          Inside Q = Subgroup.zpowers a ∧
          B = Subgroup.closure ({a, x, y.val, z.val} : Set (Normalizer Q)) ∧
          (∀ g : B, g ^ 2 = 1) ∧ IsMulCommutative B := by
  classical
  obtain ⟨e, P, hxf, hp, hIP, hxP, hm, hk, hkr, hn, y, z, hyf, hzf,
    hxord, hyord, hzord, hxy, hxz, hyz, hQcomm⟩ :=
    ThreeSwapCommutingActual.exists_commuting_lifts Q hQ hseven S hS himage
      A hA hQA x hxA hx hlocal houtside
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let B := SylowPreimageNormalizer.ambient f V P
  change f x = Equiv.swap (e 0) (e 1) at hxf
  change f y.val = Equiv.swap (e 2) (e 3) at hyf
  change f z.val = Equiv.swap (e 4) (e 5) at hzf
  change B.map f = V at hm
  have hgenim : B.map f = Subgroup.closure (f '' ({x, y.val, z.val} : Set (Normalizer Q))) := by
    rw [hm]
    simp only [Set.image_insert_eq, Set.image_singleton, hxf, hyf, hzf]
    rfl
  have hxsq : x ^ 2 = 1 := Subtype.ext (hxord ▸ pow_orderOf_eq_one (x : G))
  have hysq : y.val ^ 2 = 1 := by
    apply Subtype.ext
    change (y.val : G) ^ 2 = 1
    simpa only [hyord] using pow_orderOf_eq_one (y.val : G)
  have hzsq : z.val ^ 2 = 1 := by
    apply Subtype.ext
    change (z.val : G) ^ 2 = 1
    simpa only [hzord] using pow_orderOf_eq_one (z.val : G)
  obtain ⟨a, haI, haord, hagen, hgen, hsq, habel⟩ := generated_elementary
    Q hQ f B hk x y.val z.val hxP y.property z.property hxsq hysq hzsq
    (Subtype.ext hxy.eq) (Subtype.ext hxz.eq) (Subtype.ext hyz.eq) hgenim
  exact ⟨e, P, hxf, hp, hIP, hxP, hm, hk, hkr, hn, y, z, hyf, hzf,
    hxord, hyord, hzord, hxy, hxz, hyz, hQcomm, a, haI, haord, hagen, hgen, hsq, habel⟩

end FiveTransitive.ThreeSwapElementaryActual

end CFSG
