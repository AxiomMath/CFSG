module

public import CFSG.Permutation.FiveTransitive.ThreeSwapCompatibleSylow
public import CFSG.Permutation.FiveTransitive.ThreeSwapNormalizerConjugators
public import CFSG.Permutation.FiveTransitive.ThreeSwapLiftCommutativity
public import CFSG.Permutation.FiveTransitive.NormalizerTwoElementInvolution

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.ThreeSwapCommutingActual

open MulAction FixedNormalizerAction

theorem exists_commuting_lifts
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
        ∀ q : Q, Commute (q : G) (x : G) ∧
          Commute (q : G) (y.val : G) ∧ Commute (q : G) (z.val : G) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, P, hxf, hVsq, hp, hIP, hxP, hm, hk, hkr, hn, y, z, hyf, hzf⟩ :=
    ThreeSwapCompatibleSylow.exists_three_swaps Q hseven S hS himage A hA hQA x hxA hlocal
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let B := SylowPreimageNormalizer.ambient f V P
  have hcentral : ∀ q : Inside Q, ∀ g : Normalizer Q,
      (q : Normalizer Q) * g = g * q := by
    intro q g
    apply Subtype.ext
    exact NormalizerTwoElementInvolution.central_of_card_two Q hQ g ⟨q.val.val, q.property⟩
  have hQsq : ∀ q : Inside Q, (q : Normalizer Q) ^ 2 = 1 := by
    intro q
    apply Subtype.ext
    let qQ : Q := ⟨q.val.val, q.property⟩
    have hqQ : qQ ^ 2 = 1 := by rw [← hQ]; exact pow_card_eq_one' (x := qQ)
    exact congrArg (fun q : Q => (q : G)) hqQ
  have himsq (g : Normalizer Q) (hg : g ∈ B) : (f g) ^ 2 = 1 := by
    exact congrArg Subtype.val (hVsq ⟨f g, hm.le ⟨g, hg, rfl⟩⟩)
  obtain ⟨la, lb, lc, hla, hlb, hlc, hlbp⟩ := ThreeSwapNormalizerConjugators.exists_conjugators e
  obtain ⟨ga, hga, hfga⟩ := hn.ge la.property
  obtain ⟨gb, hgb, hfgb⟩ := hn.ge lb.property
  obtain ⟨gc, hgc, hfgc⟩ := hn.ge lc.property
  change f ga = la.val at hfga
  change f gb = lb.val at hfgb
  change f gc = lc.val at hfgc
  change f x = Equiv.swap (e 0) (e 1) at hxf
  change f y.val = Equiv.swap (e 2) (e 3) at hyf
  change f z.val = Equiv.swap (e 4) (e 5) at hzf
  have hgaimage : f (ga * x * ga⁻¹) = f y.val := by
    simpa only [map_mul, map_inv, hfga, hxf, hyf] using hla
  have hgbimage : f (gb * x * gb⁻¹) = f z.val := by
    simpa only [map_mul, map_inv, hfgb, hxf, hzf] using hlb
  have hxpow : x ^ 2 = 1 := Subtype.ext (hx ▸ pow_orderOf_eq_one (x : G))
  have hypow : y.val ^ 2 = 1 :=
    (CentralKernelSquareTransport.square_eq_of_image_conjugacy
      f B (Inside Q) hk hcentral hQsq x y.val ga hxP y.property hga (himsq x hxP) hgaimage).symm.trans hxpow
  have hzpow : z.val ^ 2 = 1 :=
    (CentralKernelSquareTransport.square_eq_of_image_conjugacy
      f B (Inside Q) hk hcentral hQsq x z.val gb hxP z.property hgb (himsq x hxP) hgbimage).symm.trans hxpow
  have hyne : y.val ≠ 1 := by
    intro hyone
    have heq : Equiv.swap (e 2) (e 3) = 1 := by rw [← hyf, hyone, map_one]
    exact (e.injective.ne (by decide : (2 : Fin 6) ≠ 3)) (Equiv.swap_eq_one_iff.mp heq)
  have hzne : z.val ≠ 1 := by
    intro hzone
    have heq : Equiv.swap (e 4) (e 5) = 1 := by rw [← hzf, hzone, map_one]
    exact (e.injective.ne (by decide : (4 : Fin 6) ≠ 5)) (Equiv.swap_eq_one_iff.mp heq)
  have hyorder : orderOf (y.val : G) = 2 :=
    (orderOf_injective (Normalizer Q).subtype Subtype.val_injective y.val).trans
      (orderOf_eq_prime hypow hyne)
  have hzorder : orderOf (z.val : G) = 2 :=
    (orderOf_injective (Normalizer Q).subtype Subtype.val_injective z.val).trans
      (orderOf_eq_prime hzpow hzne)
  obtain ⟨aQ, haQorder⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (by rw [hQ])
  have haQne : aQ ≠ 1 := by intro h; rw [h, orderOf_one] at haQorder; omega
  let a : Normalizer Q := ⟨aQ.val, Q.le_normalizer aQ.property⟩
  have haI : a ∈ Inside Q := aQ.property
  have hImem : ∀ q ∈ Inside Q, q = 1 ∨ q = a := by
    intro q hq
    rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hQ aQ haQne
      (⟨q.val, hq⟩ : Q) with he | he
    · exact Or.inl (Subtype.ext (congrArg (fun t : Q => (t : G)) he))
    · exact Or.inr (Subtype.ext (congrArg (fun t : Q => (t : G)) he))
  have hfixa : fixedBy X a = fixedPoints Q X := by
    ext w
    constructor
    · intro hw
      rw [mem_fixedPoints]
      intro q
      rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hQ aQ haQne q with he | he
      · rw [he, one_smul]
      · rw [he]
        exact hw
    · intro hw
      exact mem_fixedPoints.mp hw aQ
  have hcback : lc.val⁻¹ * (Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5)) *
      (lc.val⁻¹)⁻¹ = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) := by
    rw [← hlc]
    group
  have hbback : lb.val⁻¹ * (Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5)) *
      (lb.val⁻¹)⁻¹ = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) := by
    rw [← hlbp]
    group
  have he13 : f (gc⁻¹ * (x * z.val) * (gc⁻¹)⁻¹) = f (x * y.val) := by
    simpa only [map_mul, map_inv, hfgc, hxf, hyf, hzf] using hcback
  have he23 : f (gb⁻¹ * (y.val * z.val) * (gb⁻¹)⁻¹) = f (x * y.val) := by
    simpa only [map_mul, map_inv, hfgb, hxf, hyf, hzf] using hbback
  have htwo : (fixedBy X x \ fixedBy X a).ncard = 2 := by rw [hfixa]; exact houtside
  obtain ⟨hxy, hxz, hyz⟩ := ThreeSwapLiftCommutativity.pairwise_commute
    (X := X) f B (Inside Q) hk a (by simpa only [pow_two] using hQsq ⟨a, haI⟩)
    haI hImem hcentral x y.val z.val hxP y.property z.property
    (by simpa only [pow_two] using hxpow) (by simpa only [pow_two] using hypow)
    (by simpa only [pow_two] using hzpow)
    (himsq (x * y.val) (B.mul_mem hxP y.property))
    (himsq (x * z.val) (B.mul_mem hxP z.property))
    (himsq (y.val * z.val) (B.mul_mem y.property z.property))
    gc⁻¹ gb⁻¹ ((Subgroup.normalizer (B : Set (Normalizer Q))).inv_mem hgc)
    ((Subgroup.normalizer (B : Set (Normalizer Q))).inv_mem hgb) he13 he23 htwo
  refine ⟨e, P, hxf, hp, hIP, hxP, hm, hk, hkr, hn, y, z, hyf, hzf, hx, hyorder, hzorder,
    congrArg Subtype.val hxy.eq, congrArg Subtype.val hxz.eq, congrArg Subtype.val hyz.eq, ?_⟩
  intro q
  exact ⟨NormalizerTwoElementInvolution.central_of_card_two Q hQ x q,
    NormalizerTwoElementInvolution.central_of_card_two Q hQ y.val q,
    NormalizerTwoElementInvolution.central_of_card_two Q hQ z.val q⟩

end FiveTransitive.ThreeSwapCommutingActual

end CFSG
