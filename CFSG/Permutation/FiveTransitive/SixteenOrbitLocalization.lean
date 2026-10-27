module

public import CFSG.Permutation.FiveTransitive.SixteenNormalizerFixedFour

public section

namespace CFSG

namespace FiveTransitive.SixteenOrbitLocalization

open MulAction

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]

omit [Finite G] [Finite X] in
theorem orbit_card_of_free (S : Subgroup G) (x : X)
    (hfree : ∀ s : S, s • x = x → s = 1) : (orbit S x).ncard = Nat.card S := by
  let f : S → orbit S x := fun s => ⟨s • x, mem_orbit_iff.mpr ⟨s,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s t h
      have hst : s • x = t • x := congrArg Subtype.val h
      change s • x = t • x at hst
      have he : (t⁻¹ * s) • x = x := by
        rw [mul_smul, hst, inv_smul_smul]
      exact (inv_mul_eq_one.mp (hfree _ he)).symm
    · intro y
      obtain ⟨s,hs⟩ := mem_orbit_iff.mp y.property
      exact ⟨s,Subtype.ext hs⟩
  exact (Nat.card_coe_set_eq _).symm.trans (Nat.card_congr (Equiv.ofBijective f hf).symm)

theorem fixed_outside_subset_orbit
    (S : Subgroup G) (hcomm : ∀ s t : S, s * t = t * s) (h2 : ∀ s : S, s * s = 1)
    (hcard : Nat.card S = 16)
    (b : G) (hb : b ∈ Subgroup.normalizer (S : Set G)) (hb2 : b * b = 1)
    (hfree : ∀ (s : S) (x : X), x ∉ fixedPoints S X → s • x = x → s = 1)
    (hsix : (fixedBy X b).ncard = 6)
    (htwo : (fixedBy X b ∩ fixedPoints S X).ncard = 2)
    (x : X) (hbx : b • x = x) (hx : x ∉ fixedPoints S X) :
    fixedBy X b \ fixedPoints S X ⊆ orbit S x := by
  let A := orbit S x ∩ fixedBy X b
  let B := fixedBy X b \ fixedPoints S X
  have hcount := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X b) (fixedPoints S X)
  have hB : B.ncard = 4 := by change (fixedBy X b \ fixedPoints S X).ncard = 4; omega
  have hAB : A ⊆ B := by
    intro y hy
    exact ⟨hy.2, SemiregularNormalizerBound.orbit_not_fixed S X x hx hy.1⟩
  have hA : A.ncard ≤ 4 := (Set.ncard_le_ncard hAB).trans_eq hB
  have hbound := SemiregularNormalizerBound.card_le_orbit_fixed_sq G X S hcomm h2 b hb hb2
    x hbx (fun s => hfree s x hx)
  let e : {y : X // y ∈ orbit S x ∧ b • y = y} ≃ A :=
    { toFun := fun y => ⟨y.val,y.property⟩
      invFun := fun y => ⟨y.val,y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hcard, Nat.card_congr e, Nat.card_coe_set_eq] at hbound
  have hA4 : A.ncard = 4 := by nlinarith
  have heq : A = B := Set.eq_of_subset_of_ncard_le hAB (by omega)
  intro y hy
  exact (heq ▸ hy : y ∈ A).1

theorem coset_involution_fixed_subset_orbit
    (S : Subgroup G) (hcomm : ∀ s t : S, s * t = t * s) (h2 : ∀ s : S, s * s = 1)
    (hcard : Nat.card S = 16)
    (b : G) (hb : b ∈ Subgroup.normalizer (S : Set G)) (hb2 : b * b = 1)
    (hfree : ∀ (s : S) (x : X), x ∉ fixedPoints S X → s • x = x → s = 1)
    (hsix : (fixedBy X b).ncard = 6)
    (htwo : (fixedBy X b ∩ fixedPoints S X).ncard = 2)
    (x : X) (hbx : b • x = x) (hx : x ∉ fixedPoints S X)
    (a : G) (ha2 : a * a = 1) (hab : a * b⁻¹ ∈ S) :
    fixedBy X a \ fixedPoints S X ⊆ orbit S x := by
  obtain ⟨s,hs⟩ := SixteenNormalizerFixedFour.coset_conjugate_of_fixed_six G X S
    hcomm h2 hcard b hb hb2 hfree hsix htwo a ha2 hab
  intro y hy
  have hsy : (s⁻¹ : S) • y ∉ fixedPoints S X := by
    exact SemiregularNormalizerBound.orbit_not_fixed S X y hy.2
      (mem_orbit_iff.mpr ⟨s⁻¹,rfl⟩)
  have hbsy : b • ((s⁻¹ : S) • y) = (s⁻¹ : S) • y := by
    have h := congrArg (fun z : X => (s.val)⁻¹ • z) hy.1
    rw [← hs, mul_smul, mul_smul, inv_smul_smul] at h
    exact h
  have hm := fixed_outside_subset_orbit S hcomm h2 hcard b hb hb2 hfree hsix htwo
    x hbx hx ⟨hbsy,hsy⟩
  have ht := mem_orbit_of_mem_orbit s hm
  simpa only [smul_inv_smul] using ht

end FiveTransitive.SixteenOrbitLocalization

end CFSG
