module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Data.Set.Card

public section

namespace CFSG

namespace FiveTransitive.FreeComplementOrbitCount

open MulAction
open scoped BigOperators

@[expose] def complement {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (s : Set X) (hs : ∀ (h : H) (x : X), x ∈ s → h • x ∈ s) :
    SubMulAction H X where
  carrier := sᶜ
  smul_mem' h x hx := by
    change h • x ∉ s
    intro hh
    have ht := hs h⁻¹ (h • x) hh
    exact hx (by simpa only [inv_smul_smul] using ht)

theorem card_complement {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (H : Subgroup G) (s : Set X) (hs : ∀ (h : H) (x : X), x ∈ s → h • x ∈ s) :
    Nat.card (complement H s hs) = Nat.card X - s.ncard := by
  change Nat.card ↥sᶜ = _
  rw [Nat.card_coe_set_eq, Set.ncard_compl]

@[expose] def fixedComplement {G X : Type*} [Group G] [MulAction G X] (S : Subgroup G) :
    SubMulAction S X :=
  complement S (fixedPoints S X) (by
    intro s x hx
    rwa [mem_fixedPoints.mp hx s])

theorem card_fixedComplement {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (S : Subgroup G) : Nat.card (fixedComplement (X := X) S) =
      Nat.card X - (fixedPoints S X).ncard := card_complement S _ _

theorem card_eq_mul_orbits {H Y : Type*} [Group H] [Finite H] [MulAction H Y] [Finite Y]
    (hfree : ∀ (h : H) (y : Y), h • y = y → h = 1) :
    Nat.card Y = Nat.card H * Nat.card (orbitRel.Quotient H Y) := by
  classical
  let _ : Fintype Y := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient H Y) := Fintype.ofFinite _
  have hc (y : Y) : Nat.card (orbit H y) = Nat.card H := by
    let f : H → orbit H y := fun h => ⟨h • y, mem_orbit_iff.mpr ⟨h,rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro h k he
        have he' : h • y = k • y := congrArg Subtype.val he
        change h • y = k • y at he'
        have hz : (k⁻¹ * h) • y = y := by rw [mul_smul,he',inv_smul_smul]
        exact (inv_mul_eq_one.mp (hfree _ y hz)).symm
      · intro z
        obtain ⟨h,hh⟩ := mem_orbit_iff.mp z.property
        exact ⟨h,Subtype.ext hh⟩
    exact Nat.card_congr (Equiv.ofBijective f hf).symm
  have he : Nat.card Y = ∑ q : orbitRel.Quotient H Y, Nat.card (orbit H q.out) := by
    rw [Nat.card_congr (selfEquivSigmaOrbits H Y)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  rw [he]
  simp_rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, Nat.mul_comm]

end FiveTransitive.FreeComplementOrbitCount

end CFSG
