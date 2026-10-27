module

public import CFSG.Permutation.FiveTransitive.TwoSylowFixedOrbits
public import CFSG.Permutation.FiveTransitive.FreeComplementOrbitCount
public import CFSG.Permutation.FiveTransitive.NormalizerSwappedOrbits

public section

namespace CFSG

namespace FiveTransitive.SemiregularThirdOrbit

open MulAction

variable {H X : Type*} [Group H] [MulAction H X]

private def nonfixedOrbit (S : Subgroup H) (u : X) : SubMulAction S X where
  carrier := orbit H u \ fixedPoints S X
  smul_mem' q x hx := by
    refine ⟨mem_orbit_of_mem_orbit q.val hx.1,?_⟩
    intro hf
    have he : q • x = x := by
      have ht := mem_fixedPoints.mp hf q⁻¹
      simpa only [inv_smul_smul] using ht.symm
    exact hx.2 (he ▸ hf)

private theorem card_dvd_orbit_sub_one [Finite H] [Finite X]
    (S : Subgroup H) (u : X)
    (hfix : orbit H u ∩ fixedPoints S X = {u})
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1) :
    Nat.card S ∣ Nat.card (orbit H u) - 1 := by
  let C := nonfixedOrbit S u
  have he : orbit H u \ fixedPoints S X = orbit H u \ {u} := by
    calc
      _ = orbit H u \ (orbit H u ∩ fixedPoints S X) := by ext x; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
      _ = _ := by rw [hfix]
  have hc : Nat.card C = Nat.card (orbit H u) - 1 := by
    change Nat.card ↥(orbit H u \ fixedPoints S X) = _
    rw [Nat.card_coe_set_eq,he,Set.ncard_sdiff_singleton_of_mem (mem_orbit_self _),Nat.card_coe_set_eq]
  rw [← hc,FreeComplementOrbitCount.card_eq_mul_orbits (fun q x hh =>
    hfree q x.val x.property.2 (congrArg Subtype.val hh))]
  exact dvd_mul_right _ _

theorem exists_third_point [Finite H] [Finite X]
    (S : Sylow 2 H) (s : Set X) (u v : X)
    (hs : s.ncard = 4) (hH : fixedPoints H X = s)
    (hS : fixedPoints S X = s ∪ {u,v})
    (hu : u ∉ s) (hv : v ∉ s) (huv : u ≠ v)
    (hcard : Nat.card S = 16)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hequal : Nat.card (orbit H u) = Nat.card (orbit H v))
    (hdegree : 32 ∣ (Nat.card X - 22)) :
    ∃ w : X, w ∉ s ∪ orbit H u ∪ orbit H v := by
  classical
  have hsep := (TwoSylowFixedOrbits.two_odd_distinct S s u v hH hS hu hv huv).2.2
  have hfix := TwoSylowFixedOrbits.fixed_inter_orbit S s u v hH hS hu hsep
  have hmod := card_dvd_orbit_sub_one (S : Subgroup H) u hfix hfree
  rw [hcard] at hmod
  have hlarge := NormalizerSwappedOrbits.one_lt_card_orbit u (show u ∉ fixedPoints H X by rwa [hH])
  have hdu : Disjoint (orbit H u) s := by
    rw [← hH]
    exact TwoSylowFixedOrbits.orbit_disjoint_fixed u (by rwa [hH])
  have hdv : Disjoint (orbit H v) s := by
    rw [← hH]
    exact TwoSylowFixedOrbits.orbit_disjoint_fixed v (by rwa [hH])
  have hduv : Disjoint (orbit H u) (orbit H v) := by
    rw [Set.disjoint_left]
    intro x hxu hxv
    obtain ⟨a,ha⟩ := mem_orbit_iff.mp hxu
    obtain ⟨b,hb⟩ := mem_orbit_iff.mp hxv
    apply hsep
    refine mem_orbit_iff.mpr ⟨b⁻¹*a,?_⟩
    rw [mul_smul,ha,← hb,inv_smul_smul]
  by_contra hn
  have he : s ∪ orbit H u ∪ orbit H v = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact hn ⟨x,hx⟩
  have hcount : Nat.card X = 4 + Nat.card (orbit H u) + Nat.card (orbit H v) := by
    rw [← Set.ncard_univ,← he,Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨hdv.symm,hduv⟩),
      Set.ncard_union_eq hdu.symm,hs,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq]
  obtain ⟨k,hk⟩ := hmod
  obtain ⟨l,hl⟩ := hdegree
  omega

end FiveTransitive.SemiregularThirdOrbit

end CFSG
