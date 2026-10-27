module

public import CFSG.Permutation.FiveTransitive.OyamaSixElementary
public import CFSG.Permutation.FiveTransitive.SemiregularThirdOrbit

public section

namespace CFSG

namespace FiveTransitive.OyamaPointOrbitGeometry

open MulAction

variable (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]

omit [Finite G] [Fintype X] in
private theorem base_subset_fixed (s : Set X) (S : Sylow 2 (fixingSubgroup G s)) :
    s ⊆ fixedPoints S X := by
  intro x hx
  rw [mem_fixedPoints]
  intro q
  exact (mem_fixingSubgroup_iff G).mp (q : fixingSubgroup G s).property x hx

omit [Finite G] in
private theorem exists_extra_pair (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hcard : (fixedPoints S X).ncard = 6) :
    ∃ u v : X, u ∉ s ∧ v ∉ s ∧ u ≠ v ∧ fixedPoints S X = s ∪ {u,v} := by
  have hc : (fixedPoints S X \ s).ncard = 2 := by
    rw [Set.ncard_sdiff (base_subset_fixed G X s S),hcard,hs]
  obtain ⟨u,v,huv,he⟩ := Set.ncard_eq_two.mp hc
  have hu : u ∈ fixedPoints S X \ s := by rw [he]; simp
  have hv : v ∈ fixedPoints S X \ s := by rw [he]; simp
  refine ⟨u,v,hu.2,hv.2,huv,?_⟩
  rw [← he]
  ext x
  have ht := (base_subset_fixed G X s S) (a := x)
  simp only [Set.mem_union,Set.mem_sdiff]
  tauto

omit [Finite G] in
private theorem equal_nontrivial (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hH : fixedPoints (fixingSubgroup G s) X = s)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (u v : X) (hu : u ∈ fixedPoints S X) (hv : v ∈ fixedPoints S X)
    (hus : u ∉ s) (hvs : v ∉ s) (huv : u ≠ v) :
    Nat.card (orbit (fixingSubgroup G s) u) = Nat.card (orbit (fixingSubgroup G s) v) ∧
      1 < Nat.card (orbit (fixingSubgroup G s) u) ∧
      1 < Nat.card (orbit (fixingSubgroup G s) v) := by
  let H := fixingSubgroup G s
  let Q := (S : Subgroup H).map H.subtype
  have he : fixedPoints Q X = fixedPoints S X := OyamaSixElementary.fixedPoints_image G X H S
  obtain ⟨g,hg,hgu⟩ := NormalizerSwappedOrbits.exists_swapping G X Q s (by omega)
    (by rw [he]; exact base_subset_fixed G X s S) himage u v
    (by rwa [he]) (by rwa [he]) hus hvs huv
  refine ⟨?_,NormalizerSwappedOrbits.one_lt_card_orbit u (by rwa [hH]),
    NormalizerSwappedOrbits.one_lt_card_orbit v (by rwa [hH])⟩
  rw [← hgu]
  exact NormalizerSwappedOrbits.card_orbit_eq G X H g hg u

theorem exists_geometry (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hH : fixedPoints (fixingSubgroup G s) X = s)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16)
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hdegree : 32 ∣ (Nat.card X - 22)) :
    ∃ u v w : X, u ∉ s ∧ v ∉ s ∧ u ≠ v ∧ fixedPoints S X = s ∪ {u,v} ∧
      v ∉ orbit (fixingSubgroup G s) u ∧
      (¬ 2 ∣ Nat.card (orbit (fixingSubgroup G s) u)) ∧
      (¬ 2 ∣ Nat.card (orbit (fixingSubgroup G s) v)) ∧
      Nat.card (orbit (fixingSubgroup G s) u) = Nat.card (orbit (fixingSubgroup G s) v) ∧
      1 < Nat.card (orbit (fixingSubgroup G s) u) ∧
      1 < Nat.card (orbit (fixingSubgroup G s) v) ∧
      w ∉ s ∪ orbit (fixingSubgroup G s) u ∪ orbit (fixingSubgroup G s) v := by
  obtain ⟨u,v,hu,hv,huv,hfix⟩ := exists_extra_pair G X s hs S hcard
  obtain ⟨heq,hlu,hlv⟩ := equal_nontrivial G X s hs S hH himage u v
    (by rw [hfix]; simp) (by rw [hfix]; simp) hu hv huv
  obtain ⟨hou,hov,hsep⟩ := TwoSylowFixedOrbits.two_odd_distinct S s u v hH hfix hu hv huv
  obtain ⟨w,hw⟩ := SemiregularThirdOrbit.exists_third_point S s u v hs hH hfix hu hv huv
    hS hfree heq hdegree
  exact ⟨u,v,w,hu,hv,huv,hfix,hsep,hou,hov,heq,hlu,hlv,hw⟩

end FiveTransitive.OyamaPointOrbitGeometry

end CFSG
