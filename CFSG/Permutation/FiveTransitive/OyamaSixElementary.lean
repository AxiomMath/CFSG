module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom
public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy
public import CFSG.Permutation.FiveTransitive.ConjugateFixedNormalizer
public import CFSG.Permutation.FiveTransitive.SixLocalSylowExponentTwo

public section

namespace CFSG

namespace FiveTransitive.OyamaSixElementary

open MulAction FixedSetNormalizerPerm

abbrev fixedHom
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G) :=
  FixedSetNormalizerHom.fixedPermHom G X Q

theorem local_of_base
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hcard : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (heven : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1) :
    SixLocalSylowExponentTwo.EvenSixLocal G X := by
  intro t ht T
  obtain ⟨c, hc⟩ := BaseSylowConjugacy.exists_conjugate_sylow_images G X 4 h4 s t hs ht S T
  exact ConjugateFixedNormalizer.six_even_of_conjugate G X _ _ c hc hcard heven

theorem fixedPoints_image
    (G X : Type*) [Group G] [MulAction G X] (H : Subgroup G) (S : Subgroup H) :
    fixedPoints (S.map H.subtype) X = fixedPoints S X := by
  ext x
  constructor
  · intro hx
    rw [mem_fixedPoints]
    intro q
    exact mem_fixedPoints.mp hx ⟨(q : H), Subgroup.mem_map_of_mem H.subtype q.property⟩
  · intro hx
    rw [mem_fixedPoints]
    intro q
    obtain ⟨r, hr, hqr⟩ := Subgroup.mem_map.mp q.property
    change (q : G) • x = x
    rw [← hqr]
    exact mem_fixedPoints.mp hx ⟨r, hr⟩

theorem square_eq_one_and_commute
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedHom G X Q).range = alternatingGroup (fixedPoints Q X)) :
    (∀ q : S, q * q = 1) ∧ (∀ q r : S, q * r = r * q) := by
  classical
  let H := fixingSubgroup G s
  let Q := (S : Subgroup H).map H.subtype
  have hfixed : fixedPoints Q X = fixedPoints S X := fixedPoints_image G X H S
  have hcardQ : (fixedPoints Q X).ncard = 6 := by rw [hfixed]; exact hcard
  have heven : ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1 := by
    intro a ha
    let _ := Fintype.ofFinite (fixedPoints Q X)
    let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
    have hmem : fixedPerm G X Q a ha ∈ (fixedHom G X Q).range := ⟨⟨a, ha⟩, rfl⟩
    rw [himage] at hmem
    exact Equiv.Perm.mem_alternatingGroup.mp hmem
  have hlocal := local_of_base G X h4 s hs S hcardQ heven
  have hfreeQ : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1 := by
    intro q x hx hqx
    obtain ⟨r, hr, hqr⟩ := Subgroup.mem_map.mp q.property
    change (r : G) = (q : G) at hqr
    have hrx : (⟨r, hr⟩ : S) • x = x := by
      change (r : G) • x = x
      rw [hqr]
      exact hqx
    have hr1 := hfree ⟨r, hr⟩ x (by rwa [hfixed] at hx) hrx
    have hval := congrArg (fun z : S => ((z : H) : G)) hr1
    apply Subtype.ext
    simpa only [Subgroup.coe_one, hqr] using hval
  have hQ : IsPGroup 2 Q := S.isPGroup'.map H.subtype
  obtain ⟨hsq, hcomm⟩ := SixLocalSylowExponentTwo.square_eq_one_and_commute G X hlocal Q hQ hfreeQ
  let e : S ≃* Q := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  constructor
  · intro q
    apply e.injective
    simpa only [map_mul, map_one] using hsq (e q)
  · intro q r
    apply e.injective
    simpa only [map_mul] using hcomm (e q) (e r)

end FiveTransitive.OyamaSixElementary

end CFSG
