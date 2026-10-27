module

public import CFSG.Monster.B.E6.StdF4Orbital
public import CFSG.Monster.B.E6.FixedE6RootVector
public import CFSG.Monster.B.E6.StdF4Fiber

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension (GStar betaGroup parStar parLeft)
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.Monster.B.Geometry CFSG.Monster.B.Classical
open CFSG.Monster.B.E6.FixedE6Root (commute_conj_pair_iff repPoint_mem_rootClass)

theorem lidx_ptIdx_wOf
    (g : stdGroup) :
    lidx (ptIdx (wOf g)) = ([2, 1, 0, -1, -2] : List ℤ).idxOf (lev g) := by
  rw [lidx, levList_ptIdx]
  rfl

theorem idxOf_repLevel : ∀ i : Fin 5, ([2, 1, 0, -1, -2] : List ℤ).idxOf (repLevel i) = i := by
  decide

theorem relPt_rootMap_rootMap
    (k g : stdGroup) :
    relPt (rootMap k) (rootMap (k * g)) = ([2, 1, 0, -1, -2] : List ℤ).idxOf (lev g) := by
  rw [relPt_rootMap, inv_mul_cancel_left, lidx_ptIdx_wOf]

theorem relPt_conj_pair
    (k : stdGroup) (i : Fin 5) :
    relPt (k * rootInv * k⁻¹) (k * repPoint i * k⁻¹) = i := by
  have e1 : k * rootInv * k⁻¹ = rootMap k := rfl
  have e2 : k * repPoint i * k⁻¹ = rootMap (k * stdRep (ncs.wordProd (repWord i))) := by
    rw [rootMap_mul]
    rfl
  rw [e1, e2, relPt_rootMap_rootMap, lev_repPoint, idxOf_repLevel]

theorem commute_iff_relPt_lt
    {x y : stdGroup} (hx : x ∈ rootClass) (hy : y ∈ rootClass) :
    Commute x y ↔ relPt x y < 3 := by
  obtain ⟨k, i, rfl, rfl⟩ := FixedE6Root.exists_conj_pair hx hy
  rw [commute_conj_pair_iff, relPt_conj_pair]
  fin_cases i <;> decide

theorem relPt_rootInv_rootMap
    (g : stdGroup) :
    relPt rootInv (rootMap g) = ([2, 1, 0, -1, -2] : List ℤ).idxOf (lev g) := by
  rw [← rootMap_one, ← relPt_rootMap_rootMap 1 g, one_mul]

theorem mem_fibOrbit_iff
    {z : stdGroup} (hz : z ∈ rootClass) (d : Fin 5) :
    SemidirectProduct.inl z ∈ fibOrbit d ↔ relPt rootInv z = d := by
  rw [fibOrbit_eq, SemidirectProduct.inl_injective.mem_set_image]
  obtain ⟨g, rfl⟩ := (mem_rootClass_iff z).1 hz
  constructor
  · rintro ⟨h, hh, e⟩
    rw [← e, relPt_rootInv_rootMap, hh, idxOf_repLevel]
  · intro h
    rw [relPt_rootInv_rootMap] at h
    obtain ⟨i, hi⟩ := exists_repLevel g
    rw [hi, idxOf_repLevel] at h
    have hid : i = d := Fin.ext h
    exact ⟨g, show lev g = repLevel d by rw [hi, hid], rfl⟩

theorem exists_inl_of_mem_fibOrbit
    {d : Fin 5} {x : GStar} (hx : x ∈ fibOrbit d) :
    ∃ z ∈ rootClass, x = SemidirectProduct.inl z := by
  rw [fibOrbit_eq] at hx
  obtain ⟨z, ⟨g, -, rfl⟩, rfl⟩ := hx
  exact ⟨rootMap g, (mem_rootClass_iff _).2 ⟨g, rfl⟩, rfl⟩

theorem commute_inl_iff
    (x y : stdGroup) :
    Commute (SemidirectProduct.inl x : GStar) (SemidirectProduct.inl y) ↔ Commute x y := by
  refine ⟨fun h => ?_, fun h => h.map SemidirectProduct.inl⟩
  have e : (SemidirectProduct.inl (x * y) : GStar) = SemidirectProduct.inl (y * x) := by
    rw [map_mul, map_mul]
    exact h.eq
  exact SemidirectProduct.inl_injective e

theorem orbM_sum : orbM 1 2 0 + orbM 1 2 1 + orbM 1 2 2 = 54 := by decide

theorem card_filter_lt_three
    (x y : Pts) :
    (Finset.univ.filter fun z : Pts => relIdx x z = 1 ∧ (relIdx z y : ℕ) < 3).card =
      orbM 1 (relIdx x y) 0 + orbM 1 (relIdx x y) 1 + orbM 1 (relIdx x y) 2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun z => relIdx z y) (t := {0, 1, 2})
    (fun z hz => by
      have h := (Finset.mem_filter.1 hz).2.2
      have h3 : (relIdx z y : ℕ) = 0 ∨ (relIdx z y : ℕ) = 1 ∨ (relIdx z y : ℕ) = 2 := by omega
      have h3' : relIdx z y = 0 ∨ relIdx z y = 1 ∨ relIdx z y = 2 := by
        rcases h3 with h0 | h0 | h0
        · exact Or.inl (show relIdx z y = 0 from Fin.ext h0)
        · exact Or.inr (Or.inl (show relIdx z y = 1 from Fin.ext h0))
        · exact Or.inr (Or.inr (show relIdx z y = 2 from Fin.ext h0))
      simpa using h3')]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    ← card_filter_relIdx x y 1 0, ← card_filter_relIdx x y 1 1, ← card_filter_relIdx x y 1 2,
    add_assoc]
  congr 1
  · congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by rw [h.2]; decide⟩, h.2⟩⟩
  · congr 1
    · congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by rw [h.2]; decide⟩, h.2⟩⟩
    · congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by rw [h.2]; decide⟩, h.2⟩⟩

theorem ncard_commute_fibOrbit_one
    {q : GStar} (hq : q ∈ fibOrbit 2) :
    {p | p ∈ fibOrbit 1 ∧ Commute p q}.ncard = 54 := by
  obtain ⟨q', hq', rfl⟩ := exists_inl_of_mem_fibOrbit hq
  have hrq : relPt rootInv q' = 2 := (mem_fibOrbit_iff hq' 2).1 hq
  set y : Pts := ⟨q', hq'⟩
  have hset : {p | p ∈ fibOrbit 1 ∧ Commute p (SemidirectProduct.inl q')} =
      (fun z : Pts => (SemidirectProduct.inl z.1 : GStar)) ''
        ↑(Finset.univ.filter fun z : Pts => relIdx basePt z = 1 ∧ (relIdx z y : ℕ) < 3) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hp, hc⟩
      obtain ⟨p', hp', rfl⟩ := exists_inl_of_mem_fibOrbit hp
      refine ⟨⟨p', hp'⟩, ⟨Fin.ext ((mem_fibOrbit_iff hp' 1).1 hp), ?_⟩, rfl⟩
      exact (commute_iff_relPt_lt hp' hq').1 ((commute_inl_iff _ _).1 hc)
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨(mem_fibOrbit_iff z.2 1).2 (congrArg Fin.val h1),
        (commute_inl_iff _ _).2 ((commute_iff_relPt_lt z.2 hq').2 h2)⟩
  rw [hset, Set.ncard_image_of_injective _ fun a b h => Subtype.ext
      (SemidirectProduct.inl_injective h), Set.ncard_coe_finset, card_filter_lt_three]
  have hb : relIdx basePt y = 2 := Fin.ext hrq
  rw [hb, orbM_sum]

theorem conjOrbit_radStar_subset
    {d : Fin 5} {x : GStar} (hx : x ∈ fibOrbit d) :
    conjOrbit radStar x ⊆ fibOrbit d := by
  obtain ⟨γ, hγ, rfl⟩ := hx
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨u * γ, mul_mem (radStar_le_parStar hu) hγ, by group⟩

theorem ncard_fibSub_eq
    {T : Submodule K (Fin 6 → K)} (hT : T ∈ isoSubs 2) :
    {p | p ∈ fibOrbit 1 ∧ fibSub 1 p = T}.ncard = 2 := by
  have hmid : IsMid 1 := Or.inl rfl
  have hT' : T ∈ fibSub 1 '' fibOrbit 1 := by
    rw [image_fibSub hmid]
    exact hT
  obtain ⟨p₁, hp₁, rfl⟩ := hT'
  have hset : {p | p ∈ fibOrbit 1 ∧ fibSub 1 p = fibSub 1 p₁} = conjOrbit radStar p₁ := by
    ext p
    constructor
    · rintro ⟨hp, he⟩
      exact (fibSub_eq_iff hmid hp₁ hp).1 he.symm
    · intro hp
      exact ⟨conjOrbit_radStar_subset hp₁ hp,
        ((fibSub_eq_iff hmid hp₁ (conjOrbit_radStar_subset hp₁ hp)).2 hp).symm⟩
  rw [hset, ncard_conjOrbit_radStar hp₁]
  rfl

theorem finite_isoSubs
    (k : Fin 3) : (isoSubs k).Finite := by
  rw [← range_flagSub]
  exact Set.finite_range _

theorem ncard_fibSub_preimage
    {𝒯 : Set (Submodule K (Fin 6 → K))} (h𝒯 : 𝒯 ⊆ isoSubs 2) :
    {p | p ∈ fibOrbit 1 ∧ fibSub 1 p ∈ 𝒯}.ncard = 2 * 𝒯.ncard := by
  classical
  have hfin𝒯 : 𝒯.Finite := (finite_isoSubs 2).subset h𝒯
  have hfinS : {p | p ∈ fibOrbit 1 ∧ fibSub 1 p ∈ 𝒯}.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfinS, Set.ncard_eq_toFinset_card _ hfin𝒯,
    Finset.card_eq_sum_card_fiberwise (f := fibSub 1) (t := hfin𝒯.toFinset)
      (fun p hp => by simpa using ((Set.Finite.mem_toFinset _).1 hp).2)]
  rw [Finset.sum_congr rfl fun T hT => ?_, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [Set.Finite.mem_toFinset] at hT
  rw [← ncard_fibSub_eq (h𝒯 hT), Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  congr 1
  ext p
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hT⟩, h.2⟩⟩

end CFSG.Monster.B.E6.StdF4
