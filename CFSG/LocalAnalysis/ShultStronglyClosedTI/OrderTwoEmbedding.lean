module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OrderTwoHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise

variable {G : Type} [Group G]

theorem involutionPointHull_eq_normalClosure_zpowers (z : G) :
    involutionPointHull z = Subgroup.normalClosure (Subgroup.zpowers z : Set G) := by
  have hclass : involutionPointClass z = conjugatesOf z := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact isConj_iff.mpr ⟨g⁻¹, by simp [rightConjugateElem]⟩
    · intro hx
      obtain ⟨g, hg⟩ := isConj_iff.mp hx
      exact ⟨g⁻¹, by simpa [rightConjugateElem] using hg⟩
  have hsingleton : Group.conjugatesOfSet ({z} : Set G) = conjugatesOf z := by
    ext x
    rw [Group.mem_conjugatesOfSet_iff]
    change (∃ a, a ∈ ({z} : Set G) ∧ IsConj a x) ↔ IsConj z x
    simp only [Set.mem_singleton_iff, exists_eq_left]
  rw [involutionPointHull, hclass, Subgroup.zpowers_eq_closure,
    Subgroup.normalClosure_closure_eq_normalClosure, Subgroup.normalClosure, hsingleton]

theorem normalizer_zpowers_eq_centralizer {z : G} (hz : orderOf z = 2) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) =
      Subgroup.centralizer ({z} : Set G) := by
  have hzne : z ≠ 1 := by intro h; simp [h] at hz
  apply le_antisymm
  · intro g hg
    have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    have hmem : (MulAut.conj g) z ∈ Subgroup.zpowers z := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (Subgroup.mem_zpowers z)
    have hfixed := eq_of_ne_one_of_card_two (Subgroup.zpowers z)
      (by simpa only [Nat.card_zpowers] using hz) (Subgroup.mem_zpowers z) hzne hmem
      (fun h => hzne ((MulAut.conj g).injective (h.trans (map_one _).symm)))
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg (fun x : G => x * g) hfixed
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using h
  · intro g hg
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hfixed : (MulAut.conj g) z = z := by
      change g * z * g⁻¹ = z
      rw [hcomm]
      group
    change Subgroup.zpowers ((MulAut.conj g) z) = Subgroup.zpowers z
    rw [hfixed]

variable [Finite G]

theorem order_two_hull_factorization (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G)) :
    (Nat.card (involutionPointHull z)).factorization 2 = 1 := by
  let L := Subgroup.normalClosure (Subgroup.zpowers z : Set G)
  have hindex : (oddCore L).index = 2 := (order_two_odd_core_hull T z hzT hz hclosed).2.2
  have hcard : Nat.card L = Nat.card (oddCore L) * 2 := by
    rw [← (oddCore L).card_mul_index, hindex]
  have hodd : Odd (Nat.card (oddCore L)) := CFSG.ComponentClassification.OddCore.odd_card L
  have hzero : (Nat.card (oddCore L)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (fun hdvd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd))
  rw [involutionPointHull_eq_normalClosure_zpowers, hcard,
    Nat.factorization_mul (Nat.card_pos (α := oddCore L)).ne' (by decide),
    Finsupp.add_apply, hzero,
    Nat.prime_two.factorization_self, zero_add]

theorem involutions_isConj_of_two_part_one (hfactor : (Nat.card G).factorization 2 = 1)
    {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2) : IsConj z t := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 G := Sylow.ofCard (Subgroup.zpowers z)
    (by rw [Nat.card_zpowers, hz, hfactor, pow_one])
  let Q : Sylow 2 G := Sylow.ofCard (Subgroup.zpowers t)
    (by rw [Nat.card_zpowers, ht, hfactor, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hmem : (MulAut.conj g) z ∈ (g • P : Sylow 2 G) :=
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (Subgroup.mem_zpowers z)
  rw [hg] at hmem
  change (MulAut.conj g) z ∈ Subgroup.zpowers t at hmem
  have hzne : z ≠ 1 := by intro h; simp [h] at hz
  have htne : t ≠ 1 := by intro h; simp [h] at ht
  exact isConj_iff.mpr ⟨g, eq_of_ne_one_of_card_two (Subgroup.zpowers t)
    (by simpa only [Nat.card_zpowers] using ht) (Subgroup.mem_zpowers t) htne hmem
    (fun h => hzne ((MulAut.conj g).injective (h.trans (map_one _).symm)))⟩

theorem involution_eq_of_centralizing_of_two_part_one
    (hfactor : (Nat.card G).factorization 2 = 1) {z t : G}
    (hz : orderOf z = 2) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer ({z} : Set G)) : t = z := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({z} : Set G)
  let zC : C := ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  let tC : C := ⟨t, htC⟩
  have hzCorder : orderOf zC = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have htCorder : orderOf tC = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hzcenter : zC ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro c
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.property
  let : (Subgroup.zpowers zC).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzcenter)
  have hztwo : IsPGroup 2 (Subgroup.zpowers zC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzCorder, pow_one])
  have httwo : IsPGroup 2 (Subgroup.zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htCorder, pow_one])
  obtain ⟨S, htS⟩ := httwo.exists_le_sylow
  have hzS : zC ∈ (S : Subgroup C) := hztwo.le_sylow_of_normal S (Subgroup.mem_zpowers zC)
  have htS' : tC ∈ (S : Subgroup C) := htS (Subgroup.mem_zpowers tC)
  obtain ⟨P, hSP⟩ := (S.isPGroup'.map C.subtype).exists_le_sylow
  have hcardle : Nat.card (S : Subgroup C) ≤ 2 := by
    have h := Subgroup.card_le_of_le hSP
    rw [Subgroup.card_map_of_injective C.subtype_injective, P.card_eq_multiplicity,
      hfactor, pow_one] at h
    exact h
  have htwo : 2 ∣ Nat.card (S : Subgroup C) := by
    have h := Subgroup.orderOf_dvd_natCard (S : Subgroup C) htS'
    rwa [htCorder] at h
  have hcard : Nat.card (S : Subgroup C) = 2 := by
    have hpos := Nat.card_pos (α := (S : Subgroup C))
    omega
  have hzne : zC ≠ 1 := by intro h; simp [h] at hzCorder
  have htne : tC ≠ 1 := by intro h; simp [h] at htCorder
  exact congrArg Subtype.val
    (eq_of_ne_one_of_card_two (S : Subgroup C) hcard hzS hzne htS' htne)

theorem centralizer_stronglyEmbedded_of_two_part_one
    (hfactor : (Nat.card G).factorization 2 = 1) {z : G} (hz : orderOf z = 2)
    (hproper : Subgroup.centralizer ({z} : Set G) ≠ ⊤) :
    fusionStronglyEmbedded (Subgroup.centralizer ({z} : Set G)) := by
  let M := Subgroup.centralizer ({z} : Set G)
  have hzM : z ∈ M := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨hproper, even_iff_two_dvd.mpr (hz ▸ Subgroup.orderOf_dvd_natCard M hzM), ?_⟩
  intro g hg
  rw [← Nat.not_even_iff_odd]
  intro heven
  let I := M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := I) 2
    (even_iff_two_dvd.mp heven)
  have hxorder : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hxz : (x : G) = z :=
    involution_eq_of_centralizing_of_two_part_one hfactor hz hxorder x.property.1
  obtain ⟨t, htM, htx⟩ := Subgroup.mem_map.mp x.property.2
  change (MulAut.conj g⁻¹) t = (x : G) at htx
  have htorder : orderOf t = 2 := by
    rw [← (MulAut.conj g⁻¹).orderOf_eq t, htx]
    exact hxorder
  have htz : t = z := involution_eq_of_centralizing_of_two_part_one hfactor hz htorder htM
  simp only [MulAut.conj_apply, inv_inv] at htx
  rw [htz, hxz] at htx
  apply hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := congrArg (fun y : G => g * y) htx
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h.symm

theorem order_two_hull_pointClass_image (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G)) :
    let L := involutionPointHull z
    let zL : L := ⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩
    L.subtype '' involutionPointClass zL = involutionPointClass z := by
  dsimp only
  let L := involutionPointHull z
  let zL : L := ⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩
  have hzLorder : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans hz
  ext t
  constructor
  · rintro ⟨s, ⟨g, hg⟩, rfl⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  · intro ht
    have htL : t ∈ L := Subgroup.subset_closure ht
    let tL : L := ⟨t, htL⟩
    have htLorder : orderOf tL = 2 := (Subgroup.orderOf_coe tL).symm.trans
      (order_two_of_mem_pointClass hz ht)
    have hconj := involutions_isConj_of_two_part_one
      (order_two_hull_factorization T z hzT hz hclosed) hzLorder htLorder
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    refine ⟨tL, ⟨g⁻¹, ?_⟩, rfl⟩
    simpa only [rightConjugateElem, inv_inv] using hg

theorem order_two_hull_centralizer_ne_top (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G))
    (hnormal : ¬ (Subgroup.zpowers z).Normal) :
    let L := involutionPointHull z
    let zL : L := ⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩
    Subgroup.centralizer ({zL} : Set L) ≠ ⊤ := by
  dsimp only
  let L := involutionPointHull z
  let zL : L := ⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩
  intro htop
  have hfixed (g : G) : rightConjugateElem z g = z := by
    have htclass : rightConjugateElem z g ∈ involutionPointClass z := ⟨g, rfl⟩
    rw [← order_two_hull_pointClass_image T z hzT hz hclosed] at htclass
    obtain ⟨t, ⟨l, hl⟩, ht⟩ := htclass
    have hlC : l ∈ Subgroup.centralizer ({zL} : Set L) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hlcomm := Subgroup.mem_centralizer_singleton_iff.mp hlC
    have hlfix : rightConjugateElem zL l = zL := by
      change l⁻¹ * zL * l = zL
      rw [mul_assoc, ← hlcomm]
      group
    exact ht.symm.trans (congrArg Subtype.val (hl.symm.trans hlfix))
  apply hnormal
  apply Subgroup.normalizer_eq_top_iff.mp
  rw [normalizer_zpowers_eq_centralizer hz]
  apply top_unique
  intro g _
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := congrArg (fun y : G => g * y) (hfixed g)
  simpa only [rightConjugateElem, ← mul_assoc, mul_inv_cancel, one_mul] using h.symm

omit [Finite G] in
theorem order_two_hull_centralizer_subgroupOf (z : G) :
    let L := involutionPointHull z
    let zL : L := ⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩
    (Subgroup.centralizer ({z} : Set G)).subgroupOf L =
      Subgroup.centralizer ({zL} : Set L) := by
  dsimp only
  ext x
  constructor
  · intro hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hx))
  · intro hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx))

theorem order_two_hull_strong_embedding (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G)) (hz : orderOf z = 2)
    (hclosed : fusionStronglyClosed (Subgroup.zpowers z : Set G) (T : Subgroup G))
    (hnormal : ¬ (Subgroup.zpowers z).Normal) :
    let L := involutionPointHull z
    let zL : L := ⟨z, Subgroup.subset_closure (distinguished_mem_pointClass z)⟩
    (⟨z, hzT⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) ∧
      2 ^ (Nat.card L).factorization 2 = 2 ∧
      L.subtype '' involutionPointClass zL = involutionPointClass z ∧
      Subgroup.normalizer (Subgroup.zpowers z : Set G) =
        Subgroup.centralizer ({z} : Set G) ∧
      (Subgroup.centralizer ({z} : Set G)).subgroupOf L =
        Subgroup.centralizer ({zL} : Set L) ∧
      fusionStronglyEmbedded ((Subgroup.centralizer ({z} : Set G)).subgroupOf L) := by
  dsimp only
  refine ⟨central_in_sylow_of_order_two T z hzT hz hclosed, ?_,
    order_two_hull_pointClass_image T z hzT hz hclosed,
    normalizer_zpowers_eq_centralizer hz, order_two_hull_centralizer_subgroupOf z, ?_⟩
  · rw [order_two_hull_factorization T z hzT hz hclosed, pow_one]
  · rw [order_two_hull_centralizer_subgroupOf]
    exact centralizer_stronglyEmbedded_of_two_part_one
      (order_two_hull_factorization T z hzT hz hclosed)
      ((Subgroup.orderOf_coe _).symm.trans hz)
      (order_two_hull_centralizer_ne_top T z hzT hz hclosed hnormal)

end CFSG.ShultStronglyClosedTI
