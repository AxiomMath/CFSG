module

public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingOddCore
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem oddCore_eq_twoPrimeCore : oddCore G = twoPrimeCore G := by
  unfold oddCore twoPrimeCore pPrimeCore
  congr 1
  ext N
  exact and_congr_right fun _ => Nat.coprime_two_left.symm

theorem square_one_eq_one_of_odd_card {Y : Type*} [Group Y] [Finite Y]
    (hodd : Odd (Nat.card Y)) {y : Y} (hsquare : y ^ 2 = 1) : y = 1 := by
  have horderOdd : Odd (orderOf y) := hodd.of_dvd_nat (orderOf_dvd_natCard y)
  rcases (Nat.dvd_prime Nat.prime_two).mp
      (orderOf_dvd_iff_pow_eq_one.mpr hsquare) with horder | horder
  · exact orderOf_eq_one_iff.mp horder
  · rw [horder] at horderOdd
    norm_num at horderOdd

theorem square_one_eq_one_of_mem_odd_subgroup (R : Subgroup G)
    (hodd : Odd (Nat.card R)) {y : G} (hy : y ∈ R) (hsquare : y ^ 2 = 1) : y = 1 := by
  exact congrArg Subtype.val (square_one_eq_one_of_odd_card hodd
    (y := (⟨y, hy⟩ : R)) (Subtype.ext hsquare))

theorem odd_quotient_injective_on_elementary (V R : Subgroup G) [R.Normal]
    (hV : IsElemAbelian 2 V) (hR : Odd (Nat.card R)) :
    Function.Injective ((QuotientGroup.mk' R).domRestrict V) := by
  intro a b hab
  have hkernel : (a : G)⁻¹ * b ∈ R := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' R) ((a : G)⁻¹ * b) = 1
    rw [map_mul, map_inv]
    change (((QuotientGroup.mk' R).domRestrict V) a)⁻¹ *
      ((QuotientGroup.mk' R).domRestrict V) b = 1
    rw [hab, inv_mul_cancel]
  have hmemV : (a : G)⁻¹ * b ∈ V := V.mul_mem (V.inv_mem a.property) b.property
  have hone := square_one_eq_one_of_mem_odd_subgroup R hR hkernel (hV.2 _ hmemV)
  exact Subtype.ext (inv_mul_eq_one.mp hone)

omit [Finite G] in
theorem twoRankAtLeastTwo_of_elementary_card_ge_four (V : Subgroup G)
    (hV : IsElemAbelian 2 V) (hcard : 4 ≤ Nat.card V) : TwoRankAtLeastTwo V := by
  have htwo : IsPGroup 2 V := isPGroup_iff_pow_pow_eq_one.mpr fun v =>
    ⟨1, by simpa only [pow_one] using (Subtype.ext (hV.2 v v.property) : v ^ 2 = 1)⟩
  obtain ⟨E, hEcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (G := V) (n := 2) (p := 2) Nat.prime_two htwo (by simpa using hcard)
  refine ⟨E, by simpa using hEcard, ?_⟩
  intro v
  apply Subtype.ext
  apply Subtype.ext
  exact hV.2 v v.val.property

omit [Finite G] in
theorem elementary_normalClosure_le_involutionCore (V : Subgroup G)
    (hV : IsElemAbelian 2 V) : Subgroup.normalClosure (V : Set G) ≤ involutionCore G := by
  apply Subgroup.normalClosure_le_normal
  intro v hv
  by_cases hone : v = 1
  · subst v
    exact (involutionCore G).one_mem
  · rw [involutionCore_eq_closure]
    exact Subgroup.subset_closure ⟨hone, hV.2 v hv⟩

omit [Finite G] in
theorem involutionCore_eq_top_of_elementary_hull (V : Subgroup G)
    (hV : IsElemAbelian 2 V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤) :
    involutionCore G = ⊤ := by
  exact top_unique (hgen ▸ elementary_normalClosure_le_involutionCore V hV)

theorem square_one_mem_normal_of_odd_index (N : Subgroup G) [N.Normal]
    (hodd : Odd N.index) {v : G} (hsquare : v ^ 2 = 1) : v ∈ N := by
  apply (QuotientGroup.eq_one_iff v).mp
  apply square_one_eq_one_of_odd_card
  · simpa only [Subgroup.index_eq_card] using hodd
  · change (QuotientGroup.mk' N) v ^ 2 = 1
    rw [← map_pow, hsquare, map_one]

theorem normal_eq_top_of_odd_index_elementary_hull (V N : Subgroup G) [N.Normal]
    (hV : IsElemAbelian 2 V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤)
    (hodd : Odd N.index) : N = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact Subgroup.normalClosure_le_normal fun v hv =>
    square_one_mem_normal_of_odd_index N hodd (hV.2 v hv)

theorem oddCore_le_stronglyEmbedded_of_elementary (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hVH : V ≤ H)
    (hV : IsElemAbelian 2 V) (hcard : 4 ≤ Nat.card V) : oddCore G ≤ H := by
  obtain ⟨E, hEcard, hEsquare⟩ := twoRankAtLeastTwo_of_elementary_card_ge_four V hV hcard
  let W : Subgroup G := E.map V.subtype
  have hWH : W ≤ H := (Subgroup.map_subtype_le E).trans hVH
  have hWcard : Nat.card W = 4 := by
    rw [Subgroup.card_map_of_injective V.subtype_injective]
    exact hEcard
  have hWsq : ∀ w : W, w ^ 2 = 1 := by
    intro w
    obtain ⟨v, hv, heq⟩ := Subgroup.mem_map.mp w.property
    apply Subtype.ext
    change (w : G) ^ 2 = 1
    rw [← heq]
    exact congrArg (fun x : E => (x : G)) (hEsquare ⟨v, hv⟩)
  exact fourGroup_odd_subgroup_le_stronglyEmbedded (native_strong_embedding_of_order_conditions hH) hWH hWcard hWsq
    (Subgroup.le_normalizer_of_normal) (CFSG.ComponentClassification.OddCore.odd_card G)

theorem elementary_commutes_with_odd_core (H V : Subgroup G) (hVH : V ≤ H)
    (hVnormal : (V.subgroupOf H).Normal) (hV : IsElemAbelian 2 V)
    (hRH : oddCore G ≤ H) {v r : G} (hv : v ∈ V) (hr : r ∈ oddCore G) :
    Commute r v := by
  have hHN : H ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVH).mp hVnormal
  have hconj : r * v * r⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hHN (hRH hr)) v).mp hv
  have hcommV : ⁅r, v⁆ ∈ V := V.mul_mem hconj (V.inv_mem hv)
  have hcommR : ⁅r, v⁆ ∈ oddCore G := by
    have hconjR := (inferInstance : (oddCore G).Normal).conj_mem r⁻¹
      ((oddCore G).inv_mem hr) v
    simpa only [commutatorElement_def, mul_assoc] using (oddCore G).mul_mem hr hconjR
  have hone := square_one_eq_one_of_mem_odd_subgroup (oddCore G)
    (CFSG.ComponentClassification.OddCore.odd_card G) hcommR (hV.2 _ hcommV)
  exact commutatorElement_eq_one_iff_commute.mp hone

theorem oddCore_le_center_of_normal_elementary_hull (H V : Subgroup G)
    (hH : fusionStronglyEmbedded H) (hVH : V ≤ H)
    (hVnormal : (V.subgroupOf H).Normal) (hV : IsElemAbelian 2 V)
    (hcard : 4 ≤ Nat.card V) (hgen : Subgroup.normalClosure (V : Set G) = ⊤) :
    oddCore G ≤ Subgroup.center G := by
  have hRH := oddCore_le_stronglyEmbedded_of_elementary H V hH hVH hV hcard
  have hVne : V ≠ ⊥ := by intro hbot; simp [hbot] at hcard
  obtain ⟨v, hvne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
  have hvneG : (v : G) ≠ 1 := fun h => hvne (Subtype.ext h)
  have hcentral : twoPrimeCore G ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
    rw [← oddCore_eq_twoPrimeCore]
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (elementary_commutes_with_odd_core H V hVH hVnormal hV hRH v.property hr)
  rw [oddCore_eq_twoPrimeCore]
  exact (native_strong_embedding_of_order_conditions hH).twoPrimeCore_le_center_of_involutionCore_eq_top
    ⟨hvneG, hV.2 v v.property⟩ hcentral (involutionCore_eq_top_of_elementary_hull V hV hgen)

end CFSG.ShultStronglyClosedTI
