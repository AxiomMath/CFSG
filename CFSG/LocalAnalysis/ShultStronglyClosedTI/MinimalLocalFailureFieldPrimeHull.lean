module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedOddFixedSet
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldAlgebra

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem conj_mem_closure_conjugacyWithin {Y : Subgroup G} {r a : G} (ha : a ∈ Y) {x : G}
    (hx : x ∈ Subgroup.closure (conjugacyWithin Y r)) :
    a * x * a⁻¹ ∈ Subgroup.closure (conjugacyWithin Y r) := by
  induction hx using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    apply Subgroup.subset_closure
    refine ⟨k * ⟨a, ha⟩⁻¹, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  | one => simp
  | mul x w _ _ hx hw =>
    have he : a * (x * w) * a⁻¹ = (a * x * a⁻¹) * (a * w * a⁻¹) := by group
    rw [he]
    exact Subgroup.mul_mem _ hx hw
  | inv x _ hx =>
    have he : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [he]
    exact Subgroup.inv_mem _ hx

@[expose] def conjAutOfNormalizes (L : Subgroup G) {a : G} (hL : ∀ x ∈ L, a * x * a⁻¹ ∈ L)
    (hL' : ∀ x ∈ L, a⁻¹ * x * a ∈ L) : L ≃* L where
  toFun x := ⟨a * x * a⁻¹, hL x x.2⟩
  invFun x := ⟨a⁻¹ * x * a, hL' x x.2⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv x := Subtype.ext (by simp only; group)
  map_mul' x w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conj_mem_oddCore_image {L : Subgroup G} {a : G} (hL : ∀ x ∈ L, a * x * a⁻¹ ∈ L)
    (hL' : ∀ x ∈ L, a⁻¹ * x * a ∈ L) {g : G} (hg : g ∈ (CFSG.oddCore L).map L.subtype) :
    a * g * a⁻¹ ∈ (CFSG.oddCore L).map L.subtype := by
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hg
  let φ := conjAutOfNormalizes L hL hL'
  have hinv : (CFSG.oddCore L).map φ.toMonoidHom = CFSG.oddCore L :=
    CFSG.ComponentClassification.OddCore.char_invariant φ
  have hφl : φ l ∈ CFSG.oddCore L := by
    rw [← hinv]
    exact Subgroup.mem_map_of_mem _ hl
  exact Subgroup.mem_map.mpr ⟨φ l, hφl, rfl⟩

theorem oddCore_le_center_of_commutator [Finite G] {Y L : Subgroup G} (hLY : L ≤ Y)
    (hnorm : ∀ a ∈ Y, ∀ x ∈ L, a * x * a⁻¹ ∈ L)
    (hRL : ⁅(CFSG.oddCore Y).map Y.subtype, L⁆ = ⊥) :
    (CFSG.oddCore L).map L.subtype ≤ (CFSG.oddCore Y).map Y.subtype ∧
      CFSG.oddCore L ≤ Subgroup.center L := by
  let RL := (CFSG.oddCore L).map L.subtype
  have hRLY : RL ≤ Y := (Subgroup.map_subtype_le _).trans hLY
  have hnormal : (RL.subgroupOf Y).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : ((g : G))⁻¹ ∈ Y := Y.inv_mem g.2
    have hmem := conj_mem_oddCore_image (L := L) (a := (g : G))
      (fun x hx => hnorm _ g.2 x hx)
      (fun x hx => by simpa only [inv_inv] using hnorm _ hg x hx) hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  have hodd : Odd (Nat.card RL) := odd_card_oddCore_map L
  have hRLR : RL ≤ (CFSG.oddCore Y).map Y.subtype :=
    le_oddCore_map_of_normal_odd hRLY hnormal hodd
  refine ⟨hRLR, ?_⟩
  intro l hl
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hcomm : ∀ g ∈ (CFSG.oddCore Y).map Y.subtype, ∀ w ∈ L, g * w = w * g := by
    intro g hg w hw
    have hc : ⁅g, w⁆ ∈ ⁅(CFSG.oddCore Y).map Y.subtype, L⁆ :=
      Subgroup.commutator_mem_commutator hg hw
    rw [hRL, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  apply Subtype.ext
  have hlR : (l : G) ∈ (CFSG.oddCore Y).map Y.subtype :=
    hRLR (Subgroup.mem_map_of_mem L.subtype hl)
  exact (hcomm _ hlR _ x.2).symm

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
