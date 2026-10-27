module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem inf_centralizer_conj_V₀_eq (h : Hyp65 n M V₀ V g) (hle : conjSubgroup V₀ g ≤ M) :
    V ⊓ centralizer (conjSubgroup V₀ g : Set G) = UOf M V g := by
  have hY : YOf M V₀ g = conjSubgroup V₀ g := inf_eq_left.2 hle
  have hYne : conjSubgroup V₀ g ≠ ⊥ := hY ▸ Y_ne_bot h
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hYne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hCle : centralizer ({x} : Set G) ≤ conjSubgroup M g := h.centralizer_le_conjM hx hx1'
  refine le_antisymm ?_ ?_
  · intro v hv
    exact ⟨hv.1, hCle (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hx) hv.2)⟩
  · intro u hu
    refine ⟨hu.1, ?_⟩
    have h1 : conjSubgroup V₀ g ≤ centralizer (UOf M V g : Set G) := hY ▸ Y_le_centralizer_U h
    exact Subgroup.le_centralizer_iff.1 h1 hu

theorem relIndex_U_eq_two (h : Hyp65 1 M V₀ V g) : (UOf M V g).relIndex V = 2 := by
  have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup h.elemAbelian
  have hfac : (UOf M V g).relIndex V = 2 ^ E3.mQuot V (conjSubgroup M g) := by
    have h1 : (UOf M V g).relIndex V = (conjSubgroup M g).relIndex V := by
      rw [UOf, Subgroup.inf_relIndex_left]
    rw [h1, E3.relIndex_eq_two_pow hV2]
  have hne : (UOf M V g).relIndex V ≠ 1 := by
    intro h1
    apply h.not_V_le_conjM
    exact (Subgroup.relIndex_eq_one.1 h1).trans inf_le_right
  have hm : E3.mQuot V (conjSubgroup M g) ≤ 1 := h.mQuot_le
  rw [hfac] at hne ⊢
  interval_cases hq : E3.mQuot V (conjSubgroup M g)
  · exact absurd (pow_zero 2) hne
  · rfl

theorem commutator_eq_V₀ (h : Hyp65 n M V₀ V g)
    (hcomm : ⁅conjSubgroup V₀ g, V⁆ ≤ V₀) : ⁅V, conjSubgroup V₀ g⁆ = V₀ := by
  refine le_antisymm (by rw [Subgroup.commutator_comm]; exact hcomm) ?_
  obtain ⟨a, haV, haMg⟩ := Set.not_subset.1 h.not_V_le_conjM
  have hmem : ∀ w : ↥(conjSubgroup V₀ g), ⁅a, (w : G)⁆ ∈ V₀ := fun w => by
    rw [← commutatorElement_inv]
    exact V₀.inv_mem (hcomm (Subgroup.commutator_mem_commutator w.2 haV))
  let φ : ↥(conjSubgroup V₀ g) → ↥V₀ := fun w => ⟨⁅a, (w : G)⁆, hmem w⟩
  have hinj : Function.Injective φ := by
    intro w w' hww
    have hEq : a * (w : G) * a⁻¹ * (w : G)⁻¹ = a * (w' : G) * a⁻¹ * (w' : G)⁻¹ := by
      have h0 : ⁅a, (w : G)⁆ = ⁅a, (w' : G)⁆ := congrArg Subtype.val hww
      simpa only [commutatorElement_def] using h0
    have h1 : (w : G) * a⁻¹ * (w : G)⁻¹ = (w' : G) * a⁻¹ * (w' : G)⁻¹ := by
      refine mul_left_cancel (a := a) ?_
      simpa only [mul_assoc] using hEq
    set z : G := (w' : G)⁻¹ * w with hz
    have h2 : a⁻¹ * z = z * a⁻¹ := by
      calc a⁻¹ * z = (w' : G)⁻¹ * ((w' : G) * a⁻¹ * (w' : G)⁻¹) * w := by rw [hz]; group
        _ = (w' : G)⁻¹ * ((w : G) * a⁻¹ * (w : G)⁻¹) * w := by rw [h1]
        _ = z * a⁻¹ := by rw [hz]; group
    have h3 : a * z = z * a := by
      have := (show Commute a⁻¹ z from h2).inv_left
      rwa [inv_inv] at this
    have hzV : z ∈ conjSubgroup V₀ g :=
      (conjSubgroup V₀ g).mul_mem ((conjSubgroup V₀ g).inv_mem w'.2) w.2
    by_contra hne
    have hz1 : z ≠ 1 := by
      intro hz1
      apply hne
      apply Subtype.ext
      have : (w : G) = (w' : G) := by
        calc (w : G) = (w' : G) * ((w' : G)⁻¹ * w) := by group
          _ = (w' : G) := by rw [← hz, hz1, mul_one]
      exact this
    have hC := h.centralizer_le_conjM hzV hz1
    apply haMg
    exact hC (Subgroup.mem_centralizer_singleton_iff.2 h3)
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    exact (E3.card_conjSubgroup V₀ g).ge
  intro v₀ hv₀
  obtain ⟨w, hw⟩ := hbij.2 ⟨v₀, hv₀⟩
  have hw' : ⁅a, (w : G)⁆ = v₀ := congrArg Subtype.val hw
  rw [← hw']
  exact Subgroup.commutator_mem_commutator haV w.2

theorem one_facts (h : Hyp65 1 M V₀ V g) (hs : InCalOStar 1 M V₀ V g) :
    conjSubgroup V₀ g ≤ M ∧ (centralizer (conjSubgroup V₀ g : Set G)).relIndex V = 2 ∧
      ⁅V, conjSubgroup V₀ g⁆ = V₀ := by
  obtain ⟨-, K, -, -, -, -, hcomm, -⟩ := hs
  have hle : conjSubgroup V₀ g ≤ M := by
    rw [← h.normalizer_eq, Subgroup.le_normalizer_iff_commutator_le_right]
    exact hcomm.trans h.le
  refine ⟨hle, ?_, commutator_eq_V₀ h hcomm⟩
  have h1 : (centralizer (conjSubgroup V₀ g : Set G)).relIndex V = (UOf M V g).relIndex V := by
    rw [← h.inf_centralizer_conj_V₀_eq hle, Subgroup.inf_relIndex_left]
  rw [h1]
  exact h.relIndex_U_eq_two

theorem one_facts_conj {k : G}
    (h : Hyp65 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) k)
    (hs : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) k) :
    conjSubgroup V₀ (g * k * g⁻¹) ≤ M ∧
      (centralizer (conjSubgroup V₀ (g * k * g⁻¹) : Set G)).relIndex V = 2 ∧
      ⁅V, conjSubgroup V₀ (g * k * g⁻¹)⁆ = V₀ := by
  obtain ⟨h1, h2, h3⟩ := h.one_facts hs
  have e : ∀ A : Subgroup G, conjSubgroup (conjSubgroup (conjSubgroup A g) k) g⁻¹ =
      conjSubgroup A (g * k * g⁻¹) := fun A => by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · have h4 := E3.conjSubgroup_mono_left g⁻¹ h1
    rwa [e, conjSubgroup_conjSubgroup_inv] at h4
  · have h4 := E3.relIndex_conjSubgroup
      (Subgroup.centralizer (conjSubgroup (conjSubgroup V₀ g) k : Set G)) (conjSubgroup V g) g⁻¹
    rw [E3.conjSubgroup_centralizer, e, conjSubgroup_conjSubgroup_inv, h2] at h4
    exact h4
  · have h4 := congrArg (fun W => conjSubgroup W g⁻¹) h3
    simp only [E3.conjSubgroup_commutator, conjSubgroup_conjSubgroup_inv, e] at h4
    exact h4

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81

end
