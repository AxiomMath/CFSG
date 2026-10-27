module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresComplement
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SixF

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X]

theorem mem_normalizer_of_comm_mod {P N Y : Subgroup X} (hNY : N ≤ Y) (hYP : Y ≤ P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x⁻¹ * y⁻¹ * x * y ∈ N) {g : X} (hg : g ∈ P) :
    g ∈ normalizer (Y : Set X) := by
  have key : ∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
    intro g hg y hy
    have h1 : g * y * g⁻¹ = y * (y⁻¹ * g⁻¹⁻¹ * y * g⁻¹) := by group
    rw [h1]
    exact mul_mem hy (hNY (hcomm y (hYP hy) g⁻¹ (inv_mem hg)))
  refine mem_normalizer_iff.mpr fun y => ⟨fun hy => key g hg y hy, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

theorem mul_eq_sup_of_comm_mod {P N A B : Subgroup X} (hNP : N ≤ P)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x⁻¹ * y⁻¹ * x * y ∈ N) (hAP : A ≤ P) (hBP : B ≤ P)
    (hN : (N : Set X) ⊆ (A : Set X) * (B : Set X)) :
    (A : Set X) * (B : Set X) = ((A ⊔ B : Subgroup X) : Set X) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  have hAN := coe_mul_of_left_le_normalizer_right A N fun g hg =>
    mem_normalizer_of_comm_mod le_rfl hNP hcomm (hAP hg)
  have hNB := coe_mul_of_right_le_normalizer_left N B fun g hg =>
    mem_normalizer_of_comm_mod le_rfl hNP hcomm (hBP hg)
  have hST := coe_mul_of_left_le_normalizer_right (A ⊔ N) (N ⊔ B) fun g hg =>
    mem_normalizer_of_comm_mod le_sup_left (sup_le hNP hBP) hcomm (sup_le hAP hNP hg)
  intro x hx
  have hle : A ⊔ B ≤ (A ⊔ N) ⊔ (N ⊔ B) :=
    sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_right)
  have hx' : x ∈ (A ⊔ N) ⊔ (N ⊔ B) := hle hx
  rw [← SetLike.mem_coe, hST, hAN, hNB] at hx'
  obtain ⟨_, ⟨a, ha, m, hm, rfl⟩, _, ⟨m', hm', b, hb, rfl⟩, rfl⟩ := hx'
  obtain ⟨a', ha', b', hb', hab⟩ := hN (mul_mem hm hm')
  refine ⟨a * a', mul_mem ha ha', b' * b, mul_mem hb' hb, ?_⟩
  change a * a' * (b' * b) = a * m * (m' * b)
  rw [show a * m * (m' * b) = a * (m * m') * b by group, ← hab]
  group

omit [Group X] in
theorem mul_mem_iff_of_relIndex_two {X : Type*} [Group X] {Y E : Subgroup X}
    (hidx : Y.relIndex E = 2) {y z : X} (hy : y ∈ E) (hz : z ∈ E) :
    y * z ∈ Y ↔ (y ∈ Y ↔ z ∈ Y) := by
  have h := mul_mem_iff_of_index_two (H := Y.subgroupOf E) hidx (a := ⟨y, hy⟩) (b := ⟨z, hz⟩)
  simpa [mem_subgroupOf] using h

theorem mem_of_perfect_of_index_two {C Y E : Subgroup X} [Group.IsPerfect ↥C]
    (hidx : Y.relIndex E = 2) (hCY : C ≤ normalizer (Y : Set X)) {x : X}
    (hx : ∀ c ∈ C, x⁻¹ * c * x * c⁻¹ ∈ E) : ∀ c ∈ C, x⁻¹ * c * x * c⁻¹ ∈ Y := by
  classical
  set d : X → X := fun c => x⁻¹ * c * x * c⁻¹ with hd
  have hdm : ∀ c₁ c₂ : X, d (c₁ * c₂) = d c₁ * (c₁ * d c₂ * c₁⁻¹) := fun c₁ c₂ => by
    simp only [hd]
    group
  have hiff : ∀ c₁ ∈ C, ∀ c₂ ∈ C, (d (c₁ * c₂) ∈ Y ↔ (d c₁ ∈ Y ↔ d c₂ ∈ Y)) := by
    intro c₁ hc₁ c₂ hc₂
    have h1 : c₁ * d c₂ * c₁⁻¹ ∈ E := by
      have := mul_mem (inv_mem (hx c₁ hc₁)) (hx _ (mul_mem hc₁ hc₂))
      rwa [show (d c₁)⁻¹ * d (c₁ * c₂) = c₁ * d c₂ * c₁⁻¹ by rw [hdm]; group] at this
    rw [hdm, mul_mem_iff_of_relIndex_two hidx (hx c₁ hc₁) h1,
      ← mem_normalizer_iff.mp (hCY hc₁) (d c₂)]
  let f : ↥C →* Multiplicative (ZMod 2) :=
    { toFun := fun c => if d c ∈ Y then 1 else Multiplicative.ofAdd 1
      map_one' := by simp [hd]
      map_mul' := fun c₁ c₂ => by
        have h := hiff c₁ c₁.2 c₂ c₂.2
        change (if d ((c₁ : X) * c₂) ∈ Y then 1 else Multiplicative.ofAdd (1 : ZMod 2)) =
          (if d c₁ ∈ Y then 1 else Multiplicative.ofAdd 1) *
            (if d c₂ ∈ Y then 1 else Multiplicative.ofAdd 1)
        rcases em (d c₁ ∈ Y) with h₁ | h₁ <;> rcases em (d c₂ ∈ Y) with h₂ | h₂
        · have h12 : d ((c₁ : X) * c₂) ∈ Y := h.mpr (iff_of_true h₁ h₂)
          simp only [h12, h₁, h₂, ite_true, mul_one]
        · have h12 : d ((c₁ : X) * c₂) ∉ Y := fun h3 => h₂ ((h.mp h3).mp h₁)
          simp only [h12, h₁, h₂, ite_true, ite_false, one_mul]
        · have h12 : d ((c₁ : X) * c₂) ∉ Y := fun h3 => h₁ ((h.mp h3).mpr h₂)
          simp only [h12, h₁, h₂, ite_true, ite_false, mul_one]
        · have h12 : d ((c₁ : X) * c₂) ∈ Y := h.mpr (iff_of_false h₁ h₂)
          simp only [h12, h₁, h₂, ite_true, ite_false]
          decide }
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := ↥C), _root_.commutator_def,
      commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  intro c hc
  have h1 : f ⟨c, hc⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact mem_top _
  by_contra h2
  have h2' : ¬ d c ∈ Y := h2
  have h3 : f ⟨c, hc⟩ = Multiplicative.ofAdd 1 := by
    change (if d c ∈ Y then 1 else Multiplicative.ofAdd (1 : ZMod 2)) = _
    simp only [h2', ite_false]
  rw [h3] at h1
  exact absurd h1 (by decide)

theorem le_of_elementary_mod {E X₀ U D Y : Subgroup X} {t : X} (htt : t * t = 1)
    (hcov : ∀ e ∈ E, e ∈ X₀ ∨ t * e ∈ X₀) (hX₀E : X₀ ≤ E)
    (hUc : ∀ u ∈ U, ∀ e ∈ E, u * e = e * u)
    (hX₀ : ∀ x ∈ X₀, ∀ y ∈ X₀, x * x ∈ U ∧ x⁻¹ * y⁻¹ * x * y ∈ U)
    (hD : ∀ x ∈ X₀, x⁻¹ * t⁻¹ * x * t ∈ U → x ∈ D) (htD : t ∈ D)
    (hYE : Y ≤ E) (hY : ∀ x ∈ Y, ∀ y ∈ Y, x * x ∈ U ∧ x⁻¹ * y⁻¹ * x * y ∈ U)
    (hYX : ¬ Y ≤ X₀) : Y ≤ D := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨y₀, hy₀Y, hy₀X⟩ := IsConcreteLE.not_le_iff_exists.mp hYX
  have hx₀ : t * y₀ ∈ X₀ := (hcov y₀ (hYE hy₀Y)).resolve_left hy₀X
  set x₀ := t * y₀ with hx₀def
  have hy₀ : y₀ = t * x₀ := by rw [hx₀def, ← mul_assoc, htt, one_mul]
  have hA : ∀ y ∈ Y, y ∈ X₀ → y ∈ D := by
    intro y hyY hyX
    refine hD y hyX ?_
    have c₁ := (hY y hyY y₀ hy₀Y).2
    have c₂ := (hX₀ y hyX x₀ hx₀).2
    have e : y⁻¹ * t⁻¹ * y * t =
        x₀ * ((y⁻¹ * x₀⁻¹ * y * x₀)⁻¹ * (y⁻¹ * y₀⁻¹ * y * y₀)) * x₀⁻¹ := by
      rw [hy₀]
      group
    have hu : (y⁻¹ * x₀⁻¹ * y * x₀)⁻¹ * (y⁻¹ * y₀⁻¹ * y * y₀) ∈ U := mul_mem (inv_mem c₂) c₁
    rw [e, ← hUc _ hu x₀ (hX₀E hx₀), mul_inv_cancel_right]
    exact hu
  have hy₀D : y₀ ∈ D := by
    have hx₀D : x₀ ∈ D := by
      refine hD x₀ hx₀ ?_
      have hu := (hY y₀ hy₀Y y₀ hy₀Y).1
      have hv := (hX₀ x₀ hx₀ x₀ hx₀).1
      have e : x₀⁻¹ * t⁻¹ * x₀ * t = x₀⁻¹ * (y₀ * y₀) * x₀⁻¹ := by
        rw [hy₀, htinv]
        group
      rw [e, ← hUc _ hu x₀⁻¹ (inv_mem (hX₀E hx₀)), mul_assoc, ← mul_inv_rev]
      exact mul_mem hu (inv_mem hv)
    rw [hy₀]
    exact mul_mem htD hx₀D
  intro y hyY
  rcases hcov y (hYE hyY) with hyX | hyX
  · exact hA y hyY hyX
  · have h1 : y₀⁻¹ * y ∈ X₀ := by
      have := mul_mem (inv_mem hx₀) hyX
      rwa [hx₀def, mul_inv_rev, mul_assoc, ← mul_assoc t⁻¹, inv_mul_cancel, one_mul] at this
    have h2 := hA _ (mul_mem (inv_mem hy₀Y) hyY) h1
    have := mul_mem hy₀D h2
    rwa [mul_inv_cancel_left] at this

@[expose] def WeylProductConclusion {G : Type} [Group G] (M M' P E X A V C J₀ : Subgroup G)
    (t w : G) (q e : ℕ) : Prop :=
  (M : Set G) * (M' : Set G) = ((M ⊔ M' : Subgroup G) : Set G) ∧ M ⊔ M' ≤ P ∧ M ⊓ M' = V ∧
    ((M ⊔ M' : Subgroup G) : Set G) * (E : Set G) = (P : Set G) ∧ (M ⊔ M') ⊓ E = X ∧
    Nat.card (M ⊔ M' : Subgroup G) = q ^ e ∧
    (P ≤ normalizer ((M ⊔ M' : Subgroup G) : Set G) ∧ (M ⊔ M') ⊔ zpowers t = P ∧
      (M ⊔ M') ⊓ zpowers t = ⊥) ∧
    (M ⊔ M') ⊓ C = A ∧ J₀ ≤ normalizer ((M ⊔ M' : Subgroup G) : Set G) ∧
    t ∈ normalizer ((M ⊔ M' : Subgroup G) : Set G) ∧
    w ∈ normalizer ((M ⊔ M' : Subgroup G) : Set G)

end SixF

end CFSG.LocalAnalysis.SymplecticFourStandard
