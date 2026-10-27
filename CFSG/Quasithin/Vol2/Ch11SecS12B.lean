module

public import CFSG.Quasithin.Background.OperatorJordanHolderJH2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.OperatorJH
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix commutatorElement

variable {G : Type} [Group G]

section Basic

variable {Y K : Subgroup G} {x : G} {F : Type} [Field F] {α₀ : ↥K →* ↥(StatedSL 2 F)}

theorem labMultiset_eq_zero_of_central (hKY : K ≤ Y) (hα : Function.Surjective α₀) :
    ∀ (l : List (Subgroup G × Option F)) {C D : Subgroup G},
      (∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈ C) → IsLabSeries Y K x α₀ C l D →
      labMultiset l = 0 := by
  intro l
  induction l with
  | nil => intro C D _ _; rfl
  | cons p l ih =>
    intro C D hcent hl
    obtain ⟨hf, hl'⟩ := hl
    have hCp : C ≤ p.1 := hf.1.le
    have hpD : p.1 ≤ D := hl'.le
    have hnone : p.2 = none := by
      rcases hp : p.2 with _ | a
      · rfl
      · exfalso
        have hf' := hf.2.2.2.2.2
        rw [hp] at hf'
        exact IsNatEigSection.not_centralized hf' le_rfl hα (hKY.trans hf.2.2.2.1)
          fun k hk s hs => hcent k hk s (hpD hs)
    rw [labMultiset_cons, hnone, ih (fun k hk d hd => hCp (hcent k hk d hd)) hl']
    rfl

theorem one_le_count_tw [DecidableEq F] {μ : F} (hμ3 : μ ^ 3 = 1) {j : ℕ} (hj : j < 3) :
    1 ≤ Multiset.count (1 : F) ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F) := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ3
  rw [Multiset.one_le_count_iff_mem]
  interval_cases j
  · simp
  · simp [mul_inv_cancel₀ hμ0]
  · simp [hμ3]

theorem j_eq_zero_of_count [DecidableEq F] {μ ω : F} (hμ3 : μ ^ 3 = 1) {j : ℕ} (hj : j < 3)
    (hω : ω ≠ 1)
    (hωc : Multiset.count ω ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F) = 1) :
    j = 0 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ3
  have hinv : μ⁻¹ = μ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', hμ3])
  interval_cases j
  · rfl
  · exfalso
    have e : ({μ ^ (1 + 1), (μ ^ 1)⁻¹, μ ^ 1 * μ⁻¹} : Multiset F) = {μ ^ 2, μ ^ 2, 1} := by
      rw [pow_one, mul_inv_cancel₀ hμ0, hinv]
    rw [e] at hωc
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hωc
    by_cases h2 : ω = μ ^ 2 <;> simp [h2, hω] at hωc
  · exfalso
    have e2 : (μ ^ 2)⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [← pow_succ', hμ3])
    have e3 : μ ^ 2 * μ⁻¹ = μ := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hμ0, mul_one]
    have e : ({μ ^ (2 + 1), (μ ^ 2)⁻¹, μ ^ 2 * μ⁻¹} : Multiset F) = {1, μ, μ} := by
      rw [show μ ^ (2 + 1) = 1 from hμ3, e2, e3]
    rw [e] at hωc
    simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton] at hωc
    by_cases h2 : ω = μ
    · simp only [h2, ite_true] at hωc
      split_ifs at hωc <;> omega
    · simp [h2, hω] at hωc

end Basic

section Count

theorem le_normalizer_of_comm {V₁ U C D : Subgroup G} (hV₁C : V₁ ≤ C) (hCU : C ≤ U)
    (hDU : D ≤ U) (hab : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ V₁) :
    D ≤ Subgroup.normalizer (C : Set G) := by
  have key : ∀ g ∈ D, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    have h1 := hV₁C (hab g (hDU hg) c (hCU hc))
    have e : g * c * g⁻¹ = (g * c * g⁻¹ * c⁻¹) * c := by group
    rw [e]
    exact C.mul_mem h1 hc
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (D.inv_mem hg) _ hc
  simpa [mul_assoc] using this

variable {Y K : Subgroup G} {x : G} {F : Type} [Field F] {α₀ : ↥K →* ↥(StatedSL 2 F)}

theorem eq_nil_of_isLabSeries_self {D : Subgroup G} :
    ∀ {l : List (Subgroup G × Option F)}, IsLabSeries Y K x α₀ D l D → l = []
  | [], _ => rfl
  | _ :: _, h => absurd (h.1.1.trans_le h.2.le) (lt_irrefl D)

variable [Finite G]

theorem labMultiset_eq_zero_of_count [DecidableEq F] {Γ L K V₁ U : Subgroup G} {x : G}
    {α₀ : ↥L →* ↥(StatedSL 2 F)} (hLY : L ≤ Y) (hxY : x ∈ Y) (hYΓ : Y ≤ Γ) (hLK : L ≤ K)
    (hα : Function.Surjective α₀) (hUab : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ V₁)
    (hB : ∀ C S : Subgroup G, V₁ ≤ C → S ≤ U → IsYSimple Γ C S →
      (∃ k ∈ K, ∃ s ∈ S, k * s * k⁻¹ * s⁻¹ ∉ C) →
      ∃ (μ : F) (j : ℕ), j < 3 ∧ μ ^ 3 = 1 ∧
        ∃ l : List (Subgroup G × Option F), IsLabSeries Y L x α₀ C l S ∧
          labMultiset l = ({μ ^ (j + 1), (μ ^ j)⁻¹, μ ^ j * μ⁻¹} : Multiset F)) :
    ∀ (t : List (Subgroup G)) (D₁ D₂ : Subgroup G), V₁ ≤ D₁ → D₂ ≤ U → IsYSeries Γ D₁ t D₂ →
      ∀ l : List (Subgroup G × Option F), IsLabSeries Y L x α₀ D₁ l D₂ →
        Multiset.count 1 (labMultiset l) = 0 → labMultiset l = 0 := by
  intro t
  induction t with
  | nil =>
    intro D₁ D₂ _ _ ht l hl _
    have hD : D₁ = D₂ := ht
    subst hD
    rw [eq_nil_of_isLabSeries_self hl]
    rfl
  | cons S' t ih =>
    intro D₁ D₂ hV₁D₁ hD₂U ht l hl h0
    obtain ⟨hS', ht'⟩ := ht
    have hJH := operatorJHNatEig_holds G Y L x 2 F α₀ hLY hxY le_rfl hα
    have hD₁S' : D₁ ≤ S' := ht'.le
    have hS'U : S' ≤ U := hS'.1.le.trans hD₂U
    obtain ⟨l₁, l₂, hl₁, hl₂, hsum⟩ := (hJH D₁ D₂ l hl).2 S' hD₁S' hS'.1.le
      (le_normalizer_of_comm hV₁D₁ (hD₁S'.trans hS'U) hS'U hUab) hS'.2.1 (hYΓ.trans hS'.2.2.1)
    rw [← hsum, Multiset.count_add] at h0
    have h01 : Multiset.count 1 (labMultiset l₁) = 0 := by omega
    have h02 : Multiset.count 1 (labMultiset l₂) = 0 := by omega
    have hz₂ : labMultiset l₂ = 0 := by
      by_cases hc : ∀ k ∈ K, ∀ s ∈ D₂, k * s * k⁻¹ * s⁻¹ ∈ S'
      · exact labMultiset_eq_zero_of_central hLY hα l₂ (fun k hk s hs => hc k (hLK hk) s hs) hl₂
      · push Not at hc
        obtain ⟨μ, j, hj, hμ3, l₃, hl₃, hm₃⟩ :=
          hB S' D₂ (hV₁D₁.trans hD₁S') hD₂U hS' hc
        have heq := (hJH S' D₂ l₃ hl₃).1 l₂ hl₂
        have h03 := one_le_count_tw hμ3 hj
        rw [heq, hm₃] at h02
        omega
    rw [← hsum, ih D₁ S' hV₁D₁ hS'U ht' l₁ hl₁ h01, hz₂, add_zero]

end Count

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
