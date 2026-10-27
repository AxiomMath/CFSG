module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelSpNormal
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.CTP CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem exists_spForm_eq_pair {l : ℕ} {F : Type} [Field F] {a a' : Fin l ⊕ Fin l → F}
    (ha : a ≠ 0) (ha' : ∀ c : F, a' ≠ c • a) (α β : F) :
    ∃ u : Fin l ⊕ Fin l → F, spForm l F u a = α ∧ spForm l F u a' = β := by
  have key : ∀ {x y : Fin l ⊕ Fin l → F}, x ≠ 0 → (∀ c : F, y ≠ c • x) →
      ∃ w, spForm l F w x = 0 ∧ spForm l F w y = 1 := by
    intro x y hx hy
    obtain ⟨u₁, hu₁⟩ : ∃ u, spForm l F u x ≠ 0 := by
      by_contra hcon
      apply hx
      apply (spForm_nondegenerate (r := l) (K := F)).2 x
      intro u
      by_contra hu
      exact hcon ⟨u, hu⟩
    set u₀ := (spForm l F u₁ x)⁻¹ • u₁ with hu₀
    have hu₀x : spForm l F u₀ x = 1 := by
      rw [hu₀, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hu₁]
    obtain ⟨w, hwx, hwy⟩ : ∃ w, spForm l F w x = 0 ∧ spForm l F w y ≠ 0 := by
      by_contra hcon
      apply hy (spForm l F u₀ y)
      have h0 : y - spForm l F u₀ y • x = 0 := by
        apply (spForm_nondegenerate (r := l) (K := F)).2 _
        intro w
        have h1 : spForm l F (w - spForm l F w x • u₀) x = 0 := by
          rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, hu₀x, smul_eq_mul,
            mul_one, sub_self]
        have h2 : spForm l F (w - spForm l F w x • u₀) y = 0 := by
          by_contra h
          exact hcon ⟨_, h1, h⟩
        rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
          sub_eq_zero] at h2
        rw [map_sub, map_smul, smul_eq_mul, h2, sub_eq_zero, mul_comm]
      exact sub_eq_zero.mp h0
    refine ⟨(spForm l F w y)⁻¹ • w, ?_, ?_⟩
    · rw [map_smul, LinearMap.smul_apply, hwx, smul_zero]
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hwy]
  obtain ⟨w₁, hw₁a, hw₁a'⟩ := key ha ha'
  have ha'0 : a' ≠ 0 := fun h => ha' 0 (by rw [h, zero_smul])
  have ha'' : ∀ c : F, a ≠ c • a' := by
    intro c h
    have hc : c ≠ 0 := by
      rintro rfl
      exact ha (by rw [h, zero_smul])
    exact ha' c⁻¹ (by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul])
  obtain ⟨w₂, hw₂a', hw₂a⟩ := key ha'0 ha''
  refine ⟨α • w₂ + β • w₁, ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, hw₂a, hw₁a]
    simp
  · rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, hw₂a', hw₁a']
    simp

private theorem exists_smul_of_mem_of_isTransvection {l : ℕ} {F : Type} [Field F]
    (A : Subgroup ↥(StatedSp l F))
    (hAt : ∀ x ∈ A, x ≠ 1 → IsSymplecticTransvectionIn l x)
    {a a' : Fin l ⊕ Fin l → F} {c c' : F} (ha : a ≠ 0) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hx : spTransvection a c ∈ A) (hy : spTransvection a' c' ∈ A) :
    ∃ μ : F, a' = μ • a := by
  by_contra hne
  have hne' : ∀ μ : F, a' ≠ μ • a := fun μ h => hne ⟨μ, h⟩
  obtain ⟨u₁, hu₁a, hu₁a'⟩ := exists_spForm_eq_pair ha hne' 0 1
  obtain ⟨u₂, hu₂a, hu₂a'⟩ := exists_spForm_eq_pair ha hne' 1 0
  have hz : spTransvection a c * spTransvection a' c' ∈ A := A.mul_mem hx hy
  have hmul : ∀ (x y : StatedSp l F) (v : Fin l ⊕ Fin l → F),
      spEnd (x * y) v = spEnd x (spEnd y v) := by
    intro x y v
    rw [spEnd_mul, Module.End.mul_apply]
  have hz2 : spEnd (spTransvection a c * spTransvection a' c') u₂ = u₂ + c • a := by
    rw [hmul, spEnd_spTransvection a' c' u₂, hu₂a', spEnd_spTransvection a c _]
    simp [map_add, map_smul, hu₂a]
  have hz1 : spEnd (spTransvection a c * spTransvection a' c') u₁ =
      u₁ + (c' • a' + (c * (c' * spForm l F a' a)) • a) := by
    rw [hmul, spEnd_spTransvection a' c' u₁, hu₁a', spEnd_spTransvection a c _]
    simp [map_add, map_smul, hu₁a, add_assoc]
  have hne1 : spTransvection a c * spTransvection a' c' ≠ 1 := by
    intro h
    rw [h, spEnd_one, Module.End.one_apply] at hz2
    have h3 : c • a = 0 := by simpa using hz2
    rcases smul_eq_zero.mp h3 with h | h
    · exact hc h
    · exact ha h
  obtain ⟨a'', c'', ha'', hc'', hzeq⟩ := borel86_spn_eq_spTransvection (hAt _ hz hne1)
  rw [hzeq, spEnd_spTransvection] at hz1 hz2
  have e2 : (c'' * spForm l F u₂ a'') • a'' = c • a := add_left_cancel hz2
  have e1 : (c'' * spForm l F u₁ a'') • a'' = c' • a' + (c * (c' * spForm l F a' a)) • a :=
    add_left_cancel hz1
  have hk2 : c'' * spForm l F u₂ a'' ≠ 0 := by
    intro h
    rw [h, zero_smul] at e2
    exact smul_ne_zero hc ha e2.symm
  generalize c'' * spForm l F u₁ a'' = K₁ at e1
  generalize c'' * spForm l F u₂ a'' = K₂ at e2 hk2
  have hA'' : a'' = K₂⁻¹ • (c • a) := by rw [← e2, inv_smul_smul₀ hk2]
  have h3 : c' • a' = (K₁ * (K₂⁻¹ * c) - c * (c' * spForm l F a' a)) • a := by
    rw [sub_smul, mul_smul K₁ (K₂⁻¹ * c) a, mul_smul K₂⁻¹ c a, ← hA'', e1, add_sub_cancel_right]
  apply hne' (c'⁻¹ * (K₁ * (K₂⁻¹ * c) - c * (c' * spForm l F a' a)))
  rw [← smul_smul, ← h3, inv_smul_smul₀ hc']

theorem kFacts_sp_rootGroup {l n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (A : Subgroup ↥(StatedSp l F))
    (hA : Nat.card A = 2 ^ n)
    (hAt : ∀ x ∈ A, x ≠ 1 → IsSymplecticTransvectionIn l x) :
    ∃ a : Fin l ⊕ Fin l → F, a ≠ 0 ∧
      ∀ x : ↥(StatedSp l F), x ∈ A ↔ ∃ s : F, x = spTransvection a s := by
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra hcon
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr fun x hx => by
      by_contra h
      exact hcon ⟨x, hx, h⟩
    rw [hbot, Subgroup.card_bot] at hA
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨a, c, ha, hc, rfl⟩ := borel86_spn_eq_spTransvection (hAt x₀ hx₀ hx₀1)
  refine ⟨a, ha, ?_⟩
  have hsub : ∀ x ∈ A, ∃ s : F, x = spTransvection a s := by
    intro x hx
    by_cases hx1 : x = 1
    · exact ⟨0, by rw [hx1, borel86_spn_spTransvection_param_zero]⟩
    · obtain ⟨a', c', ha', hc', rfl⟩ := borel86_spn_eq_spTransvection (hAt x hx hx1)
      obtain ⟨μ, rfl⟩ := exists_smul_of_mem_of_isTransvection A hAt ha hc hc' hx₀ hx
      exact ⟨μ * μ * c', CFSG.RankThree.PartOne.CTP.spTransvection_smul μ a c'⟩
  intro x
  refine ⟨hsub x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, spForm l F y a ≠ 0 := by
    by_contra hcon
    apply ha
    apply (spForm_nondegenerate (r := l) (K := F)).2 a
    intro y
    by_contra hy
    exact hcon ⟨y, hy⟩
  have hinj : Function.Injective (fun s : F => spTransvection a s) := by
    intro s s' h
    have h1 := congrArg (fun g => spEnd g y) h
    simp only [spEnd_spTransvection] at h1
    have h2 := smul_left_injective F ha (add_left_cancel h1)
    exact mul_right_cancel₀ hy h2
  have hsubset : (A : Set ↥(StatedSp l F)) ⊆ Set.range (fun s : F => spTransvection a s) := by
    intro z hz
    obtain ⟨s, hs⟩ := hsub z hz
    exact ⟨s, hs.symm⟩
  have hcard : (Set.range (fun s : F => spTransvection a s)).ncard ≤
      (A : Set ↥(StatedSp l F)).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
    change Nat.card F ≤ Nat.card A
    rw [hA, hF]
  have heq := Set.eq_of_subset_of_ncard_le hsubset hcard (Set.finite_range _)
  obtain ⟨s, hs⟩ := hx
  have : x ∈ Set.range (fun s : F => spTransvection a s) := ⟨s, hs.symm⟩
  rw [← heq] at this
  exact this

theorem kFacts_spTransvection_comm_of_spForm_eq_zero {l : ℕ} {F : Type} [Field F]
    {a c : Fin l ⊕ Fin l → F} (h : spForm l F c a = 0) (s t : F) :
    spTransvection c s * spTransvection a t = spTransvection a t * spTransvection c s := by
  have hu : spEnd (spTransvection a t) c = c := by
    rw [spEnd_spTransvection, h]
    simp
  exact commute_spTransvection hu s

theorem kFacts_sp_hyperbolic_pair {l n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (A B : Subgroup ↥(StatedSp l F))
    (hA : Nat.card A = 2 ^ n) (hB : Nat.card B = 2 ^ n)
    (hAt : ∀ x ∈ A, x ≠ 1 → IsSymplecticTransvectionIn l x)
    (hBt : ∀ x ∈ B, x ≠ 1 → IsSymplecticTransvectionIn l x)
    (hnc : ¬ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a)) :
    ∃ a b : Fin l ⊕ Fin l → F, spForm l F a b = 1 ∧
      (∀ x : ↥(StatedSp l F), x ∈ A ↔ ∃ s : F, x = spTransvection a s) ∧
      (∀ x : ↥(StatedSp l F), x ∈ B ↔ ∃ s : F, x = spTransvection b s) := by
  obtain ⟨a, ha, hAa⟩ := kFacts_sp_rootGroup hF hn A hA hAt
  obtain ⟨b, hb, hBb⟩ := kFacts_sp_rootGroup hF hn B hB hBt
  have hab : spForm l F a b ≠ 0 := by
    intro h0
    apply hnc
    intro x hx y hy
    obtain ⟨s, rfl⟩ := (hAa x).mp hx
    obtain ⟨t, rfl⟩ := (hBb y).mp hy
    exact kFacts_spTransvection_comm_of_spForm_eq_zero h0 s t
  have hμ : (spForm l F a b)⁻¹ ≠ 0 := inv_ne_zero hab
  have hμμ : (spForm l F a b)⁻¹ * (spForm l F a b)⁻¹ ≠ 0 := mul_ne_zero hμ hμ
  refine ⟨a, (spForm l F a b)⁻¹ • b, ?_, hAa, ?_⟩
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hab]
  · intro x
    rw [hBb x]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨((spForm l F a b)⁻¹ * (spForm l F a b)⁻¹)⁻¹ * s, ?_⟩
      rw [CFSG.RankThree.PartOne.CTP.spTransvection_smul, mul_inv_cancel_left₀ hμμ]
    · rintro ⟨s, rfl⟩
      exact ⟨_, CFSG.RankThree.PartOne.CTP.spTransvection_smul _ b s⟩

end CFSG.LocalAnalysis.WeakClosure81
