module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusHDefs
public import CFSG.LocalAnalysis.StandardType.GGL45E67RankLift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

private lemma ggL45SatK_mem_center_of_map_eq_one {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {x : K}
    (hx : θ (x : K ⧸ Subgroup.center K) = 1) : x ∈ Subgroup.center K := by
  rw [← QuotientGroup.eq_one_iff x]
  exact θ.injective (by simpa using hx)

private lemma ggL45SatK_exists_central_mul {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {α : MulAut K} {a : R} {x : K}
    (hx : θ (x : K ⧸ Subgroup.center K) = a) (ha : ggInducedAut θ α a = a) :
    ∃ z ∈ Subgroup.center K, α x = z * x := by
  refine ⟨α x * x⁻¹, ?_, by group⟩
  apply ggL45SatK_mem_center_of_map_eq_one θ
  have h1 : θ ((α x * x⁻¹ : K) : K ⧸ Subgroup.center K) =
      ggInducedAut θ α (θ (x : K ⧸ Subgroup.center K)) *
        (θ (x : K ⧸ Subgroup.center K))⁻¹ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv,
      ← ggInducedAut_apply θ α x]
  rw [h1, hx, ha]
  group

private lemma ggL45SatK_map_commutator_eq {K : Type} [Group K] {α : MulAut K} {x y z w : K}
    (hz : z ∈ Subgroup.center K) (hw : w ∈ Subgroup.center K)
    (hx : α x = z * x) (hy : α y = w * y) : α ⁅x, y⁆ = ⁅x, y⁆ := by
  have hx' : α x = x * z := by rw [hx, (Subgroup.mem_center_iff.mp hz x).symm]
  have hy' : α y = y * w := by rw [hy, (Subgroup.mem_center_iff.mp hw y).symm]
  have hmap : α ⁅x, y⁆ = ⁅α x, α y⁆ := by
    simp only [commutatorElement_def, map_mul, map_inv]
  rw [hmap, hx', hy']
  rw [CFSG.RankThree.Classical2.commutatorElement_mul_central_left hz,
    CFSG.RankThree.Classical2.commutatorElement_mul_central_right hw]

private lemma ggL45SatK_ggInducedAut_conj {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (k : K) :
    ggInducedAut θ (MulAut.conj k) = MulAut.conj (θ (k : K ⧸ Subgroup.center K)) := by
  ext r
  obtain ⟨y, rfl⟩ := θ.surjective r
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  simp only [ggInducedAut_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, map_mul, map_inv]

private lemma ggL45SatK_mul_eq_one_of_conj {G : Type} [Group G] {a b : G}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hu3 : (a * b) ^ 3 = 1)
    (h : (a * b) ^ 2 * a * ((a * b) ^ 2)⁻¹ = a) : a * b = 1 := by
  have hsqa : a * a = 1 := by rwa [pow_two] at ha
  have hsqb : b * b = 1 := by rwa [pow_two] at hb
  have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_left hsqa
  have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_left hsqb
  have hu_inv : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, haa, hbb]
  have hau : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hu_inv, haa]
    calc a * (a * b) * a = (a * a) * (b * a) := by group
      _ = b * a := by rw [hsqa]; group
  have hu2 : (a * b) ^ 2 = (a * b)⁻¹ := by
    have h1 : (a * b) ^ 3 = (a * b) ^ 2 * (a * b) := by rw [pow_succ]
    rw [h1] at hu3
    exact eq_inv_of_mul_eq_one_left hu3
  have hcomm : (a * b) ^ 2 * a = a * (a * b) ^ 2 := by
    calc (a * b) ^ 2 * a = ((a * b) ^ 2 * a * ((a * b) ^ 2)⁻¹) * (a * b) ^ 2 := by group
      _ = a * (a * b) ^ 2 := by rw [h]
  have hconv : (a * b)⁻¹ * a = a * (a * b)⁻¹ := by rw [← hu2]; exact hcomm
  have hua : (a * b) * a = a * (a * b) := by
    have h1 : a = (a * b) * a * (a * b)⁻¹ := by
      calc a = (a * b) * ((a * b)⁻¹ * a) := by group
        _ = (a * b) * (a * (a * b)⁻¹) := by rw [hconv]
        _ = (a * b) * a * (a * b)⁻¹ := by group
    calc (a * b) * a = ((a * b) * a * (a * b)⁻¹) * (a * b) := by group
      _ = a * (a * b) := by rw [← h1]
  have hinv_eq : (a * b)⁻¹ = a * b := by
    rw [← hau, ← hua, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : (a * b) ^ 2 = a * b := by rw [hu2, hinv_eq]
  rw [pow_two] at h2
  exact mul_left_cancel (a := a * b) (by simpa using h2)

private lemma ggL45SatK_conj_sq_eq {K R : Type} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {k ahat bhat : K} {a b : R}
    (hk : k = ⁅ahat, bhat⁆) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (ha' : θ (ahat : K ⧸ Subgroup.center K) = a)
    (hb' : θ (bhat : K ⧸ Subgroup.center K) = b)
    (hconj : ggInducedAut θ (MulAut.conj k) a = a) :
    (a * b) ^ 2 * a * ((a * b) ^ 2)⁻¹ = a := by
  have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rwa [pow_two] at ha)
  have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by rwa [pow_two] at hb)
  have ht : θ (k : K ⧸ Subgroup.center K) = (a * b) ^ 2 := by
    have hkq : (k : K ⧸ Subgroup.center K) =
        ((ahat * bhat * ahat⁻¹ * bhat⁻¹ : K) : K ⧸ Subgroup.center K) := by
      rw [hk, commutatorElement_def]
    rw [hkq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv, map_inv,
      ha', hb', haa, hbb, pow_two]
    group
  have hconj' : MulAut.conj (θ (k : K ⧸ Subgroup.center K)) a = a := by
    rw [← ggL45SatK_ggInducedAut_conj θ k]
    exact hconj
  have h1 : MulAut.conj ((a * b) ^ 2) a = a := by
    rw [← ht]
    exact hconj'
  rw [MulAut.conj_apply] at h1
  exact h1

theorem ggL45_false_of_satK_of_fixed_involutions {K : Type} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {ψ : MulAut K} {E : Subgroup (MulAut K)}
    (hsat : ∀ k : K, k ^ 3 = 1 → (∀ e ∈ E, e k = k) → ψ k = k → MulAut.conj k ∈ E)
    {a b : R} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : orderOf (a * b) = 3)
    (hψa : ggInducedAut θ ψ a = a) (hψb : ggInducedAut θ ψ b = b)
    (hEa : ∀ e ∈ E, ggInducedAut θ e a = a) (hEb : ∀ e ∈ E, ggInducedAut θ e b = b) : False := by
  obtain ⟨a', ha'⟩ := θ.surjective a
  obtain ⟨ahat, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b', hb'⟩ := θ.surjective b
  obtain ⟨bhat, rfl⟩ := QuotientGroup.mk_surjective b'
  have hsq_a : ahat ^ 2 ∈ Subgroup.center K := by
    apply ggL45SatK_mem_center_of_map_eq_one θ
    rwa [QuotientGroup.mk_pow, map_pow, ha']
  have hsq_b : bhat ^ 2 ∈ Subgroup.center K := by
    apply ggL45SatK_mem_center_of_map_eq_one θ
    rwa [QuotientGroup.mk_pow, map_pow, hb']
  have hcube : (ahat * bhat) ^ 3 ∈ Subgroup.center K := by
    apply ggL45SatK_mem_center_of_map_eq_one θ
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, map_pow, map_mul, ha', hb']
    simpa [hab] using pow_orderOf_eq_one (a * b)
  set k : K := ⁅ahat, bhat⁆ with hk
  have hk3 : k ^ 3 = 1 := CentralLift.commutator_pow_three_eq_one_of_central hsq_a hsq_b hcube
  have hfix : ∀ {α : MulAut K}, ggInducedAut θ α a = a → ggInducedAut θ α b = b → α k = k := by
    intro α hαa hαb
    obtain ⟨z₁, hz₁, h₁⟩ := ggL45SatK_exists_central_mul θ ha' hαa
    obtain ⟨z₂, hz₂, h₂⟩ := ggL45SatK_exists_central_mul θ hb' hαb
    exact ggL45SatK_map_commutator_eq hz₁ hz₂ h₁ h₂
  have hEfix : ∀ e ∈ E, e k = k := fun e he => hfix (hEa e he) (hEb e he)
  have hψfix : ψ k = k := hfix hψa hψb
  have hmem : MulAut.conj k ∈ E := hsat k hk3 hEfix hψfix
  have hconj : ggInducedAut θ (MulAut.conj k) a = a := hEa _ hmem
  have hu3 : (a * b) ^ 3 = 1 := by simpa [hab] using pow_orderOf_eq_one (a * b)
  have hu1 : a * b = 1 := ggL45SatK_mul_eq_one_of_conj ha hb hu3
    (ggL45SatK_conj_sq_eq θ hk ha hb ha' hb' hconj)
  rw [hu1, orderOf_one] at hab
  omega

end CFSG.StandardType
