module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsC
public import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.CTP CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Quasithin (conjSubgroup)

private theorem exists_ne_zero_spForm_eq_zero_pair {l : ℕ} {F : Type} [Field F] (hl : 2 ≤ l)
    (a b : Fin l ⊕ Fin l → F) :
    ∃ c : Fin l ⊕ Fin l → F, c ≠ 0 ∧ spForm l F c a = 0 ∧ spForm l F c b = 0 := by
  let L : (Fin l ⊕ Fin l → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := fun c => ![spForm l F c a, spForm l F c b]
      map_add' := fun c d => by
        ext i; fin_cases i <;> simp
      map_smul' := fun r c => by
        ext i; fin_cases i <;> simp }
  have hlt : Module.finrank F (Fin 2 → F) < Module.finrank F (Fin l ⊕ Fin l → F) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_sum]
    omega
  have hker : LinearMap.ker L ≠ ⊥ := L.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have h := LinearMap.mem_ker.mp hc
  refine ⟨c, hc0, ?_, ?_⟩
  · simpa [L] using congrFun h 0
  · simpa [L] using congrFun h 1

private theorem spEnd_tau_apply {l : ℕ} {F : Type} [Field F] [CharP F 2]
    {a b : Fin l ⊕ Fin l → F} (hab : spForm l F a b = 1) {ν : F} (hν : ν ≠ 0) :
    spEnd ((spTransvection a ν * spTransvection b ν⁻¹ * spTransvection a ν) *
      (spTransvection a 1 * spTransvection b 1 * spTransvection a 1)⁻¹) a = ν • a := by
  have haa : spForm l F a a = 0 := (spForm_isAlt (r := l) (K := F)).self_eq_zero a
  have hbb : spForm l F b b = 0 := (spForm_isAlt (r := l) (K := F)).self_eq_zero b
  have hba : spForm l F b a = 1 := by
    have h := (spForm_isAlt (r := l) (K := F)).neg_eq a b
    rw [hab] at h
    rw [← h, CharTwo.neg_eq]
  have hmul : ∀ (x y : StatedSp l F) (v : Fin l ⊕ Fin l → F),
      spEnd (x * y) v = spEnd x (spEnd y v) := by
    intro x y v
    rw [spEnd_mul, Module.End.mul_apply]
  have h2a : a + a = 0 := by rw [← two_smul F a, CharTwo.two_eq_zero, zero_smul]
  have h2b : b + b = 0 := by rw [← two_smul F b, CharTwo.two_eq_zero, zero_smul]
  have hneg : (-1 : F) = 1 := CharTwo.neg_eq 1
  rw [mul_inv_rev, mul_inv_rev, spTransvection_inv, spTransvection_inv, hneg]
  have h1 : spEnd (spTransvection a 1 * (spTransvection b 1 * spTransvection a 1)) a = b := by
    simp only [hmul, spEnd_spTransvection]
    simp [haa, hab, hba, map_add, LinearMap.add_apply]
    rw [add_comm a b, add_assoc, h2a, add_zero]
  have h11 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, CharTwo.two_eq_zero]
  rw [hmul, h1]
  simp only [hmul, spEnd_spTransvection]
  simp [haa, hbb, hab, hba, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hν,
    h11]
  rw [add_comm b (ν • a), add_assoc, h2b, add_zero]

private theorem mem_conjSubgroup_iff_exists_spTransvection {l : ℕ} {F : Type} [Field F]
    {A : Subgroup ↥(StatedSp l F)} {a c : Fin l ⊕ Fin l → F} (γ : ↥(StatedSp l F))
    (hγ : spEnd γ c = a)
    (hA : ∀ x : ↥(StatedSp l F), x ∈ A ↔ ∃ s : F, x = spTransvection a s)
    (x : ↥(StatedSp l F)) :
    x ∈ conjSubgroup A γ ↔ ∃ s : F, x = spTransvection c s := by
  rw [CFSG.Quasithin.mem_conjSubgroup_iff, hA]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have h := CFSG.RankThree.PartOne.CTP.spTransvection_conj γ c s
    rw [hγ] at h
    have : γ * x * γ⁻¹ = γ * spTransvection c s * γ⁻¹ := by rw [hs, h]
    exact mul_left_cancel (mul_right_cancel this)
  · rintro ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    rw [CFSG.RankThree.PartOne.CTP.spTransvection_conj, hγ]

theorem kFacts_sp_config :
    ∀ (l n : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ l → 2 ≤ n → Nat.card F = 2 ^ n →
      ∀ A B : Subgroup ↥(StatedSp l F), Nat.card A = 2 ^ n → Nat.card B = 2 ^ n →
        (∀ x ∈ A, x ≠ 1 → SevenK.IsSymplecticTransvectionIn l x) →
        (∀ x ∈ B, x ≠ 1 → SevenK.IsSymplecticTransvectionIn l x) →
        ¬ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
          ∃ γ τ, τ ∈ A ⊔ B ∧ conjSubgroup A γ ≠ A ∧
            (∀ x ∈ conjSubgroup A γ, ∀ y ∈ A ⊔ B, x * y = y * x) ∧
            τ ∈ Subgroup.normalizer (A : Set _) ∧ (∀ a ∈ A, τ * a = a * τ → a = 1) := by
  intro l n F _ _ hl hn hF A B hA hB hAt hBt hnc
  haveI : CharP F 2 := charP_two_of_card_eq_two_pow hF
  obtain ⟨a, b, hab, hAa, hBb⟩ := kFacts_sp_hyperbolic_pair hF hn A B hA hB hAt hBt hnc
  have haa : spForm l F a a = 0 := (spForm_isAlt (r := l) (K := F)).self_eq_zero a
  have hba : spForm l F b a = 1 := by
    have h := (spForm_isAlt (r := l) (K := F)).neg_eq a b
    rw [hab] at h
    rw [← h, CharTwo.neg_eq]
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hab
  obtain ⟨c, hc0, hca, hcb⟩ := exists_ne_zero_spForm_eq_zero_pair hl a b
  obtain ⟨γ, hγ⟩ := exists_spEnd_eq hc0 ha0
  have hconj := mem_conjSubgroup_iff_exists_spTransvection γ hγ hAa
  obtain ⟨ν, hν0, hν1, -⟩ := exists_zech_of_card_two_pow hF (by omega)
  have hAmem : ∀ s : F, spTransvection a s ∈ A := fun s => (hAa _).mpr ⟨s, rfl⟩
  have hBmem : ∀ s : F, spTransvection b s ∈ B := fun s => (hBb _).mpr ⟨s, rfl⟩
  have hA' : ∀ s : F, spTransvection a s ∈ A ⊔ B := fun s => Subgroup.mem_sup_left (hAmem s)
  have hB' : ∀ s : F, spTransvection b s ∈ A ⊔ B := fun s => Subgroup.mem_sup_right (hBmem s)
  have hτ := spEnd_tau_apply hab hν0
  set τ : ↥(StatedSp l F) :=
    (spTransvection a ν * spTransvection b ν⁻¹ * spTransvection a ν) *
      (spTransvection a 1 * spTransvection b 1 * spTransvection a 1)⁻¹ with hτdef
  have hτmem : τ ∈ A ⊔ B :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hA' ν) (hB' ν⁻¹)) (hA' ν))
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hA' 1) (hB' 1)) (hA' 1)))
  have hτconj : ∀ s : F, τ * spTransvection a s * τ⁻¹ = spTransvection a (ν * ν * s) := by
    intro s
    rw [CFSG.RankThree.PartOne.CTP.spTransvection_conj, hτ,
      CFSG.RankThree.PartOne.CTP.spTransvection_smul]
  have hbc : spForm l F b c = 0 := by
    have h := (spForm_isAlt (r := l) (K := F)).neg_eq c b
    rw [hcb] at h
    rw [← h, neg_zero]
  refine ⟨γ, τ, hτmem, ?_, ?_, ?_, ?_⟩
  · intro hAeq
    have h1 : spTransvection c 1 ∈ conjSubgroup A γ := (hconj _).mpr ⟨1, rfl⟩
    rw [hAeq] at h1
    obtain ⟨s, hs⟩ := (hAa _).mp h1
    have h2 := congrArg (fun g => spEnd g b) hs
    simp only [spEnd_spTransvection, hbc, hba] at h2
    have hs0 : s = 0 := by
      have h3 : (s * 1) • a = 0 := by simpa using h2.symm
      rcases smul_eq_zero.mp h3 with h | h
      · simpa using h
      · exact absurd h ha0
    have h3 : spTransvection c 1 = 1 := by
      rw [hs, hs0, borel86_spn_spTransvection_param_zero]
    obtain ⟨y, hy⟩ : ∃ y, spForm l F y c ≠ 0 := by
      by_contra hcon
      apply hc0
      apply (spForm_nondegenerate (r := l) (K := F)).2 c
      intro y
      by_contra hy
      exact hcon ⟨y, hy⟩
    have h4 := congrArg (fun g => spEnd g y) h3
    simp only [spEnd_spTransvection, spEnd_one, Module.End.one_apply] at h4
    have h5 : (1 * spForm l F y c) • c = 0 := by simpa using h4
    rcases smul_eq_zero.mp h5 with h | h
    · exact hy (by simpa using h)
    · exact hc0 h
  · intro x hx y hy
    obtain ⟨s, rfl⟩ := (hconj x).mp hx
    have hle : A ⊔ B ≤ Subgroup.centralizer {spTransvection c s} := by
      refine sup_le ?_ ?_
      · intro z hz
        obtain ⟨t, rfl⟩ := (hAa z).mp hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (kFacts_spTransvection_comm_of_spForm_eq_zero hca s t).symm
      · intro z hz
        obtain ⟨t, rfl⟩ := (hBb z).mp hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (kFacts_spTransvection_comm_of_spForm_eq_zero hcb s t).symm
    have h := hle hy
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h.symm
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨s, rfl⟩ := (hAa z).mp hz
      rw [hτconj]
      exact hAmem _
    · intro hz
      obtain ⟨t, ht⟩ := (hAa _).mp hz
      have hν2 : ν * ν ≠ 0 := mul_ne_zero hν0 hν0
      have h5 : τ * z * τ⁻¹ = τ * spTransvection a ((ν * ν)⁻¹ * t) * τ⁻¹ := by
        rw [ht, hτconj, mul_inv_cancel_left₀ hν2]
      have h6 : z = spTransvection a ((ν * ν)⁻¹ * t) := mul_left_cancel (mul_right_cancel h5)
      rw [h6]
      exact hAmem _
  · intro z hz hcomm
    obtain ⟨s, rfl⟩ := (hAa z).mp hz
    have h7 : τ * spTransvection a s * τ⁻¹ = spTransvection a s := by
      rw [hcomm, mul_inv_cancel_right]
    rw [hτconj] at h7
    have h8 := congrArg (fun g => spEnd g b) h7
    simp only [spEnd_spTransvection, hba, mul_one] at h8
    have hνν : ν * ν ≠ 1 := by
      intro h
      rcases mul_self_eq_one_iff.mp h with h | h
      · exact hν1 h
      · exact hν1 (by rw [h, CharTwo.neg_eq])
    have h9 : (ν * ν * s - s) • a = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_left_cancel h8
    rcases smul_eq_zero.mp h9 with h | h
    · have h10 : (ν * ν - 1) * s = 0 := by rw [← h]; ring
      rcases mul_eq_zero.mp h10 with h | h
      · exact absurd (sub_eq_zero.mp h) hνν
      · rw [h, borel86_spn_spTransvection_param_zero]
    · exact absurd h ha0

end CFSG.LocalAnalysis.WeakClosure81
