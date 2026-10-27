module

public import CFSG.Quasithin.Recognition.SzR1Gram
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SzR1

theorem centralizes_of_perfect {G : Type*} [Group G] {K Zs : Subgroup G} {y : G}
    (hK : ⁅K, K⁆ = K) (hKZ : ∀ k ∈ K, ∀ s ∈ Zs, k * s = s * k)
    (hZZ : ∀ s ∈ Zs, ∀ t ∈ Zs, s * t = t * s)
    (hy : ∀ k ∈ K, ∃ s ∈ Zs, k * y * k⁻¹ = s * y) :
    ∀ k ∈ K, k * y = y * k := by
  obtain ⟨φ, hφdef⟩ : ∃ φ : G → G, ∀ k, φ k = k * y * k⁻¹ * y⁻¹ := ⟨_, fun _ => rfl⟩
  have hφ : ∀ k ∈ K, φ k ∈ Zs := by
    intro k hk
    obtain ⟨s, hs, hks⟩ := hy k hk
    have : φ k = s := by
      rw [hφdef, hks]
      group
    exact this ▸ hs
  have hφy : ∀ k, φ k * y = k * y * k⁻¹ := by
    intro k
    rw [hφdef]
    group
  have hmul : ∀ k ∈ K, ∀ k' ∈ K, φ (k * k') = φ k' * φ k := by
    intro k hk k' hk'
    have h1 : k * k' * y * (k * k')⁻¹ = φ k' * (φ k * y) := by
      calc k * k' * y * (k * k')⁻¹ = k * (k' * y * k'⁻¹) * k⁻¹ := by group
        _ = k * (φ k' * y) * k⁻¹ := by rw [← hφy k']
        _ = (k * φ k') * y * k⁻¹ := by group
        _ = (φ k' * k) * y * k⁻¹ := by rw [hKZ k hk _ (hφ k' hk')]
        _ = φ k' * (k * y * k⁻¹) := by group
        _ = φ k' * (φ k * y) := by rw [← hφy k]
    rw [hφdef (k * k'), h1]
    group
  have hone : φ 1 = 1 := by
    rw [hφdef]
    group
  have hinv : ∀ k ∈ K, φ k⁻¹ = (φ k)⁻¹ := by
    intro k hk
    have h1 := hmul k hk k⁻¹ (K.inv_mem hk)
    rw [mul_inv_cancel, hone] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, φ (a * b * a⁻¹ * b⁻¹) = 1 := by
    intro a ha b hb
    have hab : a * b ∈ K := K.mul_mem ha hb
    have habi : a * b * a⁻¹ ∈ K := K.mul_mem hab (K.inv_mem ha)
    rw [hmul _ habi _ (K.inv_mem hb), hmul _ hab _ (K.inv_mem ha), hmul _ ha _ hb,
      hinv b hb, hinv a ha, hZZ _ (hφ b hb) _ (hφ a ha)]
    group
  have hle : ⁅K, K⁆ ≤ K ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    show a * b * a⁻¹ * b⁻¹ ∈ K ⊓ Subgroup.centralizer ({y} : Set G)
    refine ⟨K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb), ?_⟩
    have h1 := hcomm a ha b hb
    rw [hφdef] at h1
    have hc : (a * b * a⁻¹ * b⁻¹) * y = y * (a * b * a⁻¹ * b⁻¹) := by
      calc (a * b * a⁻¹ * b⁻¹) * y
          = ((a * b * a⁻¹ * b⁻¹) * y * (a * b * a⁻¹ * b⁻¹)⁻¹ * y⁻¹) *
              (y * (a * b * a⁻¹ * b⁻¹)) := by group
        _ = y * (a * b * a⁻¹ * b⁻¹) := by rw [h1, one_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc
  intro k hk
  have hk0 : k ∈ ⁅K, K⁆ := by
    rw [hK]
    exact hk
  have hk' : k ∈ K ⊓ Subgroup.centralizer ({y} : Set G) := hle hk0
  exact Subgroup.mem_centralizer_singleton_iff.mp hk'.2

end SzR1

end CFSG.Quasithin
