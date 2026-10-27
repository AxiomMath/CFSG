module

public import CFSG.RankThree.PartOne.SEITZ5.USpace

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2 u2_zero)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

section Cocycle

variable {P : Frame σ n} {H : Subgroup (SUid σ n)}

theorem lam_sub_eq {hL : lSub P H = ⊤} {lam : K →ₗ[fixSub σ] fixSub σ}
    (hS : sSub P H hL ≤ LinearMap.ker lam) {g g' : SUid σ n} (hg : g ∈ affGroup P H)
    (hg' : g' ∈ affGroup P H) {m : SpecialLinearGroup (Fin 2) (fixSub σ)} {τ₁ τ₂ τ₁' τ₂' : K}
    (h : Aff P g m τ₁ τ₂) (h' : Aff P g' m τ₁' τ₂') :
    lam τ₁ = lam τ₁' ∧ lam τ₂ = lam τ₂' := by
  have hx := sub_mem_xTrans hg hg' h h'
  have h1 : τ₁ - τ₁' ∈ LinearMap.ker lam := hS (fst_mem_sSub hL hx)
  have h2 : τ₂ - τ₂' ∈ LinearMap.ker lam := hS (snd_mem_sSub hL hx)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem lam_smul' (lam : K →ₗ[fixSub σ] fixSub σ) (s : fixSub σ) (a : K) :
    lam ((s : K) * a) = s * lam a := by
  have : (s : K) * a = s • a := rfl
  rw [this, map_smul, smul_eq_mul]

theorem lam_torus {hL : lSub P H = ⊤} {lam : K →ₗ[fixSub σ] fixSub σ}
    (hS : sSub P H hL ≤ LinearMap.ker lam) (hF : ∃ s₀ : fixSub σ, s₀ ≠ 0 ∧ s₀ ≠ 1) :
    ∃ κ : fixSub σ, ∀ (s : fixSub σ) (hs : s ≠ 0) (g : SUid σ n), g ∈ affGroup P H →
      ∀ a₁ a₂ : K, Aff P g (dg s hs) a₁ a₂ → lam a₁ = κ * (s - 1) := by
  classical
  have hlift : ∀ s : fixSub σ, ∃ g : SUid σ n, ∃ a₁ a₂ : K, ∀ hs : s ≠ 0,
      g ∈ affGroup P H ∧ Aff P g (dg s hs) a₁ a₂ := by
    intro s
    by_cases hs : s = 0
    · exact ⟨1, 0, 0, fun h => absurd hs h⟩
    · have hm : dg s hs ∈ lSub P H := hL ▸ Subgroup.mem_top _
      obtain ⟨g, hg, a₁, a₂, hA⟩ := hm
      exact ⟨g, a₁, a₂, fun _ => ⟨hg, hA⟩⟩
  choose g a₁ a₂ hga using hlift
  have hcoc : ∀ (s s' : fixSub σ) (hs : s ≠ 0) (hs' : s' ≠ 0),
      s' * lam (a₁ s) + lam (a₁ s') = lam (a₁ (s * s')) := by
    intro s s' hs hs'
    have hx := cocycle_mem hs hs' (hga s hs).1 (hga s' hs').1
      (hga (s * s') (mul_ne_zero hs hs')).1 (hga s hs).2 (hga s' hs').2
      (hga (s * s') (mul_ne_zero hs hs')).2
    have h1 : (s' : K) * a₁ s + a₁ s' - a₁ (s * s') ∈ LinearMap.ker lam := hS (fst_mem_sSub hL hx)
    rw [LinearMap.mem_ker, map_sub, map_add, lam_smul', sub_eq_zero] at h1
    exact h1
  obtain ⟨s₀, hs₀, hs₀1⟩ := hF
  have hs₀1' : s₀ - 1 ≠ 0 := sub_ne_zero.2 hs₀1
  refine ⟨lam (a₁ s₀) / (s₀ - 1), ?_⟩
  have hcho : ∀ (s : fixSub σ) (hs : s ≠ 0), lam (a₁ s) = lam (a₁ s₀) / (s₀ - 1) * (s - 1) := by
    intro s hs
    have h1 := hcoc s s₀ hs hs₀
    have h2 := hcoc s₀ s hs₀ hs
    rw [mul_comm s₀ s] at h2
    field_simp
    linear_combination h1 - h2
  intro s hs g' hg' b₁ b₂ hA'
  have := (lam_sub_eq hS hg' (hga s hs).1 hA' (hga s hs).2).1
  rw [this]
  exact hcho s hs

theorem lam_generator {hL : lSub P H = ⊤} {lam : K →ₗ[fixSub σ] fixSub σ}
    (hS : sSub P H hL ≤ LinearMap.ker lam)
    (hE : ∃ t ∈ affGroup P H, Aff P t (u2 (1 : fixSub σ)) 0 0) {κ : fixSub σ}
    (hκ : ∀ (s : fixSub σ) (hs : s ≠ 0) (g : SUid σ n), g ∈ affGroup P H →
      ∀ a₁ a₂ : K, Aff P g (dg s hs) a₁ a₂ → lam a₁ = κ * (s - 1))
    {c s : fixSub σ} (hss : s * s = c) {θ₂ : K} {t : SUid σ n} (ht : t ∈ affGroup P H)
    (hA : Aff P t (u2 c) 0 θ₂) : lam θ₂ = κ * (s * s - s) := by
  by_cases hs : s = 0
  · have hc : c = 0 := by rw [← hss, hs, mul_zero]
    rw [hc, u2_zero] at hA
    have := (lam_sub_eq hS ht (affGroup P H).one_mem hA (Aff.one P)).2
    rw [this, map_zero, hs]
    ring
  · have hm : dg s hs ∈ lSub P H := hL ▸ Subgroup.mem_top _
    obtain ⟨g, hg, a₁, a₂, hgA⟩ := hm
    obtain ⟨te, hte, hteA⟩ := hE
    have hc := hgA.conj_dg hs hteA
    have hmem : g * te * g⁻¹ ∈ affGroup P H :=
      (affGroup P H).mul_mem ((affGroup P H).mul_mem hg hte) ((affGroup P H).inv_mem hg)
    rw [mul_one, hss] at hc
    have h1 := (lam_sub_eq hS ht hmem hA hc).2
    rw [h1]
    have : ((s : K) * ((1 : fixSub σ) : K) * a₁) = (s : K) * a₁ := by simp
    rw [this, lam_smul', hκ s hs g hg a₁ a₂ hgA]
    ring

end Cocycle

end CFSG.RankThree.PartOne.SEITZ5
