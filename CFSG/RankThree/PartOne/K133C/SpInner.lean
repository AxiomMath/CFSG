module

public import CFSG.RankThree.PartOne.K133C.SpForm

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_moving_isoGrp {p : ℕ} (hpK : (p : K) ≠ 0) (J : Matrix ι ι K) (hJ : Jᵀ = J)
    (hJa : ∀ y : ι → K, y ⬝ᵥ (J *ᵥ y) = 0) (hJnd : ∀ w : ι → K, J *ᵥ w = 0 → w = 0)
    {v : ι → K} (hv : v ≠ 0) (P : Subgroup (GL ι K)) (hPJ : P ≤ isoGrp J)
    (hpow : ∀ h ∈ P, h ^ p = 1) (hfix : ∀ h ∈ P, (h : Matrix ι ι K) *ᵥ v = v)
    (hP1 : ∃ h ∈ P, h ≠ 1) :
    ∃ S : Subgroup (GL ι K), S ≤ isoGrp J ∧ IsPGroup 2 S ∧
      (∀ h ∈ P, ∀ s ∈ S, h * s * h⁻¹ ∈ S) ∧ ∃ h ∈ P, ∃ s ∈ S, h * s * h⁻¹ ≠ s := by
  have hψv : (J *ᵥ v) ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact hJa v
  have hψ : ∀ h ∈ P, ∀ y : ι → K,
      (J *ᵥ v) ⬝ᵥ ((h : Matrix ι ι K) *ᵥ y) = (J *ᵥ v) ⬝ᵥ y := by
    intro h hh y
    have h1 : (J *ᵥ v) ⬝ᵥ ((h : Matrix ι ι K) *ᵥ y) = bf J ((h : Matrix ι ι K) *ᵥ y) v :=
      dotProduct_comm _ _
    have h2 : (J *ᵥ v) ⬝ᵥ y = bf J y v := dotProduct_comm _ _
    rw [h1, h2]
    have := (mem_isoGrp_iff J).1 (hPJ hh) y v
    rw [hfix h hh] at this
    exact this
  have hvw_of : ∀ w : ι → K, (J *ᵥ v) ⬝ᵥ w = 0 → bf J v w = 0 := by
    intro w hw
    have h1 : (J *ᵥ v) ⬝ᵥ w = bf J w v := dotProduct_comm _ _
    rw [bf_comm J hJ, ← h1]
    exact hw
  refine ⟨radFlag v (J *ᵥ v) hψv ⊓ isoGrp J, inf_le_right, ?_, ?_, ?_⟩
  · intro g
    refine ⟨2, ?_⟩
    have := radFlag_pow_four (hψv := hψv) g.2.1
    apply Subtype.ext
    simpa using this
  · intro h hh s hs
    refine ⟨radFlag_normalized (hfix h hh) (hψ h hh) hs.1, ?_⟩
    exact (isoGrp J).mul_mem ((isoGrp J).mul_mem (hPJ hh) hs.2) ((isoGrp J).inv_mem (hPJ hh))
  · obtain ⟨w, hw, h, hh, hne⟩ := exists_moved_of_family (hψv := hψv) hpK P hpow hfix hψ hP1
      (fun w => sglGL J hJ hJa v w)
      (fun h hh w hw => by
        rw [conj_sglGL J hJ hJa (hPJ hh) (hvw_of w hw), hfix h hh])
      (fun w w' hw hw' hww => sglGL_inj J hJ hJa hJnd hv (hvw_of w hw) (hvw_of w' hw') hww)
    have hvw := hvw_of w hw
    exact ⟨h, hh, sglGL J hJ hJa v w,
      ⟨sglGL_mem_radFlag J hJ hJa hvw hψv, sglGL_mem_isoGrp J hJ hJa hvw⟩, hne⟩

end CFSG.RankThree.PartOne.K133C
