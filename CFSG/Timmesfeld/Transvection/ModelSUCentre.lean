module

public import CFSG.Timmesfeld.Transvection.ModelSUTheta
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection

namespace ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

theorem eq_one_of_mem_isUTransGroup_of_mem_center [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {a d : Fin m → F} (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) {k : SU σ m} (hk : k ∈ T)
    (hkc : k ∈ Subgroup.center (SU σ m)) : k = 1 := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  obtain ⟨c, -, hkc'⟩ := (hT.1 k).1 hk
  obtain ⟨t, ht⟩ := exists_suMat_eq_uTrans hσ hdd h1
  have hda : uForm σ d a = 1 := uForm_swap_eq_one hσ had
  have hcomm : suMat σ m (t * k) *ᵥ d = suMat σ m (k * t) *ᵥ d := by
    rw [Subgroup.mem_center_iff.1 hkc t]
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hkc', ht] at hcomm
  have h2 := congrArg (uForm σ a) hcomm
  simp only [uTrans_mulVec, uForm_add_right, uForm_smul_right, haa, had, hdd, hda] at h2
  have hc : c = 0 := by linear_combination h2
  apply suMat_injective σ
  rw [hkc', hc, uTrans_zero, map_one]

theorem suMat_mulVec_eq_sub_of_mem_uRad (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (had : uForm σ a d = 1) {T : Subgroup (SU σ m)}
    (Θ : SUThetaFacts σ a d T) {x : SU σ m} (hx : x ∈ uRad σ a) {p : Fin m → F}
    (hp : p ∈ perpPair σ a d) :
    suMat σ m x *ᵥ p = p - uForm σ (radVec σ a d x) p • a := by
  obtain ⟨c, hc⟩ := hx.2 p hp.1
  obtain ⟨μ, hμ⟩ := exists_suMat_mulVec_d_eq_radVec had hx
  have hda : uForm σ d a = 1 := uForm_swap_eq_one hσ had
  have hwa : uForm σ (radVec σ a d x) a = 0 := uForm_eq_zero_comm hσ (Θ.mem_perp x).1
  have h1 := uForm_mulVec σ x d p
  rw [hμ, hc] at h1
  simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, hp.1, hp.2,
    hda, hwa, haa] at h1
  have hc' : c = -uForm σ (radVec σ a d x) p := by linear_combination h1
  rw [hc, hc', neg_smul, ← sub_eq_add_neg]

theorem uForm_radVec_eq_of_commute (hσ : ∀ c, σ (σ c) = c) {a d : Fin m → F}
    (haa : uForm σ a a = 0) (hdd : uForm σ d d = 0) (had : uForm σ a d = 1)
    {T : Subgroup (SU σ m)} (Θ : SUThetaFacts σ a d T) {z u : SU σ m} (hz : z ∈ uRad σ a)
    (hu : u ∈ uRad σ a) (h : z * u = u * z) :
    uForm σ (radVec σ a d z) (radVec σ a d u) = uForm σ (radVec σ a d u) (radVec σ a d z) := by
  obtain ⟨μz, hμz⟩ := exists_suMat_mulVec_d_eq_radVec had hz
  obtain ⟨μu, hμu⟩ := exists_suMat_mulVec_d_eq_radVec had hu
  have hda : uForm σ d a = 1 := uForm_swap_eq_one hσ had
  have hwz := Θ.mem_perp z
  have hwu := Θ.mem_perp u
  have hzu := suMat_mulVec_eq_sub_of_mem_uRad hσ haa had Θ hz hwu
  have huz := suMat_mulVec_eq_sub_of_mem_uRad hσ haa had Θ hu hwz
  have h1 : suMat σ m (z * u) *ᵥ d = suMat σ m (u * z) *ᵥ d := by rw [h]
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hμz, hμu] at h1
  simp only [mulVec_add, mulVec_smul, hz.1, hu.1, hμz, hμu, hzu, huz] at h1
  have h2 := congrArg (uForm σ d) h1
  simp only [uForm_add_right, uForm_sub_right, uForm_smul_right, hdd, hda, hwz.2, hwu.2] at h2
  linear_combination -h2

theorem mem_of_forall_commute_of_mem_uRad [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ c, σ c = c → ∃ e, e + σ e = c) {a d : Fin m → F} (haa : uForm σ a a = 0)
    (hdd : uForm σ d d = 0) (had : uForm σ a d = 1) {T : Subgroup (SU σ m)}
    (Θ : SUThetaFacts σ a d T) (G : SUGeomFacts σ a d) {z : SU σ m} (hz : z ∈ uRad σ a)
    (hc : ∀ u ∈ uRad σ a, z * u = u * z) : z ∈ T := by
  refine (Θ.eq_zero_iff hz).1 ?_
  by_contra hw0
  obtain ⟨e, he, -, hew⟩ := G.nonorth (Θ.mem_perp z) hw0
  obtain ⟨γ, hγ⟩ := htr 1 (map_one σ)
  obtain ⟨u, hu, hue⟩ := Θ.exists_eq
    ((perpPair σ a d).smul_mem (σ (γ * (uForm σ e (radVec σ a d z))⁻¹)) he)
  have h1 := uForm_radVec_eq_of_commute hσ haa hdd had Θ hz hu (hc u hu)
  have hβ : σ (uForm σ e (radVec σ a d z)) = uForm σ (radVec σ a d z) e := uForm_conj σ hσ _ _
  rw [hue, uForm_smul_right, uForm_smul_left, hσ, ← hβ, ← map_mul,
    inv_mul_cancel_right₀ hew] at h1
  rw [h1, CharTwo.add_self_eq_zero] at hγ
  exact zero_ne_one hγ

end ModelRank

end CFSG.Timmesfeld.Transvection
