module

public import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic

public section

namespace CFSG.StandardType.SympMinus

open Matrix CFSG.StandardType.TorC
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram par sgn par_par par_injective
  sgn_ne_zero mulVec_single_one_apply)

variable {K : Type} [Field K] {m : ℕ}

@[expose] def SmuSuppIn (S : Finset (Fin m)) (v : Fin m ⊕ Fin m → K) : Prop :=
  ∀ r, WitSpNs.plane r ∉ S → v r = 0

@[expose] def SmuSuppOff (S : Finset (Fin m)) (v : Fin m ⊕ Fin m → K) : Prop :=
  ∀ r, WitSpNs.plane r ∈ S → v r = 0

@[expose] def SmuOffFix (S : Finset (Fin m)) (j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) : Prop :=
  ∀ x ∉ S, ∀ y : Fin m, blk j y x = if y = x then 1 else 0

theorem smu_coord_side_plane (s : Fin m ⊕ Fin m) :
    WitSpNs.coord (WitSpNs.side s) (WitSpNs.plane s) = s :=
  WitSpNs.eq_of_plane_side (by simp) (by simp)

theorem smu_plane_par (r : Fin m ⊕ Fin m) : WitSpNs.plane (par r) = WitSpNs.plane r := by
  rcases r with i | i <;> rfl

theorem smu_suppIn_single {S : Finset (Fin m)} {r : Fin m ⊕ Fin m} (hr : WitSpNs.plane r ∈ S) :
    SmuSuppIn S (Pi.single r (1 : K) : Fin m ⊕ Fin m → K) := by
  intro r' hr'
  have : r' ≠ r := fun h => hr' (h ▸ hr)
  simp [Pi.single_apply, this]

theorem smu_suppOff_single {S : Finset (Fin m)} {r : Fin m ⊕ Fin m} (hr : WitSpNs.plane r ∉ S) :
    SmuSuppOff S (Pi.single r (1 : K) : Fin m ⊕ Fin m → K) := by
  intro r' hr'
  have : r' ≠ r := fun h => hr (h ▸ hr')
  simp [Pi.single_apply, this]

theorem smu_vec_eq_sum_single (v : Fin m ⊕ Fin m → K) :
    v = ∑ r, v r • (Pi.single r (1 : K) : Fin m ⊕ Fin m → K) := by
  funext a
  simp [Finset.sum_apply, Pi.single_apply]

theorem SmuOffFix.mulVec_single {S : Finset (Fin m)}
    {j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K} (hj : SmuOffFix S j) (r : Fin m ⊕ Fin m)
    (hr : WitSpNs.plane r ∉ S) : j *ᵥ Pi.single r 1 = Pi.single r 1 := by
  funext s
  rw [mulVec_single_one_apply]
  have h := congrFun (congrFun (hj (WitSpNs.plane r) hr (WitSpNs.plane s)) (WitSpNs.side s))
    (WitSpNs.side r)
  simp only [blk, Matrix.of_apply, smu_coord_side_plane] at h
  rw [h]
  by_cases hp : WitSpNs.plane s = WitSpNs.plane r
  · by_cases hs : WitSpNs.side s = WitSpNs.side r
    · have : s = r := WitSpNs.eq_of_plane_side hp hs
      subst this
      simp [Matrix.one_apply]
    · have : s ≠ r := fun h => hs (by rw [h])
      simp [hp, hs, this, Matrix.one_apply, Pi.single_apply]
  · have : s ≠ r := fun h => hp (by rw [h])
    simp [hp, this, Pi.single_apply]

theorem SmuOffFix.mulVec_eq {S : Finset (Fin m)} {j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hj : SmuOffFix S j) {v : Fin m ⊕ Fin m → K} (hv : SmuSuppOff S v) : j *ᵥ v = v := by
  conv_lhs => rw [smu_vec_eq_sum_single v]
  conv_rhs => rw [smu_vec_eq_sum_single v]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.mulVec_smul]
  by_cases hr : WitSpNs.plane r ∈ S
  · simp [hv r hr]
  · rw [hj.mulVec_single r hr]

theorem smu_form_mulVec {j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hjs : jᵀ * gram K m * j = gram K m) (u w : Fin m ⊕ Fin m → K) :
    (j *ᵥ u) ⬝ᵥ (gram K m *ᵥ (j *ᵥ w)) = u ⬝ᵥ (gram K m *ᵥ w) := by
  calc (j *ᵥ u) ⬝ᵥ (gram K m *ᵥ (j *ᵥ w))
      = (u ᵥ* jᵀ) ⬝ᵥ (gram K m *ᵥ (j *ᵥ w)) := by rw [Matrix.vecMul_transpose]
    _ = u ⬝ᵥ (jᵀ *ᵥ (gram K m *ᵥ (j *ᵥ w))) := (Matrix.dotProduct_mulVec u jᵀ _).symm
    _ = u ⬝ᵥ ((jᵀ * gram K m * j) *ᵥ w) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = u ⬝ᵥ (gram K m *ᵥ w) := by rw [hjs]

theorem smu_form_single (w : Fin m ⊕ Fin m → K) (r : Fin m ⊕ Fin m) :
    w ⬝ᵥ (gram K m *ᵥ Pi.single (par r) (1 : K)) = w r * sgn K r := by
  simp only [dotProduct, mulVec_single_one_apply,
    _root_.CFSG.ClassicalInvolution.Models.SymplecticPairs.gram_apply]
  rw [Finset.sum_eq_single r]
  · simp
  · intro a _ ha
    rw [if_neg (fun h => ha (par_injective h).symm), mul_zero]
  · simp

theorem SmuOffFix.suppIn_mulVec {S : Finset (Fin m)}
    {j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hjs : jᵀ * CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K m * j =
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K m)
    (hj : SmuOffFix S j) {v : Fin m ⊕ Fin m → K} (hv : SmuSuppIn S v) : SmuSuppIn S (j *ᵥ v) := by
  intro r hr
  have hr' : WitSpNs.plane (par r) ∉ S := by rwa [smu_plane_par]
  have hfix : j *ᵥ (Pi.single (par r) (1 : K) : Fin m ⊕ Fin m → K) = Pi.single (par r) 1 :=
    hj.mulVec_single (par r) hr'
  have key : (j *ᵥ v) ⬝ᵥ (gram K m *ᵥ Pi.single (par r) (1 : K)) =
      v ⬝ᵥ (gram K m *ᵥ Pi.single (par r) (1 : K)) := by
    have h := smu_form_mulVec hjs v (Pi.single (par r) (1 : K))
    rwa [hfix] at h
  rw [smu_form_single, smu_form_single, hv r hr, zero_mul] at key
  exact (mul_eq_zero.mp key).resolve_right (sgn_ne_zero r)

theorem planeMat_mulVec_eq_of_one {S : Finset (Fin m)} {M : Fin m → Matrix (Fin 2) (Fin 2) K}
    (hM : ∀ x ∈ S, M x = 1) {v : Fin m ⊕ Fin m → K} (hv : SmuSuppIn S v) :
    WitSpNs.planeMat M *ᵥ v = v := by
  conv_lhs => rw [smu_vec_eq_sum_single v]
  conv_rhs => rw [smu_vec_eq_sum_single v]
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.mulVec_smul]
  by_cases hr : WitSpNs.plane r ∈ S
  · congr 1
    rcases r with x | x
    · have h := WitSpNs.planeMat_mulVec_inl M x
      have hx : M x = 1 := hM x hr
      rw [hx] at h
      simpa [Matrix.one_apply] using h
    · have h := WitSpNs.planeMat_mulVec_inr M x
      have hx : M x = 1 := hM x hr
      rw [hx] at h
      simpa [Matrix.one_apply] using h
  · rw [hv r hr]
    simp

theorem planeMat_suppOff_mulVec {S : Finset (Fin m)} (M : Fin m → Matrix (Fin 2) (Fin 2) K)
    {v : Fin m ⊕ Fin m → K} (hv : SmuSuppOff S v) : SmuSuppOff S (WitSpNs.planeMat M *ᵥ v) := by
  intro r hr
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases h : WitSpNs.plane r = WitSpNs.plane s
  · rw [hv s (h ▸ hr), mul_zero]
  · simp [WitSpNs.planeMat_apply, h]

theorem SmuOffFix.commute_planeMat {S : Finset (Fin m)}
    {j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K}
    (hjs : jᵀ * CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K m * j =
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K m)
    (hj : SmuOffFix S j) {M : Fin m → Matrix (Fin 2) (Fin 2) K} (hM : ∀ x ∈ S, M x = 1) :
    j * WitSpNs.planeMat M = WitSpNs.planeMat M * j := by
  ext a r
  have key : (j * WitSpNs.planeMat M) *ᵥ (Pi.single r (1 : K) : Fin m ⊕ Fin m → K) =
      (WitSpNs.planeMat M * j) *ᵥ (Pi.single r (1 : K) : Fin m ⊕ Fin m → K) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    by_cases hr : WitSpNs.plane r ∈ S
    · have hPe : WitSpNs.planeMat M *ᵥ (Pi.single r (1 : K) : Fin m ⊕ Fin m → K) =
          Pi.single r 1 := planeMat_mulVec_eq_of_one hM (smu_suppIn_single hr)
      have hje : SmuSuppIn S (j *ᵥ (Pi.single r (1 : K) : Fin m ⊕ Fin m → K)) :=
        hj.suppIn_mulVec hjs (smu_suppIn_single hr)
      rw [hPe, planeMat_mulVec_eq_of_one hM hje]
    · have hje : j *ᵥ (Pi.single r (1 : K) : Fin m ⊕ Fin m → K) = Pi.single r 1 :=
        hj.mulVec_single r hr
      have hPoff : SmuSuppOff S (WitSpNs.planeMat M *ᵥ
          (Pi.single r (1 : K) : Fin m ⊕ Fin m → K)) :=
        planeMat_suppOff_mulVec M (smu_suppOff_single hr)
      rw [hje, hj.mulVec_eq hPoff]
  have h1 := congrFun key a
  rwa [mulVec_single_one_apply, mulVec_single_one_apply] at h1

end CFSG.StandardType.SympMinus

end
