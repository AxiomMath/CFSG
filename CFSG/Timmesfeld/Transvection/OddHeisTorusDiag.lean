module

public import CFSG.Timmesfeld.Transvection.OddHeisFrameBasics
import CFSG.Timmesfeld.Transvection.OddModelShortTorus
import CFSG.Timmesfeld.Transvection.OddNormalize
import CFSG.Timmesfeld.Transvection.OddResidueTrans
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LocalAnalysis.UniquenessCase

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H] {Δ : Set (Subgroup H)}
  {P Q : Fin (2 * r / 2) → Subgroup H} (hm : 4 ≤ 2 * r)

private theorem conjSub_framePt_le_of_toHom_diagonal
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q) {g : SU (unitaryInvolution F 2 n) (2 * r)}
    {d : Fin (2 * r) → F}
    (hg : mat (unitaryInvolution F 2 n) (2 * r) g = Matrix.diagonal d)
    (hd : ∀ s, unitaryInvolution F 2 n (d s) * d (Fin.rev s) = 1)
    (a : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) :
    conjSub (framePt P Q a) (R.toHom hFn (even_two_mul r) hm g) ≤ framePt P Q a := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨e, he, rfl⟩ := (hR.long a y).1 hy
  have hparam : unitaryInvolution F 2 n (d (crd a) * e * (d (crd (Sum.swap a)))⁻¹) =
      d (crd a) * e * (d (crd (Sum.swap a)))⁻¹ := by
    have hp : unitaryInvolution F 2 n (d (crd a)) = (d (crd (Sum.swap a)))⁻¹ := by
      have h := hd (crd a)
      rw [← crd_swap a] at h
      exact eq_inv_of_mul_eq_one_left h
    have hq : unitaryInvolution F 2 n (d (crd (Sum.swap a))) = (d (crd a))⁻¹ := by
      have h := hd (crd (Sum.swap a))
      have hrev : Fin.rev (crd (Sum.swap a)) = crd a := by rw [crd_swap, Fin.rev_rev]
      rw [hrev] at h
      exact eq_inv_of_mul_eq_one_left h
    rw [map_mul, map_mul, map_inv₀, hp, hq, he, inv_inv]
    ring
  have hconj : R.toHom hFn (even_two_mul r) hm g * R.ξL a e *
      (R.toHom hFn (even_two_mul r) hm g)⁻¹ =
      R.ξL a (d (crd a) * e * (d (crd (Sum.swap a)))⁻¹) := by
    rw [← R.toHom_suLong hFn (even_two_mul r) hm a he, ← map_inv, ← map_mul, ← map_mul,
      conj_suLong_of_mat_diagonal hg hd a e,
      R.toHom_suLong hFn (even_two_mul r) hm a hparam]
  change R.toHom hFn (even_two_mul r) hm g * R.ξL a e *
      (R.toHom hFn (even_two_mul r) hm g)⁻¹ ∈ framePt P Q a
  rw [hconj]
  exact (hR.long a _).2 ⟨_, hparam, rfl⟩

private theorem conjSub_framePt_eq_of_toHom_diagonal
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q) {g : SU (unitaryInvolution F 2 n) (2 * r)}
    {d : Fin (2 * r) → F}
    (hg : mat (unitaryInvolution F 2 n) (2 * r) g = Matrix.diagonal d)
    (hd : ∀ s, unitaryInvolution F 2 n (d s) * d (Fin.rev s) = 1)
    (a : Fin (2 * r / 2) ⊕ Fin (2 * r / 2)) :
    conjSub (framePt P Q a) (R.toHom hFn (even_two_mul r) hm g) = framePt P Q a := by
  refine le_antisymm (conjSub_framePt_le_of_toHom_diagonal hFn hm hR hg hd a) ?_
  have hdne : ∀ s, d s ≠ 0 := by
    intro s h
    have h1 := hd s
    rw [h, map_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hg' : mat (unitaryInvolution F 2 n) (2 * r) g⁻¹ =
      Matrix.diagonal (fun s => (d s)⁻¹) := by
    have hleft : Matrix.diagonal d * mat (unitaryInvolution F 2 n) (2 * r) g⁻¹ = 1 := by
      calc Matrix.diagonal d * mat (unitaryInvolution F 2 n) (2 * r) g⁻¹
          = mat (unitaryInvolution F 2 n) (2 * r) g *
              mat (unitaryInvolution F 2 n) (2 * r) g⁻¹ := by rw [hg]
        _ = mat (unitaryInvolution F 2 n) (2 * r) (g * g⁻¹) :=
            (map_mul (mat (unitaryInvolution F 2 n) (2 * r)) g g⁻¹).symm
        _ = mat (unitaryInvolution F 2 n) (2 * r) 1 := by rw [mul_inv_cancel]
        _ = 1 := map_one _
    have hdiag : Matrix.diagonal (fun s => (d s)⁻¹) * Matrix.diagonal d = 1 := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
      funext s
      exact inv_mul_cancel₀ (hdne s)
    calc mat (unitaryInvolution F 2 n) (2 * r) g⁻¹
        = 1 * mat (unitaryInvolution F 2 n) (2 * r) g⁻¹ := (one_mul _).symm
      _ = (Matrix.diagonal (fun s => (d s)⁻¹) * Matrix.diagonal d) *
            mat (unitaryInvolution F 2 n) (2 * r) g⁻¹ := by rw [hdiag]
      _ = Matrix.diagonal (fun s => (d s)⁻¹) *
            (Matrix.diagonal d * mat (unitaryInvolution F 2 n) (2 * r) g⁻¹) := by
          rw [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun s => (d s)⁻¹) * 1 := by rw [hleft]
      _ = Matrix.diagonal (fun s => (d s)⁻¹) := Matrix.mul_one _
  have hd' : ∀ s, unitaryInvolution F 2 n ((d s)⁻¹) * (d (Fin.rev s))⁻¹ = 1 := by
    intro s
    rw [map_inv₀, ← mul_inv, hd s, inv_one]
  have hle' : conjSub (framePt P Q a) (R.toHom hFn (even_two_mul r) hm g)⁻¹ ≤
      framePt P Q a := by
    rw [← map_inv]
    exact conjSub_framePt_le_of_toHom_diagonal hFn hm hR hg' hd' a
  calc framePt P Q a =
        conjSub (conjSub (framePt P Q a) (R.toHom hFn (even_two_mul r) hm g)⁻¹)
          (R.toHom hFn (even_two_mul r) hm g) := by
        rw [← conjSub_mul (framePt P Q a) (R.toHom hFn (even_two_mul r) hm g)
          ((R.toHom hFn (even_two_mul r) hm g)⁻¹), mul_inv_cancel, conjSub_one]
    _ ≤ conjSub (framePt P Q a) (R.toHom hFn (even_two_mul r) hm g) :=
        Subgroup.map_mono hle'

private theorem exists_conj_weyl_mul_eq_diagonal
    (R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H) {c : F} (hc : c ≠ 0) :
    ∃ (g : SU (unitaryInvolution F 2 n) (2 * r)) (d : Fin (2 * r) → F),
      R.toHom hFn (even_two_mul r) hm g =
        ((R.toHom hFn (even_two_mul r) hm
            (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (cPrevIdx r hr)))⁻¹ *
          (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
            R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
            R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) ∧
      mat (unitaryInvolution F 2 n) (2 * r) g = Matrix.diagonal d ∧
      (∀ s, unitaryInvolution F 2 n (d s) * d (Fin.rev s) = 1) ∧
      d (lowIdx (cLastIdx r hr)) = c ∧
      d (Fin.rev (lowIdx (cLastIdx r hr))) = (unitaryInvolution F 2 n c)⁻¹ := by
  classical
  have hk : (cPrevIdx r hr).val + 1 < 2 * r / 2 := by
    simp only [cPrevIdx, Fin.val_mk]
    omega
  let P' := cPrevIdx r hr
  let L' := cLastIdx r hr
  have hstep : (⟨P'.val + 1, hk⟩ : Fin (2 * r / 2)) = L' := by
    apply Fin.ext
    simp only [L', P', cLastIdx, cPrevIdx, Fin.val_mk]
    omega
  let w : F → SU (unitaryInvolution F 2 n) (2 * r) := fun t =>
    shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) t
  let W : H := R.toHom hFn (even_two_mul r) hm
    (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ P')
  let wξ : H := R.ξ (Sum.inl P') (Sum.inr L') c * R.ξ (Sum.inl L') (Sum.inr P') (-c⁻¹) *
    R.ξ (Sum.inl P') (Sum.inr L') c
  let g : SU (unitaryInvolution F 2 n) (2 * r) :=
    (shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) 1)⁻¹ *
      shortWeyl (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _) c
  let d : Fin (2 * r) → F :=
    shortTorusFun (unitaryInvolution F 2 n) (lowIdx L') (lowIdx P') c
  have hW : W = R.toHom hFn (even_two_mul r) hm (w 1) := by
    dsimp only [W]
    rw [R.toHom_levelWeyl_cPrevIdx hFn hr hm]
    rw [← R.toHom_shortWeyl_cPrevIdx hFn hr hm hk 1]
  have hwξ : wξ = R.toHom hFn (even_two_mul r) hm (w c) := by
    dsimp only [wξ]
    rw [← R.toHom_shortWeyl_cPrevIdx hFn hr hm hk c]
  have hDg : R.toHom hFn (even_two_mul r) hm g = W⁻¹ * wξ := by
    rw [hW, hwξ, ← map_inv, ← map_mul]
  have hg : mat (unitaryInvolution F 2 n) (2 * r) g = Matrix.diagonal d := by
    have h := mat_shortWeyl_inv_mul_shortWeyl
      (σ := unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (a := lowIdx P') (b := lowIdx (⟨P'.val + 1, hk⟩ : Fin (2 * r / 2)))
      (lowIdx_ne_succ hk) (lowIdx_ne_rev _ _) (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev _ _) (κ := 1) (c := c) one_ne_zero hc
    rw [show d = shortTorusFun (unitaryInvolution F 2 n)
        (lowIdx (⟨P'.val + 1, hk⟩ : Fin (2 * r / 2))) (lowIdx P') c by
      rw [show d = shortTorusFun (unitaryInvolution F 2 n) (lowIdx L') (lowIdx P') c from rfl,
        ← hstep]]
    rw [one_mul] at h
    exact h
  have hdunit : ∀ s, unitaryInvolution F 2 n (d s) * d (Fin.rev s) = 1 := by
    intro s
    have hsum := sum_mat_mul_mat (σ := unitaryInvolution F 2 n) g s (Fin.rev s)
    rw [hg] at hsum
    rw [Finset.sum_eq_single s] at hsum
    · simpa using hsum
    · intro t _ ht
      simp [Matrix.diagonal_apply, ht]
    · simp
  have hdb : d (lowIdx L') = c :=
    shortTorusFun_left (σ := unitaryInvolution F 2 n) (lowIdx L') (lowIdx P') c
  have hdrev : d (Fin.rev (lowIdx L')) = (unitaryInvolution F 2 n c)⁻¹ := by
    have h := hdunit (lowIdx L')
    rw [hdb] at h
    exact eq_inv_of_mul_eq_one_right h
  exact ⟨g, d, hDg, hg, hdunit, hdb, hdrev⟩

private theorem conjSub_framePt_eq_of_weyl_mul
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q) {c : F} (hc : c ≠ 0) :
    (∀ i : Fin (2 * r / 2),
        conjSub (P i)
          ((R.toHom hFn (even_two_mul r) hm
              (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
                (cPrevIdx r hr)))⁻¹ *
            (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
              R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
              R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) = P i) ∧
      ∀ i : Fin (2 * r / 2),
        conjSub (Q i)
          ((R.toHom hFn (even_two_mul r) hm
              (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
                (cPrevIdx r hr)))⁻¹ *
            (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
              R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
              R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) = Q i := by
  obtain ⟨g, d, hDg, hg, hdunit, -, -⟩ :=
    exists_conj_weyl_mul_eq_diagonal hFn hr hm R hc
  constructor
  · intro i
    have h := conjSub_framePt_eq_of_toHom_diagonal hFn hm hR hg hdunit (Sum.inl i)
    simpa only [framePt_inl, hDg] using h
  · intro i
    have h := conjSub_framePt_eq_of_toHom_diagonal hFn hm hR hg hdunit (Sum.inr i)
    simpa only [framePt_inr, hDg] using h

private theorem conjSub_map_heis_of_weyl_mul (hΔ : IsRootClass Δ)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm) {c : F} (hc : c ≠ 0) :
    conjSub ((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
      ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) =
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ := by
  obtain ⟨hP, hQ⟩ := conjSub_framePt_eq_of_weyl_mul hFn hr hm hR hc
  have hres : conjSub (residueGroup Δ P Q (cLastIdx r hr))
      ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) =
      residueGroup Δ P Q (cLastIdx r hr) := by
    have h := conjSub_residueGroup_of_perm (k := cLastIdx r hr)
      (g := ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)))
      (π := Equiv.refl (Fin (2 * r / 2))) hP hQ hΔ
    simpa using h
  have hθr' : conjSub θ.range
      ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) = θ.range := by
    rw [hθr]
    exact hres
  have htop : (su3Top (unitaryInvolution F 2 n)).map θ = P (cLastIdx r hr) :=
    (SURelations.HasFrameImages.map_su3Top_su3Bot_of_comp hFn hr hm hR hθc).1
  exact conjSub_map_heis_eq hFn hθo htop hθr' (hP (cLastIdx r hr))

private theorem conj_weyl_mul_suLong
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ)
    {c : F} (hc : c ≠ 0) {e : F} (he : unitaryInvolution F 2 n e = e) :
    ((R.toHom hFn (even_two_mul r) hm
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (cPrevIdx r hr)))⁻¹ *
      (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
        R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
        R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) *
      θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) e) *
      ((R.toHom hFn (even_two_mul r) hm
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (cPrevIdx r hr)))⁻¹ *
      (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
        R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
        R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c))⁻¹ =
      θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2)))
        (unitaryInvolution F 2 n c * c * e)) := by
  let W : H := R.toHom hFn (even_two_mul r) hm
    (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr))
  let wξ : H := R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
    R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
    R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c
  let D : H := W⁻¹ * wξ
  change D * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) e) * D⁻¹ =
    θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2)))
      (unitaryInvolution F 2 n c * c * e))
  obtain ⟨g, d, hDg, hg, hdunit, hdb, hdrev⟩ :=
    exists_conj_weyl_mul_eq_diagonal hFn hr hm R hc
  have hDg' : D = R.toHom hFn (even_two_mul r) hm g := hDg.symm
  have hfix : unitaryInvolution F 2 n
      (d (lowIdx (cLastIdx r hr)) * e * (d (Fin.rev (lowIdx (cLastIdx r hr))))⁻¹) =
      d (lowIdx (cLastIdx r hr)) * e *
        (d (Fin.rev (lowIdx (cLastIdx r hr))))⁻¹ := by
    rw [hdb, hdrev, inv_inv]
    rw [map_mul, map_mul, unitaryInvolution_involutive hFn, he]
    ring
  have hfix2 : unitaryInvolution F 2 n
      (unitaryInvolution F 2 n c * c * e) =
      unitaryInvolution F 2 n c * c * e := by
    rw [map_mul, map_mul, unitaryInvolution_involutive hFn, he]
    ring
  have hlast : R.toHom hFn (even_two_mul r) hm
      (suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) e) =
      θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) e) :=
    (hd.long_last e he).1
  have hconj : g * suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) e * g⁻¹ =
      suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr))
        (unitaryInvolution F 2 n c * c * e) := by
    rw [conj_suLong_of_mat_diagonal hg hdunit (Sum.inl (cLastIdx r hr)) e]
    congr 1
    simp only [crd_inl, crd_swap]
    rw [hdb, hdrev, inv_inv]
    ring
  calc D * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) e) * D⁻¹
      = D * R.toHom hFn (even_two_mul r) hm
            (suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) e) * D⁻¹ := by
        rw [← hlast]
    _ = R.toHom hFn (even_two_mul r) hm
          (g * suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) e * g⁻¹) := by
        rw [hDg', ← map_inv, ← map_mul, ← map_mul]
    _ = R.toHom hFn (even_two_mul r) hm
          (suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr))
            (unitaryInvolution F 2 n c * c * e)) := by rw [hconj]
    _ = θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2)))
          (unitaryInvolution F 2 n c * c * e)) :=
        (hd.long_last (unitaryInvolution F 2 n c * c * e) hfix2).1

theorem SURelations.HasFrameImages.conj_weyl_mul_map_heis (hΔ : IsRootClass Δ)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr))
    (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) =
      R.lastBlock hFn (even_two_mul r) hm)
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) {c : F} (hc : c ≠ 0) :
    (∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) * θ x *
        ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c))⁻¹ ∈
      (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) ∧
    ∀ e : F, unitaryInvolution F 2 n e = e →
      ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) *
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) e) *
        ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c))⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2)))
          (unitaryInvolution F 2 n c * c * e)) := by
  constructor
  · intro x hx
    have hx' : θ x ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ :=
      ⟨x, hx, rfl⟩
    have hmem := conj_mem_conjSub
      (H := (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
      ((R.toHom hFn (even_two_mul r) hm
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)))⁻¹ *
        (R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c *
          R.ξ (Sum.inl (cLastIdx r hr)) (Sum.inr (cPrevIdx r hr)) (-c⁻¹) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) c)) hx'
    rwa [conjSub_map_heis_of_weyl_mul hFn hr hm hΔ hR hθr hθo hθc hc] at hmem
  · intro e he
    exact conj_weyl_mul_suLong hFn hr hm hd hc he

end CFSG.Timmesfeld.Transvection
