module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagCore
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Universal CFSG.Timmesfeld.LieEmbed

@[expose] noncomputable def suHerm (n g : ℕ) (x y : Fin n → GaloisField 2 (2 * g)) : GaloisField 2 (2 * g) :=
  (fun i => CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g (x i)) ⬝ᵥ
    ((Unitary.antidiag n : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))).mulVec y)

private noncomputable abbrev rckFlagSUL_sigma (g : ℕ) :
    GaloisField 2 (2 * g) ≃+* GaloisField 2 (2 * g) :=
  CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g

private lemma rckFlagSUL_suHerm_eq_uForm (n g : ℕ) (x y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g x y = CFSG.Timmesfeld.LieEmbed.uForm (rckFlagSUL_sigma g) x y := rfl

private lemma rckFlagSUL_suHerm_add_left (n g : ℕ) (x x' y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g (x + x') y = suHerm n g x y + suHerm n g x' y := by
  simp only [rckFlagSUL_suHerm_eq_uForm, CFSG.Timmesfeld.LieEmbed.uForm_eq, Pi.add_apply,
    map_add, add_mul, Finset.sum_add_distrib]

private lemma rckFlagSUL_suHerm_add_right (n g : ℕ) (x y y' : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g x (y + y') = suHerm n g x y + suHerm n g x y' := by
  simp only [rckFlagSUL_suHerm_eq_uForm, CFSG.Timmesfeld.LieEmbed.uForm_eq, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]

private lemma rckFlagSUL_suHerm_smul_left (n g : ℕ) (l : GaloisField 2 (2 * g))
    (x y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g (l • x) y = rckFlagSUL_sigma g l * suHerm n g x y := by
  simp only [rckFlagSUL_suHerm_eq_uForm]
  exact CFSG.Timmesfeld.LieEmbed.uForm_smul_left (rckFlagSUL_sigma g) l x y

private lemma rckFlagSUL_suHerm_smul_right (n g : ℕ) (l : GaloisField 2 (2 * g))
    (x y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g x (l • y) = l * suHerm n g x y := by
  simp only [rckFlagSUL_suHerm_eq_uForm]
  exact CFSG.Timmesfeld.LieEmbed.uForm_smul_right (rckFlagSUL_sigma g) l x y

private lemma rckFlagSUL_suHerm_conj (n g : ℕ)
    (hσ : ∀ c : GaloisField 2 (2 * g), rckFlagSUL_sigma g (rckFlagSUL_sigma g c) = c)
    (x y : Fin n → GaloisField 2 (2 * g)) :
    rckFlagSUL_sigma g (suHerm n g x y) = suHerm n g y x := by
  simp only [rckFlagSUL_suHerm_eq_uForm]
  exact CFSG.Timmesfeld.LieEmbed.uForm_conj (rckFlagSUL_sigma g) hσ x y

private lemma rckFlagSUL_suHerm_zero_left (n g : ℕ) (y : Fin n → GaloisField 2 (2 * g)) :
    suHerm n g 0 y = 0 := by
  simp only [rckFlagSUL_suHerm_eq_uForm, CFSG.Timmesfeld.LieEmbed.uForm_eq, Pi.zero_apply,
    map_zero, zero_mul, Finset.sum_const_zero]

private lemma rckFlagSUL_eq_zero_of_suHerm {n g : ℕ} {v : Fin n → GaloisField 2 (2 * g)}
    (h : ∀ x, suHerm n g v x = 0) : v = 0 := by
  by_contra hv
  have hrow := CFSG.Timmesfeld.LieEmbed.uRow_ne_zero (rckFlagSUL_sigma g) hv
  apply hrow
  funext i
  have h1 := h (Pi.single i 1)
  rw [rckFlagSUL_suHerm_eq_uForm, ← CFSG.Timmesfeld.LieEmbed.uRow_dotProduct] at h1
  simpa [dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using h1

private theorem rckFlagSUL_uForm_mulVec_eq {n g : ℕ}
    (A : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g)))
    (x y : Fin n → GaloisField 2 (2 * g)) :
    CFSG.Timmesfeld.LieEmbed.uForm (rckFlagSUL_sigma g) (A.mulVec x) (A.mulVec y) =
      (fun a => rckFlagSUL_sigma g (x a)) ⬝ᵥ
        ((Unitary.conjTr (rckFlagSUL_sigma g) A * Unitary.antidiag n * A).mulVec y) := by
  rw [← CFSG.Timmesfeld.LieEmbed.uRow_dotProduct, CFSG.Timmesfeld.LieEmbed.uRow,
    CFSG.Timmesfeld.LieEmbed.map_mulVec_sigma, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.dotProduct_mulVec]
  simp only [Unitary.conjTr, Matrix.mul_assoc]

private theorem rckFlagSUL_conjTr_mul_antidiag_of_preserves {n g : ℕ}
    {A : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))}
    (hpres : ∀ x y, suHerm n g (A.mulVec x) (A.mulVec y) = suHerm n g x y) :
    Unitary.conjTr (rckFlagSUL_sigma g) A * Unitary.antidiag n * A = Unitary.antidiag n := by
  ext j k
  have h := hpres (Pi.single j 1) (Pi.single k 1)
  rw [rckFlagSUL_suHerm_eq_uForm, rckFlagSUL_uForm_mulVec_eq, rckFlagSUL_suHerm_eq_uForm] at h
  have hfun : (fun a => rckFlagSUL_sigma g ((Pi.single j 1 : Fin n → GaloisField 2 (2 * g)) a)) =
      (Pi.single j 1 : Fin n → GaloisField 2 (2 * g)) := by
    funext a
    by_cases ha : a = j
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  rw [hfun] at h
  have hL : (Pi.single j 1 : Fin n → GaloisField 2 (2 * g)) ⬝ᵥ
      ((Unitary.conjTr (rckFlagSUL_sigma g) A * Unitary.antidiag n * A).mulVec
        (Pi.single k 1)) =
      (Unitary.conjTr (rckFlagSUL_sigma g) A * Unitary.antidiag n * A :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))) j k := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.mem_univ]
  have hR : CFSG.Timmesfeld.LieEmbed.uForm (rckFlagSUL_sigma g)
      (Pi.single j 1 : Fin n → GaloisField 2 (2 * g)) (Pi.single k 1) =
      Unitary.antidiag n j k := by
    rw [CFSG.Timmesfeld.LieEmbed.uForm_eq,
      Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp [Unitary.antidiag, Matrix.of_apply, Pi.single_apply, eq_comm]
  rw [hL, hR] at h
  exact h

theorem rckFlagSU_lift (n g : ℕ) (hg : 1 ≤ g)
    (R' : Subgroup (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * g)) 2 g) n))
    (W H : Submodule (GaloisField 2 (2 * g)) (Fin n → GaloisField 2 (2 * g))) (hWH : W ≤ H)
    (hv : ∀ v ∈ R', v ≠ 1 →
      LinearMap.range (Matrix.toLin' (((v : GL (Fin n) (GaloisField 2 (2 * g))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))) - 1)) = W ∧
      LinearMap.ker (Matrix.toLin' (((v : GL (Fin n) (GaloisField 2 (2 * g))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))) - 1)) = H)
    (r : Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * g)) 2 g) n)
    (hr : r ∈ R') (hr1 : r ≠ 1) (m : Fin n → GaloisField 2 (2 * g))
    (hm : suHerm n g ((((r : GL (Fin n) (GaloisField 2 (2 * g))) :
      Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))) - 1).mulVec m) m = 0) :
    ∃ c ∈ Subgroup.centralizer ({r} : Set (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * g)) 2 g) n)),
      ∀ w ∈ W, ((c : GL (Fin n) (GaloisField 2 (2 * g))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))).mulVec w =
        w + suHerm n g m w • (((r : GL (Fin n) (GaloisField 2 (2 * g))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))) - 1).mulVec m := by
  classical
  have hgpos : 2 * g ≠ 0 := by omega
  have hK : Nat.card (GaloisField 2 (2 * g)) = (2 ^ g) ^ 2 := by
    rw [GaloisField.card 2 (2 * g) hgpos, show 2 * g = g * 2 by omega, pow_mul]
  have hσ : ∀ c : GaloisField 2 (2 * g), rckFlagSUL_sigma g (rckFlagSUL_sigma g c) = c :=
    CFSG.LieType.BorelTits.unitaryInvolution_involutive hK
  let Ar : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g)) :=
    ((r : GL (Fin n) (GaloisField 2 (2 * g))) : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g)))
  let N : (Fin n → GaloisField 2 (2 * g)) →ₗ[GaloisField 2 (2 * g)]
      (Fin n → GaloisField 2 (2 * g)) := Matrix.toLin' (Ar - 1)
  have hrange : N.range = W := by simpa only [N, Ar] using (hv r hr hr1).1
  have hker : N.ker = H := by simpa only [N, Ar] using (hv r hr hr1).2
  have hNr : Matrix.toLin' Ar = N + 1 := by
    have h : Matrix.toLin' Ar - 1 = N := by
      dsimp only [N]
      rw [map_sub, Matrix.toLin'_one]
      rfl
    exact sub_eq_iff_eq_add.mp h
  have hNr_apply : ∀ x : Fin n → GaloisField 2 (2 * g), Ar.mulVec x = N x + x := by
    intro x
    have h := congrArg (fun L : (Fin n → GaloisField 2 (2 * g)) →ₗ[GaloisField 2 (2 * g)]
        (Fin n → GaloisField 2 (2 * g)) => L x) hNr
    simpa [Matrix.toLin'_apply, LinearMap.add_apply] using h
  have hpres_r : ∀ x y, suHerm n g (Ar.mulVec x) (Ar.mulVec y) = suHerm n g x y := by
    intro x y
    have h := CFSG.Timmesfeld.LieEmbed.uForm_mulVec (rckFlagSUL_sigma g) r x y
    have hsmat : CFSG.Timmesfeld.LieEmbed.suMat (rckFlagSUL_sigma g) n r = Ar := rfl
    rw [hsmat] at h
    simpa only [rckFlagSUL_suHerm_eq_uForm] using h
  have hNw : ∀ w ∈ W, N w = 0 := by
    intro w hw
    have hwH : w ∈ N.ker := by rw [hker]; exact hWH hw
    simpa using hwH
  have hNN : N * N = 0 := by
    apply LinearMap.ext
    intro x
    have hx : N x ∈ N.ker := by
      rw [hker]
      exact hWH (by rw [← hrange]; exact LinearMap.mem_range_self N x)
    show N (N x) = 0
    exact hx
  have hNNm : N (N m) = 0 := by
    have h := congrArg (fun L : (Fin n → GaloisField 2 (2 * g)) →ₗ[GaloisField 2 (2 * g)]
        (Fin n → GaloisField 2 (2 * g)) => L m) hNN
    simpa [Module.End.mul_apply] using h
  have hU1 : ∀ w ∈ W, ∀ y, suHerm n g w (N y) = 0 := by
    intro w hw y
    have h := hpres_r w y
    rw [show Ar.mulVec w = w by rw [hNr_apply w, hNw w hw, zero_add], hNr_apply y] at h
    rw [rckFlagSUL_suHerm_add_right] at h
    have h' : suHerm n g w (N y) + suHerm n g w y = 0 + suHerm n g w y := by simpa using h
    exact add_right_cancel h'
  have hWW : ∀ w ∈ W, ∀ w' ∈ W, suHerm n g w w' = 0 := by
    intro w hw w' hw'
    have hwr : w ∈ N.range := by rw [hrange]; exact hw
    have hw'r : w' ∈ N.range := by rw [hrange]; exact hw'
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hwr
    obtain ⟨z', rfl⟩ := LinearMap.mem_range.mp hw'r
    exact hU1 (N z) (by rw [← hrange]; exact LinearMap.mem_range_self N z) z'
  have hTot : ∀ x y, suHerm n g (N x) (N y) = 0 := fun x y =>
    hU1 (N x) (by rw [← hrange]; exact LinearMap.mem_range_self N x) y
  have hU2 : ∀ x y, suHerm n g (N x) y = suHerm n g x (N y) := by
    intro x y
    have h := hpres_r x y
    simp only [hNr_apply, rckFlagSUL_suHerm_add_left, rckFlagSUL_suHerm_add_right, hTot x y,
      zero_add] at h
    have h0 : suHerm n g (N x) y + suHerm n g x (N y) = 0 := by
      have h1 : (suHerm n g (N x) y + suHerm n g x (N y)) + suHerm n g x y =
          0 + suHerm n g x y := by simpa [add_assoc, add_comm, add_left_comm] using h
      exact add_right_cancel h1
    exact (CharTwo.add_eq_zero).mp h0
  have hmN : suHerm n g (N m) m = 0 := by
    simpa only [N, Ar, Matrix.toLin'_apply] using hm
  by_cases hu : N m = 0
  · refine ⟨1, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]; simp
    · intro w hw
      have hm0 : (((r : GL (Fin n) (GaloisField 2 (2 * g))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))) - 1).mulVec m = 0 := by
        simpa only [N, Ar, Matrix.toLin'_apply] using hu
      simp [hm0]
  · have hfix : rckFlagSUL_sigma g (suHerm n g m m) = suHerm n g m m := by
      rw [rckFlagSUL_suHerm_eq_uForm]
      exact CFSG.Timmesfeld.LieEmbed.uForm_conj (rckFlagSUL_sigma g) hσ m m
    have hφne : ∃ v ∈ W, suHerm n g m v ≠ 0 := by
      by_contra h
      push Not at h
      have hNm : N m = 0 := rckFlagSUL_eq_zero_of_suHerm (fun x => by
        rw [hU2 m x]
        exact h (N x) (by rw [← hrange]; exact LinearMap.mem_range_self N x))
      exact hu hNm
    obtain ⟨v, hvW, hvne⟩ := hφne
    obtain ⟨c, hc⟩ :=
      CFSG.LieType.BorelTits.exists_add_unitaryInvolution_eq hK (a := suHerm n g m m) hfix
    let l : GaloisField 2 (2 * g) := c * (suHerm n g m v)⁻¹
    let w₀ : Fin n → GaloisField 2 (2 * g) := l • v
    have hw₀W : w₀ ∈ W := W.smul_mem l hvW
    have hw₀ : suHerm n g m w₀ = c := by
      dsimp only [w₀, l]
      rw [rckFlagSUL_suHerm_smul_right, mul_assoc, inv_mul_cancel₀ hvne, mul_one]
    let m' : Fin n → GaloisField 2 (2 * g) := m + w₀
    have hNw₀ : N w₀ = 0 := hNw w₀ hw₀W
    have hNm' : N m' = N m := by
      dsimp only [m']
      rw [map_add, hNw₀, add_zero]
    have hm'w : ∀ w ∈ W, suHerm n g m' w = suHerm n g m w := by
      intro w hw
      dsimp only [m']
      rw [rckFlagSUL_suHerm_add_left, hWW w₀ hw₀W w hw, add_zero]
    have huw : ∀ w ∈ W, suHerm n g (N m) w = 0 := fun w hw =>
      hWW (N m) (by rw [← hrange]; exact LinearMap.mem_range_self N m) w hw
    have hmNm : suHerm n g m (N m) = 0 := by
      have h := rckFlagSUL_suHerm_conj n g hσ (N m) m
      rw [hmN, map_zero] at h
      exact h.symm
    have hm'u : suHerm n g m' (N m) = 0 := by
      dsimp only [m']
      rw [rckFlagSUL_suHerm_add_left, hmNm, hWW w₀ hw₀W (N m)
        (by rw [← hrange]; exact LinearMap.mem_range_self N m), add_zero]
    have huu : suHerm n g (N m) (N m) = 0 :=
      hWW (N m) (by rw [← hrange]; exact LinearMap.mem_range_self N m) (N m)
        (by rw [← hrange]; exact LinearMap.mem_range_self N m)
    have hum' : suHerm n g (N m) m' = 0 := by
      have h := rckFlagSUL_suHerm_conj n g hσ (N m) m'
      rw [hm'u] at h
      exact (map_eq_zero_iff (rckFlagSUL_sigma g) (rckFlagSUL_sigma g).injective).mp h
    have hw₀m : suHerm n g w₀ m = rckFlagSUL_sigma g c := by
      have h := rckFlagSUL_suHerm_conj n g hσ m w₀
      rw [hw₀] at h
      exact h.symm
    have hm'm' : suHerm n g m' m' = 0 := by
      dsimp only [m']
      rw [rckFlagSUL_suHerm_add_left, rckFlagSUL_suHerm_add_right, rckFlagSUL_suHerm_add_right,
        hw₀, hw₀m, hWW w₀ hw₀W w₀ hw₀W, ← hc, add_zero]
      have h : ((c + rckFlagSUL_sigma g c) + c) + rckFlagSUL_sigma g c =
          (c + rckFlagSUL_sigma g c) + (c + rckFlagSUL_sigma g c) := by abel
      rw [h, CharTwo.add_self_eq_zero]
    let φm' : (Fin n → GaloisField 2 (2 * g)) →ₗ[GaloisField 2 (2 * g)]
        (GaloisField 2 (2 * g)) :=
      { toFun := fun x => suHerm n g m' x
        map_add' := rckFlagSUL_suHerm_add_right n g m'
        map_smul' := fun a x => rckFlagSUL_suHerm_smul_right n g a m' x }
    let φu : (Fin n → GaloisField 2 (2 * g)) →ₗ[GaloisField 2 (2 * g)]
        (GaloisField 2 (2 * g)) :=
      { toFun := fun x => suHerm n g (N m) x
        map_add' := rckFlagSUL_suHerm_add_right n g (N m)
        map_smul' := fun a x => rckFlagSUL_suHerm_smul_right n g a (N m) x }
    have hφm' : ∀ x, φm' x = suHerm n g m' x := fun x => rfl
    have hφu : ∀ x, φu x = suHerm n g (N m) x := fun x => rfl
    let X : Module.End (GaloisField 2 (2 * g)) (Fin n → GaloisField 2 (2 * g)) :=
      φm'.smulRight (N m) + φu.smulRight m'
    have hXX : X * X = 0 := by
      apply LinearMap.ext
      intro x
      dsimp only [Module.End.mul_apply, X]
      simp only [LinearMap.add_apply, LinearMap.smulRight_apply, hφm', hφu]
      simp only [rckFlagSUL_suHerm_add_right, rckFlagSUL_suHerm_smul_right, hm'u, hm'm', huu,
        hum', mul_zero, zero_smul, add_zero]
      rfl
    have hXN : X * N = N * X := by
      apply LinearMap.ext
      intro x
      dsimp only [Module.End.mul_apply, X]
      simp only [LinearMap.add_apply, LinearMap.smulRight_apply, hφm', hφu]
      simp only [map_add, map_smul, ← hU2 m' x, hNm', ← hU2 (N m) x, hNNm,
        rckFlagSUL_suHerm_zero_left, zero_smul, smul_zero, add_zero, zero_add]
    let G : Module.End (GaloisField 2 (2 * g)) (Fin n → GaloisField 2 (2 * g)) := 1 + X
    have hGN : G * N = N * G := by
      dsimp only [G]
      rw [add_mul, one_mul, mul_add, mul_one, hXN]
    have hGpres : ∀ x y, suHerm n g (G x) (G y) = suHerm n g x y := by
      intro x y
      have hXXy : suHerm n g (X x) (X y) = 0 := by
        dsimp only [X]
        simp only [LinearMap.add_apply, LinearMap.smulRight_apply, hφm', hφu]
        simp only [rckFlagSUL_suHerm_add_left, rckFlagSUL_suHerm_add_right,
          rckFlagSUL_suHerm_smul_left, rckFlagSUL_suHerm_smul_right, huu, hum', hm'u, hm'm']
        ring
      have hcross : suHerm n g (X x) y = suHerm n g x (X y) := by
        dsimp only [X]
        simp only [LinearMap.add_apply, LinearMap.smulRight_apply, hφm', hφu]
        simp only [rckFlagSUL_suHerm_add_left, rckFlagSUL_suHerm_add_right,
          rckFlagSUL_suHerm_smul_left, rckFlagSUL_suHerm_smul_right,
          rckFlagSUL_suHerm_conj n g hσ m' x, rckFlagSUL_suHerm_conj n g hσ (N m) x,
          ← rckFlagSUL_suHerm_conj n g hσ y (N m), ← rckFlagSUL_suHerm_conj n g hσ y m']
        ring
      dsimp only [G]
      change suHerm n g (x + X x) (y + X y) = suHerm n g x y
      simp only [rckFlagSUL_suHerm_add_left, rckFlagSUL_suHerm_add_right]
      rw [hXXy, hcross, add_zero, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have hcomm_lin : G * Matrix.toLin' Ar = Matrix.toLin' Ar * G := by
      rw [hNr, mul_add, mul_one, hGN, add_mul, one_mul]
    have hinj : Function.Injective (Matrix.toLin' (R := GaloisField 2 (2 * g))
        (m := Fin n) (n := Fin n)) := by
      intro A B h
      have hh := congrArg (LinearMap.toMatrix' (R := GaloisField 2 (2 * g))
        (m := Fin n) (n := Fin n)) h
      simpa only [LinearMap.toMatrix'_toLin'] using hh
    let Gm : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g)) := LinearMap.toMatrix' G
    have hGm_apply : ∀ x, Gm.mulVec x = G x := by
      intro x
      have h := congrArg (fun L : (Fin n → GaloisField 2 (2 * g)) →ₗ[GaloisField 2 (2 * g)]
          (Fin n → GaloisField 2 (2 * g)) => L x)
        (Matrix.toLin'_toMatrix' (R := GaloisField 2 (2 * g)) (m := Fin n) (n := Fin n) G)
      simpa [Gm, Matrix.toLin'_apply] using h
    have hmat_comm : Gm * Ar = Ar * Gm := by
      apply hinj
      show Matrix.toLin' (Gm * Ar) = Matrix.toLin' (Ar * Gm)
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
      simp only [Gm, Matrix.toLin'_toMatrix']
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
      exact hcomm_lin
    have hXX_nil : IsNilpotent (LinearMap.toMatrix' X) := by
      refine IsNilpotent.mk _ 2 ?_
      rw [pow_two, ← LinearMap.toMatrix'_mul, hXX, map_zero]
    have hGm_eq : Gm = 1 + LinearMap.toMatrix' X := by
      dsimp only [Gm, G]
      rw [map_add, LinearMap.toMatrix'_one]
    have hGm_det : Gm.det = 1 := by
      rw [hGm_eq]
      exact CFSG.LieType.BorelTits.det_one_add_of_isNilpotent
        (F := GaloisField 2 (2 * g)) 2 hXX_nil
    have hmat : Unitary.conjTr (rckFlagSUL_sigma g) Gm * Unitary.antidiag n * Gm =
        Unitary.antidiag n := by
      refine rckFlagSUL_conjTr_mul_antidiag_of_preserves (n := n) (g := g) (A := Gm) ?_
      intro x y
      rw [hGm_apply x, hGm_apply y]
      exact hGpres x y
    let gmat : GL (Fin n) (GaloisField 2 (2 * g)) :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero Gm (by rw [hGm_det]; exact one_ne_zero)
    have hmemSU : gmat ∈ Unitary.SU (rckFlagSUL_sigma g) n := by
      rw [Unitary.mem_SU]
      exact ⟨hGm_det, hmat⟩
    let cc : Unitary.SU (rckFlagSUL_sigma g) n := ⟨gmat, hmemSU⟩
    have hccmat : ((cc : GL (Fin n) (GaloisField 2 (2 * g))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))) = Gm := rfl
    refine ⟨cc, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
      show Gm * Ar = Ar * Gm
      exact hmat_comm
    · intro w hw
      have hXw : X w = suHerm n g m w • N m := by
        dsimp only [X]
        simp only [LinearMap.add_apply, LinearMap.smulRight_apply, hφm', hφu]
        rw [hm'w w hw, huw w hw, zero_smul, add_zero]
      have hact : Gm.mulVec w = w + suHerm n g m w • N m := by
        rw [hGm_apply]
        dsimp only [G]
        change w + X w = w + suHerm n g m w • N m
        rw [hXw]
      have hNm_eq : N m = (((r : GL (Fin n) (GaloisField 2 (2 * g))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * g))) - 1).mulVec m := by
        rw [show N m = (Ar - 1).mulVec m from Matrix.toLin'_apply (Ar - 1) m]
      rw [hccmat, hact, hNm_eq]

end CFSG.StandardType.RCKFlag
