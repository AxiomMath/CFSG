module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinTorusAutBasic
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneSignedPerm

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.StandardType Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

private theorem planeExt_apply_mat (t : ℕ) (ε : Fin 2) (A : GL (Fin t ⊕ Fin t) K) :
    ((planeExt t ε A : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (A : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) 0 0 1 :=
  rfl

private theorem tau_apply_mat (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (t : ℕ) (ε : Fin 2) (u : PlaneRaw.V t) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks
        (WitSpNs.planeMat fun j =>
          ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K)) 0 0 1 := by
  rw [tau_eq_planeExt, planeExt_apply_mat, SpBlocks.coe_tau]

private theorem planeIdem_apply_mat (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    (planeIdem t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 := by
  ext x y
  rcases x with (i | i) | k <;> rcases y with (j | j) | l <;>
    simp [planeIdem, SpBlocks.planeIdem, Matrix.fromBlocks, Matrix.diagonal_apply]

private theorem one_sub_planeIdem_apply_mat (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) :
    (1 - planeIdem t ε S false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      Matrix.fromBlocks (1 - SpBlocks.planeIdem t S) 0 0 1 := by
  ext x y
  rcases x with (i | i) | k <;> rcases y with (j | j) | l <;>
    simp [planeIdem, SpBlocks.planeIdem, Matrix.fromBlocks, Matrix.diagonal_apply,
      Matrix.one_apply]

private theorem tau_linear_injective (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (t : ℕ) (ε : Fin 2) (hζ : Function.Injective ζ) : Function.Injective (tau ζ t ε) := by
  intro u v h
  apply SpBlocks.tau_injective hζ t
  apply Subtype.ext
  exact planeExt_injective (K := K) t ε (by simpa only [tau_eq_planeExt] using h)

private theorem planeExt_mem_levi (t : ℕ) (ε : Fin 2) {S : Finset (Fin t)}
    {g : ↥(StatedSp t K)} (hg : g ∈ SpBlocks.levi t S) :
    planeExt t ε ((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) ∈
      levi (planeIdem t ε S false) := by
  set G : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K :=
    (((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) with hG
  set P : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K := SpBlocks.planeIdem t S with hP
  have hGQ : G * (1 - P) = 1 - P := by
    change (((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) *
      (1 - SpBlocks.planeIdem t S) = 1 - SpBlocks.planeIdem t S
    exact hg
  have hGP : G * P = P * G := by
    change (((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
      Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K) * SpBlocks.planeIdem t S =
      SpBlocks.planeIdem t S * (((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) :
        Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K)
    exact SpBlocks.commute_planeIdem_of_mem_levi hg
  have hQG : (1 - P) * G = 1 - P := by
    calc (1 - P) * G = G - P * G := by rw [sub_mul, one_mul]
      _ = G - G * P := by rw [hGP]
      _ = G * (1 - P) := by rw [mul_sub, mul_one]
      _ = 1 - P := hGQ
  constructor
  · calc ((planeExt t ε ((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) * (1 - planeIdem t ε S false)
        = Matrix.fromBlocks G 0 0 1 * Matrix.fromBlocks (1 - P) 0 0 1 := by
            rw [planeExt_apply_mat, one_sub_planeIdem_apply_mat]
      _ = Matrix.fromBlocks (G * (1 - P)) 0 0 1 := by
            rw [Matrix.fromBlocks_multiply]; simp
      _ = Matrix.fromBlocks (1 - P) 0 0 1 := by rw [hGQ]
      _ = 1 - planeIdem t ε S false := by rw [one_sub_planeIdem_apply_mat]
  · calc (1 - planeIdem t ε S false) *
        ((planeExt t ε ((g : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) : GL (LinIdx t ε) K) :
          Matrix (LinIdx t ε) (LinIdx t ε) K)
        = Matrix.fromBlocks (1 - P) 0 0 1 * Matrix.fromBlocks G 0 0 1 := by
            rw [planeExt_apply_mat, one_sub_planeIdem_apply_mat]
      _ = Matrix.fromBlocks ((1 - P) * G) 0 0 1 := by
            rw [Matrix.fromBlocks_multiply]; simp
      _ = Matrix.fromBlocks (1 - P) 0 0 1 := by rw [hQG]
      _ = 1 - planeIdem t ε S false := by rw [one_sub_planeIdem_apply_mat]

private theorem commute_tau_of_mem_levi_linear
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    {S : Finset (Fin t)} {u : PlaneRaw.V t} (hu : ∀ i ∈ S, u i = 0)
    {g : GL (LinIdx t ε) K} (hg : g ∈ levi (planeIdem t ε S false)) :
    g * tau ζ t ε u = tau ζ t ε u * g := by
  set G : Matrix (LinIdx t ε) (LinIdx t ε) K := (g : Matrix (LinIdx t ε) (LinIdx t ε) K)
    with hG
  set T : Matrix (LinIdx t ε) (LinIdx t ε) K :=
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) with hT
  set P : Matrix (LinIdx t ε) (LinIdx t ε) K := planeIdem t ε S false with hP
  set Q : Matrix (LinIdx t ε) (LinIdx t ε) K := 1 - P with hQ
  have hGQ : G * Q = Q := by simpa [hG, hQ, hP] using hg.1
  have hQG : Q * G = Q := by simpa [hG, hQ, hP] using hg.2
  have hPQ : P + Q = 1 := by rw [hQ]; simp
  have hP' : P = 1 - Q := by rw [hQ]; abel_nf
  have hGP : G * P = P * G := by
    have h1 : G * P = G - Q := by
      rw [hP', mul_sub, mul_one, hGQ]
    have h2 : P * G = G - Q := by
      rw [hP', sub_mul, one_mul, hQG]
    rw [h1, h2]
  have hPsp : SpBlocks.planeIdem (K := K) t S * SpBlocks.planeIdem (K := K) t S =
      SpBlocks.planeIdem (K := K) t S :=
    SpBlocks.isIdempotentElem_planeIdem (K := K) t S
  have hPP : P * P = P := by
    rw [show P = Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 by
      simpa [hP] using planeIdem_apply_mat (K := K) t ε S,
      Matrix.fromBlocks_multiply]
    simp [hPsp]
  have hQQ : Q * Q = Q := by
    rw [hQ]
    calc (1 - P) * (1 - P) = 1 * (1 - P) - P * (1 - P) := by rw [sub_mul]
      _ = (1 - P) - (P * 1 - P * P) := by rw [one_mul, mul_sub]
      _ = (1 - P) - (P - P) := by rw [mul_one, hPP]
      _ = 1 - P := by rw [sub_self, sub_zero]
  have hM : ∀ i ∈ S,
      ((ζ (Multiplicative.ofAdd (u i)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
    intro i hi
    rw [hu i hi, ofAdd_zero, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hAB : WitSpNs.planeMat (fun j =>
      ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) * SpBlocks.planeIdem t S = SpBlocks.planeIdem t S := by
    rw [SpBlocks.planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · simp [hj, hM j hj]
    · simp [hj]
  have hBA : SpBlocks.planeIdem t S * WitSpNs.planeMat (fun j =>
      ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = SpBlocks.planeIdem t S := by
    rw [SpBlocks.planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · simp [hj, hM j hj]
    · simp [hj]
  have hTP : T * P = P := by
    rw [show T = Matrix.fromBlocks (WitSpNs.planeMat fun j =>
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) 0 0 1 by simpa [hT] using tau_apply_mat ζ t ε u,
      show P = Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 by
        simpa [hP] using planeIdem_apply_mat (K := K) t ε S,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [hAB]
  have hPT : P * T = P := by
    rw [show T = Matrix.fromBlocks (WitSpNs.planeMat fun j =>
        ((ζ (Multiplicative.ofAdd (u j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) 0 0 1 by simpa [hT] using tau_apply_mat ζ t ε u,
      show P = Matrix.fromBlocks (SpBlocks.planeIdem t S) 0 0 0 by
        simpa [hP] using planeIdem_apply_mat (K := K) t ε S,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    rw [hBA]
  have hTQ : T * Q = Q * T := by
    calc T * Q = T * (1 - P) := by rw [hQ]
      _ = T - T * P := by rw [mul_sub, mul_one]
      _ = T - P := by rw [hTP]
      _ = T - P * T := by rw [hPT]
      _ = (1 - P) * T := by rw [sub_mul, one_mul]
      _ = Q * T := by rw [hQ]
  have hQTQ : Q * T * Q = Q * T := by
    rw [Matrix.mul_assoc, hTQ, ← Matrix.mul_assoc, hQQ]
  have hTdecomp : T = P + Q * T * Q := by
    calc T = T * 1 := by rw [mul_one]
      _ = T * (P + Q) := by rw [hPQ]
      _ = T * P + T * Q := by rw [mul_add]
      _ = P + T * Q := by rw [hTP]
      _ = P + Q * T := by rw [hTQ]
      _ = P + Q * T * Q := by rw [hQTQ]
  have hGZ : G * (Q * T * Q) = Q * T * Q := by
    calc G * (Q * T * Q) = (G * (Q * T)) * Q := by rw [← Matrix.mul_assoc]
      _ = ((G * Q) * T) * Q := by rw [← Matrix.mul_assoc]
      _ = (G * Q) * (T * Q) := by rw [Matrix.mul_assoc]
      _ = Q * (T * Q) := by rw [hGQ]
      _ = Q * T * Q := by rw [← Matrix.mul_assoc]
  have hTZG : (Q * T * Q) * G = Q * T * Q := by
    calc (Q * T * Q) * G = (Q * T) * (Q * G) := by rw [← Matrix.mul_assoc]
      _ = Q * T * Q := by rw [hQG]
  have hGT : G * T = P * G + Q * T * Q := by
    calc G * T = G * (P + Q * T * Q) := by conv_lhs => rw [hTdecomp]
      _ = G * P + G * (Q * T * Q) := by rw [mul_add]
      _ = P * G + G * (Q * T * Q) := by rw [hGP]
      _ = P * G + Q * T * Q := by rw [hGZ]
  have hTG : T * G = P * G + Q * T * Q := by
    calc T * G = (P + Q * T * Q) * G := by conv_lhs => rw [hTdecomp]
      _ = P * G + (Q * T * Q) * G := by rw [add_mul]
      _ = P * G + Q * T * Q := by rw [hTZG]
  apply Units.ext
  exact hGT.trans hTG.symm

private theorem linExt_orientCoeff_of_ne_zero {x : ZMod 3} (h : x ≠ 0) :
    (if x = -1 then (-1 : ZMod 3) else 1) = x := by
  revert x
  decide

private theorem linExt_orientCoeff_mul_self (x : ZMod 3) :
    (if x = -1 then (-1 : ZMod 3) else 1) * (if x = -1 then (-1 : ZMod 3) else 1) = 1 := by
  revert x
  decide

private theorem linExt_orientEquiv_apply {t : ℕ} (e v : PlaneRaw.V t) (k : Fin t) :
    PlaneRaw.orientEquiv t e v k = (if e k = -1 then (-1 : ZMod 3) else 1) * v k := by
  simp only [PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

private theorem linExt_swapEquiv_apply {t : ℕ} (i j : Fin t) (v : PlaneRaw.V t) (k : Fin t) :
    PlaneRaw.swapEquiv t i j v k = v (Equiv.swap i j k) := by
  simp [PlaneRaw.swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

private theorem linExt_orientEquiv_mul_self {t : ℕ} (e : PlaneRaw.V t) :
    PlaneRaw.orientEquiv t e * PlaneRaw.orientEquiv t e = 1 := by
  ext w k
  rw [LinearEquiv.mul_apply, linExt_orientEquiv_apply, linExt_orientEquiv_apply, ← mul_assoc,
    linExt_orientCoeff_mul_self, one_mul]
  rfl

private theorem linExt_swapVec_eq_swapTwist {t : ℕ} (e : PlaneRaw.V t) {i j : Fin t}
    (hij : i ≠ j) (hi : e i ≠ 0) (hj : e j ≠ 0) (u : PlaneRaw.V t) :
    SpBlocks.swapVec e i j u = PlaneRaw.swapTwist t e i j u := by
  have h_inv : (PlaneRaw.orientEquiv t e)⁻¹ = PlaneRaw.orientEquiv t e :=
    inv_eq_of_mul_eq_one_left (linExt_orientEquiv_mul_self e)
  funext k
  rw [PlaneRaw.swapTwist, h_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    linExt_orientEquiv_apply, linExt_swapEquiv_apply, linExt_orientEquiv_apply]
  by_cases hki : k = i
  · subst hki
    rw [SpBlocks.swapVec_apply_fst e hij, Equiv.swap_apply_left,
      linExt_orientCoeff_of_ne_zero hi, linExt_orientCoeff_of_ne_zero hj, mul_assoc]
  · by_cases hkj : k = j
    · subst hkj
      rw [SpBlocks.swapVec_apply_snd, Equiv.swap_apply_right,
        linExt_orientCoeff_of_ne_zero hi, linExt_orientCoeff_of_ne_zero hj]
      ring
    · rw [SpBlocks.swapVec_apply_of_ne e hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj,
        ← mul_assoc, linExt_orientCoeff_mul_self, one_mul]

private theorem linExt_swapTwist_self {t : ℕ} (e : PlaneRaw.V t) (i : Fin t) :
    PlaneRaw.swapTwist t e i i = 1 := by
  have h : PlaneRaw.swapEquiv t i i = 1 := by
    ext u k
    rw [linExt_swapEquiv_apply, Equiv.swap_self, Equiv.refl_apply]
    rfl
  rw [PlaneRaw.swapTwist, h, mul_one, inv_mul_cancel]

theorem torusAut_blockGroup_extension_eq (h : LinTorusAutSubsetSignedPerm) {K : Type} [Field K]
    [Finite K] [CharP K 2] {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} {t : ℕ}
    {ε : Fin 2} (hK : Nat.card K = 2) (hζ : Function.Injective ζ) (e : PlaneRaw.V t) :
    torusAut ζ t ε (blockGroup ζ t ε (PlaneRaw.Code.extension e)) =
      ((PlaneRaw.twistedPermGroupOn t e : Subgroup _) : Set _) := by
  apply Set.Subset.antisymm
  · intro φ hφ
    have hφmem : φ ∈ torusAut ζ t ε (blockGroup ζ t ε (PlaneRaw.Code.extension e)) := hφ
    obtain ⟨y, hy, hyφ⟩ := hφ
    have hyB := Subgroup.mem_inf.mp hy
    have hyL : y ∈ levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) := hyB.1
    have hyC : y * tau ζ t ε e = tau ζ t ε e * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hyB.2
    have hφsp : φ ∈ PlaneRaw.signedPermGroup t := by
      have hsub := h ζ t ε hK hζ (blockGroup ζ t ε (PlaneRaw.Code.extension e))
      exact hsub hφmem
    refine PlaneRaw.mem_twistedPermGroupOn_of_mem_signedPermGroup hφsp ?_ ?_
    · have h := hyφ e
      have hτ : tau ζ t ε (φ e) = tau ζ t ε e := by
        rw [← h, hyC, mul_inv_cancel_right]
      exact tau_linear_injective ζ t ε hζ hτ
    · intro l hl
      have hu : ∀ i ∈ PlaneRaw.Code.extSupport e, (Pi.single l 1 : PlaneRaw.V t) i = 0 := by
        intro i hi
        refine Pi.single_eq_of_ne (fun hli => (PlaneRaw.mem_extSupport e i).mp hi ?_) 1
        rw [hli]
        exact hl
      have hcomm := commute_tau_of_mem_levi_linear ζ t ε hu hyL
      have h := hyφ (Pi.single l 1)
      have hτ : tau ζ t ε (φ (Pi.single l 1)) = tau ζ t ε (Pi.single l 1) := by
        rw [← h, hcomm, mul_inv_cancel_right]
      exact tau_linear_injective ζ t ε hζ hτ
  · refine closure_subset_torusAut ζ t ε ?_
    rintro φ ⟨i, j, hi, hj, rfl⟩
    by_cases hij : i = j
    · subst hij
      rw [linExt_swapTwist_self]
      exact one_mem_torusAut ζ t ε _
    · let σ : ↥(StatedSp t K) := SpBlocks.extSwap e i j hij
      let y : GL (LinIdx t ε) K :=
        planeExt t ε ((σ : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K)
      have hσL : σ ∈ SpBlocks.levi t (PlaneRaw.Code.extSupport e) :=
        SpBlocks.extSwap_mem_levi e
          ((PlaneRaw.mem_extSupport e i).mpr hi) ((PlaneRaw.mem_extSupport e j).mpr hj) hij
      have hyL : y ∈ levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) :=
        planeExt_mem_levi t ε hσL
      have hyC : y * tau ζ t ε e = tau ζ t ε e * y := by
        have h := SpBlocks.extSwap_conj_tau hK hζ hij hi hj e
        rw [SpBlocks.swapVec_self hij hi hj] at h
        have h' := congrArg (fun x : ↥(StatedSp t K) =>
          planeExt t ε ((x : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K)) h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at h'
        rw [show planeExt t ε ((SpBlocks.tau ζ t e : ↥(StatedSp t K)) :
          GL (Fin t ⊕ Fin t) K) = tau ζ t ε e from (tau_eq_planeExt ζ t ε e).symm] at h'
        exact mul_inv_eq_iff_eq_mul.mp h'
      refine ⟨y, Subgroup.mem_inf.mpr ⟨hyL,
        Subgroup.mem_centralizer_singleton_iff.mpr hyC⟩, fun u => ?_⟩
      have h := SpBlocks.extSwap_conj_tau hK hζ hij hi hj u
      rw [linExt_swapVec_eq_swapTwist e hij hi hj u] at h
      have h' := congrArg (fun x : ↥(StatedSp t K) =>
        planeExt t ε ((x : ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K)) h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at h'
      rw [show planeExt t ε ((SpBlocks.tau ζ t u : ↥(StatedSp t K)) :
        GL (Fin t ⊕ Fin t) K) = tau ζ t ε u from (tau_eq_planeExt ζ t ε u).symm,
        show planeExt t ε ((SpBlocks.tau ζ t (PlaneRaw.swapTwist t e i j u) :
          ↥(StatedSp t K)) : GL (Fin t ⊕ Fin t) K) =
          tau ζ t ε (PlaneRaw.swapTwist t e i j u) from
          (tau_eq_planeExt ζ t ε (PlaneRaw.swapTwist t e i j u)).symm] at h'
      exact h'

end CFSG.StandardType.GGQ2Frame.LinBlocks
