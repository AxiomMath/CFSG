module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup QuadraticMap CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

private theorem frame_neg_one_mem_sylow {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (Q : Sylow 2 SL(2, K)) :
    (-1 : SL(2, K)) ∈ (Q : Subgroup SL(2, K)) := by
  obtain ⟨x, hx, y, hy, hxx, -, -⟩ :=
    (CFSG.ComponentClassification.HarrisLit.T1.sylow_sl2_facts hodd Q).1 1
      (Q : Subgroup SL(2, K)).one_mem
  have hmem : x * x ∈ (Q : Subgroup SL(2, K)) := (Q : Subgroup SL(2, K)).mul_mem hx hx
  rwa [hxx] at hmem

private theorem frame_exists_quat_pair {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (P : Sylow 2 SL(2, K)) :
    ∃ i j : SL(2, K), i ∈ (P : Subgroup SL(2, K)) ∧ j ∈ (P : Subgroup SL(2, K)) ∧
      (i : Matrix (Fin 2) (Fin 2) K) * (i : Matrix (Fin 2) (Fin 2) K) = -1 ∧
      (j : Matrix (Fin 2) (Fin 2) K) * (j : Matrix (Fin 2) (Fin 2) K) = -1 ∧
      (i : Matrix (Fin 2) (Fin 2) K) * (j : Matrix (Fin 2) (Fin 2) K) =
        -((j : Matrix (Fin 2) (Fin 2) K) * (i : Matrix (Fin 2) (Fin 2) K)) := by
  obtain ⟨n, hn3, ⟨e⟩⟩ := CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion K hodd P
  set N : ℕ := 2 ^ (n - 2) with hNdef
  set hz : ZMod (2 * N) := ((N / 2 : ℕ) : ZMod (2 * N)) with hzdef
  have hNeven : Even N := by
    rw [hNdef]
    exact (Nat.even_pow' (by omega)).mpr even_two
  have hNpos : 0 < N := by
    rw [hNdef]
    exact pow_pos (by norm_num) _
  have hhalf_nat : N / 2 + N / 2 = N := by
    have h := Nat.div_two_mul_two_of_even hNeven
    omega
  have hhalf : hz + hz = (N : ZMod (2 * N)) := by
    rw [hzdef, ← Nat.cast_add, hhalf_nat]
  have hkey : -hz - (N : ZMod (2 * N)) = hz := by
    have hNzero : (N : ZMod (2 * N)) + (N : ZMod (2 * N)) = 0 := by
      rw [← Nat.cast_add, show N + N = 2 * N by ring, ZMod.natCast_self]
    linear_combination -hhalf - hNzero
  have hminus : (((e.symm (QuaternionGroup.a (N : ZMod (2 * N))) : (P : Subgroup SL(2, K))) :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
    have hord : orderOf ((e.symm (QuaternionGroup.a (N : ZMod (2 * N))) :
        (P : Subgroup SL(2, K))) : SL(2, K)) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two, QuaternionGroup.a_mul_a, ← Nat.cast_add,
          show N + N = 2 * N by ring, ZMod.natCast_self, QuaternionGroup.a_zero]
      · intro h1
        have h2' : (N : ZMod (2 * N)) = 0 :=
          QuaternionGroup.a.inj (by rw [h1, QuaternionGroup.one_def])
        rw [ZMod.natCast_eq_zero_iff] at h2'
        have hle := Nat.le_of_dvd (by omega) h2'
        omega
    have h := (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2
      ((e.symm (QuaternionGroup.a (N : ZMod (2 * N))) :
        (P : Subgroup SL(2, K))) : SL(2, K))).mp hord
    rw [h]
    rfl
  have hii : (((e.symm (QuaternionGroup.a hz) : (P : Subgroup SL(2, K))) : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) *
      (((e.symm (QuaternionGroup.a hz) : (P : Subgroup SL(2, K))) : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, ← map_mul,
      QuaternionGroup.a_mul_a, hhalf, hminus]
  have hjj : (((e.symm (QuaternionGroup.xa (0 : ZMod (2 * N))) : (P : Subgroup SL(2, K))) :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      (((e.symm (QuaternionGroup.xa (0 : ZMod (2 * N))) : (P : Subgroup SL(2, K))) :
        SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← pow_two,
      QuaternionGroup.xa_sq, hminus]
  have hL : (((e.symm (QuaternionGroup.a hz) : (P : Subgroup SL(2, K))) : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) *
      (((e.symm (QuaternionGroup.xa (0 : ZMod (2 * N))) : (P : Subgroup SL(2, K))) :
        SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (((e.symm (QuaternionGroup.xa (-hz)) : (P : Subgroup SL(2, K))) : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, ← map_mul,
      QuaternionGroup.a_mul_xa, zero_sub]
  have hR : (((e.symm (QuaternionGroup.xa (0 : ZMod (2 * N))) : (P : Subgroup SL(2, K))) :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      (((e.symm (QuaternionGroup.a hz) : (P : Subgroup SL(2, K))) : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) =
      (((e.symm (QuaternionGroup.xa hz) : (P : Subgroup SL(2, K))) : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, ← map_mul,
      QuaternionGroup.xa_mul_a, zero_add]
  have hstep : (((e.symm (QuaternionGroup.xa hz) : (P : Subgroup SL(2, K))) : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) =
      -(((e.symm (QuaternionGroup.xa (-hz)) : (P : Subgroup SL(2, K))) : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) := by
    have hmul : (((e.symm (QuaternionGroup.a (N : ZMod (2 * N))) : (P : Subgroup SL(2, K))) :
        SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        (((e.symm (QuaternionGroup.xa (-hz)) : (P : Subgroup SL(2, K))) : SL(2, K)) :
          Matrix (Fin 2) (Fin 2) K) =
        (((e.symm (QuaternionGroup.xa hz) : (P : Subgroup SL(2, K))) : SL(2, K)) :
          Matrix (Fin 2) (Fin 2) K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, ← map_mul,
        QuaternionGroup.a_mul_xa, hkey]
    rw [← hmul, hminus, neg_one_mul]
  refine ⟨↑(e.symm (QuaternionGroup.a hz)), ↑(e.symm (QuaternionGroup.xa (0 : ZMod (2 * N)))),
    (e.symm _).2, (e.symm _).2, hii, hjj, ?_⟩
  rw [hL, hR, hstep, neg_neg]

private theorem frame_eq_mulRight_of_commute_pair {K : Type} [Field K]
    {i j : Matrix (Fin 2) (Fin 2) K} (h2 : (2 : K) ≠ 0)
    (hii : i * i = -1) (hjj : j * j = -1) (hanti : i * j = -(j * i))
    (T : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K)
    (hi : ∀ X, T (i * X) = i * T X) (hj : ∀ X, T (j * X) = j * T X) :
    ∀ X, T X = X * T 1 := by
  have hj0 : j ≠ 0 := by
    intro h0
    have h1 : (-1 : Matrix (Fin 2) (Fin 2) K) = 0 := by rw [← hjj, h0, Matrix.zero_mul]
    have h2' : (-1 : K) = 0 := by
      have hthis := congrFun (congrFun h1 0) 0
      simp at hthis
    exact one_ne_zero (neg_eq_zero.mp h2')
  have hi_ne : ∀ c : K, i ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro c hc
    have hc2 : c * c = -1 := by
      have h1 : (c • (1 : Matrix (Fin 2) (Fin 2) K)) * (c • 1) = -1 := by rw [← hc]; exact hii
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one] at h1
      have h2' := congrFun (congrFun h1 0) 0
      simpa using h2'
    have hcj : c • j = -(c • j) := by
      have h := hanti
      rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul] at h
      exact h
    have h3 : ((2 : K) * c) • j = 0 := by
      rw [mul_smul, two_smul, eq_neg_iff_add_eq_zero.mp hcj]
    have hc0 : c = 0 := by
      rcases (smul_eq_zero.mp h3) with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' h2
        · exact h'
      · exact absurd h hj0
    rw [hc0, zero_mul] at hc2
    exact one_ne_zero (neg_eq_zero.mp hc2.symm)
  intro X
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin 2) (Fin 2) K, P = X - i * X * i := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Matrix (Fin 2) (Fin 2) K, N = X + i * X * i := ⟨_, rfl⟩
  have hPcomm : P * i = i * P := by
    rw [hPdef]
    have hL : (X - i * X * i) * i = X * i + i * X := by
      rw [Matrix.sub_mul, Matrix.mul_assoc (i * X) i i, hii, Matrix.mul_neg, Matrix.mul_one]
      abel
    have hR : i * (X - i * X * i) = i * X + X * i := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc i (i * X) i, ← Matrix.mul_assoc i i X, hii,
        Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mul]
      abel
    rw [hL, hR, add_comm]
  have hNanti : N * i = -(i * N) := by
    rw [hNdef]
    have hL : (X + i * X * i) * i = X * i - i * X := by
      rw [Matrix.add_mul, Matrix.mul_assoc (i * X) i i, hii, Matrix.mul_neg, Matrix.mul_one]
      abel
    have hR : i * (X + i * X * i) = i * X - X * i := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc i (i * X) i, ← Matrix.mul_assoc i i X, hii,
        Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mul]
      abel
    rw [hL, hR, neg_sub]
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.HarrisLit.T1.exists_eq_smul_one_add_smul_of_commute hi_ne hPcomm
  obtain ⟨Z, hZdef⟩ : ∃ Z : Matrix (Fin 2) (Fin 2) K, Z = -j * N := ⟨_, rfl⟩
  have hZcomm : Z * i = i * Z := by
    rw [hZdef]
    have hanti' : j * i = -(i * j) := by rw [hanti, neg_neg]
    have hR : i * (-j * N) = -(i * (j * N)) := by
      rw [Matrix.neg_mul, Matrix.mul_neg]
    have hL : (-j * N) * i = -(i * (j * N)) := by
      rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc, hNanti, Matrix.mul_neg, neg_neg,
        ← Matrix.mul_assoc, hanti', Matrix.neg_mul, Matrix.mul_assoc]
    rw [hL, hR]
  obtain ⟨c, d, hcd⟩ :=
    CFSG.ComponentClassification.HarrisLit.T1.exists_eq_smul_one_add_smul_of_commute hi_ne hZcomm
  have hNZ : j * Z = N := by
    rw [hZdef, ← Matrix.mul_assoc, Matrix.mul_neg, hjj, neg_neg, Matrix.one_mul]
  have hTi : T i = i * T 1 := by
    have h := hi 1
    rwa [Matrix.mul_one] at h
  have hTP : T P = P * T 1 := by
    rw [hab, map_add, map_smul, map_smul, hTi, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul]
  have hTZ : T Z = Z * T 1 := by
    rw [hcd, map_add, map_smul, map_smul, hTi, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul]
  have hTN : T N = N * T 1 := by
    rw [← hNZ, hj, hTZ, ← Matrix.mul_assoc j Z (T 1)]
  have hPN : P + N = (2 : K) • X := by
    rw [hPdef, hNdef, two_smul]
    abel
  have hX : X = (2 : K)⁻¹ • (P + N) := by
    rw [hPN, smul_smul, inv_mul_cancel₀ h2, one_smul]
  calc T X = T ((2 : K)⁻¹ • (P + N)) := by rw [hX]
    _ = (2 : K)⁻¹ • (P * T 1 + N * T 1) := by rw [map_smul, map_add, hTP, hTN]
    _ = X * T 1 := by rw [hX, Matrix.smul_mul, Matrix.add_mul]

theorem frame_apply_eq_self_of_commute_sylow {K V : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (F : Frame Q) (Q₁ Q₂ : Sylow 2 SL(2, K)) {h : V ≃ₗ[K] V}
    (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hh : Odd (orderOf h))
    (h₁ : ∀ A ∈ (Q₁ : Subgroup SL(2, K)), h * F.La A = F.La A * h)
    (h₂ : ∀ B ∈ (Q₂ : Subgroup SL(2, K)), h * F.swap.La B = F.swap.La B * h) :
    ∀ x ∈ F.span, h x = x := by
  classical
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hneg1 : (-1 : SL(2, K)) ∈ (Q₁ : Subgroup SL(2, K)) :=
    frame_neg_one_mem_sylow hodd Q₁
  have hLa_comm : ∀ y : V, F.La (-1) (h y) = h (F.La (-1) y) := by
    intro y
    rw [← LinearEquiv.mul_apply, ← h₁ (-1) hneg1, LinearEquiv.mul_apply]
  have hLa_incl : ∀ Z : Matrix (Fin 2) (Fin 2) K, F.La (-1) (F.incl Z) = -F.incl Z := by
    intro Z
    rw [F.La_apply_incl, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      neg_one_mul, LinearMap.map_neg]
  set T : Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
    F.coords ∘ₗ (h : V →ₗ[K] V) ∘ₗ F.incl with hTdef
  have hTapply : ∀ X, T X = F.coords (h (F.incl X)) := fun X => rfl
  have hincl : ∀ X, h (F.incl X) = F.incl (T X) := by
    intro X
    have h1 : F.La (-1) (h (F.incl X)) = -(h (F.incl X)) := by
      rw [hLa_comm, hLa_incl, map_neg]
    rw [F.La_neg_one_apply] at h1
    have h2' : (2 : K) • F.incl (F.coords (h (F.incl X))) = (2 : K) • h (F.incl X) := by
      have h1' : h (F.incl X) - (2 : K) • F.incl (F.coords (h (F.incl X))) +
          h (F.incl X) = 0 := by rw [h1]; abel
      calc (2 : K) • F.incl (F.coords (h (F.incl X))) =
          (h (F.incl X) + h (F.incl X)) -
            (h (F.incl X) - (2 : K) • F.incl (F.coords (h (F.incl X))) + h (F.incl X)) := by
            abel
        _ = h (F.incl X) + h (F.incl X) := by rw [h1']; abel
        _ = (2 : K) • h (F.incl X) := by rw [two_smul K]
    have h3 : F.incl (F.coords (h (F.incl X))) = h (F.incl X) :=
      (smul_right_inj h2).mp h2'
    rw [hTapply]
    exact h3.symm
  obtain ⟨i, j, hiQ, hjQ, hii, hjj, hanti⟩ := frame_exists_quat_pair hodd Q₁
  have hTleft : ∀ (A : SL(2, K)), A ∈ (Q₁ : Subgroup SL(2, K)) → ∀ X,
      T ((A : Matrix (Fin 2) (Fin 2) K) * X) = (A : Matrix (Fin 2) (Fin 2) K) * T X := by
    intro A hA X
    have hcomm : h (F.La A (F.incl X)) = F.La A (h (F.incl X)) := by
      rw [← LinearEquiv.mul_apply, h₁ A hA, LinearEquiv.mul_apply]
    have hLaX : F.incl ((A : Matrix (Fin 2) (Fin 2) K) * X) = F.La A (F.incl X) :=
      (F.La_apply_incl A X).symm
    rw [hTapply]
    rw [hLaX, hcomm, hincl, F.La_apply_incl, F.coords_incl]
  have hTC : ∀ X, T X = X * T 1 :=
    frame_eq_mulRight_of_commute_pair h2 hii hjj hanti T (hTleft i hiQ) (hTleft j hjQ)
  have hTright : ∀ B ∈ (Q₂ : Subgroup SL(2, K)), ∀ X,
      T (X * sigmaLin (B : Matrix (Fin 2) (Fin 2) K)) =
        T X * sigmaLin (B : Matrix (Fin 2) (Fin 2) K) := by
    intro B hB X
    have hmb : ∀ Y : Matrix (Fin 2) (Fin 2) K,
        F.embLin (LinearMap.mulRight K (sigmaLin (B : Matrix (Fin 2) (Fin 2) K))) (F.incl Y) =
          F.incl (Y * sigmaLin (B : Matrix (Fin 2) (Fin 2) K)) := by
      intro Y
      rw [F.embLin_apply_eq, F.coords_incl, sub_self, add_zero, LinearMap.mulRight_apply]
    have hcomm : h (F.swap.La B (F.incl X)) = F.swap.La B (h (F.incl X)) := by
      rw [← LinearEquiv.mul_apply, h₂ B hB, LinearEquiv.mul_apply]
    have hsw : F.swap.La B (F.incl X) =
        F.incl (X * sigmaLin (B : Matrix (Fin 2) (Fin 2) K)) := by
      rw [F.La_swap_apply, hmb]
    rw [hTapply, ← hsw, hcomm, hincl, F.La_swap_apply, hmb, F.coords_incl]
  have hCcomm : ∀ B ∈ (Q₂ : Subgroup SL(2, K)),
      sigmaLin (B : Matrix (Fin 2) (Fin 2) K) * T 1 =
        T 1 * sigmaLin (B : Matrix (Fin 2) (Fin 2) K) := by
    intro B hB
    have hkey := hTright B hB 1
    rw [Matrix.one_mul, hTC] at hkey
    exact hkey
  have hMcomm : ∀ B ∈ (Q₂ : Subgroup SL(2, K)),
      sigmaLin (T 1) * (B : Matrix (Fin 2) (Fin 2) K) =
        (B : Matrix (Fin 2) (Fin 2) K) * sigmaLin (T 1) := by
    intro B hB
    have hkey := congrArg sigmaLin (hCcomm B hB)
    rw [sigmaLin_mul, sigmaLin_mul, sigmaLin_sigmaLin] at hkey
    exact hkey
  obtain ⟨c, hc⟩ :=
    CFSG.ComponentClassification.HarrisLit.T1.eq_smul_one_of_commute_sylow_sl2 hodd Q₂ hMcomm
  have hC : T 1 = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have hkey := congrArg sigmaLin hc
    rw [map_smul] at hkey
    have hone : sigmaLin (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]
    rw [hone, sigmaLin_sigmaLin] at hkey
    exact hkey
  have hscale : ∀ X, h (F.incl X) = c • F.incl X := by
    intro X
    rw [hincl, hTC, hC, Matrix.mul_smul, Matrix.mul_one, LinearMap.map_smul]
  have hQ1 : Q (F.incl (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
    rw [F.Q_incl, Matrix.det_one]
  have hc2 : c ^ 2 = 1 := by
    have hkey := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO) (F.incl 1)
    rw [hscale, QuadraticMap.map_smul, hQ1, smul_eq_mul, mul_one] at hkey
    rw [pow_two]
    exact hkey
  have hpow : ∀ n : ℕ, (h ^ n) (F.incl 1) = (c ^ n) • F.incl 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hscale, smul_smul, ← pow_succ]
  have hincl1 : F.incl (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro h0
    have hkey := congrArg F.coords h0
    rw [F.coords_incl, map_zero] at hkey
    exact one_ne_zero hkey
  have hcn : c ^ orderOf h = 1 := by
    have hkey := hpow (orderOf h)
    rw [pow_orderOf_eq_one] at hkey
    rw [show (1 : V ≃ₗ[K] V) (F.incl 1) = F.incl 1 from rfl] at hkey
    have h' : (c ^ orderOf h) • F.incl 1 = (1 : K) • F.incl 1 := by
      rw [one_smul]
      exact hkey.symm
    exact (smul_left_inj hincl1).mp h'
  have hc1 : c = 1 := by
    have hdvd2 : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hc2
    have hdvdn : orderOf c ∣ orderOf h := orderOf_dvd_iff_pow_eq_one.mpr hcn
    have hcop : Nat.Coprime 2 (orderOf h) := Nat.coprime_two_left.mpr hh
    have h1 : orderOf c ∣ Nat.gcd 2 (orderOf h) := Nat.dvd_gcd hdvd2 hdvdn
    rw [hcop.gcd_eq_one, Nat.dvd_one] at h1
    exact orderOf_eq_one_iff.mp h1
  intro x hx
  rw [F.mem_span_iff] at hx
  rw [hx, hincl, hTC, hC, hc1]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
