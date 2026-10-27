module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
public import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofPerm
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofFrame
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofEven
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan430L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec15.KSL3Two
open Matrix Res417Frame Res424Six

variable {K : Type} [Field K]

@[expose] def diagRatio (M : Matrix (Fin 3) (Fin 3) K) : K × K :=
  (M 1 1 / M 0 0, M 2 2 / M 0 0)

theorem diagRatio_smul (M : Matrix (Fin 3) (Fin 3) K) {μ : K} (hμ : μ ≠ 0) :
    diagRatio (μ • M) = diagRatio M := by
  simp only [diagRatio, Matrix.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hμ, mul_div_mul_left _ _ hμ]

theorem diagRatio_mul_scalar (M : GL (Fin 3) K) (μ : Kˣ) :
    diagRatio ((M * GeneralLinearGroup.scalar (Fin 3) μ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagRatio (M : Matrix (Fin 3) (Fin 3) K) := by
  rw [Units.val_mul, coe_scalar_eq_smul, Matrix.mul_smul, Matrix.mul_one]
  exact diagRatio_smul _ μ.ne_zero

theorem diagRatio_mul {M N : Matrix (Fin 3) (Fin 3) K} (hM : M.IsDiag) (hN : N.IsDiag) :
    diagRatio (M * N) = diagRatio M * diagRatio N := by
  rw [← hM.diagonal_diag, ← hN.diagonal_diag, Matrix.diagonal_mul_diagonal]
  simp only [diagRatio, Matrix.diagonal_apply_eq, Prod.mk_mul_mk]
  rw [mul_div_mul_comm, mul_div_mul_comm]

theorem eq_smul_one_of_diagRatio {M : Matrix (Fin 3) (Fin 3) K} (hM : M.IsDiag)
    (hM0 : M 0 0 ≠ 0) (h : diagRatio M = 1) : M = M 0 0 • 1 := by
  have h1 : M 1 1 = M 0 0 := by
    have := congrArg Prod.fst h
    simp only [diagRatio, Prod.fst_one] at this
    exact (div_eq_one_iff_eq hM0).mp this
  have h2 : M 2 2 = M 0 0 := by
    have := congrArg Prod.snd h
    simp only [diagRatio, Prod.snd_one] at this
    exact (div_eq_one_iff_eq hM0).mp this
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    fin_cases i
    · rfl
    · exact h1
    · exact h2
  · rw [hM hij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]

theorem permGL_conj_diagonal (σ : Equiv.Perm (Fin 3)) {D : GL (Fin 3) K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ((permGL σ * D * (permGL σ)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => (D : Matrix (Fin 3) (Fin 3) K) (σ⁻¹ i) (σ⁻¹ i) := by
  rw [Units.val_mul, Units.val_mul, ← hD.diagonal_diag, permGL_mul_diagonal, Matrix.mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  congr 1
  funext i
  rw [Matrix.diagonal_apply_eq, Matrix.diag_apply]

theorem diagRatio_finRotate {d : Fin 3 → K} (hd0 : d 0 ≠ 0) :
    diagRatio (diagonal fun i => d ((finRotate 3)⁻¹ i)) =
      ((diagRatio (diagonal d)).2⁻¹,
        (diagRatio (diagonal d)).1 * (diagRatio (diagonal d)).2⁻¹) := by
  have e0 : (finRotate 3)⁻¹ (0 : Fin 3) = 2 := by decide
  have e1 : (finRotate 3)⁻¹ (1 : Fin 3) = 0 := by decide
  have e2 : (finRotate 3)⁻¹ (2 : Fin 3) = 1 := by decide
  simp only [diagRatio, Matrix.diagonal_apply_eq, e0, e1, e2, inv_div]
  exact Prod.ext rfl (div_mul_div_cancel₀ hd0).symm

theorem diagRatio_swap {d : Fin 3 → K} (hd0 : d 0 ≠ 0) :
    diagRatio (diagonal fun i => d ((Equiv.swap (0 : Fin 3) 1)⁻¹ i)) =
      ((diagRatio (diagonal d)).1⁻¹,
        (diagRatio (diagonal d)).2 * (diagRatio (diagonal d)).1⁻¹) := by
  have e0 : (Equiv.swap (0 : Fin 3) 1)⁻¹ (0 : Fin 3) = 1 := by decide
  have e1 : (Equiv.swap (0 : Fin 3) 1)⁻¹ (1 : Fin 3) = 0 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 1)⁻¹ (2 : Fin 3) = 2 := by decide
  simp only [diagRatio, Matrix.diagonal_apply_eq, e0, e1, e2, inv_div]
  exact Prod.ext rfl (div_mul_div_cancel₀ hd0).symm

section SL

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} [hLn : L.Normal] {p f : ℕ} {π : Bool}

theorem exists_mem_of_frame (hK : PiField π p f K) (e : L ≃* slPi π 3 (p ^ f) K)
    {A : Subgroup H} (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) {g : GL (Fin 3) K}
    (hdiag : ∀ a ∈ A, ∀ y, IsPGLAt e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (hcube : ∀ a ∈ A, ∀ y, IsPGLAt e a y → ∀ i j,
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ 3 =
        ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j ^ 3)
    (σ : Equiv.Perm (Fin 3)) {Q : GL (Fin 3) K}
    (hQc : ∀ D : GL (Fin 3) K, Q * D * Q⁻¹ = permGL σ * D * (permGL σ)⁻¹)
    (hQ : g * Q * g⁻¹ ∈ slPi π 3 (p ^ f) K) :
    ∃ n ∈ L, n ∈ Subgroup.normalizer (A : Set H) ∧
      ∀ a ∈ A, ∀ y, IsPGLAt e a y → ∃ y', IsPGLAt e (n * a * n⁻¹) y' ∧
        g⁻¹ * y' * g = permGL σ * (g⁻¹ * y * g) * (permGL σ)⁻¹ := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hψmul : ∀ X Y : GL (Fin 3) K, g⁻¹ * (X * Y) * g = (g⁻¹ * X * g) * (g⁻¹ * Y * g) :=
    fun X Y => by group
  have hψinj : ∀ X Y : GL (Fin 3) K, g⁻¹ * X * g = g⁻¹ * Y * g → X = Y := fun X Y h => by
    have := congrArg (fun Z => g * Z * g⁻¹) h
    simpa [mul_assoc] using this
  have hcent : ∀ m (hm : m ∈ L),
      ((g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag → ∀ a ∈ A, a * m = m * a := by
    intro m hm hmD a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have hmL : a * m * a⁻¹ ∈ L := hLn.conj_mem m hm a
    have h1 := coe_e_conj_of_isPGLAt hy hm hmL
    have h2 : y * (e ⟨m, hm⟩ : GL (Fin 3) K) * y⁻¹ = (e ⟨m, hm⟩ : GL (Fin 3) K) := by
      apply hψinj
      have hc := commute_of_isDiag (hdiag a ha y hy) hmD
      have hc' : (g⁻¹ * y * g) * (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) =
          (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) * (g⁻¹ * y * g) := Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact hc)
      calc g⁻¹ * (y * (e ⟨m, hm⟩ : GL (Fin 3) K) * y⁻¹) * g =
            (g⁻¹ * y * g) * (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) * (g⁻¹ * y * g)⁻¹ := by
              group
        _ = g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g := by rw [hc']; group
    rw [h2] at h1
    have h3 : (⟨a * m * a⁻¹, hmL⟩ : L) = ⟨m, hm⟩ := e.injective (Subtype.ext h1)
    have h4 : a * m * a⁻¹ = m := congrArg Subtype.val h3
    calc a * m = a * m * a⁻¹ * a := by group
      _ = m * a := by rw [h4]
  set n : H := (e.symm ⟨g * Q * g⁻¹, hQ⟩ : H) with hndef
  have hnL : n ∈ L := (e.symm _).2
  have hen : ((e ⟨n, hnL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = g * Q * g⁻¹ := by
    have : (⟨n, hnL⟩ : L) = e.symm ⟨g * Q * g⁻¹, hQ⟩ := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hψn : ∀ D : GL (Fin 3) K, g⁻¹ * (((e ⟨n, hnL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) *
      (g * D * g⁻¹) * ((e ⟨n, hnL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)⁻¹) * g =
        permGL σ * D * (permGL σ)⁻¹ := by
    intro D
    rw [hen, ← hQc D]
    group
  have hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
    intro a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have ht'L : a * n⁻¹ * a⁻¹ ∈ L := hLn.conj_mem _ (L.inv_mem hnL) a
    have hmL : n * (a * n⁻¹ * a⁻¹) ∈ L := L.mul_mem hnL ht'L
    have hem : ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        (e ⟨n, hnL⟩ : GL (Fin 3) K) * y * (e ⟨n, hnL⟩ : GL (Fin 3) K)⁻¹ * y⁻¹ := by
      have e1 : (⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : L) =
          ⟨n, hnL⟩ * ⟨a * n⁻¹ * a⁻¹, ht'L⟩ := rfl
      rw [e1, map_mul, Subgroup.coe_mul, coe_e_conj_of_isPGLAt hy (L.inv_mem hnL) ht'L]
      have e2 : (⟨n⁻¹, L.inv_mem hnL⟩ : L) = (⟨n, hnL⟩ : L)⁻¹ := rfl
      rw [e2, map_inv, Subgroup.coe_inv]
      group
    have hψm : g⁻¹ * ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) :
        GL (Fin 3) K) * g =
        permGL σ * (g⁻¹ * y * g) * (permGL σ)⁻¹ * (g⁻¹ * y * g)⁻¹ := by
      have := hψn (g⁻¹ * y * g)
      rw [hem]
      calc g⁻¹ * ((e ⟨n, hnL⟩ : GL (Fin 3) K) * y * (e ⟨n, hnL⟩ : GL (Fin 3) K)⁻¹ * y⁻¹) * g =
          (g⁻¹ * ((e ⟨n, hnL⟩ : GL (Fin 3) K) * (g * (g⁻¹ * y * g) * g⁻¹) *
            (e ⟨n, hnL⟩ : GL (Fin 3) K)⁻¹) * g) * (g⁻¹ * y * g)⁻¹ := by group
        _ = _ := by rw [this]
    obtain ⟨hmD, hm3⟩ := commutator_permGL σ (hdiag a ha y hy) (hcube a ha y hy)
    rw [← hψm] at hmD hm3
    have hmA : n * (a * n⁻¹ * a⁻¹) ∈ A := by
      refine mem_of_maximal_of_commute hA ?_ fun a' ha' => hcent _ hmL hmD a' ha'
      have h1 : ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) :
          GL (Fin 3) K) ^ 3 = 1 := by
        have e1 : (g⁻¹ * ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) :
            GL (Fin 3) K) * g) ^ 3 = g⁻¹ * ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ :
              slPi π 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 * g := by
          simp only [pow_succ, pow_zero, one_mul]
          group
        rw [e1] at hm3
        calc ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 =
            g * (g⁻¹ * ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) :
              GL (Fin 3) K) ^ 3 * g) * g⁻¹ := by group
          _ = 1 := by rw [hm3]; group
      have h2' : (e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, h1]; rfl)
      rw [← map_pow, map_eq_one_iff _ e.injective] at h2'
      exact congrArg Subtype.val h2'
    have : n * a * n⁻¹ = (n * (a * n⁻¹ * a⁻¹)) * a := by group
    rw [this]
    exact A.mul_mem hmA ha
  refine ⟨n, hnL, mem_normalizer_of_conj_mem hnA, fun a ha y hy => ?_⟩
  have hninv : ((e ⟨n⁻¹, L.inv_mem hnL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      ((e ⟨n, hnL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)⁻¹ := by
    have e2 : (⟨n⁻¹, L.inv_mem hnL⟩ : L) = (⟨n, hnL⟩ : L)⁻¹ := rfl
    rw [e2, map_inv, Subgroup.coe_inv]
  have hlift := isPGLAt_mul e (isPGLAt_mul e (isPGLAt_of_mem e hπ hnL) hy)
    (isPGLAt_of_mem e hπ (L.inv_mem hnL))
  rw [hninv] at hlift
  refine ⟨_, hlift, ?_⟩
  have := hψn (g⁻¹ * y * g)
  calc g⁻¹ * ((e ⟨n, hnL⟩ : GL (Fin 3) K) * y * (e ⟨n, hnL⟩ : GL (Fin 3) K)⁻¹) * g =
      g⁻¹ * ((e ⟨n, hnL⟩ : GL (Fin 3) K) * (g * (g⁻¹ * y * g) * g⁻¹) *
        (e ⟨n, hnL⟩ : GL (Fin 3) K)⁻¹) * g := by group
    _ = _ := this


theorem exists_ratio_of_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup H} (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y)
    {g : GL (Fin 3) K}
    (hdiag : ∀ a ∈ A, ∀ y, IsPGLAt e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ∃ r : H → K × K, (∀ x ∈ A, ∀ y, IsPGLAt e x y →
        r x = diagRatio ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ∧
      (1 ∈ A → r 1 = 1) ∧ (∀ x ∈ A, ∀ y ∈ A, r (x * y) = r x * r y) ∧
      ∀ x ∈ A, r x = 1 → x ∈ Subgroup.centralizer (L : Set H) := by
  classical
  have hsc : ∀ (u : Kˣ) (X : GL (Fin 3) K),
      GeneralLinearGroup.scalar (Fin 3) u * X = X * GeneralLinearGroup.scalar (Fin 3) u :=
    fun u X => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u X).eq.symm
  let r : H → K × K := fun x => if hx : x ∈ A then
    diagRatio ((g⁻¹ * (hpgl x hx).choose * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) else 1
  have hr : ∀ x ∈ A, ∀ y, IsPGLAt e x y →
      r x = diagRatio ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro x hx y hy
    have hr' : r x = diagRatio ((g⁻¹ * (hpgl x hx).choose * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := dif_pos hx
    rw [hr']
    obtain ⟨μ, hμ⟩ := isPGLAt_inv_mul_mem hK hq (hpgl x hx).choose_spec hy
    have hyμ : y = (hpgl x hx).choose * GeneralLinearGroup.scalar (Fin 3) μ := by rw [hμ]; group
    have : g⁻¹ * y * g = g⁻¹ * (hpgl x hx).choose * g * GeneralLinearGroup.scalar (Fin 3) μ := by
      rw [hyμ, mul_assoc g⁻¹, mul_assoc, hsc μ g, ← mul_assoc, ← mul_assoc]
    rw [this, diagRatio_mul_scalar]
  refine ⟨r, hr, fun h1 => ?_, fun x hx x' hx' => ?_, fun x hx hx1 => ?_⟩
  · rw [hr 1 h1 1 (isPGLAt_of_mem_centralizer e (Subgroup.one_mem _)), mul_one, inv_mul_cancel,
      Units.val_one]
    simp [diagRatio]
  · obtain ⟨y, hy⟩ := hpgl x hx
    obtain ⟨y', hy'⟩ := hpgl x' hx'
    rw [hr _ (A.mul_mem hx hx') _ (isPGLAt_mul e hy hy'), hr x hx y hy, hr x' hx' y' hy']
    have : g⁻¹ * (y * y') * g = (g⁻¹ * y * g) * (g⁻¹ * y' * g) := by group
    rw [this, Units.val_mul]
    exact diagRatio_mul (hdiag x hx y hy) (hdiag x' hx' y' hy')
  · obtain ⟨y, hy⟩ := hpgl x hx
    rw [hr x hx y hy] at hx1
    have hD := hdiag x hx y hy
    have hD0 := apply_self_ne_zero_of_isDiag hD 0
    have h1 := eq_smul_one_of_diagRatio hD hD0 hx1
    apply mem_centralizer_of_isPGLAt_scalar hy
    refine ⟨Units.mk0 _ hD0, ?_⟩
    have h2 : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hD0) :=
      Units.ext (by rw [coe_scalar_eq_smul, Units.val_mk0]; exact h1)
    calc GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hD0) =
        g * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hD0) * g⁻¹ := by
          rw [← hsc, mul_inv_cancel_right]
      _ = y := by rw [← h2]; group

theorem exists_theta_of_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup H} {c : H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hc3 : orderOf c = 3) (hAc : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) {b : H} (hbA : b ∈ A) (hbL : b ∈ L)
    (hbc : b ∉ Subgroup.zpowers c) :
    ∃ P ∈ L, ∃ T ∈ L, P ∈ Subgroup.normalizer (A : Set H) ∧
      T ∈ Subgroup.normalizer (A : Set H) ∧ ∃ r : H → K × K, r 1 = 1 ∧
        (∀ x ∈ A, ∀ y ∈ A, r (x * y) = r x * r y) ∧
        (∀ x ∈ A, r x = 1 → x ∈ Subgroup.zpowers c) ∧
        (∀ x ∈ A, r (P * x * P⁻¹) = ((r x).2⁻¹, (r x).1 * (r x).2⁻¹)) ∧
        (∀ x ∈ A, r (T * x * T⁻¹) = ((r x).1⁻¹, (r x).2 * (r x).1⁻¹)) := by
  classical
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨-, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  set eb : GL (Fin 3) K := (e ⟨b, hbL⟩ : GL (Fin 3) K) with heb
  have hebZ : eb ∉ zPi π 3 (p ^ f) K := by
    intro hz
    apply hbc
    rw [← hLC]
    exact ⟨hbL, mem_centralizer_of_scalar hbL (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)⟩
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have heb3 : orderOf eb = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : eb ^ 3 = 1 := by
      rw [heb, ← Subgroup.coe_pow, ← map_pow]
      have : (⟨b, hbL⟩ : L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hb3]; rfl)
      rw [this, map_one, Subgroup.coe_one]
    refine orderOf_eq_prime h3 fun h1 => hebZ ?_
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨g, hgH, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 (e ⟨b, hbL⟩).2 hebZ heb3
  set d : Fin 3 → K := ![τ, τ ^ 2, 1] with hddef
  have hd : Function.Injective d := Res417Two.injective_diagTau_entries hτ hτ1
  have hψb : ((g⁻¹ * eb * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [hgD, coe_diagTau_eq_diagonal]
  have hψmul : ∀ X Y : GL (Fin 3) K, g⁻¹ * (X * Y) * g = (g⁻¹ * X * g) * (g⁻¹ * Y * g) :=
    fun X Y => by group
  have hdiag : ∀ a ∈ A, ∀ y, IsPGLAt e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro a ha y hy
    apply isDiag_of_commute_diagonal hd
    have hc := isPGLAt_commute_of_mem hbL (hAcomm a ha b hbA) hy
    rw [← hψb, ← Units.val_mul, ← Units.val_mul, ← hψmul, ← hψmul, hc]
  have hcube : ∀ a ∈ A, ∀ y, IsPGLAt e a y → ∀ i j,
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ 3 =
        ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j ^ 3 := by
    intro a ha y hy i j
    obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1
      (pow_three_mem_zPi hK hq (hA.1.2 a ha) hy)
    have h3 : ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        (ℓ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have e1 : (g⁻¹ * y * g) ^ 3 = g⁻¹ * y ^ 3 * g := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [← Units.val_pow_eq_pow_val, e1, ← hℓ,
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ g⁻¹).eq, inv_mul_cancel_right,
        coe_scalar_eq_smul]
    have hD := hdiag a ha y hy
    have hk : ∀ k, ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k ^ 3 = ℓ := by
      intro k
      have := congrFun (congrFun h3 k) k
      rw [← hD.diagonal_diag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at this
      simpa using this
    rw [hk i, hk j]
  have hdetg : ∀ M : GL (Fin 3) K, ((g * M * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (M : Matrix (Fin 3) (Fin 3) K).det := by
    intro M
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  have hσ3 : (finRotate 3) ^ 3 = 1 := by decide
  have hPsl : g * permGL (finRotate 3) * g⁻¹ ∈ slPi π 3 (p ^ f) K := by
    refine (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hgH (permGL_mem_glPi hK _)) (inv_mem hgH), ?_⟩
    rw [hdetg, det_permGL_eq_sign, sign_eq_one_of_pow_three _ hσ3]
    simp
  have hneg : (-1 : GL (Fin 3) K) * permGL (Equiv.swap (0 : Fin 3) 1) ∈ glPi π 3 (p ^ f) K :=
    mul_mem (neg_one_mem_glPi hK) (permGL_mem_glPi hK _)
  have hTsl : g * ((-1 : GL (Fin 3) K) * permGL (Equiv.swap (0 : Fin 3) 1)) * g⁻¹ ∈
      slPi π 3 (p ^ f) K := by
    refine (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hgH hneg) (inv_mem hgH), ?_⟩
    rw [hdetg, Units.val_mul, Matrix.det_mul, det_permGL_eq_sign,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 3) ≠ 1), Units.val_neg, Units.val_one,
      Matrix.det_neg, Fintype.card_fin, Matrix.det_one]
    norm_num
  have hnegc : ∀ D : GL (Fin 3) K, ((-1 : GL (Fin 3) K) * permGL (Equiv.swap (0 : Fin 3) 1)) * D *
      ((-1 : GL (Fin 3) K) * permGL (Equiv.swap (0 : Fin 3) 1))⁻¹ =
        permGL (Equiv.swap (0 : Fin 3) 1) * D * (permGL (Equiv.swap (0 : Fin 3) 1))⁻¹ := by
    intro D
    simp [mul_assoc]
  obtain ⟨P, hPL, hPN, hPy⟩ := exists_mem_of_frame hK e hA hpgl hdiag hcube (finRotate 3)
    (fun D => rfl) hPsl
  obtain ⟨T, hTL, hTN, hTy⟩ := exists_mem_of_frame hK e hA hpgl hdiag hcube
    (Equiv.swap (0 : Fin 3) 1) hnegc hTsl
  obtain ⟨r, hr, hr1, hrmul, hrker⟩ := exists_ratio_of_frame hK hq e hpgl hdiag
  have hconjA : ∀ {n : H}, n ∈ Subgroup.normalizer (A : Set H) → ∀ x ∈ A, n * x * n⁻¹ ∈ A :=
    fun {n} hn x hx => (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  refine ⟨P, hPL, T, hTL, hPN, hTN, r, hr1 (Subgroup.one_mem _), hrmul,
    fun x hx hx1 => hAc ▸ ⟨hx, hrker x hx hx1⟩, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := hpgl x hx
    obtain ⟨y', hy', hyy'⟩ := hPy x hx y hy
    have hD := hdiag x hx y hy
    rw [hr _ (hconjA hPN x hx) y' hy', hyy', permGL_conj_diagonal _ hD, hr x hx y hy]
    have hDd := hD.diagonal_diag.symm
    conv_rhs => rw [hDd]
    exact diagRatio_finRotate (d := fun j => ((g⁻¹ * y * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) j j) (apply_self_ne_zero_of_isDiag hD 0)
  · obtain ⟨y, hy⟩ := hpgl x hx
    obtain ⟨y', hy', hyy'⟩ := hTy x hx y hy
    have hD := hdiag x hx y hy
    rw [hr _ (hconjA hTN x hx) y' hy', hyy', permGL_conj_diagonal _ hD, hr x hx y hy]
    have hDd := hD.diagonal_diag.symm
    conv_rhs => rw [hDd]
    exact diagRatio_swap (d := fun j => ((g⁻¹ * y * g : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) j j) (apply_self_ne_zero_of_isDiag hD 0)

end SL

end CFSG.RankThree.PartTwo.Sec4.Ronan430L3
