module

public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux5
import CFSG.RankThree.PartOne.KF.BloomAut
import CFSG.LieType.Steinberg.CentralExt.SUThree

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem exists_outer_order_three_of_u62 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (π : X →* Y) (ψ₀ : Su K 2 1 6 →* Y) (σ : MulAut X) (τ : MulAut Y) (g : GL (Fin 6) K)
    (hX : Group.IsPerfect X) (hπ : Function.Surjective π)
    (hπZ : ∀ x ∈ π.ker, ∀ x' : X, x' * x = x * x') (hψ : Function.Surjective ψ₀)
    (hψZ : ψ₀.ker ≤ Subgroup.center (Su K 2 1 6)) (hστ : ∀ x, π (σ x) = τ (π x))
    (hg : ggIsUnitaryMat (p := 2) (f := 1) g) (hdet : Matrix.GeneralLinearGroup.det g ≠ 1)
    (hτ : ∀ s : Su K 2 1 6, ∃ y : Su K 2 1 6,
      (y : GL (Fin 6) K) = g * (s : GL (Fin 6) K) * g⁻¹ ∧ τ (ψ₀ s) = ψ₀ y) :
    ∃ α : MulAut X, α ^ 3 = 1 ∧ α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X ∧
      ∀ z ∈ Subgroup.center X, α z = σ z := by
  classical
  let c : Kˣ := Matrix.GeneralLinearGroup.det g
  have hc3 : c ^ 3 = 1 := by
    have hcard : Nat.card Kˣ = 3 := by
      rw [Nat.card_units, hK]
      norm_num
    have h := pow_card_eq_one' (G := Kˣ) (x := c)
    rwa [hcard] at h
  have hc3K : (c : K) ^ 3 = 1 := by
    have h := congrArg Units.val hc3
    simpa using h
  let d : Fin 6 → Kˣ := ![c, 1, 1, 1, 1, 1]
  let g₀ : GL (Fin 6) K := TauCeti.diagGL d
  have hg₀3 : g₀ ^ 3 = 1 := by
    rw [show g₀ = TauCeti.diagGL d from rfl, ← map_pow]
    have hd3 : d ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [d, hc3]
    rw [hd3, map_one]
  have hcoe : (g₀ : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal (fun i => (d i : K)) := by
    ext i j
    rw [TauCeti.diagGL_apply, Matrix.diagonal_apply]
  have hg₀U : ggIsUnitaryMat (p := 2) (f := 1) g₀ := by
    unfold ggIsUnitaryMat
    rw [hcoe, CFSG.LieType.Steinberg.conjTr_diagonal]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    fin_cases i <;> simp [d, frobenius_def]
    have hc3K2 : (c : K) ^ 2 * (c : K) = 1 := by
      rw [← pow_succ]
      exact hc3K
    simpa using hc3K2
  have hg₀det : Matrix.GeneralLinearGroup.det g₀ = c := by
    rw [show g₀ = TauCeti.diagGL d from rfl, TauCeti.det_diagGL]
    simp [d, Fin.prod_univ_six]
  have hs₀U : ggIsUnitaryMat (p := 2) (f := 1) (g₀⁻¹ * g) :=
    ggNSPosPA_ggIsUnitaryMat_mul (ggNSPosPA_ggIsUnitaryMat_inv hg₀U) hg
  have hs₀det : ((g₀⁻¹ * g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
    have h : Matrix.GeneralLinearGroup.det (g₀⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hg₀det]
      exact inv_mul_cancel c
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Units.val h
  let s₀ : Su K 2 1 6 := ⟨g₀⁻¹ * g, mem_SUid.mpr ⟨hs₀det, hs₀U⟩⟩
  obtain ⟨x₀, hx₀⟩ := hπ (ψ₀ s₀)
  let α : MulAut X := σ * (MulAut.conj x₀)⁻¹
  have hαπ : ∀ (x : X) (t : Su K 2 1 6), π x = ψ₀ t →
      π (α x) = ψ₀ ⟨g₀ * (t : GL (Fin 6) K) * g₀⁻¹,
        InnerDiagSU.conj_mem_SUid hg₀U t.2⟩ := by
    intro x t hxt
    have hαx : α x = σ (x₀⁻¹ * x * x₀) := by
      simp only [α, MulAut.mul_apply, MulAut.conj_inv_apply]
    rw [hαx, hστ]
    have hπ_conj : π (x₀⁻¹ * x * x₀) = ψ₀ (s₀⁻¹ * t * s₀) := by
      rw [map_mul, map_mul, map_inv, hx₀, hxt]
      simp only [← map_mul, ← map_inv]
    rw [hπ_conj]
    obtain ⟨y, hy, hτy⟩ := hτ (s₀⁻¹ * t * s₀)
    let t' : Su K 2 1 6 := ⟨g₀ * (t : GL (Fin 6) K) * g₀⁻¹, InnerDiagSU.conj_mem_SUid hg₀U t.2⟩
    have hy_eq : y = t' := by
      apply Subtype.ext
      rw [hy]
      change g * ((s₀ : GL (Fin 6) K)⁻¹ * (t : GL (Fin 6) K) * (s₀ : GL (Fin 6) K)) * g⁻¹ =
        (t' : GL (Fin 6) K)
      rw [show (s₀ : GL (Fin 6) K) = g₀⁻¹ * g from rfl]
      rw [show (t' : GL (Fin 6) K) = g₀ * (t : GL (Fin 6) K) * g₀⁻¹ from rfl]
      group
    rw [hτy, hy_eq]
  have hg₀_unitary_pow : ∀ n : ℕ, ggIsUnitaryMat (p := 2) (f := 1) (g₀ ^ n) := by
    intro n
    induction n with
    | zero =>
      show ggIsUnitaryMat (p := 2) (f := 1) (1 : GL (Fin 6) K)
      unfold ggIsUnitaryMat
      rw [Units.val_one, conjTr_one, Matrix.mul_one]
    | succ n ih =>
      rw [pow_succ]
      exact ggNSPosPA_ggIsUnitaryMat_mul ih hg₀U
  have hiter : ∀ (n : ℕ) (x : X) (t : Su K 2 1 6), π x = ψ₀ t →
      ∃ t' : Su K 2 1 6, (t' : GL (Fin 6) K) = (g₀ ^ n) * (t : GL (Fin 6) K) * (g₀ ^ n)⁻¹ ∧
        π ((α ^ n) x) = ψ₀ t' := by
    intro n
    induction n with
    | zero =>
      intro x t hxt
      exact ⟨t, by simp, hxt⟩
    | succ n ih =>
      intro x t hxt
      obtain ⟨t', ht'_val, ht'_π⟩ := ih x t hxt
      have hαπ_n := hαπ ((α ^ n) x) t' ht'_π
      refine ⟨⟨g₀ * (t' : GL (Fin 6) K) * g₀⁻¹, InnerDiagSU.conj_mem_SUid hg₀U t'.2⟩,
        ?_, ?_⟩
      · show g₀ * (t' : GL (Fin 6) K) * g₀⁻¹ =
          g₀ ^ (n + 1) * (t : GL (Fin 6) K) * (g₀ ^ (n + 1))⁻¹
        rw [ht'_val, pow_succ]
        group
      · rw [pow_succ']
        change π (α ((α ^ n) x)) = _
        exact hαπ_n
  have hα3_π : ∀ x : X, π ((α ^ 3) x) = π x := by
    intro x
    obtain ⟨t, ht⟩ := hψ (π x)
    obtain ⟨t', ht'_val, ht'_π⟩ := hiter 3 x t ht.symm
    rw [ht'_π]
    have ht'_eq : t' = t := by
      apply Subtype.ext
      rw [ht'_val, hg₀3]
      simp
    rw [ht'_eq]
    exact ht
  have hα3 : α ^ 3 = 1 := by
    have : Group.IsPerfect X := hX
    apply CFSG.RankThree.PartOne.KFBloom.aut_eq_one_of_central_perfect
    intro x
    rw [Subgroup.mem_center_iff]
    intro y
    have hmem : x⁻¹ * (α ^ 3) x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα3_π x, inv_mul_cancel]
    exact hπZ _ hmem y
  have hαZ : ∀ z ∈ Subgroup.center X, α z = σ z := by
    intro z hz
    have hαz : α z = σ (x₀⁻¹ * z * x₀) := by
      simp only [α, MulAut.mul_apply, MulAut.conj_inv_apply]
    rw [hαz]
    have hz_comm : x₀⁻¹ * z * x₀ = z := by
      rw [Subgroup.mem_center_iff] at hz
      calc x₀⁻¹ * z * x₀ = (z * x₀⁻¹) * x₀ := by rw [hz x₀⁻¹]
        _ = z * (x₀⁻¹ * x₀) := by group
        _ = z := by simp
    rw [hz_comm]
  have hα_not_inner : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    intro hin
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.mem_range] at hin
    obtain ⟨x₁, hx₁⟩ := hin
    obtain ⟨s₁, hs₁⟩ := hψ (π x₁)
    have hs₁U : ggIsUnitaryMat (p := 2) (f := 1) (s₁ : GL (Fin 6) K) := (mem_SUid.mp s₁.2).2
    have h_eq : ∀ t : Su K 2 1 6,
        ψ₀ ⟨g₀ * (t : GL (Fin 6) K) * g₀⁻¹, InnerDiagSU.conj_mem_SUid hg₀U t.2⟩ =
        ψ₀ ⟨s₁ * (t : GL (Fin 6) K) * s₁⁻¹, InnerDiagSU.conj_mem_SUid hs₁U t.2⟩ := by
      intro t
      obtain ⟨x, hx⟩ := hπ (ψ₀ t)
      have h1 := hαπ x t hx
      have h2 : π (α x) = ψ₀ ⟨s₁ * (t : GL (Fin 6) K) * s₁⁻¹,
          InnerDiagSU.conj_mem_SUid hs₁U t.2⟩ := by
        have hαx₁ : α x = x₁ * x * x₁⁻¹ := by
          rw [← hx₁]
          rw [MulAut.conj_apply]
        rw [hαx₁, map_mul, map_mul, map_inv, ← hs₁, hx]
        rw [show (⟨s₁ * (t : GL (Fin 6) K) * s₁⁻¹,
          InnerDiagSU.conj_mem_SUid hs₁U t.2⟩ : Su K 2 1 6) = s₁ * t * s₁⁻¹ from
          Subtype.ext rfl]
        rw [map_mul, map_mul, map_inv]
      rw [h1] at h2
      exact h2
    let N : GL (Fin 6) K := (s₁ : GL (Fin 6) K)⁻¹ * g₀
    have hN_unit : ggIsUnitaryMat (p := 2) (f := 1) N :=
      ggNSPosPA_ggIsUnitaryMat_mul (ggNSPosPA_ggIsUnitaryMat_inv hs₁U) hg₀U
    have hN_conj : ∀ t : Su K 2 1 6,
        ψ₀ ⟨N * (t : GL (Fin 6) K) * N⁻¹, InnerDiagSU.conj_mem_SUid hN_unit t.2⟩ = ψ₀ t := by
      intro t
      let u : Su K 2 1 6 := ⟨g₀ * (t : GL (Fin 6) K) * g₀⁻¹, InnerDiagSU.conj_mem_SUid hg₀U t.2⟩
      let v : Su K 2 1 6 := ⟨s₁ * (t : GL (Fin 6) K) * s₁⁻¹, InnerDiagSU.conj_mem_SUid hs₁U t.2⟩
      have h1 : ψ₀ u = ψ₀ v := h_eq t
      let w : Su K 2 1 6 := (s₁⁻¹ : Su K 2 1 6) * u * s₁
      have h_eq_w : (⟨N * (t : GL (Fin 6) K) * N⁻¹,
          InnerDiagSU.conj_mem_SUid hN_unit t.2⟩ : Su K 2 1 6) = w := by
        apply Subtype.ext
        show N * (t : GL (Fin 6) K) * N⁻¹ = (w : GL (Fin 6) K)
        rw [show w = (s₁⁻¹ : Su K 2 1 6) * u * s₁ from rfl]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [show N = (s₁ : GL (Fin 6) K)⁻¹ * g₀ from rfl]
        rw [show ((u : Su K 2 1 6) : GL (Fin 6) K) = g₀ * (t : GL (Fin 6) K) * g₀⁻¹ from rfl]
        group
      rw [h_eq_w]
      have hw : ψ₀ w = (ψ₀ s₁)⁻¹ * ψ₀ u * ψ₀ s₁ := by
        show ψ₀ ((s₁⁻¹ : Su K 2 1 6) * u * s₁) = _
        rw [map_mul, map_mul, map_inv]
      have hv : ψ₀ v = ψ₀ s₁ * ψ₀ t * (ψ₀ s₁)⁻¹ := by
        rw [show v = s₁ * t * s₁⁻¹ from Subtype.ext rfl]
        rw [map_mul, map_mul, map_inv]
      rw [hw, h1, hv]
      group
    obtain ⟨c', hc'⟩ := exists_scalar_of_su_conj_trivial hK (by norm_num) hψZ hN_unit hN_conj
    have hc'_ne : c' ≠ 0 := by
      intro h0
      have hN_zero : (N : Matrix (Fin 6) (Fin 6) K) = 0 := by
        rw [hc']
        ext i j
        simp [Matrix.scalar_apply, h0]
      have hN_det := Matrix.GeneralLinearGroup.det_ne_zero N
      rw [hN_zero] at hN_det
      simp at hN_det
    have hc'3 : c' ^ 3 = 1 := by
      have h := hN_unit
      unfold ggIsUnitaryMat at h
      rw [hc'] at h
      have hconj : conjTr (unitaryInvolution K 2 1) (Matrix.scalar (Fin 6) c') =
          Matrix.scalar (Fin 6) (c' ^ 2) := by
        rw [show Matrix.scalar (Fin 6) c' = Matrix.diagonal (fun _ => c') from rfl]
        rw [show Matrix.scalar (Fin 6) (c' ^ 2) = Matrix.diagonal (fun _ => c' ^ 2) from rfl]
        rw [CFSG.LieType.Steinberg.conjTr_diagonal]
        simp [frobenius_def]
      rw [hconj] at h
      rw [show Matrix.scalar (Fin 6) (c' ^ 2) = Matrix.diagonal (fun _ => c' ^ 2) from rfl] at h
      rw [show Matrix.scalar (Fin 6) c' = Matrix.diagonal (fun _ => c') from rfl] at h
      rw [Matrix.diagonal_mul_diagonal] at h
      have h2 := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M 0 0) h
      simp only [Matrix.diagonal_apply, Matrix.one_apply_eq, if_true] at h2
      rw [← h2, pow_succ]
    have hc_eq : c = 1 := by
      have hN_det1 : Matrix.GeneralLinearGroup.det N = c := by
        rw [show N = (s₁ : GL (Fin 6) K)⁻¹ * g₀ from rfl, map_mul, map_inv, hg₀det]
        have hs₁det : Matrix.GeneralLinearGroup.det (s₁ : GL (Fin 6) K) = 1 := by
          apply Units.ext
          rw [Matrix.GeneralLinearGroup.val_det_apply]
          exact (mem_SUid.mp s₁.2).1
        rw [hs₁det, inv_one, one_mul]
      have hN_det2 : ((N : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = c' ^ 6 := by
        rw [hc']
        show (Matrix.scalar (Fin 6) c').det = c' ^ 6
        rw [show Matrix.scalar (Fin 6) c' = Matrix.diagonal (fun _ => c') from rfl]
        rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hN_det1' : ((N : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = (c : K) := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact congrArg Units.val hN_det1
      rw [hN_det1'] at hN_det2
      have hc'6 : c' ^ 6 = 1 := by
        rw [show 6 = 3 * 2 by norm_num, pow_mul, hc'3, one_pow]
      rw [hc'6] at hN_det2
      exact Units.ext hN_det2
    exact hdet hc_eq
  exact ⟨α, hα3, hα_not_inner, hαZ⟩

end CFSG.StandardType

end
