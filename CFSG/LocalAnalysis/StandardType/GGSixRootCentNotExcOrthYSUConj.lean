module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepair
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepWitt
public import CFSG.LieType.Steinberg.CentralExt.SUOddFieldThreeLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace OrthYSU

private theorem diagonal_mul_wittMat {F : Type} [Field F] {n : ℕ} {γ : F} {a : Fin n → Fˣ}
    (ha : ∀ i, a (Fin.rev i) = a i) :
    Matrix.diagonal (fun i => (a i : F)) * SURep.wittMat n γ =
      SURep.wittMat n γ * Matrix.diagonal (fun i => (a i : F)) := by
  ext r c
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hrc : r = c
  · rw [hrc]
    ring
  · by_cases hrrc : r = Fin.rev c
    · rw [hrrc]
      have h := ha c
      rw [h]
      ring
    · rw [SURep.wittMat_apply, ite_eq_right hrc, ite_eq_right hrrc, add_zero, mul_zero,
        zero_mul]

private theorem diagonal_mul_ggInvUMatrix_one {F : Type} [Field F] {k : ℕ}
    (a : Fin (k + 2) → Fˣ) (h0 : a 0 = a (Fin.last (k + 1))) :
    Matrix.diagonal (fun i => (a i : F)) * ggInvUMatrix (k + 2) 1 F =
      ggInvUMatrix (k + 2) 1 F * Matrix.diagonal (fun i => (a i : F)) := by
  ext r c
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h1 : r = Fin.last (k + 1) ∧ c = 0
  · obtain ⟨rfl, rfl⟩ := h1
    rw [← h0]
    ring
  · by_cases h2 : r = c
    · rw [h2]
      ring
    · have hc : ¬ ((c : ℕ) < 1 ∧ (r : ℕ) + c + 1 = k + 2 ∧ (c : ℕ) < r) := by
        rintro ⟨hc1, hc2, -⟩
        have hc0 : c = 0 := by
          apply Fin.ext
          change (c : ℕ) = 0
          omega
        have hr : r = Fin.last (k + 1) := by
          apply Fin.ext
          have hcval : (c : ℕ) = 0 := by simp [hc0]
          rw [hcval] at hc2
          have hlast : ((Fin.last (k + 1) : Fin (k + 2)) : ℕ) = k + 1 :=
            Fin.val_last _
          omega
        exact h1 ⟨hr, hc0⟩
      rw [ggInvUMatrix, Matrix.add_apply, ggInvUNil_apply, Matrix.one_apply_ne h2,
        ite_eq_right hc, add_zero, mul_zero, zero_mul]

private theorem conjSU_conj_eq_self {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}
    {A : GL (Fin n) F} {h : SU σ n}
    (hA : InnerDiagSU.IsJUnitary σ ((h : GL (Fin n) F) * A * (h : GL (Fin n) F)⁻¹))
    {z : SU σ n} (hz : A * (z : GL (Fin n) F) = (z : GL (Fin n) F) * A) :
    InnerDiagSU.conjSU ((h : GL (Fin n) F) * A * (h : GL (Fin n) F)⁻¹) hA (h * z * h⁻¹) =
      h * z * h⁻¹ := by
  apply Subtype.ext
  simp only [InnerDiagSU.coe_conjSU, Subgroup.coe_mul, Subgroup.coe_inv]
  have hz' : A * (z : GL (Fin n) F) * A⁻¹ = (z : GL (Fin n) F) := by
    rw [hz]
    group
  calc ((h : GL (Fin n) F) * A * (h : GL (Fin n) F)⁻¹) *
        ((h : GL (Fin n) F) * (z : GL (Fin n) F) * (h : GL (Fin n) F)⁻¹) *
        (((h : GL (Fin n) F) * A * (h : GL (Fin n) F)⁻¹))⁻¹
      = (h : GL (Fin n) F) * (A * (z : GL (Fin n) F) * A⁻¹) *
          (h : GL (Fin n) F)⁻¹ := by group
    _ = (h : GL (Fin n) F) * (z : GL (Fin n) F) * (h : GL (Fin n) F)⁻¹ := by rw [hz']

theorem exists_SU_conj_frameDiag {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hm : 1 ≤ m) {Q : GL (Fin (m + 1)) F}
    (hQ : UFusion.IsUFrame (unitaryInvolution F 2 f) Q) (e : Fin (m + 1) → Fˣ)
    (ρ : Equiv.Perm (Fin (m + 1))) (hρ : ∀ i, e (ρ (Fin.rev i)) = e (ρ i)) :
    ∃ g : SU (unitaryInvolution F 2 f) (m + 1),
      (g : GL (Fin (m + 1)) F) * LinFusion.ggFrameDiag Q e * (g : GL (Fin (m + 1)) F)⁻¹ =
        InnerDiagA.diagGL (e ∘ ρ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let n := m + 1
  have hn2 : 2 ≤ n := by omega
  let σ := unitaryInvolution F 2 f
  obtain ⟨γ, hγ⟩ :=
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF).trace_surj 1
      (map_one σ)
  have hγ' : σ γ + γ = 1 := by rw [add_comm]; exact hγ
  let W : Matrix (Fin n) (Fin n) F := SURep.wittMat n γ
  have hW : conjTr σ W * W = antidiag n := SURep.conjTr_wittMat_mul σ hγ'
  have hdetW : W.det ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det hW
    have hmap : (W.map σ).det = σ W.det :=
      (RingHom.map_det (σ : F →+* F) W).symm
    rw [Matrix.det_mul, conjTr, Matrix.det_transpose, hmap, h0, map_zero, zero_mul] at h
    exact det_antidiag_ne_zero n h.symm
  let Wgl : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero W hdetW
  have hWgl : ((Wgl : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = W :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero W hdetW
  let R : GL (Fin n) F := CFSG.RankThree.Classical.permGL ρ
  let Qm : Matrix (Fin n) (Fin n) F := (Q : Matrix (Fin n) (Fin n) F)
  let Qi : Matrix (Fin n) (Fin n) F :=
    ((Q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hQ' : conjTr σ Qm * Qm = antidiag n := hQ
  have hQQi : Qm * Qi = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQiQ : Qi * Qm = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hQJ : conjTr σ Qi * antidiag n * Qi = 1 := by
    rw [← hQ']
    calc conjTr σ Qi * (conjTr σ Qm * Qm) * Qi =
        conjTr σ (Qm * Qi) * (Qm * Qi) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQQi, conjTr_one, Matrix.one_mul]
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf | hf
    · exfalso
      subst hf
      rw [pow_zero, one_pow] at hF
      have h2 : 1 < Nat.card F := Finite.one_lt_card
      omega
    · omega
  have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    { prime := Nat.prime_two
      one_le := hf1
      card := by rw [hF, ← pow_mul, mul_comm] }
  have hRR : conjTr σ (R : Matrix (Fin n) (Fin n) F) * (R : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [SURep.conjTr_eq_bar hUFD]
    exact CFSG.RankThree.Classical2.permGL_unitary hUFD ρ
  let B : GL (Fin n) F := Q⁻¹ * R * Wgl
  have hBmat : ((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Qi * (R : Matrix (Fin n) (Fin n) F) * W := by
    rw [show B = Q⁻¹ * R * Wgl from rfl, Units.val_mul, Units.val_mul, hWgl]
  have hBiso : InnerDiagSU.IsJUnitary σ B := by
    unfold InnerDiagSU.IsJUnitary
    rw [hBmat]
    calc conjTr σ (Qi * (R : Matrix (Fin n) (Fin n) F) * W) * antidiag n *
          (Qi * (R : Matrix (Fin n) (Fin n) F) * W)
        = conjTr σ W * (conjTr σ (R : Matrix (Fin n) (Fin n) F) *
            (conjTr σ Qi * antidiag n * Qi) * (R : Matrix (Fin n) (Fin n) F)) * W := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = antidiag n := by rw [hQJ, Matrix.mul_one, hRR, Matrix.mul_one, hW]
  have hRconj : R⁻¹ * InnerDiagA.diagGL e * R = InnerDiagA.diagGL (e ∘ ρ) := by
    have h := CFSG.RankThree.Classical2.permGL_mul_diagHom_mul_inv (K := F) ρ (e ∘ ρ)
    have hfun : (e ∘ ρ) ∘ ⇑(Equiv.symm ρ) = e := by
      funext i
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [hfun] at h
    have hdiag : ∀ d : Fin n → Fˣ,
        CFSG.SectionRank.OddCover.diagHom n d = InnerDiagA.diagGL d := by
      intro d
      apply Units.ext
      rw [CFSG.SectionRank.OddCover.coe_diagHom, InnerDiagA.coe_diagGL]
    rw [hdiag (e ∘ ρ), hdiag e] at h
    have hR : R * InnerDiagA.diagGL (e ∘ ρ) * R⁻¹ = InnerDiagA.diagGL e := h
    have h' : R⁻¹ * InnerDiagA.diagGL e * R = InnerDiagA.diagGL (e ∘ ρ) := by
      rw [← hR]
      group
    exact h'
  have hWcomm_mat : ((InnerDiagA.diagGL (e ∘ ρ) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) * W =
      W * ((InnerDiagA.diagGL (e ∘ ρ) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) := by
    exact diagonal_mul_wittMat (a := e ∘ ρ) (fun i => hρ i)
  have hWcomm : InnerDiagA.diagGL (e ∘ ρ) * Wgl = Wgl * InnerDiagA.diagGL (e ∘ ρ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hWgl]
    exact hWcomm_mat
  have hXB : B⁻¹ * LinFusion.ggFrameDiag Q e * B = InnerDiagA.diagGL (e ∘ ρ) := by
    rw [show LinFusion.ggFrameDiag Q e = Q⁻¹ * InnerDiagA.diagGL e * Q from rfl,
      show B = Q⁻¹ * R * Wgl from rfl]
    calc (Q⁻¹ * R * Wgl)⁻¹ * (Q⁻¹ * InnerDiagA.diagGL e * Q) * (Q⁻¹ * R * Wgl)
        = Wgl⁻¹ * (R⁻¹ * InnerDiagA.diagGL e * R) * Wgl := by group
      _ = Wgl⁻¹ * InnerDiagA.diagGL (e ∘ ρ) * Wgl := by rw [hRconj]
      _ = InnerDiagA.diagGL (e ∘ ρ) := by
          rw [mul_assoc, hWcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  let d : F := ((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det
  have hdetJ : (antidiag n : Matrix (Fin n) (Fin n) F).det ≠ 0 := det_antidiag_ne_zero n
  have hBiso' : conjTr σ ((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n := hBiso
  have hσd : σ d * d = 1 := by
    have h := congrArg Matrix.det hBiso'
    have hmap : (((B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ).det = σ d :=
      (RingHom.map_det (σ : F →+* F) ((B : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F)).symm
    rw [Matrix.det_mul, Matrix.det_mul, conjTr, Matrix.det_transpose, hmap] at h
    have h' : (σ d * d - 1) * (antidiag n : Matrix (Fin n) (Fin n) F).det = 0 := by
      change σ d * (antidiag n : Matrix (Fin n) (Fin n) F).det * d =
        (antidiag n : Matrix (Fin n) (Fin n) F).det at h
      linear_combination h
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · exact absurd h'' hdetJ
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hσd
    exact zero_ne_one hσd
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' d⁻¹
  have hσμ : σ μ * μ = 1 := by
    refine eq_of_mul_self_eq_mul_self_charTwo ?_
    calc σ μ * μ * (σ μ * μ) = σ (μ * μ) * (μ * μ) := by rw [map_mul]; ring
      _ = σ d⁻¹ * d⁻¹ := by rw [← hμ]
      _ = (σ d * d)⁻¹ := by rw [map_inv₀, mul_inv]
      _ = 1 * 1 := by rw [hσd, inv_one, one_mul]
  set ε : Fin n → F := Pi.mulSingle (⟨0, by omega⟩ : Fin n) μ *
    Pi.mulSingle (Fin.rev (⟨0, by omega⟩ : Fin n)) μ with hε
  have hε_val : ∀ x : Fin n,
      ε x = if (x : ℕ) = 0 ∨ (x : ℕ) = n - 1 then μ else 1 := by
    intro x
    have := x.isLt
    simp only [hε, Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff, Fin.val_rev]
    split_ifs <;> first | (exfalso; omega) | simp
  have hprod : ∏ x, ε x = μ * μ := by
    simp only [hε, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, ite_true]
  have hDiso : conjTr σ (Matrix.diagonal ε) * antidiag n * Matrix.diagonal ε =
      antidiag n := by
    ext a b
    have ha := a.isLt
    rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [antidiag, of_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    split_ifs with hab
    · subst hab
      rw [hε_val, hε_val]
      simp only [Fin.val_rev]
      split_ifs <;> first | (exfalso; omega) | simp [hσμ]
    · rfl
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hσμ
    exact zero_ne_one hσμ
  have hdetD : (Matrix.diagonal ε).det ≠ 0 := by
    rw [Matrix.det_diagonal, hprod, ← hμ]
    exact inv_ne_zero hd0
  let D : GL (Fin n) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ε) hdetD
  have hDgl : InnerDiagSU.IsJUnitary σ D := by
    unfold InnerDiagSU.IsJUnitary
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact hDiso
  have hBDgl : InnerDiagSU.IsJUnitary σ (B * D) := UFusion.isJUnitary_mul hBiso hDgl
  have hBDdet : (((B * D : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_diagonal, hprod, ← hμ,
      mul_inv_cancel₀ hd0]
  have hBDSU : B * D ∈ SU σ n := mem_SU.mpr ⟨hBDdet, hBDgl⟩
  let g : SU σ n := (⟨B * D, hBDSU⟩ : SU σ n)⁻¹
  refine ⟨g, ?_⟩
  have hDcomm : D * InnerDiagA.diagGL (e ∘ ρ) = InnerDiagA.diagGL (e ∘ ρ) * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      InnerDiagA.coe_diagGL, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hDconj : D⁻¹ * InnerDiagA.diagGL (e ∘ ρ) * D = InnerDiagA.diagGL (e ∘ ρ) := by
    rw [mul_assoc, ← hDcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hgval : ((g : GL (Fin n) F)) = (B * D)⁻¹ := rfl
  rw [hgval, inv_inv]
  calc (B * D)⁻¹ * LinFusion.ggFrameDiag Q e * (B * D)
      = D⁻¹ * (B⁻¹ * LinFusion.ggFrameDiag Q e * B) * D := by group
    _ = D⁻¹ * InnerDiagA.diagGL (e ∘ ρ) * D := by rw [hXB]
    _ = InnerDiagA.diagGL (e ∘ ρ) := hDconj

theorem exists_conj_comm_root_levi {G : Type} [Group G] {F : Type} [Field F] [Finite F]
    [CharP F 2] {f k : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (ψ : SU (unitaryInvolution F 2 f) (k + 2) →* G) {Q : GL (Fin (k + 2)) F}
    (hQ : UFusion.IsUFrame (unitaryInvolution F 2 f) Q) {e : Fin (k + 2) → Fˣ}
    {j₁ j₂ : Fin (k + 2)} (hj : j₁ ≠ j₂) (he₁₂ : e j₁ = e j₂)
    (he : ∀ i i', i ≠ j₁ → i ≠ j₂ → i' ≠ j₁ → i' ≠ j₂ → e i = e i') {d : G}
    (hd : (d, LinFusion.ggFrameDiag Q e) ∈ UFusion.suInducedPairs ψ)
    (h : SU (unitaryInvolution F 2 f) (k + 2)) :
    ∃ g : SU (unitaryInvolution F 2 f) (k + 2),
      ψ g * d * (ψ g)⁻¹ * ψ (h * ggInvSU (unitaryInvolution F 2 f) (k + 2) 1 * h⁻¹) =
          ψ (h * ggInvSU (unitaryInvolution F 2 f) (k + 2) 1 * h⁻¹) * (ψ g * d * (ψ g)⁻¹) ∧
        ∀ u : SU (unitaryInvolution F 2 f) k,
          ψ g * d * (ψ g)⁻¹ *
              ψ (h * CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u * h⁻¹) =
            ψ (h * CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u * h⁻¹) *
              (ψ g * d * (ψ g)⁻¹) := by
  let σ := unitaryInvolution F 2 f
  let c : Fin (k + 2) := (Equiv.swap (0 : Fin (k + 2)) j₁).symm j₂
  let ρ : Equiv.Perm (Fin (k + 2)) :=
    Equiv.swap (0 : Fin (k + 2)) j₁ * Equiv.swap (Fin.last (k + 1)) c
  have hc0 : c ≠ 0 := by
    intro hc
    have h1 : (Equiv.swap (0 : Fin (k + 2)) j₁) c = j₁ := by
      rw [hc, Equiv.swap_apply_left]
    have h2 : (Equiv.swap (0 : Fin (k + 2)) j₁) c = j₂ :=
      Equiv.apply_symm_apply (Equiv.swap (0 : Fin (k + 2)) j₁) j₂
    exact hj (h1.symm.trans h2)
  have hρ0 : ρ 0 = j₁ := by
    simp only [ρ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne
      (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.zero_ne_last) (Ne.symm hc0),
      Equiv.swap_apply_left]
  have hρlast : ρ (Fin.last (k + 1)) = j₂ := by
    simp only [ρ, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_left]
    exact Equiv.apply_symm_apply (Equiv.swap (0 : Fin (k + 2)) j₁) j₂
  have hρ : ∀ i, e (ρ (Fin.rev i)) = e (ρ i) := by
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      rw [Fin.rev_zero, hρlast, hρ0]
      exact he₁₂.symm
    · by_cases hil : i = Fin.last (k + 1)
      · subst hil
        rw [Fin.rev_last, hρ0, hρlast]
        exact he₁₂
      · have hri0 : Fin.rev i ≠ 0 := by
          intro hri
          apply hil
          have := congrArg Fin.rev hri
          rwa [Fin.rev_rev, Fin.rev_zero] at this
        have hril : Fin.rev i ≠ Fin.last (k + 1) := by
          intro hri
          apply hi0
          have := congrArg Fin.rev hri
          rwa [Fin.rev_rev, Fin.rev_last] at this
        refine (he (ρ i) (ρ (Fin.rev i)) ?_ ?_ ?_ ?_).symm
        · intro hji
          exact hi0 (ρ.injective (hji.trans hρ0.symm))
        · intro hji
          exact hil (ρ.injective (hji.trans hρlast.symm))
        · intro hji
          exact hri0 (ρ.injective (hji.trans hρ0.symm))
        · intro hji
          exact hril (ρ.injective (hji.trans hρlast.symm))
  obtain ⟨g₁, hg₁⟩ :=
    exists_SU_conj_frameDiag (f := f) (m := k + 1) hF (by omega) (Q := Q) hQ e ρ hρ
  let g : SU σ (k + 2) := h * g₁
  have hgX : ((g : GL (Fin (k + 2)) F)) * LinFusion.ggFrameDiag Q e *
      ((g : GL (Fin (k + 2)) F))⁻¹ = (h : GL (Fin (k + 2)) F) *
        InnerDiagA.diagGL (e ∘ ρ) * (h : GL (Fin (k + 2)) F)⁻¹ := by
    rw [show g = h * g₁ from rfl, Subgroup.coe_mul, ← hg₁]
    group
  have hprod : (ψ g * d * (ψ g)⁻¹,
      (h : GL (Fin (k + 2)) F) * InnerDiagA.diagGL (e ∘ ρ) *
        (h : GL (Fin (k + 2)) F)⁻¹) ∈ UFusion.suInducedPairs ψ := by
    have h0 := (UFusion.suInducedPairs ψ).mul_mem
      ((UFusion.suInducedPairs ψ).mul_mem (UFusion.mem_suInducedPairs_coe ψ g) hd)
      ((UFusion.suInducedPairs ψ).inv_mem (UFusion.mem_suInducedPairs_coe ψ g))
    simp only [Prod.mk_mul_mk, Prod.inv_mk] at h0
    rwa [hgX] at h0
  obtain ⟨hA, hconj⟩ := UFusion.mem_suInducedPairs.mp hprod
  have h0 : (e ∘ ρ) 0 = (e ∘ ρ) (Fin.last (k + 1)) := by
    simp only [Function.comp_apply, hρ0, hρlast]
    exact he₁₂
  have hcomm_gg : InnerDiagA.diagGL (e ∘ ρ) *
      (ggInvSU σ (k + 2) 1 : GL (Fin (k + 2)) F) =
        (ggInvSU σ (k + 2) 1 : GL (Fin (k + 2)) F) * InnerDiagA.diagGL (e ∘ ρ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL,
      coe_ggInvSU σ (by omega : 2 * 1 ≤ k + 2)]
    exact diagonal_mul_ggInvUMatrix_one (e ∘ ρ) h0
  let I : Finset (Fin (k + 2)) := Finset.univ.filter (fun i =>
    i ∈ Set.range (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid (m := k)))
  have hI : ∀ i, i ∈ I ↔ i ∈ Set.range
      (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid (m := k)) := by
    intro i
    simp [I]
  have hconst : ∀ i ∈ I, ∀ j ∈ I, (e ∘ ρ) i = (e ∘ ρ) j := by
    intro i hi j hj
    rw [hI] at hi hj
    obtain ⟨a, rfl⟩ := hi
    obtain ⟨b, rfl⟩ := hj
    simp only [Function.comp_apply]
    refine he _ _ ?_ ?_ ?_ ?_
    · intro hji
      exact CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid_ne_zero a
        (ρ.injective (hji.trans hρ0.symm))
    · intro hji
      exact CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid_ne_last a
        (ρ.injective (hji.trans hρlast.symm))
    · intro hji
      exact CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid_ne_zero b
        (ρ.injective (hji.trans hρ0.symm))
    · intro hji
      exact CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid_ne_last b
        (ρ.injective (hji.trans hρlast.symm))
  have hcomm_iota (u : SU σ k) : InnerDiagA.diagGL (e ∘ ρ) *
      (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u :
        GL (Fin (k + 2)) F) =
        (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u :
          GL (Fin (k + 2)) F) * InnerDiagA.diagGL (e ∘ ρ) := by
    have hdet : (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaMat
        (SUExtras.mat σ k u)).det ≠ 0 := by
      rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.det_iotaMat,
        SUExtras.mat_apply, (mem_SU.mp u.2).1]
      exact one_ne_zero
    let A : GL (Fin (k + 2)) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
      (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaMat
        (SUExtras.mat σ k u)) hdet
    have hAmat : ((A : GL (Fin (k + 2)) F) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) F) =
        CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaMat
          (SUExtras.mat σ k u) :=
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ hdet
    have hmem : A ∈ UFusion.glBlock (F := F) I := by
      rw [UFusion.mem_glBlock]
      intro i j hij
      have hij' : i ∉ Set.range
          (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid (m := k)) ∨
          j ∉ Set.range
            (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mid (m := k)) := by
        rcases hij with hi | hj
        · exact Or.inl (fun h => hi ((hI i).mpr h))
        · exact Or.inr (fun h => hj ((hI j).mpr h))
      rw [hAmat]
      exact CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaMat_isBlkOn _ i j hij'
    have h := congrArg (fun x : GL (Fin (k + 2)) F =>
      ((x : GL (Fin (k + 2)) F) : Matrix (Fin (k + 2)) (Fin (k + 2)) F))
      (UFusion.diagGL_mul_comm_of_mem_glBlock hconst hmem)
    rw [Units.val_mul, Units.val_mul, InnerDiagA.coe_diagGL, hAmat] at h
    apply Units.ext
    change Matrix.diagonal (fun i => ((e ∘ ρ) i : F)) *
        (SUExtras.mat σ (k + 2))
          (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u) =
      (SUExtras.mat σ (k + 2))
          (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u) *
        Matrix.diagonal (fun i => ((e ∘ ρ) i : F))
    rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mat_iotaHom]
    exact h
  refine ⟨g, ?_, ?_⟩
  · have h1 := hconj (h * ggInvSU σ (k + 2) 1 * h⁻¹)
    rw [conjSU_conj_eq_self hA hcomm_gg] at h1
    calc ψ g * d * (ψ g)⁻¹ * ψ (h * ggInvSU σ (k + 2) 1 * h⁻¹)
        = ψ g * d * (ψ g)⁻¹ * ψ (h * ggInvSU σ (k + 2) 1 * h⁻¹) *
            (ψ g * d * (ψ g)⁻¹)⁻¹ * (ψ g * d * (ψ g)⁻¹) := by group
      _ = ψ (h * ggInvSU σ (k + 2) 1 * h⁻¹) * (ψ g * d * (ψ g)⁻¹) := by rw [h1]
  · intro u
    have h1 := hconj (h * CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u *
      h⁻¹)
    rw [conjSU_conj_eq_self hA (hcomm_iota u)] at h1
    calc ψ g * d * (ψ g)⁻¹ *
          ψ (h * CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u * h⁻¹)
        = ψ g * d * (ψ g)⁻¹ *
            ψ (h * CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u * h⁻¹) *
            (ψ g * d * (ψ g)⁻¹)⁻¹ * (ψ g * d * (ψ g)⁻¹) := by group
      _ = ψ (h * CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom u * h⁻¹) *
            (ψ g * d * (ψ g)⁻¹) := by rw [h1]

end OrthYSU

end CFSG.StandardType
