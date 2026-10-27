module

public import CFSG.LocalAnalysis.StandardType.GGSixTCPSUDualPairEmb

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.LieType.Universal CFSG.StandardType.TableCRes

private lemma dpeq_star_inv {g n : ℕ} {γ : GL (Fin n) (PSUF g)}
    (hγU : Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
      Unitary.antidiag n * (γ : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n) :
    ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      Unitary.antidiag n * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
        Unitary.antidiag n := by
  set J : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n with hJ
  have hJ2 : J * J = 1 := by rw [hJ]; exact Unitary.antidiag_mul_self n
  have h1 : Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J =
      J * ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
    calc Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J
        = Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J * 1 :=
            (Matrix.mul_one _).symm
      _ = Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J *
            ((γ : Matrix (Fin n) (Fin n) (PSUF g)) *
              ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g))) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = (Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J *
            (γ : Matrix (Fin n) (Fin n) (PSUF g))) *
              ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
            noncomm_ring
      _ = J * ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by rw [hγU]
  calc ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g))
      = J * (J * ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g))) := by
          rw [← Matrix.mul_assoc, hJ2, Matrix.one_mul]
    _ = J * (Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J) := by
          rw [← h1]
    _ = J * Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J :=
          (Matrix.mul_assoc _ _ _).symm

private lemma dpeq_commute_QW {g n k : ℕ} {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W)
    {γ : GL (Fin n) (PSUF g)}
    (hγU : Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
      Unitary.antidiag n * (γ : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n)
    (hγP : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R) =
      P * R * (γ : Matrix (Fin n) (Fin n) (PSUF g))) :
    (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) =
      Q * W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
  let J : Matrix (Fin n) (Fin n) (PSUF g) := Unitary.antidiag n
  have hJ2 : J * J = 1 := Unitary.antidiag_mul_self n
  have hJt : tcConjTr (PSUσ g) J = J := PSUantidiag_transpose_map n g
  have hpj : tcConjTr (PSUσ g) P * J = W := hD.pj
  have hqj : tcConjTr (PSUσ g) Q * J = R := hD.qj
  have hPstar : tcConjTr (PSUσ g) P = W * J := by
    calc tcConjTr (PSUσ g) P = tcConjTr (PSUσ g) P * 1 := (Matrix.mul_one _).symm
      _ = tcConjTr (PSUσ g) P * (J * J) := by rw [hJ2]
      _ = (tcConjTr (PSUσ g) P * J) * J := by simp only [Matrix.mul_assoc]
      _ = W * J := by rw [hpj]
  have hRstar : tcConjTr (PSUσ g) R = J * Q := by
    have h := congrArg (tcConjTr (PSUσ g)) hqj
    rw [tcConjTr_mul, hJt, tcConjTr_tcConjTr (PSUσ_involutive g)] at h
    exact h.symm
  have hcomm_star : tcConjTr (PSUσ g) (P * R) *
      tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) =
      tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
        tcConjTr (PSUσ g) (P * R) := by
    calc tcConjTr (PSUσ g) (P * R) * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g))
        = tcConjTr (PSUσ g) ((γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R)) :=
            (tcConjTr_mul (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) (P * R)).symm
      _ = tcConjTr (PSUσ g) ((P * R) * (γ : Matrix (Fin n) (Fin n) (PSUF g))) := by rw [hγP]
      _ = tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
            tcConjTr (PSUσ g) (P * R) :=
            tcConjTr_mul (PSUσ g) (P * R) (γ : Matrix (Fin n) (Fin n) (PSUF g))
  have hQWeq : Q * W = J * tcConjTr (PSUσ g) (P * R) * J := by
    have h : J * tcConjTr (PSUσ g) (P * R) * J = Q * W := by
      rw [tcConjTr_mul, hRstar, hPstar]
      rw [show J * ((J * Q) * (W * J)) * J = (J * J) * Q * W * (J * J) by
            simp only [Matrix.mul_assoc], hJ2]
      simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    exact h.symm
  have hγinv : ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      J * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J := by
    change ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) =
      Unitary.antidiag n * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
        Unitary.antidiag n
    exact dpeq_star_inv (g := g) (n := n) hγU
  have h1 : ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) =
      (Q * W) * ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) := by
    rw [hγinv, hQWeq]
    have hL : (J * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J) *
        (J * tcConjTr (PSUσ g) (P * R) * J) =
        J * (tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
          tcConjTr (PSUσ g) (P * R)) * J := by
      rw [show (J * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J) *
            (J * tcConjTr (PSUσ g) (P * R) * J) =
          J * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (J * J) *
            tcConjTr (PSUσ g) (P * R) * J by simp only [Matrix.mul_assoc], hJ2]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    have hR : (J * tcConjTr (PSUσ g) (P * R) * J) *
        (J * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J) =
        J * (tcConjTr (PSUσ g) (P * R) *
          tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g))) * J := by
      rw [show (J * tcConjTr (PSUσ g) (P * R) * J) *
            (J * tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J) =
          J * tcConjTr (PSUσ g) (P * R) * (J * J) *
            tcConjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * J by
              simp only [Matrix.mul_assoc], hJ2]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [hL, hR, hcomm_star]
  have h2 : (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
      ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h3 : ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) *
      (γ : Matrix (Fin n) (Fin n) (PSUF g)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h5 : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) *
      ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) = Q * W := by
    calc (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) *
          ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g))
        = (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
            ((Q * W) * ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g))) :=
            Matrix.mul_assoc _ _ _
      _ = (γ : Matrix (Fin n) (Fin n) (PSUF g)) *
            (((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W)) := by
            rw [h1.symm]
      _ = ((γ : Matrix (Fin n) (Fin n) (PSUF g)) *
            ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g))) * (Q * W) :=
            (Matrix.mul_assoc _ _ _).symm
      _ = Q * W := by rw [h2, Matrix.one_mul]
  calc (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W)
      = ((γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) *
          ((γ⁻¹ : GL (Fin n) (PSUF g)) : Matrix (Fin n) (Fin n) (PSUF g))) *
            (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
          rw [Matrix.mul_assoc, h3, Matrix.mul_one]
    _ = (Q * W) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by rw [h5]

private lemma dpeq_R_comm {g n k : ℕ} {P : Matrix (Fin n) (Fin k) (PSUF g)}
    {R : Matrix (Fin k) (Fin n) (PSUF g)} (hrp : R * P = 1)
    {γ : GL (Fin n) (PSUF g)}
    (hγP : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R) =
      P * R * (γ : Matrix (Fin n) (Fin n) (PSUF g))) :
    R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) =
      (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) * R := by
  calc R * (γ : Matrix (Fin n) (Fin n) (PSUF g))
      = (R * P) * R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by rw [hrp, Matrix.one_mul]
    _ = R * (P * R * (γ : Matrix (Fin n) (Fin n) (PSUF g))) := by
          simp only [Matrix.mul_assoc]
    _ = R * ((γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R)) := by rw [hγP]
    _ = (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) * R := by
          simp only [Matrix.mul_assoc]

private lemma dpeq_W_comm {g n k : ℕ} {Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {W : Matrix (Fin k) (Fin n) (PSUF g)} (hwq : W * Q = 1)
    {γ : GL (Fin n) (PSUF g)}
    (hγQ : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) =
      Q * W * (γ : Matrix (Fin n) (Fin n) (PSUF g))) :
    W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) =
      (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) * W := by
  calc W * (γ : Matrix (Fin n) (Fin n) (PSUF g))
      = (W * Q) * W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by rw [hwq, Matrix.one_mul]
    _ = W * (Q * W * (γ : Matrix (Fin n) (Fin n) (PSUF g))) := by
          simp only [Matrix.mul_assoc]
    _ = W * ((γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W)) := by rw [hγQ]
    _ = (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) * W := by
          simp only [Matrix.mul_assoc]

private lemma dpeq_dpEmb_conj {g n k : ℕ} {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} {γ : GL (Fin n) (PSUF g)}
    {a₀ a₁ a₀' a₁' : Matrix (Fin k) (Fin k) (PSUF g)}
    (hγX : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R) =
      P * R * (γ : Matrix (Fin n) (Fin n) (PSUF g)))
    (hγY : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) =
      Q * W * (γ : Matrix (Fin n) (Fin n) (PSUF g)))
    (hγP : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P = P * a₀)
    (hγQ : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q = Q * a₁)
    (hRγ : R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) = a₀ * R)
    (hWγ : W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) = a₁ * W)
    (h₀ : a₀' * a₀ = 1) (h₁ : a₁' * a₁ = 1) (x y : Matrix (Fin k) (Fin k) (PSUF g)) :
    (γ : Matrix (Fin n) (Fin n) (PSUF g)) * dpEmb P Q R W x y =
      dpEmb P Q R W (a₀ * x * a₀') (a₁ * y * a₁') *
        (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
  have hN : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - (P * R + Q * W)) =
      (1 - (P * R + Q * W)) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
    rw [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, hγX, hγY, Matrix.sub_mul, Matrix.add_mul,
      Matrix.one_mul]
  have hpx : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * x * R) =
      (P * (a₀ * x * a₀') * R) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
    calc (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * x * R)
        = ((γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) * (x * R) := by
            simp only [Matrix.mul_assoc]
      _ = (P * a₀) * (x * R) := by rw [hγP]
      _ = P * a₀ * x * R := by simp only [Matrix.mul_assoc]
      _ = P * (a₀ * x * a₀') * (a₀ * R) := by
            rw [show P * (a₀ * x * a₀') * (a₀ * R) = P * a₀ * x * (a₀' * a₀) * R by
                  simp only [Matrix.mul_assoc], h₀]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = P * (a₀ * x * a₀') * (R * (γ : Matrix (Fin n) (Fin n) (PSUF g))) := by rw [hRγ]
      _ = (P * (a₀ * x * a₀') * R) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
            simp only [Matrix.mul_assoc]
  have hqy : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * y * W) =
      (Q * (a₁ * y * a₁') * W) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
    calc (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * y * W)
        = ((γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) * (y * W) := by
            simp only [Matrix.mul_assoc]
      _ = (Q * a₁) * (y * W) := by rw [hγQ]
      _ = Q * a₁ * y * W := by simp only [Matrix.mul_assoc]
      _ = Q * (a₁ * y * a₁') * (a₁ * W) := by
            rw [show Q * (a₁ * y * a₁') * (a₁ * W) = Q * a₁ * y * (a₁' * a₁) * W by
                  simp only [Matrix.mul_assoc], h₁]
            simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Q * (a₁ * y * a₁') * (W * (γ : Matrix (Fin n) (Fin n) (PSUF g))) := by rw [hWγ]
      _ = (Q * (a₁ * y * a₁') * W) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
            simp only [Matrix.mul_assoc]
  calc (γ : Matrix (Fin n) (Fin n) (PSUF g)) * dpEmb P Q R W x y
      = (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (1 - (P * R + Q * W)) +
          (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * x * R) +
            (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * y * W) := by
          rw [dpEmb, Matrix.mul_add, Matrix.mul_add]
    _ = (1 - (P * R + Q * W)) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) +
          (P * (a₀ * x * a₀') * R) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) +
            (Q * (a₁ * y * a₁') * W) * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
          rw [hN, hpx, hqy]
    _ = (1 - (P * R + Q * W) + P * (a₀ * x * a₀') * R + Q * (a₁ * y * a₁') * W) *
          (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by
          rw [Matrix.add_mul, Matrix.add_mul]
    _ = dpEmb P Q R W (a₀ * x * a₀') (a₁ * y * a₁') *
          (γ : Matrix (Fin n) (Fin n) (PSUF g)) := by rw [dpEmb]

theorem dualPairEmbGL_conj_of_commute {g n k : ℕ} {P Q : Matrix (Fin n) (Fin k) (PSUF g)}
    {R W : Matrix (Fin k) (Fin n) (PSUF g)} (hD : PSUDualData g n k P Q R W)
    {γ : GL (Fin n) (PSUF g)}
    (hγU : Unitary.conjTr (PSUσ g) (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Unitary.antidiag n *
      (γ : Matrix (Fin n) (Fin n) (PSUF g)) = Unitary.antidiag n)
    (hγP : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (P * R) =
      P * R * (γ : Matrix (Fin n) (Fin n) (PSUF g))) :
    ∃ a : GL (Fin k) (PSUF g), ∀ x : GL (Fin k) (PSUF g),
      γ * dualPairEmbGL hD x * γ⁻¹ = dualPairEmbGL hD (a * x * a⁻¹) := by
  have hγQW : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * (Q * W) =
      Q * W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) := dpeq_commute_QW hD hγU hγP
  have hUP : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P =
      P * (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) := mul_P_eq_of_commute hD.rp hγP
  have hUQ : (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q =
      Q * (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) := mul_P_eq_of_commute hD.wq hγQW
  have hRγ : R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) =
      (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) * R := dpeq_R_comm hD.rp hγP
  have hWγ : W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) =
      (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) * W := dpeq_W_comm hD.wq hγQW
  have h01 : tcConjTr (PSUσ g) (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) *
      (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) = 1 :=
    tcConjTr_mul_eq_one_of_unitary hD.wq hD.pj hγU hUP hUQ
  have h10 : tcConjTr (PSUσ g) (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) *
      (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) = 1 := by
    have h := congrArg (tcConjTr (PSUσ g)) h01
    rwa [tcConjTr_mul, tcConjTr_tcConjTr (PSUσ_involutive g), tcConjTr_one] at h
  have h01' : (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) *
      tcConjTr (PSUσ g) (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) = 1 :=
    mul_eq_one_comm.mp h10
  let a : GL (Fin k) (PSUF g) :=
    ⟨R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P,
      tcConjTr (PSUσ g) (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q), h01', h10⟩
  refine ⟨a, fun x => ?_⟩
  have harg1 : (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) *
      (x : Matrix (Fin k) (Fin k) (PSUF g)) *
        tcConjTr (PSUσ g) (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) =
      ((a * x * a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)) := by
    rw [Units.val_mul, Units.val_mul]
    rfl
  have harg2 : (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) *
      (tcConjTr (PSUσ g) ((x⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g))) *
        tcConjTr (PSUσ g) (R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P) =
      tcConjTr (PSUσ g) (((a * x * a⁻¹)⁻¹ : GL (Fin k) (PSUF g)) :
        Matrix (Fin k) (Fin k) (PSUF g)) := by
    have hinv : (((a * x * a⁻¹)⁻¹ : GL (Fin k) (PSUF g)) :
        Matrix (Fin k) (Fin k) (PSUF g)) =
        (a : Matrix (Fin k) (Fin k) (PSUF g)) *
          ((x⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)) *
            ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)) := by
      simp only [mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hinv]
    rw [show ((a : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)) =
          R * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * P from rfl,
      show ((a⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)) =
          tcConjTr (PSUσ g) (W * (γ : Matrix (Fin n) (Fin n) (PSUF g)) * Q) from rfl]
    simp only [tcConjTr_mul, tcConjTr_tcConjTr (PSUσ_involutive g), Matrix.mul_assoc]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dualPairEmbGL, coe_dualPairEmbGL]
  have hconj := dpeq_dpEmb_conj hγP hγQW hUP hUQ hRγ hWγ h10 h01
    (x : Matrix (Fin k) (Fin k) (PSUF g))
    (tcConjTr (PSUσ g) ((x⁻¹ : GL (Fin k) (PSUF g)) : Matrix (Fin k) (Fin k) (PSUF g)))
  rw [hconj]
  rw [Matrix.mul_assoc]
  rw [show (γ : Matrix (Fin n) (Fin n) (PSUF g)) * ((γ⁻¹ : GL (Fin n) (PSUF g)) :
      Matrix (Fin n) (Fin n) (PSUF g)) = 1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one], Matrix.mul_one]
  rw [harg1, harg2]

end CFSG.StandardType.ClassicalPosition
