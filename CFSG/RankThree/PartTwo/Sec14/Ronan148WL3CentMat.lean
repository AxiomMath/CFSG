module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG.RankThree.PartTwo.Sec4 Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K]

theorem exists_eq_diagUnits {Y : GL (Fin 3) K} (h01 : (Y : Matrix (Fin 3) (Fin 3) K) 0 1 = 0)
    (h02 : (Y : Matrix (Fin 3) (Fin 3) K) 0 2 = 0) (h10 : (Y : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h12 : (Y : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) (h20 : (Y : Matrix (Fin 3) (Fin 3) K) 2 0 = 0)
    (h21 : (Y : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) :
    ∃ a b c : Kˣ, Y = diagUnits a b c := by
  have hdet : (Y : Matrix (Fin 3) (Fin 3) K).det =
      (Y : Matrix (Fin 3) (Fin 3) K) 0 0 * (Y : Matrix (Fin 3) (Fin 3) K) 1 1 *
        (Y : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    rw [det_fin_three, h01, h02, h10, h12, h20, h21]
    ring
  have hne : (Y : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    (Y.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  rw [hdet] at hne
  have h0 : (Y : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := fun h => hne (by rw [h]; ring)
  have h1 : (Y : Matrix (Fin 3) (Fin 3) K) 1 1 ≠ 0 := fun h => hne (by rw [h]; ring)
  have h2 : (Y : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := fun h => hne (by rw [h]; ring)
  refine ⟨Units.mk0 _ h0, Units.mk0 _ h1, Units.mk0 _ h2, Units.ext ?_⟩
  rw [coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]

theorem exists_eq_diagUnits_of_commute {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {Y : GL (Fin 3) K} (hY : Y * diagTau hτ = diagTau hτ * Y) :
    ∃ a b c : Kˣ, Y = diagUnits a b c := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hc := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hY
  simp only [Units.val_mul, coe_diagTau_eq_diagonal] at hc
  have z := fun i j (hij : (![τ, τ ^ 2, 1] : Fin 3 → K) i ≠ ![τ, τ ^ 2, 1] j) =>
    entry_eq_zero_of_commute_diagonal hc hij
  exact exists_eq_diagUnits (z 0 1 (by simpa using hττ2)) (z 0 2 (by simpa using hτ1))
    (z 1 0 (by simpa using hττ2.symm)) (z 1 2 (by simpa using hτ2))
    (z 2 0 (by simpa using hτ1.symm)) (z 2 1 (by simpa using hτ2.symm))

theorem exists_cycThree_pow_conj_diagUnits (k : ℕ) (a b c : Kˣ) :
    ∃ a' b' c' : Kˣ, cycThree ^ k * diagUnits a b c * (cycThree ^ k)⁻¹ = diagUnits a' b' c' := by
  induction k generalizing a b c with
  | zero => exact ⟨a, b, c, by simp⟩
  | succ k ih =>
    obtain ⟨a', b', c', h⟩ := ih a b c
    refine ⟨c', a', b', ?_⟩
    calc cycThree ^ (k + 1) * diagUnits a b c * (cycThree ^ (k + 1))⁻¹ =
        cycThree * (cycThree ^ k * diagUnits a b c * (cycThree ^ k)⁻¹) * cycThree⁻¹ := by
          rw [pow_succ', _root_.mul_inv_rev]
          simp only [mul_assoc]
      _ = diagUnits c' a' b' := by rw [h, cycThree_conj_diagUnits]

theorem pow_three_eq_one_of_conj {Y d : GL (Fin 3) K} {c : Kˣ}
    (h : Y * d * Y⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * d) : c ^ 3 = 1 := by
  have h1 := congrArg GeneralLinearGroup.det h
  rw [map_mul, map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det Y),
    mul_assoc, mul_inv_cancel, mul_one] at h1
  have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c) = c ^ 3 :=
    Units.ext (by
      rw [GeneralLinearGroup.val_det_apply, det_scalar, Units.val_pow_eq_pow_val])
  rw [h2] at h1
  have h3 : c ^ 3 * GeneralLinearGroup.det d = 1 * GeneralLinearGroup.det d := by
    rw [one_mul, ← h1]
  exact mul_right_cancel h3

theorem monomial_of_conj_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {Y : GL (Fin 3) K}
    {c : Kˣ} (h : Y * diagTau hτ * Y⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * diagTau hτ) :
    ∃ (a b c' : Kˣ) (k : ℕ), k < 3 ∧ Y = diagUnits a b c' * cycThree ^ k := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set t := Units.mk0 τ hτ0 with ht
  have hc3 := pow_three_eq_one_of_conj h
  have hroots : c = t ^ (2 * 0) ∨ c = t ^ (2 * 1) ∨ c = t ^ (2 * 2) := by
    have hc3' : (c : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    have hsum : τ ^ 2 + τ + 1 = 0 := by
      have : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hτ1)
    have hfac : ((c : K) - 1) * ((c : K) - τ ^ 2) * ((c : K) - τ ^ 4) = 0 := by
      linear_combination hc3' + (-(c : K) ^ 2 + τ ^ 2 * c) * hsum +
        (-τ * (c : K) ^ 2 + τ ^ 3 * c - τ ^ 3 - 1) * hτ
    rcases mul_eq_zero.mp hfac with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · exact Or.inl (Units.ext (by simpa using sub_eq_zero.mp h1))
      · exact Or.inr (Or.inl (Units.ext (by simpa [ht] using sub_eq_zero.mp h2)))
    · exact Or.inr (Or.inr (Units.ext (by simpa [ht] using sub_eq_zero.mp h3)))
  have key : ∀ k : ℕ, c = t ^ (2 * k) →
      ∃ (a b c' : Kˣ), Y = diagUnits a b c' * cycThree ^ k := by
    intro k hk
    have hck := cycThree_pow_conj_diagTau hτ hτ0 k
    rw [← ht, ← hk, ← h] at hck
    have hcomm : ((cycThree ^ k)⁻¹ * Y) * diagTau hτ = diagTau hτ * ((cycThree ^ k)⁻¹ * Y) := by
      have : (cycThree ^ k)⁻¹ * Y * diagTau hτ * ((cycThree ^ k)⁻¹ * Y)⁻¹ = diagTau hτ := by
        calc (cycThree ^ k)⁻¹ * Y * diagTau hτ * ((cycThree ^ k)⁻¹ * Y)⁻¹ =
            (cycThree ^ k)⁻¹ * (Y * diagTau hτ * Y⁻¹) * cycThree ^ k := by group
          _ = (cycThree ^ k)⁻¹ * (cycThree ^ k * diagTau hτ * (cycThree ^ k)⁻¹) *
              cycThree ^ k := by rw [hck]
          _ = diagTau hτ := by group
      calc (cycThree ^ k)⁻¹ * Y * diagTau hτ =
          (cycThree ^ k)⁻¹ * Y * diagTau hτ * ((cycThree ^ k)⁻¹ * Y)⁻¹ *
            ((cycThree ^ k)⁻¹ * Y) := by group
        _ = diagTau hτ * ((cycThree ^ k)⁻¹ * Y) := by rw [this]
    obtain ⟨a, b, c', hD⟩ := exists_eq_diagUnits_of_commute hτ hτ1 hcomm
    obtain ⟨a', b', c'', hD'⟩ := exists_cycThree_pow_conj_diagUnits k a b c'
    refine ⟨a', b', c'', ?_⟩
    rw [← hD']
    calc Y = cycThree ^ k * ((cycThree ^ k)⁻¹ * Y) := by group
      _ = cycThree ^ k * diagUnits a b c' * (cycThree ^ k)⁻¹ * cycThree ^ k := by rw [hD]; group
  rcases hroots with h0 | h1 | h2
  · obtain ⟨a, b, c', hY⟩ := key 0 h0
    exact ⟨a, b, c', 0, by norm_num, hY⟩
  · obtain ⟨a, b, c', hY⟩ := key 1 h1
    exact ⟨a, b, c', 1, by norm_num, hY⟩
  · obtain ⟨a, b, c', hY⟩ := key 2 h2
    exact ⟨a, b, c', 2, by norm_num, hY⟩

theorem conj_monomial_diagUnits_eq (a b c u v w : Kˣ) {k : ℕ} (hk : k < 3) :
    (diagUnits a b c * cycThree ^ k) * diagUnits u v w * (diagUnits a b c * cycThree ^ k)⁻¹ =
      diagUnits u v w ∨
    (diagUnits a b c * cycThree ^ k) * diagUnits u v w * (diagUnits a b c * cycThree ^ k)⁻¹ =
      diagUnits w u v ∨
    (diagUnits a b c * cycThree ^ k) * diagUnits u v w * (diagUnits a b c * cycThree ^ k)⁻¹ =
      diagUnits v w u := by
  have hD : ∀ x y z : Kˣ, diagUnits a b c * diagUnits x y z * (diagUnits a b c)⁻¹ =
      diagUnits x y z := fun x y z => by
    rw [Sec12.KS128Move.diagUnits_comm a b c x y z, mul_inv_cancel_right]
  have hexp : (diagUnits a b c * cycThree ^ k) * diagUnits u v w *
      (diagUnits a b c * cycThree ^ k)⁻¹ =
      diagUnits a b c * (cycThree ^ k * diagUnits u v w * (cycThree ^ k)⁻¹) *
        (diagUnits a b c)⁻¹ := by group
  interval_cases k
  · left
    rw [hexp, pow_zero, one_mul, inv_one, mul_one, hD]
  · right; left
    rw [hexp, pow_one, cycThree_conj_diagUnits, hD]
  · right; right
    rw [hexp, show (cycThree : GL (Fin 3) K) ^ 2 * diagUnits u v w * (cycThree ^ 2)⁻¹ =
        cycThree * (cycThree * diagUnits u v w * cycThree⁻¹) * cycThree⁻¹ by
          rw [pow_two, _root_.mul_inv_rev]
          simp only [mul_assoc],
      cycThree_conj_diagUnits, cycThree_conj_diagUnits, hD]

theorem mk_conj_torus_eq {a b c ρ ρ' : Kˣ} {k : ℕ} (hk : k < 3)
    (h : pmk ((diagUnits a b c * cycThree ^ k) * diagUnits ρ' 1 ρ'⁻¹ *
      (diagUnits a b c * cycThree ^ k)⁻¹) = pmk (diagUnits ρ 1 ρ⁻¹ : GL (Fin 3) K)) :
    ρ' = ρ ∧ (k = 0 ∨ ρ ^ 3 = 1) := by
  have hexp : (diagUnits a b c * cycThree ^ k) * diagUnits ρ' 1 ρ'⁻¹ *
      (diagUnits a b c * cycThree ^ k)⁻¹ =
      diagUnits a b c * (cycThree ^ k * diagUnits ρ' 1 ρ'⁻¹ * (cycThree ^ k)⁻¹) *
        (diagUnits a b c)⁻¹ := by group
  have hD : ∀ x y z : Kˣ, diagUnits a b c * diagUnits x y z * (diagUnits a b c)⁻¹ =
      diagUnits x y z := fun x y z => by
    rw [Sec12.KS128Move.diagUnits_comm a b c x y z, mul_inv_cancel_right]
  rw [hexp] at h
  interval_cases k
  · rw [pow_zero, one_mul, inv_one, mul_one, hD] at h
    obtain ⟨u, h1, h2, -⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h
    rw [one_mul] at h2
    rw [h2, mul_one] at h1
    exact ⟨h1, Or.inl rfl⟩
  · rw [pow_one, cycThree_conj_diagUnits, hD] at h
    obtain ⟨u, h1, h2, h3⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h
    rw [one_mul] at h3
    rw [h3] at h1 h2
    have hρ' : ρ' = ρ := mul_inv_eq_one.mp h2
    refine ⟨hρ', Or.inr ?_⟩
    rw [hρ'] at h1
    calc ρ ^ 3 = ρ * ρ * ρ := by rw [pow_succ, pow_two]
      _ = ρ * ρ * (ρ⁻¹ * ρ⁻¹) := by rw [h1]
      _ = 1 := by group
  · rw [show (cycThree : GL (Fin 3) K) ^ 2 * diagUnits ρ' 1 ρ'⁻¹ * (cycThree ^ 2)⁻¹ =
        cycThree * (cycThree * diagUnits ρ' 1 ρ'⁻¹ * cycThree⁻¹) * cycThree⁻¹ by
          rw [pow_two, _root_.mul_inv_rev]
          simp only [mul_assoc],
      cycThree_conj_diagUnits, cycThree_conj_diagUnits, hD] at h
    obtain ⟨u, h1, h2, h3⟩ := (RonanK432.L3Hard.mk_diagUnits_eq_iff _ _ _ _ _ _).mp h
    rw [one_mul] at h1
    rw [h1] at h2 h3
    have hρ' : ρ' = ρ := inv_mul_eq_one.mp h2
    refine ⟨hρ', Or.inr ?_⟩
    rw [hρ'] at h3
    calc ρ ^ 3 = ρ * ρ * ρ := by rw [pow_succ, pow_two]
      _ = ρ⁻¹ * ρ := by rw [h3]
      _ = 1 := inv_mul_cancel ρ

theorem commute_of_conj_diagE (h3 : (3 : K) ≠ 0) {ε : Kˣ} (hε3 : (ε : K) ^ 3 = 1)
    {Y : GL (Fin 3) K} {c : Kˣ}
    (h : Y * diagE ε * Y⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * diagE ε) :
    Y * diagE ε = diagE ε * Y := by
  have he2 : (ε : K) + 2 ≠ 0 := by
    intro h0
    have : (ε : K) = -2 := by linear_combination h0
    rw [this] at hε3
    apply h3
    have h9 : (3 : K) * 3 = 0 := by linear_combination -hε3
    exact mul_self_eq_zero.mp h9
  have htr := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K).trace) h
  simp only [Units.val_mul] at htr
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, coe_diagE] at htr
  simp only [trace_diagonal, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul] at htr
  have hc1 : (c : K) = 1 := by
    have : ((c : K) - 1) * ((ε : K) + 2) = 0 := by linear_combination -htr
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right he2)
  have hc : c = 1 := Units.ext hc1
  rw [hc, map_one, one_mul] at h
  calc Y * diagE ε = Y * diagE ε * Y⁻¹ * Y := by group
    _ = diagE ε * Y := by rw [h]

theorem commute_diagUnits_of_commute_diagE {ε : Kˣ} (hε : ε ≠ 1) {Y : GL (Fin 3) K}
    (hY : Y * diagE ε = diagE ε * Y) (a b : Kˣ) :
    Y * diagUnits a b b = diagUnits a b b * Y := by
  have he' : (ε : K) ≠ 1 := fun h => hε (Units.ext h)
  have hc := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hY
  simp only [Units.val_mul, coe_diagE] at hc
  have z := fun i j (hij : (![(ε : K), 1, 1] : Fin 3 → K) i ≠ ![(ε : K), 1, 1] j) =>
    entry_eq_zero_of_commute_diagonal hc hij
  have l01 := z 0 1 (by simpa using he')
  have l02 := z 0 2 (by simpa using he')
  have l10 := z 1 0 (by simpa using he'.symm)
  have l20 := z 2 0 (by simpa using he'.symm)
  apply Units.ext
  simp only [Units.val_mul, coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, l01, l02, l10, l20, mul_comm]

theorem frobGL_diagUnits (σ : K ≃+* K) (a b c : Kˣ) :
    frobGL σ (diagUnits a b c) = diagUnits (Units.map (σ : K →* K) a)
      (Units.map (σ : K →* K) b) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_frobGL, coe_diagUnits, coe_diagUnits, Matrix.diagonal_map (map_zero σ)]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem frobGL_cycThree (σ : K ≃+* K) : frobGL σ cycThree = cycThree := by
  apply Units.ext
  rw [coe_frobGL, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem frobGL_diagTau (σ : K ≃+* K) {τ : K} (hτ : τ ^ 3 = 1) (hστ : σ τ = τ) :
    frobGL σ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_frobGL, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hστ]

theorem ringAut_apply_eq_of_pow_three {σ : K ≃+* K} {m : ℕ} (hσ : ∀ c, σ c = c ^ m)
    (hm : m % 3 = 1) {τ : K} (hτ : τ ^ 3 = 1) : σ τ = τ := by
  rw [hσ, ← Nat.div_add_mod m 3, hm, pow_add, pow_mul, hτ, one_pow, one_mul, pow_one]

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
