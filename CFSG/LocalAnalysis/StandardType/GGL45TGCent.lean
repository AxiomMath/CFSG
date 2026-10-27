module

public import CFSG.LocalAnalysis.StandardType.GGL45TGTorus

public section

namespace CFSG.StandardType.GGL45TG

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA Matrix
open GGL45TA (diagGL coe_diagGL map_diagGL)

namespace GSetting

variable {d : ℕ} {k : Type} [Field k] [Finite k] {K : Type} [Group K] {D : GData d k} {p q₀ : ℕ}
  {ψ : MulAut K} {E : Subgroup (MulAut K)}

theorem exists_frame (S : GSetting p q₀ d k D K ψ E) : ∃ P : GL (Fin d) k,
    Matrix.GeneralLinearGroup.map S.τ.toRingHom P = P ∧
    (∀ x, S.IsLift x → ∃ t : Fin d → kˣ, (∀ i, t i ^ p = 1) ∧ P * x * P⁻¹ = diagGL d t) ∧
    (∀ g : GL (Fin d) k, (∀ x, S.IsLift x → g * x = x * g) →
      ∃ t : Fin d → kˣ, P * g * P⁻¹ = diagGL d t) ∧
    ∀ t : Fin d → kˣ, ∏ i, t i = 1 → (∀ i, GGL45IsPElt p (t i)) →
      P⁻¹ * diagGL d t * P ∈ D.H := by
  obtain ⟨P, hPτ, hP, hPH⟩ := S.exists_diag_frame
  refine ⟨P, hPτ, fun x hx => S.frame_eq_diagGL hP hx, fun g hg => ?_, hPH⟩
  set M := ((P * g * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) with hM
  have hdiag : M.IsDiag := by
    refine RawTorusPProof.isDiag_of_commute_separating fun i j hij => ?_
    obtain ⟨x, hx, hne⟩ := S.frame_separating hPτ hP hPH hij
    refine ⟨((P * x * P⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k), ?_, hne, ?_⟩
    · obtain ⟨t, -, ht⟩ := S.frame_eq_diagGL hP hx
      rw [ht, coe_diagGL]
      exact isDiag_diagonal _
    · rw [hM, ← Units.val_mul, ← Units.val_mul]
      congr 1
      have := hg x hx
      calc P * g * P⁻¹ * (P * x * P⁻¹) = P * (g * x) * P⁻¹ := by group
        _ = P * (x * g) * P⁻¹ := by rw [this]
        _ = P * x * P⁻¹ * (P * g * P⁻¹) := by group
  have hMd : M = diagonal fun i => M i i := ((isDiag_iff_diagonal_diag M).mp hdiag).symm
  have hne : ∀ i, M i i ≠ 0 := TypeA.PGLTor.diag_ne_zero_of_eq_diagonal hMd
  refine ⟨fun i => Units.mk0 (M i i) (hne i), Units.ext ?_⟩
  rw [coe_diagGL]
  simp only [Units.val_mk0]
  exact hMd

theorem comm_of_comm_lifts (S : GSetting p q₀ d k D K ψ E) {g g' : GL (Fin d) k}
    (hg : ∀ x, S.IsLift x → g * x = x * g) (hg' : ∀ x, S.IsLift x → g' * x = x * g') :
    g * g' = g' * g := by
  obtain ⟨P, -, -, hcent, -⟩ := S.exists_frame
  obtain ⟨t, ht⟩ := hcent g hg
  obtain ⟨t', ht'⟩ := hcent g' hg'
  have h1 : diagGL d t * diagGL d t' = diagGL d t' * diagGL d t := by
    rw [← map_mul, ← map_mul, mul_comm]
  rw [← ht, ← ht'] at h1
  have h2 : P * (g * g') * P⁻¹ = P * (g' * g) * P⁻¹ := by
    calc P * (g * g') * P⁻¹ = P * g * P⁻¹ * (P * g' * P⁻¹) := by group
      _ = P * g' * P⁻¹ * (P * g * P⁻¹) := h1
      _ = P * (g' * g) * P⁻¹ := by group
  simpa using h2

theorem map_tau_of_comm_lifts (S : GSetting p q₀ d k D K ψ E) {g : GL (Fin d) k}
    (hg : ∀ x, S.IsLift x → g * x = x * g) :
    Matrix.GeneralLinearGroup.map S.τ.toRingHom g = g ^ q₀ := by
  obtain ⟨P, hPτ, -, hcent, -⟩ := S.exists_frame
  obtain ⟨t, ht⟩ := hcent g hg
  have hg' : g = P⁻¹ * diagGL d t * P := by rw [← ht]; group
  have hτt : (fun i => Units.map S.τ.toRingHom.toMonoidHom (t i)) = t ^ q₀ := by
    funext i
    apply Units.ext
    change S.τ (t i : k) = ((t ^ q₀) i : k)
    rw [S.τ_apply, Pi.pow_apply, Units.val_pow_eq_pow_val]
  rw [hg', map_mul, map_mul, map_inv, hPτ, map_diagGL, hτt, map_pow]
  rw [show P⁻¹ * diagGL d t ^ q₀ * P = P⁻¹ * diagGL d t ^ q₀ * P⁻¹⁻¹ by rw [inv_inv], ← conj_pow,
    inv_inv]

theorem pow_card_sub_one_of_comm_lifts (S : GSetting p q₀ d k D K ψ E) {g : GL (Fin d) k}
    (hg : ∀ x, S.IsLift x → g * x = x * g) : g ^ (Nat.card k - 1) = 1 := by
  obtain ⟨P, -, -, hcent, -⟩ := S.exists_frame
  obtain ⟨t, ht⟩ := hcent g hg
  have hg' : g = P⁻¹ * diagGL d t * P⁻¹⁻¹ := by rw [← ht]; group
  have htq : t ^ (Nat.card k - 1) = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← Nat.card_units]
    exact pow_card_eq_one'
  rw [hg', conj_pow, ← map_pow, htq, map_one, mul_one, mul_inv_cancel]

theorem exists_pval (S : GSetting p q₀ d k D K ψ E) : ∃ s m k' : ℕ, 2 ≤ s ∧
    Nat.card k - 1 = p ^ s * m ∧ ¬ p ∣ m ∧ ¬ p ∣ k' ∧ (q₀ : ℤ) = 1 + (p : ℤ) ^ (s - 1) * k' := by
  have hcard := S.card_k
  have hq₀ : 2 ≤ q₀ := by
    rcases Nat.lt_or_ge q₀ 2 with h | h
    · interval_cases q₀
      · have := Nat.card_pos (α := k)
        rw [hcard, zero_pow S.hp.ne_zero] at this
        omega
      · have := Finite.one_lt_card (α := k)
        rw [hcard, one_pow] at this
        omega
    · exact h
  have hdvd : p ∣ q₀ - 1 := by
    have h1 := S.dvd_q₀
    have : ((q₀ - 1 : ℕ) : ℤ) = (q₀ : ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ q₀)]; ring
    exact Int.natCast_dvd_natCast.mp (this ▸ h1)
  obtain ⟨a, k', hk', hq⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := q₀ - 1) (by omega) p
    S.hp.ne_one
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero, one_mul] at hq
      exact absurd (hq ▸ hdvd) hk'
    · exact h0
  have hmod : q₀ ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' (by omega)).mpr hdvd).symm
  obtain ⟨u, hu, hpu⟩ := CFSG.HardMathSupport.C14Group.geom_sum_eq_prime_mul S.hp S.hp2 hmod
  have hq₀Z : (q₀ : ℤ) - 1 = (p : ℤ) ^ a * k' := by
    have h1 : ((q₀ - 1 : ℕ) : ℤ) = (q₀ : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q₀), Nat.cast_one]
    rw [← h1, hq]
    push_cast
    ring
  have hsumZ : (∑ i ∈ Finset.range p, (q₀ : ℤ) ^ i) = (p : ℤ) * u := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hu
    push_cast at this
    exact this
  have hcardZ : ((Nat.card k - 1 : ℕ) : ℤ) = (q₀ : ℤ) ^ p - 1 := by
    rw [← Nat.card_units]
    exact S.card_units
  refine ⟨a + 1, k' * u, k', by omega, ?_, ?_, hk', ?_⟩
  · have h2 : ((Nat.card k - 1 : ℕ) : ℤ) = ((p ^ (a + 1) * (k' * u) : ℕ) : ℤ) := by
      rw [hcardZ, ← geom_sum_mul, hsumZ, hq₀Z]
      push_cast
      ring
    exact_mod_cast h2
  · intro h
    rcases (Nat.Prime.dvd_mul S.hp).mp h with h | h
    · exact hk' h
    · exact hpu h
  · rw [Nat.add_sub_cancel]
    linarith

end GSetting

end CFSG.StandardType.GGL45TG
