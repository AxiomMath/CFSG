module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentCnt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentEigen
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

private lemma k330c_psu_qres {Q : ℕ}
    (hQ7 : ¬ 7 ∣ Q ∧ ¬ 7 ∣ Q - 1 ∧ ¬ 7 ∣ Q + 1) :
    Q % 7 = 2 ∨ Q % 7 = 3 ∨ Q % 7 = 4 ∨ Q % 7 = 5 := by
  have hlt : Q % 7 < 7 := Nat.mod_lt Q (by norm_num)
  have h0 : Q % 7 ≠ 0 := fun h => hQ7.1 (Nat.dvd_of_mod_eq_zero h)
  have h1 : Q % 7 ≠ 1 := by
    intro h
    apply hQ7.2.1
    have hQeq : 7 * (Q / 7) + Q % 7 = Q := Nat.div_add_mod Q 7
    rw [h] at hQeq
    exact ⟨Q / 7, by omega⟩
  have h6 : Q % 7 ≠ 6 := by
    intro h
    apply hQ7.2.2
    have hQeq : 7 * (Q / 7) + Q % 7 = Q := Nat.div_add_mod Q 7
    rw [h] at hQeq
    exact ⟨Q / 7 + 1, by omega⟩
  omega

private lemma k330c_psu_pow_defect_one {Q a c : ℕ} (hQ : ¬ 7 ∣ Q) (hca : c ≤ a)
    (h : Q ^ a ≡ Q ^ c [MOD 7]) : (Q % 7) ^ (a - c) % 7 = 1 := by
  have h1 : Q ^ a = Q ^ c * Q ^ (a - c) := by
    rw [← pow_add, Nat.add_sub_cancel' hca]
  have h2 : Q ^ c * Q ^ (a - c) ≡ Q ^ c * 1 [MOD 7] := by
    rw [mul_one, ← h1]
    exact h
  have hcop : (7).gcd (Q ^ c) = 1 :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).mpr hQ).pow_right c
  have h3 : Q ^ (a - c) ≡ 1 [MOD 7] := h2.cancel_left_of_coprime hcop
  have h4 : Q ^ (a - c) % 7 = 1 % 7 := h3
  rw [Nat.pow_mod] at h4
  norm_num at h4
  exact h4

private lemma k330c_psu_defect {Q a c : ℕ}
    (hQ7 : ¬ 7 ∣ Q ∧ ¬ 7 ∣ Q - 1 ∧ ¬ 7 ∣ Q + 1)
    (hca : c ≤ a) (ha : a ≤ 5) (h : Q ^ a ≡ Q ^ c [MOD 7]) :
    a - c = 0 ∨ a - c = 3 := by
  have hmod := k330c_psu_pow_defect_one hQ7.1 hca h
  have hdcases : a - c = 0 ∨ a - c = 1 ∨ a - c = 2 ∨ a - c = 3 ∨ a - c = 4 ∨
      a - c = 5 := by
    omega
  rcases k330c_psu_qres hQ7 with hq | hq | hq | hq <;> rw [hq] at hmod
  · rcases hdcases with hd | hd | hd | hd | hd | hd
    · left; exact hd
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · right; exact hd
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
  · rcases hdcases with hd | hd | hd | hd | hd | hd
    · left; exact hd
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
  · rcases hdcases with hd | hd | hd | hd | hd | hd
    · left; exact hd
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · right; exact hd
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
  · rcases hdcases with hd | hd | hd | hd | hd | hd
    · left; exact hd
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)
    · exfalso; rw [hd] at hmod; exact absurd hmod (by norm_num)

private lemma k330c_psu_arith (Q n b f1 fω fω2 b1 bω bω2 : ℕ)
    (hQ7 : ¬ 7 ∣ Q ∧ ¬ 7 ∣ Q - 1 ∧ ¬ 7 ∣ Q + 1)
    (hn : n = 4 ∨ n = 5) (hb : b < n) (hf1 : f1 < n)
    (hnsum : n = f1 + fω + fω2) (hbsum : b = b1 + bω + bω2)
    (hfω : fω = fω2) (hb1 : b1 ≤ f1) (hbω : bω ≤ fω) (hbω2 : bω2 ≤ fω2)
    (hgn : Q ^ n ≡ Q ^ b [MOD 7]) (hg1 : Q ^ f1 ≡ Q ^ b1 [MOD 7])
    (hgω : Q ^ fω ≡ Q ^ bω [MOD 7]) (hgω2 : Q ^ fω2 ≡ Q ^ bω2 [MOD 7]) :
    n = 5 ∧ b ≠ 0 ∧ b1 = 0 := by
  have hn5le : n ≤ 5 := by omega
  have hf1le : f1 ≤ 5 := by omega
  have hfωle : fω ≤ 5 := by omega
  have hfω2le : fω2 ≤ 5 := by omega
  have hdn := k330c_psu_defect hQ7 (le_of_lt hb) hn5le hgn
  have hd1 := k330c_psu_defect hQ7 hb1 hf1le hg1
  have hdω := k330c_psu_defect hQ7 hbω hfωle hgω
  have hdω2 := k330c_psu_defect hQ7 hbω2 hfω2le hgω2
  have hnb : n - b = 3 := by
    rcases hdn with h | h
    · omega
    · exact h
  have hsum : (f1 - b1) + (fω - bω) + (fω2 - bω2) = 3 := by omega
  have hdω0 : fω - bω = 0 := by
    rcases hdω with h | h
    · exact h
    · exfalso; omega
  have hdω20 : fω2 - bω2 = 0 := by
    rcases hdω2 with h | h
    · exact h
    · exfalso; omega
  have hd1_3 : f1 - b1 = 3 := by
    rcases hd1 with h | h
    · omega
    · exact h
  have hf1_ge : 3 ≤ f1 := by omega
  have hn5 : n = 5 := by
    rcases hn with h | h
    · exfalso; omega
    · exact h
  have hf1_eq : f1 = 3 := by omega
  have hb1_0 : b1 = 0 := by omega
  exact ⟨hn5, by omega, hb1_0⟩

theorem psu_chain {F : Type*} [Field F] [Finite F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hn : Module.finrank F V = 4 ∨ Module.finrank F V = 5)
    (hQ7 : ¬ 7 ∣ Nat.card F ∧ ¬ 7 ∣ Nat.card F - 1 ∧ ¬ 7 ∣ Nat.card F + 1)
    (ω : F) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {x r : V ≃ₗ[F] V} (hxr : x * r = r * x) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hr : r ^ 7 = 1) (hr1 : r ≠ 1)
    (hdual : Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) =
      Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1))) :
    Module.finrank F V = 5 ∧ LinearMap.ker ((r : V →ₗ[F] V) - 1) ≠ ⊥ ∧
      LinearMap.ker ((x : V →ₗ[F] V) - 1) ⊓ LinearMap.ker ((r : V →ₗ[F] V) - 1) = ⊥ := by
  classical
  have h7 : Nat.Prime 7 := by decide
  have hcomm : ∀ v : V, x (r v) = r (x v) := by
    intro v
    have h := DFunLike.congr_fun hxr v
    simpa using h
  have hmem1 : ∀ v : V, v ∈ LinearMap.ker ((x : V →ₗ[F] V) - 1) ↔ x v = v := by
    intro v
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      LinearEquiv.coe_toLinearMap]
  have hmemω : ∀ v : V, v ∈ LinearMap.ker ((x : V →ₗ[F] V) - ω • 1) ↔ x v = ω • v := by
    intro v
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero,
      LinearEquiv.coe_toLinearMap]
  have hmemω2 : ∀ v : V, v ∈ LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1) ↔
      x v = ω ^ 2 • v := by
    intro v
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero,
      LinearEquiv.coe_toLinearMap]
  have hmemB : ∀ v : V, v ∈ LinearMap.ker ((r : V →ₗ[F] V) - 1) ↔ r v = v := by
    intro v
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      LinearEquiv.coe_toLinearMap]
  have hA1inv : ∀ w ∈ LinearMap.ker ((x : V →ₗ[F] V) - 1),
      r w ∈ LinearMap.ker ((x : V →ₗ[F] V) - 1) := by
    intro w hw
    rw [hmem1] at hw ⊢
    rw [hcomm, hw]
  have hAωinv : ∀ w ∈ LinearMap.ker ((x : V →ₗ[F] V) - ω • 1),
      r w ∈ LinearMap.ker ((x : V →ₗ[F] V) - ω • 1) := by
    intro w hw
    rw [hmemω] at hw ⊢
    rw [hcomm, hw, LinearEquiv.map_smul]
  have hAω2inv : ∀ w ∈ LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1),
      r w ∈ LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1) := by
    intro w hw
    rw [hmemω2] at hw ⊢
    rw [hcomm, hw, LinearEquiv.map_smul]
  have hBinv : ∀ w ∈ LinearMap.ker ((r : V →ₗ[F] V) - 1),
      x w ∈ LinearMap.ker ((r : V →ₗ[F] V) - 1) := by
    intro w hw
    rw [hmemB] at hw ⊢
    rw [← hcomm, hw]
  have hA1ne : LinearMap.ker ((x : V →ₗ[F] V) - 1) ≠ ⊤ := by
    intro htop
    apply hx1
    ext v
    have hv : v ∈ LinearMap.ker ((x : V →ₗ[F] V) - 1) := by rw [htop]; trivial
    rw [hmem1] at hv
    simpa using hv
  have hBne : LinearMap.ker ((r : V →ₗ[F] V) - 1) ≠ ⊤ := by
    intro htop
    apply hr1
    ext v
    have hv : v ∈ LinearMap.ker ((r : V →ₗ[F] V) - 1) := by rw [htop]; trivial
    rw [hmemB] at hv
    simpa using hv
  have hcard : ∀ W : Submodule F V, Nat.card ↥W = (Nat.card F) ^ Module.finrank F ↥W := by
    intro W
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥W)]
  have hnsum : Module.finrank F V =
      Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - 1)) +
      Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) +
      Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) := by
    have h := finrank_eq_sum_eigen x hx ω hω3 hω1 ⊤ (fun _ _ => trivial)
    rw [finrank_top, top_inf_eq, top_inf_eq, top_inf_eq] at h
    exact h
  have hbsum : Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1)) =
      Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - 1)) +
      Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) +
      Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) :=
    finrank_eq_sum_eigen x hx ω hω3 hω1 (LinearMap.ker ((r : V →ₗ[F] V) - 1)) hBinv
  have hgn0 := card_modEq_inf_ker r h7 hr ⊤ (fun _ _ => trivial)
  rw [top_inf_eq] at hgn0
  have hgn : (Nat.card F) ^ Module.finrank F V ≡
      (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1)) [MOD 7] := by
    have htop : Nat.card ↥(⊤ : Submodule F V) = (Nat.card F) ^ Module.finrank F V := by
      rw [hcard (⊤ : Submodule F V), finrank_top]
    have hB : Nat.card ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1)) =
        (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1)) :=
      hcard (LinearMap.ker ((r : V →ₗ[F] V) - 1))
    rw [htop, hB] at hgn0
    exact hgn0
  have hg1₀ := card_modEq_inf_ker r h7 hr (LinearMap.ker ((x : V →ₗ[F] V) - 1)) hA1inv
  rw [inf_comm] at hg1₀
  have hg1 : (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - 1)) ≡
      (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - 1)) [MOD 7] := by
    have h1 : Nat.card ↥(LinearMap.ker ((x : V →ₗ[F] V) - 1)) =
        (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - 1)) :=
      hcard (LinearMap.ker ((x : V →ₗ[F] V) - 1))
    have h2 : Nat.card ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
          LinearMap.ker ((x : V →ₗ[F] V) - 1)) =
        (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
          LinearMap.ker ((x : V →ₗ[F] V) - 1)) :=
      hcard (LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓ LinearMap.ker ((x : V →ₗ[F] V) - 1))
    rw [h1, h2] at hg1₀
    exact hg1₀
  have hgω₀ := card_modEq_inf_ker r h7 hr (LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) hAωinv
  rw [inf_comm] at hgω₀
  have hgω : (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) ≡
      (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) [MOD 7] := by
    have h1 : Nat.card ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) =
        (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) :=
      hcard (LinearMap.ker ((x : V →ₗ[F] V) - ω • 1))
    have h2 : Nat.card ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
          LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) =
        (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
          LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)) :=
      hcard (LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - ω • 1))
    rw [h1, h2] at hgω₀
    exact hgω₀
  have hgω2₀ := card_modEq_inf_ker r h7 hr (LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1))
    hAω2inv
  rw [inf_comm] at hgω2₀
  have hgω2 : (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) ≡
      (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) [MOD 7] := by
    have h1 : Nat.card ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) =
        (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) :=
      hcard (LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1))
    have h2 : Nat.card ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
          LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) =
        (Nat.card F) ^ Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
          LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)) :=
      hcard (LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1))
    rw [h1, h2] at hgω2₀
    exact hgω2₀
  have harith := k330c_psu_arith (Nat.card F) (Module.finrank F V)
    (Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1)))
    (Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - 1)))
    (Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)))
    (Module.finrank F ↥(LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)))
    (Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
      LinearMap.ker ((x : V →ₗ[F] V) - 1)))
    (Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
      LinearMap.ker ((x : V →ₗ[F] V) - ω • 1)))
    (Module.finrank F ↥(LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
      LinearMap.ker ((x : V →ₗ[F] V) - ω ^ 2 • 1)))
    hQ7 hn (Submodule.finrank_lt hBne) (Submodule.finrank_lt hA1ne) hnsum hbsum hdual
    (Submodule.finrank_mono inf_le_right) (Submodule.finrank_mono inf_le_right)
    (Submodule.finrank_mono inf_le_right) hgn hg1 hgω hgω2
  have hn5 := harith.1
  have hbne := harith.2.1
  have hb1zero := harith.2.2
  refine ⟨hn5, ?_, ?_⟩
  · intro hbot
    apply hbne
    rw [hbot]
    exact finrank_bot F V
  · have hB1bot : LinearMap.ker ((r : V →ₗ[F] V) - 1) ⊓
        LinearMap.ker ((x : V →ₗ[F] V) - 1) = ⊥ :=
      Submodule.finrank_eq_zero.mp hb1zero
    rw [inf_comm]
    exact hB1bot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
