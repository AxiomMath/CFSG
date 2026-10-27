module

public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.RankThree.GF2n.Tim79a34TwLower

public section

namespace CFSG.RankThree.GF2n.Tim79a.Gamma

open Matrix
open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank

private theorem tev_spForm_ba {n : ℕ} {a b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hab : spForm a b = 1) : spForm b a = -1 := by
  rw [spForm_comm a b, hab]

private theorem tev_ne_zero {n : ℕ} {a b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hab : spForm a b = 1) : a ≠ 0 := by
  rintro rfl
  rw [spForm_zero_left] at hab
  exact zero_ne_one hab

private theorem tev_corr {n : ℕ} {a b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hab : spForm a b = 1) {z : Fin n ⊕ Fin n → GaloisField 2 1} (hz : spForm a z = 0) :
    spForm a (z + spForm b z • a) = 0 ∧ spForm b (z + spForm b z • a) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [spForm_add_right, spForm_smul_right', spForm_self, hz, mul_zero, add_zero]
  · rw [spForm_add_right, spForm_smul_right', tev_spForm_ba hab]
    ring

private theorem tev_add_smul {n : ℕ} {a y : Fin n ⊕ Fin n → GaloisField 2 1}
    (hay : spForm a y = 0) (z : Fin n ⊕ Fin n → GaloisField 2 1) (k : GaloisField 2 1) :
    spForm y (z + k • a) = spForm y z := by
  rw [spForm_add_right, spForm_smul_right', spForm_eq_zero_comm hay, mul_zero, add_zero]

private theorem tev_eq_zero_of_smul {n : ℕ} {a b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hab : spForm a b = 1) {y : Fin n ⊕ Fin n → GaloisField 2 1}
    (hby : spForm b y = 0) {d : GaloisField 2 1} (hd : y = d • a) : y = 0 := by
  have h := hby
  rw [hd, spForm_smul_right', tev_spForm_ba hab] at h
  have hd0 : d = 0 := by linear_combination -h
  rw [hd, hd0, zero_smul]

private theorem tev_ne_smul {n : ℕ} {a b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hab : spForm a b = 1) {y : Fin n ⊕ Fin n → GaloisField 2 1}
    (hby : spForm b y = 0) (hy0 : y ≠ 0) : ∀ c : GaloisField 2 1, y ≠ c • a :=
  fun c hc => hy0 (tev_eq_zero_of_smul hab hby hc)

private theorem tev_dual {n : ℕ} {a b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hab : spForm a b = 1) {y : Fin n ⊕ Fin n → GaloisField 2 1}
    (hay : spForm a y = 0) (hby : spForm b y = 0) (hy0 : y ≠ 0) :
    ∃ y' : Fin n ⊕ Fin n → GaloisField 2 1,
      spForm a y' = 0 ∧ spForm b y' = 0 ∧ spForm y y' = 1 := by
  obtain ⟨u, hau, hyu⟩ := exists_dual (tev_ne_zero hab) hay (tev_ne_smul hab hby hy0)
  exact ⟨u + spForm b u • a, (tev_corr hab hau).1, (tev_corr hab hau).2,
    by rw [tev_add_smul hay, hyu]⟩

private theorem tev_eigen {n : ℕ} {a b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hab : spForm a b = 1)
    (φ : (Fin n ⊕ Fin n → GaloisField 2 1) →+ (Fin n ⊕ Fin n → GaloisField 2 1))
    (hφ : ∀ y e, spForm a y = 0 → spForm b y = 0 → spForm a e = 0 → spForm b e = 0 →
      ∃ c : GaloisField 2 1, φ (e + spForm y e • y) = φ e + spForm y (φ e) • y + c • a)
    {y : Fin n ⊕ Fin n → GaloisField 2 1} (hay : spForm a y = 0) (hby : spForm b y = 0)
    (hy0 : y ≠ 0) : ∃ l c : GaloisField 2 1, φ y = l • y + c • a := by
  obtain ⟨y', hay', hby', hyy'⟩ := tev_dual hab hay hby hy0
  obtain ⟨c, hc⟩ := hφ y y' hay hby hay' hby'
  rw [hyy', one_smul, map_add] at hc
  exact ⟨spForm y (φ y'), c, add_left_cancel (hc.trans (add_assoc _ _ _))⟩

private theorem tev_eigen_eq {n : ℕ} {a b : Fin n ⊕ Fin n → GaloisField 2 1}
    (hab : spForm a b = 1)
    (φ : (Fin n ⊕ Fin n → GaloisField 2 1) →+ (Fin n ⊕ Fin n → GaloisField 2 1))
    (hφ : ∀ y e, spForm a y = 0 → spForm b y = 0 → spForm a e = 0 → spForm b e = 0 →
      ∃ c : GaloisField 2 1, φ (e + spForm y e • y) = φ e + spForm y (φ e) • y + c • a)
    {y₁ y₂ : Fin n ⊕ Fin n → GaloisField 2 1} (h₁ : spForm a y₁ = 0)
    (h₁' : spForm b y₁ = 0) (h₂ : spForm a y₂ = 0) (h₂' : spForm b y₂ = 0)
    (h12 : spForm y₁ y₂ = 1) {l₁ l₂ c₁ c₂ : GaloisField 2 1}
    (e₁ : φ y₁ = l₁ • y₁ + c₁ • a) (e₂ : φ y₂ = l₂ • y₂ + c₂ • a) : l₁ = l₂ := by
  obtain ⟨c, hc⟩ := hφ y₁ y₂ h₁ h₁' h₂ h₂'
  rw [h12, one_smul, map_add] at hc
  have hφ1 : φ y₁ = spForm y₁ (φ y₂) • y₁ + c • a :=
    add_left_cancel (hc.trans (add_assoc _ _ _))
  have hsp : spForm y₁ (φ y₂) = l₂ := by
    rw [e₂, spForm_add_right, spForm_smul_right', spForm_smul_right', h12,
      spForm_eq_zero_comm h₁, mul_one, mul_zero, add_zero]
  rw [hsp] at hφ1
  by_contra hne
  have hd : l₁ - l₂ = 1 := (twl_gf2 _).resolve_left (sub_ne_zero.2 hne)
  have hl : l₁ = l₂ + 1 := by linear_combination hd
  rw [hl] at e₁
  have hy1 : y₁ = (c - c₁) • a := by
    linear_combination (norm := module) e₁.symm.trans hφ1
  have hy10 : y₁ = 0 := tev_eq_zero_of_smul hab h₁' hy1
  rw [hy10, spForm_zero_left] at h12
  exact zero_ne_one h12

theorem eq_smul_of_trans_equivariant {n : ℕ} (hn : 2 ≤ n)
    {a b : Fin n ⊕ Fin n → GaloisField 2 1} (hab : CaseM.spForm a b = 1)
    (φ : (Fin n ⊕ Fin n → GaloisField 2 1) →+ (Fin n ⊕ Fin n → GaloisField 2 1))
    (hφ : ∀ y e, CaseM.spForm a y = 0 → CaseM.spForm b y = 0 → CaseM.spForm a e = 0 →
      CaseM.spForm b e = 0 → ∃ c : GaloisField 2 1,
        φ (e + CaseM.spForm y e • y) = φ e + CaseM.spForm y (φ e) • y + c • a) :
    ∃ μ : GaloisField 2 1, ∀ e, CaseM.spForm a e = 0 → CaseM.spForm b e = 0 →
      ∃ c : GaloisField 2 1, φ e = μ • e + c • a := by
  obtain ⟨y₀, hy₀0, hy₀⟩ := exists_ne_zero_forall_spForm_eq_zero ![a, b]
    (by rw [Fintype.card_fin]; omega)
  have hy₀a : spForm a y₀ = 0 := hy₀ 0
  have hy₀b : spForm b y₀ = 0 := hy₀ 1
  obtain ⟨μ, _, hμ⟩ := tev_eigen hab φ hφ hy₀a hy₀b hy₀0
  refine ⟨μ, fun e hae hbe => ?_⟩
  by_cases he0 : e = 0
  · subst he0
    exact ⟨0, by simp⟩
  · obtain ⟨z, haz, hwz, hw'z⟩ := exists_perp_spForm_ne_zero_both
      (tev_ne_smul hab hbe he0) (tev_ne_smul hab hy₀b hy₀0)
    have hwz1 : spForm e z = 1 := (twl_gf2 _).resolve_left hwz
    have hw'z1 : spForm y₀ z = 1 := (twl_gf2 _).resolve_left hw'z
    obtain ⟨z', hz'a, hz'b, hez', hy₀z'⟩ : ∃ z' : Fin n ⊕ Fin n → GaloisField 2 1,
        spForm a z' = 0 ∧ spForm b z' = 0 ∧ spForm e z' = 1 ∧ spForm y₀ z' = 1 :=
      ⟨z + spForm b z • a, (tev_corr hab haz).1, (tev_corr hab haz).2,
        by rw [tev_add_smul hae]; exact hwz1, by rw [tev_add_smul hy₀a]; exact hw'z1⟩
    have hz'0 : z' ≠ 0 := by
      rintro rfl
      rw [spForm_zero_right] at hy₀z'
      exact zero_ne_one hy₀z'
    obtain ⟨l', _, hz'e⟩ := tev_eigen hab φ hφ hz'a hz'b hz'0
    obtain ⟨le, ce, hee⟩ := tev_eigen hab φ hφ hae hbe he0
    have h1 : μ = l' := tev_eigen_eq hab φ hφ hy₀a hy₀b hz'a hz'b hy₀z' hμ hz'e
    have h2 : le = l' := tev_eigen_eq hab φ hφ hae hbe hz'a hz'b hez' hee hz'e
    exact ⟨ce, by rw [hee, h2, h1]⟩

end CFSG.RankThree.GF2n.Tim79a.Gamma
