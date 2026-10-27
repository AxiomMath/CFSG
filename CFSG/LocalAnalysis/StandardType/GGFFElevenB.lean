module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal
public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
import Mathlib.GroupTheory.Sylow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped Pointwise

section RootFix

variable {G : Type} [Group G]

private lemma cjp_zero (W t : G) : cjp W (0 : Fin 3) t = t := by
  simp [cjp]

private lemma cjp_add {W : G} (hW3 : W ^ 3 = 1) (c a : Fin 3) (t : G) :
    cjp W c (cjp W a t) = cjp W (c + a) t := by
  simp only [cjp, Fin.val_add]
  have h1 : W ^ ((c : ℕ) + (a : ℕ)) = W ^ (((c : ℕ) + (a : ℕ)) % 3) :=
    pow_eq_pow_mod (n := 3) ((c : ℕ) + (a : ℕ)) hW3
  calc
    W ^ (c : ℕ) * (W ^ (a : ℕ) * t * (W ^ (a : ℕ))⁻¹) * (W ^ (c : ℕ))⁻¹
        = W ^ ((c : ℕ) + (a : ℕ)) * t * (W ^ ((c : ℕ) + (a : ℕ)))⁻¹ := by
          group
    _ = W ^ (((c : ℕ) + (a : ℕ)) % 3) * t *
          (W ^ (((c : ℕ) + (a : ℕ)) % 3))⁻¹ := by rw [h1]

private lemma conj_inj (g : G) {t u : G} (h : g * t * g⁻¹ = g * u * g⁻¹) : t = u := by
  have h' := congrArg (fun z => g⁻¹ * z * g) h
  simpa [mul_assoc] using h'

private lemma alpha_three {ρ : G} (hρ3 : ρ ^ 3 = 1) (t : G) :
    ρ * (ρ * (ρ * t * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = t := by
  have h : ρ * ρ * ρ = 1 := by
    simpa [pow_succ, mul_assoc] using hρ3
  calc
    ρ * (ρ * (ρ * t * ρ⁻¹) * ρ⁻¹) * ρ⁻¹
        = (ρ * ρ * ρ) * t * (ρ * ρ * ρ)⁻¹ := by group
    _ = t := by rw [h, one_mul, inv_one, mul_one]

private lemma alpha_inv {ρ : G} (hρ3 : ρ ^ 3 = 1) (t : G) :
    ρ⁻¹ * t * ρ = ρ * (ρ * t * ρ⁻¹) * ρ⁻¹ := by
  have h3 := alpha_three (ρ := ρ) hρ3 t
  have h4 : ρ * (ρ⁻¹ * t * ρ) * ρ⁻¹ = t := by group
  exact conj_inj ρ (h4.trans h3.symm)

private lemma fin3_sub_add_cancel (a b : Fin 3) : (b - a) + a = b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma fin3_eq_zero_of_add_eq (a c : Fin 3) (h : a + c = c + a + a) : a = 0 := by
  fin_cases a <;> fin_cases c <;> simp_all

private lemma R_ne_one {W R R' : G} (hdist : ∀ a a' : Fin 3,
    (cjp W a R = cjp W a' R → a = a') ∧
    (cjp W a R' = cjp W a' R' → a = a') ∧ cjp W a R ≠ cjp W a' R')
    (h : R = 1) : False := by
  have h01 : cjp W (0 : Fin 3) R = cjp W 1 R := by simp [cjp, h]
  exact absurd ((hdist 0 1).1 h01) (by decide)

private lemma R'_ne_one {W R R' : G} (hdist : ∀ a a' : Fin 3,
    (cjp W a R = cjp W a' R → a = a') ∧
    (cjp W a R' = cjp W a' R' → a = a') ∧ cjp W a R ≠ cjp W a' R')
    (h : R' = 1) : False := by
  have h01 : cjp W (0 : Fin 3) R' = cjp W 1 R' := by simp [cjp, h]
  exact absurd ((hdist 0 1).2.1 h01) (by decide)

private lemma alpha_R_eq (good : G → Prop) {W R R' ρ : G}
    (hW3 : W ^ 3 = 1) (hR : good R) (hR' : good R')
    (hchar : ∀ t, good t → t = 1 ∨ ∃ a : Fin 3, t = cjp W a R ∨ t = cjp W a R')
    (hdist : ∀ a a' : Fin 3, (cjp W a R = cjp W a' R → a = a') ∧
      (cjp W a R' = cjp W a' R' → a = a') ∧ cjp W a R ≠ cjp W a' R')
    (hρ3 : ρ ^ 3 = 1)
    (hρgood : ∀ t, good t → good (ρ * t * ρ⁻¹))
    (hρcjp : ∀ t (a : Fin 3), good t → ρ * cjp W a t * ρ⁻¹ = cjp W a (ρ * t * ρ⁻¹)) :
    ∃ a : Fin 3, ρ * R * ρ⁻¹ = cjp W a R := by
  have hRgood : good (ρ * R * ρ⁻¹) := hρgood R hR
  have hR'good : good (ρ * R' * ρ⁻¹) := hρgood R' hR'
  have hRne : ρ * R * ρ⁻¹ ≠ 1 := by
    intro h
    exact R_ne_one hdist (conj_inj ρ (by simpa using h))
  have hR'ne : ρ * R' * ρ⁻¹ ≠ 1 := by
    intro h
    exact R'_ne_one hdist (conj_inj ρ (by simpa using h))
  obtain ⟨a, ha | ha⟩ := (hchar _ hRgood).resolve_left hRne
  · exact ⟨a, ha⟩
  · exfalso
    obtain ⟨a', ha' | ha'⟩ := (hchar _ hR'good).resolve_left hR'ne
    · have hααR : ρ * (ρ * R * ρ⁻¹) * ρ⁻¹ = cjp W (a + a') R := by
        rw [ha, hρcjp R' a hR', ha', cjp_add hW3]
      have hαααR : ρ * (ρ * (ρ * R * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ =
          cjp W ((a + a') + a) R' := by
        rw [hααR, hρcjp R (a + a') hR, ha, cjp_add hW3]
      have hRcross : R = cjp W ((a + a') + a) R' :=
        (alpha_three hρ3 R).symm.trans hαααR
      have h0 : cjp W (0 : Fin 3) R = cjp W ((a + a') + a) R' := by
        rw [cjp_zero]
        exact hRcross
      exact (hdist 0 ((a + a') + a)).2.2 h0
    · have h1 : ρ * cjp W (a' - a) R * ρ⁻¹ = cjp W (a' - a) (cjp W a R') := by
        rw [hρcjp R (a' - a) hR, ha]
      have h2 : cjp W (a' - a) (cjp W a R') = cjp W (a' - a + a) R' := by
        rw [cjp_add hW3]
      have h3 : cjp W (a' - a) R = R' := by
        apply conj_inj ρ
        rw [h1, h2, fin3_sub_add_cancel]
        exact ha'.symm
      have h4 : cjp W (a' - a) R = cjp W (0 : Fin 3) R' := by
        rw [h3, cjp_zero]
      exact (hdist (a' - a) 0).2.2 h4

private lemma a_eq_zero (good : G → Prop) {W R R' ρ x : G} {a : Fin 3}
    (hW3 : W ^ 3 = 1) (hR : good R) (hR' : good R')
    (hcjp : ∀ t (a : Fin 3), good t → good (cjp W a t))
    (hchar : ∀ t, good t → t = 1 ∨ ∃ a : Fin 3, t = cjp W a R ∨ t = cjp W a R')
    (hdist : ∀ a a' : Fin 3, (cjp W a R = cjp W a' R → a = a') ∧
      (cjp W a R' = cjp W a' R' → a = a') ∧ cjp W a R ≠ cjp W a' R')
    (hρ3 : ρ ^ 3 = 1)
    (hρcjp : ∀ t (a : Fin 3), good t → ρ * cjp W a t * ρ⁻¹ = cjp W a (ρ * t * ρ⁻¹))
    (hxgood : ∀ t, good t → good (x * t * x⁻¹))
    (hxcjp : ∀ t (a : Fin 3), x * cjp W a t * x⁻¹ = cjp W a (x * t * x⁻¹))
    (hy : ∀ t, good t → x * ρ * x⁻¹ * ρ * t = t * (x * ρ * x⁻¹ * ρ))
    (ha : ρ * R * ρ⁻¹ = cjp W a R)
    (ha' : ρ * R' * ρ⁻¹ = cjp W a R') : a = 0 := by
  set V : G := x * R * x⁻¹ with hV
  have hVgood : good V := hxgood R hR
  have hVne : V ≠ 1 := by
    intro hV1
    have hxR : x * R * x⁻¹ = x * 1 * x⁻¹ := by
      rw [← hV]
      simpa using hV1
    exact R_ne_one hdist (conj_inj x hxR)
  obtain ⟨c, hc | hc⟩ := (hchar V hVgood).resolve_left hVne
  · have hleft : x * (ρ * R * ρ⁻¹) * x⁻¹ = cjp W (a + c) R := by
      rw [ha, hxcjp R a, ← hV, hc, cjp_add hW3]
    have hαV : ρ * V * ρ⁻¹ = cjp W (c + a) R := by
      rw [hc, hρcjp R c hR, ha, cjp_add hW3]
    have hααV : ρ * (ρ * V * ρ⁻¹) * ρ⁻¹ = cjp W ((c + a) + a) R := by
      rw [hαV, hρcjp R (c + a) hR, ha, cjp_add hW3]
    have hg : good (cjp W ((c + a) + a) R) := by
      have h := hcjp (cjp W a R) (c + a) (hcjp R a hR)
      rwa [cjp_add hW3] at h
    have hright : x * (ρ * R * ρ⁻¹) * x⁻¹ = cjp W ((c + a) + a) R := by
      calc
        x * (ρ * R * ρ⁻¹) * x⁻¹
            = (x * ρ * x⁻¹) * (x * R * x⁻¹) * (x * ρ * x⁻¹)⁻¹ := by group
        _ = (x * ρ * x⁻¹) * V * (x * ρ * x⁻¹)⁻¹ := by rw [← hV]
        _ = (x * ρ * x⁻¹ * ρ) * (ρ⁻¹ * V * ρ) * (x * ρ * x⁻¹ * ρ)⁻¹ := by
              group
        _ = (x * ρ * x⁻¹ * ρ) * (cjp W ((c + a) + a) R) *
              (x * ρ * x⁻¹ * ρ)⁻¹ := by rw [alpha_inv hρ3 V, hααV]
        _ = cjp W ((c + a) + a) R := by
              rw [hy _ hg]
              group
    have hfin : cjp W (a + c) R = cjp W ((c + a) + a) R := by
      rw [← hleft, hright]
    exact fin3_eq_zero_of_add_eq a c ((hdist (a + c) ((c + a) + a)).1 hfin)
  · have hleft : x * (ρ * R * ρ⁻¹) * x⁻¹ = cjp W (a + c) R' := by
      rw [ha, hxcjp R a, ← hV, hc, cjp_add hW3]
    have hαV : ρ * V * ρ⁻¹ = cjp W (c + a) R' := by
      rw [hc, hρcjp R' c hR', ha', cjp_add hW3]
    have hααV : ρ * (ρ * V * ρ⁻¹) * ρ⁻¹ = cjp W ((c + a) + a) R' := by
      rw [hαV, hρcjp R' (c + a) hR', ha', cjp_add hW3]
    have hg : good (cjp W ((c + a) + a) R') := by
      have h := hcjp (cjp W a R') (c + a) (hcjp R' a hR')
      rwa [cjp_add hW3] at h
    have hright : x * (ρ * R * ρ⁻¹) * x⁻¹ = cjp W ((c + a) + a) R' := by
      calc
        x * (ρ * R * ρ⁻¹) * x⁻¹
            = (x * ρ * x⁻¹) * (x * R * x⁻¹) * (x * ρ * x⁻¹)⁻¹ := by group
        _ = (x * ρ * x⁻¹) * V * (x * ρ * x⁻¹)⁻¹ := by rw [← hV]
        _ = (x * ρ * x⁻¹ * ρ) * (ρ⁻¹ * V * ρ) * (x * ρ * x⁻¹ * ρ)⁻¹ := by
              group
        _ = (x * ρ * x⁻¹ * ρ) * (cjp W ((c + a) + a) R') *
              (x * ρ * x⁻¹ * ρ)⁻¹ := by rw [alpha_inv hρ3 V, hααV]
        _ = cjp W ((c + a) + a) R' := by
              rw [hy _ hg]
              group
    have hfin : cjp W (a + c) R' = cjp W ((c + a) + a) R' := by
      rw [← hleft, hright]
    exact fin3_eq_zero_of_add_eq a c ((hdist (a + c) ((c + a) + a)).2.1 hfin)

private lemma alpha_R'_eq (good : G → Prop) {W R R' ρ : G} {a : Fin 3}
    (hW3 : W ^ 3 = 1) (hR' : good R')
    (hchar : ∀ t, good t → t = 1 ∨ ∃ a : Fin 3, t = cjp W a R ∨ t = cjp W a R')
    (hdist : ∀ a a' : Fin 3, (cjp W a R = cjp W a' R → a = a') ∧
      (cjp W a R' = cjp W a' R' → a = a') ∧ cjp W a R ≠ cjp W a' R')
    (hρgood : ∀ t, good t → good (ρ * t * ρ⁻¹))
    (hρcjp : ∀ t (a : Fin 3), good t → ρ * cjp W a t * ρ⁻¹ = cjp W a (ρ * t * ρ⁻¹))
    (ha : ρ * R * ρ⁻¹ = cjp W a R) :
    ∃ a' : Fin 3, ρ * R' * ρ⁻¹ = cjp W a' R' := by
  have hR'good : good (ρ * R' * ρ⁻¹) := hρgood R' hR'
  have hR'ne : ρ * R' * ρ⁻¹ ≠ 1 := by
    intro h
    exact R'_ne_one hdist (conj_inj ρ (by simpa using h))
  obtain ⟨a', ha' | ha'⟩ := (hchar _ hR'good).resolve_left hR'ne
  · exfalso
    have h1 : ρ * cjp W (a - a') R' * ρ⁻¹ = cjp W (a - a') (cjp W a' R) := by
      rw [hρcjp R' (a - a') hR', ha']
    have h2 : cjp W (a - a') (cjp W a' R) = cjp W (a - a' + a') R := by
      rw [cjp_add hW3]
    have h3 : cjp W (a - a') R' = R := by
      apply conj_inj ρ
      rw [h1, h2, fin3_sub_add_cancel]
      exact ha.symm
    have h4 : cjp W (a - a') R' = cjp W (0 : Fin 3) R := by
      rw [h3, cjp_zero]
    exact (hdist 0 (a - a')).2.2 h4.symm
  · exact ⟨a', ha'⟩

private lemma same_shift {W R R' ρ : G} {a a' : Fin 3}
    (hbraid : R * R' * R = R' * R * R')
    (hbraid_eq : ∀ a a' : Fin 3, cjp W a R * cjp W a' R' * cjp W a R =
      cjp W a' R' * cjp W a R * cjp W a' R' → a = a')
    (ha : ρ * R * ρ⁻¹ = cjp W a R)
    (ha' : ρ * R' * ρ⁻¹ = cjp W a' R') : a = a' := by
  apply hbraid_eq a a'
  calc
    cjp W a R * cjp W a' R' * cjp W a R
        = (ρ * R * ρ⁻¹) * (ρ * R' * ρ⁻¹) * (ρ * R * ρ⁻¹) := by rw [ha, ha']
    _ = ρ * (R * R' * R) * ρ⁻¹ := by group
    _ = ρ * (R' * R * R') * ρ⁻¹ := by rw [hbraid]
    _ = (ρ * R' * ρ⁻¹) * (ρ * R * ρ⁻¹) * (ρ * R' * ρ⁻¹) := by group
    _ = cjp W a' R' * cjp W a R * cjp W a' R' := by rw [ha, ha']

private theorem root_fix (good : G → Prop) {W R R' ρ x : G}
    (hW3 : W ^ 3 = 1)
    (hR : good R) (hR' : good R')
    (hcjp : ∀ t (a : Fin 3), good t → good (cjp W a t))
    (hchar : ∀ t, good t → t = 1 ∨ ∃ a : Fin 3, t = cjp W a R ∨ t = cjp W a R')
    (hdist : ∀ a a' : Fin 3, (cjp W a R = cjp W a' R → a = a') ∧
      (cjp W a R' = cjp W a' R' → a = a') ∧ cjp W a R ≠ cjp W a' R')
    (hbraid : R * R' * R = R' * R * R')
    (hbraid_eq : ∀ a a' : Fin 3, cjp W a R * cjp W a' R' * cjp W a R =
      cjp W a' R' * cjp W a R * cjp W a' R' → a = a')
    (hρ3 : ρ ^ 3 = 1)
    (hρgood : ∀ t, good t → good (ρ * t * ρ⁻¹))
    (hρcjp : ∀ t (a : Fin 3), good t → ρ * cjp W a t * ρ⁻¹ = cjp W a (ρ * t * ρ⁻¹))
    (hxgood : ∀ t, good t → good (x * t * x⁻¹))
    (hxcjp : ∀ t (a : Fin 3), x * cjp W a t * x⁻¹ = cjp W a (x * t * x⁻¹))
    (hy : ∀ t, good t → x * ρ * x⁻¹ * ρ * t = t * (x * ρ * x⁻¹ * ρ)) :
    ρ * R = R * ρ ∧ ρ * R' = R' * ρ := by
  obtain ⟨a, ha⟩ := alpha_R_eq good hW3 hR hR' hchar hdist hρ3 hρgood hρcjp
  obtain ⟨a', ha'⟩ := alpha_R'_eq good hW3 hR' hchar hdist hρgood hρcjp ha
  have haa' : a = a' := same_shift hbraid hbraid_eq ha ha'
  rw [← haa'] at ha'
  have ha0 : a = 0 :=
    a_eq_zero good hW3 hR hR' hcjp hchar hdist hρ3 hρcjp hxgood hxcjp hy ha ha'
  have hRfix : ρ * R * ρ⁻¹ = R := by rw [ha, ha0, cjp_zero]
  have hR'fix : ρ * R' * ρ⁻¹ = R' := by rw [ha', ha0, cjp_zero]
  constructor
  · calc ρ * R = ρ * R * ρ⁻¹ * ρ := by group
      _ = R * ρ := by rw [hRfix]
  · calc ρ * R' = ρ * R' * ρ⁻¹ * ρ := by group
      _ = R' * ρ := by rw [hR'fix]

end RootFix

section SylConj

variable {G : Type} [Group G] [Finite G]

private theorem exists_conj_pow_of_sylow7 (K₁ : Subgroup G)
    (h7 : ∀ P : Subgroup G, P ≤ K₁ → IsPGroup 7 P → Nat.card P ≤ 7)
    {g₀ : G} (hg₀ : g₀ ∈ K₁) (hg7 : g₀ ^ 7 = 1) (hg1 : g₀ ≠ 1)
    {q : G} (hq : ∀ t ∈ K₁, q * t * q⁻¹ ∈ K₁) :
    ∃ k ∈ K₁, ∃ j : ℕ, ¬ 7 ∣ j ∧ q * g₀ * q⁻¹ = k * g₀ ^ j * k⁻¹ := by
  classical
  have hprime : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hord : orderOf g₀ = 7 := @orderOf_eq_prime G _ g₀ 7 hprime hg7 hg1
  have hg₁K : q * g₀ * q⁻¹ ∈ K₁ := hq g₀ hg₀
  have hg₁pow : (q * g₀ * q⁻¹) ^ 7 = 1 := by
    rw [← MulAut.conj_apply q g₀, ← map_pow, hg7, map_one]
  have hg₁1 : q * g₀ * q⁻¹ ≠ 1 := by
    intro h
    have hg0 : g₀ = 1 := by
      have h' : q⁻¹ * (q * g₀ * q⁻¹) * q = 1 := by
        simpa using congrArg (fun x => q⁻¹ * x * q) h
      rwa [show q⁻¹ * (q * g₀ * q⁻¹) * q = g₀ by group] at h'
    exact hg1 hg0
  have hord₁ : orderOf (q * g₀ * q⁻¹) = 7 :=
    @orderOf_eq_prime G _ (q * g₀ * q⁻¹) 7 hprime hg₁pow hg₁1
  let P : Subgroup G := Subgroup.zpowers g₀
  let Q : Subgroup G := Subgroup.zpowers (q * g₀ * q⁻¹)
  have hPK : P ≤ K₁ := Subgroup.zpowers_le.mpr hg₀
  have hQK : Q ≤ K₁ := Subgroup.zpowers_le.mpr hg₁K
  have hPcard : Nat.card P = 7 := by
    show Nat.card (Subgroup.zpowers g₀) = 7
    rw [Nat.card_zpowers, hord]
  have hQcard : Nat.card Q = 7 := by
    show Nat.card (Subgroup.zpowers (q * g₀ * q⁻¹)) = 7
    rw [Nat.card_zpowers, hord₁]
  let P' : Subgroup ↥K₁ := P.subgroupOf K₁
  let Q' : Subgroup ↥K₁ := Q.subgroupOf K₁
  have hP'card : Nat.card P' = 7 := by
    show Nat.card (P.subgroupOf K₁) = 7
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv, hPcard]
  have hQ'card : Nat.card Q' = 7 := by
    show Nat.card (Q.subgroupOf K₁) = 7
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hQcard]
  have hP'grp : IsPGroup 7 P' := IsPGroup.of_card (n := 1) (by rw [hP'card]; norm_num)
  obtain ⟨S, hP'S⟩ := hP'grp.exists_le_sylow
  have hSle : (S : Subgroup ↥K₁).map K₁.subtype ≤ K₁ :=
    Subgroup.map_subtype_le (S : Subgroup ↥K₁)
  have hSgrp : IsPGroup 7 ((S : Subgroup ↥K₁).map K₁.subtype) :=
    S.isPGroup'.map K₁.subtype
  have hSbound : Nat.card (S : Subgroup ↥K₁) ≤ 7 := by
    have h := h7 _ hSle hSgrp
    rwa [Subgroup.card_map_of_injective K₁.subtype_injective] at h
  have hP'eqS : P' = S :=
    Subgroup.eq_of_le_of_card_ge hP'S (by simpa [hP'card] using hSbound)
  have hQ'grp : IsPGroup 7 Q' := IsPGroup.of_card (n := 1) (by rw [hQ'card]; norm_num)
  obtain ⟨T, hQ'T⟩ := hQ'grp.exists_le_sylow
  have hTle : (T : Subgroup ↥K₁).map K₁.subtype ≤ K₁ :=
    Subgroup.map_subtype_le (T : Subgroup ↥K₁)
  have hTgrp : IsPGroup 7 ((T : Subgroup ↥K₁).map K₁.subtype) :=
    T.isPGroup'.map K₁.subtype
  have hTbound : Nat.card (T : Subgroup ↥K₁) ≤ 7 := by
    have h := h7 _ hTle hTgrp
    rwa [Subgroup.card_map_of_injective K₁.subtype_injective] at h
  have hQ'eqT : Q' = T :=
    Subgroup.eq_of_le_of_card_ge hQ'T (by simpa [hQ'card] using hTbound)
  have hpre : MulAction.IsPretransitive (↥K₁) (Sylow 7 ↥K₁) :=
    @Sylow.isPretransitive_of_finite 7 (↥K₁) _ hprime _
  obtain ⟨k, hk⟩ :=
    @MulAction.exists_smul_eq (↥K₁) (Sylow 7 ↥K₁) _ hpre S T
  have hQ'P' : Q' = MulAut.conj k • P' := by
    rw [hQ'eqT, ← hk, Sylow.coe_subgroup_smul, ← hP'eqS]
  have hmemQ' : (⟨q * g₀ * q⁻¹, hg₁K⟩ : ↥K₁) ∈ Q' :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _)
  rw [hQ'P'] at hmemQ'
  rw [Subgroup.mem_smul_pointwise_iff_exists] at hmemQ'
  obtain ⟨s, hsP', hsk⟩ := hmemQ'
  have hsP : (s : G) ∈ P := Subgroup.mem_subgroupOf.mp hsP'
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hsP
  let j : ℕ := (i % 7).toNat
  have hj_nonneg : 0 ≤ i % 7 := Int.emod_nonneg i (by norm_num)
  have hj_lt : j < 7 := by
    have h := Int.emod_lt_of_pos i (by norm_num : (0 : ℤ) < 7)
    omega
  have hj_cast : (j : ℤ) = i % ((7 : ℕ) : ℤ) := by
    simp [j, Int.toNat_of_nonneg hj_nonneg]
  have hpow : g₀ ^ i = g₀ ^ j := by
    rw [zpow_eq_zpow_emod' i hg7, ← hj_cast, zpow_natCast]
  have hval : (k : G) * (s : G) * (k : G)⁻¹ = q * g₀ * q⁻¹ := by
    have := congrArg (Subtype.val : ↥K₁ → G) hsk
    simpa [MulAut.conj_apply] using this
  have hval' : (k : G) * g₀ ^ j * (k : G)⁻¹ = q * g₀ * q⁻¹ := by
    rw [← hi, hpow] at hval
    exact hval
  refine ⟨k, k.2, j, ?_, hval'.symm⟩
  intro hdvd
  have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hj_lt
  have hone : q * g₀ * q⁻¹ = 1 := by
    rw [← hval', hj0, pow_zero]
    simp
  exact hg₁1 hone

end SylConj

end CFSG.StandardType.GGFF

namespace CFSG.StandardType.GGFF.Setting

open SettingCore

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] [Finite G] {b : G} {K : Subgroup G} {z : Fin 3 → K}

private def RootGood (K : Subgroup G) (z : Fin 3 → K) (j : Fin 2) (t : G) : Prop :=
  t ∈ K ∧ t * t = 1 ∧ t * rootK₁ (zs z) j = rootK₁ (zs z) j * t ∧
    t * rootK₂ (zs z) j = rootK₂ (zs z) j * t ∧ RootRel (rootW (zs z) j) t

omit [Finite G] in
private lemma coe_rootW (j : Fin 2) : ((rootW z j : K) : G) = rootW (zs z) j := by
  fin_cases j <;> rfl

omit [Finite G] in
private lemma coe_rootK₁ (j : Fin 2) : ((rootK₁ z j : K) : G) = rootK₁ (zs z) j := by
  fin_cases j <;> rfl

omit [Finite G] in
private lemma coe_rootK₂ (j : Fin 2) : ((rootK₂ z j : K) : G) = rootK₂ (zs z) j := by
  fin_cases j <;> rfl

omit [Finite G] in
private lemma coe_cjp (w u : K) (a : Fin 3) :
    ((cjp w a u : K) : G) = cjp (w : G) a (u : G) := by
  simp only [cjp, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]

omit [Finite G] in
private lemma rootRel_coe_iff (w u : K) : RootRel (w : G) (u : G) ↔ RootRel w u := by
  rw [RootRel, RootRel]
  constructor
  · intro h
    exact Subtype.ext (by
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] using h)
  · intro h
    have := congrArg (Subtype.val : K → G) h
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] using this

omit [Finite G] in
private lemma commute_self_mul (h : Setting b K z) (i j : Fin 3) :
    Commute (zs z i) (zs z i * zs z j) := by
  show zs z i * (zs z i * zs z j) = zs z i * zs z j * zs z i
  calc zs z i * (zs z i * zs z j) = zs z i * (zs z j * zs z i) := by rw [h.zs_comm i j]
    _ = zs z i * zs z j * zs z i := by rw [mul_assoc]

omit [Finite G] in
private lemma cjp_mem {W t : G} (hW : W ∈ K) (ht : t ∈ K) (a : Fin 3) :
    cjp W a t ∈ K := by
  simp only [cjp]
  exact K.mul_mem (K.mul_mem (K.pow_mem hW _) ht) (K.inv_mem (K.pow_mem hW _))

omit [Finite G] in
private lemma cjp_involution {W t : G} (ht : t * t = 1) (a : Fin 3) :
    cjp W a t * cjp W a t = 1 := by
  simp only [cjp]
  calc W ^ (a : ℕ) * t * (W ^ (a : ℕ))⁻¹ * (W ^ (a : ℕ) * t * (W ^ (a : ℕ))⁻¹)
      = W ^ (a : ℕ) * (t * t) * (W ^ (a : ℕ))⁻¹ := by group
    _ = 1 := by rw [ht]; group

private lemma cjp_comm {H : Type} [Group H] {w t k : H} (hw : Commute w k)
    (ht : Commute t k) (a : Fin 3) : Commute (cjp w a t) k := by
  have h1 : Commute (w ^ (a : ℕ)) k := hw.pow_left _
  have h2 : Commute ((w ^ (a : ℕ))⁻¹) k := h1.inv_left
  have h3 : Commute (w ^ (a : ℕ) * t) k := h1.mul_left ht
  have h4 : Commute (w ^ (a : ℕ) * t * (w ^ (a : ℕ))⁻¹) k := h3.mul_left h2
  simpa only [cjp] using h4

private lemma rootRel_conj {H : Type} [Group H] {w t x : H} (hx : Commute x w)
    (h : RootRel w t) : RootRel w (x * t * x⁻¹) := by
  rw [RootRel] at h ⊢
  rw [pow_two] at h ⊢
  have hx' : x * w * x⁻¹ = w := by rw [hx.eq]; group
  have hx2 : x * (w * w) * x⁻¹ = w * w := by
    calc x * (w * w) * x⁻¹ = (x * w * x⁻¹) * (x * w * x⁻¹) := by group
      _ = w * w := by rw [hx']
  have e1 : w * (x * t * x⁻¹) * w⁻¹ = x * (w * t * w⁻¹) * x⁻¹ := by
    conv_lhs => rw [show w = x * w * x⁻¹ from hx'.symm]
    group
  have e2 : (w * w) * (x * t * x⁻¹) * (w * w)⁻¹ =
      x * ((w * w) * t * (w * w)⁻¹) * x⁻¹ := by
    conv_lhs => rw [show w * w = x * (w * w) * x⁻¹ from hx2.symm]
    group
  calc (x * t * x⁻¹) * (w * (x * t * x⁻¹) * w⁻¹)
      = (x * t * x⁻¹) * (x * (w * t * w⁻¹) * x⁻¹) := by rw [e1]
    _ = x * (t * (w * t * w⁻¹)) * x⁻¹ := by group
    _ = x * ((w * w) * t * (w * w)⁻¹) * x⁻¹ := by rw [h]
    _ = (w * w) * (x * t * x⁻¹) * (w * w)⁻¹ := by rw [e2]

private lemma rootRel_cjp {H : Type} [Group H] {w t : H} (h : RootRel w t) (a : Fin 3) :
    RootRel w (cjp w a t) := by
  have hx : Commute (w ^ (a : ℕ)) w := (Commute.refl w).pow_left _
  simpa only [cjp] using rootRel_conj hx h

omit [Finite G] in
private lemma rootGood_cjp (j : Fin 2) (hWmem : rootW (zs z) j ∈ K)
    (hWk1 : Commute (rootW (zs z) j) (rootK₁ (zs z) j))
    (hWk2 : Commute (rootW (zs z) j) (rootK₂ (zs z) j))
    {t : G} (ht : RootGood K z j t) (a : Fin 3) :
    RootGood K z j (cjp (rootW (zs z) j) a t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact cjp_mem hWmem ht.1 a
  · exact cjp_involution ht.2.1 a
  · exact (cjp_comm hWk1 (show Commute t (rootK₁ (zs z) j) from ht.2.2.1) a).eq
  · exact (cjp_comm hWk2 (show Commute t (rootK₂ (zs z) j) from ht.2.2.2.1) a).eq
  · exact rootRel_cjp ht.2.2.2.2 a

omit [Finite G] in
private theorem rootGood_facts (h : Setting b K z) {π x₀ : K} {r r' : Fin 2 → K}
    (hB : ModelNB K z π x₀ r r') (j : Fin 2) :
    rootW (zs z) j ^ 3 = 1 ∧ RootGood K z j (r j) ∧ RootGood K z j (r' j) ∧
    (∀ t (a : Fin 3), RootGood K z j t → RootGood K z j (cjp (rootW (zs z) j) a t)) ∧
    (∀ t, RootGood K z j t → t = 1 ∨ ∃ a : Fin 3, t = cjp (rootW (zs z) j) a (r j) ∨
      t = cjp (rootW (zs z) j) a (r' j)) ∧
    (∀ a a' : Fin 3, (cjp (rootW (zs z) j) a (r j) = cjp (rootW (zs z) j) a' (r j) → a = a') ∧
      (cjp (rootW (zs z) j) a (r' j) = cjp (rootW (zs z) j) a' (r' j) → a = a') ∧
      cjp (rootW (zs z) j) a (r j) ≠ cjp (rootW (zs z) j) a' (r' j)) ∧
    ((r j : G) * r' j * r j = r' j * r j * r' j) ∧
    (∀ a a' : Fin 3, cjp (rootW (zs z) j) a (r j) * cjp (rootW (zs z) j) a' (r' j) *
      cjp (rootW (zs z) j) a (r j) = cjp (rootW (zs z) j) a' (r' j) *
      cjp (rootW (zs z) j) a (r j) * cjp (rootW (zs z) j) a' (r' j) → a = a') := by
  have hW3 : rootW (zs z) j ^ 3 = 1 := by
    fin_cases j
    · simpa [rootW] using h.zs_pow 0
    · simpa [rootW] using h.zs_pow 1
  have hWmem : rootW (zs z) j ∈ K := by
    fin_cases j
    · exact zs_mem z 0
    · exact zs_mem z 1
  have hWk1 : Commute (rootW (zs z) j) (rootK₁ (zs z) j) := by
    fin_cases j
    · exact commute_self_mul h 0 1
    · exact commute_self_mul h 1 2
  have hWk2 : Commute (rootW (zs z) j) (rootK₂ (zs z) j) := by
    fin_cases j
    · exact h.zs_comm 0 2
    · exact h.zs_comm 1 0
  have hr : RootGood K z j (r j) := by
    refine ⟨(r j).2, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg Subtype.val (hB.root_sq j).1
    · simpa only [Subgroup.coe_mul, coe_rootK₁] using congrArg Subtype.val (hB.root_comm j).1
    · simpa only [Subgroup.coe_mul, coe_rootK₂] using congrArg Subtype.val (hB.root_comm j).2.1
    · simpa only [coe_rootW] using (rootRel_coe_iff (rootW z j) (r j)).2 (hB.root_rel j).1
  have hr' : RootGood K z j (r' j) := by
    refine ⟨(r' j).2, ?_, ?_, ?_, ?_⟩
    · simpa using congrArg Subtype.val (hB.root_sq j).2
    · simpa only [Subgroup.coe_mul, coe_rootK₁] using congrArg Subtype.val (hB.root_comm j).2.2.1
    · simpa only [Subgroup.coe_mul, coe_rootK₂] using congrArg Subtype.val (hB.root_comm j).2.2.2
    · simpa only [coe_rootW] using (rootRel_coe_iff (rootW z j) (r' j)).2 (hB.root_rel j).2
  have hcjp : ∀ t (a : Fin 3), RootGood K z j t → RootGood K z j (cjp (rootW (zs z) j) a t) :=
    fun t a ht => rootGood_cjp j hWmem hWk1 hWk2 ht a
  have hchar : ∀ t, RootGood K z j t → t = 1 ∨ ∃ a : Fin 3,
      t = cjp (rootW (zs z) j) a (r j) ∨ t = cjp (rootW (zs z) j) a (r' j) := by
    intro t ht
    let u : K := ⟨t, ht.1⟩
    have hu2 : u * u = 1 := by
      refine Subtype.ext ?_
      simpa using ht.2.1
    have hc1 : u * rootK₁ z j = rootK₁ z j * u := by
      refine Subtype.ext ?_
      simpa only [Subgroup.coe_mul, coe_rootK₁] using ht.2.2.1
    have hc2 : u * rootK₂ z j = rootK₂ z j * u := by
      refine Subtype.ext ?_
      simpa only [Subgroup.coe_mul, coe_rootK₂] using ht.2.2.2.1
    have hrel : RootRel (rootW z j) u := by
      refine (rootRel_coe_iff (rootW z j) u).1 ?_
      simpa only [coe_rootW] using ht.2.2.2.2
    rcases hB.root_char j u hu2 hc1 hc2 hrel with h1 | ⟨a, h2 | h2⟩
    · left
      exact congrArg Subtype.val h1
    · right
      refine ⟨a, Or.inl ?_⟩
      simpa only [coe_cjp, coe_rootW] using congrArg Subtype.val h2
    · right
      refine ⟨a, Or.inr ?_⟩
      simpa only [coe_cjp, coe_rootW] using congrArg Subtype.val h2
  refine ⟨hW3, hr, hr', hcjp, hchar, ?_, ?_, ?_⟩
  · intro a a'
    refine ⟨?_, ?_, ?_⟩
    · intro heq
      refine (hB.root_dist j a a').1 ?_
      refine Subtype.ext ?_
      simpa only [coe_cjp, coe_rootW] using heq
    · intro heq
      refine (hB.root_dist j a a').2.1 ?_
      refine Subtype.ext ?_
      simpa only [coe_cjp, coe_rootW] using heq
    · intro heq
      exact (hB.root_dist j a a').2.2 (by
        refine Subtype.ext ?_
        simpa only [coe_cjp, coe_rootW] using heq)
  · simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hB.braid j)
  · intro a a' heq
    exact hB.braid_eq j a a' (by
      refine Subtype.ext ?_
      simpa only [Subgroup.coe_mul, coe_cjp, coe_rootW] using heq)

omit [Finite G] in
private lemma zeta_comm_zs (h : Setting b K z) (i : Fin 3) :
    Commute (zetaOf (zs z)) (zs z i) :=
  Commute.mul_left (Commute.mul_left (h.zs_comm 0 i) (h.zs_comm 1 i)) (h.zs_comm 2 i)

omit [Finite G] in
private lemma b_comm_zs (h : Setting b K z) (i : Fin 3) : Commute b (zs z i) :=
  (h.comm_of_mem (zs_mem z i)).symm

omit [Finite G] in
private lemma inv_bz_comm_zs (h : Setting b K z) (i : Fin 3) :
    Commute ((b * zetaOf (zs z))⁻¹) (zs z i) :=
  (Commute.mul_left (b_comm_zs h i) (zeta_comm_zs h i)).inv_left

omit [Finite G] in
private lemma inv_bz_comm_rootW (h : Setting b K z) (j : Fin 2) :
    Commute ((b * zetaOf (zs z))⁻¹) (rootW (zs z) j) := by
  fin_cases j
  · exact inv_bz_comm_zs h 0
  · exact inv_bz_comm_zs h 1

omit [Finite G] in
private lemma zeta_eq_rootK₁_mul_rootK₂ (h : Setting b K z) (j : Fin 2) :
    zetaOf (zs z) = rootK₁ (zs z) j * rootK₂ (zs z) j := by
  fin_cases j
  · rfl
  · show zs z 0 * zs z 1 * zs z 2 = zs z 1 * zs z 2 * zs z 0
    calc zs z 0 * zs z 1 * zs z 2
        = zs z 0 * (zs z 1 * zs z 2) := by rw [mul_assoc]
      _ = (zs z 1 * zs z 2) * zs z 0 :=
          (Commute.mul_right (h.zs_comm 0 1) (h.zs_comm 0 2)).eq

omit [Finite G] in
private lemma conj_rootW {ρ : G}
    (hρz : ∀ i, ρ * zs z i * ρ⁻¹ = zs z i * (b * zetaOf (zs z))⁻¹) (j : Fin 2) :
    ρ * rootW (zs z) j * ρ⁻¹ = rootW (zs z) j * (b * zetaOf (zs z))⁻¹ := by
  fin_cases j
  · exact hρz 0
  · exact hρz 1

omit [Finite G] in
private lemma conj_rootK₂ {ρ : G}
    (hρz : ∀ i, ρ * zs z i * ρ⁻¹ = zs z i * (b * zetaOf (zs z))⁻¹) (j : Fin 2) :
    ρ * rootK₂ (zs z) j * ρ⁻¹ = rootK₂ (zs z) j * (b * zetaOf (zs z))⁻¹ := by
  fin_cases j
  · exact hρz 2
  · exact hρz 0

omit [Finite G] in
private lemma conj_rootK₁ (h : Setting b K z) {ρ : G}
    (hρz : ∀ i, ρ * zs z i * ρ⁻¹ = zs z i * (b * zetaOf (zs z))⁻¹) (j : Fin 2) :
    ρ * rootK₁ (zs z) j * ρ⁻¹ =
      rootK₁ (zs z) j * (b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹ := by
  have hc0 : Commute ((b * zetaOf (zs z))⁻¹) (zs z 0) := inv_bz_comm_zs h 0
  have hc1 : Commute ((b * zetaOf (zs z))⁻¹) (zs z 1) := inv_bz_comm_zs h 1
  have hc2 : Commute ((b * zetaOf (zs z))⁻¹) (zs z 2) := inv_bz_comm_zs h 2
  fin_cases j
  · show ρ * (zs z 0 * zs z 1) * ρ⁻¹ =
        zs z 0 * zs z 1 * (b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹
    calc ρ * (zs z 0 * zs z 1) * ρ⁻¹
        = (ρ * zs z 0 * ρ⁻¹) * (ρ * zs z 1 * ρ⁻¹) := by group
      _ = (zs z 0 * (b * zetaOf (zs z))⁻¹) * (zs z 1 * (b * zetaOf (zs z))⁻¹) := by
            rw [hρz 0, hρz 1]
      _ = zs z 0 * zs z 1 * (b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹ := by
            rw [Commute.mul_mul_mul_comm hc1 (zs z 0) ((b * zetaOf (zs z))⁻¹)]
            group
  · show ρ * (zs z 1 * zs z 2) * ρ⁻¹ =
        zs z 1 * zs z 2 * (b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹
    calc ρ * (zs z 1 * zs z 2) * ρ⁻¹
        = (ρ * zs z 1 * ρ⁻¹) * (ρ * zs z 2 * ρ⁻¹) := by group
      _ = (zs z 1 * (b * zetaOf (zs z))⁻¹) * (zs z 2 * (b * zetaOf (zs z))⁻¹) := by
            rw [hρz 1, hρz 2]
      _ = zs z 1 * zs z 2 * (b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹ := by
            rw [Commute.mul_mul_mul_comm hc2 (zs z 1) ((b * zetaOf (zs z))⁻¹)]
            group

omit [Finite G] in
private lemma mul_comm_conj_mul_inv {w x v : G} (hxv : Commute x v) :
    w * x * v * (w * x)⁻¹ = w * v * w⁻¹ := by
  have h1 : w * x * v * (w * x)⁻¹ = w * (x * v * x⁻¹) * w⁻¹ := by group
  rw [h1, hxv.mul_inv_cancel]

omit [Finite G] in
private lemma rootGood_conj_rho_aux (h : Setting b K z)
    (hmem : ∀ c ∈ Cen b, ∀ m : ℕ, c ^ 2 ^ m = 1 → c ∈ K)
    {ρ : G} (hρb : ρ * b * ρ⁻¹ = b * zetaOf (zs z) ^ 2)
    (hρζ : ρ * zetaOf (zs z) * ρ⁻¹ = zetaOf (zs z))
    (hρz : ∀ i, ρ * zs z i * ρ⁻¹ = zs z i * (b * zetaOf (zs z))⁻¹)
    (j : Fin 2) {t : G} (ht : RootGood K z j t) :
    ρ * t * ρ⁻¹ ∈ K ∧ (ρ * t * ρ⁻¹) * (ρ * t * ρ⁻¹) = 1 ∧
      Commute (ρ * t * ρ⁻¹) (rootK₁ (zs z) j) ∧
      Commute (ρ * t * ρ⁻¹) (rootK₂ (zs z) j) ∧
      RootRel (rootW (zs z) j) (ρ * t * ρ⁻¹) := by
  obtain ⟨htK, ht2, htk1, htk2, htrel⟩ := ht
  have htb : Commute t b := h.comm_of_mem htK
  have htζ : Commute t (zetaOf (zs z)) := by
    rw [zeta_eq_rootK₁_mul_rootK₂ h j]
    exact Commute.mul_right htk1 htk2
  have hu_bζ2 : Commute (ρ * t * ρ⁻¹) (b * zetaOf (zs z) ^ 2) := by
    rw [← hρb]
    exact htb.conj ρ
  have hu_ζ : Commute (ρ * t * ρ⁻¹) (zetaOf (zs z)) := by
    rw [← hρζ]
    exact htζ.conj ρ
  have hu_b : Commute (ρ * t * ρ⁻¹) b := by
    have h1 : Commute (ρ * t * ρ⁻¹)
        ((b * zetaOf (zs z) ^ 2) * (zetaOf (zs z) ^ 2)⁻¹) :=
      hu_bζ2.mul_right ((hu_ζ.pow_right 2).inv_right)
    rwa [mul_inv_cancel_right] at h1
  have hu2 : (ρ * t * ρ⁻¹) * (ρ * t * ρ⁻¹) = 1 := by
    rw [← pow_two, conj_pow, pow_two, ht2, mul_one, mul_inv_cancel]
  have huCen : ρ * t * ρ⁻¹ ∈ Cen b :=
    Subgroup.mem_centralizer_singleton_iff.mpr hu_b.eq
  have huK : ρ * t * ρ⁻¹ ∈ K := hmem (ρ * t * ρ⁻¹) huCen 1 (by simpa [pow_two] using hu2)
  have hu_c : Commute (ρ * t * ρ⁻¹) ((b * zetaOf (zs z))⁻¹) := by
    have h1 : Commute (ρ * t * ρ⁻¹) (b * zetaOf (zs z)) := hu_b.mul_right hu_ζ
    exact h1.inv_right
  have hu_k1 : Commute (ρ * t * ρ⁻¹) (rootK₁ (zs z) j) := by
    have h1 : Commute (ρ * t * ρ⁻¹) (ρ * rootK₁ (zs z) j * ρ⁻¹) :=
      (show Commute t (rootK₁ (zs z) j) from htk1).conj ρ
    rw [conj_rootK₁ h hρz j] at h1
    have h2 : Commute (ρ * t * ρ⁻¹)
        ((rootK₁ (zs z) j * (b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹) *
          ((b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹)⁻¹) :=
      h1.mul_right ((hu_c.mul_right hu_c).inv_right)
    have hcancel : (rootK₁ (zs z) j * (b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹) *
        ((b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹)⁻¹ = rootK₁ (zs z) j := by
      rw [show rootK₁ (zs z) j * (b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹ =
          rootK₁ (zs z) j * ((b * zetaOf (zs z))⁻¹ * (b * zetaOf (zs z))⁻¹) by group,
        mul_inv_cancel_right]
    rwa [hcancel] at h2
  have hu_k2 : Commute (ρ * t * ρ⁻¹) (rootK₂ (zs z) j) := by
    have h1 : Commute (ρ * t * ρ⁻¹) (ρ * rootK₂ (zs z) j * ρ⁻¹) :=
      (show Commute t (rootK₂ (zs z) j) from htk2).conj ρ
    rw [conj_rootK₂ hρz j] at h1
    have h2 : Commute (ρ * t * ρ⁻¹)
        ((rootK₂ (zs z) j * (b * zetaOf (zs z))⁻¹) * ((b * zetaOf (zs z))⁻¹)⁻¹) :=
      h1.mul_right hu_c.inv_right
    have hcancel : (rootK₂ (zs z) j * (b * zetaOf (zs z))⁻¹) *
        ((b * zetaOf (zs z))⁻¹)⁻¹ = rootK₂ (zs z) j := mul_inv_cancel_right _ _
    rwa [hcancel] at h2
  have hW : Commute ((b * zetaOf (zs z))⁻¹) (rootW (zs z) j) := inv_bz_comm_rootW h j
  have hu_rel : RootRel (rootW (zs z) j) (ρ * t * ρ⁻¹) := by
    have hrel : ρ * (t * (rootW (zs z) j * t * (rootW (zs z) j)⁻¹)) * ρ⁻¹ =
        ρ * ((rootW (zs z) j) ^ 2 * t * ((rootW (zs z) j) ^ 2)⁻¹) * ρ⁻¹ :=
      congrArg (fun x => ρ * x * ρ⁻¹) htrel
    have hL : ρ * (t * (rootW (zs z) j * t * (rootW (zs z) j)⁻¹)) * ρ⁻¹ =
        (ρ * t * ρ⁻¹) * ((rootW (zs z) j * (b * zetaOf (zs z))⁻¹) * (ρ * t * ρ⁻¹) *
          (rootW (zs z) j * (b * zetaOf (zs z))⁻¹)⁻¹) := by
      rw [show rootW (zs z) j * (b * zetaOf (zs z))⁻¹ = ρ * rootW (zs z) j * ρ⁻¹ from
        (conj_rootW hρz j).symm]
      group
    have hR : ρ * ((rootW (zs z) j) ^ 2 * t * ((rootW (zs z) j) ^ 2)⁻¹) * ρ⁻¹ =
        (rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ 2 * (ρ * t * ρ⁻¹) *
          ((rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ 2)⁻¹ := by
      rw [show rootW (zs z) j * (b * zetaOf (zs z))⁻¹ = ρ * rootW (zs z) j * ρ⁻¹ from
          (conj_rootW hρz j).symm,
        conj_pow (a := ρ) (b := rootW (zs z) j) (i := 2)]
      group
    rw [hL, hR] at hrel
    have h1 : (rootW (zs z) j * (b * zetaOf (zs z))⁻¹) * (ρ * t * ρ⁻¹) *
        (rootW (zs z) j * (b * zetaOf (zs z))⁻¹)⁻¹ =
        rootW (zs z) j * (ρ * t * ρ⁻¹) * (rootW (zs z) j)⁻¹ :=
      mul_comm_conj_mul_inv hu_c.symm
    have h2 : (rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ 2 =
        (rootW (zs z) j) ^ 2 * (b * zetaOf (zs z))⁻¹ ^ 2 := hW.symm.mul_pow 2
    have h3 : ((rootW (zs z) j) ^ 2 * (b * zetaOf (zs z))⁻¹ ^ 2) * (ρ * t * ρ⁻¹) *
        ((rootW (zs z) j) ^ 2 * (b * zetaOf (zs z))⁻¹ ^ 2)⁻¹ =
        (rootW (zs z) j) ^ 2 * (ρ * t * ρ⁻¹) * ((rootW (zs z) j) ^ 2)⁻¹ :=
      mul_comm_conj_mul_inv (hu_c.symm.pow_left 2)
    rw [h1, h2, h3] at hrel
    exact hrel
  exact ⟨huK, hu2, hu_k1, hu_k2, hu_rel⟩

omit [Finite G] in
private theorem rootGood_conj_rho (h : Setting b K z)
    (hmem : ∀ c ∈ Cen b, ∀ m : ℕ, c ^ 2 ^ m = 1 → c ∈ K)
    {ρ : G} (hρb : ρ * b * ρ⁻¹ = b * zetaOf (zs z) ^ 2)
    (hρζ : ρ * zetaOf (zs z) * ρ⁻¹ = zetaOf (zs z))
    (hρz : ∀ i, ρ * zs z i * ρ⁻¹ = zs z i * (b * zetaOf (zs z))⁻¹) (j : Fin 2) :
    (∀ t, RootGood K z j t → RootGood K z j (ρ * t * ρ⁻¹)) ∧
    (∀ t (a : Fin 3), RootGood K z j t →
      ρ * cjp (rootW (zs z) j) a t * ρ⁻¹ = cjp (rootW (zs z) j) a (ρ * t * ρ⁻¹)) := by
  constructor
  · intro t ht
    obtain ⟨huK, hu2, huk1, huk2, hurel⟩ :=
      rootGood_conj_rho_aux h hmem hρb hρζ hρz j ht
    exact ⟨huK, hu2, huk1.eq, huk2.eq, hurel⟩
  · intro t a ht
    obtain ⟨huK, -, huk1, huk2, -⟩ :=
      rootGood_conj_rho_aux h hmem hρb hρζ hρz j ht
    have hu_b : Commute (ρ * t * ρ⁻¹) b := h.comm_of_mem huK
    have hu_ζ : Commute (ρ * t * ρ⁻¹) (zetaOf (zs z)) := by
      rw [zeta_eq_rootK₁_mul_rootK₂ h j]
      exact Commute.mul_right huk1 huk2
    have hu_c : Commute (ρ * t * ρ⁻¹) ((b * zetaOf (zs z))⁻¹) :=
      (hu_b.mul_right hu_ζ).inv_right
    have hW : Commute ((b * zetaOf (zs z))⁻¹) (rootW (zs z) j) := inv_bz_comm_rootW h j
    have hstep : ρ * (rootW (zs z) j ^ (a : ℕ) * t * (rootW (zs z) j ^ (a : ℕ))⁻¹) *
        ρ⁻¹ = (rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ (a : ℕ) * (ρ * t * ρ⁻¹) *
          ((rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ (a : ℕ))⁻¹ := by
      rw [show rootW (zs z) j * (b * zetaOf (zs z))⁻¹ = ρ * rootW (zs z) j * ρ⁻¹ from
          (conj_rootW hρz j).symm,
        conj_pow (a := ρ) (b := rootW (zs z) j) (i := (a : ℕ))]
      group
    have hstep2 : (rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ (a : ℕ) * (ρ * t * ρ⁻¹) *
        ((rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ (a : ℕ))⁻¹ =
        (rootW (zs z) j ^ (a : ℕ) * (b * zetaOf (zs z))⁻¹ ^ (a : ℕ)) * (ρ * t * ρ⁻¹) *
          (rootW (zs z) j ^ (a : ℕ) * (b * zetaOf (zs z))⁻¹ ^ (a : ℕ))⁻¹ := by
      rw [hW.symm.mul_pow]
    have hstep3 : (rootW (zs z) j ^ (a : ℕ) * (b * zetaOf (zs z))⁻¹ ^ (a : ℕ)) *
        (ρ * t * ρ⁻¹) *
        (rootW (zs z) j ^ (a : ℕ) * (b * zetaOf (zs z))⁻¹ ^ (a : ℕ))⁻¹ =
        rootW (zs z) j ^ (a : ℕ) * (ρ * t * ρ⁻¹) * (rootW (zs z) j ^ (a : ℕ))⁻¹ :=
      mul_comm_conj_mul_inv (hu_c.symm.pow_left (a : ℕ))
    calc ρ * cjp (rootW (zs z) j) a t * ρ⁻¹
        = ρ * (rootW (zs z) j ^ (a : ℕ) * t * (rootW (zs z) j ^ (a : ℕ))⁻¹) * ρ⁻¹ := rfl
      _ = (rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ (a : ℕ) * (ρ * t * ρ⁻¹) *
            ((rootW (zs z) j * (b * zetaOf (zs z))⁻¹) ^ (a : ℕ))⁻¹ := hstep
      _ = rootW (zs z) j ^ (a : ℕ) * (ρ * t * ρ⁻¹) * (rootW (zs z) j ^ (a : ℕ))⁻¹ := by
            rw [hstep2, hstep3]
      _ = cjp (rootW (zs z) j) a (ρ * t * ρ⁻¹) := rfl

section

omit [Finite G]

private lemma commute_of_conj_eq {x y : G} (h : x * y * x⁻¹ = y) : Commute x y := by
  rw [commute_iff_eq]
  calc x * y = x * y * x⁻¹ * x := (inv_mul_cancel_right (x * y) x).symm
    _ = y * x := by rw [h]

private lemma conj_eq_of_commute {x y : G} (h : Commute x y) : x * y * x⁻¹ = y := by
  rw [h.eq, mul_inv_cancel_right]

private lemma commute_rootW {x : G} (hxz : ∀ i, x * zs z i * x⁻¹ = zs z i) (j : Fin 2) :
    Commute x (rootW (zs z) j) := by
  have h0 : Commute x (zs z 0) := commute_of_conj_eq (hxz 0)
  have h1 : Commute x (zs z 1) := commute_of_conj_eq (hxz 1)
  fin_cases j
  · simpa [rootW] using h0
  · simpa [rootW] using h1

private lemma commute_rootK₁ {x : G} (hxz : ∀ i, x * zs z i * x⁻¹ = zs z i) (j : Fin 2) :
    Commute x (rootK₁ (zs z) j) := by
  have h0 : Commute x (zs z 0) := commute_of_conj_eq (hxz 0)
  have h1 : Commute x (zs z 1) := commute_of_conj_eq (hxz 1)
  have h2 : Commute x (zs z 2) := commute_of_conj_eq (hxz 2)
  fin_cases j
  · simpa [rootK₁] using h0.mul_right h1
  · simpa [rootK₁] using h1.mul_right h2

private lemma commute_rootK₂ {x : G} (hxz : ∀ i, x * zs z i * x⁻¹ = zs z i) (j : Fin 2) :
    Commute x (rootK₂ (zs z) j) := by
  have h0 : Commute x (zs z 0) := commute_of_conj_eq (hxz 0)
  have h2 : Commute x (zs z 2) := commute_of_conj_eq (hxz 2)
  fin_cases j
  · simpa [rootK₂] using h2
  · simpa [rootK₂] using h0

private lemma rootRel_conj_x {w u x : G} (hxw : Commute x w) (h : RootRel w u) :
    RootRel w (x * u * x⁻¹) := by
  have hxw' : MulAut.conj x w = w := by
    rw [MulAut.conj_apply, conj_eq_of_commute hxw]
  unfold RootRel at h ⊢
  have h' := congrArg (MulAut.conj x) h
  simpa only [map_mul, map_pow, map_inv, hxw', MulAut.conj_apply] using h'

private lemma cjp_conj {w u x : G} (a : Fin 3) (hxw : Commute x w) :
    x * cjp w a u * x⁻¹ = cjp w a (x * u * x⁻¹) := by
  have hxw' : MulAut.conj x w = w := by
    rw [MulAut.conj_apply, conj_eq_of_commute hxw]
  have h : MulAut.conj x (cjp w a u) = cjp w a (MulAut.conj x u) := by
    simp only [cjp, map_mul, map_pow, map_inv, hxw']
  simpa only [MulAut.conj_apply] using h

end

private theorem rootGood_conj_x (h : Setting b K z)
    (hmem : ∀ c ∈ Cen b, ∀ m : ℕ, c ^ 2 ^ m = 1 → c ∈ K)
    {x : G} (hxb : x * b * x⁻¹ = b⁻¹) (hxz : ∀ i, x * zs z i * x⁻¹ = zs z i) (j : Fin 2) :
    (∀ t, RootGood K z j t → RootGood K z j (x * t * x⁻¹)) ∧
    (∀ t (a : Fin 3), x * cjp (rootW (zs z) j) a t * x⁻¹ =
      cjp (rootW (zs z) j) a (x * t * x⁻¹)) := by
  have hfin : 0 < Nat.card G := Finite.card_pos
  have hxW : Commute x (rootW (zs z) j) := commute_rootW hxz j
  have hxK1 : Commute x (rootK₁ (zs z) j) := commute_rootK₁ hxz j
  have hxK2 : Commute x (rootK₂ (zs z) j) := commute_rootK₂ hxz j
  have hxW' : x * rootW (zs z) j * x⁻¹ = rootW (zs z) j := conj_eq_of_commute hxW
  have hxK1' : x * rootK₁ (zs z) j * x⁻¹ = rootK₁ (zs z) j := conj_eq_of_commute hxK1
  have hxK2' : x * rootK₂ (zs z) j * x⁻¹ = rootK₂ (zs z) j := conj_eq_of_commute hxK2
  constructor
  · intro t ht
    have htK : t ∈ K := ht.1
    have ht2 : t * t = 1 := ht.2.1
    have htK1 : t * rootK₁ (zs z) j = rootK₁ (zs z) j * t := ht.2.2.1
    have htK2 : t * rootK₂ (zs z) j = rootK₂ (zs z) j * t := ht.2.2.2.1
    have htRel : RootRel (rootW (zs z) j) t := ht.2.2.2.2
    have htb : t * b = b * t := h.comm_of_mem htK
    have hu2 : x * t * x⁻¹ * (x * t * x⁻¹) = 1 := by
      calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    have huCen : x * t * x⁻¹ ∈ Cen b := by
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hc : Commute (x * t * x⁻¹) (x * b * x⁻¹) :=
        ((commute_iff_eq t b).mpr htb).conj x
      rw [hxb] at hc
      exact (Commute.inv_right_iff.mp hc).eq
    have huK : x * t * x⁻¹ ∈ K := hmem _ huCen 1 (by simpa [pow_two] using hu2)
    refine ⟨huK, hu2, ?_, ?_, rootRel_conj_x hxW htRel⟩
    · calc (x * t * x⁻¹) * rootK₁ (zs z) j
          = (x * t * x⁻¹) * (x * rootK₁ (zs z) j * x⁻¹) := by rw [hxK1']
        _ = x * (t * rootK₁ (zs z) j) * x⁻¹ := by group
        _ = x * (rootK₁ (zs z) j * t) * x⁻¹ := by rw [htK1]
        _ = x * rootK₁ (zs z) j * x⁻¹ * (x * t * x⁻¹) := by group
        _ = rootK₁ (zs z) j * (x * t * x⁻¹) := by rw [hxK1']
    · calc (x * t * x⁻¹) * rootK₂ (zs z) j
          = (x * t * x⁻¹) * (x * rootK₂ (zs z) j * x⁻¹) := by rw [hxK2']
        _ = x * (t * rootK₂ (zs z) j) * x⁻¹ := by group
        _ = x * (rootK₂ (zs z) j * t) * x⁻¹ := by rw [htK2]
        _ = x * rootK₂ (zs z) j * x⁻¹ * (x * t * x⁻¹) := by group
        _ = rootK₂ (zs z) j * (x * t * x⁻¹) := by rw [hxK2']
  · intro t a
    exact cjp_conj (w := rootW (zs z) j) (u := t) (x := x) a hxW

omit [Finite G] in
private lemma inv_mul_comm_of_conj_eq {a b t t' : G} (ha : a * t * a⁻¹ = t')
    (hb : b * t * b⁻¹ = t') : Commute (a⁻¹ * b) t := by
  show (a⁻¹ * b) * t = t * (a⁻¹ * b)
  calc (a⁻¹ * b) * t = a⁻¹ * (b * t * b⁻¹) * b := by group
    _ = a⁻¹ * t' * b := by rw [hb]
    _ = a⁻¹ * (a * t * a⁻¹) * b := by rw [ha]
    _ = t * (a⁻¹ * b) := by group

private lemma conj_mem_centralizer {B : Subgroup G} {n c : G} (hn : n ∈ Nor B)
    (hc : c ∈ CenS B) : n * c * n⁻¹ ∈ CenS B := by
  refine Subgroup.mem_centralizer_iff.mpr fun β hβ => ?_
  have hβ' : n⁻¹ * β * n ∈ B :=
    inv_conj_mem_of_conj_mem (fun k hk => (Subgroup.mem_normalizer_iff.mp hn k).mp hk) hβ
  have hcomm := Subgroup.mem_centralizer_iff.mp hc (n⁻¹ * β * n) hβ'
  calc β * (n * c * n⁻¹) = n * ((n⁻¹ * β * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * β * n)) * n⁻¹ := by rw [hcomm]
    _ = (n * c * n⁻¹) * β := by group

private theorem caseB_sqrt (h : Setting b K z) (hN : ModelN K z)
    (hmem : ∀ c ∈ Cen b, ∀ m : ℕ, c ^ 2 ^ m = 1 → c ∈ K)
    {x : G} (hx2 : x * x = 1)
    {n : G} (hnN : n ∈ Nor (Bt b z))
    (hn3 : ∀ w : Fin 3 → ZMod 3, w 0 + w 1 + w 2 = 0 → ∀ c : G, c * b = b * c →
      c * zetaOf (zs z) = zetaOf (zs z) * c →
      c * (n⁻¹ * vecElt (zs z) w * n) = n⁻¹ * vecElt (zs z) w * n * c)
    (hnx : n * x * n⁻¹ * b * (n * x * n⁻¹)⁻¹ = b ∧
      n * x * n⁻¹ * zs z 0 * (n * x * n⁻¹)⁻¹ = zs z 0 ∧
      n * x * n⁻¹ * zs z 1 * (n * x * n⁻¹)⁻¹ = zs z 2 ∧
      n * x * n⁻¹ * zs z 2 * (n * x * n⁻¹)⁻¹ = zs z 1)
    {π x₀ : K} {r r' : Fin 2 → K} (hB : ModelNB K z π x₀ r r')
    (hyB : x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n) ∈ CenS (Bt b z)) :
    (∀ c : G, c * b = b * c → c * zetaOf (zs z) = zetaOf (zs z) * c →
      c * (x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n)) =
        x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n) * c) ∧
    ∃ q : K, ((q * q : K) : G) = n * x * n⁻¹ ∧
      ∀ y ∈ ({z 0 * (z 1)⁻¹, zetaOf z, π} : Set K), q * y * q⁻¹ ∈ rOne z π := by
  have _ : b ^ 3 = 1 := h.b_cube
  have hx'sq : (n * x * n⁻¹) * (n * x * n⁻¹) = 1 := by
    calc n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hx'cen : n * x * n⁻¹ ∈ Cen b := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n * x * n⁻¹ * b = (n * x * n⁻¹ * b * (n * x * n⁻¹)⁻¹) * (n * x * n⁻¹) := by
          group
      _ = b * (n * x * n⁻¹) := by rw [hnx.1]
  have hx'K : n * x * n⁻¹ ∈ K := by
    refine hmem (n * x * n⁻¹) hx'cen 1 ?_
    simpa [pow_two] using hx'sq
  let X : K := ⟨n * x * n⁻¹, hx'K⟩
  have hXval : (X : G) = n * x * n⁻¹ := rfl
  have hnx' : ∀ i, n * x * n⁻¹ * zs z i * (n * x * n⁻¹)⁻¹ = zs z (![0, 2, 1] i) := by
    intro i
    fin_cases i
    · simpa using hnx.2.1
    · simpa using hnx.2.2.1
    · simpa using hnx.2.2.2
  have hx0' : ∀ i, (x₀ : G) * zs z i * (x₀ : G)⁻¹ = zs z (![0, 2, 1] i) := by
    intro i
    fin_cases i
    · simpa [zs] using congrArg Subtype.val hB.x0_z0
    · simpa [zs] using congrArg Subtype.val hB.x0_z1
    · simpa [zs] using congrArg Subtype.val hB.x0_z2
  have hcommX : ∀ i, (x₀ : G)⁻¹ * (n * x * n⁻¹) * zs z i =
      zs z i * ((x₀ : G)⁻¹ * (n * x * n⁻¹)) :=
    fun i => (inv_mul_comm_of_conj_eq (hx0' i) (hnx' i)).eq
  have hcommK : ∀ i, (x₀⁻¹ * X) * z i = z i * (x₀⁻¹ * X) := by
    intro i
    apply Subtype.ext
    simpa using hcommX i
  obtain ⟨v, hv⟩ := hN.cen (x₀⁻¹ * X) hcommK
  have hX : X = x₀ * vecElt z v := by
    rw [← hv]
    group
  have hXG : ((x₀ * vecElt z v : K) : G) = n * x * n⁻¹ :=
    (congrArg Subtype.val hX).symm.trans hXval
  have hu2G : ((x₀ * vecElt z v : K) : G) * ((x₀ * vecElt z v : K) : G) = 1 := by
    rw [hXG]
    exact hx'sq
  have hu2K : x₀ * vecElt z v * (x₀ * vecElt z v) = 1 := by
    apply Subtype.ext
    simpa using hu2G
  have hyC : n * (x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n)) * n⁻¹ ∈ CenS (Bt b z) :=
    conj_mem_centralizer hnN hyB
  let Y : K := X * π * X⁻¹ * π
  have hYval : (Y : G) = n * (x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n)) * n⁻¹ := by
    show ((X * π * X⁻¹ * π : K) : G) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hXval]
    group
  have hYcommK : ∀ i, Y * z i = z i * Y := by
    intro i
    apply Subtype.ext
    have hmemY := Subgroup.mem_centralizer_iff.mp hyC (zs z i) (zs_mem_Bt b z i)
    simpa [hYval] using hmemY.symm
  obtain ⟨w, hwY⟩ := hN.cen Y hYcommK
  have hc : ∃ w, x₀ * vecElt z v * π * (x₀ * vecElt z v)⁻¹ * π = vecElt z w := by
    refine ⟨w, ?_⟩
    rw [← hX]
    exact hwY
  obtain ⟨⟨w', hw0, hcw⟩, q, hq, hqR⟩ := hB.sqrt v hu2K hc
  refine ⟨?_, q, ?_, hqR⟩
  · intro c hcb hcζ
    have hcwG : ((x₀ * vecElt z v * π * (x₀ * vecElt z v)⁻¹ * π : K) : G) =
        vecElt (zs z) w' := by
      rw [congrArg Subtype.val hcw, vecElt_zs]
    have hvalL : ((x₀ * vecElt z v * π * (x₀ * vecElt z v)⁻¹ * π : K) : G) =
        (n * x * n⁻¹) * (π : G) * (n * x * n⁻¹)⁻¹ * (π : G) := by
      rw [← hX]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hXval]
    have hx'π : (n * x * n⁻¹) * (π : G) * (n * x * n⁻¹)⁻¹ * (π : G) =
        vecElt (zs z) w' := hvalL ▸ hcwG
    have hconjEq : n * (x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n)) * n⁻¹ =
        (n * x * n⁻¹) * (π : G) * (n * x * n⁻¹)⁻¹ * (π : G) := by
      group
    have hxr : x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n) =
        n⁻¹ * vecElt (zs z) w' * n := by
      rw [← hconjEq.trans hx'π]
      group
    rw [hxr]
    exact hn3 w' hw0 c hcb hcζ
  · calc ((q * q : K) : G) = ((x₀ * vecElt z v : K) : G) := congrArg Subtype.val hq
      _ = n * x * n⁻¹ := hXG

omit [Finite G] in
private theorem conj_mem_closure {S : Set G} {T : Subgroup G} {n : G}
    (h : ∀ s ∈ S, n * s * n⁻¹ ∈ T) {x : G} (hx : x ∈ Subgroup.closure S) :
    n * x * n⁻¹ ∈ T := by
  have hle : Subgroup.closure S ≤ T.comap (MulAut.conj n).toMonoidHom :=
    (Subgroup.closure_le (T.comap (MulAut.conj n).toMonoidHom)).mpr fun s hs => by
      simpa only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulAut.conj_apply] using h s hs
  simpa only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.conj_apply] using hle hx

omit [Finite G] in
private theorem inv_conj_mem_closure {S : Set G} {T : Subgroup G} {n : G}
    (h : ∀ s ∈ S, n⁻¹ * s * n ∈ T) {x : G} (hx : x ∈ Subgroup.closure S) :
    n⁻¹ * x * n ∈ T := by
  have h' : ∀ s ∈ S, n⁻¹ * s * (n⁻¹)⁻¹ ∈ T := fun s hs => by simpa using h s hs
  simpa using conj_mem_closure (n := n⁻¹) (T := T) h' hx

omit [Finite G] in
private theorem conj_of_eq_inv_conj {n y z : G} (h : n⁻¹ * y * n = z) : n * z * n⁻¹ = y := by
  have hh := congrArg (fun t => n * t * n⁻¹) h
  rw [show n * (n⁻¹ * y * n) * n⁻¹ = y from by group] at hh
  exact hh.symm

private theorem caseB_final (h : Setting b K z) (hN : ModelN K z)
    (hmem : ∀ c ∈ Cen b, ∀ m : ℕ, c ^ 2 ^ m = 1 → c ∈ K)
    (hsyl : ∀ K₁ : Subgroup G, (∀ P : Subgroup G, P ≤ K₁ → IsPGroup 7 P → Nat.card P ≤ 7) →
      ∀ g₀ ∈ K₁, g₀ ^ 7 = 1 → g₀ ≠ 1 → ∀ q : G, (∀ t ∈ K₁, q * t * q⁻¹ ∈ K₁) →
        ∃ k ∈ K₁, ∃ j : ℕ, ¬ 7 ∣ j ∧ q * g₀ * q⁻¹ = k * g₀ ^ j * k⁻¹)
    {x : G} (hxb : x * b * x⁻¹ = b⁻¹)
    (hout : ∀ k ∈ K, ¬ ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹)
    {n : G} (hn1 : n⁻¹ * (zs z 0 * (zs z 1)⁻¹) * n = b * zetaOf (zs z))
    (hn2 : n⁻¹ * zetaOf (zs z) * n = zetaOf (zs z))
    {π x₀ : K} {r r' : Fin 2 → K} (hB : ModelNB K z π x₀ r r')
    (hfix : ∀ j, n⁻¹ * π * n * (r j : G) = r j * (n⁻¹ * π * n) ∧
      n⁻¹ * π * n * (r' j : G) = r' j * (n⁻¹ * π * n))
    {q : K} (hq2 : ((q * q : K) : G) = n * x * n⁻¹)
    (hqR : ∀ y ∈ ({z 0 * (z 1)⁻¹, zetaOf z, π} : Set K), q * y * q⁻¹ ∈ rOne z π) :
    False := by
  set ζ : G := zetaOf (zs z) with hζdef
  set ρ : G := n⁻¹ * (π : G) * n with hρdef
  set qq : G := n⁻¹ * (q : G) * n with hqqdef
  set S₁ : Set G := {b * ζ, ζ, ρ} with hS₁def
  set R₁ : Subgroup G := Subgroup.closure S₁ with hR₁def
  set S₂ : Set G := {t : G | (∃ m : ℕ, t ^ 2 ^ m = 1) ∧ ∀ y ∈ R₁, t * y = y * t}
    with hS₂def
  set K₁ : Subgroup G := Subgroup.closure S₂ with hK₁def
  have hζ_coe : ((zetaOf z : K) : G) = ζ := by
    rw [hζdef]
    rfl
  have hK₁_le_K : K₁ ≤ K := by
    rw [hK₁def]
    refine (Subgroup.closure_le K).mpr fun t ht => ?_
    rw [hS₂def] at ht
    obtain ⟨⟨m, hm⟩, hcomm⟩ := ht
    have hbζ : t * (b * ζ) = b * ζ * t :=
      hcomm (b * ζ) (Subgroup.subset_closure (by rw [hS₁def]; simp))
    have hζ : t * ζ = ζ * t :=
      hcomm ζ (Subgroup.subset_closure (by rw [hS₁def]; simp))
    have hb : t * b = b * t := by
      have h1 : t * b * ζ = b * t * ζ := by
        calc t * b * ζ = t * (b * ζ) := by group
          _ = b * ζ * t := hbζ
          _ = b * (ζ * t) := by group
          _ = b * (t * ζ) := by rw [hζ]
          _ = b * t * ζ := by group
      exact mul_right_cancel h1
    exact hmem t (Subgroup.mem_centralizer_singleton_iff.mpr hb) m hm
  have hR₁_ζ : ζ ∈ R₁ := by
    rw [hR₁def]
    exact Subgroup.subset_closure (by rw [hS₁def]; simp)
  have hK₁_comm_ζ : ∀ t ∈ K₁, t * ζ = ζ * t := by
    have hle : K₁ ≤ Subgroup.centralizer ({ζ} : Set G) := by
      rw [hK₁def]
      refine (Subgroup.closure_le _).mpr fun t ht => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr (ht.2 ζ hR₁_ζ)
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ht)
  have hζ_eq : ∀ j : Fin 2, ζ = rootK₁ (zs z) j * rootK₂ (zs z) j := by
    intro j
    fin_cases j
    · rw [hζdef]
      rfl
    · rw [hζdef]
      have hcomm : Commute (zs z 0) (zs z 1 * zs z 2) :=
        (show Commute (zs z 0) (zs z 1) from h.zs_comm 0 1).mul_right (h.zs_comm 0 2)
      calc zetaOf (zs z) = zs z 0 * (zs z 1 * zs z 2) := by rw [zetaOf, mul_assoc]
        _ = (zs z 1 * zs z 2) * zs z 0 := hcomm.eq
        _ = zs z 1 * zs z 2 * zs z 0 := rfl
  have hrootK₁ : ∀ j : Fin 2, ((rootK₁ z j : K) : G) = rootK₁ (zs z) j := by
    intro j
    fin_cases j <;> rfl
  have hrootK₂ : ∀ j : Fin 2, ((rootK₂ z j : K) : G) = rootK₂ (zs z) j := by
    intro j
    fin_cases j <;> rfl
  have hr_comm_b : ∀ j : Fin 2, (r j : G) * b = b * (r j : G) :=
    fun j => h.comm_of_mem (r j).2
  have hr'_comm_b : ∀ j : Fin 2, (r' j : G) * b = b * (r' j : G) :=
    fun j => h.comm_of_mem (r' j).2
  have hr_comm_k1 : ∀ j : Fin 2,
      (r j : G) * rootK₁ (zs z) j = rootK₁ (zs z) j * (r j : G) := by
    intro j
    have hh := congrArg (fun y : K => (y : G)) (hB.root_comm j).1
    simpa only [Subgroup.coe_mul, hrootK₁ j] using hh
  have hr_comm_k2 : ∀ j : Fin 2,
      (r j : G) * rootK₂ (zs z) j = rootK₂ (zs z) j * (r j : G) := by
    intro j
    have hh := congrArg (fun y : K => (y : G)) (hB.root_comm j).2.1
    simpa only [Subgroup.coe_mul, hrootK₂ j] using hh
  have hr'_comm_k1 : ∀ j : Fin 2,
      (r' j : G) * rootK₁ (zs z) j = rootK₁ (zs z) j * (r' j : G) := by
    intro j
    have hh := congrArg (fun y : K => (y : G)) (hB.root_comm j).2.2.1
    simpa only [Subgroup.coe_mul, hrootK₁ j] using hh
  have hr'_comm_k2 : ∀ j : Fin 2,
      (r' j : G) * rootK₂ (zs z) j = rootK₂ (zs z) j * (r' j : G) := by
    intro j
    have hh := congrArg (fun y : K => (y : G)) (hB.root_comm j).2.2.2
    simpa only [Subgroup.coe_mul, hrootK₂ j] using hh
  have hr_comm_ζ : ∀ j : Fin 2, (r j : G) * ζ = ζ * (r j : G) := by
    intro j
    rw [hζ_eq j]
    calc (r j : G) * (rootK₁ (zs z) j * rootK₂ (zs z) j)
        = (r j : G) * rootK₁ (zs z) j * rootK₂ (zs z) j := by group
      _ = rootK₁ (zs z) j * (r j : G) * rootK₂ (zs z) j := by rw [hr_comm_k1 j]
      _ = rootK₁ (zs z) j * ((r j : G) * rootK₂ (zs z) j) := by group
      _ = rootK₁ (zs z) j * (rootK₂ (zs z) j * (r j : G)) := by rw [hr_comm_k2 j]
      _ = rootK₁ (zs z) j * rootK₂ (zs z) j * (r j : G) := by group
  have hr'_comm_ζ : ∀ j : Fin 2, (r' j : G) * ζ = ζ * (r' j : G) := by
    intro j
    rw [hζ_eq j]
    calc (r' j : G) * (rootK₁ (zs z) j * rootK₂ (zs z) j)
        = (r' j : G) * rootK₁ (zs z) j * rootK₂ (zs z) j := by group
      _ = rootK₁ (zs z) j * (r' j : G) * rootK₂ (zs z) j := by rw [hr'_comm_k1 j]
      _ = rootK₁ (zs z) j * ((r' j : G) * rootK₂ (zs z) j) := by group
      _ = rootK₁ (zs z) j * (rootK₂ (zs z) j * (r' j : G)) := by rw [hr'_comm_k2 j]
      _ = rootK₁ (zs z) j * rootK₂ (zs z) j * (r' j : G) := by group
  have hr_sq : ∀ j : Fin 2, (r j : G) ^ 2 = 1 := by
    intro j
    have hh := congrArg (fun y : K => (y : G)) (hB.root_sq j).1
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using hh
  have hr'_sq : ∀ j : Fin 2, (r' j : G) ^ 2 = 1 := by
    intro j
    have hh := congrArg (fun y : K => (y : G)) (hB.root_sq j).2
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using hh
  have hgen_r : ∀ j : Fin 2, (r j : G) ∈ S₂ := by
    intro j
    rw [hS₂def]
    refine ⟨⟨1, by simpa using hr_sq j⟩, ?_⟩
    intro y hy
    have hmemc : (r j : G) ∈ Subgroup.centralizer S₁ := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [hS₁def] at hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · exact ((show Commute (r j : G) (b * ζ) from
          (show Commute (r j : G) b from hr_comm_b j).mul_right
            (show Commute (r j : G) ζ from hr_comm_ζ j)).eq).symm
      · exact (hr_comm_ζ j).symm
      · exact (hfix j).1
    have hmemc' : (r j : G) ∈ Subgroup.centralizer R₁ := by
      rw [hR₁def, Subgroup.centralizer_closure]
      exact hmemc
    exact (Subgroup.mem_centralizer_iff.mp hmemc' y hy).symm
  have hgen_r' : ∀ j : Fin 2, (r' j : G) ∈ S₂ := by
    intro j
    rw [hS₂def]
    refine ⟨⟨1, by simpa using hr'_sq j⟩, ?_⟩
    intro y hy
    have hmemc : (r' j : G) ∈ Subgroup.centralizer S₁ := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [hS₁def] at hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · exact ((show Commute (r' j : G) (b * ζ) from
          (show Commute (r' j : G) b from hr'_comm_b j).mul_right
            (show Commute (r' j : G) ζ from hr'_comm_ζ j)).eq).symm
      · exact (hr'_comm_ζ j).symm
      · exact (hfix j).2
    have hmemc' : (r' j : G) ∈ Subgroup.centralizer R₁ := by
      rw [hR₁def, Subgroup.centralizer_closure]
      exact hmemc
    exact (Subgroup.mem_centralizer_iff.mp hmemc' y hy).symm
  have hr_mem : ∀ j : Fin 2, (r j : G) ∈ K₁ := by
    intro j
    rw [hK₁def]
    exact Subgroup.subset_closure (hgen_r j)
  have hr'_mem : ∀ j : Fin 2, (r' j : G) ∈ K₁ := by
    intro j
    rw [hK₁def]
    exact Subgroup.subset_closure (hgen_r' j)
  set g₀ : G := gOf (fun j => (r j : G)) (fun j => (r' j : G)) with hg₀def
  have hg₀_coe : g₀ = ((gOf r r' : K) : G) := by
    simp only [hg₀def, gOf, Subgroup.coe_mul]
  have hg₀_mem : g₀ ∈ K₁ := by
    rw [hg₀_coe]
    have hprod : ((gOf r r' : K) : G) = (r 0 : G) * (r 1 : G) * (r' 0 : G) *
        (r 0 : G) * (r' 1 : G) * (r' 0 : G) := by
      simp only [gOf, Subgroup.coe_mul]
    rw [hprod]
    exact K₁.mul_mem (K₁.mul_mem (K₁.mul_mem (K₁.mul_mem (K₁.mul_mem (hr_mem 0) (hr_mem 1))
      (hr'_mem 0)) (hr_mem 0)) (hr'_mem 1)) (hr'_mem 0)
  have hg₀_pow : g₀ ^ 7 = 1 := by
    rw [hg₀_coe, ← Subgroup.coe_pow, hB.g_pow, Subgroup.coe_one]
  have hg₀_ne : g₀ ≠ 1 := by
    rw [hg₀_coe]
    intro h1
    exact hB.g_ne (Subtype.ext (by simpa using h1))
  set S₃ : Set G := K.subtype '' ({z 0 * (z 1)⁻¹, zetaOf z, π} : Set K) with hS₃def
  set R₁' : Subgroup G := Subgroup.closure S₃ with hR₁'def
  have hR₁'_eq : (rOne z π).map K.subtype = R₁' := by
    rw [hR₁'def, hS₃def, rOne, MonoidHom.map_closure]
  have hq_gen : ∀ s ∈ S₃, (q : G) * s * (q : G)⁻¹ ∈ R₁' := by
    intro s hs
    rw [hS₃def] at hs
    obtain ⟨y, hy, rfl⟩ := hs
    rw [← hR₁'_eq]
    have hqy : q * y * q⁻¹ ∈ rOne z π := hqR y hy
    have hmap := Subgroup.mem_map_of_mem K.subtype hqy
    change (q : G) * (y : G) * (q : G)⁻¹ ∈ Subgroup.map K.subtype (rOne z π)
    simpa only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hmap
  have hq_inv_R₁' : ∀ s ∈ R₁', (q : G) * s * (q : G)⁻¹ ∈ R₁' := by
    intro s hs
    rw [hR₁'def] at hs
    exact conj_mem_closure hq_gen hs
  have hn_inv_gen : ∀ s ∈ S₃, n⁻¹ * s * n ∈ R₁ := by
    intro s hs
    rw [hS₃def] at hs
    obtain ⟨y, hy, rfl⟩ := hs
    rw [hR₁def]
    change n⁻¹ * (y : G) * n ∈ Subgroup.closure S₁
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy
    · have h1 : n⁻¹ * ((z 0 * (z 1)⁻¹ : K) : G) * n = b * ζ := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hn1
      rw [hy, h1]
      exact Subgroup.subset_closure (by rw [hS₁def]; simp)
    · have h1 : n⁻¹ * ((zetaOf z : K) : G) * n = ζ := by
        rw [hζ_coe, hn2]
      rw [hy, h1]
      exact Subgroup.subset_closure (by rw [hS₁def]; simp)
    · have h1 : n⁻¹ * ((π : K) : G) * n = ρ := hρdef.symm
      rw [hy, h1]
      exact Subgroup.subset_closure (by rw [hS₁def]; simp)
  have hn_inv_R₁' : ∀ s ∈ R₁', n⁻¹ * s * n ∈ R₁ := by
    intro s hs
    rw [hR₁'def] at hs
    exact inv_conj_mem_closure hn_inv_gen hs
  have hn_fwd_gen : ∀ s ∈ S₁, n * s * n⁻¹ ∈ R₁' := by
    intro s hs
    rw [hS₁def] at hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rw [hR₁'def]
    rcases hs with hs | hs | hs
    · have h1 : n * (b * ζ) * n⁻¹ = zs z 0 * (zs z 1)⁻¹ := conj_of_eq_inv_conj hn1
      rw [hs, h1]
      refine Subgroup.subset_closure ?_
      rw [hS₃def]
      refine ⟨z 0 * (z 1)⁻¹, by simp, ?_⟩
      simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    · have h1 : n * ζ * n⁻¹ = ζ := conj_of_eq_inv_conj hn2
      rw [hs, h1]
      refine Subgroup.subset_closure ?_
      rw [hS₃def]
      exact ⟨zetaOf z, by simp, hζ_coe⟩
    · have h1 : n * ρ * n⁻¹ = (π : G) := conj_of_eq_inv_conj hρdef
      rw [hs, h1]
      refine Subgroup.subset_closure ?_
      rw [hS₃def]
      exact ⟨π, by simp, rfl⟩
  have hn_fwd_R₁ : ∀ s ∈ R₁, n * s * n⁻¹ ∈ R₁' := by
    intro s hs
    rw [hR₁def] at hs
    exact conj_mem_closure hn_fwd_gen hs
  have hqq_conj_R₁ : ∀ y ∈ R₁, qq * y * qq⁻¹ ∈ R₁ := by
    intro y hy
    have hny : n * y * n⁻¹ ∈ R₁' := hn_fwd_R₁ y hy
    have hqny : (q : G) * (n * y * n⁻¹) * (q : G)⁻¹ ∈ R₁' := hq_inv_R₁' _ hny
    have hmem : n⁻¹ * ((q : G) * (n * y * n⁻¹) * (q : G)⁻¹) * n ∈ R₁ := hn_inv_R₁' _ hqny
    rw [hqqdef]
    rw [show n⁻¹ * (q : G) * n * y * (n⁻¹ * (q : G) * n)⁻¹ =
      n⁻¹ * ((q : G) * (n * y * n⁻¹) * (q : G)⁻¹) * n from by group]
    exact hmem
  have hqq_nor : qq ∈ Nor R₁ := by
    refine mem_nor_of_closure (S := S₁) fun s hs => ?_
    have hmem := hqq_conj_R₁ s (Subgroup.subset_closure hs)
    rwa [hR₁def] at hmem
  have hqq_inv_conj_R₁ : ∀ y ∈ R₁, qq⁻¹ * y * qq ∈ R₁ := by
    intro y hy
    have h := (Subgroup.mem_normalizer_iff.mp ((Nor R₁).inv_mem hqq_nor) y).mp hy
    simpa using h
  have hqq_conj_K₁ : ∀ t ∈ K₁, qq * t * qq⁻¹ ∈ K₁ := by
    intro t ht
    rw [hK₁def] at ht
    refine conj_mem_closure (S := S₂) (T := Subgroup.closure S₂) ?_ ht
    intro s hs
    rw [hS₂def] at hs
    obtain ⟨⟨m, hm⟩, hcomm⟩ := hs
    refine Subgroup.subset_closure ?_
    rw [hS₂def]
    refine ⟨⟨m, ?_⟩, ?_⟩
    · rw [conj_pow, hm, mul_one, mul_inv_cancel]
    · intro y hy
      have hy' : qq⁻¹ * y * qq ∈ R₁ := hqq_inv_conj_R₁ y hy
      have hcomm' : s * (qq⁻¹ * y * qq) = qq⁻¹ * y * qq * s := hcomm _ hy'
      calc qq * s * qq⁻¹ * y = qq * (s * (qq⁻¹ * y * qq)) * qq⁻¹ := by group
        _ = qq * ((qq⁻¹ * y * qq) * s) * qq⁻¹ := by rw [hcomm']
        _ = y * (qq * s * qq⁻¹) := by group
  have hqq_sq : qq * qq = x := by
    rw [hqqdef]
    calc n⁻¹ * (q : G) * n * (n⁻¹ * (q : G) * n)
        = n⁻¹ * ((q * q : K) : G) * n := by simp only [Subgroup.coe_mul]; group
      _ = n⁻¹ * (n * x * n⁻¹) * n := by rw [hq2]
      _ = x := by group
  have h7 : ∀ P : Subgroup G, P ≤ K₁ → IsPGroup 7 P → Nat.card P ≤ 7 := by
    intro P hPK₁ hP
    have hPK : P ≤ K := hPK₁.trans hK₁_le_K
    have hcard : Nat.card (P.subgroupOf K) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
    have hP' : IsPGroup 7 (P.subgroupOf K) := hP.comap_subtype
    have hcomm : ∀ p ∈ P.subgroupOf K, p * zetaOf z = zetaOf z * p := by
      intro p hp
      have hpP : (p : G) ∈ P := hp
      have hpK₁ : (p : G) ∈ K₁ := hPK₁ hpP
      exact Subtype.ext (by
        have hh := hK₁_comm_ζ _ hpK₁
        simpa only [Subgroup.coe_mul, hζ_coe] using hh)
    have hle := hN.syl7 (P.subgroupOf K) hP' hcomm
    rwa [hcard] at hle
  obtain ⟨k, hkK₁, j, hjndvd, hconj⟩ :=
    hsyl K₁ h7 g₀ hg₀_mem hg₀_pow hg₀_ne qq hqq_conj_K₁
  have hkK : (k : G) ∈ K := hK₁_le_K hkK₁
  have hqqk : qq * (k : G) * qq⁻¹ ∈ K₁ := hqq_conj_K₁ k hkK₁
  set κ : G := (qq * (k : G) * qq⁻¹) * (k : G) with hκdef
  have hκK₁ : κ ∈ K₁ := K₁.mul_mem hqqk hkK₁
  have hκK : κ ∈ K := hK₁_le_K hκK₁
  have hjmod : (j * j) % 7 = 1 ∨ (j * j) % 7 = 2 ∨ (j * j) % 7 = 4 := by
    have hj7 : j % 7 = 1 ∨ j % 7 = 2 ∨ j % 7 = 3 ∨ j % 7 = 4 ∨ j % 7 = 5 ∨
        j % 7 = 6 := by
      have h1 : j % 7 < 7 := Nat.mod_lt _ (by norm_num)
      have h2 : j % 7 ≠ 0 := fun h0 => hjndvd ((Nat.dvd_iff_mod_eq_zero).mpr h0)
      omega
    rcases hj7 with h | h | h | h | h | h <;>
      · rw [Nat.mul_mod, h]
        norm_num
  have hxN : x ∈ Nor (Subgroup.zpowers b) := by
    have h0 : x ∈ Nor (Subgroup.closure ({b} : Set G)) := by
      refine mem_nor_of_closure (S := {b}) fun s hs => ?_
      rw [Set.mem_singleton_iff] at hs
      rw [hs, hxb]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_singleton b))
    rwa [← Subgroup.zpowers_eq_closure] at h0
  have hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K := fun k hk => h.nor_K hxN hk
  have hα : ∀ k : K, conjAut hxK ≠ MulAut.conj k := by
    intro k hk
    apply hout k k.2
    intro y hy
    have hh := congrArg (fun α : MulAut K => ((α ⟨y, hy⟩ : K) : G)) hk
    simpa only [conjAut_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using hh
  have hstep : x * g₀ * x⁻¹ = κ * g₀ ^ (j * j) * κ⁻¹ := by
    calc x * g₀ * x⁻¹ = (qq * qq) * g₀ * (qq * qq)⁻¹ := by rw [hqq_sq]
      _ = qq * (qq * g₀ * qq⁻¹) * qq⁻¹ := by group
      _ = qq * (k * g₀ ^ j * k⁻¹) * qq⁻¹ := by rw [hconj]
      _ = (qq * (k : G) * qq⁻¹) * (qq * g₀ * qq⁻¹) ^ j * (qq * (k : G)⁻¹ * qq⁻¹) := by
        rw [conj_pow]
        group
      _ = (qq * (k : G) * qq⁻¹) * (k * g₀ ^ j * k⁻¹) ^ j * (qq * (k : G)⁻¹ * qq⁻¹) := by
        rw [hconj]
      _ = (qq * (k : G) * qq⁻¹) * (k * g₀ ^ (j * j) * k⁻¹) *
          (qq * (k : G)⁻¹ * qq⁻¹) := by
        rw [conj_pow, ← pow_mul]
      _ = κ * g₀ ^ (j * j) * κ⁻¹ := by
        rw [hκdef, show qq * (k : G)⁻¹ * qq⁻¹ = (qq * (k : G) * qq⁻¹)⁻¹ from by group]
        group
  refine (hB.g_out (conjAut hxK) hα ⟨κ, hκK⟩ (j * j) hjmod) (Subtype.ext ?_)
  rw [conjAut_apply]
  have hcoe : ((⟨κ, hκK⟩ * gOf r r' ^ (j * j) * ⟨κ, hκK⟩⁻¹ : K) : G) =
      κ * g₀ ^ (j * j) * κ⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, ← hg₀_coe]
  rw [hcoe, ← hg₀_coe]
  exact hstep

theorem not_caseB (h : Setting b K z) (hN : ModelN K z)
    (hmem : ∀ c ∈ Cen b, ∀ m : ℕ, c ^ 2 ^ m = 1 → c ∈ K)
    {x : G} (hxb : x * b * x⁻¹ = b⁻¹) (hxz : ∀ i, x * zs z i * x⁻¹ = zs z i) (hx2 : x * x = 1)
    (hout : ∀ k ∈ K, ¬ ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹)
    {n : G} (hnN : n ∈ Nor (Bt b z))
    (hn1 : n⁻¹ * (zs z 0 * (zs z 1)⁻¹) * n = b * zetaOf (zs z))
    (hn2 : n⁻¹ * zetaOf (zs z) * n = zetaOf (zs z))
    (hn3 : ∀ w : Fin 3 → ZMod 3, w 0 + w 1 + w 2 = 0 → ∀ c : G, c * b = b * c →
      c * zetaOf (zs z) = zetaOf (zs z) * c →
      c * (n⁻¹ * vecElt (zs z) w * n) = n⁻¹ * vecElt (zs z) w * n * c)
    (hnx : n * x * n⁻¹ * b * (n * x * n⁻¹)⁻¹ = b ∧
      n * x * n⁻¹ * zs z 0 * (n * x * n⁻¹)⁻¹ = zs z 0 ∧
      n * x * n⁻¹ * zs z 1 * (n * x * n⁻¹)⁻¹ = zs z 2 ∧
      n * x * n⁻¹ * zs z 2 * (n * x * n⁻¹)⁻¹ = zs z 1)
    {π x₀ : K} {r r' : Fin 2 → K} (hB : ModelNB K z π x₀ r r')
    (hρ : n⁻¹ * π * n * b * (n⁻¹ * π * n)⁻¹ = b * zetaOf (zs z) ^ 2 ∧
      n⁻¹ * π * n * zetaOf (zs z) * (n⁻¹ * π * n)⁻¹ = zetaOf (zs z) ∧
      (∀ i, n⁻¹ * π * n * zs z i * (n⁻¹ * π * n)⁻¹ = zs z i * (b * zetaOf (zs z))⁻¹) ∧
      x * (n⁻¹ * π * n) * x⁻¹ * (n⁻¹ * π * n) ∈ CenS (Bt b z)) :
    False := by
  obtain ⟨hρb, hρζ, hρz, hyB⟩ := hρ
  obtain ⟨hy, q, hq2, hqR⟩ := h.caseB_sqrt hN hmem hx2 hnN hn3 hnx hB hyB
  have hρ3 : (n⁻¹ * (π : G) * n) ^ 3 = 1 := by
    rw [show n⁻¹ * (π : G) * n = n⁻¹ * (π : G) * n⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv,
      ← Subgroup.coe_pow, hB.pi_cube, Subgroup.coe_one, mul_one, inv_mul_cancel]
  have hζ : ∀ j : Fin 2, zetaOf (zs z) = rootK₁ (zs z) j * rootK₂ (zs z) j := by
    intro j
    fin_cases j
    · rfl
    · show zs z 0 * zs z 1 * zs z 2 = zs z 1 * zs z 2 * zs z 0
      rw [mul_assoc]
      exact ((show Commute (zs z 0) (zs z 1) from h.zs_comm 0 1).mul_right
        (h.zs_comm 0 2)).eq
  have hfix : ∀ j, n⁻¹ * π * n * (r j : G) = r j * (n⁻¹ * π * n) ∧
      n⁻¹ * π * n * (r' j : G) = r' j * (n⁻¹ * π * n) := fun j => by
    obtain ⟨hW3, hR, hR', hcjp, hchar, hdist, hbraid, hbraid_eq⟩ := h.rootGood_facts hB j
    obtain ⟨hρgood, hρcjp⟩ := h.rootGood_conj_rho hmem hρb hρζ hρz j
    obtain ⟨hxgood, hxcjp⟩ := h.rootGood_conj_x hmem hxb hxz j
    refine root_fix (RootGood K z j) hW3 hR hR' hcjp hchar hdist hbraid hbraid_eq hρ3 hρgood hρcjp
      hxgood hxcjp fun t ht => (hy t (h.comm_of_mem ht.1) ?_).symm
    rw [hζ j, ← mul_assoc, ht.2.2.1, mul_assoc, ht.2.2.2.1, mul_assoc]
  exact h.caseB_final hN hmem (fun K₁ h7 g₀ hg₀ hg7 hg1 q hq =>
    exists_conj_pow_of_sylow7 K₁ h7 hg₀ hg7 hg1 hq) hxb hout hn1 hn2 hB hfix hq2 hqR

end CFSG.StandardType.GGFF.Setting

end
