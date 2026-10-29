module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFBase

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

private theorem zmod2_one_of_ne_nsbfa : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

private theorem char2_eq_nsbfa : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide

private theorem two_eq_zero_nsbfa : (2 : ZMod 2) = 0 := by decide

private theorem coef_zero_nsbfa {ι : Type*} {x₁ x₂ : ι → ZMod 2} (h1 : x₁ ≠ 0) (h2 : x₂ ≠ 0)
    (h12 : x₁ ≠ x₂) (c₁ c₂ : ZMod 2) (h : ∀ i, x₁ i * c₁ + x₂ i * c₂ = 0) :
    c₁ = 0 ∧ c₂ = 0 := by
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c₁ with rfl | rfl <;> rcases hc c₂ with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso
    apply h2
    funext i
    have hi := h i
    simpa using hi
  · exfalso
    apply h1
    funext i
    have hi := h i
    simpa using hi
  · exfalso
    apply h12
    funext i
    have hi := h i
    simp only [mul_one] at hi
    exact char2_eq_nsbfa _ _ hi

theorem eq_zero_of_actM_eq_zero {j n : ℕ} (hj : 0 < j) {B : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : ∀ Y : Fin j → Fin n → ZMod 2, actM B Y = 0) : B = 0 := by
  have hv : ∀ v : Fin n → ZMod 2, B.mulVec v = 0 := by
    intro v
    have hY := congrFun (h (fun i => if i = ⟨0, hj⟩ then v else 0)) ⟨0, hj⟩
    simpa [actM_apply] using hY
  ext i b
  have hib := congrFun (hv (Pi.single b 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hib

theorem tens_right_injective {j n : ℕ} {a : Fin n → ZMod 2} (ha : a ≠ 0) :
    Function.Injective (fun x : Fin j → ZMod 2 => tens a x) := by
  intro x x' hxx
  obtain ⟨b, hb⟩ : ∃ b, a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  have hb1 : a b = 1 := zmod2_one_of_ne_nsbfa _ hb
  funext i
  have hi := congrFun (congrFun hxx i) b
  simp only [tens_apply_apply] at hi
  rw [hb1, mul_one, mul_one] at hi
  exact hi

theorem tens_left_injective {j n : ℕ} {x : Fin j → ZMod 2} (hx : x ≠ 0) :
    Function.Injective (fun a : Fin n → ZMod 2 => tens a x) := by
  intro a a' haa
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  have hi1 : x i = 1 := zmod2_one_of_ne_nsbfa _ hi
  have he := congrFun haa i
  simp only [tens_apply, hi1, one_smul] at he
  exact he

theorem tens_pair_injective {j n : ℕ} {x₁ x₂ : Fin j → ZMod 2} (h1 : x₁ ≠ 0) (h2 : x₂ ≠ 0)
    (h12 : x₁ ≠ x₂) :
    Function.Injective
      (fun p : (Fin n → ZMod 2) × (Fin n → ZMod 2) => tens p.1 x₁ + tens p.2 x₂) := by
  rintro ⟨u₁, u₂⟩ ⟨u₁', u₂'⟩ hp
  have hc : ∀ b : Fin n, u₁ b - u₁' b = 0 ∧ u₂ b - u₂' b = 0 := by
    intro b
    apply coef_zero_nsbfa h1 h2 h12
    intro i
    have hi := congrFun (congrFun hp i) b
    simp only [Pi.add_apply, tens_apply_apply] at hi
    linear_combination hi
  have e1 : u₁ = u₁' := funext fun b => sub_eq_zero.mp (hc b).1
  have e2 : u₂ = u₂' := funext fun b => sub_eq_zero.mp (hc b).2
  rw [e1, e2]

theorem rank_one_sum {j n : ℕ} {a₁ a₂ a₃ : Fin n → ZMod 2} {t₁ t₂ t₃ : Fin j → ZMod 2}
    (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₁₂ : a₁ ≠ a₂) (h₃ : a₃ ≠ 0) (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (ht₃ : t₃ ≠ 0) (h : tens a₁ t₁ + tens a₂ t₂ = tens a₃ t₃) :
    t₁ = t₂ ∧ t₂ = t₃ ∧ a₃ = a₁ + a₂ := by
  have hpt : ∀ i b, t₁ i * a₁ b + t₂ i * a₂ b = t₃ i * a₃ b := by
    intro i b
    have hib := congrFun (congrFun h i) b
    simpa only [Pi.add_apply, tens_apply_apply] using hib
  obtain ⟨i₃, hi₃⟩ : ∃ i, t₃ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ht₃ (funext hcon)
  have hi₃' : t₃ i₃ = 1 := zmod2_one_of_ne_nsbfa _ hi₃
  have ha₃ : a₃ = t₁ i₃ • a₁ + t₂ i₃ • a₂ := by
    funext b
    have hb := hpt i₃ b
    rw [hi₃', one_mul] at hb
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hb.symm
  have hkey : ∀ i, t₁ i = t₃ i * t₁ i₃ ∧ t₂ i = t₃ i * t₂ i₃ := by
    intro i
    have hv : ∀ b, a₁ b * (t₁ i + t₃ i * t₁ i₃) + a₂ b * (t₂ i + t₃ i * t₂ i₃) = 0 := by
      intro b
      have hb1 := hpt i b
      have hb2 := congrFun ha₃ b
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hb2
      linear_combination hb1 + t₃ i * hb2 +
        (t₃ i * t₁ i₃ * a₁ b + t₃ i * t₂ i₃ * a₂ b) * two_eq_zero_nsbfa
    obtain ⟨c₁, c₂⟩ := coef_zero_nsbfa h₁ h₂ h₁₂ _ _ hv
    exact ⟨char2_eq_nsbfa _ _ c₁, char2_eq_nsbfa _ _ c₂⟩
  have hp : t₁ i₃ = 1 := by
    apply zmod2_one_of_ne_nsbfa
    intro hz
    apply ht₁
    funext i
    rw [Pi.zero_apply, (hkey i).1, hz, mul_zero]
  have hq : t₂ i₃ = 1 := by
    apply zmod2_one_of_ne_nsbfa
    intro hz
    apply ht₂
    funext i
    rw [Pi.zero_apply, (hkey i).2, hz, mul_zero]
  have e1 : t₁ = t₃ := funext fun i => by rw [(hkey i).1, hp, mul_one]
  have e2 : t₂ = t₃ := funext fun i => by rw [(hkey i).2, hq, mul_one]
  refine ⟨e1.trans e2.symm, e2, ?_⟩
  rw [ha₃, hp, hq, one_smul, one_smul]

theorem exists_ne_zero_mulVec {n : ℕ} {B : Matrix (Fin n) (Fin n) (ZMod 2)} (hB : B ≠ 0) :
    ∃ b : Fin n, B.mulVec (Pi.single b 1) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hB
  ext i b
  have hib := congrFun (hcon b) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hib

end CFSG.Quasithin.H13.Ch4.NSB
