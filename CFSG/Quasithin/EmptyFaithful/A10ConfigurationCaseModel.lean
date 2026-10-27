module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

theorem B_cases : ∀ w : Wc, w ∈ A2 →
    w = 1 ∨ D1 w = true ∨ D2 w = true ∨ D3 w = true ∨ D4 w = true ∨ D5 w = true := by
  decide +kernel

theorem B_ne_one_involution : ∀ w : Wc, w ∈ A2 → w ≠ 1 → w * w = 1 := by decide +kernel

theorem centralizer_B_Th : ∀ x ∈ Th, (∀ y ∈ A2, x * y = y * x) → x ∈ A2 :=
  forall_mem_Th fun a ha b hb e => by
    intro hc
    have key : ∀ a ∈ dList, ∀ b ∈ dList, ∀ e : Bool,
        (∀ a' ∈ v'List, ∀ b' ∈ v'List, (⟨a, b, e⟩ : Wc) * ⟨a', b', false⟩ =
          ⟨a', b', false⟩ * ⟨a, b, e⟩) → (⟨a, b, e⟩ : Wc) ∈ A2 := by decide +kernel
    exact key a ha b hb e fun a' ha' b' hb' => hc ⟨a', b', false⟩ ⟨rfl, ha', hb'⟩

def Zset (a b : Bool) : Finset Wc :=
  Finset.univ.filter fun w => w = z0 ∨ (a = true ∧ w ∈ A2 ∧ D4 w = true) ∨
    (b = true ∧ w ∈ A2 ∧ D5 w = true)

theorem card_Zset (a b : Bool) :
    (Zset a b).card = 1 + 4 * a.toNat + 4 * b.toNat := by
  cases a <;> cases b <;> decide +kernel

theorem mem_Zset {a b : Bool} {w : Wc} : w ∈ Zset a b ↔
    w = z0 ∨ (a = true ∧ w ∈ A2 ∧ D4 w = true) ∨ (b = true ∧ w ∈ A2 ∧ D5 w = true) := by
  simp [Zset]

theorem B_compl_Zset : ∀ w : Wc, w ∈ A2 → w ≠ 1 → w ∉ Zset true true →
    D2 w = true ∨ D3 w = true := by decide +kernel

theorem mem_Zset_true : ∀ w : Wc, w ∈ A2 → (D1 w = true ∨ D4 w = true ∨ D5 w = true) →
    w ∈ Zset true true := by decide +kernel

theorem D23_not_mem_Zset : ∀ w : Wc, (D2 w = true ∨ D3 w = true) → w ∉ Zset true true := by
  decide +kernel

theorem t0_mem_D2 : D2 t0 = true := by decide +kernel

theorem R_fact : ∀ y : Wc, y ∈ A2 → (D2 y = true ∨ D3 y = true) → y ≠ t0 →
    (D2 (t0 * y) = true ∨ D3 (t0 * y) = true) → y.b = 1 := by decide +kernel

theorem P_fact : ∀ y : Wc, y ∈ A2 → (D2 y = true ∨ D3 y = true) → y.b ≠ 1 →
    y.a = 1 ∧ y.b ∈ v'List ∧ y.e = false := by decide +kernel

theorem one_V'_mem_Zset_false : ∀ b ∈ v'List, b ≠ 1 →
    (⟨1, b, false⟩ : Wc) ∈ A2 ∧ (D2 ⟨1, b, false⟩ = true ∨ D3 ⟨1, b, false⟩ = true) := by
  decide +kernel

theorem V'_generated : ∀ a ∈ v'List, ∀ b ∈ v'List, a ≠ 1 → b ≠ 1 → a ≠ b →
    ∀ v ∈ v'List, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by decide +kernel

theorem V'_third : ∀ a ∈ v'List, ∀ b ∈ v'List, a ≠ 1 → b ≠ 1 → a ≠ b →
    a * b ∈ v'List ∧ a * b ≠ 1 ∧ a * b ≠ a ∧ a * b ≠ b := by decide +kernel

theorem V'_one_mem : ∀ b ∈ v'List, (⟨1, b, false⟩ : Wc) ∈ A2 := by decide +kernel

def Ctau : Subgroup S4 :=
  subOfList [1, tau] (by decide +kernel) (by decide +kernel) (by decide +kernel)

def Cr4 : Subgroup S4 :=
  subOfList [1, r, tau, r3] (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem mem_Ctau {x : S4} : x ∈ Ctau ↔ x ∈ [1, tau] := Iff.rfl
theorem mem_Cr4 {x : S4} : x ∈ Cr4 ↔ x ∈ [1, r, tau, r3] := Iff.rfl

instance : DecidablePred (· ∈ Ctau) := fun x => decidable_of_iff (x ∈ [1, tau]) mem_Ctau.symm
instance : DecidablePred (· ∈ Cr4) := fun x => decidable_of_iff (x ∈ [1, r, tau, r3]) mem_Cr4.symm

theorem Ctau_le_D : Ctau ≤ D := by
  intro x hx
  have : ∀ x ∈ [1, tau], x ∈ dList := by decide +kernel
  exact this x hx

theorem Cr4_le_D : Cr4 ≤ D := by
  intro x hx
  have : ∀ x ∈ [1, r, tau, r3], x ∈ dList := by decide +kernel
  exact this x hx

@[expose] def Kt : Subgroup Wc := baseSub Ctau D
@[expose] def Kr : Subgroup Wc := baseSub Cr4 D

instance : DecidablePred (· ∈ Kt) := inferInstanceAs (DecidablePred (· ∈ baseSub Ctau D))
instance : DecidablePred (· ∈ Kr) := inferInstanceAs (DecidablePred (· ∈ baseSub Cr4 D))

theorem forall_mem_Kt {P : Wc → Prop} (h : ∀ a ∈ [1, tau], ∀ b ∈ dList, P ⟨a, b, false⟩) :
    ∀ x ∈ Kt, P x :=
  forall_mem_baseSub (fun _ => Iff.rfl) (fun _ => Iff.rfl) h

theorem forall_mem_Kr {P : Wc → Prop} (h : ∀ a ∈ [1, r, tau, r3], ∀ b ∈ dList, P ⟨a, b, false⟩) :
    ∀ x ∈ Kr, P x :=
  forall_mem_baseSub (fun _ => Iff.rfl) (fun _ => Iff.rfl) h

theorem Kt_le_Jh : Kt ≤ Jh := baseSub_le_baseSub Ctau_le_D le_rfl
theorem Kr_le_Jh : Kr ≤ Jh := baseSub_le_baseSub Cr4_le_D le_rfl

theorem Kt_conj : ∀ h ∈ Jh, ∀ k ∈ Kt, h * k * h⁻¹ ∈ Kt :=
  forall_mem_Jh fun a ha b hb => forall_mem_Kt fun a' ha' b' hb' => by
    revert a ha b hb a' ha' b' hb'; decide +kernel

theorem Kr_conj : ∀ h ∈ Jh, ∀ k ∈ Kr, h * k * h⁻¹ ∈ Kr :=
  forall_mem_Jh fun a ha b hb => forall_mem_Kr fun a' ha' b' hb' => by
    revert a ha b hb a' ha' b' hb'; decide +kernel

theorem commutator_Jh_le_Kt : ⁅Jh, Jh⁆ ≤ Kt := by
  rw [Subgroup.commutator_le]
  exact forall_mem_Jh fun a ha b hb => forall_mem_Jh fun a' ha' b' hb' => by
    revert a ha b hb a' ha' b' hb'; decide +kernel

theorem commutator_Jh_le_Kr : ⁅Jh, Jh⁆ ≤ Kr :=
  (commutator_Jh_le_Kt).trans (baseSub_le_baseSub (by
    intro x hx
    have : ∀ x ∈ [1, tau], x ∈ [1, r, tau, r3] := by decide +kernel
    exact this x hx) le_rfl)

theorem forall_mem_T1h {P : Wc → Prop} (h : ∀ a ∈ dList, P ⟨a, 1, false⟩) :
    ∀ x ∈ T1h, P x :=
  forall_mem_baseSub (lx := dList) (ly := [1]) (fun _ => Iff.rfl)
    (fun b => by simp [Subgroup.mem_bot]) (fun a ha b hb => by
      have : b = 1 := by simpa using hb
      subst this
      exact h a ha)

theorem forall_mem_T2h {P : Wc → Prop} (h : ∀ b ∈ dList, P ⟨1, b, false⟩) :
    ∀ x ∈ T2h, P x :=
  forall_mem_baseSub (lx := [1]) (ly := dList) (fun a => by simp [Subgroup.mem_bot])
    (fun _ => Iff.rfl) (fun a ha b hb => by
      have : a = 1 := by simpa using ha
      subst this
      exact h b hb)

theorem T2h_eq : ∀ w ∈ T2h, ∃ d ∈ dList, w = ⟨1, d, false⟩ :=
  forall_mem_T2h fun b hb => ⟨b, hb, rfl⟩

theorem f1_mem : f1 ∈ v'List := by decide +kernel
theorem f1_ne_one : f1 ≠ 1 := by decide +kernel
theorem f1_sq : f1 * f1 = 1 := by decide +kernel

theorem T1h_cases : ∀ x ∈ T1h, x = 1 ∨ x = t0 ∨ x = ⟨r, 1, false⟩ ∨ x = ⟨r3, 1, false⟩ ∨
    (x * x = 1 ∧ x ≠ 1 ∧ x ≠ t0) :=
  forall_mem_T1h (by decide +kernel)

theorem T1h_involution : ∀ x ∈ T1h, x * x = 1 → x ≠ 1 → D2 x = true ∨ D3 x = true :=
  forall_mem_T1h (by decide +kernel)

theorem T2h_involution : ∀ x ∈ T2h, x * x = 1 → x ≠ 1 → D2 x = true ∨ D3 x = true :=
  forall_mem_T2h (by decide +kernel)

theorem Jh_eq_mul : ∀ w ∈ Jh, ∃ a ∈ T1h, ∃ b ∈ T2h, w = a * b := by
  rintro ⟨a, b, e⟩ ⟨he, ha, hb⟩
  have he' : e = false := he
  subst he'
  refine ⟨⟨a, 1, false⟩, ⟨rfl, ha, Subgroup.one_mem _⟩, ⟨1, b, false⟩,
    ⟨rfl, Subgroup.one_mem _, hb⟩, ?_⟩
  refine Wc.ext ?_ ?_ rfl <;> simp [mul_false]

theorem SC1_fact : ∀ w₁ ∈ Jh, w₁ ≠ 1 → w₁ * w₁ = 1 → (D2 w₁ = true ∨ D3 w₁ = true) →
    (D2 (t0 * w₁) = true ∨ D3 (t0 * w₁) = true ∨ t0 * w₁ = 1) → w₁ ∈ T1h := by
  refine forall_mem_Jh fun a ha b hb => ?_
  revert a ha b hb
  decide +kernel

theorem SC2_fact : ∀ w₁ ∈ Jh, w₁ * w₁ = t0 →
    (⟨r, 1, false⟩ : Wc)⁻¹ * w₁ ∈ Kt ∧ (⟨r3, 1, false⟩ : Wc)⁻¹ * w₁ ∈ Kt := by
  refine forall_mem_Jh fun a ha b hb => ?_
  revert a ha b hb
  decide +kernel

theorem SC3_fact : ∀ w ∈ T1h, ∀ w₁ ∈ T1h, w * w = 1 → w₁ * w₁ = 1 → w ≠ 1 → w ≠ t0 → w₁ ≠ 1 →
    w₁ ≠ t0 → w⁻¹ * w₁ ∈ Kr :=
  forall_mem_T1h fun a ha => forall_mem_T1h fun a' ha' => by
    revert a ha a' ha'; decide +kernel

theorem r_one_sq : (⟨r, 1, false⟩ : Wc) * ⟨r, 1, false⟩ = t0 := by decide +kernel
theorem r3_one_sq : (⟨r3, 1, false⟩ : Wc) * ⟨r3, 1, false⟩ = t0 := by decide +kernel
theorem r_one_mem : (⟨r, 1, false⟩ : Wc) ∈ T1h := by decide +kernel
theorem r_one_not_mem_Kt : (⟨r, 1, false⟩ : Wc) ∉ Kt := by decide +kernel
theorem r_one_not_mem_Kr : ∀ x : Wc, x ∈ T1h → x * x = 1 → x ≠ 1 → x ≠ t0 → x ∉ Kr := by
  decide +kernel

theorem V_odd_products : ∀ v ∈ vList, ∃ a b : S4, a * a * a = 1 ∧ b * b * b = 1 ∧ a * b = v := by
  decide +kernel

theorem D_eq_V_mul_V' : ∀ d ∈ dList, ∃ v ∈ vList, ∃ v' ∈ v'List, d = v * v' := by
  decide +kernel

theorem exists_diag_odd_product :
    ∃ a b : S4, a * a * a = 1 ∧ b * b * b = 1 ∧ a * b = v2 := by decide +kernel

theorem D1_v2_v2 : D1 ⟨v2, v2, false⟩ = true := by decide +kernel

theorem one_a_commute_t0 : ∀ a : S4, (⟨1, a, false⟩ : Wc) * t0 = t0 * ⟨1, a, false⟩ := by
  decide +kernel

theorem diag_commute_s0 : ∀ a : S4, (⟨a, a, false⟩ : Wc) * s0 = s0 * ⟨a, a, false⟩ := by
  decide +kernel

theorem t0_mul_t0' : t0 * t0' = z0 := z0_eq_mul.symm

theorem D3_into_B : ∀ w : Wc, D3 w = true → ∃ v : Wc, v⁻¹ * w * v ∈ A2 := by decide +kernel

theorem card_NK : (Finset.univ.filter fun w : Wc => w ∈ A2 ∧ w ≠ 1 ∧ w ∉ Zset true true).card = 6 := by
  decide +kernel

theorem t0_ne_one : t0 ≠ 1 := by decide +kernel
theorem t0_b : t0.b = 1 := by decide +kernel
theorem card_Rm : (Finset.univ.filter fun w : Wc => w ∈ A2 ∧ w.b = 1).card = 4 := by
  decide +kernel
theorem t0'_ne_t0 : t0' ≠ t0 := by decide +kernel
theorem T1h_le_Jh : T1h ≤ Jh := baseSub_le_baseSub le_rfl bot_le
theorem T2h_le_Jh : T2h ≤ Jh := baseSub_le_baseSub bot_le le_rfl
theorem t0_not_mem_T2h : t0 ∉ T2h := by decide +kernel
theorem r_one_pow3 : (⟨r, 1, false⟩ : Wc) ^ 3 = ⟨r3, 1, false⟩ := by decide +kernel
theorem r3_one_inv : (⟨r3, 1, false⟩ : Wc)⁻¹ = ⟨r, 1, false⟩ := by decide +kernel
theorem centralizer_z0_Wc : ∀ w : Wc, w * z0 = z0 * w → w ∈ Th := by decide +kernel
theorem D2_A2 : ∀ w : Wc, w ∈ A2 → D2 w = true → w = t0 ∨ w = t0' := by decide +kernel

theorem card_Ctau : Nat.card Ctau = 2 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem card_Kt : Nat.card Kt = 16 := by
  rw [Kt, card_baseSub, card_Ctau, card_D]

theorem card_T2h : Nat.card T2h = 8 := by
  rw [T2h, card_baseSub, Subgroup.card_bot, card_D]

theorem Kt_cases : ∀ w ∈ Kt, ∃ b : Wc, b ∈ T2h ∧ (w = b ∨ w = t0 * b) :=
  forall_mem_Kt fun a ha b hb => by revert a ha b hb; decide +kernel

theorem mul_mem_Kt : ∀ a ∈ T1h, ∀ b ∈ T2h, (a = 1 ∨ a = t0) → a * b ∈ Kt :=
  forall_mem_T1h fun a ha => forall_mem_T2h fun b hb => by revert a ha b hb; decide +kernel

theorem diag_pow_three : ∀ a : S4, a * a * a = 1 → (⟨a, a, false⟩ : Wc) ^ 3 = 1 := by
  decide +kernel

theorem diag_mul : ∀ a b : S4, (⟨a, a, false⟩ : Wc) * ⟨b, b, false⟩ = ⟨a * b, a * b, false⟩ := by
  decide +kernel

theorem q_sq : (⟨v2, v2, false⟩ : Wc) * ⟨v2, v2, false⟩ = 1 := by decide +kernel
theorem q_ne_one : (⟨v2, v2, false⟩ : Wc) ≠ 1 := by decide +kernel

theorem AB_cases : ∀ w : Wc, w ∈ A1 → w ∈ A2 → w = 1 ∨ w = t0 ∨ w = t0' ∨ w = z0 := by
  decide +kernel

theorem t0'_eq_mul : t0' = t0 * z0 := by decide +kernel

theorem commutator_Jh_le_A1_inf_A2 : ⁅Jh, Jh⁆ ≤ A1 ⊓ A2 := by
  have key : ∀ x ∈ Jh, ∀ y ∈ Jh, x * y * x⁻¹ * y⁻¹ ∈ A1 ∧ x * y * x⁻¹ * y⁻¹ ∈ A2 :=
    forall_mem_Jh fun a ha b hb => forall_mem_Jh fun a' ha' b' hb' => by
      revert a ha b hb a' ha' b' hb'; decide +kernel
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact Subgroup.mem_inf.2 (key x hx y hy)

end CFSG.Quasithin.A10
