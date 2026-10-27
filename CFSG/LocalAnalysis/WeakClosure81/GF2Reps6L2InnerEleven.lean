module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Transport
public import CFSG.GH74.Generic.BProg.B2.GenLocPsl2Full
public import CFSG.GroupTheory.InvolutionPair

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.GorensteinWalter
open scoped MatrixGroups

noncomputable section

private abbrev SL2Z11 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 11)

private def q11 : SL2Z11 →* PSL2 (ZMod 11) :=
  QuotientGroup.mk' (Subgroup.center SL2Z11)

private def T0 : SL2Z11 := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
private def U0 : SL2Z11 := ⟨!![1, 3; 3, -1], by decide⟩
private def R1 : SL2Z11 := ⟨!![1, 1; 1, 2], by decide⟩
private def R2 : SL2Z11 := ⟨!![2, 0; 5, 6], by decide⟩
private def R3 : SL2Z11 := ⟨!![1, 5; 10, 7], by decide⟩

private def t0 : PSL2 (ZMod 11) := q11 T0
private def u0 : PSL2 (ZMod 11) := q11 U0
private def v0 : PSL2 (ZMod 11) := t0 * u0
private def tau1 : PSL2 (ZMod 11) := q11 R1
private def tau2 : PSL2 (ZMod 11) := q11 R2
private def tau3 : PSL2 (ZMod 11) := q11 R3

private lemma q11_neg_one : q11 (-1 : SL2Z11) = 1 := by
  change (QuotientGroup.mk' (Subgroup.center SL2Z11) (-1 : SL2Z11) : PSL2 (ZMod 11)) = 1
  rw [QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_one_iff]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, ?_, ?_⟩
  · decide
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.scalar]

private lemma q11_pow_eq_one {M : SL2Z11} {n : ℕ}
    (h : M ^ n = 1 ∨ M ^ n = -1) : (q11 M) ^ n = 1 := by
  rw [← map_pow]
  rcases h with h | h
  · rw [h, map_one]
  · rw [h, q11_neg_one]

private lemma q11_ne_one_of_ne {M : SL2Z11} (h1 : M ≠ 1) (h2 : M ≠ -1) :
    q11 M ≠ 1 := by
  have : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  intro hq
  change (QuotientGroup.mk' (Subgroup.center SL2Z11) M : PSL2 (ZMod 11)) = 1 at hq
  rw [QuotientGroup.mk'_apply] at hq
  have hc : M ∈ Subgroup.center SL2Z11 := (QuotientGroup.eq_one_iff _).mp hq
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hc
  obtain ⟨r, hr, hscalar⟩ := hc
  have hr2 : r ^ 2 = 1 := by simpa using hr
  rcases sq_eq_one_iff.mp hr2 with rfl | rfl
  · apply h1
    apply Subtype.ext
    rw [← hscalar]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.scalar]
  · apply h2
    apply Subtype.ext
    rw [← hscalar]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.scalar]

private lemma orderOf_q11_eq_prime {M : SL2Z11} {n : ℕ} (hn : Nat.Prime n)
    (hpow : M ^ n = 1 ∨ M ^ n = -1) (h1 : M ≠ 1) (h2 : M ≠ -1) :
    orderOf (q11 M) = n := by
  have : Fact (Nat.Prime n) := ⟨hn⟩
  exact orderOf_eq_prime (q11_pow_eq_one hpow) (q11_ne_one_of_ne h1 h2)

private lemma t0_mul_self : t0 * t0 = 1 := by
  rw [t0, ← map_mul, show T0 * T0 = -1 by decide, q11_neg_one]

private lemma u0_mul_self : u0 * u0 = 1 := by
  rw [u0, ← map_mul, show U0 * U0 = -1 by decide, q11_neg_one]

private lemma t0_ne_one : t0 ≠ 1 :=
  q11_ne_one_of_ne (by decide) (by decide)

private lemma u0_ne_one : u0 ≠ 1 :=
  q11_ne_one_of_ne (by decide) (by decide)

private lemma t0_comm_u0 : t0 * u0 = u0 * t0 := by
  rw [t0, u0, ← map_mul, ← map_mul,
    show T0 * U0 = (-1 : SL2Z11) * (U0 * T0) by decide,
    map_mul, q11_neg_one, one_mul]

private lemma v0_ne_one : v0 ≠ 1 := by
  rw [v0]
  exact q11_ne_one_of_ne (by decide) (by decide)

private lemma t0_ne_u0 : t0 ≠ u0 := by
  intro h
  apply v0_ne_one
  rw [v0, h, u0_mul_self]

private def V0 : Subgroup (PSL2 (ZMod 11)) := Subgroup.closure ({t0, u0} : Set (PSL2 (ZMod 11)))

private lemma V0_card : Nat.card V0 = 4 :=
  CFSG.GroupTheory.card_closure_pair_eq_four t0_mul_self u0_mul_self t0_comm_u0
    t0_ne_one u0_ne_one t0_ne_u0

private lemma V0_coe :
    (V0 : Set (PSL2 (ZMod 11))) = {1, t0, u0, t0 * u0} :=
  CFSG.GroupTheory.coe_closure_pair_eq t0_mul_self u0_mul_self t0_comm_u0
    t0_ne_one u0_ne_one t0_ne_u0

private lemma orderOf_tau1 : orderOf tau1 = 5 := by
  rw [tau1]
  exact orderOf_q11_eq_prime Nat.prime_five (Or.inl (by decide)) (by decide) (by decide)

private lemma orderOf_tau2 : orderOf tau2 = 5 := by
  rw [tau2]
  exact orderOf_q11_eq_prime Nat.prime_five (Or.inr (by decide)) (by decide) (by decide)

private lemma orderOf_tau3 : orderOf tau3 = 5 := by
  rw [tau3]
  exact orderOf_q11_eq_prime Nat.prime_five (Or.inr (by decide)) (by decide) (by decide)

private lemma odd_tau1 : Odd (orderOf tau1) := by
  rw [orderOf_tau1]; norm_num

private lemma odd_tau2 : Odd (orderOf tau2) := by
  rw [orderOf_tau2]; norm_num

private lemma odd_tau3 : Odd (orderOf tau3) := by
  rw [orderOf_tau3]; norm_num

private lemma tau1_inv : t0 * tau1 * t0⁻¹ = tau1⁻¹ := by
  calc t0 * tau1 * t0⁻¹ = q11 (T0 * R1 * T0⁻¹) := by
        simp [t0, tau1, map_mul, map_inv]
    _ = q11 R1⁻¹ := by rw [show T0 * R1 * T0⁻¹ = R1⁻¹ by decide]
    _ = tau1⁻¹ := by simp [tau1]

private lemma tau2_inv : u0 * tau2 * u0⁻¹ = tau2⁻¹ := by
  calc u0 * tau2 * u0⁻¹ = q11 (U0 * R2 * U0⁻¹) := by
        simp [u0, tau2, map_mul, map_inv]
    _ = q11 R2⁻¹ := by rw [show U0 * R2 * U0⁻¹ = R2⁻¹ by decide]
    _ = tau2⁻¹ := by simp [tau2]

private lemma tau3_inv : v0 * tau3 * v0⁻¹ = tau3⁻¹ := by
  calc v0 * tau3 * v0⁻¹ = q11 ((T0 * U0) * R3 * (T0 * U0)⁻¹) := by
        simp [v0, t0, u0, tau3, map_mul, map_inv]
    _ = q11 R3⁻¹ := by
        rw [show (T0 * U0) * R3 * (T0 * U0)⁻¹ = R3⁻¹ by decide]
    _ = tau3⁻¹ := by simp [tau3]

private def e1_3 : PSL2 (ZMod 11) := u0 * tau1 * u0 * tau1
private def e1_11 : PSL2 (ZMod 11) := t0 * u0 * tau1 * u0 * tau1 * tau1
private def e2_3 : PSL2 (ZMod 11) := t0 * tau2 * t0 * tau2
private def e2_11 : PSL2 (ZMod 11) := t0 * u0 * tau2 * t0 * tau2 * tau2
private def e3_3 : PSL2 (ZMod 11) := t0 * tau3 * t0 * tau3
private def e3_11 : PSL2 (ZMod 11) := t0 * tau3 * u0 * tau3 * tau3

private lemma orderOf_e1_3 : orderOf e1_3 = 3 := by
  have h : e1_3 = q11 (U0 * R1 * U0 * R1) := by
    simp [e1_3, u0, tau1, map_mul]
  rw [h]
  exact orderOf_q11_eq_prime Nat.prime_three (Or.inr (by decide)) (by decide) (by decide)

private lemma orderOf_e1_11 : orderOf e1_11 = 11 := by
  have h : e1_11 = q11 (T0 * U0 * R1 * U0 * R1 * R1) := by
    simp [e1_11, t0, u0, tau1, map_mul]
  rw [h]
  exact orderOf_q11_eq_prime Nat.prime_eleven (Or.inr (by decide)) (by decide) (by decide)

private lemma orderOf_e2_3 : orderOf e2_3 = 3 := by
  have h : e2_3 = q11 (T0 * R2 * T0 * R2) := by
    simp [e2_3, t0, tau2, map_mul]
  rw [h]
  exact orderOf_q11_eq_prime Nat.prime_three (Or.inr (by decide)) (by decide) (by decide)

private lemma orderOf_e2_11 : orderOf e2_11 = 11 := by
  have h : e2_11 = q11 (T0 * U0 * R2 * T0 * R2 * R2) := by
    simp [e2_11, t0, u0, tau2, map_mul]
  rw [h]
  exact orderOf_q11_eq_prime Nat.prime_eleven (Or.inl (by decide)) (by decide) (by decide)

private lemma orderOf_e3_3 : orderOf e3_3 = 3 := by
  have h : e3_3 = q11 (T0 * R3 * T0 * R3) := by
    simp [e3_3, t0, tau3, map_mul]
  rw [h]
  exact orderOf_q11_eq_prime Nat.prime_three (Or.inr (by decide)) (by decide) (by decide)

private lemma orderOf_e3_11 : orderOf e3_11 = 11 := by
  have h : e3_11 = q11 (T0 * R3 * U0 * R3 * R3) := by
    simp [e3_11, t0, u0, tau3, map_mul]
  rw [h]
  exact orderOf_q11_eq_prime Nat.prime_eleven (Or.inl (by decide)) (by decide) (by decide)

private lemma card_psl2_zmod_eleven : Nat.card (PSL2 (ZMod 11)) = 660 := by
  have : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  have hodd : IsOddPrimePower (Nat.card (ZMod 11)) :=
    ⟨11, 1, Nat.prime_eleven, by decide, by norm_num, by rw [Nat.card_zmod]; norm_num⟩
  have h := psl2_card_formula (ZMod 11) hodd
  rw [h, Nat.card_zmod]
  norm_num

private lemma closure_eq_top_of_data {τ a3 a11 : PSL2 (ZMod 11)}
    (h5 : orderOf τ = 5) (h3 : orderOf a3 = 3) (h11 : orderOf a11 = 11)
    (ha3 : a3 ∈ Subgroup.closure ({t0, u0, τ} : Set (PSL2 (ZMod 11))))
    (ha11 : a11 ∈ Subgroup.closure ({t0, u0, τ} : Set (PSL2 (ZMod 11)))) :
    Subgroup.closure ({t0, u0, τ} : Set (PSL2 (ZMod 11))) = ⊤ := by
  let H : Subgroup (PSL2 (ZMod 11)) := Subgroup.closure ({t0, u0, τ} : Set (PSL2 (ZMod 11)))
  have ht0 : t0 ∈ H := Subgroup.subset_closure (by simp)
  have hu0 : u0 ∈ H := Subgroup.subset_closure (by simp)
  have hτ : τ ∈ H := Subgroup.subset_closure (by simp)
  have h4 : 4 ∣ Nat.card H := by
    have hle : Subgroup.closure ({t0, u0} : Set (PSL2 (ZMod 11))) ≤ H := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ht0
      · exact hu0
    have hV0card : Nat.card (Subgroup.closure ({t0, u0} : Set (PSL2 (ZMod 11)))) = 4 :=
      V0_card
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [hV0card] at hdvd
  have h5dvd : 5 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H hτ
    rwa [h5] at this
  have h3dvd : 3 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H ha3
    rwa [h3] at this
  have h11dvd : 11 ∣ Nat.card H := by
    have := Subgroup.orderOf_dvd_natCard H ha11
    rwa [h11] at this
  have h660 : 660 ∣ Nat.card H := by
    have h20 : 20 ∣ Nat.card H :=
      (by decide : Nat.Coprime 4 5).mul_dvd_of_dvd_of_dvd h4 h5dvd
    have h60 : 60 ∣ Nat.card H :=
      (by decide : Nat.Coprime 20 3).mul_dvd_of_dvd_of_dvd h20 h3dvd
    have hdiv := (by decide : Nat.Coprime 60 11).mul_dvd_of_dvd_of_dvd h60 h11dvd
    rwa [show 60 * 11 = 660 by norm_num] at hdiv
  have htop : H = ⊤ := by
    refine Subgroup.eq_top_of_le_card H ?_
    rw [card_psl2_zmod_eleven]
    exact Nat.le_of_dvd Nat.card_pos h660
  exact htop

private lemma closure_tau1 :
    Subgroup.closure ({t0, u0, tau1} : Set (PSL2 (ZMod 11))) = ⊤ := by
  have ht0 : t0 ∈ Subgroup.closure ({t0, u0, tau1} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  have hu0 : u0 ∈ Subgroup.closure ({t0, u0, tau1} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  have hτ : tau1 ∈ Subgroup.closure ({t0, u0, tau1} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  refine closure_eq_top_of_data (τ := tau1) (a3 := e1_3) (a11 := e1_11)
    orderOf_tau1 orderOf_e1_3 orderOf_e1_11 ?_ ?_
  · simp only [e1_3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu0 hτ) hu0) hτ
  · simp only [e1_11]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht0 hu0) hτ) hu0) hτ) hτ

private lemma closure_tau2 :
    Subgroup.closure ({t0, u0, tau2} : Set (PSL2 (ZMod 11))) = ⊤ := by
  have ht0 : t0 ∈ Subgroup.closure ({t0, u0, tau2} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  have hu0 : u0 ∈ Subgroup.closure ({t0, u0, tau2} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  have hτ : tau2 ∈ Subgroup.closure ({t0, u0, tau2} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  refine closure_eq_top_of_data (τ := tau2) (a3 := e2_3) (a11 := e2_11)
    orderOf_tau2 orderOf_e2_3 orderOf_e2_11 ?_ ?_
  · simp only [e2_3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht0 hτ) ht0) hτ
  · simp only [e2_11]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht0 hu0) hτ) ht0) hτ) hτ

private lemma closure_tau3 :
    Subgroup.closure ({t0, u0, tau3} : Set (PSL2 (ZMod 11))) = ⊤ := by
  have ht0 : t0 ∈ Subgroup.closure ({t0, u0, tau3} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  have hu0 : u0 ∈ Subgroup.closure ({t0, u0, tau3} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  have hτ : tau3 ∈ Subgroup.closure ({t0, u0, tau3} : Set (PSL2 (ZMod 11))) :=
    Subgroup.subset_closure (by simp)
  refine closure_eq_top_of_data (τ := tau3) (a3 := e3_3) (a11 := e3_11)
    orderOf_tau3 orderOf_e3_3 orderOf_e3_11 ?_ ?_
  · simp only [e3_3]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht0 hτ) ht0) hτ
  · simp only [e3_11]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ ht0 hτ) hu0) hτ) hτ

private lemma mem_V0_iff {z : PSL2 (ZMod 11)} :
    z ∈ V0 ↔ z = 1 ∨ z = t0 ∨ z = u0 ∨ z = v0 := by
  change z ∈ (V0 : Set (PSL2 (ZMod 11))) ↔ _
  rw [V0_coe]
  simp [v0]

private lemma parrottGen_t0_u0 : ParrottGen ⊤ t0 u0 := by
  refine ⟨tau1, by simp, odd_tau1, tau1_inv, ?_⟩
  exact le_of_eq closure_tau1.symm

private lemma parrottGen_t0_v0 : ParrottGen ⊤ t0 v0 := by
  refine ⟨tau1, by simp, odd_tau1, tau1_inv, ?_⟩
  have htop : Subgroup.closure ({t0, v0, tau1} : Set (PSL2 (ZMod 11))) = ⊤ := by
    apply le_antisymm le_top
    rw [← closure_tau1]
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · have hu0 : u0 = t0 * v0 := by
        rw [v0, ← mul_assoc, t0_mul_self, one_mul]
      rw [hu0]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  exact le_of_eq htop.symm

private lemma parrottGen_u0_t0 : ParrottGen ⊤ u0 t0 := by
  refine ⟨tau2, by simp, odd_tau2, tau2_inv, ?_⟩
  have htop : Subgroup.closure ({u0, t0, tau2} : Set (PSL2 (ZMod 11))) = ⊤ := by
    rw [show ({u0, t0, tau2} : Set (PSL2 (ZMod 11))) = {t0, u0, tau2} by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto]
    exact closure_tau2
  exact le_of_eq htop.symm

private lemma parrottGen_u0_v0 : ParrottGen ⊤ u0 v0 := by
  refine ⟨tau2, by simp, odd_tau2, tau2_inv, ?_⟩
  have htop : Subgroup.closure ({u0, v0, tau2} : Set (PSL2 (ZMod 11))) = ⊤ := by
    apply le_antisymm le_top
    rw [← closure_tau2]
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · have ht0 : t0 = u0 * v0 := by
        rw [v0]
        calc t0 = t0 * (u0 * u0) := by rw [u0_mul_self, mul_one]
          _ = (t0 * u0) * u0 := by rw [mul_assoc]
          _ = (u0 * t0) * u0 := by rw [t0_comm_u0]
          _ = u0 * (t0 * u0) := by rw [mul_assoc]
      rw [ht0]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  exact le_of_eq htop.symm

private lemma parrottGen_v0_t0 : ParrottGen ⊤ v0 t0 := by
  refine ⟨tau3, by simp, odd_tau3, tau3_inv, ?_⟩
  have htop : Subgroup.closure ({v0, t0, tau3} : Set (PSL2 (ZMod 11))) = ⊤ := by
    apply le_antisymm le_top
    rw [← closure_tau3]
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · have hu0 : u0 = t0 * v0 := by
        rw [v0, ← mul_assoc, t0_mul_self, one_mul]
      rw [hu0]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  exact le_of_eq htop.symm

private lemma parrottGen_v0_u0 : ParrottGen ⊤ v0 u0 := by
  refine ⟨tau3, by simp, odd_tau3, tau3_inv, ?_⟩
  have htop : Subgroup.closure ({v0, u0, tau3} : Set (PSL2 (ZMod 11))) = ⊤ := by
    apply le_antisymm le_top
    rw [← closure_tau3]
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · have ht0 : t0 = u0 * v0 := by
        rw [v0]
        calc t0 = t0 * (u0 * u0) := by rw [u0_mul_self, mul_one]
          _ = (t0 * u0) * u0 := by rw [mul_assoc]
          _ = (u0 * t0) * u0 := by rw [t0_comm_u0]
          _ = u0 * (t0 * u0) := by rw [mul_assoc]
      rw [ht0]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  exact le_of_eq htop.symm

private lemma parrottGen_of_mem_V0 {x y : PSL2 (ZMod 11)}
    (hx : x ∈ V0) (hy : y ∈ V0) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    ParrottGen ⊤ x y := by
  rcases mem_V0_iff.mp hx with rfl | rfl | rfl | rfl
  · exact absurd rfl hx1
  · rcases mem_V0_iff.mp hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hy1
    · exact absurd rfl hxy
    · exact parrottGen_t0_u0
    · exact parrottGen_t0_v0
  · rcases mem_V0_iff.mp hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hy1
    · exact parrottGen_u0_t0
    · exact absurd rfl hxy
    · exact parrottGen_u0_v0
  · rcases mem_V0_iff.mp hy with rfl | rfl | rfl | rfl
    · exact absurd rfl hy1
    · exact parrottGen_v0_t0
    · exact parrottGen_v0_u0
    · exact absurd rfl hxy

private lemma exists_conj_map_eq_of_card_four {G : Type*} [Group G] [Finite G]
    {H V : Subgroup G} (hGcard : Nat.card G = 660)
    (hH4 : Nat.card H = 4) (hV4 : Nat.card V = 4)
    (hHp : IsPGroup 2 H) (hVp : IsPGroup 2 V) :
    ∃ g : G, H.map (MulAut.conj g).toMonoidHom = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHidx : ¬ 2 ∣ H.index := by
    have h := Subgroup.card_mul_index H
    rw [hH4, hGcard] at h
    omega
  have hVidx : ¬ 2 ∣ V.index := by
    have h := Subgroup.card_mul_index V
    rw [hV4, hGcard] at h
    omega
  let SH : Sylow 2 G := hHp.toSylow hHidx
  let SV : Sylow 2 G := hVp.toSylow hVidx
  have hSH : (SH : Subgroup G) = H := IsPGroup.toSylow_coe hHp hHidx
  have hSV : (SV : Subgroup G) = V := IsPGroup.toSylow_coe hVp hVidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (SH : Sylow 2 G) SV
  refine ⟨g, ?_⟩
  have hcoe := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul] at hcoe
  rw [hSH, hSV] at hcoe
  exact hcoe

private lemma parrottGen_of_involutions {t u : PSL2 (ZMod 11)}
    (ht : t * t = 1) (hu : u * u = 1) (hcomm : t * u = u * t)
    (ht1 : t ≠ 1) (hu1 : u ≠ 1) (hne : t ≠ u) :
    ParrottGen ⊤ t u := by
  let H : Subgroup (PSL2 (ZMod 11)) :=
    Subgroup.closure ({t, u} : Set (PSL2 (ZMod 11)))
  have hHcard : Nat.card H = 4 :=
    CFSG.GroupTheory.card_closure_pair_eq_four ht hu hcomm ht1 hu1 hne
  have hHp : IsPGroup 2 H :=
    IsPGroup.of_card (p := 2) (n := 2) (by rw [hHcard]; norm_num)
  have hV0p : IsPGroup 2 V0 :=
    IsPGroup.of_card (p := 2) (n := 2) (by rw [V0_card]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_map_eq_of_card_four (G := PSL2 (ZMod 11))
    card_psl2_zmod_eleven hHcard (show Nat.card V0 = 4 from V0_card) hHp hV0p
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  have huH : u ∈ H := Subgroup.subset_closure (by simp)
  have hx : (MulAut.conj g) t ∈ V0 := by
    rw [← hg]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom htH
  have hy : (MulAut.conj g) u ∈ V0 := by
    rw [← hg]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom huH
  have hx1 : (MulAut.conj g) t ≠ 1 := by
    intro h
    apply ht1
    have h1 : (MulAut.conj g) t = (MulAut.conj g) 1 := by simpa using h
    exact (MulAut.conj g).injective h1
  have hy1 : (MulAut.conj g) u ≠ 1 := by
    intro h
    apply hu1
    have h1 : (MulAut.conj g) u = (MulAut.conj g) 1 := by simpa using h
    exact (MulAut.conj g).injective h1
  have hxy : (MulAut.conj g) t ≠ (MulAut.conj g) u := by
    intro h
    exact hne ((MulAut.conj g).injective h)
  have hp := parrottGen_of_mem_V0 hx hy hx1 hy1 hxy
  have hmap := ParrottGen.map (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective hp
  have htop : (⊤ : Subgroup (PSL2 (ZMod 11))).map
      (MulAut.conj g⁻¹).toMonoidHom = ⊤ :=
    Subgroup.map_equiv_top (MulAut.conj g⁻¹)
  rw [htop] at hmap
  have hxt : g⁻¹ * (g * t * g⁻¹) * g = t := by group
  have hyu : g⁻¹ * (g * u * g⁻¹) * g = u := by group
  simpa [MulAut.conj_apply, hxt, hyu] using hmap

private theorem l2InnerFacts_psl2_zmod_eleven :
    L2InnerFacts (PSL2 (ZMod 11)) := by
  refine ⟨?_, ?_⟩
  · intro t u ht ht1 hu hu1 hcomm hne
    exact parrottGen_of_involutions ht hu hcomm ht1 hu1 hne
  · intro t u ht ht1 hu hu1 hcomm hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) ht1
    have huord : orderOf u = 2 := orderOf_eq_prime (by rwa [pow_two]) hu1
    have hF : Nat.card (ZMod 11) = 11 ^ 1 := by
      rw [Nat.card_zmod]
      norm_num
    exact CFSG.GH74.Generic.BProg.B2.psl2_sup_centralizer_eq_top
      (p := 11) (f := 1) hF (by norm_num) (by norm_num) htord huord hne hcomm

theorem l2InnerFacts_psl2_eleven {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 11) : L2InnerFacts (PSL2 K) := by
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = 11 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  let e : ZMod 11 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_eleven hKcard
  exact l2InnerFacts_psl2_zmod_eleven.of_mulEquiv (psl2RingEquiv e)

end
end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
