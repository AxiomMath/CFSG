module

public import CFSG.Quasithin.H13.A7Nat1238QTabCmp
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Ru
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {X : Type} [Group X] [Finite X]

theorem forall_odd_ne_of {v : ℕ}
    (h : ∀ j : ℕ, v ≠ 60 * (2 * j + 1) ∧ v ≠ 360 * (2 * j + 1) ∧ v ≠ 2520 * (2 * j + 1) ∧
      v ≠ 20160 * (2 * j + 1)) :
    ∀ k : ℕ, Odd k → v ≠ 60 * k ∧ v ≠ 360 * k ∧ v ≠ 2520 * k ∧ v ≠ 20160 * k := by
  rintro k ⟨j, rfl⟩
  exact h j

theorem not_list1222_of_psp_four_four (hZ : Odd (Nat.card (center X))) (hX : IsPSp4 2 2 X) :
    ¬ List1222 X := by
  have hc : Nat.card X = 979200 := by
    rw [(Timmesfeld.card_statedClassicalModel_two hX).2.2.1 rfl]
    decide
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_g_two_four (hZ : Odd (Nat.card (center X))) (hX : IsG2 2 2 X) :
    ¬ List1222 X := by
  have hc : Nat.card X = 251596800 := by
    have h := Timmesfeld.card_chevalleyExceptionalModel_two hX
    simp only at h
    rw [h]
    decide
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_triality_four (hZ : Odd (Nat.card (center X))) (hX : Is3D4 2 2 X) :
    ¬ List1222 X := by
  have hc : Nat.card X = ordTrialityD4 (2 ^ 2) := by
    have h := Timmesfeld.card_chevalleyExceptionalModel_two hX
    simp only at h
    exact h
  have hv : ordTrialityD4 (2 ^ 2) = 67802350642790400 := by decide
  rw [hv] at hc
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_psl_two_twentyfive (hZ : Odd (Nat.card (center X)))
    (hX : IsPSL 2 5 2 X) : ¬ List1222 X := by
  obtain ⟨-, F, hF, hFfin, hFc, ⟨e⟩⟩ := hX
  have hc : Nat.card X = 7800 := by
    rw [Nat.card_congr e.toEquiv,
      Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 2) (by norm_num), hFc]
    decide
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_psl_three_five (hZ : Odd (Nat.card (center X)))
    (hX : IsPSL 3 5 1 X) : ¬ List1222 X := by
  obtain ⟨-, F, hF, hFfin, hFc, ⟨e⟩⟩ := hX
  have hc : Nat.card X = 372000 := by
    rw [Nat.card_congr e.toEquiv,
      Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F) (n := 3) (by norm_num), hFc]
    decide
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_sl_three_five (hZ : Odd (Nat.card (center X))) (hX : IsSL3 5 X) :
    ¬ List1222 X := by
  obtain ⟨F, hF, hFfin, hFc, ⟨e⟩⟩ := hX
  have hc : Nat.card X = 372000 := by
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hFc]
    decide
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_psu_three_five (hZ : Odd (Nat.card (center X)))
    (hX : IsPSU 3 5 1 X) : ¬ List1222 X := by
  obtain ⟨-, F, hF, hFfin, hFc, ⟨e⟩⟩ := hX
  have hc : Nat.card X = 126000 := by
    rw [Nat.card_congr e.toEquiv,
      Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) Nat.prime_five le_rfl hFc
        (by norm_num)]
    decide
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_su_three_five (hZ : Odd (Nat.card (center X))) (hX : IsSU3 5 X) :
    ¬ List1222 X := by
  obtain ⟨F, hF, hFfin, hFc, ⟨e⟩⟩ := hX
  set S := Assembly.LowTwoRank.StatedSU 3 5 F with hSdef
  set N := (Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf S with hN
  have hP : Nat.card (S ⧸ N) = 126000 := by
    have h := Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) (p := 5) (f := 1)
      Nat.prime_five le_rfl (by rw [hFc]; norm_num) (by norm_num : 2 ≤ 3)
    simp only [pow_one] at h
    rw [show Nat.card (S ⧸ N) = Nat.card (Assembly.LowTwoRank.StatedProj S) from rfl, h]
    decide
  have hS : Nat.card ↥S = 126000 * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hP]
  have hNodd : Odd (Nat.card N) := by
    have hNZ : N.map e.symm.toMonoidHom ≤ center X := by
      rintro _ ⟨n, hn, rfl⟩
      have hc := statedScalars_subgroupOf_le_center S hn
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro y
      apply e.injective
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
      exact hc (e y)
    have h1 := Subgroup.card_dvd_of_le hNZ
    rw [Subgroup.card_map_of_injective e.symm.injective] at h1
    exact Odd.of_dvd_nat hZ h1
  have hc : Nat.card X = 126000 * Nat.card N := by rw [Nat.card_congr e.toEquiv, hS]
  obtain ⟨m, hm⟩ := hNodd
  rw [hm] at hc
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_m22 (hZ : Odd (Nat.card (center X)))
    (hX : IsSporadic .M22 X) : ¬ List1222 X := by
  obtain ⟨e⟩ := hX
  have hc : Nat.card X = 443520 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M22
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_m22_hat
    (hZ : Odd (Nat.card (center X)))
    (hX : IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22)) : ¬ List1222 X := by
  obtain ⟨-, hZ3, ⟨e⟩⟩ := hX
  have hc : Nat.card X = 1330560 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    have h2 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
      CFSG.Sporadic.Mathieu.card_M22
    rw [Nat.card_congr e.toEquiv, h2, hZ3] at h1
    omega
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_m23
    (hZ : Odd (Nat.card (center X))) (hX : IsSporadic .M23 X) : ¬ List1222 X := by
  obtain ⟨e⟩ := hX
  have hc : Nat.card X = 10200960 := by
    rw [Nat.card_congr e.toEquiv]
    show Nat.card CFSG.Blueprint.NativeSporadic.M23 = 10200960
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
    exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
      CFSG.M23.M23Group.card_M23
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_j1 (hZ : Odd (Nat.card (center X)))
    (hX : IsSporadic .J1 X) : ¬ List1222 X := by
  obtain ⟨e⟩ := hX
  have hc : Nat.card X = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_j2 (hZ : Odd (Nat.card (center X)))
    (hX : IsSporadic .J2 X) : ¬ List1222 X := by
  obtain ⟨e⟩ := hX
  have hc : Nat.card X = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_j4 (hZ : Odd (Nat.card (center X)))
    (hX : IsSporadic .J4 X) : ¬ List1222 X := by
  obtain ⟨e⟩ := hX
  have hc : Nat.card X = 86775571046077562880 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J4.card_J4
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_hs (hZ : Odd (Nat.card (center X)))
    (hX : IsSporadic .HS X) : ¬ List1222 X := by
  obtain ⟨e⟩ := hX
  have hc : Nat.card X = 44352000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.HS.card_HS
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

theorem not_list1222_of_ru (hZ : Odd (Nat.card (center X)))
    (hX : IsSporadic .Ru X) : ¬ List1222 X := by
  obtain ⟨e⟩ := hX
  have hc : Nat.card X = 145926144000 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Ru.card_Ru
  exact not_list1222_of_card' hZ hc (by omega) (forall_odd_ne_of fun j => by omega)

end CFSG.Quasithin.H13.A7
