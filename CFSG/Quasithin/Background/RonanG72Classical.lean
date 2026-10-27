module

public import CFSG.Quasithin.Background.RonanG72Basic
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.CoverOdd
public import CFSG.Quasithin.Background.Harris.G2.U33Module

public section

namespace CFSG.Quasithin.RonanG72

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G11
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem psl2_bound {L : Subgroup (GLV V)} {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h9 : 9 < p ^ e) (hL : IsPSL 2 p e ↥L) :
    6 < Module.finrank (ZMod 2) V ∧ (p ^ e ≠ 17 → 8 < Module.finrank (ZMod 2) V) := by
  obtain ⟨hd, hdvd⟩ :=
    CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.oddL2_finrank_bound hp hp2 hL
  rcases Nat.lt_or_ge (p ^ e) 19 with hlt | hge
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have he1 : e = 1 := by
      rcases e with _ | _ | e
      · simp at h9
      · rfl
      · exfalso
        have h1 : p ^ 2 ≤ p ^ (e + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hp4 : p ≤ 4 := by
          by_contra hp5
          have h25 : 25 ≤ p ^ 2 := by
            calc 25 = 5 ^ 2 := by norm_num
              _ ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
          omega
        have hp3' : p = 3 := by
          interval_cases p
          · rfl
          · exact absurd hp (by norm_num)
        subst hp3'
        rcases e with _ | e
        · norm_num at h9
        · have h27 : 27 ≤ 3 ^ (e + 1 + 1 + 1) := by
            calc 27 = 3 ^ 3 := by norm_num
              _ ≤ 3 ^ (e + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
    subst he1
    rw [pow_one] at hlt h9 hd ⊢
    have : Fact p.Prime := ⟨hp⟩
    have key : 10 ≤ Module.finrank (ZMod 2) V ∨ p = 17 := by
      interval_cases p <;> norm_num at hp
      · left
        have h := orderOf_two_le_finrank_of_dvd_card L (p := 11) (by norm_num) hdvd
        rw [ord_two_eleven] at h
        exact h
      · left
        have h := orderOf_two_le_finrank_of_dvd_card L (p := 13) (by norm_num) hdvd
        rw [ord_two_thirteen] at h
        omega
      · right
        rfl
    rcases key with h | rfl
    · exact ⟨by omega, fun _ => by omega⟩
    · exact ⟨by omega, fun h => absurd rfl h⟩
  · have : 9 ≤ (p ^ e - 1) / 2 := by omega
    exact ⟨by omega, fun _ => by omega⟩

theorem psl3_nine_le (L : Subgroup (GLV V)) {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : StatedClassicalModel X .PSL 3 p 1) (hdvd : Nat.card X ∣ Nat.card L) :
    9 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hKp : Nat.card K = p := by rw [hK, pow_one]
  have hXc : Nat.card X = Nat.card (StatedProj (StatedSL 3 K)) := Nat.card_congr e.toEquiv
  by_cases hp3 : p = 3
  · subst hp3
    have h13 := thirteen_dvd_card_psl_three_three hKp
    rw [← hXc] at h13
    have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    have h1 := orderOf_two_le_finrank_of_dvd_card L (p := 13) (by norm_num) (h13.trans hdvd)
    rw [ord_two_thirteen] at h1
    omega
  · have hp5 : 5 ≤ p := by
      have := hp.two_le
      have hp4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by norm_num)
      omega
    have hcube := p_cube_dvd_card_psl_three hp hKp
    rw [← hXc] at hcube
    exact nine_le_finrank_of_cube_dvd L hp hp5 (hcube.trans hdvd)

theorem psu3_nine_le (L : Subgroup (GLV V)) {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hX : StatedClassicalModel X .PSU 3 p 1) (hdvd : Nat.card X ∣ Nat.card L) :
    9 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hcube := p_cube_dvd_card_psu_three hp hK
  rw [← Nat.card_congr e.toEquiv] at hcube
  exact nine_le_finrank_of_cube_dvd L hp hp5 (hcube.trans hdvd)

theorem statedClassicalModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y)
    {t : StatedLieTag} {n p e : ℕ} (h : StatedClassicalModel Y t n p e) :
    StatedClassicalModel X t n p e := by
  obtain ⟨hadm, hm⟩ := h
  refine ⟨hadm, ?_⟩
  cases t with
  | PSL =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | PSU =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | PSp =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | POmegaOdd =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | POmegaPlus =>
    obtain ⟨K, i1, i2, hK, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, ⟨f.trans g⟩⟩
  | POmegaMinus =>
    obtain ⟨K, i1, i2, hK, b, c, hbc, ⟨g⟩⟩ := hm
    exact ⟨K, i1, i2, hK, b, c, hbc, ⟨f.trans g⟩⟩
  | _ => exact hm

noncomputable def equivQuotientCenter {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    X ≃* (X ⧸ Subgroup.center X) :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)


theorem u33_six {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤)
    (hd : Module.finrank (ZMod 2) V ≤ 8) (hm : StatedClassicalModel ↥L .PSU 3 3 1) :
    IsPSU 3 3 1 ↥L ∧ Module.finrank (ZMod 2) V = 6 :=
  ⟨hm, CFSG.Quasithin.G11.Harris.G2.finrank_eq_six_of_u33
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 hm).2 hm hirr hd⟩

theorem sl3_eps_bound {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤) (ε : Bool) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : IsPSLEps3 ε p 1 ↥L ∨ IsSLEps3 ε p ↥L)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    IsPSU 3 3 1 ↥L ∧ Module.finrank (ZMod 2) V = 6 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp35 : p = 3 ∨ 5 ≤ p := by
    have := hp.two_le
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  rcases hL with hL | hL
  · cases ε with
    | true =>
      have := psl3_nine_le L hp hp2 (X := ↥L) hL dvd_rfl
      omega
    | false =>
      rcases hp35 with rfl | hp5
      · exact u33_six hirr hd hL
      · have := psu3_nine_le L hp hp5 (X := ↥L) hL dvd_rfl
        omega
  · cases ε with
    | true =>
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
      have hm := CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.statedProj_quotient_center_SL
        hp hK e
      have := psl3_nine_le L hp hp2 hm (Subgroup.card_quotient_dvd_card _)
      omega
    | false =>
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hL
      obtain ⟨hm, hcen⟩ :=
        CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.statedProj_quotient_center_SU
          hp2 hK e
      rcases hp35 with rfl | hp5
      · obtain ⟨h3, h4⟩ :=
          CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.card_center_statedSU_three_dvd
            hK hcen
        have h1 : Nat.card (Subgroup.center ↥L) = 1 := by
          have h1' : Nat.card (Subgroup.center ↥(StatedSU 3 3 K)) =
              Nat.card (Subgroup.center ↥L) := by
            rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
          rw [← h1']
          exact Nat.eq_one_of_dvd_coprimes (a := 3) (b := 4) (by norm_num) h3 h4
        exact u33_six hirr hd
          (statedClassicalModel_of_mulEquiv (equivQuotientCenter (Subgroup.card_eq_one.1 h1)) hm)
      · have := psu3_nine_le L hp hp5 hm (Subgroup.card_quotient_dvd_card _)
        omega

end CFSG.Quasithin.RonanG72
