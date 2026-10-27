module
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

section Main

public theorem CFSG.lemma_4_5_c {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) [Fact (IsPGroup p R)] (hncyc : ¬ IsCyclic R) :
    ¬ IsCyclic (omega₁ (G := ↥(Subgroup.upperCentralSeries R 2)) (p := p)) ∧
      Monoid.exponent ↥(omega₁ (G := ↥(Subgroup.upperCentralSeries R 2)) (p := p)) = p := by
  classical
  let Z2 : Subgroup R := Subgroup.upperCentralSeries R 2
  let Ω : Subgroup Z2 := omega₁ (G := ↥Z2) (p := p)
  obtain ⟨A, hA_normal, hAcard, hAelem⟩ := lemma_4_5_a (R := R) (p := p) hpodd hncyc
  letI : A.Normal := hA_normal
  have hp_one_lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hA_not_cyclic : ¬ IsCyclic A := by
    intro hAcyc
    have hAexp_dvd : Nat.card A ∣ p := by
      simpa [hAcyc.exponent_eq_card] using (IsElementaryAbelian.exponent_dvd_p p A)
    have hp_lt_sq : p < p ^ 2 := pow_two_gt_prime
    have hp_sq_not_dvd : ¬ p ^ 2 ∣ p :=
      Nat.not_dvd_of_pos_of_lt (Fact.out : Nat.Prime p).pos hp_lt_sq
    exact hp_sq_not_dvd (by simpa [hAcard] using hAexp_dvd)
  have hA_nontrivial : Nontrivial A :=
    Finite.one_lt_card_iff_nontrivial.mp (hAcard ▸ one_lt_pow₀ hp_one_lt two_ne_zero)
  obtain ⟨Z, hZ_normal, hZ_le_A, hZcard_pow⟩ :=
    exists_normal_subgroup_card_pow_of_normal (G := R) (p := p) (N := A) hA_normal hAcard 1
      (by decide : 1 ≤ 2)
  have hZcard : Nat.card Z = p := by
    simpa using hZcard_pow
  letI : Z.Normal := hZ_normal
  have hZ_le_center : Z ≤ Subgroup.center R :=
    normal_subgroup_card_eq_prime_le_center (G := R) (p := p) (N := Z) hZcard
  let q : R →* R ⧸ Z := QuotientGroup.mk' Z
  let Abar : Subgroup (R ⧸ Z) := A.map q
  have hAbar_normal : Abar.Normal := by
    simpa [Abar, q] using (QuotientGroup.map_normal Z A)
  letI : Abar.Normal := hAbar_normal
  let qA : A →* Abar := q.subgroupMap A
  have hqA_surj : Function.Surjective qA := MonoidHom.subgroupMap_surjective q A
  have hqA_range_top : qA.range = ⊤ := by
    ext y
    constructor
    · intro _hy
      simp
    · intro _hy
      rcases hqA_surj y with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have hAquot_card : Nat.card (A ⧸ qA.ker) = Nat.card Abar := by
    have hcard := Nat.card_congr (QuotientGroup.quotientKerEquivRange qA).toEquiv
    simpa [hqA_range_top, Abar] using hcard
  let ZA : Subgroup A := Z.subgroupOf A
  have hqA_ker : qA.ker = ZA := by
    simpa [qA, ZA, q, QuotientGroup.ker_mk'] using (Subgroup.ker_subgroupMap (f := q) (H := A))
  have hZA_card : Nat.card ZA = p := by
    calc
      Nat.card ZA = Nat.card Z := natCard_subgroupOf_eq _ _ hZ_le_A
      _ = p := hZcard
  have hA_card_expr : Nat.card A = Nat.card (A ⧸ qA.ker) * Nat.card qA.ker := by
    simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := qA.ker))
  have hAbar_card : Nat.card Abar = p := by
    have htmp : p ^ 2 = Nat.card Abar * p := by
      calc
        p ^ 2 = Nat.card A := hAcard.symm
        _ = Nat.card (A ⧸ qA.ker) * Nat.card qA.ker := hA_card_expr
        _ = Nat.card Abar * Nat.card qA.ker := by rw [hAquot_card]
        _ = Nat.card Abar * p := by rw [hqA_ker, hZA_card]
    have hmul : p * Nat.card Abar = p * p := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using htmp.symm
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : Nat.Prime p).pos hmul
  letI : Fact (IsPGroup p (R ⧸ Z)) := ⟨(Fact.out : IsPGroup p R).to_quotient Z⟩
  have hAbar_le_center : Abar ≤ Subgroup.center (R ⧸ Z) :=
    normal_subgroup_card_eq_prime_le_center (G := R ⧸ Z) (p := p) (N := Abar) hAbar_card
  have hA_le_Z2 : A ≤ Z2 := by
    intro a ha
    refine (Subgroup.mem_upperCentralSeries_succ_iff (G := R) (n := 1) (x := a)).2 ?_
    intro r
    have haq : q a ∈ Abar := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    have hqa_center : q a ∈ Subgroup.center (R ⧸ Z) := hAbar_le_center haq
    have hcomm_mem_Z : ⁅a, r⁆ ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) (x := ⁅a, r⁆)).1
      have hcomm_eq_one : ⁅q a, q r⁆ = 1 := by
        exact (commutatorElement_eq_one_iff_mul_comm).2
          ((Subgroup.mem_center_iff.mp hqa_center) (q r)).symm
      calc
        q ⁅a, r⁆ = ⁅q a, q r⁆ := by simp [q, commutatorElement_def, MonoidHom.map_mul]
        _ = 1 := hcomm_eq_one
    simpa [Subgroup.upperCentralSeries_one] using hZ_le_center hcomm_mem_Z
  let A2 : Subgroup Z2 := A.subgroupOf Z2
  have hA2_card : Nat.card A2 = p ^ 2 := by
    calc
      Nat.card A2 = Nat.card A := natCard_subgroupOf_eq _ _ hA_le_Z2
      _ = p ^ 2 := hAcard
  have hA2_le_Ω : A2 ≤ Ω := by
    intro a ha
    change a ∈ Subgroup.closure {x : Z2 | x ^ (p ^ 1) = 1}
    refine Subgroup.subset_closure ?_
    have haA : (a : R) ∈ A := ha
    have ha_pow : (a : R) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (a : R) haA
    apply Subtype.ext
    simpa [pow_one] using ha_pow
  have hA2_not_cyclic : ¬ IsCyclic A2 := by
    intro hA2cyc
    have hAcyc : IsCyclic A := (Subgroup.subgroupOfEquivOfLe hA_le_Z2).isCyclic.mp hA2cyc
    exact hA_not_cyclic hAcyc
  have hΩ_not_cyclic : ¬ IsCyclic Ω := by
    intro hΩcyc
    letI : IsCyclic Ω := hΩcyc
    have hA2cyc : IsCyclic A2 := Subgroup.isCyclic_of_le hA2_le_Ω
    exact hA2_not_cyclic hA2cyc
  have hΩ_exp_dvd : Monoid.exponent Ω ∣ p := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    apply Subtype.ext
    simpa using
      (pth_pow_eq_one_of_mem_omega₁_upperCentralSeries_two (G := R) (p := p) hpodd x.property)
  have hA2_card_gt_one : 1 < Nat.card A2 := by
    rw [hA2_card]
    exact one_lt_pow₀ hp_one_lt two_ne_zero
  have hΩ_card_gt_one : 1 < Nat.card Ω := lt_of_lt_of_le hA2_card_gt_one (Subgroup.card_le_of_le hA2_le_Ω)
  have hΩ_nontrivial : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp hΩ_card_gt_one
  letI : Nontrivial Ω := hΩ_nontrivial
  have hZ2_p : IsPGroup p Z2 := (Fact.out : IsPGroup p R).to_subgroup Z2
  have hΩ_p : IsPGroup p Ω := hZ2_p.to_subgroup Ω
  obtain ⟨n, hn, hΩ_card⟩ := hΩ_p.nontrivial_iff_card.mp hΩ_nontrivial
  have hp_dvd_cardΩ : p ∣ Nat.card Ω := by
    rw [hΩ_card]
    exact dvd_pow_self p (Nat.ne_of_gt hn)
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hp_dvd_cardΩ_f : p ∣ Fintype.card Ω := by
    simpa [Nat.card_eq_fintype_card] using hp_dvd_cardΩ
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := Ω) p hp_dvd_cardΩ_f
  have hp_dvd_expΩ : p ∣ Monoid.exponent Ω := by
    simpa [hx] using (Monoid.order_dvd_exponent x)
  exact ⟨hΩ_not_cyclic, Nat.dvd_antisymm hΩ_exp_dvd hp_dvd_expΩ⟩


end Main
