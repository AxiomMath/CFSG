module

public import CFSG.RankThree.PartTwo.Toolkit.M12Facts
public import Certificates.Certificate8115

public section

namespace CFSG.RankThree.PartTwo.Sec12.BCensus

open CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.GH74.M12.Hyp CFSG.Blueprint Subgroup
open scoped commutatorElement

theorem cz_check : czCheck = true :=
  Certificates.certificate8115

theorem centralizer_z_le_normalizer :
    centralizer ({⁅x, y⁆} : Set G12) ≤ normalizer (P0 : Set G12) := by
  intro g hg
  obtain ⟨k, hk, hgk⟩ := exists_eq_prodP g.2
  have htg : tbl g.1 = prodT k := by rw [hgk, tbl_prodP]
  have hgz : g * ⁅x, y⁆ = ⁅x, y⁆ * g := mem_centralizer_singleton_iff.mp hg
  have hgzT : tmul (prodT k) zT = tmul zT (prodT k) := by
    have h1 := congrArg (fun u : G12 => tbl u.1) hgz
    simp only [tblG_mul, tbl_z, htg] at h1
    exact h1
  have hc := cz_check
  simp only [czCheck, List.all_eq_true] at hc
  have hk' := hc k hk
  have hpred : predC [zT] (prodT k) = true := by
    simp [predC, hgzT]
  rw [hpred, Bool.not_true, Bool.false_or] at hk'
  exact (mem_normalizer_pair_iff tbl_x tbl_y mem_P0_iff g).2 (by rw [htg]; exact hk')

theorem isSolvable_normalizer_P0 :
    Group.IsSolvable (normalizer (P0 : Set G12)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : CFSG.IsElementaryAbelian 2 QP := isElementaryAbelian_QP
  have hQs : Group.IsSolvable QP := inferInstance
  have hP3 : IsPGroup 3 (P0.subgroupOf (normalizer (P0 : Set G12))) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe P0_le_NP).toEquiv, card_P0]
    norm_num
  have : Group.IsNilpotent (P0.subgroupOf (normalizer (P0 : Set G12))) := hP3.isNilpotent
  have : Group.IsSolvable (P0.subgroupOf (normalizer (P0 : Set G12))) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient (P0.subgroupOf (normalizer (P0 : Set G12)))

theorem factorization_card_G12 :
    (Nat.card G12).factorization 3 = 3 := by
  rw [CFSG.Sporadic.Mathieu.card_M12, show (95040 : ℕ) = 3 ^ 3 * 3520 by norm_num,
    Nat.factorization_mul (pow_ne_zero 3 (by norm_num)) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem eq_bot_of_isPerfect_le_centralizer
    {w : G12} (hw1 : w ≠ 1) (P : Sylow 3 G12) (hwP : w ∈ (P : Subgroup G12))
    (hPw : (P : Subgroup G12) ≤ centralizer ({w} : Set G12)) {H : Subgroup G12}
    (hH : Group.IsPerfect H) (hHw : H ≤ centralizer ({w} : Set G12)) : H = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S₀ : Sylow 3 G12 := Sylow.ofCard P0 (by rw [card_P0, factorization_card_G12]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G12 P S₀
  have hS₀ : ((S₀ : Sylow 3 G12) : Subgroup G12) = P0 := Sylow.coe_ofCard _ _
  have hconj : ∀ u ∈ (P : Subgroup G12), g * u * g⁻¹ ∈ P0 := by
    intro u hu
    have h1 : g * u * g⁻¹ ∈ ((g • P : Sylow 3 G12) : Subgroup G12) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      exact ⟨u, hu, by simp [MulAut.smul_def]⟩
    rw [hg, hS₀] at h1
    exact h1
  have hconj' : ∀ v ∈ P0, g⁻¹ * v * g ∈ (P : Subgroup G12) := by
    intro v hv
    have hP : P = g⁻¹ • S₀ := by rw [← hg, inv_smul_smul]
    rw [hP, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨v, hS₀ ▸ hv, by simp [MulAut.smul_def]⟩
  set w' := g * w * g⁻¹ with hw'
  have hw'P : w' ∈ P0 := hconj w hwP
  have hw'C : ∀ v ∈ P0, v * w' = w' * v := by
    intro v hv
    have h2 : (g⁻¹ * v * g) * w = w * (g⁻¹ * v * g) :=
      mem_centralizer_singleton_iff.mp (hPw (hconj' v hv))
    calc v * w' = g * ((g⁻¹ * v * g) * w) * g⁻¹ := by rw [hw']; group
      _ = g * (w * (g⁻¹ * v * g)) * g⁻¹ := by rw [h2]
      _ = w' * v := by rw [hw']; group
  have hw'Z : w' ∈ zpowers ⁅x, y⁆ := by
    rw [← center_P0]
    refine ⟨⟨w', hw'P⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro v
    exact Subtype.ext (hw'C v v.2)
  have hw'1 : w' ≠ 1 := by
    intro h1
    apply hw1
    have : w = g⁻¹ * w' * g := by rw [hw']; group
    rw [this, h1]
    group
  have hord : ∀ u : G12, u ∈ P0 → u ≠ 1 → Nat.card (zpowers u) = 3 := fun u hu hu1 => by
    rw [Nat.card_zpowers, orderOf_eq_prime (cube_of_mem_P0 hu) hu1]
  have hzw : ⁅x, y⁆ ∈ zpowers w' := by
    have heq : zpowers w' = zpowers ⁅x, y⁆ :=
      Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hw'Z)
        (by rw [hord _ z_mem_P0 z_ne_one, hord _ hw'P hw'1])
    rw [heq]
    exact mem_zpowers _
  set H' := H.map (MulAut.conj g).toMonoidHom with hH'
  have hH'C : H' ≤ centralizer ({⁅x, y⁆} : Set G12) := by
    rintro _ ⟨h, hh, rfl⟩
    have hhw : h * w = w * h := mem_centralizer_singleton_iff.mp (hHw hh)
    have hcw : (g * h * g⁻¹) * w' = w' * (g * h * g⁻¹) := by
      calc (g * h * g⁻¹) * w' = g * (h * w) * g⁻¹ := by rw [hw']; group
        _ = g * (w * h) * g⁻¹ := by rw [hhw]
        _ = w' * (g * h * g⁻¹) := by rw [hw']; group
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hzw
    rw [mem_centralizer_singleton_iff]
    change (g * h * g⁻¹) * ⁅x, y⁆ = ⁅x, y⁆ * (g * h * g⁻¹)
    rw [← hm]
    exact ((Commute.zpow_right hcw m).eq)
  have hH'N : H' ≤ normalizer (P0 : Set G12) := hH'C.trans centralizer_z_le_normalizer
  have hsol : Group.IsSolvable H' := by
    have := isSolvable_normalizer_P0
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hH'N)
  have hperf : Group.IsPerfect H' := Group.IsPerfect.map _
  have hH'bot : H' = ⊥ := by
    by_contra hne
    have : Nontrivial H' := (Subgroup.nontrivial_iff_ne_bot H').mpr hne
    exact Group.IsPerfect.not_isSolvable H' hsol
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hH'bot

end CFSG.RankThree.PartTwo.Sec12.BCensus
