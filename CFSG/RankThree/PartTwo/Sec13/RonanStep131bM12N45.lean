module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem centralizer_le_normalizer_zpowers' {G : Type} [Group G] (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro x hx
  have hfc : x ∈ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hx)
  exact Subgroup.centralizer_le_normalizer _ hfc

theorem s1n_holds (h45 : Sec4.Item4_5) : S1N := by
  intro G _ _ A c L E F a b R Y hY Q hQ3 hQC
  obtain ⟨-, hbo, -⟩ := Sec13.zpowers_mem_omegaA_iff.mp hY.hD.zpowers_mem_omegaA
  have hb3 : orderOf b = 3 := by rwa [Nat.card_zpowers] at hbo
  exact Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hY.hD.toTheoremFourHyp hb3
    hY.hD.mem_thetaComponentsAt hQ3 (hQC.trans (centralizer_le_normalizer_zpowers' b))

theorem s2e_holds (h45 : Sec4.Item4_5) : S2e := by
  intro G _ _ A c L E F a b R Y hY v v' ρ hvL hv'C hv'L hρ3 hρΘ
  have hD := hY.hCfg.hD
  have hL := hD.mem_thetaComponentsAt
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hΘC : thetaC c ≤ Subgroup.centralizer ({c} : Set G) := by
    unfold thetaC
    exact Subgroup.map_subtype_le _
  have hNΘ : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (thetaC c : Set G) :=
    Sec6.le_normalizer_theta _
  have hρC : ρ ∈ Subgroup.centralizer ({c} : Set G) := by
    have h1 : ρ = (v * v') * ((v * v')⁻¹ * ρ) := by group
    rw [h1]
    exact mul_mem (mul_mem (hLC hvL) hv'C) (hΘC hρΘ)
  have hρ3' : IsPGroup 3 (Subgroup.zpowers ρ) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ3, one_zpow]
  have hρN : ρ ∈ Subgroup.normalizer (L : Set G) :=
    Sec12.le_normalizer_of_mem_thetaComponentsAt h45 hD.toTheoremFourHyp hD.orderOf_eq hL hρ3'
      (Subgroup.zpowers_le.mpr (centralizer_le_normalizer_zpowers' c hρC)) (Subgroup.mem_zpowers ρ)
  refine ⟨hρN, ?_⟩
  set w : G := v⁻¹ * ρ with hw
  have hwN : w ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hvL)) hρN
  have hwC : w ∈ Sec4.thetaQuotCentralizer L := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hwN, fun l hl => ?_⟩
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL]
    unfold thetaC at hv'L hρΘ
    set Θ' : Subgroup G :=
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) with hΘ'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    ·
      have h1 : w * l * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hwN l).mp hl
      exact mul_mem (inv_mem hl) h1
    ·
      set θ : G := (v * v')⁻¹ * ρ with hθ
      have hwe : w = v' * θ := by rw [hw, hθ]; group
      have hΘn : ∀ x ∈ Subgroup.centralizer ({c} : Set G), ∀ y ∈ Θ',
          x * y * x⁻¹ ∈ Θ' := fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hNΘ hx) y).mp hy
      have hlC : l ∈ Subgroup.centralizer ({c} : Set G) := hLC hl
      have hθ1 : θ * l * θ⁻¹ * l⁻¹ ∈ Θ' := by
        have h2 : θ * l * θ⁻¹ * l⁻¹ = θ * (l * θ⁻¹ * l⁻¹) := by group
        rw [h2]
        exact mul_mem hρΘ (hΘn l hlC _ (inv_mem hρΘ))
      have hm : v' * (θ * l * θ⁻¹ * l⁻¹) * v'⁻¹ ∈ Θ' := hΘn v' hv'C _ hθ1
      have hA : l⁻¹ * (v' * (θ * l * θ⁻¹ * l⁻¹) * v'⁻¹) * l ∈ Θ' := by
        have := hΘn l⁻¹ (inv_mem hlC) _ hm
        simpa using this
      have hB : l⁻¹ * (v' * l * v'⁻¹ * l⁻¹) * l ∈ Θ' := by
        have := hΘn l⁻¹ (inv_mem hlC) _ (hv'L l hl)
        simpa using this
      rw [hwe]
      have hid : l⁻¹ * (v' * θ * l * (v' * θ)⁻¹) =
          (l⁻¹ * (v' * (θ * l * θ⁻¹ * l⁻¹) * v'⁻¹) * l) * (l⁻¹ * (v' * l * v'⁻¹ * l⁻¹) * l) := by
        group
      rw [hid]
      exact mul_mem hA hB
  have hρe : ρ = v * w := by rw [hw]; group
  rw [hρe]
  exact mul_mem (Subgroup.mem_sup_left hvL) (Subgroup.mem_sup_right hwC)

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
