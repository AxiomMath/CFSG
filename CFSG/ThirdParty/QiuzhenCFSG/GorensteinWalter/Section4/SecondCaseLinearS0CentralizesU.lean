module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationNine
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseTwoSubgroupCentralizesU
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Equation (9): the rotation subgroup centralizes the odd core

After the ambient Sylow subgroup lies in the linear component, its cyclic
rotation subgroup and the odd factor `K0` have commuting images in the PSL₂
torus.  Normality of `K0` and its trivial intersection with the odd center
lift that commutation to the component.  The equation-(7) coprime-action
transfer then shows that `S0` centralizes all of `U`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- At the equation-(9) endpoint `S ≤ E`, the rotation subgroup `S0`
centralizes `U`. -/
public theorem secondCase_linear_S0_centralizes_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (torus : SecondCasePSL2QuotientTorusCard d K)
    (od : SecondCaseLinearOmegaData c w d)
    (hSleE : (c.S : Subgroup G) ≤ d.E)
    (hK0normal : IsNormalIn od.K0 (c.H ⊓ w.M))
    (hS0leT : (c.S0.subgroupOf d.E).map
      (QuotientGroup.mk' (Subgroup.center d.E)) ≤ torus.T) :
    (c.S0 : Subgroup G) ≤ Subgroup.centralizer (c.U : Set G) := by
  classical
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  have hS0leE : (c.S0 : Subgroup G) ≤ d.E :=
    c.S0_le_S.trans hSleE
  have hK0leK : od.K0 ≤ od.K := by
    rw [od.K0_eq]
    exact inf_le_right
  have hK0leE : od.K0 ≤ d.E := hK0leK.trans od.K_le_E
  have hK0mapT : (od.K0.subgroupOf d.E).map q ≤ torus.T :=
    secondCase_equationNine_K0_quotient_le_torus c w d od.s od.K od.K0
      od.K_inverted od.K0_eq hK0leE torus.T torus.T_odd_centralized_le
  have hsI : IsInvolution od.s := by
    constructor
    · intro hsone
      exact od.s_involution.1 (congrArg Subtype.val hsone)
    · apply Subtype.ext
      exact od.s_involution.2
  have hK0center : od.K0 ⊓
      (Subgroup.center d.E).map d.E.subtype = ⊥ :=
    secondCase_equationNine_K0_intersection_center_eq_bot
      c w d od.s od.K od.K0 od.K_inverted od.K0_eq hsI
  have hS0centK0 : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (od.K0 : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    let aE : d.E := ⟨a, hS0leE ha⟩
    let kE : d.E := ⟨k, hK0leE hk⟩
    let aT : torus.T := ⟨q aE, hS0leT
      (Subgroup.mem_map.mpr ⟨aE, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)⟩
    let kT : torus.T := ⟨q kE, hK0mapT
      (Subgroup.mem_map.mpr ⟨kE, Subgroup.mem_subgroupOf.mpr hk, rfl⟩)⟩
    let : IsCyclic torus.T := torus.T_cyclic
    let : CommGroup torus.T := IsCyclic.commGroup
    have hqcomm : q aE * q kE = q kE * q aE := by
      simpa [aT, kT] using congrArg Subtype.val (mul_comm aT kT)
    have hqconj : q (aE * kE * aE⁻¹) = q kE := by
      simp only [map_mul, map_inv]
      rw [hqcomm]
      simp
    let zE : d.E := (aE * kE * aE⁻¹) * kE⁻¹
    have hqz : q zE = 1 := by
      calc
        q zE = q (aE * kE * aE⁻¹) * q (kE⁻¹) := by rw [map_mul]
        _ = q kE * (q kE)⁻¹ := by rw [hqconj, map_inv]
        _ = 1 := mul_inv_cancel _
    have hzCenter : zE ∈ Subgroup.center d.E :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center d.E) zE).mp hqz
    have haC : a ∈ c.H ⊓ w.M :=
      ⟨centralizerSetup_S_le_H c (c.S0_le_S ha),
        d.E_component.1 (hS0leE ha)⟩
    have hkconj : a * k * a⁻¹ ∈ od.K0 :=
      hK0normal.2 a haC k hk
    have hzK0 : (zE : G) ∈ od.K0 :=
      od.K0.mul_mem hkconj (od.K0.inv_mem hk)
    have hzCenterMap : (zE : G) ∈
        (Subgroup.center d.E).map d.E.subtype :=
      Subgroup.mem_map.mpr ⟨zE, hzCenter, rfl⟩
    have hzInf : (zE : G) ∈ od.K0 ⊓
        (Subgroup.center d.E).map d.E.subtype := ⟨hzK0, hzCenterMap⟩
    rw [hK0center] at hzInf
    have hzOne : zE = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp hzInf
    have hconj : a * k * a⁻¹ = k := by
      have hzAmbient := congrArg Subtype.val hzOne
      exact mul_inv_eq_one.mp (by simpa [zE, aE, kE] using hzAmbient)
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  have hS0centF : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (od.F : Set G) := by
    apply Subgroup.le_centralizer_iff.mp
    exact od.F_centralizes_E.trans
      (Subgroup.centralizer_le (SetLike.coe_mono hS0leE))
  have hS0centJoin : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer ((od.K0 ⊔ od.F : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with hx | hx
      · exact (Subgroup.mem_centralizer_iff.mp (hS0centK0 ha)) x hx
      · exact (Subgroup.mem_centralizer_iff.mp (hS0centF ha)) x hx
    · intro y hy
      rcases hy with hy | hy
      · have h := (Subgroup.mem_centralizer_iff.mp (hS0centK0 ha)) y hy
        calc
          y⁻¹ * a = y⁻¹ * (a * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * a) * y⁻¹ := by rw [← h]
          _ = a * y⁻¹ := by group
      · have h := (Subgroup.mem_centralizer_iff.mp (hS0centF ha)) y hy
        calc
          y⁻¹ * a = y⁻¹ * (a * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * a) * y⁻¹ := by rw [← h]
          _ = a * y⁻¹ := by group
    · simp
    · intro x y _ _ hx hy
      calc
        (x * y) * a = x * (y * a) := by group
        _ = x * (a * y) := by rw [hy]
        _ = (x * a) * y := by group
        _ = (a * x) * y := by rw [hx]
        _ = a * (x * y) := by group
  have hS0centY : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (((c.FU ⊓ w.M : Subgroup G)) : Set G) := by
    rw [← od.FU_inter_M_eq]
    exact hS0centJoin
  have hS0leC : (c.S0 : Subgroup G) ≤ c.H ⊓ w.M := by
    intro a ha
    exact ⟨centralizerSetup_S_le_H c (c.S0_le_S ha),
      d.E_component.1 (hS0leE ha)⟩
  have hS0p : IsPGroup 2 (c.S0 : Subgroup G) := by
    have hpS0S : IsPGroup 2 (c.S0.subgroupOf (c.S : Subgroup G)) :=
      c.S.isPGroup'.to_subgroup (c.S0.subgroupOf (c.S : Subgroup G))
    exact hpS0S.of_equiv (Subgroup.subgroupOfEquivOfLe c.S0_le_S)
  have hFne : od.F ≠ ⊥ := by
    intro hFbot
    have hPbot : od.P = ⊥ := by
      apply le_bot_iff.mp
      exact od.P_le_F.trans (le_of_eq hFbot)
    have hPcard := od.P_card
    have hpone : od.p = 1 := by
      rw [hPbot] at hPcard
      simpa using hPcard.symm
    exact od.hp_prime.ne_one hpone
  have hFleY : od.F ≤ c.FU ⊓ w.M := by
    rw [← od.FU_inter_M_eq]
    exact le_sup_right
  exact secondCase_twoSubgroup_centralizes_U_of_centralizes_fitting_inter
    hmin c w od.F od.F_normal_M hFne hFleY (c.S0 : Subgroup G)
      hS0p hS0leC hS0centY

end CFSG.GorensteinWalter
