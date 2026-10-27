module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
open scoped Pointwise commutatorElement
noncomputable section
namespace CFSG.GorensteinWalter
universe u
variable {G : Type u} [Group G] [Finite G]
variable (c : CentralizerSetup G) (w : SecondCaseWitness c)
variable (d : SecondCaseComponentData w)
variable (od : SecondCaseLinearOmegaData c w d)

private theorem F_le_FU : od.F ≤ c.FU := by
  intro f hf
  rw [od.F_fixed] at hf
  exact hf.1.1

private theorem K0_le_K : od.K0 ≤ od.K := by
  rw [od.K0_eq]
  exact inf_le_right

private theorem K0_le_M : od.K0 ≤ w.M := by
  intro x hx
  have hxK : x ∈ od.K := K0_le_K c w d od hx
  have hxI : x ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
    rw [← od.K_inverted]
    exact hxK
  exact hxI.1.2

private theorem K0_sup_F_comm : ⁅od.K0, od.F⁆ = ⊥ := by
  apply le_bot_iff.mp
  rw [Subgroup.commutator_le]
  intro k hk f hf
  have hkE : (k : G) ∈ d.E := od.K_le_E (K0_le_K c w d od hk)
  have hcent : (f : G) ∈ Subgroup.centralizer (d.E : Set G) := od.F_centralizes_E hf
  have hcomm : (f : G) * (k : G) = (k : G) * (f : G) :=
    (Subgroup.mem_centralizer_iff.mp hcent (k : G) hkE).symm
  rw [commutatorElement_def, ← hcomm]
  exact Subgroup.mem_bot.mpr (by group)
 
private theorem F_order_p_eq_P :
    {x : G | x ∈ od.F ∧ x ^ od.p = 1} = (od.P : Set G) := by
  classical
  let S : Set G := {x : G | x ∈ od.F ∧ x ^ od.p = 1}
  let : Fintype (↥od.F) := Fintype.ofFinite (↥od.F)
  let : IsCyclic (↥od.F) := od.F_cyclic
  have hp_pos : 0 < od.p := od.hp_prime.pos
  have hPsubS : (od.P : Set G) ⊆ S := by
    intro x hx
    exact ⟨od.P_le_F hx,
      (orderOf_dvd_iff_pow_eq_one (x := x) (n := od.p)).mp (by
        simpa [od.P_card] using (Subgroup.orderOf_dvd_natCard od.P hx))⟩
  have hScard : Nat.card {x : G // x ∈ S} = od.p := by
    apply le_antisymm
    · let e : {x : G // x ∈ S} ≃ {a : (↥od.F) // a ^ od.p = 1} :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            apply Subtype.ext
            simpa using x.2.2⟩
          invFun := fun a => ⟨(a.1 : G), ⟨a.1.2, by
            exact congrArg Subtype.val a.2⟩⟩
          left_inv := by intro x; rfl
          right_inv := by intro a; rfl }
      calc
        Nat.card {x : G // x ∈ S} = Nat.card {a : (↥od.F) // a ^ od.p = 1} := Nat.card_congr e
        _ = Fintype.card {a : (↥od.F) // a ^ od.p = 1} := by rw [Nat.card_eq_fintype_card]
        _ ≤ od.p := by
          simpa [Fintype.card_subtype] using
            (IsCyclic.card_pow_eq_one_le (α := (↥od.F)) (n := od.p) hp_pos)
    · have hle : Nat.card od.P ≤ Nat.card {x : G // x ∈ S} :=
        Nat.card_le_card_of_injective (fun x : od.P => ⟨(x : G), hPsubS x.2⟩) (by
          intro a b h
          simpa using congrArg Subtype.val h)
      simpa [od.P_card] using hle
  have hcard : Nat.card {x : G // x ∈ S} ≤ Nat.card {x : G // x ∈ (od.P : Set G)} := by
    exact le_of_eq (by
      change Nat.card {x : G // x ∈ S} = Nat.card (↥od.P)
      rw [hScard, od.P_card])
  let : Fintype (↥od.P) := Fintype.ofFinite (↥od.P)
  exact (Set.eq_of_subset_of_card_le hPsubS (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard)).symm

private theorem K0_order_p_eq_P0 :
    {x : G | x ∈ od.K0 ∧ x ^ od.p = 1} = (od.P0 : Set G) := by
  classical
  let S : Set G := {x : G | x ∈ od.K0 ∧ x ^ od.p = 1}
  let : Fintype (↥od.K0) := Fintype.ofFinite (↥od.K0)
  let : IsCyclic (↥od.K) := od.K_cyclic
  let : IsCyclic (↥od.K0) := Subgroup.isCyclic_of_le (K0_le_K c w d od)
  have hp_pos : 0 < od.p := od.hp_prime.pos
  have hP0subS : (od.P0 : Set G) ⊆ S := by
    intro x hx
    exact ⟨od.P0_le_K0 hx,
      (orderOf_dvd_iff_pow_eq_one (x := x) (n := od.p)).mp (by
        simpa [od.P0_card] using (Subgroup.orderOf_dvd_natCard od.P0 hx))⟩
  have hScard : Nat.card {x : G // x ∈ S} = od.p := by
    apply le_antisymm
    · let e : {x : G // x ∈ S} ≃ {a : (↥od.K0) // a ^ od.p = 1} :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            apply Subtype.ext
            simpa using x.2.2⟩
          invFun := fun a => ⟨(a.1 : G), ⟨a.1.2, by
            exact congrArg Subtype.val a.2⟩⟩
          left_inv := by intro x; rfl
          right_inv := by intro a; rfl }
      calc
        Nat.card {x : G // x ∈ S} = Nat.card {a : (↥od.K0) // a ^ od.p = 1} := Nat.card_congr e
        _ = Fintype.card {a : (↥od.K0) // a ^ od.p = 1} := by rw [Nat.card_eq_fintype_card]
        _ ≤ od.p := by
          simpa [Fintype.card_subtype] using
            (IsCyclic.card_pow_eq_one_le (α := (↥od.K0)) (n := od.p) hp_pos)
    · have hle : Nat.card od.P0 ≤ Nat.card {x : G // x ∈ S} :=
        Nat.card_le_card_of_injective (fun x : od.P0 => ⟨(x : G), hP0subS x.2⟩) (by
          intro a b h
          simpa using congrArg Subtype.val h)
      simpa [od.P0_card] using hle
  have hcard : Nat.card {x : G // x ∈ S} ≤ Nat.card {x : G // x ∈ (od.P0 : Set G)} := by
    exact le_of_eq (by
      change Nat.card {x : G // x ∈ S} = Nat.card (↥od.P0)
      rw [hScard, od.P0_card])
  let : Fintype (↥od.P0) := Fintype.ofFinite (↥od.P0)
  exact (Set.eq_of_subset_of_card_le hP0subS (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard)).symm

private theorem pow_one_of_sup_le_A :
    ∀ x : G, x ∈ od.K0 ⊔ od.F → x ^ od.p = 1 → x ∈ od.A := by
  intro x hx hxp
  have hcentF : od.F ≤ Subgroup.centralizer (od.K0 : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (od.F_centralizes_E hf))
      (k : G) (od.K_le_E (K0_le_K c w d od hk))
  have hF_norm_K0 : od.F ≤ Subgroup.normalizer (od.K0 : Set G) := by
    intro f hf
    exact Subgroup.centralizer_le_normalizer (od.K0 : Set G) (hcentF hf)
  have hx' : x ∈ (od.K0 : Set G) * (od.F : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left od.K0 od.F hF_norm_K0]
    exact hx
  rcases Set.mem_mul.mp hx' with ⟨k, hk, f, hf, hxeq⟩
  have hcomm1 : ⁅k, f⁆ = 1 := by
    have hmem : ⁅k, f⁆ ∈ ⁅od.K0, od.F⁆ :=
      Subgroup.commutator_mem_commutator hk hf
    rw [K0_sup_F_comm c w d od] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hcomm : Commute (k : G) (f : G) :=
    (commutatorElement_eq_one_iff_commute).mp hcomm1
  have hpow : (k * f) ^ od.p = (k : G) ^ od.p * (f : G) ^ od.p := hcomm.mul_pow od.p
  have hkfpow : (k : G) ^ od.p * (f : G) ^ od.p = 1 := by
    rw [← hpow]
    simpa [hxeq] using hxp
  have hkp_mem_K0 : (k : G) ^ od.p ∈ od.K0 := od.K0.pow_mem hk od.p
  have hkp_mem_F : (k : G) ^ od.p ∈ od.F := by
    rw [eq_inv_of_mul_eq_one_left hkfpow]
    exact od.F.inv_mem (od.F.pow_mem hf od.p)
  have hkp_one : (k : G) ^ od.p = 1 := by
    have hmem : (k : G) ^ od.p ∈ od.K0 ⊓ od.F := ⟨hkp_mem_K0, hkp_mem_F⟩
    have hmem' : (k : G) ^ od.p ∈ od.F ⊓ od.K0 := by simpa [inf_comm] using hmem
    have hbot : (k : G) ^ od.p ∈ (⊥ : Subgroup G) := by
      rw [secondCase_linear_omega_F_cap_K0 c w d od] at hmem'
      exact hmem'
    exact Subgroup.mem_bot.mp hbot
  have hfp_one : (f : G) ^ od.p = 1 := by
    have hfp_inv : (f : G) ^ od.p = ((k : G) ^ od.p)⁻¹ :=
      eq_inv_of_mul_eq_one_right hkfpow
    rw [hfp_inv, hkp_one]
    simp
  have hk_mem_P0 : k ∈ od.P0 := by
    have hkS : (k : G) ∈ {x : G | x ∈ od.K0 ∧ x ^ od.p = 1} := ⟨hk, hkp_one⟩
    rw [K0_order_p_eq_P0 c w d od] at hkS
    exact hkS
  have hf_mem_P : f ∈ od.P := by
    have hfS : (f : G) ∈ {x : G | x ∈ od.F ∧ x ^ od.p = 1} := ⟨hf, hfp_one⟩
    rw [F_order_p_eq_P c w d od] at hfS
    exact hfS
  have hxA : k * f ∈ od.P0 ⊔ od.P :=
    (od.P0 ⊔ od.P).mul_mem
      (Subgroup.mem_sup_left hk_mem_P0) (Subgroup.mem_sup_right hf_mem_P)
  rw [od.A_eq]
  rw [← hxeq]
  simpa [sup_comm] using hxA

private theorem P_le_pCore :
    od.P ≤ (pCore od.p (↥c.U)).map c.U.subtype := by
  let : Fact od.p.Prime := ⟨od.hp_prime⟩
  have hPleU : od.P ≤ c.U := (od.P_le_F.trans (F_le_FU c w d od)).trans (fittingSubgroupOf_le c.U)
  let P' : Subgroup (↥c.U) := od.P.subgroupOf c.U
  have hPcard' : Nat.card P' = od.p :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleU).toEquiv).trans od.P_card
  have hP'p : IsPGroup od.p (↥P') := by
    refine IsPGroup.of_card (n := 1) ?_
    simpa [pow_one] using hPcard'
  have hP'leF : P' ≤ fittingSubgroup (↥c.U) := by
    intro x hx
    change (x : G) ∈ od.P at hx
    have hxG : (x : G) ∈ c.FU := (F_le_FU c w d od) (od.P_le_F hx)
    rw [show c.FU = (fittingSubgroup (↥c.U)).map c.U.subtype by rfl] at hxG
    rcases Subgroup.mem_map.mp hxG with ⟨y, hy, hEq⟩
    have hxy : y = x := Subtype.ext hEq
    rw [← hxy]
    exact hy
  have hFnormal : (fittingSubgroup (↥c.U)).Normal := inferInstance
  have hFnil : Group.IsNilpotent (↥(fittingSubgroup (↥c.U))) := by infer_instance
  have hcore : P' ⊓ fittingSubgroup (↥c.U) ≤ pCore od.p (↥c.U) :=
    pSubgroup_inf_normal_nilpotent_le_pCore P' (fittingSubgroup (↥c.U)) od.p od.hp_prime
      hP'p hFnormal hFnil
  have hP'core : P' ≤ pCore od.p (↥c.U) := by
    intro x hx
    exact hcore ⟨hx, hP'leF hx⟩
  intro x hx
  have hxP' : (⟨x, hPleU hx⟩ : ↥c.U) ∈ P' := Subgroup.mem_subgroupOf.mpr hx
  have hxcore := hP'core hxP'
  exact Subgroup.mem_map.mpr ⟨(⟨x, hPleU hx⟩ : ↥c.U), hxcore, rfl⟩
private theorem QG_exponent : Monoid.exponent (od.Q.map c.U.subtype) = od.p := by
  let eQ : od.Q ≃* od.Q.map c.U.subtype :=
    Subgroup.equivMapOfInjective od.Q c.U.subtype c.U.subtype_injective
  exact (Monoid.exponent_eq_of_mulEquiv eQ).symm.trans od.Q_exponent

private theorem normalizer_le_A :
    (Subgroup.normalizer (od.P : Set G)) ⊓ (od.Q.map c.U.subtype) ≤ od.A := by
  intro x hx
  have hxQ : x ∈ od.Q.map c.U.subtype := hx.2
  have hxU : x ∈ c.U := by
    rcases Subgroup.mem_map.mp hxQ with ⟨q, hq, rfl⟩
    exact q.2
  have hxNU : x ∈ normalizerIn c.U od.P := ⟨hxU, hx.1⟩
  have hxM : x ∈ w.M := by
    rw [secondCase_linear_omega_NU_P_eq_U_inter_M c w d od] at hxNU
    exact hxNU.2
  have hxFU : x ∈ c.FU := secondCase_linear_omega_QG_le_FU c w d od hxQ
  have hxKF : x ∈ od.K0 ⊔ od.F := by
    rw [od.FU_inter_M_eq]
    exact ⟨hxFU, hxM⟩
  have hxpow : x ^ od.p = 1 := by
    have hqpow : (⟨x, hxQ⟩ : od.Q.map c.U.subtype) ^ od.p = 1 :=
      (Monoid.exponent_dvd_iff_forall_pow_eq_one (G := od.Q.map c.U.subtype)
        (n := od.p)).mp (by rw [QG_exponent c w d od]) ⟨x, hxQ⟩
    exact congrArg Subtype.val hqpow
  exact pow_one_of_sup_le_A c w d od x hxKF hxpow

private theorem center_pCore_ambient_centralizer
    {OpU : Subgroup (↥c.U)}
    (z : G)
    (hz : z ∈ ((Subgroup.center OpU).map OpU.subtype).map c.U.subtype) :
    z ∈ Subgroup.centralizer ((OpU.map c.U.subtype : Subgroup G) : Set G) := by
  intro y hy
  rcases Subgroup.mem_map.mp hz with ⟨z1, hz1, hz1eq⟩
  rcases Subgroup.mem_map.mp hz1 with ⟨z0, hz0, hz0eq⟩
  rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, hy0eq⟩
  let yO : OpU := ⟨y0, hy0⟩
  have hzy : z0 * yO = yO * z0 := (Subgroup.mem_center_iff.mp hz0) yO |>.symm
  have hzyG := congrArg (fun t : OpU => (t : G)) hzy
  have hzEq : (z0 : G) = z := by
    calc
      (z0 : G) = (z1 : G) := congrArg Subtype.val hz0eq
      _ = z := hz1eq
  have hyEq : (y0 : G) = y := hy0eq
  rw [← hzEq, ← hyEq]
  simpa [yO] using hzyG.symm

private theorem conj_le_A :
    ∀ q : G, q ∈ od.Q.map c.U.subtype → ∀ p : G, p ∈ od.P →
      q * p * q⁻¹ ∈ od.A := by
  intro q hq p hp
  let : Fact od.p.Prime := ⟨od.hp_prime⟩
  let OpU : Subgroup (↥c.U) := pCore od.p (↥c.U)
  rcases Subgroup.mem_map.mp hq with ⟨q0, hq0, hqeq⟩
  rcases Subgroup.mem_map.mp (od.Q_le_upperCentralSeries_two hq0) with ⟨z, hz, hzq⟩
  have hqOp : q ∈ OpU.map c.U.subtype := by
    refine Subgroup.mem_map.mpr ⟨(z : OpU), ?_, ?_⟩
    · simpa [OpU] using hz
    · calc
        c.U.subtype (z : OpU) = c.U.subtype q0 := by simpa using hzq
        _ = q := hqeq
  have hpCore : p ∈ OpU.map c.U.subtype := P_le_pCore c w d od hp
  rcases Subgroup.mem_map.mp hpCore with ⟨p0, hp0, hpeq⟩
  let p0O : OpU := ⟨p0, by simpa [OpU] using hp0⟩
  have hz' : (z : OpU) ∈ Subgroup.upperCentralSeries OpU 2 := by
    simpa [OpU] using hz
  have hcomm_le : ⁅Subgroup.upperCentralSeries OpU 2, ⊤⁆ ≤ Subgroup.center OpU :=
    commutator_le_center_of_le_upperCentralSeries_two
      (Subgroup.upperCentralSeries OpU 2) le_rfl
  have hcomm_center : ⁅(z : OpU), p0O⁆ ∈ Subgroup.center OpU := by
    apply hcomm_le
    exact Subgroup.commutator_mem_commutator hz' (Subgroup.mem_top p0O)
  have hqpZ : ⁅q, p⁆ ∈ ((Subgroup.center OpU).map OpU.subtype).map c.U.subtype := by
    refine Subgroup.mem_map.mpr ⟨OpU.subtype ⁅(z : OpU), p0O⁆, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⁅(z : OpU), p0O⁆, hcomm_center, rfl⟩
    · change c.U.subtype (OpU.subtype ⁅(z : OpU), p0O⁆) = ⁅q, p⁆
      rw [map_commutatorElement]
      change ⁅(z : G), (p0O : G)⁆ = ⁅q, p⁆
      have hzG : (z : G) = q := by
        calc
          (z : G) = c.U.subtype q0 := by simpa using hzq
          _ = q := hqeq
      have hpG : (p0O : G) = p := by simpa [p0O] using hpeq
      simpa [hzG, hpG]
  have hqpZ_le : ⁅q, p⁆ ∈ OpU.map c.U.subtype := by
    rcases Subgroup.mem_map.mp hqpZ with ⟨y, hy, hEq⟩
    rcases Subgroup.mem_map.mp hy with ⟨z0, hz0, hzEq⟩
    refine Subgroup.mem_map.mpr ⟨z0, z0.2, ?_⟩
    calc
      c.U.subtype z0 = c.U.subtype y := congrArg c.U.subtype hzEq
      _ = ⁅q, p⁆ := hEq
  have hqp_cent := center_pCore_ambient_centralizer (c := c) (z := ⁅q, p⁆) hqpZ
  have hqp_N : ⁅q, p⁆ ∈ Subgroup.normalizer (od.P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro p1
    constructor
    · intro hp1
      have hp1core : p1 ∈ OpU.map c.U.subtype := P_le_pCore c w d od hp1
      have hc : ⁅q, p⁆ * p1 = p1 * ⁅q, p⁆ :=
        (Subgroup.mem_centralizer_iff.mp hqp_cent p1 hp1core).symm
      have heq : ⁅q, p⁆ * p1 * ⁅q, p⁆⁻¹ = p1 := by rw [hc]; group
      rw [heq]
      exact hp1
    · intro hconj
      have hzcore : ⁅q, p⁆ ∈ OpU.map c.U.subtype := hqpZ_le
      have hconjcore : ⁅q, p⁆ * p1 * ⁅q, p⁆⁻¹ ∈ OpU.map c.U.subtype :=
        P_le_pCore c w d od hconj
      have hp1core : p1 ∈ OpU.map c.U.subtype := by
        rcases Subgroup.mem_map.mp hzcore with ⟨z0, hz0, hzEq⟩
        rcases Subgroup.mem_map.mp hconjcore with ⟨c0, hc0, hcEq⟩
        have hm0 : z0⁻¹ * c0 * z0 ∈ OpU :=
          OpU.mul_mem (OpU.mul_mem (OpU.inv_mem hz0) hc0) hz0
        refine Subgroup.mem_map.mpr ⟨z0⁻¹ * c0 * z0, hm0, ?_⟩
        calc
          c.U.subtype (z0⁻¹ * c0 * z0) =
              (c.U.subtype z0)⁻¹ * (c.U.subtype c0) * c.U.subtype z0 := by rfl
          _ = ⁅q, p⁆⁻¹ * (⁅q, p⁆ * p1 * ⁅q, p⁆⁻¹) * ⁅q, p⁆ := by
            rw [hzEq, hcEq]
          _ = p1 := by group
      have hc : ⁅q, p⁆ * p1 = p1 * ⁅q, p⁆ :=
        (Subgroup.mem_centralizer_iff.mp hqp_cent p1 hp1core).symm
      have heq : ⁅q, p⁆ * p1 * ⁅q, p⁆⁻¹ = p1 := by rw [hc]; group
      rw [← heq]
      exact hconj
  have hqp_pow : ⁅q, p⁆ ^ od.p = 1 := by
    have hcomm_q : Commute ⁅q, p⁆ q :=
      (Subgroup.mem_centralizer_iff.mp hqp_cent q hqOp).symm
    have hqpow : q ^ od.p = 1 := by
      have hqg : (⟨q, hq⟩ : od.Q.map c.U.subtype) ^ od.p = 1 :=
        (Monoid.exponent_dvd_iff_forall_pow_eq_one (G := od.Q.map c.U.subtype)
          (n := od.p)).mp (by rw [QG_exponent c w d od]) ⟨q, hq⟩
      exact congrArg Subtype.val hqg
    exact commutator_pow_eq_one_of_pow_eq_one_of_commute hcomm_q hqpow
  have hqpU : ⁅q, p⁆ ∈ c.U := by
    rcases Subgroup.mem_map.mp hqpZ_le with ⟨y, hy, hEq⟩
    have hyU : (y : G) ∈ c.U := by
      change (y : G) ∈ c.U
      exact y.2
    rw [← hEq]
    exact hyU
  have hqp_NU : ⁅q, p⁆ ∈ normalizerIn c.U od.P := ⟨hqpU, hqp_N⟩
  have hqp_M : ⁅q, p⁆ ∈ w.M := by
    rw [secondCase_linear_omega_NU_P_eq_U_inter_M c w d od] at hqp_NU
    exact hqp_NU.2
  have hqpFU : ⁅q, p⁆ ∈ c.FU := by
    rcases Subgroup.mem_map.mp hqpZ_le with ⟨y, hy, hEq⟩
    exact Subgroup.mem_map.mpr ⟨y, (pCore_le_fitting (G := ↥c.U) od.p) hy, hEq⟩
  have hqp_KF : ⁅q, p⁆ ∈ od.K0 ⊔ od.F := by
    rw [od.FU_inter_M_eq]
    exact ⟨hqpFU, hqp_M⟩
  have hqp_A : ⁅q, p⁆ ∈ od.A :=
    pow_one_of_sup_le_A c w d od _ hqp_KF hqp_pow
  have hpA : p ∈ od.A := by
    rw [od.A_eq]
    exact Subgroup.mem_sup_left hp
  rw [show q * p * q⁻¹ = ⁅q, p⁆ * p by rw [commutatorElement_def]; group]
  exact od.A.mul_mem hqp_A hpA


/-- The shared linear omega conjugation controls: the `Q`-normalizer of `P`
lies in `A`, and conjugation by `Q` sends `P` into `A`. -/
public theorem secondCase_linear_omega_conjugation_control
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    (Subgroup.normalizer (od.P : Set G)) ⊓ (od.Q.map c.U.subtype) ≤ od.A ∧
      (∀ q : G, q ∈ od.Q.map c.U.subtype → ∀ p : G, p ∈ od.P →
        q * p * q⁻¹ ∈ od.A) := by
  exact ⟨normalizer_le_A c w d od, conj_le_A c w d od⟩

end CFSG.GorensteinWalter
