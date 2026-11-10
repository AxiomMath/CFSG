module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs
import Mathlib.Order.Atoms.Finite

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27PiCentralizes
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingOddCoreEquality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27DGroupIndexParity
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DGroupQuotientNotTwoGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeQuotientInversion
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private lemma S_eq_closure_t1_t2
    {G : Type u} [Group G] [Finite G] (c : BenderGlauberman.Hyp11 G) :
    (c.S : Subgroup G) = Subgroup.closure ({c.t1, c.t2} : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  apply le_antisymm
  · intro s hs
    let K : Subgroup G := Subgroup.closure ({c.t1, c.t2} : Set G)
    have hKleS : K ≤ (c.S : Subgroup G) := by
      exact (Subgroup.closure_le (c.S : Subgroup G)).2 (by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact c.t1_mem_S
        · exact c.t2_mem_S)
    have hS0leK : (c.S0 : Subgroup G) ≤ K := by
      rw [c.S0_eq_zpowers]
      exact (Subgroup.zpowers_le).2 (K.mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)))
    have hKneS0 : K ≠ (c.S0 : Subgroup G) := by
      intro hEq
      exact c.t1_not_mem_S0 (by
        have ht1K : c.t1 ∈ K := Subgroup.subset_closure (by simp)
        simpa [hEq] using ht1K)
    let S0S : Subgroup ↥(c.S : Subgroup G) :=
      (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
    let KS : Subgroup ↥(c.S : Subgroup G) := K.subgroupOf (c.S : Subgroup G)
    have hS0S_le_KS : S0S ≤ KS := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hS0leK (Subgroup.mem_subgroupOf.mp hx))
    have hrel := Subgroup.relIndex_mul_index hS0S_le_KS
    have hrelS0 : S0S.relIndex KS = (c.S0 : Subgroup G).relIndex K :=
      Subgroup.relIndex_subgroupOf hKleS
    have hmul : (c.S0 : Subgroup G).relIndex K * KS.index = 2 := by
      rw [hrelS0] at hrel
      rw [BenderGlauberman.S0_index c] at hrel
      exact hrel
    have hrelne : (c.S0 : Subgroup G).relIndex K ≠ 1 := by
      intro hEq1
      have hKleS0 : K ≤ (c.S0 : Subgroup G) := (Subgroup.relIndex_eq_one).mp hEq1
      exact hKneS0 (le_antisymm hKleS0 hS0leK)
    have hapos : 0 < (c.S0 : Subgroup G).relIndex K :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
        (H := (c.S0 : Subgroup G).subgroupOf K))
    have hbpos : 0 < KS.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := KS))
    have hb1 : KS.index = 1 := by
      have hb_le2 : (c.S0 : Subgroup G).relIndex K ≤ 2 := by
        exact Nat.le_of_dvd (by norm_num : 0 < 2) ⟨KS.index, hmul.symm⟩
      have hb2 : (c.S0 : Subgroup G).relIndex K = 2 := by omega
      have : 2 * KS.index = 2 := by rwa [hb2] at hmul
      omega
    have hKstop : KS = ⊤ := (Subgroup.index_eq_one).mp hb1
    have hsK : (⟨s, hs⟩ : ↥(c.S : Subgroup G)) ∈ KS := by
      rw [hKstop]
      trivial
    simpa using (Subgroup.mem_subgroupOf.mp hsK)
  · exact (Subgroup.closure_le (c.S : Subgroup G)).2 (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact c.t1_mem_S
      · exact c.t2_mem_S)

private lemma t1_conj_mem_B
    {G : Type u} [Group G] [Finite G] (c : BenderGlauberman.Hyp11 G) {b : G}
    (hb : b ∈ c.B) : c.t1 * b * c.t1⁻¹ ∈ c.B := by
  have hb1 : b ∈ c.B1 := by
    have hb' : b ∈ c.B1 ⊓ c.B2 := by simpa [BenderGlauberman.Hyp11.B] using hb
    exact hb'.1
  have hb1' : b ∈ c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) := by
    simpa [BenderGlauberman.Hyp11.B1, centralizerIn] using hb1
  have hcomm : c.t1 * b = b * c.t1 :=
    (Subgroup.mem_centralizer_iff.mp hb1'.2) c.t1 (by simp)
  have hfix : c.t1 * b * c.t1⁻¹ = b := by
    rw [hcomm]
    simp
  rwa [hfix]

private lemma t2_conj_mem_B
    {G : Type u} [Group G] [Finite G] (c : BenderGlauberman.Hyp11 G) {b : G}
    (hb : b ∈ c.B) : c.t2 * b * c.t2⁻¹ ∈ c.B := by
  have hb2 : b ∈ c.B2 := by
    have hb' : b ∈ c.B1 ⊓ c.B2 := by simpa [BenderGlauberman.Hyp11.B] using hb
    exact hb'.2
  have hb2' : b ∈ c.U ⊓ Subgroup.centralizer ({c.t2} : Set G) := by
    simpa [BenderGlauberman.Hyp11.B2, centralizerIn] using hb2
  have hcomm : c.t2 * b = b * c.t2 :=
    (Subgroup.mem_centralizer_iff.mp hb2'.2) c.t2 (by simp)
  have hfix : c.t2 * b * c.t2⁻¹ = b := by
    rw [hcomm]
    simp
  rwa [hfix]

private lemma t1_normalizes_B
    {G : Type u} [Group G] [Finite G] (c : BenderGlauberman.Hyp11 G) :
    c.t1 ∈ Subgroup.normalizer ((c.B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact t1_conj_mem_B c
  · intro hb
    have hb' : c.t1 * (c.t1 * b * c.t1⁻¹) * c.t1⁻¹ ∈ c.B :=
      t1_conj_mem_B c hb
    have ht1sq : c.t1 * c.t1 = 1 := by simpa [pow_two] using c.t1_involution.2
    have ht1inv : c.t1⁻¹ = c.t1 := inv_eq_of_mul_eq_one_right ht1sq
    have hfix : c.t1 * (c.t1 * b * c.t1⁻¹) * c.t1⁻¹ = b := by
      rw [ht1inv]
      calc
        c.t1 * (c.t1 * b * c.t1) * c.t1 = (c.t1 * c.t1) * b * (c.t1 * c.t1) := by group
        _ = b := by rw [ht1sq]; simp
    simpa [hfix] using hb'

private lemma t2_normalizes_B
    {G : Type u} [Group G] [Finite G] (c : BenderGlauberman.Hyp11 G) :
    c.t2 ∈ Subgroup.normalizer ((c.B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact t2_conj_mem_B c
  · intro hb
    have hb' : c.t2 * (c.t2 * b * c.t2⁻¹) * c.t2⁻¹ ∈ c.B :=
      t2_conj_mem_B c hb
    have ht2sq : c.t2 * c.t2 = 1 := by simpa [pow_two] using c.t2_involution.2
    have ht2inv : c.t2⁻¹ = c.t2 := inv_eq_of_mul_eq_one_right ht2sq
    have hfix : c.t2 * (c.t2 * b * c.t2⁻¹) * c.t2⁻¹ = b := by
      rw [ht2inv]
      calc
        c.t2 * (c.t2 * b * c.t2) * c.t2 = (c.t2 * c.t2) * b * (c.t2 * c.t2) := by group
        _ = b := by rw [ht2sq]; simp
    simpa [hfix] using hb'

private lemma S_le_normalizer_B
    {G : Type u} [Group G] [Finite G] (c : BenderGlauberman.Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer ((c.B : Subgroup G) : Set G) := by
  rw [S_eq_closure_t1_t2 c]
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  simp at hx
  rcases hx with rfl | rfl
  · exact t1_normalizes_B c
  · exact t2_normalizes_B c

/-- The Sylow `2`-subgroup `S` centralizes `B = C_U(S)` pointwise. -/
public theorem S_centralizes_B
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) :
    (bg.S : Subgroup G) ≤
      Subgroup.centralizer ((bg.B : Subgroup G) : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hfix := (BenderGlauberman.mem_fixedSubgroup_iff
    (bg.S : Subgroup G) bg.U
    (⟨b, BenderGlauberman.mem_U_of_mem_B_s4 bg hb⟩ : ↥bg.U)).mp
      (BenderGlauberman.b_mem_fixedSubgroup_s4 bg hb)
  have hfixs := hfix (⟨s, hs⟩ : ↥(bg.S : Subgroup G))
  have h' := congrArg Subtype.val hfixs
  have hfixeq : s * b * s⁻¹ = b :=
    (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
      (bg.S : Subgroup G) bg.U
      (⟨s, hs⟩ : ↥(bg.S : Subgroup G))
      (⟨b, BenderGlauberman.mem_U_of_mem_B_s4 bg hb⟩ : ↥bg.U)).symm.trans h'
  have hsbb : s * b = b * s := by
    calc
      s * b = (s * b * s⁻¹) * s := by group
      _ = b * s := by rw [hfixeq]
  exact hsbb.symm

/-- Every Sylow `p`-subgroup of `B` is normalized by `S`. -/
public theorem S_le_normalizer_P2
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P2 : Subgroup G := sylowCarrier (firstCase_P2_sylow c od hU Q)
  have hP2leB : P2 ≤ od.d.bg.B := by
    simpa [P2, firstCase_P2_carrier c od hU Q] using
      (Subgroup.map_subtype_le (H := od.d.bg.B) (Q : Subgroup ↥od.d.bg.B))
  have hSleCentB : (od.d.bg.S : Subgroup G) ≤
      Subgroup.centralizer ((od.d.bg.B : Subgroup G) : Set G) :=
    S_centralizes_B od.d.bg
  have hSleCentP2 : (od.d.bg.S : Subgroup G) ≤
      Subgroup.centralizer ((P2 : Subgroup G) : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hsC : s ∈ Subgroup.centralizer
        ((od.d.bg.B : Subgroup G) : Set G) := hSleCentB hs
    have hcomm : x * s = s * x :=
      (Subgroup.mem_centralizer_iff.mp hsC) x (hP2leB hx)
    exact hcomm
  have hSleNP2 : (od.d.bg.S : Subgroup G) ≤
      Subgroup.normalizer ((P2 : Subgroup G) : Set G) :=
    hSleCentP2.trans (centralizer_le_normalizer P2)
  simpa [od.d.S_eq] using hSleNP2

private lemma B_mem_centralizer_t2
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G) {b : G} (hb : b ∈ bg.B) :
    b ∈ Subgroup.centralizer ({bg.t2} : Set G) := by
  have hbB2 : b ∈ bg.B2 :=
    (inf_le_right : bg.B1 ⊓ bg.B2 ≤ bg.B2)
      (by simpa [BenderGlauberman.Hyp11.B] using hb)
  have hbB2' : b ∈ bg.U ⊓ Subgroup.centralizer ({bg.t2} : Set G) := by
    simpa [BenderGlauberman.Hyp11.B2, centralizerIn] using hbB2
  exact hbB2'.2

/-- `P = O_p(U)` and `P₂` are disjoint: `t₂` inverts `P` and centralizes
`P₂ ≤ B`, and `p` is odd. -/
private theorem firstCase_P_inf_P2_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    qCoreOf od.d.bg.U od.p ⊓
      sylowCarrier (firstCase_P2_sylow c od hU Q) = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P2G : Subgroup G := sylowCarrier (firstCase_P2_sylow c od hU Q)
  have hPp : IsPGroup od.p P := qCoreOf_isPGroup od.d.bg.U od.p
  have hP2leB : P2G ≤ od.d.bg.B := by
    simpa [P2G, firstCase_P2_carrier c od hU Q] using
      (Subgroup.map_subtype_le (H := od.d.bg.B) (Q : Subgroup ↥od.d.bg.B))
  apply le_bot_iff.mp
  intro x hx
  have hxP : x ∈ P := (Subgroup.mem_inf.mp hx).1
  have hxP2 : x ∈ P2G := (Subgroup.mem_inf.mp hx).2
  have hxCent : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x := by
    have hxCent' : x ∈ Subgroup.centralizer ({od.d.bg.t2} : Set G) :=
      B_mem_centralizer_t2 od.d.bg (hP2leB hxP2)
    have hcomm : od.d.bg.t2 * x = x * od.d.bg.t2 :=
      (Subgroup.mem_centralizer_iff.mp hxCent') od.d.bg.t2 (by simp)
    calc
      od.d.bg.t2 * x * od.d.bg.t2⁻¹ =
          (x * od.d.bg.t2) * od.d.bg.t2⁻¹ := by rw [hcomm]
      _ = x := by group
  have hxInv : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x⁻¹ :=
    firstCase_t2_inverts_primeCore c od x hxP
  have hx2 : x * x = 1 := by
    have hxinv_eq : x⁻¹ = x := hxInv.symm.trans hxCent
    calc
      x * x = x⁻¹ * x := by rw [hxinv_eq]
      _ = 1 := by simp
  have hord2 : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
  have hordP : orderOf x ∣ Nat.card P := Subgroup.orderOf_dvd_natCard P hxP
  obtain ⟨m, hm⟩ := hPp.exists_card_eq
  have hcopBase : Nat.Coprime 2 od.p :=
    (Nat.coprime_primes Nat.prime_two (Fact.out : Nat.Prime od.p)).2 (by
      intro h
      exact firstCase_oriented_p_odd c od h.symm)
  have hcop : Nat.Coprime 2 (od.p ^ m) := hcopBase.pow_right m
  have hord1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord2 (by
      rw [hm] at hordP
      exact hordP)
  exact orderOf_eq_one_iff.mp hord1

/-- `P₀ = P ∩ M` is nontrivial for the maximal `M ⊇ N_G(P₂)`. -/
public theorem firstCase_P0_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M) :
    qCoreOf od.d.bg.U od.p ⊓ M ≠ ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P2G : Subgroup G := sylowCarrier (firstCase_P2_sylow c od hU Q)
  let P1G : Subgroup G := P ⊔ P2G
  intro hP0bot
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hq : qCoreOf c.U od.p = P := by
      simpa [P, hUeq] using (qCoreOf_eq_of_subgroup_eq hUeq od.p)
    exact od.primeCore_ne_bot (by simpa [hq] using hPbot)
  have hPp : IsPGroup od.p P := qCoreOf_isPGroup od.d.bg.U od.p
  have hP2p : IsPGroup od.p P2G := by
    have hP2c : P2G =
        (Q : Subgroup ↥od.d.bg.B).map od.d.bg.B.subtype := by
      simpa [P2G] using (firstCase_P2_carrier c od hU Q)
    rw [hP2c]
    exact (Q.isPGroup').map od.d.bg.B.subtype
  have hPleU : P ≤ od.d.bg.U := qCoreOf_le od.d.bg.U od.p
  have hBleU : od.d.bg.B ≤ od.d.bg.U := by
    intro b hb
    exact BenderGlauberman.mem_U_of_mem_B_s4 od.d.bg hb
  have hP2leB : P2G ≤ od.d.bg.B := by
    simpa [P2G, firstCase_P2_carrier c od hU Q] using
      (Subgroup.map_subtype_le (H := od.d.bg.B) (Q : Subgroup ↥od.d.bg.B))
  have hP2leU : P2G ≤ od.d.bg.U := hP2leB.trans hBleU
  have hP2normP : P2G ≤ Subgroup.normalizer (P : Set G) :=
    hP2leU.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in od.d.bg.U od.p))
  have hP1p : IsPGroup od.p P1G := by
    simpa [P1G] using
      (IsPGroup.to_sup_of_normal_left' (p := od.p) (H := P) (K := P2G)
        hPp hP2p hP2normP)
  have hP2leP1 : P2G ≤ P1G := by
    intro x hx
    change x ∈ P ⊔ P2G
    exact Subgroup.mem_sup_right hx
  have hPinfP2 : Disjoint P P2G := by
    exact disjoint_iff_inf_le.mpr
      (le_of_eq (firstCase_P_inf_P2_eq_bot c od hU Q))
  have hP1neP2 : P1G ≠ P2G := by
    intro hEq
    have hPleP2 : P ≤ P2G := by
      simpa [P1G, hEq] using (le_sup_left : P ≤ P ⊔ P2G)
    have hPbot : P = ⊥ :=
      le_bot_iff.mp (fun x hx => hPinfP2.le_bot ⟨hx, hPleP2 hx⟩)
    exact hPne hPbot
  -- If `P ∩ M = 1`, then `P₁ ∩ M = P₂`.
  have hP1_inter_M_le : P1G ⊓ M ≤ P2G := by
    intro x hx
    have hxP1 : x ∈ P1G := (Subgroup.mem_inf.mp hx).1
    have hxM : x ∈ M := (Subgroup.mem_inf.mp hx).2
    have hprod : (P1G : Set G) = (P : Set G) * (P2G : Set G) := by
      change (↑(P ⊔ P2G) : Set G) = (P : Set G) * (P2G : Set G)
      exact Subgroup.coe_mul_of_right_le_normalizer_left P P2G hP2normP
    have hxprod : x ∈ (P : Set G) * (P2G : Set G) := by
      change x ∈ (P1G : Set G) at hxP1
      rwa [hprod] at hxP1
    rcases hxprod with ⟨p, hp, q, hq, hxeq⟩
    have hP2leM : P2G ≤ M := Subgroup.le_normalizer.trans hMN
    have hpM : p ∈ M := by
      have hxq : x * q⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem (hP2leM hq))
      have hp_eq : p = x * q⁻¹ := by
        calc
          p = p * (q * q⁻¹) := by group
          _ = (p * q) * q⁻¹ := by group
          _ = x * q⁻¹ := by rw [← hxeq]
      rwa [hp_eq]
    have hp1 : p = 1 := by
      have hpP0 : p ∈ P ⊓ M := ⟨hp, hpM⟩
      have hpbot : p ∈ (⊥ : Subgroup G) := by
        rw [← hP0bot]
        exact hpP0
      exact Subgroup.mem_bot.mp hpbot
    have hq : q ∈ P2G := hq
    have hxq : x = q := by
      calc
        x = p * q := hxeq.symm
        _ = q := by rw [hp1]; simp
    simpa [hxq] using hq
  -- In the finite `p`-group `P₁`, the proper subgroup `P₂` has a strictly
  -- larger normalizer.
  let P2sub : Subgroup (↥P1G) := P2G.subgroupOf P1G
  have hP2sub_ne_top : P2sub ≠ ⊤ := by
    intro htop
    have hP1leP2 : P1G ≤ P2G := (Subgroup.subgroupOf_eq_top.mp htop)
    exact hP1neP2 (le_antisymm hP1leP2 hP2leP1)
  have hP2sub_proper : P2sub < ⊤ := lt_top_iff_ne_top.mpr hP2sub_ne_top
  have : Group.IsNilpotent (↥P1G) := hP1p.isNilpotent
  have hnc : NormalizerCondition (↥P1G) :=
    Group.normalizerCondition_of_isNilpotent (G := ↥P1G)
  have hltN : P2sub < Subgroup.normalizer (P2sub : Set (↥P1G)) :=
    hnc P2sub hP2sub_proper
  obtain ⟨y, hyN, hyP2⟩ := Set.not_subset.mp hltN.2
  have hNsub_eq :
      (Subgroup.normalizer (P2G : Set G)).subgroupOf P1G =
        Subgroup.normalizer (P2sub : Set (↥P1G)) :=
    Subgroup.subgroupOf_normalizer_eq hP2leP1
  have hyN' : (y : G) ∈ Subgroup.normalizer (P2G : Set G) := by
    have hyN1 : y ∈ (Subgroup.normalizer (P2G : Set G)).subgroupOf P1G := by
      simpa [hNsub_eq] using hyN
    exact Subgroup.mem_subgroupOf.mp hyN1
  have hyP2' : (y : G) ∉ P2G := by
    intro hy
    exact hyP2 (Subgroup.mem_subgroupOf.mpr hy)
  have hyM : (y : G) ∈ M := hMN hyN'
  have hyP1 : (y : G) ∈ P1G := y.2
  have hyP2 := hP1_inter_M_le ⟨hyP1, hyM⟩
  exact hyP2' hyP2

/-- The normalizer of `P₂` is a proper subgroup of the simple group `G`. -/
public theorem firstCase_normalizer_P2_proper
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≠ ⊤ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P2 : Subgroup G := sylowCarrier (firstCase_P2_sylow c od hU Q)
  let N : Subgroup G := Subgroup.normalizer (P2 : Set G)
  have hP2ne : P2 ≠ ⊥ := firstCase_P2_ne_one hmin c od hfirst hHhat hU Q
  intro hNtop
  have hP2normal : P2.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact hNtop
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple P2 hP2normal with hP2bot | hP2top
  · exact hP2ne hP2bot
  · have hP2leU : P2 ≤ od.d.bg.U := by
      have hP2leB : P2 ≤ od.d.bg.B := by
        simpa [P2, firstCase_P2_carrier c od hU Q] using
          (Subgroup.map_subtype_le (H := od.d.bg.B) (Q : Subgroup ↥od.d.bg.B))
      have hBleU : od.d.bg.B ≤ od.d.bg.U := by
        intro b hb
        exact BenderGlauberman.mem_U_of_mem_B_s4 od.d.bg hb
      exact hP2leB.trans hBleU
    have htU_bg : c.t ∈ od.d.bg.U := by
      have htP2 : c.t ∈ P2 := by simpa [hP2top]
      exact hP2leU htP2
    have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
    have htU : c.t ∈ c.U := by simpa [hUeq] using htU_bg
    have hUodd_bg : Nat.Coprime 2 (Nat.card od.d.bg.U) :=
      BenderGlauberman.U_coprime_two od.d.bg
    have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
      simpa [hUeq] using hUodd_bg
    have hord2 : orderOf (⟨c.t, htU⟩ : ↥c.U) = 2 := by
      simpa [Subgroup.orderOf_mk] using
        (orderOf_eq_prime (by simpa [pow_two] using c.t_involution.2)
          c.t_involution.1)
    have h2dvd : (2 : ℕ) ∣ Nat.card c.U := by
      rw [← hord2]
      exact orderOf_dvd_natCard _
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hUodd h2dvd

/-- There is a maximal subgroup `M` containing `N_G(P₂)`, and `S ≤ M`. -/
public theorem firstCase_exists_maximal_containing_normalizer_P2
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    ∃ M : Subgroup G,
      IsCoatom M ∧
        Subgroup.normalizer
          (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
          (c.S : Subgroup G) ≤ M := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P2 : Subgroup G := sylowCarrier (firstCase_P2_sylow c od hU Q)
  let N : Subgroup G := Subgroup.normalizer (P2 : Set G)
  have hNproper : N ≠ ⊤ := by
    simpa [N, P2] using firstCase_normalizer_P2_proper hmin c od hfirst hHhat hU Q
  obtain ⟨M, hM⟩ := section9_exists_maximalSubgroupsContaining_of_ne_top hNproper
  exact ⟨M, hM.1, by
    intro x hx
    exact hM.2 (by simpa [N] using hx), by
    have hSleN : (c.S : Subgroup G) ≤ N := by
      simpa [N, P2, od.d.S_eq] using S_le_normalizer_P2 c od hU Q
    intro x hx
    exact hM.2 (hSleN hx)⟩

/-- The full maximal-overgroup configuration: a coatom `M` containing
`N_G(P₂)` and `S`, with `P₀ = P ∩ M ≠ 1`. -/
public theorem firstCase_exists_maximal_P2_with_P0_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    ∃ M : Subgroup G,
      IsCoatom M ∧
        Subgroup.normalizer
          (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M ∧
          (c.S : Subgroup G) ≤ M ∧
            qCoreOf od.d.bg.U od.p ⊓ M ≠ ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨M, hMmax, hMN, hSM⟩ :=
    firstCase_exists_maximal_containing_normalizer_P2
      hmin c od hfirst hHhat hU Q
  exact ⟨M, hMmax, hMN, hSM,
    firstCase_P0_ne_bot hmin c od hfirst hHhat hU Q M hMmax hMN hSM⟩

/-- Lemma 2.9 applied to the maximal subgroup `M` and the Klein-four
`V₂ = ⟨t, t₂⟩`: either `V₂` meets `O₂(M)` or it meets the layer `E(M)`. -/
public theorem firstCase_V2_intersects_layer_or_twoCore
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M) :
    fd.V2 ⊓ twoCoreOf M ≠ ⊥ ∨
      fd.V2 ⊓ componentLayerOf M ≠ ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  exact lemma_2_9 hmin c (firstCase_lemma29Hypothesis c hfirst hHhat)
    (V := fd.V2) (N := M)
    (hVN := fun x hx => hSM (fd.V2_le_S hx))
    (htV := fd.t_mem_V2) (hV := fd.V2_klein)
    (hNtop := hMmax.1) (hVS := fd.V2_le_S)

/-! ### Eliminating the `O₂(M)` alternative in Lemma 2.9

The source says: "As `t₂` inverts `P₀`, `V₂` is not contained in `O₂(M)`."
The precise local transfer is that, once `O₂(M)` contains one nonidentity
element of the Klein-four `V₂`, transitivity of `N_G(P₂)` on `V₂#` forces
`t₂ ∈ O₂(M)`.  Then `O₂(M)` centralizes the odd part of `F(Ĥ)` (Bender
1.7(ii) through the control-core interface), hence centralizes
`P₀ ≤ F(U)`, contradicting the inversion of `P₀` by `t₂`.

The control-core hypothesis `hControl : NormalizerControlledBy c.Hhat M`
is the exact interface needed for the Bender 1.7(ii) step; constructing it
from the first-case Sylow configuration is a separate subnode. -/

/-- In the first case, `O₂(M)` centralizes `F(U) = O_{2'}(F(Ĥ))`, by
Bender 1.7(ii) and the control-core interface. -/
private theorem firstCase_twoCore_centralizes_FU
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (M : Subgroup G)
    (hControl : NormalizerControlledBy c.Hhat M) :
    twoCoreOf M ≤ Subgroup.centralizer (c.FU : Set G) := by
  classical
  have h26 := theorem_2_6 hmin c
  have ht2 : c.t ∈ twoCoreOf c.Hhat :=
    centralizerStructure_t_mem_twoCore c h26
  have hle : twoCoreOf c.Hhat ≤ fittingSubgroupOf c.Hhat :=
    qCoreOf_le_fittingSubgroupOf c.Hhat 2 Nat.prime_two
  have hxF : c.t ∈ fittingSubgroupOf c.Hhat := hle ht2
  have hord : orderOf c.t = 2 :=
    orderOf_eq_prime c.t_involution.2 c.t_involution.1
  have h2dvd : 2 ∣ Nat.card ↥(fittingSubgroupOf c.Hhat) := by
    let : Fintype ↥(fittingSubgroupOf c.Hhat) := Fintype.ofFinite _
    have h := orderOf_dvd_card (x := (⟨c.t, hxF⟩ : fittingSubgroupOf c.Hhat))
    simpa [Nat.card_eq_fintype_card, Subgroup.orderOf_mk, hord] using h
  have h2π : 2 ∈ primesOfOrder (fittingSubgroupOf c.Hhat) :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, Nat.card_pos.ne'⟩
  have hCent :=
    twoCoreOf_centralizes_oddPart_fittingSubgroupOf_of_control
      (minimalCounterexample_isSimple hmin) c M hControl h2π
  have hU_eq : c.U = oddCoreOf c.Hhat := h26.1
  have hEq : piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} = c.FU := by
    calc
      piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} =
          fittingSubgroupOf (oddCoreOf c.Hhat) :=
        (fittingSubgroupOf_oddCore_eq_oddPart_fittingSubgroupOf c.Hhat).symm
      _ = fittingSubgroupOf c.U := by rw [hU_eq]
      _ = c.FU := rfl
  simpa [hEq] using hCent

/-- If the control-core hypothesis is available, the Klein-four `V₂`
avoids the `2`-core of the maximal overgroup `M`. -/
public theorem firstCase_V2_inf_twoCore_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (hControl : NormalizerControlledBy c.Hhat M) :
    fd.V2 ⊓ twoCoreOf M = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  by_contra hne
  have hnt : Nontrivial ↥(fd.V2 ⊓ twoCoreOf M) :=
    (Subgroup.nontrivial_iff_ne_bot (fd.V2 ⊓ twoCoreOf M)).2 hne
  obtain ⟨x, hxne⟩ := exists_ne (1 : ↥(fd.V2 ⊓ twoCoreOf M))
  let xG : G := x
  have hxV : xG ∈ fd.V2 := x.2.1
  have hxO : xG ∈ twoCoreOf M := x.2.2
  have hxne' : xG ≠ 1 := by
    intro hx1
    apply hxne
    apply Subtype.ext
    exact hx1
  obtain ⟨m, hmN, hm⟩ :=
    firstCase_P2_transitive hmin c od fd hU Q xG od.d.bg.t2
      hxV (fd.t2_mem_V2) hxne' od.d.bg.t2_involution.1
  have hmM : m ∈ M := hMN hmN
  have hq2 : qCoreOf M 2 = twoCoreOf M := by
    rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
  have hxO' : xG ∈ qCoreOf M 2 := by simpa [hq2] using hxO
  have ht2O : od.d.bg.t2 ∈ twoCoreOf M := by
    have hnorm : IsNormalIn (qCoreOf M 2) M := qCoreOf_normal_in M 2
    have hconj : m * xG * m⁻¹ ∈ qCoreOf M 2 := hnorm.2 m hmM xG hxO'
    have hconj' : od.d.bg.t2 ∈ qCoreOf M 2 := by simpa [hm] using hconj
    simpa [hq2] using hconj'
  have hCentFU : twoCoreOf M ≤ Subgroup.centralizer (c.FU : Set G) :=
    firstCase_twoCore_centralizes_FU hmin c M hControl
  have hPleFU : P ≤ c.FU := by
    have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
    have hFU : fittingSubgroupOf od.d.bg.U = c.FU := by
      change fittingSubgroupOf od.d.bg.U = fittingSubgroupOf c.U
      rw [hUeq]
    rw [← hFU]
    exact qCoreOf_le_fittingSubgroupOf od.d.bg.U od.p od.p_prime
  have hP0ne : P ⊓ M ≠ ⊥ :=
    firstCase_P0_ne_bot hmin c od hfirst hHhat hU Q M hMmax hMN hSM
  have hP0nt : Nontrivial ↥(P ⊓ M) :=
    (Subgroup.nontrivial_iff_ne_bot (P ⊓ M)).2 hP0ne
  obtain ⟨y, hyne⟩ := exists_ne (1 : ↥(P ⊓ M))
  let yG : G := y
  have hyP : yG ∈ P := y.2.1
  have hyM : yG ∈ M := y.2.2
  have hyne' : yG ≠ 1 := by
    intro hy1
    apply hyne
    apply Subtype.ext
    exact hy1
  have hyFU : yG ∈ c.FU := hPleFU hyP
  have hyCent : od.d.bg.t2 * yG * od.d.bg.t2⁻¹ = yG := by
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hCentFU ht2O)) yG hyFU
    calc
      od.d.bg.t2 * yG * od.d.bg.t2⁻¹ = (yG * od.d.bg.t2) * od.d.bg.t2⁻¹ := by
        rw [hcomm]
      _ = yG := by group
  have hyInv : od.d.bg.t2 * yG * od.d.bg.t2⁻¹ = yG⁻¹ :=
    firstCase_t2_inverts_primeCore c od yG hyP
  have hyinv_eq : yG⁻¹ = yG := hyInv.symm.trans hyCent
  have hy2 : yG * yG = 1 := by
    calc
      yG * yG = yG⁻¹ * yG := by rw [hyinv_eq]
      _ = 1 := by simp
  have hord2 : orderOf yG ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hy2)
  have hordP : orderOf yG ∣ Nat.card P :=
    Subgroup.orderOf_dvd_natCard P hyP
  obtain ⟨n, hn⟩ := (qCoreOf_isPGroup od.d.bg.U od.p).exists_card_eq
  have hcopBase : Nat.Coprime 2 od.p :=
    (Nat.coprime_primes Nat.prime_two (Fact.out : Nat.Prime od.p)).2 (by
      intro h
      exact firstCase_oriented_p_odd c od h.symm)
  have hcop : Nat.Coprime 2 (od.p ^ n) := hcopBase.pow_right n
  have hord1 : orderOf yG = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord2 (by
      rw [hn] at hordP
      exact hordP)
  exact hyne' (orderOf_eq_one_iff.mp hord1)

/-- Once one nonidentity element of the Klein-four `V₂` lies in a normal
subgroup `L ≤ M`, transitivity of `N_G(P₂)` on `V₂#` forces `V₂ ≤ L`. -/
private theorem firstCase_V2_le_of_inf_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (L : Subgroup G)
    (hLnorm : IsNormalIn L M)
    (hne : fd.V2 ⊓ L ≠ ⊥) :
    fd.V2 ≤ L := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  have hnt : Nontrivial ↥(fd.V2 ⊓ L) :=
    (Subgroup.nontrivial_iff_ne_bot (fd.V2 ⊓ L)).2 hne
  obtain ⟨x, hxne⟩ := exists_ne (1 : ↥(fd.V2 ⊓ L))
  let xG : G := x
  have hxV : xG ∈ fd.V2 := x.2.1
  have hxL : xG ∈ L := x.2.2
  have hxne' : xG ≠ 1 := by
    intro hx1
    apply hxne
    apply Subtype.ext
    exact hx1
  have ht2L : od.d.bg.t2 ∈ L := by
    obtain ⟨m, hmN, hm⟩ :=
      firstCase_P2_transitive hmin c od fd hU Q xG od.d.bg.t2
        hxV (fd.t2_mem_V2) hxne' od.d.bg.t2_involution.1
    have hmM : m ∈ M := hMN hmN
    have hconj : m * xG * m⁻¹ ∈ L := hLnorm.2 m hmM xG hxL
    simpa [hm] using hconj
  have htL : od.d.bg.t ∈ L := by
    obtain ⟨m, hmN, hm⟩ :=
      firstCase_P2_transitive hmin c od fd hU Q od.d.bg.t2 od.d.bg.t
        fd.t2_mem_V2 (by simpa [od.d.t_eq] using fd.t_mem_V2)
        od.d.bg.t2_involution.1 od.d.bg.t_involution.1
    have hmM : m ∈ M := hMN hmN
    have hconj : m * od.d.bg.t2 * m⁻¹ ∈ L := hLnorm.2 m hmM od.d.bg.t2 ht2L
    simpa [hm] using hconj
  have hV2eq : fd.V2 = Subgroup.closure ({od.d.bg.t, od.d.bg.t2} : Set G) := by
    have hSleH : (od.d.bg.S : Subgroup G) ≤ od.d.bg.H := by
      rw [← od.d.bg.H_eq_US]
      exact le_sup_right
    have htH : od.d.bg.t ∈ od.d.bg.H :=
      hSleH (od.d.bg.S0_le_S od.d.bg.t_mem_S0)
    have ht2H : od.d.bg.t2 ∈ od.d.bg.H := hSleH od.d.bg.t2_mem_S
    have hcomm : Commute od.d.bg.t od.d.bg.t2 := by
      rw [od.d.bg.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at htH
      rw [od.d.bg.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at ht2H
      exact ht2H.symm
    have htsne : od.d.bg.t ≠ od.d.bg.t2 := by
      intro h
      apply od.d.bg.t2_not_mem_S0
      rw [← h]
      exact od.d.bg.t_mem_S0
    exact kleinFour_eq_closure_of_mem fd.V2_klein
      (by simpa [od.d.t_eq] using fd.t_mem_V2) fd.t2_mem_V2
      od.d.bg.t_involution.1 od.d.bg.t2_involution.1 htsne hcomm
  rw [hV2eq]
  exact (Subgroup.closure_le _).2 (by
    intro z hz
    simp at hz
    rcases hz with rfl | rfl
    · exact htL
    · exact ht2L)

/-- Lemma 2.9 applied to the maximal overgroup `M`: the `O₂(M)`
alternative is impossible once the control-core interface is available, so
the full Klein-four `V₂` lies in the component layer. -/
public theorem firstCase_V2_le_componentLayer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (hControl : NormalizerControlledBy c.Hhat M) :
    fd.V2 ≤ componentLayerOf M := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hdisj := firstCase_V2_intersects_layer_or_twoCore
    hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM
  have hO2bot : fd.V2 ⊓ twoCoreOf M = ⊥ :=
    firstCase_V2_inf_twoCore_eq_bot hmin c od hfirst hHhat hU Q fd M
      hMmax hMN hSM hControl
  rcases hdisj with hO2 | hE
  · exact False.elim (hO2 hO2bot)
  · exact firstCase_V2_le_of_inf_ne_bot hmin c od fd hU Q M hMN
      (componentLayerOf M) (fstar_componentLayerOf_isNormalIn M) hE

/-- In the `D`-group branch where `M / O_{2'}(M)` is a `2`-group, the
Klein-four `V₂` avoids `O₂(M)` directly: any odd-order subgroup of `M`
lies in the odd core, and the `2`-core centralizes the odd core. -/
public theorem firstCase_V2_inf_twoCore_eq_bot_of_twoGroupQuotient
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (hQ : IsPGroup 2 (↥M ⧸ pPrimeCore 2 ↥M)) :
    fd.V2 ⊓ twoCoreOf M = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  have hpodd : Odd od.p :=
    (Fact.out : Nat.Prime od.p).odd_of_ne_two (firstCase_oriented_p_odd c od)
  have hP0ne : P ⊓ M ≠ ⊥ :=
    firstCase_P0_ne_bot hmin c od hfirst hHhat hU Q M hMmax hMN hSM
  let PM : Subgroup G := P ⊓ M
  let : Fintype ↥PM := Fintype.ofFinite _
  have hP0p : IsPGroup od.p PM :=
    (qCoreOf_isPGroup od.d.bg.U od.p).to_inf_left
  obtain ⟨n, hn⟩ := hP0p.exists_card_eq
  have hP0odd : Odd (Nat.card ↥PM) := by
    rw [hn]
    exact hpodd.pow
  have hP0leOdd : PM ≤ oddCoreOf M := by
    let P0M : Subgroup ↥M := PM.subgroupOf M
    have hP0Modd : Odd (Nat.card P0M) := by
      have e : P0M ≃* PM := Subgroup.subgroupOfEquivOfLe inf_le_right
      rw [Nat.card_congr e.toEquiv]
      exact hP0odd
    have hP0Mle : P0M ≤ pPrimeCore 2 ↥M :=
      subgroup_le_pPrimeCore_of_quotient_isPGroup hQ P0M hP0Modd
    intro x hx
    have hxM : x ∈ M := (Subgroup.mem_inf.mp hx).2
    have hxP0M : (⟨x, hxM⟩ : ↥M) ∈ P0M :=
      Subgroup.mem_subgroupOf.mpr hx
    have hxCore : (⟨x, hxM⟩ : ↥M) ∈ pPrimeCore 2 ↥M := hP0Mle hxP0M
    exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, hxCore, rfl⟩
  by_contra hne
  have hnt : Nontrivial ↥(fd.V2 ⊓ twoCoreOf M) :=
    (Subgroup.nontrivial_iff_ne_bot (fd.V2 ⊓ twoCoreOf M)).2 hne
  obtain ⟨x, hxne⟩ := exists_ne (1 : ↥(fd.V2 ⊓ twoCoreOf M))
  let xG : G := x
  have hxV : xG ∈ fd.V2 := x.2.1
  have hxO : xG ∈ twoCoreOf M := x.2.2
  have hxne' : xG ≠ 1 := by
    intro hx1
    apply hxne
    apply Subtype.ext
    exact hx1
  obtain ⟨m, hmN, hm⟩ :=
    firstCase_P2_transitive hmin c od fd hU Q xG od.d.bg.t2
      hxV (fd.t2_mem_V2) hxne' od.d.bg.t2_involution.1
  have hmM : m ∈ M := hMN hmN
  have hq2 : qCoreOf M 2 = twoCoreOf M := by
    rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
  have hxO' : xG ∈ qCoreOf M 2 := by simpa [hq2] using hxO
  have ht2O : od.d.bg.t2 ∈ twoCoreOf M := by
    have hnorm : IsNormalIn (qCoreOf M 2) M := qCoreOf_normal_in M 2
    have hconj : m * xG * m⁻¹ ∈ qCoreOf M 2 := hnorm.2 m hmM xG hxO'
    have hconj' : od.d.bg.t2 ∈ qCoreOf M 2 := by simpa [hm] using hconj
    simpa [hq2] using hconj'
  have hCentOdd : twoCoreOf M ≤ Subgroup.centralizer (oddCoreOf M : Set G) :=
    twoCoreOf_centralizes_oddCoreOf M
  have hP0nt : Nontrivial ↥PM :=
    (Subgroup.nontrivial_iff_ne_bot PM).2 hP0ne
  obtain ⟨y, hyne⟩ := exists_ne (1 : ↥PM)
  let yG : G := y
  have hyP : yG ∈ P := y.2.1
  have hyM : yG ∈ M := y.2.2
  have hyne' : yG ≠ 1 := by
    intro hy1
    apply hyne
    apply Subtype.ext
    exact hy1
  have hyOdd : yG ∈ oddCoreOf M := hP0leOdd ⟨hyP, hyM⟩
  have hyCent : od.d.bg.t2 * yG * od.d.bg.t2⁻¹ = yG := by
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hCentOdd ht2O)) yG hyOdd
    calc
      od.d.bg.t2 * yG * od.d.bg.t2⁻¹ = (yG * od.d.bg.t2) * od.d.bg.t2⁻¹ := by
        rw [hcomm]
      _ = yG := by group
  have hyInv : od.d.bg.t2 * yG * od.d.bg.t2⁻¹ = yG⁻¹ :=
    firstCase_t2_inverts_primeCore c od yG hyP
  have hyinv_eq : yG⁻¹ = yG := hyInv.symm.trans hyCent
  have hy2 : yG * yG = 1 := by
    calc
      yG * yG = yG⁻¹ * yG := by rw [hyinv_eq]
      _ = 1 := by simp
  have hord2 : orderOf yG ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hy2)
  have hordP : orderOf yG ∣ Nat.card ↥PM :=
    Subgroup.orderOf_dvd_natCard PM y.2
  have hcopBase : Nat.Coprime 2 od.p :=
    (Nat.coprime_primes Nat.prime_two (Fact.out : Nat.Prime od.p)).2 (by
      intro h
      exact firstCase_oriented_p_odd c od h.symm)
  have hcop : Nat.Coprime 2 (od.p ^ n) := hcopBase.pow_right n
  have hord1 : orderOf yG = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord2 (by
      rw [hn] at hordP
      exact hordP)
  exact hyne' (orderOf_eq_one_iff.mp hord1)

/-- In the `A₇` quotient branch of the `D`-group `M`, the `2`-core is
trivial, so the Klein-four `V₂` avoids it. -/
public theorem firstCase_V2_inf_twoCore_eq_bot_of_quotient_ASeven
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (hA7 : Nonempty
      ((↥M ⧸ pPrimeCore 2 ↥M) ≃* alternatingGroup (Fin 7))) :
    fd.V2 ⊓ twoCoreOf M = ⊥ := by
  classical
  have hTbot : pCore 2 ↥M = ⊥ :=
    pCore_two_eq_bot_of_quotient_ASeven hA7
  have hmap : twoCoreOf M = ⊥ := by
    rw [twoCoreOf, hTbot]
    simp
  rw [hmap]
  simp

/-- In the large-field linear quotient branch of the `D`-group `M`, the
`2`-core is trivial, so `V₂` avoids it. -/
public theorem firstCase_V2_inf_twoCore_eq_bot_of_quotient_linear_large
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (L : Subgroup ((↥M) ⧸ pPrimeCore 2 (↥M)))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (hLmodel : Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) :
    fd.V2 ⊓ twoCoreOf M = ⊥ := by
  classical
  have hTbot : pCore 2 (↥M) = ⊥ :=
    pCore_two_eq_bot_of_linear_quotient_large
      K hK hcard L hLnormal hLindex hLmodel
  have hmap : twoCoreOf M = ⊥ := by
    rw [twoCoreOf, hTbot]
    simp
  rw [hmap]
  simp

/-- In the `PSL₂(3) ≃ A₄` quotient branch of the `D`-group `M`, the
Klein-four `V₂` avoids `O₂(M)`: its image in the model is a self-normalizing
order-three subgroup, so `O₂(M)` cannot invert it. -/
public theorem firstCase_V2_inf_twoCore_eq_bot_of_quotient_psl2_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (K : Type u) [Field K] [Finite K]
    (hK3 : Nat.card K = 3)
    (L : Subgroup ((↥M) ⧸ pPrimeCore 2 (↥M)))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (hpsl : Nonempty (L ≃* PSL2 K)) :
    fd.V2 ⊓ twoCoreOf M = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  have hpodd : Odd od.p :=
    (Fact.out : Nat.Prime od.p).odd_of_ne_two (firstCase_oriented_p_odd c od)
  have hP0ne : P ⊓ M ≠ ⊥ :=
    firstCase_P0_ne_bot hmin c od hfirst hHhat hU Q M hMmax hMN hSM
  let PM : Subgroup G := P ⊓ M
  let : Fintype ↥PM := Fintype.ofFinite _
  have hP0p : IsPGroup od.p PM :=
    (qCoreOf_isPGroup od.d.bg.U od.p).to_inf_left
  by_contra hne
  have hnt : Nontrivial ↥(fd.V2 ⊓ twoCoreOf M) :=
    (Subgroup.nontrivial_iff_ne_bot (fd.V2 ⊓ twoCoreOf M)).2 hne
  obtain ⟨x, hxne⟩ := exists_ne (1 : ↥(fd.V2 ⊓ twoCoreOf M))
  let xG : G := x
  have hxV : xG ∈ fd.V2 := x.2.1
  have hxO : xG ∈ twoCoreOf M := x.2.2
  have hxne' : xG ≠ 1 := by
    intro hx1
    apply hxne
    apply Subtype.ext
    exact hx1
  obtain ⟨m, hmN, hm⟩ :=
    firstCase_P2_transitive hmin c od fd hU Q xG od.d.bg.t2
      hxV (fd.t2_mem_V2) hxne' od.d.bg.t2_involution.1
  have hmM : m ∈ M := hMN hmN
  have hq2 : qCoreOf M 2 = twoCoreOf M := by
    rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
  have hxO' : xG ∈ qCoreOf M 2 := by simpa [hq2] using hxO
  have ht2O : od.d.bg.t2 ∈ twoCoreOf M := by
    have hnorm : IsNormalIn (qCoreOf M 2) M := qCoreOf_normal_in M 2
    have hconj : m * xG * m⁻¹ ∈ qCoreOf M 2 := hnorm.2 m hmM xG hxO'
    have hconj' : od.d.bg.t2 ∈ qCoreOf M 2 := by simpa [hm] using hconj
    simpa [hq2] using hconj'
  have ht2M' : od.d.bg.t2 ∈ M :=
    (qCoreOf_le M 2) (by simpa [hq2] using ht2O)
  let t2M : ↥M := ⟨od.d.bg.t2, ht2M'⟩
  have ht2M1 : t2M ≠ 1 := by
    intro h
    exact od.d.bg.t2_involution.1 (congrArg Subtype.val h)
  have ht2M2 : t2M ^ 2 = 1 := by
    apply Subtype.ext
    simpa using od.d.bg.t2_involution.2
  let P0M : Subgroup (↥M) := PM.subgroupOf M
  have hP0Mp : IsPGroup od.p P0M :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hP0Mne : P0M ≠ ⊥ := by
    intro hbot
    apply hP0ne
    apply le_bot_iff.mp
    intro y hy
    have hyM : y ∈ M := (Subgroup.mem_inf.mp hy).2
    have hyP0M : (⟨y, hyM⟩ : ↥M) ∈ P0M := Subgroup.mem_subgroupOf.mpr hy
    have hy1 : (⟨y, hyM⟩ : ↥M) = 1 :=
      Subgroup.mem_bot.mp (by simpa [hbot] using hyP0M)
    exact congrArg Subtype.val hy1
  have htinvP0M : ∀ x ∈ P0M, t2M * x * t2M⁻¹ = x⁻¹ := by
    intro x hx
    have hxPM : (x : G) ∈ PM := hx
    have hxP : (x : G) ∈ P := hxPM.1
    apply Subtype.ext
    exact firstCase_t2_inverts_primeCore c od (x : G) hxP
  let O : Subgroup (↥M) := pPrimeCore 2 (↥M)
  let : O.Normal := by dsimp [O]; infer_instance
  let Q : Type u := ↥M ⧸ O
  let : Group Q := QuotientGroup.Quotient.group O
  let q : ↥M →* Q := QuotientGroup.mk' O
  let : L.Normal := hLnormal
  let T2M : Subgroup (↥M) := (qCoreOf M 2).subgroupOf M
  have hT2Mp : IsPGroup 2 T2M :=
    (qCoreOf_isPGroup M 2).of_equiv
      (Subgroup.subgroupOfEquivOfLe (qCoreOf_le M 2)).symm
  have hT2Mnormal : T2M.Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer
      (H := M) (N := qCoreOf M 2) ?_
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact (qCoreOf_normal_in M 2).2 m hm y hy
    · intro hy
      have h' := (qCoreOf_normal_in M 2).2 m⁻¹ (M.inv_mem hm) (m * y * m⁻¹) hy
      have hEq : m⁻¹ * (m * y * m⁻¹) * m = y := by group
      simpa [hEq] using h'
  have hT2Mt : t2M ∈ T2M := Subgroup.mem_subgroupOf.mpr (by simpa [hq2] using ht2O)
  let T2Q : Subgroup Q := T2M.map q
  have hT2Qp : IsPGroup 2 T2Q := IsPGroup.map hT2Mp q
  have hT2QleL : T2Q ≤ L :=
    subgroup_le_of_isPGroup_coindex_odd L hLnormal hLindex T2Q hT2Qp
  have htL' : q t2M ∈ L :=
    hT2QleL (Subgroup.mem_map.mpr ⟨t2M, hT2Mt, rfl⟩)
  let P0Q : Subgroup Q := P0M.map q
  have hP0Qp : IsPGroup od.p P0Q := IsPGroup.map hP0Mp q
  have hP0Qne : P0Q ≠ ⊥ := by
    intro hbot
    have hP0MleO : P0M ≤ O := by
      have hker : q.ker = O := QuotientGroup.ker_mk' O
      have hle : P0M ≤ q.ker :=
        (Subgroup.map_eq_bot_iff P0M).mp (by simpa [P0Q] using hbot)
      simpa [hker] using hle
    have hCentOdd : twoCoreOf M ≤ Subgroup.centralizer (oddCoreOf M : Set G) :=
      twoCoreOf_centralizes_oddCoreOf M
    have hP0Mnt : Nontrivial ↥P0M :=
      (Subgroup.nontrivial_iff_ne_bot P0M).2 hP0Mne
    obtain ⟨yM, hyMne⟩ := exists_ne (1 : ↥P0M)
    let yMG : G := yM
    have hyMval : (yM : G) ∈ PM := yM.2
    have hyMP : (yM : G) ∈ P := hyMval.1
    have hyOdd : (yM : G) ∈ oddCoreOf M :=
      Subgroup.mem_map.mpr ⟨(yM : ↥M), hP0MleO yM.2, rfl⟩
    have hyCent : od.d.bg.t2 * (yM : G) * od.d.bg.t2⁻¹ = (yM : G) := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp (hCentOdd ht2O)) (yM : G) hyOdd
      calc
        od.d.bg.t2 * (yM : G) * od.d.bg.t2⁻¹ =
            ((yM : G) * od.d.bg.t2) * od.d.bg.t2⁻¹ := by rw [hcomm]
        _ = (yM : G) := by group
    have hyInv : od.d.bg.t2 * (yM : G) * od.d.bg.t2⁻¹ = (yM : G)⁻¹ :=
      firstCase_t2_inverts_primeCore c od (yM : G) hyMP
    have hyinv_eq : (yM : G)⁻¹ = (yM : G) := hyInv.symm.trans hyCent
    have hy2 : (yM : G) * (yM : G) = 1 := by
      calc
        (yM : G) * (yM : G) = (yM : G)⁻¹ * (yM : G) := by rw [hyinv_eq]
        _ = 1 := by simp
    have hord2 : orderOf (yM : G) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hy2)
    have hordP : orderOf (yM : G) ∣ Nat.card ↥PM :=
      Subgroup.orderOf_dvd_natCard PM hyMval
    obtain ⟨n, hn⟩ := hP0p.exists_card_eq
    have hcopBase : Nat.Coprime 2 od.p :=
      (Nat.coprime_primes Nat.prime_two (Fact.out : Nat.Prime od.p)).2 (by
        intro h
        exact firstCase_oriented_p_odd c od h.symm)
    have hcop : Nat.Coprime 2 (od.p ^ n) := hcopBase.pow_right n
    have hord1 : orderOf (yM : G) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hord2 (by
        rw [hn] at hordP
        exact hordP)
    exact hyMne (by
      have h1 : (yM : G) = 1 := orderOf_eq_one_iff.mp hord1
      apply Subtype.ext
      apply Subtype.ext
      exact h1)
  exact False.elim (no_involution_inverts_of_quotient_linear_three
    K hK3 L hLnormal hLindex hpsl P0M od.p od.p_prime
    hpodd hP0Mp hP0Qne t2M T2M hT2Mnormal hT2Mp hT2Mt
    ht2M1 ht2M2 htinvP0M)

/-- In the `PGL₂(3) ≃ S₄` quotient branch of the `D`-group `M`, the
Klein-four `V₂` avoids `O₂(M)`: its image in the model is a self-normalizing
order-three subgroup, so `O₂(M)` cannot invert it. -/
public theorem firstCase_V2_inf_twoCore_eq_bot_of_quotient_pgl2_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (K : Type u) [Field K] [Finite K]
    (hK3 : Nat.card K = 3)
    (L : Subgroup ((↥M) ⧸ pPrimeCore 2 (↥M)))
    (hLnormal : L.Normal) (hLindex : Odd L.index)
    (hpgl : Nonempty (L ≃* PGL2 K)) :
    fd.V2 ⊓ twoCoreOf M = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  have hpodd : Odd od.p :=
    (Fact.out : Nat.Prime od.p).odd_of_ne_two (firstCase_oriented_p_odd c od)
  have hP0ne : P ⊓ M ≠ ⊥ :=
    firstCase_P0_ne_bot hmin c od hfirst hHhat hU Q M hMmax hMN hSM
  let PM : Subgroup G := P ⊓ M
  let : Fintype ↥PM := Fintype.ofFinite _
  have hP0p : IsPGroup od.p PM :=
    (qCoreOf_isPGroup od.d.bg.U od.p).to_inf_left
  by_contra hne
  have hnt : Nontrivial ↥(fd.V2 ⊓ twoCoreOf M) :=
    (Subgroup.nontrivial_iff_ne_bot (fd.V2 ⊓ twoCoreOf M)).2 hne
  obtain ⟨x, hxne⟩ := exists_ne (1 : ↥(fd.V2 ⊓ twoCoreOf M))
  let xG : G := x
  have hxV : xG ∈ fd.V2 := x.2.1
  have hxO : xG ∈ twoCoreOf M := x.2.2
  have hxne' : xG ≠ 1 := by
    intro hx1
    apply hxne
    apply Subtype.ext
    exact hx1
  obtain ⟨m, hmN, hm⟩ :=
    firstCase_P2_transitive hmin c od fd hU Q xG od.d.bg.t2
      hxV (fd.t2_mem_V2) hxne' od.d.bg.t2_involution.1
  have hmM : m ∈ M := hMN hmN
  have hq2 : qCoreOf M 2 = twoCoreOf M := by
    rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
  have hxO' : xG ∈ qCoreOf M 2 := by simpa [hq2] using hxO
  have ht2O : od.d.bg.t2 ∈ twoCoreOf M := by
    have hnorm : IsNormalIn (qCoreOf M 2) M := qCoreOf_normal_in M 2
    have hconj : m * xG * m⁻¹ ∈ qCoreOf M 2 := hnorm.2 m hmM xG hxO'
    have hconj' : od.d.bg.t2 ∈ qCoreOf M 2 := by simpa [hm] using hconj
    simpa [hq2] using hconj'
  have ht2M' : od.d.bg.t2 ∈ M :=
    (qCoreOf_le M 2) (by simpa [hq2] using ht2O)
  let t2M : ↥M := ⟨od.d.bg.t2, ht2M'⟩
  have ht2M1 : t2M ≠ 1 := by
    intro h
    exact od.d.bg.t2_involution.1 (congrArg Subtype.val h)
  have ht2M2 : t2M ^ 2 = 1 := by
    apply Subtype.ext
    simpa using od.d.bg.t2_involution.2
  let P0M : Subgroup (↥M) := PM.subgroupOf M
  have hP0Mp : IsPGroup od.p P0M :=
    hP0p.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hP0Mne : P0M ≠ ⊥ := by
    intro hbot
    apply hP0ne
    apply le_bot_iff.mp
    intro y hy
    have hyM : y ∈ M := (Subgroup.mem_inf.mp hy).2
    have hyP0M : (⟨y, hyM⟩ : ↥M) ∈ P0M := Subgroup.mem_subgroupOf.mpr hy
    have hy1 : (⟨y, hyM⟩ : ↥M) = 1 :=
      Subgroup.mem_bot.mp (by simpa [hbot] using hyP0M)
    exact congrArg Subtype.val hy1
  have htinvP0M : ∀ x ∈ P0M, t2M * x * t2M⁻¹ = x⁻¹ := by
    intro x hx
    have hxPM : (x : G) ∈ PM := hx
    have hxP : (x : G) ∈ P := hxPM.1
    apply Subtype.ext
    exact firstCase_t2_inverts_primeCore c od (x : G) hxP
  let O : Subgroup (↥M) := pPrimeCore 2 (↥M)
  let : O.Normal := by dsimp [O]; infer_instance
  let Q : Type u := ↥M ⧸ O
  let : Group Q := QuotientGroup.Quotient.group O
  let q : ↥M →* Q := QuotientGroup.mk' O
  let : L.Normal := hLnormal
  let T2M : Subgroup (↥M) := (qCoreOf M 2).subgroupOf M
  have hT2Mp : IsPGroup 2 T2M :=
    (qCoreOf_isPGroup M 2).of_equiv
      (Subgroup.subgroupOfEquivOfLe (qCoreOf_le M 2)).symm
  have hT2Mnormal : T2M.Normal := by
    refine Subgroup.normal_subgroupOf_of_le_normalizer
      (H := M) (N := qCoreOf M 2) ?_
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact (qCoreOf_normal_in M 2).2 m hm y hy
    · intro hy
      have h' := (qCoreOf_normal_in M 2).2 m⁻¹ (M.inv_mem hm) (m * y * m⁻¹) hy
      have hEq : m⁻¹ * (m * y * m⁻¹) * m = y := by group
      simpa [hEq] using h'
  have hT2Mt : t2M ∈ T2M := Subgroup.mem_subgroupOf.mpr (by simpa [hq2] using ht2O)
  let T2Q : Subgroup Q := T2M.map q
  have hT2Qp : IsPGroup 2 T2Q := IsPGroup.map hT2Mp q
  have hT2QleL : T2Q ≤ L :=
    subgroup_le_of_isPGroup_coindex_odd L hLnormal hLindex T2Q hT2Qp
  have htL' : q t2M ∈ L :=
    hT2QleL (Subgroup.mem_map.mpr ⟨t2M, hT2Mt, rfl⟩)
  let P0Q : Subgroup Q := P0M.map q
  have hP0Qp : IsPGroup od.p P0Q := IsPGroup.map hP0Mp q
  have hP0Qne : P0Q ≠ ⊥ := by
    intro hbot
    have hP0MleO : P0M ≤ O := by
      have hker : q.ker = O := QuotientGroup.ker_mk' O
      have hle : P0M ≤ q.ker :=
        (Subgroup.map_eq_bot_iff P0M).mp (by simpa [P0Q] using hbot)
      simpa [hker] using hle
    have hCentOdd : twoCoreOf M ≤ Subgroup.centralizer (oddCoreOf M : Set G) :=
      twoCoreOf_centralizes_oddCoreOf M
    have hP0Mnt : Nontrivial ↥P0M :=
      (Subgroup.nontrivial_iff_ne_bot P0M).2 hP0Mne
    obtain ⟨yM, hyMne⟩ := exists_ne (1 : ↥P0M)
    let yMG : G := yM
    have hyMval : (yM : G) ∈ PM := yM.2
    have hyMP : (yM : G) ∈ P := hyMval.1
    have hyOdd : (yM : G) ∈ oddCoreOf M :=
      Subgroup.mem_map.mpr ⟨(yM : ↥M), hP0MleO yM.2, rfl⟩
    have hyCent : od.d.bg.t2 * (yM : G) * od.d.bg.t2⁻¹ = (yM : G) := by
      have hcomm := (Subgroup.mem_centralizer_iff.mp (hCentOdd ht2O)) (yM : G) hyOdd
      calc
        od.d.bg.t2 * (yM : G) * od.d.bg.t2⁻¹ =
            ((yM : G) * od.d.bg.t2) * od.d.bg.t2⁻¹ := by rw [hcomm]
        _ = (yM : G) := by group
    have hyInv : od.d.bg.t2 * (yM : G) * od.d.bg.t2⁻¹ = (yM : G)⁻¹ :=
      firstCase_t2_inverts_primeCore c od (yM : G) hyMP
    have hyinv_eq : (yM : G)⁻¹ = (yM : G) := hyInv.symm.trans hyCent
    have hy2 : (yM : G) * (yM : G) = 1 := by
      calc
        (yM : G) * (yM : G) = (yM : G)⁻¹ * (yM : G) := by rw [hyinv_eq]
        _ = 1 := by simp
    have hord2 : orderOf (yM : G) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hy2)
    have hordP : orderOf (yM : G) ∣ Nat.card ↥PM :=
      Subgroup.orderOf_dvd_natCard PM hyMval
    obtain ⟨n, hn⟩ := hP0p.exists_card_eq
    have hcopBase : Nat.Coprime 2 od.p :=
      (Nat.coprime_primes Nat.prime_two (Fact.out : Nat.Prime od.p)).2 (by
        intro h
        exact firstCase_oriented_p_odd c od h.symm)
    have hcop : Nat.Coprime 2 (od.p ^ n) := hcopBase.pow_right n
    have hord1 : orderOf (yM : G) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hord2 (by
        rw [hn] at hordP
        exact hordP)
    exact hyMne (by
      have h1 : (yM : G) = 1 := orderOf_eq_one_iff.mp hord1
      apply Subtype.ext
      apply Subtype.ext
      exact h1)
  exact False.elim (no_involution_inverts_of_quotient_linear_three_pgl2
    K hK3 L hLnormal hLindex hpgl P0M od.p od.p_prime
    hpodd hP0Mp hP0Qne t2M T2M hT2Mnormal hT2Mp hT2Mt
    ht2M1 ht2M2 htinvP0M)

/-- The full `D`-group quotient dispatcher: in every quotient branch of
the maximal overgroup `M`, the Klein-four `V₂` avoids `O₂(M)`, hence
lives in the component layer. -/
public theorem firstCase_V2_le_componentLayer_of_DGroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (fd : FirstCaseFourData c od.d)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (hD : IsDGroup ↥M) :
    fd.V2 ≤ componentLayerOf M := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hdisj := firstCase_V2_intersects_layer_or_twoCore
    hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM
  rcases hD with ⟨_hSylow, hQ⟩ | ⟨_hSylow, hA7⟩ |
    ⟨_hSylow, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
  · -- two-group quotient
      have hO2bot :=
        firstCase_V2_inf_twoCore_eq_bot_of_twoGroupQuotient
          hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM hQ
      rcases hdisj with hO2 | hE
      · exact False.elim (hO2 hO2bot)
      · exact firstCase_V2_le_of_inf_ne_bot hmin c od fd hU Q M hMN
          (componentLayerOf M) (fstar_componentLayerOf_isNormalIn M) hE
  · -- A₇ quotient
      have hO2bot :=
        firstCase_V2_inf_twoCore_eq_bot_of_quotient_ASeven
          hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM hA7
      rcases hdisj with hO2 | hE
      · exact False.elim (hO2 hO2bot)
      · exact firstCase_V2_le_of_inf_ne_bot hmin c od fd hU Q M hMN
          (componentLayerOf M) (fstar_componentLayerOf_isNormalIn M) hE
  · -- linear quotient
      let : Field K := inferInstance
      let : Finite K := inferInstance
      by_cases h3 : 3 < Nat.card K
      · have hO2bot :=
          firstCase_V2_inf_twoCore_eq_bot_of_quotient_linear_large
            hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM
            K hKprime h3 L hLnormal hLindex hLmodel
        rcases hdisj with hO2 | hE
        · exact False.elim (hO2 hO2bot)
        · exact firstCase_V2_le_of_inf_ne_bot hmin c od fd hU Q M hMN
            (componentLayerOf M) (fstar_componentLayerOf_isNormalIn M) hE
      · have hKge3 : 3 ≤ Nat.card K := by
          rcases hKprime with ⟨p, n, hp, hpodd, hn, hcard⟩
          rw [hcard]
          have hpge3 : 3 ≤ p := by
            have hpne2 : p ≠ 2 := by
              intro hp2
              subst p
              exact hpodd.not_two_dvd_nat (by simp)
            have hpge2 : 2 ≤ p := hp.two_le
            omega
          exact hpge3.trans (by
            have hnpos : 1 ≤ n := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (Nat.ne_of_gt hn))
            exact Nat.le_self_pow (a := p) (n := n) (Nat.ne_of_gt hnpos))
        have hK3 : Nat.card K = 3 := by omega
        rcases hLmodel with hpsl | hpgl
        · have hO2bot :=
            firstCase_V2_inf_twoCore_eq_bot_of_quotient_psl2_three
              hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM
              K hK3 L hLnormal hLindex hpsl
          rcases hdisj with hO2 | hE
          · exact False.elim (hO2 hO2bot)
          · exact firstCase_V2_le_of_inf_ne_bot hmin c od fd hU Q M hMN
              (componentLayerOf M) (fstar_componentLayerOf_isNormalIn M) hE
        · have hO2bot :=
            firstCase_V2_inf_twoCore_eq_bot_of_quotient_pgl2_three
              hmin c od hfirst hHhat hU Q fd M hMmax hMN hSM
              K hK3 L hLnormal hLindex hpgl
          rcases hdisj with hO2 | hE
          · exact False.elim (hO2 hO2bot)
          · exact firstCase_V2_le_of_inf_ne_bot hmin c od fd hU Q M hMN
              (componentLayerOf M) (fstar_componentLayerOf_isNormalIn M) hE

end CFSG.GorensteinWalter
