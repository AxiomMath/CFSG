module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBLeMSource
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreUInterM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePrimeCoreAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic first-case centralizer equation `C_U(t₁) = B × P₀` — work in progress

The requested unconditional theorem
`firstCase_cyclic_centralizer_t1_eq_B_sup_P0_of_a7` is **not yet proved**
and is intentionally not declared under that name.  The exact printed
route (`X = B ∩ PP^g ⊴ C_U(t₁)` ⇒ `C_U(t₁) ≤ M`) is invalid: the
corrected `PP^g` witness proves only `B ≤ N_G(X)`, not
`C_U(t₁) ≤ N_G(X)`.  This module currently contains only a private
conditional helper `..._of_le_M` with the extra hypothesis
`C_U(t₁) ≤ M`; the remaining core is
`C_U(t₁) ≤ N_G(B)` (with `B ≠ ⊥ ≤ B ∩ M`, so the landed normalizer
control gives `N_G(B) = M`).

No `sorry`, `admit`, `axiom`, or `opaque` is used.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Private conditional helper: the centralizer equation holds once the
remaining leg `C_U(t₁) ≤ M` is supplied.  The unconditional theorem is not
declared until that leg is proved. -/
private theorem firstCase_cyclic_centralizer_t1_eq_B_sup_P0_of_a7_of_le_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3)
    (hCUleM : centralizerIn od.d.bg.U od.d.bg.t1 ≤ M) :
    centralizerIn od.d.bg.U od.d.bg.t1 =
      od.d.bg.B ⊔ (qCoreOf od.d.bg.U od.p ⊓ M) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : BenderGlauberman.Hyp11KData od.d.bg :=
    firstCaseBGKData hmin c od.d
  have hBleM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_source
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hP0ne : qCoreOf od.d.bg.U od.p ⊓ M ≠ ⊥ :=
    firstCase_P0_ne_bot hmin c od hfirst hHhat hU Q M hMmax hMN hSM
  have hUint :=
    firstCase_cyclic_U_inter_M_eq_P0_sup_B_inter_M_of_a7
      hmin c od M hMmax hSM fd hV2 hA7 hU hp3 hP0ne
  have hBM : od.d.bg.B ⊓ M = od.d.bg.B := inf_eq_left.2 hBleM
  have hUMeq : od.d.bg.U ⊓ M =
      (qCoreOf od.d.bg.U od.p ⊓ M) ⊔ od.d.bg.B := by
    simpa [hBM, sup_comm] using hUint.1
  have hBleC : od.d.bg.B ≤ centralizerIn od.d.bg.U od.d.bg.t1 := by
    intro b hbB
    have hbU : b ∈ od.d.bg.U :=
      BenderGlauberman.theoremC_B_le_U od.d.bg hbB
    have hbB1 : b ∈ od.d.bg.B1 :=
      BenderGlauberman.theoremC_mem_B1_of_mem_B od.d.bg hbB
    have hfix : od.d.bg.t1 * b * od.d.bg.t1⁻¹ = b :=
      BenderGlauberman.theoremC_fixed_by_t1_of_mem_B1 od.d.bg hbB1
    have hcomm : b * od.d.bg.t1 = od.d.bg.t1 * b := by
      calc
        b * od.d.bg.t1 = (od.d.bg.t1 * b * od.d.bg.t1⁻¹) * od.d.bg.t1 := by
          rw [hfix]
        _ = od.d.bg.t1 * b := by group
    change b ∈ od.d.bg.U ⊓ Subgroup.centralizer ({od.d.bg.t1} : Set G)
    exact Subgroup.mem_inf.mpr ⟨hbU, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm⟩
  have hP0leC : qCoreOf od.d.bg.U od.p ⊓ M ≤
      centralizerIn od.d.bg.U od.d.bg.t1 := by
    intro x hx
    have hxP : x ∈ qCoreOf od.d.bg.U od.p := (Subgroup.mem_inf.mp hx).1
    have hxU : x ∈ od.d.bg.U := qCoreOf_le od.d.bg.U od.p hxP
    have hcomm : x * od.d.bg.t1 = od.d.bg.t1 * x :=
      (Subgroup.mem_centralizer_iff.mp
        (firstCase_t1_centralizes_primeCore c od)) x hxP
    exact Subgroup.mem_inf.mpr ⟨hxU, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm⟩
  have hCsup : od.d.bg.B ⊔ (qCoreOf od.d.bg.U od.p ⊓ M) ≤
      centralizerIn od.d.bg.U od.d.bg.t1 :=
    sup_le hBleC hP0leC
  have hCleU : centralizerIn od.d.bg.U od.d.bg.t1 ≤ od.d.bg.U :=
    by
      intro x hx
      exact (Subgroup.mem_inf.mp hx).1
  have hCleUM : centralizerIn od.d.bg.U od.d.bg.t1 ≤ od.d.bg.U ⊓ M :=
    le_inf hCleU hCUleM
  apply le_antisymm
  · intro x hx
    have hxUM : x ∈ od.d.bg.U ⊓ M := hCleUM hx
    have hxP0B : x ∈ (qCoreOf od.d.bg.U od.p ⊓ M) ⊔ od.d.bg.B := by
      rwa [hUMeq] at hxUM
    simpa [sup_comm] using hxP0B
  · exact hCsup

/-- In the cyclic first case, the selected odd core `P = O_p(U)` is disjoint
from `B = C_U(S)`: `t₂` inverts `P` and fixes `B`, and `B` has odd order. -/
public theorem firstCase_cyclic_primeCore_inf_B_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B) :
    qCoreOf od.d.bg.U od.p ⊓ od.d.bg.B = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  apply le_bot_iff.mp
  intro x hx
  have hxP : x ∈ P := (Subgroup.mem_inf.mp hx).1
  have hxB : x ∈ od.d.bg.B := (Subgroup.mem_inf.mp hx).2
  have hfix : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x := by
    have ht2S : od.d.bg.t2 ∈ (od.d.bg.S : Subgroup G) := od.d.bg.t2_mem_S
    have hScentB : od.d.bg.t2 ∈ Subgroup.centralizer
        ((od.d.bg.B : Subgroup G) : Set G) :=
      S_centralizes_B od.d.bg ht2S
    have hcomm := (Subgroup.mem_centralizer_iff.mp hScentB) x hxB
    calc
      od.d.bg.t2 * x * od.d.bg.t2⁻¹ = (x * od.d.bg.t2) * od.d.bg.t2⁻¹ := by rw [hcomm]
      _ = x := by group
  have hinv : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x⁻¹ :=
    firstCase_t2_inverts_primeCore c od x hxP
  have hxinv : x⁻¹ = x := hinv.symm.trans hfix
  have hx2 : x * x = 1 := by
    calc
      x * x = x⁻¹ * x := congrArg (fun z : G => z * x) hxinv.symm
      _ = 1 := by simp
  have hord2 : orderOf x ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
  have hordB : orderOf x ∣ Nat.card (↥od.d.bg.B) :=
    Subgroup.orderOf_dvd_natCard od.d.bg.B hxB
  have hBodd : Odd (Nat.card (↥od.d.bg.B)) :=
    firstCase_cyclic_B_odd c od hU
  have hordOdd : Odd (orderOf x) := Odd.of_dvd_nat hBodd hordB
  have hord1 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hordOdd.not_two_dvd_nat (by rw [h])
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp hord1

/-- In the cyclic first case, `P = O_p(U)` normalizes its intersection with
the maximal overgroup `M` (because `P` is abelian). -/
public theorem firstCase_cyclic_primeCore_le_normalizer_P0
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) :
    qCoreOf od.d.bg.U od.p ≤
      Subgroup.normalizer
        ((qCoreOf od.d.bg.U od.p ⊓ M : Subgroup G) : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P0 : Subgroup G := P ⊓ M
  have hPabel : IsMulCommutative (↥P) := firstCase_cyclic_primeCore_abelian c od
  rw [isMulCommutative_iff] at hPabel
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxP : (x : G) ∈ P := (Subgroup.mem_inf.mp hx).1
    have hxM : (x : G) ∈ M := (Subgroup.mem_inf.mp hx).2
    have hcomm := hPabel ⟨p, hp⟩ ⟨(x : G), hxP⟩
    have hcommG : p * (x : G) = (x : G) * p :=
      congrArg Subtype.val hcomm
    have hconj : p * (x : G) * p⁻¹ = (x : G) := by
      rw [hcommG]
      group
    have hxP' : p * (x : G) * p⁻¹ ∈ P := by rw [hconj]; exact hxP
    have hxM' : p * (x : G) * p⁻¹ ∈ M := by rw [hconj]; exact hxM
    exact Subgroup.mem_inf.mpr
      ⟨hxP', hxM'⟩
  · intro hx
    have hxP : p * (x : G) * p⁻¹ ∈ P := (Subgroup.mem_inf.mp hx).1
    have hxM : p * (x : G) * p⁻¹ ∈ M := (Subgroup.mem_inf.mp hx).2
    have hxP0 : (x : G) ∈ P := by
      have hback : (x : G) = p⁻¹ * (p * (x : G) * p⁻¹) * p := by group
      rw [hback]
      exact P.mul_mem (P.mul_mem (P.inv_mem hp) hxP) hp
    have hcomm := hPabel ⟨p, hp⟩ ⟨(x : G), hxP0⟩
    have hcommG : p * (x : G) = (x : G) * p :=
      congrArg Subtype.val hcomm
    have hconj : p * (x : G) * p⁻¹ = (x : G) := by
      rw [hcommG]
      group
    have hxM0 : (x : G) ∈ M := by
      rw [hconj] at hxM
      exact hxM
    exact Subgroup.mem_inf.mpr ⟨hxP0, hxM0⟩

/-- In the cyclic first-case A₇ model, `S` centralizes no nontrivial
`q`-core of `U`: otherwise that core would lie in `B ∩ M`, be normal in
`H`, and force `H ≤ N_G(X) ≤ M`, contradicting `N_G(P₂) ⊄ H`. -/
public theorem firstCase_cyclic_S_not_centralizes_nontrivial_qCore
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3)
    {q : ℕ} (hq : qCoreOf od.d.bg.U q ≠ ⊥) :
    ¬ (od.d.bg.S : Subgroup G) ≤
      Subgroup.centralizer (qCoreOf od.d.bg.U q : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro hScent
  let Qq : Subgroup G := qCoreOf od.d.bg.U q
  have hBleM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_source
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hQleB : Qq ≤ od.d.bg.B := by
    intro x hx
    have hxU : x ∈ od.d.bg.U := qCoreOf_le od.d.bg.U q hx
    have hxcentS : x ∈ Subgroup.centralizer
        ((od.d.bg.S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hcomm := (Subgroup.mem_centralizer_iff.mp (hScent hs)) x hx
      change s * x = x * s
      exact hcomm.symm
    rw [B_eq_centralizer_U od.d.bg]
    exact Subgroup.mem_inf.mpr ⟨hxU, hxcentS⟩
  have hQleBM : Qq ≤ od.d.bg.B ⊓ M := le_inf hQleB (hQleB.trans hBleM)
  have hQnormalH : IsNormalIn Qq od.d.bg.H := by
    change IsNormalIn
      ((pCore q (↥od.d.bg.U)).map od.d.bg.U.subtype) od.d.bg.H
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := pCore q (↥od.d.bg.U)) (hKchar := by infer_instance)
      (hHnormal := bg_U_normal_in_H od.d.bg)
  have hHleNQ : od.d.bg.H ≤ Subgroup.normalizer (Qq : Set G) :=
    le_normalizer_of_isNormalIn hQnormalH
  have hEeq := firstCase_cyclic_componentLayer_normalizer_eq_of_a7
    hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 Qq hq hQleBM
  have hNQleM := firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq
    hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 Qq hq hQleBM hEeq
  have hHleM : od.d.bg.H ≤ M := hHleNQ.trans hNQleM
  have hHcoatom : IsCoatom od.d.bg.H := by
    simpa [od.d.H_eq, hHhat] using c.Hhat_maximal
  have hEq : od.d.bg.H = M := by
    by_cases hEq : od.d.bg.H = M
    · exact hEq
    · have hlt : od.d.bg.H < M := lt_of_le_of_ne hHleM hEq
      have hMtop : M = ⊤ := hHcoatom.2 M hlt
      exact False.elim (hMmax.1 hMtop)
  have hNleH : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ od.d.bg.H := by
    simpa [hEq] using hMN
  exact (firstCase_normalizer_P2_not_le_H hmin c od fd hU Q) hNleH

/-- The user's centralizer-core reduction: if `C_B(P) ≠ 1`, then the landed
normalizer control applied to that nontrivial subgroup of `B ∩ M` gives
`P ≤ M`. -/
public theorem firstCase_cyclic_primeCore_le_M_of_a7_of_CB_ne
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3)
    (hCB : od.d.bg.B ⊓ Subgroup.centralizer
      (qCoreOf od.d.bg.U od.p : Set G) ≠ ⊥) :
    qCoreOf od.d.bg.U od.p ≤ M := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let X : Subgroup G :=
    od.d.bg.B ⊓ Subgroup.centralizer (P : Set G)
  have hXleB : X ≤ od.d.bg.B := inf_le_left
  have hBleM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_source
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hXleBM : X ≤ od.d.bg.B ⊓ M := le_inf hXleB (hXleB.trans hBleM)
  have hEeq := firstCase_cyclic_componentLayer_normalizer_eq_of_a7
    hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 X hCB hXleBM
  have hNXleM := firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq
    hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 X hCB hXleBM hEeq
  have hPleCX : P ≤ Subgroup.centralizer (X : Set G) := by
    intro p hp x hx
    have hxcentP : x ∈ Subgroup.centralizer (P : Set G) :=
      (Subgroup.mem_inf.mp hx).2
    have hcomm : p * x = x * p :=
      (Subgroup.mem_centralizer_iff.mp hxcentP) p hp
    exact hcomm.symm
  have hPleNX : P ≤ Subgroup.normalizer (X : Set G) :=
    hPleCX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  exact hPleNX.trans hNXleM

end CFSG.GorensteinWalter
