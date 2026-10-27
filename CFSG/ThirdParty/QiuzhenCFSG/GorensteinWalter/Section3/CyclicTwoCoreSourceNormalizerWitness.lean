module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBLeM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePPg
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePInfPg
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePrimeCoreAbelian
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Corrected source witness for `B ∩ PP^g`

The paper (p. 223) applies its Lemma 2.9 normalizer control to
`X = B ∩ PP^g`, a normal subgroup of `C_U(t₁)`, and concludes
`B ⊆ M`.  The `P ∩ P^g` normality/triviality steps behind that witness
are invalid (see `tasks/gw-section3.md` and `/tmp/s3-b-le-m-report.md`).

This module implements the corrected `PP^g` witness without either false
claim:

* let `C = C_U(V₁)`, `P = O_p(U)`, `P^g = P` conjugated by
  `g ∈ N_G(V₁) \ H`, and `R = P ∨ P^g`;
* `C ≤ H` and `C ≤ H^g`, so `P` and `P^g` are normal `p`-subgroups of
  `C`, hence `R` is a normal `p`-subgroup of `C` and lies in the chosen
  Sylow `p`-subgroup `P₁ = P·P₂` of `C`;
* `P^g ≠ P` (`N_G(P) ≤ H`), so `P < R`;
* `P₁ ∩ B = P₂` (`P ∩ B = 1`), and the normal-`p`-subgroup argument gives
  a nontrivial `q ∈ R ∩ P₂`; with `X = R ∩ B` we get
  `1 ≠ X ≤ P₂ ≤ B ∩ M`;
* `B ≤ C`, `C` normalizes `R`, and `B` normalizes itself, so
  `B ≤ N_G(R ∩ B) = N_G(X)`;
* the repaired `P ∩ P^g = ⊥`
  (`firstCase_P_inf_Pg_eq_bot`, see `CyclicTwoCorePInfPg.lean`) makes
  `[P, P^g] = 1`; since `P` is abelian, `R = P·P^g` centralizes `P`, so
  `X ≤ C_G(P)`.  The existential therefore also carries
  `X ≤ C_B(P)`, the input needed for `C_B(P) ≠ 1`.

The exact existential theorem is `firstCase_cyclic_exists_B_normalized_nontrivial_le_B_inter_M`.
No `sorry`, `admit`, `axiom`, or `opaque` is used.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Nontriviality of `B ∩ M` in the A₇ layer model, via the nontrivial
Sylow `p`-subgroup `P₂` of `B` contained in `M`. -/
private theorem firstCase_cyclic_B_inter_M_ne_bot_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M) :
    od.d.bg.B ⊓ M ≠ ⊥ := by
  let P2 : Subgroup G :=
    sylowCarrier (firstCase_P2_sylow c od hU Q)
  have hP2ne : P2 ≠ ⊥ :=
    firstCase_P2_ne_one hmin c od hfirst hHhat hU Q
  have hP2leBM : P2 ≤ od.d.bg.B ⊓ M := by
    intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨firstCase_cyclic_P2_le_B c od hU Q x hx,
        hMN (Subgroup.le_normalizer hx)⟩
  intro hbot
  apply hP2ne
  apply le_bot_iff.mp
  intro x hx
  have hxBM : x ∈ od.d.bg.B ⊓ M := hP2leBM hx
  rw [hbot] at hxBM
  exact Subgroup.mem_bot.mp hxBM

/-- First-case normalizer control `N_G(P) ≤ H` for `P = O_p(U)`. -/
private theorem firstCase_normalizer_P_le_H_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H) :
    Subgroup.normalizer (qCoreOf od.d.bg.U od.p : Set G) ≤ od.d.bg.H := by
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  have hPne : P ≠ ⊥ := by
    have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
    have hq : qCoreOf c.U od.p = P := by
      simpa [P] using (qCoreOf_eq_of_subgroup_eq hUeq od.p)
    simpa [hq] using od.primeCore_ne_bot
  have hPleFU : P ≤ fittingSubgroupOf od.d.bg.U :=
    fstar_qCoreOf_le_fittingSubgroupOf od.d.bg.U od.p od.p_prime
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hFU : fittingSubgroupOf c.U = fittingSubgroupOf od.d.bg.U :=
    congrArg fittingSubgroupOf hUeq
  have hPleFU' : P ≤ c.FU := by
    simpa [CentralizerSetup.FU, hFU] using hPleFU
  have hNX : Subgroup.normalizer (P : Set G) ≤ c.Hhat :=
    hfirst.2 P hPne hPleFU'
  have hNXH : Subgroup.normalizer (P : Set G) ≤ c.H := by
    simpa [hHhat] using hNX
  simpa [od.d.H_eq] using hNXH

/-- `V₁ = ⟨t, t₁⟩`. -/
private theorem firstCase_V1_eq_closure_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d) :
    fd.V1 = Subgroup.closure ({od.d.bg.t, od.d.bg.t1} : Set G) := by
  have hcomm : Commute od.d.bg.t od.d.bg.t1 := by
    have ht1H : od.d.bg.t1 ∈ od.d.bg.H := by
      have hle : (od.d.bg.S : Subgroup G) ≤
          od.d.bg.U ⊔ (od.d.bg.S : Subgroup G) :=
        le_sup_right
      rw [← od.d.bg.H_eq_US]
      exact hle od.d.bg.t1_mem_S
    rw [od.d.bg.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      at ht1H
    exact ht1H.symm
  have hne : od.d.bg.t ≠ od.d.bg.t1 := by
    intro h
    apply od.d.bg.t1_not_mem_S0
    rw [← h]
    exact od.d.bg.t_mem_S0
  exact kleinFour_eq_closure_of_mem fd.V1_klein
    (by simpa [od.d.t_eq] using fd.t_mem_V1) fd.t1_mem_V1
    od.d.bg.t_involution.1 od.d.bg.t1_involution.1 hne hcomm

/-- `C = C_U(t₁)` centralizes the whole Klein four `V₁`. -/
private theorem C_le_centralizer_V1_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d) :
    centralizerIn od.d.bg.U od.d.bg.t1 ≤
      Subgroup.centralizer (fd.V1 : Set G) := by
  have hUleCentT : od.d.bg.U ≤
      Subgroup.centralizer ({od.d.bg.t} : Set G) := by
    intro u hu
    have hUleH : od.d.bg.U ≤ od.d.bg.H :=
      le_sup_left.trans (le_of_eq od.d.bg.H_eq_US)
    have huH : u ∈ od.d.bg.H := hUleH hu
    rwa [← od.d.bg.H_eq_centralizer]
  intro x hx
  have hxU : x ∈ od.d.bg.U := (Subgroup.mem_inf.mp hx).1
  have hxT : x ∈ Subgroup.centralizer ({od.d.bg.t} : Set G) :=
    hUleCentT hxU
  have hxT1 : x ∈ Subgroup.centralizer ({od.d.bg.t1} : Set G) :=
    (Subgroup.mem_inf.mp hx).2
  rw [firstCase_V1_eq_closure_local c od fd, Subgroup.centralizer_closure]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hy with hyt | hyt1
  · subst y
    exact (Subgroup.mem_centralizer_iff.mp hxT) od.d.bg.t (by simp)
  · subst y
    exact (Subgroup.mem_centralizer_singleton_iff.mp hxT1).symm

/-- There is `g ∈ N_G(V₁) \ H` conjugating `t` into `V₁`. -/
private theorem firstCase_exists_g_outside_H_local
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d) :
    ∃ g : G, g ∈ Subgroup.normalizer (fd.V1 : Set G) ∧ g ∉ od.d.bg.H ∧
      ∃ y : G, y ∈ fd.V1 ∧ g * od.d.bg.t * g⁻¹ = y := by
  have hVtrans :=
    normalizer_transitive_on_kleinFour_pontset hmin c fd.V1_le_S fd.V1_klein
  obtain ⟨y, hyV, hy1, hyt⟩ := kleinFour_exists_mem_ne_one_ne_t fd.V1_klein
    (by simpa [od.d.t_eq] using fd.t_mem_V1) od.d.bg.t_involution.1
  obtain ⟨n, hnN, hn⟩ :=
    hVtrans od.d.bg.t y (by simpa [od.d.t_eq] using fd.t_mem_V1)
      hyV od.d.bg.t_involution.1 hy1
  refine ⟨n, hnN, ?_, y, hyV, hn⟩
  intro hnH
  have hnCent : n ∈ Subgroup.centralizer ({od.d.bg.t} : Set G) := by
    rwa [← od.d.bg.H_eq_centralizer]
  have hnfix : n * od.d.bg.t * n⁻¹ = od.d.bg.t := by
    have hcomm : od.d.bg.t * n = n * od.d.bg.t :=
      (Subgroup.mem_centralizer_singleton_iff.mp hnCent).symm
    calc
      n * od.d.bg.t * n⁻¹ = (od.d.bg.t * n) * n⁻¹ := by rw [hcomm]
      _ = od.d.bg.t := by group
  have hyeq : y = od.d.bg.t := by
    calc
      y = n * od.d.bg.t * n⁻¹ := hn.symm
      _ = od.d.bg.t := hnfix
  exact hyt hyeq

/-- `P ∩ B = 1`: `t₂` inverts `P` and fixes `B`. -/
private theorem primeCore_inf_B_eq_bot_local
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
  have hxB2 : x ∈ od.d.bg.B2 :=
    (inf_le_right : od.d.bg.B1 ⊓ od.d.bg.B2 ≤ od.d.bg.B2)
      (by simpa [BenderGlauberman.Hyp11.B] using hxB)
  have hxB2' : x ∈ od.d.bg.U ⊓
      Subgroup.centralizer ({od.d.bg.t2} : Set G) := by
    simpa [BenderGlauberman.Hyp11.B2, centralizerIn] using hxB2
  have hfix : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x := by
    have hcomm : od.d.bg.t2 * x = x * od.d.bg.t2 :=
      (Subgroup.mem_centralizer_iff.mp hxB2'.2) od.d.bg.t2 (by simp)
    calc
      od.d.bg.t2 * x * od.d.bg.t2⁻¹ =
          (x * od.d.bg.t2) * od.d.bg.t2⁻¹ := by rw [hcomm]
      _ = x := by group
  have hinv : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x⁻¹ :=
    firstCase_t2_inverts_primeCore c od x hxP
  have hx2 : x * x = 1 := by
    have hxinv : x⁻¹ = x := hinv.symm.trans hfix
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

/-- `P₁ ∩ B = P₂`, where `P₁ = P · P₂`. -/
private theorem firstCase_P1_join_inter_B_eq_P2_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B) :
    (qCoreOf od.d.bg.U od.p ⊔
        sylowCarrier (firstCase_P2_sylow c od hU Q)) ⊓ od.d.bg.B =
      sylowCarrier (firstCase_P2_sylow c od hU Q) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P2G : Subgroup G :=
    sylowCarrier (firstCase_P2_sylow c od hU Q)
  have hP2leB : P2G ≤ od.d.bg.B := firstCase_cyclic_P2_le_B c od hU Q
  have hP2leU : P2G ≤ od.d.bg.U := hP2leB.trans (by
    intro b hb
    exact BenderGlauberman.mem_U_of_mem_B_s4 od.d.bg hb)
  have hP2normP : P2G ≤ Subgroup.normalizer (P : Set G) :=
    hP2leU.trans
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in od.d.bg.U od.p))
  let : Subgroup.Normalizes P2G P := ⟨hP2normP⟩
  have hPBbot : P ⊓ od.d.bg.B = ⊥ :=
    primeCore_inf_B_eq_bot_local c od hU
  apply le_antisymm
  · intro x hx
    have hxP1 : x ∈ P ⊔ P2G := (Subgroup.mem_inf.mp hx).1
    have hxB : x ∈ od.d.bg.B := (Subgroup.mem_inf.mp hx).2
    have hprod : ((P ⊔ P2G : Subgroup G) : Set G) =
        (P : Set G) * (P2G : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left P P2G hP2normP
    have hxprod : x ∈ (P : Set G) * (P2G : Set G) := by
      change x ∈ ((P ⊔ P2G : Subgroup G) : Set G) at hxP1
      rwa [hprod] at hxP1
    rcases hxprod with ⟨p, hpP, q, hqP2, hxeq⟩
    have hpB : p ∈ od.d.bg.B := by
      have hxq : x * q⁻¹ ∈ od.d.bg.B :=
        od.d.bg.B.mul_mem hxB (od.d.bg.B.inv_mem (hP2leB hqP2))
      have hp_eq : p = x * q⁻¹ := by
        calc
          p = p * (q * q⁻¹) := by group
          _ = (p * q) * q⁻¹ := by group
          _ = x * q⁻¹ := by rw [← hxeq]
      rwa [hp_eq]
    have hpPB : p ∈ P ⊓ od.d.bg.B := Subgroup.mem_inf.mpr ⟨hpP, hpB⟩
    have hpbot : p ∈ (⊥ : Subgroup G) := by
      rw [hPBbot] at hpPB
      exact hpPB
    have hp1 : p = 1 := Subgroup.mem_bot.mp hpbot
    have hxq : x = q := by
      calc
        x = p * q := hxeq.symm
        _ = q := by rw [hp1]; simp
    simpa [hxq] using hqP2
  · intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_sup_right hx, hP2leB hx⟩

/-- `B ≤ C = C_U(t₁)`. -/
private theorem B_le_centralizerIn_t1_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c) :
    od.d.bg.B ≤ centralizerIn od.d.bg.U od.d.bg.t1 := by
  intro b hbB
  have hbB1 : b ∈ od.d.bg.B1 :=
    (inf_le_left : od.d.bg.B1 ⊓ od.d.bg.B2 ≤ od.d.bg.B1)
      (by simpa [BenderGlauberman.Hyp11.B] using hbB)
  have hbB1' : b ∈ od.d.bg.U ⊓
      Subgroup.centralizer ({od.d.bg.t1} : Set G) := by
    simpa [BenderGlauberman.Hyp11.B1, centralizerIn] using hbB1
  change b ∈ od.d.bg.U ⊓ Subgroup.centralizer ({od.d.bg.t1} : Set G)
  exact hbB1'

/-- `C = C_U(t₁) ≤ H = C_G(t)`. -/
private theorem C_le_H_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (od : FirstCaseOrientedPrimeData c) :
    centralizerIn od.d.bg.U od.d.bg.t1 ≤ od.d.bg.H := by
  intro c hc
  have hcU : c ∈ od.d.bg.U := (Subgroup.mem_inf.mp hc).1
  have hUleH : od.d.bg.U ≤ od.d.bg.H :=
    le_sup_left.trans (le_of_eq od.d.bg.H_eq_US)
  exact hUleH hcU

/-- `C = C_U(t₁)` normalizes `P^g` for `g ∈ N_G(V₁)` with `t^g ∈ V₁`. -/
private theorem C_normalizes_conjugate_primeCore_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    {g y : G} (hgN : g ∈ Subgroup.normalizer (fd.V1 : Set G))
    (hg : g * od.d.bg.t * g⁻¹ = y) (hyV : y ∈ fd.V1) :
    centralizerIn od.d.bg.U od.d.bg.t1 ≤
      Subgroup.normalizer
        ((qCoreOf od.d.bg.U od.p).map (MulAut.conj g).toMonoidHom : Set G) := by
  classical
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let Pg : Subgroup G := P.map (MulAut.conj g).toMonoidHom
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  have hcCentV : z ∈ Subgroup.centralizer (fd.V1 : Set G) :=
    C_le_centralizer_V1_local c od fd hz
  have hcY : z * y = y * z :=
    (Subgroup.mem_centralizer_iff.mp hcCentV) y hyV |>.symm
  let a : G := g⁻¹ * z * g
  have haT : a * od.d.bg.t = od.d.bg.t * a := by
    dsimp [a]
    calc
      (g⁻¹ * z * g) * od.d.bg.t = g⁻¹ * z * (g * od.d.bg.t) := by group
      _ = g⁻¹ * z * ((g * od.d.bg.t * g⁻¹) * g) := by group
      _ = g⁻¹ * (z * y) * g := by rw [← hg]; group
      _ = g⁻¹ * (y * z) * g := by rw [hcY]
      _ = g⁻¹ * ((g * od.d.bg.t * g⁻¹) * z) * g := by rw [hg]
      _ = od.d.bg.t * (g⁻¹ * z * g) := by group
  have haH : a ∈ od.d.bg.H := by
    rw [od.d.bg.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact haT
  have haN : a ∈ Subgroup.normalizer (P : Set G) :=
    firstCase_H_le_normalizer_primeCore c od haH
  have hnormalizes : ∀ c : G, c ∈ centralizerIn od.d.bg.U od.d.bg.t1 →
      ∀ x : G, x ∈ Pg → c * x * c⁻¹ ∈ Pg := by
    intro w hw x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hpP, rfl⟩
    have hcCentV' : w ∈ Subgroup.centralizer (fd.V1 : Set G) :=
      C_le_centralizer_V1_local c od fd hw
    have hcY' : w * y = y * w :=
      (Subgroup.mem_centralizer_iff.mp hcCentV') y hyV |>.symm
    let ac : G := g⁻¹ * w * g
    have hacT : ac * od.d.bg.t = od.d.bg.t * ac := by
      dsimp [ac]
      calc
        (g⁻¹ * w * g) * od.d.bg.t = g⁻¹ * w * (g * od.d.bg.t) := by group
        _ = g⁻¹ * w * ((g * od.d.bg.t * g⁻¹) * g) := by group
        _ = g⁻¹ * (w * y) * g := by rw [← hg]; group
        _ = g⁻¹ * (y * w) * g := by rw [hcY']
        _ = g⁻¹ * ((g * od.d.bg.t * g⁻¹) * w) * g := by rw [hg]
        _ = od.d.bg.t * (g⁻¹ * w * g) := by group
    have hacH : ac ∈ od.d.bg.H := by
      rw [od.d.bg.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      exact hacT
    have hacN : ac ∈ Subgroup.normalizer (P : Set G) :=
      firstCase_H_le_normalizer_primeCore c od hacH
    have hacP : ac * p * ac⁻¹ ∈ P :=
      ((Subgroup.mem_normalizer_iff.mp hacN) p).1 hpP
    have hconj : (MulAut.conj g) (ac * p * ac⁻¹) =
        w * (MulAut.conj g) p * w⁻¹ := by
      dsimp [ac]
      group
    exact Subgroup.mem_map.mpr ⟨ac * p * ac⁻¹, hacP, hconj⟩
  intro x
  constructor
  · intro hx
    exact hnormalizes z hz x hx
  · intro hx
    have hc' : z⁻¹ ∈ centralizerIn od.d.bg.U od.d.bg.t1 :=
      (centralizerIn od.d.bg.U od.d.bg.t1).inv_mem hz
    have hback := hnormalizes z⁻¹ hc' (z * x * z⁻¹) hx
    have hback' : z⁻¹ * (z * x * z⁻¹) * z ∈ Pg := by
      simpa [inv_inv] using hback
    have hxeq : z⁻¹ * (z * x * z⁻¹) * z = x := by group
    have hxPg : x ∈ Pg := by simpa [hxeq] using hback'
    exact hxPg

/-- The corrected `PP^g` source witness: a nontrivial `B ∩ M`-subgroup
normalized by `B` and centralizing the selected odd core `P = O_p(U)`. -/
public theorem firstCase_cyclic_exists_B_normalized_nontrivial_le_B_inter_M
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
    (hp3 : od.p = 3) :
    ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ od.d.bg.B ⊓ M ∧
      od.d.bg.B ≤ Subgroup.normalizer (X : Set G) ∧
        X ≤ Subgroup.centralizer (qCoreOf od.d.bg.U od.p : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let C : Subgroup G := centralizerIn od.d.bg.U od.d.bg.t1
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P2G : Subgroup G :=
    sylowCarrier (firstCase_P2_sylow c od hU Q)
  have hP2G_eq : P2G =
      (Q : Subgroup ↥od.d.bg.B).map od.d.bg.B.subtype :=
    firstCase_P2_carrier c od hU Q
  obtain ⟨g, hgN, hgout, y, hyV, hg⟩ :=
    firstCase_exists_g_outside_H_local hmin c od fd
  let Pg : Subgroup G := P.map (MulAut.conj g).toMonoidHom
  let R : Subgroup G := P ⊔ Pg
  let X : Subgroup G := R ⊓ od.d.bg.B

  have hPleC : P ≤ C := by
    intro x hx
    change x ∈ od.d.bg.U ⊓ Subgroup.centralizer ({od.d.bg.t1} : Set G)
    exact Subgroup.mem_inf.mpr
      ⟨qCoreOf_le od.d.bg.U od.p hx,
        (Subgroup.mem_centralizer_singleton_iff).mpr
          ((Subgroup.mem_centralizer_iff.mp
            (firstCase_t1_centralizes_primeCore c od)) x hx)⟩
  have hPgLeU : Pg ≤ od.d.bg.U := firstCase_Pg_le_U c od fd hgN
  have hPgLeCV : Pg ≤ od.d.bg.U ⊓
      Subgroup.centralizer (fd.V1 : Set G) :=
    firstCase_Pg_le_centralizerIn c od fd hgN
  have hPgLeC : Pg ≤ C := by
    intro x hx
    change x ∈ od.d.bg.U ⊓ Subgroup.centralizer ({od.d.bg.t1} : Set G)
    exact Subgroup.mem_inf.mpr
      ⟨hPgLeU hx,
        (Subgroup.mem_centralizer_singleton_iff).mpr
          ((Subgroup.mem_centralizer_iff.mp
            ((Subgroup.mem_inf.mp (hPgLeCV hx)).2))
              od.d.bg.t1 fd.t1_mem_V1 |>.symm)⟩
  have hC_le_NP : C ≤ Subgroup.normalizer (P : Set G) :=
    (C_le_H_local c od).trans (firstCase_H_le_normalizer_primeCore c od)
  have hPg_le_NP : Pg ≤ Subgroup.normalizer (P : Set G) :=
    hPgLeC.trans hC_le_NP
  have hPp : IsPGroup od.p P := qCoreOf_isPGroup od.d.bg.U od.p
  have hPgp : IsPGroup od.p Pg := hPp.map (MulAut.conj g).toMonoidHom
  have hRp : IsPGroup od.p R :=
    IsPGroup.to_sup_of_normal_left' (p := od.p) (H := P) (K := Pg)
      hPp hPgp hPg_le_NP
  have hP2GleC : P2G ≤ C := by
    intro x hx
    exact B_le_centralizerIn_t1_local c od ((firstCase_cyclic_P2_le_B c od hU Q) x hx)
  have hKleC : P ⊔ P2G ≤ C := sup_le hPleC hP2GleC
  have hRleC : R ≤ C := sup_le hPleC hPgLeC

  have hPnormC : IsNormalIn P C := by
    refine ⟨hPleC, ?_⟩
    intro z hz p hp
    exact ((Subgroup.mem_normalizer_iff.mp (hC_le_NP hz)) p).1 hp
  have hPgNormC : IsNormalIn Pg C := by
    refine ⟨hPgLeC, ?_⟩
    intro z hz x hx
    exact ((Subgroup.mem_normalizer_iff.mp
      (C_normalizes_conjugate_primeCore_local c od fd hgN hg hyV hz)) x).1 hx
  have hC_le_NPg : C ≤ Subgroup.normalizer (Pg : Set G) :=
    C_normalizes_conjugate_primeCore_local c od fd hgN hg hyV
  have hP0norm : (P.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := C) (N := P) hC_le_NP
  have hPg0norm : (Pg.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := C) (N := Pg) hC_le_NPg
  have : (P.subgroupOf C).Normal := hP0norm
  have : (Pg.subgroupOf C).Normal := hPg0norm
  have hR0norm : (R.subgroupOf C).Normal := by
    have hsup_eq : (P ⊔ Pg).subgroupOf C =
        P.subgroupOf C ⊔ Pg.subgroupOf C :=
      Subgroup.subgroupOf_sup hPleC hPgLeC
    rw [hsup_eq]
    exact Subgroup.sup_normal (P.subgroupOf C) (Pg.subgroupOf C)

  have hR0p : IsPGroup od.p (R.subgroupOf C) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRleC).symm
  let K : Subgroup C := (P ⊔ P2G).subgroupOf C
  have hKmap : K.map C.subtype = P ⊔ P2G :=
    Subgroup.map_subgroupOf_eq_of_le hKleC
  have hP1s_eq : sylowCarrier (firstCase_P1_sylow c od hU Q) = P ⊔ P2G := by
    rw [firstCase_P1_carrier c od hU Q, ← hP2G_eq]
  have hKmap_eq : K.map C.subtype =
      sylowCarrier (firstCase_P1_sylow c od hU Q) := by
    rw [hKmap, hP1s_eq]
  have hP1card : Nat.card (sylowCarrier (firstCase_P1_sylow c od hU Q)) =
      od.p ^ (Nat.card C).factorization od.p :=
    (sylowCarrier_le_and_card (firstCase_P1_sylow c od hU Q) rfl).2
  have hcardK : Nat.card K = Nat.card (sylowCarrier (firstCase_P1_sylow c od hU Q)) := by
    have h1 : Nat.card K = Nat.card (K.map C.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective K C.subtype C.subtype_injective).toEquiv
    rw [h1, hKmap_eq]
  have hKcard : Nat.card K = od.p ^ (Nat.card C).factorization od.p := by
    rw [hcardK, hP1card]
  let KS : Sylow od.p C := Sylow.ofCard K hKcard
  have hR0leK : R.subgroupOf C ≤ K := by
    have h := IsPGroup.le_sylow_of_normal hR0p KS
    exact h.trans_eq (by simp [KS])
  have hRleP1join : R ≤ P ⊔ P2G := by
    intro x hx
    have hxC : x ∈ C := hRleC hx
    have hxR0 : (⟨x, hxC⟩ : C) ∈ R.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hxK : (⟨x, hxC⟩ : C) ∈ K := hR0leK hxR0
    exact Subgroup.mem_subgroupOf.mp hxK

  have hPg_ne_P : Pg ≠ P := by
    intro hEq
    have hgN_P : g ∈ Subgroup.normalizer (P : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hEq
    exact hgout ((firstCase_normalizer_P_le_H_local c od hfirst hHhat) hgN_P)
  have hRnotP : ¬ R ≤ P := by
    intro hRleP
    have hPg_le_P : Pg ≤ P := by
      intro x hx
      exact hRleP ((le_sup_right : Pg ≤ P ⊔ Pg) hx)
    have hcardP_le : Nat.card P ≤ Nat.card Pg := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hPg_eq_P : Pg = P :=
      Subgroup.eq_of_le_of_card_ge hPg_le_P hcardP_le
    exact hPg_ne_P hPg_eq_P

  obtain ⟨r, hrR, hrP⟩ := Set.not_subset.mp hRnotP
  have hP2leB : P2G ≤ od.d.bg.B := firstCase_cyclic_P2_le_B c od hU Q
  have hP2leM : P2G ≤ M := by
    intro x hx
    exact hMN (Subgroup.le_normalizer hx)
  have hP2leBM : P2G ≤ od.d.bg.B ⊓ M := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hP2leB hx, hP2leM hx⟩
  have hP2leU : P2G ≤ od.d.bg.U := hP2leB.trans (by
    intro b hb
    exact BenderGlauberman.mem_U_of_mem_B_s4 od.d.bg hb)
  have hP2normP : P2G ≤ Subgroup.normalizer (P : Set G) :=
    hP2leU.trans
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in od.d.bg.U od.p))
  let : Subgroup.Normalizes P2G P := ⟨hP2normP⟩
  have hprod : ((P ⊔ P2G : Subgroup G) : Set G) =
      (P : Set G) * (P2G : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P P2G hP2normP
  have hrP1 : r ∈ P ⊔ P2G := hRleP1join hrR
  have hrprod : r ∈ (P : Set G) * (P2G : Set G) := by
    change r ∈ ((P ⊔ P2G : Subgroup G) : Set G) at hrP1
    rwa [hprod] at hrP1
  rcases hrprod with ⟨p, hpP, q, hqP2, hrpq⟩
  change p * q = r at hrpq
  have hpR : p ∈ R := (le_sup_left : P ≤ R) hpP
  have hqR : q ∈ R := by
    have hq_eq : q = p⁻¹ * r := by
      calc
        q = p⁻¹ * (p * q) := by group
        _ = p⁻¹ * r := by rw [hrpq]
    rw [hq_eq]
    exact R.mul_mem (R.inv_mem hpR) hrR
  have hqne : q ≠ 1 := by
    intro hq1
    apply hrP
    have hr_eq_p : r = p := by
      calc
        r = p * q := hrpq.symm
        _ = p := by rw [hq1]; simp
    simpa [hr_eq_p] using hpP
  have hqX : q ∈ X := Subgroup.mem_inf.mpr ⟨hqR, hP2leB hqP2⟩
  have hXne : X ≠ ⊥ := by
    intro hXbot
    apply hqne
    have hqbot : q ∈ (⊥ : Subgroup G) := by
      rw [hXbot] at hqX
      exact hqX
    exact Subgroup.mem_bot.mp hqbot

  have hP1_inter_B_eq : (P ⊔ P2G) ⊓ od.d.bg.B = P2G :=
    firstCase_P1_join_inter_B_eq_P2_local c od hU Q
  have hXleP2 : X ≤ P2G := by
    intro x hx
    have hxR : x ∈ R := hx.1
    have hxB : x ∈ od.d.bg.B := hx.2
    have hxP1 : x ∈ P ⊔ P2G := hRleP1join hxR
    have hxInf : x ∈ (P ⊔ P2G) ⊓ od.d.bg.B :=
      Subgroup.mem_inf.mpr ⟨hxP1, hxB⟩
    rw [hP1_inter_B_eq] at hxInf
    exact hxInf
  have hXleBM : X ≤ od.d.bg.B ⊓ M := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hx.2, hP2leM (hXleP2 hx)⟩

  have hPfu : P ≤ c.FU := by
    have hPleFU0 : P ≤ fittingSubgroupOf od.d.bg.U :=
      fstar_qCoreOf_le_fittingSubgroupOf od.d.bg.U od.p od.p_prime
    have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
    have hFU : fittingSubgroupOf c.U = fittingSubgroupOf od.d.bg.U :=
      congrArg fittingSubgroupOf hUeq
    simpa [CentralizerSetup.FU, hFU] using hPleFU0
  have hgH : g ∉ c.H := by
    intro hg
    exact hgout (by simpa [od.d.H_eq] using hg)
  have hPPgBot : P ⊓ Pg = ⊥ := by
    have hbot := firstCase_P_inf_Pg_eq_bot hmin c hfirst hHhat P hPfu g hgH
    simpa [Pg, conjugateSubgroup] using hbot
  have hPabel : IsMulCommutative (↥P) := firstCase_cyclic_primeCore_abelian c od
  rw [isMulCommutative_iff] at hPabel
  have hPcomm : P ≤ Subgroup.centralizer (Pg : Set G) := by
    intro p hp q hq
    have hpC : p ∈ C := hPleC hp
    have hqC : q ∈ C := hPgLeC hq
    have hpqPg : p * q * p⁻¹ ∈ Pg :=
      ((Subgroup.mem_normalizer_iff.mp (hC_le_NPg hpC)) q).1 hq
    have hpinvP : p⁻¹ ∈ P := P.inv_mem hp
    have hqpinvqP : q * p⁻¹ * q⁻¹ ∈ P :=
      ((Subgroup.mem_normalizer_iff.mp (hC_le_NP hqC)) p⁻¹).1 hpinvP
    have hcommP : p * q * p⁻¹ * q⁻¹ ∈ P := by
      have heq : p * q * p⁻¹ * q⁻¹ = p * (q * p⁻¹ * q⁻¹) := by group
      simpa [heq] using P.mul_mem hp hqpinvqP
    have hcommPg : p * q * p⁻¹ * q⁻¹ ∈ Pg :=
      Pg.mul_mem hpqPg (Pg.inv_mem hq)
    have hbot : p * q * p⁻¹ * q⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hPPgBot]
      exact Subgroup.mem_inf.mpr ⟨hcommP, hcommPg⟩
    have hcomm1 : p * q * p⁻¹ * q⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    have hpq : p * q = q * p := by
      calc
        p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
        _ = 1 * (q * p) := by rw [hcomm1]
        _ = q * p := by simp
    exact hpq.symm
  have hPgleCentP : Pg ≤ Subgroup.centralizer (P : Set G) := by
    intro q hq p hp
    exact (hPcomm hp q hq).symm
  have hPcentP : P ≤ Subgroup.centralizer (P : Set G) := by
    intro p hp p' hp'
    have hab : (p : G) * p' = p' * p := congrArg Subtype.val (hPabel ⟨p, hp⟩ ⟨p', hp'⟩)
    exact hab.symm
  have hRleCentP : R ≤ Subgroup.centralizer (P : Set G) :=
    sup_le hPcentP hPgleCentP
  have hXleCentP : X ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    exact hRleCentP (Subgroup.mem_inf.mp hx).1

  have hBleC : od.d.bg.B ≤ C := B_le_centralizerIn_t1_local c od
  have hRnormC : IsNormalIn R C := by
    refine ⟨hRleC, ?_⟩
    intro z hz x hx
    have hxR0 : (⟨x, hRleC hx⟩ : C) ∈ R.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hcR0 : (⟨z, hz⟩ : C) *
        (⟨x, hRleC hx⟩ : C) * (⟨z, hz⟩ : C)⁻¹ ∈ R.subgroupOf C :=
      hR0norm.conj_mem (⟨x, hRleC hx⟩) hxR0 (⟨z, hz⟩ : C)
    exact (Subgroup.mem_subgroupOf.mp hcR0)
  have hBleNX : od.d.bg.B ≤ Subgroup.normalizer (X : Set G) := by
    intro b hbB
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxR : b * x * b⁻¹ ∈ R :=
        hRnormC.2 b (hBleC hbB) x hx.1
      have hxB : b * x * b⁻¹ ∈ od.d.bg.B :=
        od.d.bg.B.mul_mem (od.d.bg.B.mul_mem hbB hx.2)
          (od.d.bg.B.inv_mem hbB)
      exact Subgroup.mem_inf.mpr ⟨hxR, hxB⟩
    · intro hx
      have hbB' : b⁻¹ ∈ od.d.bg.B := od.d.bg.B.inv_mem hbB
      have hbC' : b⁻¹ ∈ C := C.inv_mem (hBleC hbB)
      have hxR' : b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ ∈ R :=
        hRnormC.2 b⁻¹ hbC' (b * x * b⁻¹) hx.1
      have hxR : b⁻¹ * (b * x * b⁻¹) * b ∈ R := by
        simpa [inv_inv] using hxR'
      have hxB : b⁻¹ * (b * x * b⁻¹) * b ∈ od.d.bg.B := by
        have h1 : b⁻¹ * (b * x * b⁻¹) ∈ od.d.bg.B :=
          od.d.bg.B.mul_mem hbB' hx.2
        exact od.d.bg.B.mul_mem h1 hbB
      have hEq : b⁻¹ * (b * x * b⁻¹) * b = x := by group
      exact Subgroup.mem_inf.mpr
        ⟨by simpa [hEq] using hxR, by simpa [hEq] using hxB⟩

  exact ⟨X, hXne, hXleBM, hBleNX, hXleCentP⟩

/-- Strict reduction of the corrected source witness: `B ≤ M` already
gives the existential with `X = B ∩ M`. -/
private theorem firstCase_cyclic_exists_B_normalized_nontrivial_le_B_inter_M_of_B_le_M
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
    (hBM : od.d.bg.B ≤ M) :
    ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ od.d.bg.B ⊓ M ∧
      od.d.bg.B ≤ Subgroup.normalizer (X : Set G) := by
  refine ⟨od.d.bg.B ⊓ M, ?_, le_rfl, ?_⟩
  · exact firstCase_cyclic_B_inter_M_ne_bot_of_a7
      hmin c od hfirst hHhat hU Q M hMN
  · intro b hbB
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Subgroup.mem_inf.mpr
        ⟨od.d.bg.B.mul_mem (od.d.bg.B.mul_mem hbB hx.1)
            (od.d.bg.B.inv_mem hbB),
          M.mul_mem (M.mul_mem (hBM hbB) hx.2) (M.inv_mem (hBM hbB))⟩
    · intro hx
      have hbB' : b⁻¹ ∈ od.d.bg.B := od.d.bg.B.inv_mem hbB
      have hbM' : b⁻¹ ∈ M := M.inv_mem (hBM hbB)
      have hbBM' : b⁻¹ ∈ od.d.bg.B ⊓ M := Subgroup.mem_inf.mpr ⟨hbB', hbM'⟩
      have hbBM : b ∈ od.d.bg.B ⊓ M := Subgroup.mem_inf.mpr ⟨hbB, hBM hbB⟩
      have hxBM : b * (x : G) * b⁻¹ ∈ od.d.bg.B ⊓ M := hx
      have hback : b⁻¹ * (b * (x : G) * b⁻¹) ∈ od.d.bg.B ⊓ M :=
        (od.d.bg.B ⊓ M).mul_mem hbBM' hxBM
      have hback' : b⁻¹ * (b * (x : G) * b⁻¹) * b ∈ od.d.bg.B ⊓ M :=
        (od.d.bg.B ⊓ M).mul_mem hback hbBM
      have hEq : b⁻¹ * (b * (x : G) * b⁻¹) * b = (x : G) := by group
      simpa [hEq] using hback'

/-- The exact missing normalizer leg stated as a strict reduction: from
`B ≤ N_G(B ∩ M)` the corrected source witness exists. -/
private theorem firstCase_cyclic_exists_B_normalized_nontrivial_le_B_inter_M_of_B_normalizes_inter
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
    (hBnorm : od.d.bg.B ≤ Subgroup.normalizer
      ((od.d.bg.B ⊓ M : Subgroup G) : Set G)) :
    ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ od.d.bg.B ⊓ M ∧
      od.d.bg.B ≤ Subgroup.normalizer (X : Set G) := by
  have hBM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_layer
      hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 hU Q hMN hBnorm
  exact firstCase_cyclic_exists_B_normalized_nontrivial_le_B_inter_M_of_B_le_M
    hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3 hBM

end CFSG.GorensteinWalter
