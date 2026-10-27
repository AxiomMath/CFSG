module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreP0Card
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerOddPart
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The cyclic first-case decomposition `U ∩ M = P₀ × (B ∩ M)`

Source equation (p. 223):

```
|P₀| = 3,   U ∩ M = P₀ × (B ∩ M).
```

The proof follows the quotient route.  Let `O = B ∩ M = O₂′(M)` and
`P₀ = P ∩ M`.  Since `t₂` inverts `P` and fixes `B`, `P₀ ∩ O = 1`.
The odd subgroup `P₀` lies in `E(M)`, which centralizes `O₂′(M)`, so the
two factors commute.  Modulo `O₂′(M)`, the image of `U ∩ M` is an
odd-order subgroup centralizing the involution `q(t)`; transporting it
to `A₇` and applying
`aSeven_odd_subgroup_centralizing_involution_card_le_three` bounds its
order by `3`.  The image of `P₀` has order exactly `3` by the P₀-card
endpoint, so the two images agree, and pulling the quotient equality back
gives `U ∩ M = P₀ ∨ O`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic A₇ layer model, `P₀ = P ∩ M` is disjoint from
`O = B ∩ M = O₂′(M)`: `t₂` inverts `P₀` and fixes `O`. -/
private theorem firstCase_cyclic_P0_inf_oddCore_eq_bot_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7))) :
    (qCoreOf od.d.bg.U od.p ⊓ M) ⊓
      ((pPrimeCore 2 M).map M.subtype) = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P0 : Subgroup G := P ⊓ M
  let O : Subgroup G := (pPrimeCore 2 M).map M.subtype
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := (qCoreOf_isPGroup od.d.bg.U od.p).exists_card_eq
    rw [hn]
    exact ((Fact.out : Nat.Prime od.p).odd_of_ne_two
      (firstCase_oriented_p_odd c od)).pow
  have hP0odd : Odd (Nat.card P0) :=
    Odd.of_dvd_nat hPodd (Subgroup.card_dvd_of_le inf_le_left)
  have hBleS : od.d.bg.B ≤ Subgroup.centralizer
      ((od.d.bg.S : Subgroup G) : Set G) := by
    rw [B_eq_centralizer_U od.d.bg]
    exact inf_le_right
  have hOleB : O ≤ od.d.bg.B :=
    firstCase_cyclic_oddCore_le_B_of_a7_layer
      hmin c od M hMmax hSM fd hV2 hA7
  have hOleS : O ≤ Subgroup.centralizer
      ((od.d.bg.S : Subgroup G) : Set G) :=
    hOleB.trans hBleS
  have hOleCt2 : O ≤ Subgroup.centralizer ({od.d.bg.t2} : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hOleS ho))
      od.d.bg.t2 od.d.bg.t2_mem_S).symm
  have hP0inv : ∀ x : G, x ∈ P0 →
      od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x⁻¹ := by
    intro x hx
    exact firstCase_t2_inverts_primeCore c od x (Subgroup.mem_inf.mp hx).1
  exact oddOrder_subgroup_inf_centralized_eq_bot
    P0 O od.d.bg.t2 hP0odd hOleCt2 hP0inv

/-- In the cyclic A₇ layer model, `P₀ = P ∩ M` lies in the component
layer `E(M)`: `[t₂, P₀] = P₀⁻²` lies in `E(M)` because `E(M) ◁ M` and
`t₂ ∈ E(M)`, and odd order makes `P₀` a power of `P₀⁻²`. -/
private theorem firstCase_cyclic_P0_le_componentLayer_of_a7
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M) :
    qCoreOf od.d.bg.U od.p ⊓ M ≤ componentLayerOf M := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P0 : Subgroup G := P ⊓ M
  let E : Subgroup G := componentLayerOf M
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := (qCoreOf_isPGroup od.d.bg.U od.p).exists_card_eq
    rw [hn]
    exact ((Fact.out : Nat.Prime od.p).odd_of_ne_two
      (firstCase_oriented_p_odd c od)).pow
  intro x hx
  have hxP : x ∈ P := (Subgroup.mem_inf.mp hx).1
  have hxM : x ∈ M := (Subgroup.mem_inf.mp hx).2
  have ht2E : od.d.bg.t2 ∈ E := hV2 fd.t2_mem_V2
  have hEnorm : IsNormalIn E M := fstar_componentLayerOf_isNormalIn M
  have hinner : x * od.d.bg.t2⁻¹ * x⁻¹ ∈ E :=
    hEnorm.2 x hxM (od.d.bg.t2⁻¹) (E.inv_mem ht2E)
  have hprod : od.d.bg.t2 * (x * od.d.bg.t2⁻¹ * x⁻¹) ∈ E :=
    E.mul_mem ht2E hinner
  have hinv : od.d.bg.t2 * x * od.d.bg.t2⁻¹ = x⁻¹ :=
    firstCase_t2_inverts_primeCore c od x hxP
  have hzE : (x⁻¹) ^ 2 ∈ E := by
    have hprod' : (od.d.bg.t2 * x * od.d.bg.t2⁻¹) * x⁻¹ ∈ E := by
      simpa [mul_assoc] using hprod
    have hz : (od.d.bg.t2 * x * od.d.bg.t2⁻¹) * x⁻¹ = (x⁻¹) ^ 2 := by
      rw [hinv]
      simp [pow_two]
    simpa [hz] using hprod'
  have hordOdd : Odd (orderOf x) := by
    have hdvd : orderOf x ∣ Nat.card P :=
      Subgroup.orderOf_dvd_natCard P hxP
    exact Odd.of_dvd_nat hPodd hdvd
  obtain ⟨k, hk⟩ := hordOdd
  have hxstep : x * x ^ (2 * k) = 1 := by
    have hstep : x ^ (2 * k + 1) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one x
    simpa [pow_succ'] using hstep
  have hxpow2 : x ^ (2 * k) = x⁻¹ := by
    calc
      x ^ (2 * k) = 1 * x ^ (2 * k) := by simp
      _ = (x⁻¹ * x) * x ^ (2 * k) := by rw [inv_mul_cancel]
      _ = x⁻¹ * (x * x ^ (2 * k)) := by group
      _ = x⁻¹ * 1 := by rw [hxstep]
      _ = x⁻¹ := by simp
  have hxEq : ((x⁻¹) ^ 2) ^ k = x := by
    calc
      ((x⁻¹) ^ 2) ^ k = (x⁻¹) ^ (2 * k) := by rw [← pow_mul]
      _ = (x ^ (2 * k))⁻¹ := by rw [inv_pow]
      _ = x := by rw [hxpow2]; simp
  have hxE : ((x⁻¹) ^ 2) ^ k ∈ E := E.pow_mem hzE k
  rw [hxEq] at hxE
  exact hxE

/-- In the cyclic A₇ layer model, `P₀` centralizes `O = O₂′(M)`, because
`P₀ ≤ E(M)` and `E(M)` centralizes the normalized solvable odd core. -/
private theorem firstCase_cyclic_P0_commutator_oddCore_eq_bot_of_a7
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M) :
    ⁅qCoreOf od.d.bg.U od.p ⊓ M,
      (pPrimeCore 2 M).map M.subtype⁆ = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P0 : Subgroup G := qCoreOf od.d.bg.U od.p ⊓ M
  let O : Subgroup G := (pPrimeCore 2 M).map M.subtype
  let E : Subgroup G := componentLayerOf M
  have hP0leE : P0 ≤ E :=
    firstCase_cyclic_P0_le_componentLayer_of_a7 c od M fd hV2
  have hOleM : O ≤ M :=
    Subgroup.map_subtype_le (H := M) (pPrimeCore 2 M)
  have hOodd : Odd (Nat.card O) := by
    have hcard : Nat.card O = Nat.card (pPrimeCore 2 M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [hcard]
    exact Nat.coprime_two_left.mp
      (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  have hOnorm : IsNormalIn O M := by
    refine ⟨hOleM, ?_⟩
    intro m hm o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨m, hm⟩ : M) * o0 * (⟨m, hm⟩ : M)⁻¹, ?_, rfl⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥M)).conj_mem
      o0 ho0 ⟨m, hm⟩
  have hE_norm_O : E ≤ Subgroup.normalizer (O : Set G) :=
    (componentLayerOf_isNormalIn M).1.trans (le_normalizer_of_isNormalIn hOnorm)
  have hcommEO : ⁅E, O⁆ = ⊥ :=
    componentLayerOf_centralizes_solvable_of_le_normalizer
      M O hOleM hOsolv hE_norm_O
  have hle : ⁅P0, O⁆ ≤ ⁅E, O⁆ :=
    Subgroup.commutator_mono hP0leE le_rfl
  exact le_antisymm (by simpa [hcommEO] using hle) bot_le

/-- The main source equation `U ∩ M = P₀ × (B ∩ M)` in the cyclic
first-case A₇ layer model. -/
public theorem firstCase_cyclic_U_inter_M_eq_P0_sup_B_inter_M_of_a7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (hp3 : od.p = 3)
    (hP0ne : qCoreOf od.d.bg.U od.p ⊓ M ≠ ⊥) :
    od.d.bg.U ⊓ M =
        (qCoreOf od.d.bg.U od.p ⊓ M) ⊔ (od.d.bg.B ⊓ M) ∧
      (qCoreOf od.d.bg.U od.p ⊓ M) ⊓ (od.d.bg.B ⊓ M) = ⊥ ∧
      ⁅qCoreOf od.d.bg.U od.p ⊓ M, od.d.bg.B ⊓ M⁆ = ⊥ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let P0 : Subgroup G := P ⊓ M
  let O0 : Subgroup M := pPrimeCore 2 M
  let O : Subgroup G := O0.map M.subtype
  let : O0.Normal := pPrimeCore_normal
  let Q : Type u := M ⧸ O0
  let : Group Q := QuotientGroup.Quotient.group O0
  let q : M →* Q := QuotientGroup.mk' O0
  let Y : Subgroup G := od.d.bg.U ⊓ M
  let Y0 : Subgroup M := Y.subgroupOf M
  let P0M : Subgroup M := P0.subgroupOf M
  let Ybar : Subgroup Q := Y0.map q
  let Pbar : Subgroup Q := P0M.map q
  let E : Subgroup G := componentLayerOf M
  let eM : Q ≃* alternatingGroup (Fin 7) :=
    (firstCase_cyclic_m_quotient_a7_of_layer_a7
      hmin M hMmax hA7).some
  let YA : Subgroup (alternatingGroup (Fin 7)) := Ybar.map eM.toMonoidHom

  have hBM : od.d.bg.B ⊓ M = O := by
    dsimp [O]
    exact firstCase_cyclic_B_inter_M_eq_oddCore_of_a7_layer
      hmin c od M hMmax hSM fd hV2 hA7 hU
  have hP0Obot : P0 ⊓ O = ⊥ := by
    dsimp [P0, O]
    exact firstCase_cyclic_P0_inf_oddCore_eq_bot_of_a7
      hmin c od M hMmax hSM fd hV2 hA7
  have hP0leE : P0 ≤ E := by
    dsimp [P0, E]
    exact firstCase_cyclic_P0_le_componentLayer_of_a7 c od M fd hV2
  have hcommP0O : ⁅P0, O⁆ = ⊥ := by
    dsimp [P0, O]
    exact firstCase_cyclic_P0_commutator_oddCore_eq_bot_of_a7
      c od M fd hV2

  have hUodd : Odd (Nat.card (↥od.d.bg.U)) := by
    have hcop : Nat.Coprime 2 (Nat.card (↥od.d.bg.U)) := by
      rw [show od.d.bg.U = c.U by
        change oddCoreOf od.d.bg.H = oddCoreOf c.H
        rw [od.d.H_eq]]
      change Nat.Coprime 2
        (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
      rw [Subgroup.card_map_of_injective c.H.subtype_injective]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    exact Nat.coprime_two_left.mp hcop
  have hYodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hY0odd : Odd (Nat.card Y0) := by
    have hcard : Nat.card Y0 = Nat.card Y := by
      simpa [Y0, Y] using (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := Y) (K := M) inf_le_right).toEquiv)
    rwa [hcard]
  have hYbarOdd : Odd (Nat.card Ybar) :=
    Odd.of_dvd_nat hY0odd (Subgroup.card_map_dvd Y0 q)

  have htM : c.t ∈ M := hSM (fd.V2_le_S fd.t_mem_V2)
  let tM : M := ⟨c.t, htM⟩
  let tQ : Q := q tM
  let tA : alternatingGroup (Fin 7) := eM tQ
  have hUleH : od.d.bg.U ≤ od.d.bg.H :=
    le_sup_left.trans (le_of_eq od.d.bg.H_eq_US)
  have hYcentT : Y0 ≤ Subgroup.centralizer ({tM} : Set M) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have hyU : (y : G) ∈ od.d.bg.U := (Subgroup.mem_inf.mp hyY).1
    have hyH : (y : G) ∈ od.d.bg.H := hUleH hyU
    have hyCentBg : (y : G) ∈
        Subgroup.centralizer ({od.d.bg.t} : Set G) := by
      simpa [od.d.bg.H_eq_centralizer] using hyH
    have hyCent : (y : G) ∈
        Subgroup.centralizer ({c.t} : Set G) := by
      simpa [od.d.t_eq] using hyCentBg
    have hcomm : (y : G) * c.t = c.t * (y : G) := by
      rwa [Subgroup.mem_centralizer_singleton_iff] at hyCent
    apply Subtype.ext
    exact hcomm
  have hYbarCent : Ybar ≤ Subgroup.centralizer ({tQ} : Set Q) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hy with ⟨y0, hyY0, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_singleton_iff.mp
      (hYcentT hyY0))
    simpa [tQ] using congrArg q hcomm
  have htM_ne_one : tM ≠ 1 := by
    intro htM1
    exact c.t_involution.1 (congrArg Subtype.val htM1)
  have htM_sq : tM ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using c.t_involution.2
  have hO0odd : Odd (Nat.card O0) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have htQ : IsInvolution tQ := by
    constructor
    · intro htQ1
      have htM_O : tM ∈ O0 :=
        (QuotientGroup.eq_one_iff (N := O0) tM).mp htQ1
      have hdvd2 : 2 ∣ Nat.card O0 := by
        have hdvd : orderOf tM ∣ Nat.card O0 :=
          Subgroup.orderOf_dvd_natCard O0 htM_O
        have hord2 : orderOf tM = 2 := by
          apply orderOf_eq_prime
          · exact htM_sq
          · exact htM_ne_one
        rwa [hord2] at hdvd
      exact hO0odd.not_two_dvd_nat hdvd2
    · rw [← map_pow q tM 2, ← map_one q]
      exact congrArg q htM_sq
  have htA : IsInvolution tA := by
    constructor
    · intro htA1
      apply htQ.1
      apply eM.injective
      simpa [tA] using htA1
    · have h := congrArg eM htQ.2
      simpa [tA, pow_two] using h
  have hYACent : YA ≤ Subgroup.centralizer
      ({tA} : Set (alternatingGroup (Fin 7))) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hy with ⟨yb, hyb, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_singleton_iff.mp
      (hYbarCent hyb))
    simpa [tA] using congrArg eM hcomm
  have hYAodd : Odd (Nat.card YA) := by
    have hcard : Nat.card YA = Nat.card Ybar := by
      dsimp [YA]
      exact Subgroup.card_map_of_injective
        (K := Ybar) (f := eM.toMonoidHom) eM.injective
    rwa [hcard]
  have hYAle3 : Nat.card YA ≤ 3 :=
    aSeven_odd_subgroup_centralizing_involution_card_le_three
      (P := YA) hYAodd (t := tA) htA hYACent
  have hYbarLe3 : Nat.card Ybar ≤ 3 := by
    have hcard : Nat.card YA = Nat.card Ybar := by
      dsimp [YA]
      exact Subgroup.card_map_of_injective
        (K := Ybar) (f := eM.toMonoidHom) eM.injective
    rw [← hcard]
    exact hYAle3

  have hP0card : Nat.card P0 = 3 := by
    dsimp [P0]
    exact firstCase_cyclic_P0_card_three_of_a7
      hmin c od M hMmax hSM fd hV2 hA7 hU hp3 hP0ne
  have hP0Mcard : Nat.card P0M = Nat.card P0 := by
    dsimp [P0M, P0]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := P0) (K := M) inf_le_right).toEquiv
  have hP0M_O0_bot : P0M ⊓ O0 = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    rw [Subgroup.mem_bot]
    have hxP0M : x ∈ P0M := (Subgroup.mem_inf.mp hx).1
    have hxO0 : x ∈ O0 := (Subgroup.mem_inf.mp hx).2
    have hxP0 : (x : G) ∈ P0 := Subgroup.mem_subgroupOf.mp hxP0M
    have hxO : (x : G) ∈ O := Subgroup.mem_map.mpr ⟨x, hxO0, rfl⟩
    have hxinf : (x : G) ∈ P0 ⊓ O := Subgroup.mem_inf.mpr ⟨hxP0, hxO⟩
    have hxbotG : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [hP0Obot] at hxinf
      exact hxinf
    have hx1G : (x : G) = 1 := Subgroup.mem_bot.mp hxbotG
    apply Subtype.ext
    exact hx1G
  have hker : q.ker = O0 := QuotientGroup.ker_mk' O0
  have hP0Mker : P0M ⊓ q.ker = ⊥ := by
    simpa [hker] using hP0M_O0_bot
  have hP0Qcard : Nat.card P0M = Nat.card Pbar := by
    have h := card_map_eq_card_mul_card_ker q P0M
    rw [hP0Mker] at h
    simpa [Pbar, Nat.mul_one] using h
  have hPbarCard3 : Nat.card Pbar = 3 := by
    calc
      Nat.card Pbar = Nat.card P0M := hP0Qcard.symm
      _ = Nat.card P0 := hP0Mcard
      _ = 3 := hP0card

  have hP0M_le_Y0 : P0M ≤ Y0 := by
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    have hxP0 : (x : G) ∈ P0 := Subgroup.mem_subgroupOf.mp hx
    have hxP : (x : G) ∈ P := (Subgroup.mem_inf.mp hxP0).1
    have hxM : (x : G) ∈ M := (Subgroup.mem_inf.mp hxP0).2
    exact Subgroup.mem_inf.mpr ⟨(qCoreOf_le od.d.bg.U od.p) hxP, hxM⟩
  have hPbar_le_Ybar : Pbar ≤ Ybar := by
    exact Subgroup.map_mono (f := q) hP0M_le_Y0
  have hYbar_eq_Pbar : Ybar = Pbar := by
    exact (Subgroup.eq_of_le_of_card_ge hPbar_le_Ybar
      (by omega)).symm
  have hY0_le_sup : Y0 ≤ O0 ⊔ P0M := by
    intro y hy
    have hyQ : q y ∈ Pbar := by
      rw [← hYbar_eq_Pbar]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hyQ with ⟨p, hp, hqp⟩
    have ho : y * p⁻¹ ∈ O0 := by
      rw [← hker]
      rw [MonoidHom.mem_ker]
      calc
        q (y * p⁻¹) = q y * (q p)⁻¹ := by rw [map_mul, map_inv]
        _ = q p * (q p)⁻¹ := by rw [hqp]
        _ = 1 := by simp
    exact (Subgroup.mem_sup_of_normal_left
      (s := O0) (t := P0M) (x := y)).mpr
      ⟨y * p⁻¹, ho, p, hp, by group⟩
  have hO0_le_Y0 : O0 ≤ Y0 := by
    intro o ho
    apply Subgroup.mem_subgroupOf.mpr
    have hoO : (o : G) ∈ O := Subgroup.mem_map.mpr ⟨o, ho, rfl⟩
    have hoBM : (o : G) ∈ od.d.bg.B ⊓ M := by
      rw [hBM]
      exact hoO
    have hoB : (o : G) ∈ od.d.bg.B := (Subgroup.mem_inf.mp hoBM).1
    have hoU : (o : G) ∈ od.d.bg.U :=
      BenderGlauberman.mem_U_of_mem_B_s4 od.d.bg hoB
    have hoM : (o : G) ∈ M := (Subgroup.mem_inf.mp hoBM).2
    exact Subgroup.mem_inf.mpr ⟨hoU, hoM⟩
  have hsup_le_Y0 : O0 ⊔ P0M ≤ Y0 := sup_le hO0_le_Y0 hP0M_le_Y0
  have hY0_eq_sup : Y0 = O0 ⊔ P0M :=
    le_antisymm hY0_le_sup hsup_le_Y0
  have hmapY : Y0.map M.subtype = Y := by
    dsimp [Y0, Y]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hmapSup : (O0 ⊔ P0M).map M.subtype = O ⊔ P0 := by
    have hOmap : O0.map M.subtype = O := rfl
    have hP0Mmap : P0M.map M.subtype = P0 := by
      dsimp [P0M, P0]
      exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
    rw [Subgroup.map_sup, hOmap, hP0Mmap]
  have hY_eq : Y = P0 ⊔ O := by
    calc
      Y = Y0.map M.subtype := hmapY.symm
      _ = (O0 ⊔ P0M).map M.subtype := by rw [hY0_eq_sup]
      _ = O ⊔ P0 := hmapSup
      _ = P0 ⊔ O := by rw [sup_comm]
  refine ⟨?_, ?_, ?_⟩
  · simpa [Y, P0, O, hBM] using hY_eq
  · simpa [P0, O, hBM] using hP0Obot
  · simpa [P0, O, hBM] using hcommP0O

end CFSG.GorensteinWalter
