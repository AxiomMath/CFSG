module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Basic.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreInvertedFitting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCyclicTwoCoreInfra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreTheoremCData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreCB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBLeMSource
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreUInterM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreP0Card
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerLayerEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreASevenNormalizerControl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicOrderThreeAutomorphism
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic first case: the five Theorem-C A₇-model inputs

This module lands the five inputs of
`firstCase_cyclicTwoCore_impossible_of_a7model` in the cyclic first-case
A₇ layer model:

1. `B₁ ∩ K₂ = O₃(U)`: `K₂ = I₂ = F(U)` (Step D.1), and
   `B₁ ∩ F(U) = C_{F(U)}(t₁) = O₃(U)` (Step D.3);
2. `K = O₃′(F(U))`: `K = K₁ ∩ K₂ = I₁ ∩ I₂` with `I₁ = O₃′(F(U))`
   (Step D.2) and `I₂ = F(U)`;
3. `O₃(U) ≤ C_G(B)`: `O₃(U) = P₀ ≤ M`, and the third clause of
   `U ∩ M = P₀ × (B ∩ M)` gives `⁅P₀, B⁆ = ⊥`;
4. `K ≠ ⊥`: if `K = ⊥`, then `F(U) = O₃(U) = P₀` has order 3, so
   Fact 1.2 gives `C_U(F(U)) = C_U(P₀) ≤ F(U) = P₀`; since
   `U/C_U(P₀)` embeds into `Aut(P₀)` of order 2 and `U` is odd,
   `U = P₀`, hence `B ≤ F(U)`, contradicting `B ∩ F(U) = ⊥` and
   `B ≠ ⊥`;
5. the fixed-point-free action of `B ∖ {1}` on `K`: a fixed point
   `k` lies in `C_G(b) ≤ N_G(⟨b⟩) ≤ M` (the landed normalizer control),
   hence in `U ∩ M = P₀ × B`; the `P₀`-part is a 3-element while
   `k ∈ O₃′(F(U))`, so `k ∈ B ∩ F(U) = ⊥`.

The statement of the fifth input is corrected to quantify `b ≠ 1` (the
un-restricted form is false at `b = 1`); this matches the Frobenius
hypothesis in `BenderGlauberman.IsFrobeniusGroupWithKernel`, where the
complement element is already required to lie outside the kernel.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Intersecting an ambient centralizer with a subgroup of the ambient
group gives the centralizer inside that subgroup. -/
private theorem centralizerIn_ambient_inter_eq
    {G : Type u} [Group G]
    (X Y : Subgroup G) (s : G) (hYX : Y ≤ X) :
    centralizerIn X s ⊓ Y = centralizerIn Y s := by
  apply le_antisymm
  · intro x hx
    have hxY : x ∈ Y := (Subgroup.mem_inf.mp hx).2
    have hxC : x ∈ Subgroup.centralizer ({s} : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
    exact Subgroup.mem_inf.mpr ⟨hxY, hxC⟩
  · intro x hx
    have hxY : x ∈ Y := (Subgroup.mem_inf.mp hx).1
    have hxC : x ∈ Subgroup.centralizer ({s} : Set G) :=
      (Subgroup.mem_inf.mp hx).2
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨hYX hxY, hxC⟩, hxY⟩

/-- Membership in the join `A ⊔ B` with `A` normal in `U` splits as a
product `a * b` with `a ∈ A` and `b ∈ B`. -/
private theorem mem_sup_product_of_normal_left
    {G : Type u} [Group G]
    (U A B : Subgroup G)
    (hAU : A ≤ U) (hBU : B ≤ U) (hAnorm : IsNormalIn A U)
    {x : G} (hxU : x ∈ U) (hx : x ∈ A ⊔ B) :
    ∃ a : G, a ∈ A ∧ ∃ b : G, b ∈ B ∧ a * b = x := by
  classical
  let xU : U := ⟨x, hxU⟩
  have hxSub : xU ∈ (A ⊔ B).subgroupOf U :=
    Subgroup.mem_subgroupOf.mpr hx
  have hEq : (A ⊔ B).subgroupOf U = A.subgroupOf U ⊔ B.subgroupOf U :=
    Subgroup.subgroupOf_sup hAU hBU
  have hxSup : xU ∈ A.subgroupOf U ⊔ B.subgroupOf U := by
    simpa [hEq] using hxSub
  have : (A.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff hAU).2
      (fun a b ha hb => hAnorm.2 b hb a ha)
  rcases (Subgroup.mem_sup_of_normal_left.mp hxSup) with
    ⟨a0, ha0, b0, hb0, hprod⟩
  refine ⟨(a0 : G), Subgroup.mem_subgroupOf.mp ha0, (b0 : G),
    Subgroup.mem_subgroupOf.mp hb0, ?_⟩
  exact congrArg Subtype.val hprod

/-- If `U ⊓ C_G(P) = P` and `P` has order `3`, then the index of `P` in
`U` is at most `2`: the conjugation action of `U` on `P` has kernel
`C_U(P) = P` and lands in `Aut(P)` of order `2`. -/
private theorem index_le_two_of_normal_centralizer_card_three
    {G : Type u} [Group G] [Finite G]
    (U P : Subgroup G) [hPN : (P.subgroupOf U).Normal]
    (hPU : P ≤ U) (hPcard : Nat.card (↥P) = 3)
    (hC : U ⊓ Subgroup.centralizer (P : Set G) = P) :
    (P.subgroupOf U).index ≤ 2 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P' : Subgroup U := P.subgroupOf U
  let φ : U →* MulAut P' := MulAut.conjNormal (G := U) (H := P')
  let C : Subgroup U := φ.ker
  have hCeq : C = P' := by
    apply SetLike.ext
    intro u
    constructor
    · intro hu
      rw [MonoidHom.mem_ker] at hu
      have hucent : (u : G) ∈ Subgroup.centralizer (P : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro p hp
        let pU : U := ⟨p, hPU hp⟩
        have hpP' : pU ∈ P' := Subgroup.mem_subgroupOf.mpr hp
        have hEq : (u : U) * (⟨pU, hpP'⟩ : P') * (u : U)⁻¹ =
            (⟨pU, hpP'⟩ : P') := by
          have hφx : (φ u) (⟨pU, hpP'⟩ : P') =
              (1 : MulAut P') (⟨pU, hpP'⟩ : P') :=
            congrArg (fun f : MulAut P' => f (⟨pU, hpP'⟩ : P')) hu
          simpa [φ, MulAut.conjNormal_apply] using congrArg Subtype.val hφx
        have hG : (p : G) * (u : G) = (u : G) * (p : G) :=
          (mul_inv_eq_iff_eq_mul.mp
            (by simpa [mul_assoc] using congrArg Subtype.val hEq)).symm
        exact hG
      rw [Subgroup.mem_subgroupOf]
      rw [← hC]
      exact Subgroup.mem_inf.mpr ⟨u.2, hucent⟩
    · intro hu
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      have huP : (u : G) ∈ P := Subgroup.mem_subgroupOf.mp hu
      have hucent : (u : G) ∈ Subgroup.centralizer (P : Set G) := by
        have hmem : (u : G) ∈ U ⊓ Subgroup.centralizer (P : Set G) := by
          rw [hC]
          exact huP
        exact (Subgroup.mem_inf.mp hmem).2
      have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp x.2
      have hcomm : (x : G) * (u : G) = (u : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hucent) (x : G) hxP
      have hfix : (u : G) * (x : G) * (u : G)⁻¹ = (x : G) :=
        mul_inv_eq_iff_eq_mul.mpr hcomm.symm
      simp [φ, MulAut.conjNormal_apply]
      apply Subtype.ext
      exact hfix
  have hP'card : Nat.card (↥P') = 3 := by
    simpa [P'] using
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := P) (K := U) hPU).toEquiv).trans
        (by simpa using hPcard)
  have hcardAut : Nat.card (MulAut P') = 2 := by
    have : IsCyclic P' := isCyclic_of_prime_card hP'card
    rw [IsCyclic.card_mulAut, hP'card]
    decide
  have hrange_le : Nat.card φ.range ≤ 2 := by
    have hcard_le := Subgroup.card_le_of_le (le_top : φ.range ≤ ⊤)
    have htop : Nat.card (↥(⊤ : Subgroup (MulAut P'))) = Nat.card (MulAut P') :=
      Subgroup.card_top
    exact (hcard_le.trans_eq htop).trans_eq hcardAut
  have hquot : Nat.card (U ⧸ C) = Nat.card φ.range := by
    simpa [C] using
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv)
  have hquot_le2 : Nat.card (U ⧸ C) ≤ 2 := by
    simpa [hquot] using hrange_le
  rw [Subgroup.index_eq_card]
  simpa [P', hCeq] using hquot_le2

/-- The five Theorem-C A₇-model inputs
`firstCase_cyclic_a7_theoremC_data`, derived from the inversion
corollaries of Step D, the `U ∩ M = P₀ × (B ∩ M)` decomposition, the
landed `P₀ ≤ M` / `B ≤ M` facts, and the A₇ normalizer control. -/
public theorem firstCase_cyclic_a7_theoremC_data_of_a7model
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c)
    (hcyclic : twoCoreOf c.Hhat ≤ c.S0)
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
    firstCase_cyclic_a7_theoremC_data hmin c od := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : BenderGlauberman.Hyp11KData od.d.bg := firstCaseBGKData hmin c od.d
  let U : Subgroup G := od.d.bg.U
  let P : Subgroup G := qCoreOf U od.p
  let Q3 : Subgroup G :=
    ((pPrimeCore 3 (fittingSubgroup U)).map (fittingSubgroup U).subtype).map
      U.subtype
  have hHhat : c.Hhat = c.H := cyclicCore_hhat_eq hmin c hcyclic
  have hUeq : c.U = od.d.bg.U := firstCase_U_eq_bg_U c od.d
  have hFUeq : c.FU = fittingSubgroupOf U := by
    change fittingSubgroupOf c.U = fittingSubgroupOf U
    rw [hUeq]
  have hFUleU : c.FU ≤ U := by
    change fittingSubgroupOf c.U ≤ U
    rw [hUeq]
    exact fittingSubgroupOf_le U
  have hUodd : Odd (Nat.card (↥U)) := by
    have hcop : Nat.Coprime 2 (Nat.card (↥U)) :=
      BenderGlauberman.U_coprime_two od.d.bg
    exact Nat.coprime_two_left.mp hcop
  have hPleM : P ≤ M := by
    simpa [P] using (firstCase_cyclic_primeCore_le_M_of_a7
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3)
  have hBleM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_source
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hPne0 : P ≠ ⊥ := by
    intro hbot
    apply od.primeCore_ne_bot
    rw [hUeq]
    simpa [P] using hbot
  have hP0eq : P ⊓ M = P := le_antisymm inf_le_left (le_inf le_rfl hPleM)
  have hBMeq : od.d.bg.B ⊓ M = od.d.bg.B :=
    le_antisymm inf_le_left (le_inf le_rfl hBleM)
  have hP0ne : P ⊓ M ≠ ⊥ := by
    intro hbot
    apply hPne0
    rw [← hP0eq]
    exact hbot
  have hP0card : Nat.card (↥(P ⊓ M)) = 3 :=
    firstCase_cyclic_P0_card_three_of_a7
      hmin c od M hMmax hSM fd hV2 hA7 hU hp3 hP0ne
  have hPcard : Nat.card (↥P) = 3 := by
    have h := congrArg (fun X : Subgroup G => Nat.card (↥X)) hP0eq
    simpa using h.symm.trans hP0card
  have hUint0 := firstCase_cyclic_U_inter_M_eq_P0_sup_B_inter_M_of_a7
    hmin c od M hMmax hSM fd hV2 hA7 hU hp3 hP0ne
  have hUint : U ⊓ M = P ⊔ od.d.bg.B := by
    calc
      U ⊓ M = (P ⊓ M) ⊔ (od.d.bg.B ⊓ M) := hUint0.1
      _ = P ⊔ od.d.bg.B := by rw [hP0eq, hBMeq]
  have hcommPB : ⁅P, od.d.bg.B⁆ = ⊥ := by
    calc
      ⁅P, od.d.bg.B⁆ = ⁅P ⊓ M, od.d.bg.B ⊓ M⁆ := by rw [hP0eq, hBMeq]
      _ = ⊥ := hUint0.2.2
  have hP3eq : P = qCoreOf U 3 := by
    simp [P, hp3]
  have hPinfQ3 : P ⊓ Q3 = ⊥ := by
    have hcopPQ : Nat.Coprime (Nat.card (↥P)) (Nat.card (↥Q3)) := by
      rw [hPcard]
      exact pPrimeCore_map_card_coprime U 3
    have hdisjPQ : Disjoint P Q3 := Subgroup.disjoint_of_coprime_natCard hcopPQ
    apply le_antisymm
    · exact disjoint_iff_inf_le.mp hdisjPQ
    · exact bot_le
  have hI2FU : od.d.I2 = c.FU :=
    firstCase_cyclic_I2_eq_FU_of_a7
      hmin c od hfirst hcyclic hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hK2eq : od.d.bg.K2 = od.d.I2 := by
    rfl
  have hB1FU : od.d.bg.B1 ⊓ c.FU = centralizerIn c.FU od.d.bg.t1 := by
    simpa [BenderGlauberman.Hyp11.B1] using
      (centralizerIn_ambient_inter_eq od.d.bg.U c.FU od.d.bg.t1 hFUleU)
  have hC3 : centralizerIn c.FU od.d.bg.t1 = qCoreOf U 3 :=
    firstCase_cyclic_centralizer_FU_t1_eq_threeCore_of_a7
      hmin c od hfirst hcyclic hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hAeq0 : od.d.bg.B1 ⊓ od.d.bg.K2 = qCoreOf U 3 := by
    calc
      od.d.bg.B1 ⊓ od.d.bg.K2 = od.d.bg.B1 ⊓ od.d.I2 := by
            rw [hK2eq]
      _ = od.d.bg.B1 ⊓ c.FU := by rw [hI2FU]
      _ = centralizerIn c.FU od.d.bg.t1 := hB1FU
      _ = qCoreOf U 3 := hC3
  have hI1eq : od.d.I1 = Q3 :=
    firstCase_cyclic_I1_eq_pPrimeCore_fittingSubgroupOf_of_a7
      hmin c od hfirst hcyclic hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hK1eq : od.d.bg.K1 = od.d.I1 := by
    rfl
  have hQ3leFU : Q3 ≤ c.FU := by
    simpa [hI1eq] using od.d.I1_hall.1
  have hKeq0 : od.d.bg.K = Q3 := by
    change od.d.bg.K1 ⊓ od.d.bg.K2 = Q3
    rw [hK1eq, hK2eq, hI1eq, hI2FU]
    apply le_antisymm
    · exact inf_le_left
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hx, hQ3leFU hx⟩
  have hPleCB : P ≤ Subgroup.centralizer (od.d.bg.B : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommPB
  have hPcentB0 : qCoreOf U 3 ≤ Subgroup.centralizer
      (od.d.bg.B : Set G) := by
    simpa [P, hp3] using hPleCB
  have hBinterFU : od.d.bg.B ⊓ c.FU = ⊥ :=
    firstCase_cyclic_B_inter_FU_eq_bot_of_a7
      hmin c od hfirst hcyclic hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hKne0 : @BenderGlauberman.Hyp11.K G _ _ od.d.bg
      (firstCaseBGKData hmin c od.d) ≠ ⊥ := by
    intro hK0
    have hQ3bot : Q3 = ⊥ := by
      rw [← hKeq0]
      exact hK0
    have hdecomp : fittingSubgroupOf U = qCoreOf U 3 ⊔ Q3 :=
      fittingSubgroupOf_eq_qCore_sup_pPrimeCore_map U 3
    have hFUeq_P : c.FU = P := by
      calc
        c.FU = fittingSubgroupOf U := hFUeq
        _ = qCoreOf U 3 ⊔ Q3 := hdecomp
        _ = qCoreOf U 3 ⊔ ⊥ := by rw [hQ3bot]
        _ = qCoreOf U 3 := by simp
        _ = P := hP3eq.symm
    have hCsolv : IsSolvable (↥U) := odd_order_theorem U hUodd
    have hCleF := fact_1_2_centralizer_fitting_le_fitting U hCsolv
    have hFU2 : fittingSubgroupOf U = P := hFUeq.symm.trans hFUeq_P
    have hCleP : U ⊓ Subgroup.centralizer (P : Set G) ≤ P := by
      simpa [hFU2] using hCleF
    have hPcentP : P ≤ Subgroup.centralizer (P : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative).mpr
        (firstCase_cyclic_primeCore_abelian c od)
    have hPleCU : P ≤ U ⊓ Subgroup.centralizer (P : Set G) := by
      intro x hx
      exact Subgroup.mem_inf.mpr ⟨qCoreOf_le U od.p hx, hPcentP hx⟩
    have hCU_eq_P : U ⊓ Subgroup.centralizer (P : Set G) = P :=
      le_antisymm hCleP hPleCU
    have : (P.subgroupOf U).Normal :=
      (Subgroup.normal_subgroupOf_iff (qCoreOf_le U od.p)).2
        (fun h k hh hk => (qCoreOf_normal_in U od.p).2 k hk h hh)
    have hindex_le2 := index_le_two_of_normal_centralizer_card_three
      U P (qCoreOf_le U od.p) hPcard hCU_eq_P
    have hindex_odd : Odd (P.subgroupOf U).index := by
      exact Odd.of_dvd_nat hUodd (P.subgroupOf U).index_dvd_card
    have hindex_ne0 : (P.subgroupOf U).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have hindex_lt2 : (P.subgroupOf U).index < 2 := by
      by_contra hnot
      have hge : 2 ≤ (P.subgroupOf U).index := Nat.le_of_not_gt hnot
      have heq2 : (P.subgroupOf U).index = 2 :=
        le_antisymm hindex_le2 hge
      exact hindex_odd.not_two_dvd_nat (by rw [heq2])
    have hindex_eq_one : (P.subgroupOf U).index = 1 := by
      have hpos : 0 < (P.subgroupOf U).index := Nat.pos_of_ne_zero hindex_ne0
      omega
    have hP'top : P.subgroupOf U = ⊤ := Subgroup.index_eq_one.mp hindex_eq_one
    have hUleP : U ≤ P := Subgroup.subgroupOf_eq_top.mp hP'top
    have hUeqP : U = P := le_antisymm hUleP (qCoreOf_le U od.p)
    have hBleFU : od.d.bg.B ≤ c.FU := by
      intro b hb
      rw [hFUeq_P]
      have hbU : b ∈ U := BenderGlauberman.theoremC_B_le_U od.d.bg hb
      simpa [hUeqP] using hbU
    have hBbot : od.d.bg.B = ⊥ := by
      calc
        od.d.bg.B = od.d.bg.B ⊓ c.FU :=
          (le_antisymm inf_le_left (le_inf le_rfl hBleFU)).symm
        _ = ⊥ := hBinterFU
    exact (firstCase_cyclic_B_ne_bot hmin c od hfirst hHhat hU Q) hBbot
  have hBfpf0 : ∀ b : G, b ∈ od.d.bg.B → b ≠ 1 → ∀ k : G,
      k ∈ Q3 → k ≠ 1 → b * k * b⁻¹ ≠ k := by
    intro b hbB hbne1 k hkQ hkne hfix
    have hkU : k ∈ U := hFUleU (hQ3leFU hkQ)
    have hkCb : k ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp
        (by simpa [mul_assoc] using hfix)).symm
    have hkCzp : k ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hkCb
    have hkN : k ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers b : Set G)) hkCzp
    have hXne : Subgroup.zpowers b ≠ ⊥ := by
      intro hbot
      apply hbne1
      have hbzp : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
      exact Subgroup.mem_bot.mp (by rwa [hbot] at hbzp)
    have hXle : Subgroup.zpowers b ≤ od.d.bg.B ⊓ M :=
      le_inf (Subgroup.zpowers_le.mpr hbB) (Subgroup.zpowers_le.mpr (hBleM hbB))
    have hEeq :
        componentLayerOf (Subgroup.normalizer (Subgroup.zpowers b : Set G)) =
          componentLayerOf M :=
      firstCase_cyclic_componentLayer_normalizer_eq_of_a7
        hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7
        (Subgroup.zpowers b) hXne hXle
    have hNleM : Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ M :=
      firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq
        hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7
        (Subgroup.zpowers b) hXne hXle hEeq
    have hkM : k ∈ M := hNleM hkN
    have hkUM : k ∈ U ⊓ M := Subgroup.mem_inf.mpr ⟨hkU, hkM⟩
    have hkPB : k ∈ P ⊔ od.d.bg.B := by
      simpa [hUint] using hkUM
    rcases mem_sup_product_of_normal_left U P od.d.bg.B
      (qCoreOf_le U od.p) (BenderGlauberman.theoremC_B_le_U od.d.bg)
      (qCoreOf_normal_in U od.p) hkU hkPB with ⟨p, hpP, b0, hb0B, hkpb⟩
    have hpF : p ∈ c.FU := by
      simpa [P, hFUeq] using
        (fstar_qCoreOf_le_fittingSubgroupOf U od.p od.p_prime hpP)
    have hkF : k ∈ c.FU := hQ3leFU hkQ
    have hb0_eq : b0 = p⁻¹ * k := by
      calc
        b0 = p⁻¹ * (p * b0) := by group
        _ = p⁻¹ * k := by rw [← hkpb]
    have hb0F : b0 ∈ c.FU := by
      rw [hb0_eq]
      exact c.FU.mul_mem (c.FU.inv_mem hpF) hkF
    have hb0BF : b0 ∈ od.d.bg.B ⊓ c.FU :=
      Subgroup.mem_inf.mpr ⟨hb0B, hb0F⟩
    have hb0bot : b0 ∈ (⊥ : Subgroup G) := by
      rw [hBinterFU] at hb0BF
      exact hb0BF
    have hb0_1 : b0 = 1 := Subgroup.mem_bot.mp hb0bot
    have hk_eq_p : k = p := by
      calc
        k = p * b0 := hkpb.symm
        _ = p * 1 := by rw [hb0_1]
        _ = p := by simp
    have hpQ3 : p ∈ Q3 := by
      simpa [hk_eq_p] using hkQ
    have hpPinfQ : p ∈ P ⊓ Q3 := Subgroup.mem_inf.mpr ⟨hpP, hpQ3⟩
    have hpbot : p ∈ (⊥ : Subgroup G) := by
      rw [hPinfQ3] at hpPinfQ
      exact hpPinfQ
    have hp1 : p = 1 := Subgroup.mem_bot.mp hpbot
    exact hkne (by simp [hk_eq_p, hp1])
  unfold firstCase_cyclic_a7_theoremC_data
  exact ⟨hAeq0, hKeq0, hPcentB0, hKne0, hBfpf0⟩

end CFSG.GorensteinWalter
