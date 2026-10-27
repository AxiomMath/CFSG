module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingFixedNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingNormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingCyclicCardLe
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseConjugator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerConjugate
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePInfPg
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoSubgroupCentralizingULeTwoCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the equations-(5)--(7) package after equation (4)

The source (`refs/bender-dihedral-sylow.tex`, L672–735) obtains, from the
equation-(3) decomposition and the equation-(4) component-centralization
fact `F ≤ C_G(E)`, the nontriviality, self-normalization, trivial
intersections, and cyclicity of the fixed part `F`:

* (5): `1 ≠ F = C_{F(U)∩M}(s)` and `N_G(F) = M`;
* (6): `F ∩ F^g = 1` for every `g ∉ M`, and `F` is isomorphic to a
  subgroup of the cyclic inverted part `K0`, hence cyclic;
* (7): `O_2(H ∩ M) = O_2(Ĥ)`.

The theorem below packages these facts PSL₂-independently.  Two inputs are
supplied:

* `hFcentE : F ≤ C_G(d.E)` — the legitimate equation-(4) component
  centralization fact (Fact 1.10(ii)); in the A₇ branch this is supplied by
  `secondCase_a7_fitting_centralizes_component_of_reflection`, and the
  PSL₂ branch supplies its semilinear analogue;
* `hLayer : componentLayerOf (N_G(X)) = d.E` for every nontrivial
  `X ≤ F` — the normalizer-layer control used by the source's
  `E = E(N_G(X))` step (L682–687).  In the A₇ branch this is
  `secondCase_a7_normalizer_layer_eq_component`; the PSL₂ analogue is the
  first genuinely missing post-equation-(4) theorem for the linear branch.

Given those two inputs, everything downstream — normality of `F` in `M`,
nontriviality, self-normalization, trivial intersections with outside
conjugates, cyclicity, the cardinal bound `|F| ≤ |K0|`, nontriviality of
`K0`, and the equation-(7) two-core identity — is derived here without any
A₇/PSL₂ model.  These are exactly the facts that unlock choosing the prime
`p` and the rank-two subgroup `A` of the source's parameter package.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The equation-(3) fixed part is normal in the maximal subgroup once
equation (4) supplies its component centralization.  This is the
model-independent half of the source's equation (4): `F` centralizes `E`,
and `F ≤ C_M(t)` is normalized there, so the factorization
`M = E·C_M(t)` makes `F` normal in `M`. -/
private theorem fitting_fixed_normal_in_M_of_component_centralization
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F : Subgroup G)
    (hFleFU : F ≤ fittingSubgroupOf c.U)
    (hFleM : F ≤ w.M)
    (s : d.E)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G)) :
    IsNormalIn F w.M := by
  have hUleH : c.U ≤ c.H := Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hFleC : F ≤ Subgroup.centralizer ({c.t} : Set G) ⊓ w.M := by
    intro f hf
    have hfH : f ∈ c.H := hUleH (fittingSubgroupOf_le c.U (hFleFU hf))
    rw [c.H_eq_centralizer] at hfH
    exact ⟨hfH, hFleM hf⟩
  have hFnormalC : IsNormalIn F
      (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M) := by
    refine ⟨hFleC, ?_⟩
    intro z hz f hf
    have hzH : z ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact hz.1
    have hzM : z ∈ w.M := hz.2
    have hfFU : f ∈ fittingSubgroupOf c.U := hFleFU hf
    have hfM : f ∈ w.M := hFleM hf
    have hconjFU : z * f * z⁻¹ ∈ fittingSubgroupOf c.U :=
      (centralizerSetup_FU_isNormalIn_H c).2 z hzH f hfFU
    have hconjM : z * f * z⁻¹ ∈ w.M :=
      w.M.mul_mem (w.M.mul_mem hzM hfM) (w.M.inv_mem hzM)
    have hconjY : z * f * z⁻¹ ∈ fittingSubgroupOf c.U ⊓ w.M :=
      ⟨hconjFU, hconjM⟩
    have hconjCentE : z * f * z⁻¹ ∈
        Subgroup.centralizer (d.E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : z⁻¹ * e * z ∈ d.E :=
        by simpa using d.E_normal.2 z⁻¹ (w.M.inv_mem hzM) e he
      have hfe : f * (z⁻¹ * e * z) = (z⁻¹ * e * z) * f :=
        (Subgroup.mem_centralizer_iff.mp (hFcentE hf))
          (z⁻¹ * e * z) he' |>.symm
      calc
        e * (z * f * z⁻¹) = z * ((z⁻¹ * e * z) * f) * z⁻¹ := by group
        _ = z * (f * (z⁻¹ * e * z)) * z⁻¹ := by rw [hfe]
        _ = (z * f * z⁻¹) * e := by group
    have hconjS : z * f * z⁻¹ ∈
        Subgroup.centralizer ({(s : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hconjCentE) (s : G) s.2).symm
    rw [hF_eq]
    exact Subgroup.mem_inf.mpr ⟨hconjY, hconjS⟩
  exact secondCase_fitting_normal_in_M_of_centralizes_component
    c w d F hFleC hFnormalC hFcentE

/-- The equation-(4) fixed part has trivial intersection with each conjugate
by an element outside the second-case maximal subgroup.  The normalizer-layer
control `hLayer` (the source's `E = E(N_G(X))` step) is supplied explicitly;
everything else is model-independent. -/
private theorem fitting_fixed_TI_of_normalizer_layer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F : Subgroup G)
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E)
    (g : G) (hg : g ∉ w.M) :
    F ⊓ conjugateSubgroup F g = ⊥ := by
  classical
  let X : Subgroup G := F ⊓ conjugateSubgroup F g
  by_contra hXbot
  have hXne : X ≠ ⊥ := by simpa [X] using hXbot
  have hXleF : X ≤ F := inf_le_left
  let Y : Subgroup G := conjugateSubgroup X g⁻¹
  have hYmap : conjugateSubgroup Y g = X := by
    simpa [Y] using conj_inv_then_conj_eq X g
  have hYleF : Y ≤ F := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxConj : x ∈ conjugateSubgroup F g :=
      (inf_le_right : X ≤ conjugateSubgroup F g) hx
    rcases Subgroup.mem_map.mp hxConj with ⟨f, hf, hxf⟩
    have hxf' : x = g * f * g⁻¹ := by
      simpa [conjugateSubgroup, MulAut.conj_apply] using hxf.symm
    have heq : (MulAut.conj g⁻¹).toMonoidHom x = f := by
      rw [hxf']
      simp
      group
    rw [heq]
    exact hf
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    apply hXne
    rw [← hYmap]
    simp [conjugateSubgroup, hYbot]
  have hLayerX : componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E :=
    hLayer X hXne hXleF
  have hLayerY : componentLayerOf (Subgroup.normalizer (Y : Set G)) = d.E :=
    hLayer Y hYne hYleF
  have hmapN : conjugateSubgroup (Subgroup.normalizer (Y : Set G)) g =
      Subgroup.normalizer (X : Set G) := by
    have hYmap' : Y.map (MulAut.conj g).toMonoidHom = X := by
      simpa [conjugateSubgroup] using hYmap
    change (Subgroup.normalizer (Y : Set G)).map
        (MulAut.conj g).toMonoidHom = _
    rw [Subgroup.map_normalizer_eq_of_bijective Y (MulAut.conj g).bijective]
    rw [hYmap']
  have hEg : conjugateSubgroup d.E g = d.E := by
    calc
      conjugateSubgroup d.E g =
          conjugateSubgroup
            (componentLayerOf (Subgroup.normalizer (Y : Set G))) g := by
        rw [hLayerY]
      _ = componentLayerOf
          (conjugateSubgroup (Subgroup.normalizer (Y : Set G)) g) := by
        simpa [conjugateSubgroup] using
          (componentLayerOf_conjugateSubgroup
            (Subgroup.normalizer (Y : Set G)) g).symm
      _ = componentLayerOf (Subgroup.normalizer (X : Set G)) := by rw [hmapN]
      _ = d.E := hLayerX
  have hgNE : g ∈ Subgroup.normalizer (d.E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxmap : g * x * g⁻¹ ∈ conjugateSubgroup d.E g :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [hEg] at hxmap
    · intro hxconj
      have hxconjMap : g * x * g⁻¹ ∈ conjugateSubgroup d.E g := by
        rwa [hEg]
      rcases Subgroup.mem_map.mp hxconjMap with ⟨y, hy, hyx⟩
      have hyxeq : y = x := by
        apply (MulAut.conj g).injective
        simpa [MulAut.conj_apply] using hyx
      rwa [← hyxeq]
  have hEnormalSub : (d.E.subgroupOf w.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff d.E_component.1]
    intro e m he hm
    exact d.E_normal.2 m hm e he
  have hNE : Subgroup.normalizer (d.E : Set G) = w.M :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) w.M_maximal d.E_component.1
        ((Subgroup.nontrivial_iff_ne_bot d.E).mp d.E_component.2.2.1)
        hEnormalSub
  exact hg (by rwa [← hNE])

/-- The equation-(6) cardinal transfer: with the outside normalizer
conjugator and the normalizer-layer trivial intersections, the generic
`secondCase_fitting_fixed_part_cyclic_and_card_le_of_conjugate_disjoint`
supplies cyclicity of `F` and the bound `|F| ≤ |K0|`. -/
private theorem fitting_fixed_cyclic_and_card_le_of_normalizer_layer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K0 F : Subgroup G)
    (hK0cyc : IsCyclic K0)
    (hFleFU : F ≤ fittingSubgroupOf c.U)
    (hFnormalM : IsNormalIn F w.M)
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M)
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E) :
    IsCyclic F ∧ Nat.card F ≤ Nat.card K0 := by
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
  obtain ⟨g, hgY, hgnotM⟩ := secondCase_exists_conjugator_not_mem_M hmin c w
  have hFleM : F ≤ w.M := hFnormalM.1
  have hFleY : F ≤ Y := by
    intro f hf
    exact ⟨hFleFU hf, hFleM hf⟩
  have hFnormalY : IsNormalIn F Y := by
    refine ⟨hFleY, ?_⟩
    intro y hy f hf
    exact hFnormalM.2 y hy.2 f hf
  have hdisj : F ⊓ conjugateSubgroup F g = ⊥ :=
    fitting_fixed_TI_of_normalizer_layer hmin c w d F hLayer g hgnotM
  exact secondCase_fitting_fixed_part_cyclic_and_card_le_of_conjugate_disjoint
    K0 F Y hK0cyc hFnormalY (by simpa [Y] using hjoin) g
      (by simpa [Y] using hgY) hdisj

/-- Equation (7), first half: `O2(H ∩ M)` centralizes `F(U)`.  The normal
subgroups `P = O2(H ∩ M)` and `Y = F(U) ∩ M` have coprime orders, so `P`
centralizes `Y`; the fixed subgroup of the resulting coprime action on
`F(U)` is self-centralizing: anything centralizing it centralizes the
equation-(6) subgroup `F`, hence lies in `N_G(F) = M` and therefore in
`Y`.  Proposition 1.10 then makes the action on all of `F(U)` trivial. -/
private theorem fitting_twoCore_inter_centralizes_fitting
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (K0 F : Subgroup G)
    (hFnormalM : IsNormalIn F w.M)
    (hFne : F ≠ ⊥)
    (hjoinY : K0 ⊔ F = c.FU ⊓ w.M) :
    twoCoreOf (c.H ⊓ w.M) ≤ Subgroup.centralizer (c.FU : Set G) := by
  classical
  let C : Subgroup G := c.H ⊓ w.M
  let P : Subgroup G := twoCoreOf C
  let Y : Subgroup G := c.FU ⊓ w.M
  have hUleH : c.U ≤ c.H := Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hUnormalH : IsNormalIn c.U c.H := by
    refine ⟨hUleH, ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
        pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        p hp (⟨h, hh⟩ : c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  have hFUnormalH : IsNormalIn c.FU c.H := centralizerSetup_FU_isNormalIn_H c
  have hYleC : Y ≤ C := by
    intro y hy
    exact ⟨hUleH (fittingSubgroupOf_le c.U hy.1), hy.2⟩
  have hYnormalC : IsNormalIn Y C := by
    refine ⟨hYleC, ?_⟩
    intro z hz y hy
    refine ⟨hFUnormalH.2 z hz.1 y hy.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hz.2 hy.2) (w.M.inv_mem hz.2)
  have hPleC : P ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xC, hxC, rfl⟩
    exact xC.2
  have hPnormalC : IsNormalIn P C := by
    refine ⟨hPleC, ?_⟩
    intro z hz x hx
    rcases Subgroup.mem_map.mp hx with ⟨xC, hxP, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨z, hz⟩ : C) * xC * (⟨z, hz⟩ : C)⁻¹, ?_, by simp⟩
    exact (pCore_normal (p := 2) (G := C)).conj_mem
      xC hxP (⟨z, hz⟩ : C)
  have hPp : IsPGroup 2 P := by
    change IsPGroup 2 ((pCore 2 C).map C.subtype)
    exact (pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hYleU : Y ≤ c.U := by
    intro y hy
    exact fittingSubgroupOf_le c.U hy.1
  have hYodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hYleU)
  have hPYcop : Nat.Coprime (Nat.card P) (Nat.card Y) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hYodd.coprime_two_left.pow_left n
  let PC : Subgroup C := P.subgroupOf C
  let YC : Subgroup C := Y.subgroupOf C
  have hPCnormal : PC.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPleC]
    intro p z hp hz
    exact hPnormalC.2 z hz p hp
  have hYCnormal : YC.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hYleC]
    intro y z hy hz
    exact hYnormalC.2 z hz y hy
  let : PC.Normal := hPCnormal
  let : YC.Normal := hYCnormal
  have hPCcard : Nat.card PC = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleC).toEquiv
  have hYCcard : Nat.card YC = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleC).toEquiv
  have hPCYCcop : Nat.Coprime (Nat.card PC) (Nat.card YC) := by
    simpa [hPCcard, hYCcard] using hPYcop
  have hPCYCdisj : Disjoint PC YC :=
    Subgroup.disjoint_of_coprime_natCard hPCYCcop
  have hcommbot : ⁅PC, YC⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_le_inf PC YC).trans
      (by rw [hPCYCdisj.eq_bot])
  have hPcentY : P ≤ Subgroup.centralizer (Y : Set G) := by
    have hPCcentYC : PC ≤ Subgroup.centralizer (YC : Set C) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommbot
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let pC : C := ⟨p, hPleC hp⟩
    let yC : C := ⟨y, hYleC hy⟩
    have hpPC : pC ∈ PC := Subgroup.mem_subgroupOf.mpr hp
    have hyYC : yC ∈ YC := Subgroup.mem_subgroupOf.mpr hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hPCcentYC hpPC)) yC hyYC
    exact congrArg Subtype.val hcomm
  have hNFeq : Subgroup.normalizer (F : Set G) = w.M :=
    secondCase_normalizer_fitting_fixed_eq_M hmin c w F hFne hFnormalM
  have hPnormFU : P ≤ Subgroup.normalizer (c.FU : Set G) :=
    hPleC.trans (inf_le_left.trans (le_normalizer_of_isNormalIn hFUnormalH))
  let : P.Normalizes c.FU := ⟨hPnormFU⟩
  let : MulDistribMulAction P c.FU :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P c.FU hPnormFU
  have hfixEq : fixedPointSubgroup P c.FU =
      (subgroupCentralizerIn c.FU P).subgroupOf c.FU :=
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
      c.FU P hPnormFU
  have hFleY : F ≤ Y := by
    intro f hf
    change f ∈ c.FU ⊓ w.M
    rw [← hjoinY]
    exact (le_sup_right : F ≤ K0 ⊔ F) hf
  have hYcentP : Y ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.le_centralizer_iff.mp hPcentY
  have hcentralizerFix :
      Subgroup.centralizer (fixedPointSubgroup P c.FU : Set c.FU) ≤
        fixedPointSubgroup P c.FU := by
    rw [hfixEq]
    intro x hx
    have hxCentF : (x : G) ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      let fFU : c.FU := ⟨f, hFleY hf |>.1⟩
      have hfC : f ∈ subgroupCentralizerIn c.FU P :=
        ⟨hFleY hf |>.1, hYcentP (hFleY hf)⟩
      have hfFix : fFU ∈
          (subgroupCentralizerIn c.FU P).subgroupOf c.FU :=
        Subgroup.mem_subgroupOf.mpr hfC
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) fFU hfFix
      exact congrArg Subtype.val hcomm
    have hxM : (x : G) ∈ w.M := by
      have hxN := Subgroup.centralizer_le_normalizer (F : Set G) hxCentF
      rw [hNFeq] at hxN
      exact hxN
    have hxY : (x : G) ∈ Y := ⟨x.2, hxM⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hYcentP hxY⟩
  have hFUodd : Odd (Nat.card c.FU) :=
    Odd.of_dvd_nat hUodd
      (Subgroup.card_dvd_of_le (fittingSubgroupOf_le c.U))
  have hPFUcop : Nat.Coprime (Nat.card P) (Nat.card c.FU) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hFUodd.coprime_two_left.pow_left n
  have htriv : ActsTrivially (A := P) (G := c.FU) :=
    actsTrivially_of_nilpotent_coprime_and_centralizer_fixedPointSubgroup
      (fittingSubgroupOf_isNilpotent c.U) hPFUcop hcentralizerFix
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  let pP : P := ⟨p, hp⟩
  let fFU : c.FU := ⟨f, hf⟩
  have hfix : pP • fFU = fFU := htriv pP fFU
  have hconj : p * f * p⁻¹ = f := by
    simpa [pP, fFU,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPnormFU] using
      congrArg Subtype.val hfix
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

/-- Equation (7), second half: `O2(H ∩ M)` centralizes `U`.  Since `F(U)`
is normal and self-centralizing in the odd solvable group `U`, the normal
case of Fact 1.1(iv) upgrades the centralization of `F(U)` to all of `U`. -/
private theorem fitting_twoCore_inter_centralizes_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (K0 F : Subgroup G)
    (hFnormalM : IsNormalIn F w.M)
    (hFne : F ≠ ⊥)
    (hjoinY : K0 ⊔ F = c.FU ⊓ w.M) :
    twoCoreOf (c.H ⊓ w.M) ≤ Subgroup.centralizer (c.U : Set G) := by
  let C : Subgroup G := c.H ⊓ w.M
  let P : Subgroup G := twoCoreOf C
  have hPcentFU : P ≤ Subgroup.centralizer (c.FU : Set G) := by
    simpa [P, C] using
      fitting_twoCore_inter_centralizes_fitting
        hmin c w K0 F hFnormalM hFne hjoinY
  have hUleH : c.U ≤ c.H := Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hUnormalH : IsNormalIn c.U c.H := by
    refine ⟨hUleH, ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
        pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        p hp (⟨h, hh⟩ : c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  have hPleH : P ≤ c.H := by
    intro p hp
    exact (show p ∈ C from (by
      rcases Subgroup.mem_map.mp hp with ⟨pC, hpC, rfl⟩
      exact pC.2)).1
  have hPnormU : P ≤ Subgroup.normalizer (c.U : Set G) :=
    hPleH.trans (le_normalizer_of_isNormalIn hUnormalH)
  have hFUleU : c.FU ≤ c.U := fittingSubgroupOf_le c.U
  have hFUnormalU : IsNormalIn c.FU c.U := by
    change IsNormalIn ((fittingSubgroup c.U).map c.U.subtype) c.U
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := fittingSubgroup c.U) (hKchar := by infer_instance)
      (hHnormal := ⟨le_rfl, by
        intro u hu x hx
        exact c.U.mul_mem (c.U.mul_mem hu hx) (c.U.inv_mem hu)⟩)
  have hFUnormalSub : (c.FU.subgroupOf c.U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (H := c.U) (N := c.FU) (le_normalizer_of_isNormalIn hFUnormalU)
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hUsolv : IsSolvable c.U := odd_order_theorem c.U hUodd
  have hself : c.U ⊓ Subgroup.centralizer (c.FU : Set G) ≤ c.FU := by
    change c.U ⊓ Subgroup.centralizer
        (((fittingSubgroup c.U).map c.U.subtype : Subgroup G) : Set G) ≤
      (fittingSubgroup c.U).map c.U.subtype
    exact fact_1_2_centralizer_fitting_le_fitting c.U hUsolv
  have hPp : IsPGroup 2 P := by
    change IsPGroup 2 ((pCore 2 C).map C.subtype)
    exact (pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hcop : Nat.Coprime (Nat.card P) (Nat.card c.U) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hUodd.coprime_two_left.pow_left n
  exact centralizes_of_normal_selfCentralizing_coprime
    P c.U c.FU hPnormU hFUleU hFUnormalSub hPcentFU hself hcop hUsolv

/-- Equation (7), forward containment: `O2(H ∩ M)` lies in `O2(Hhat)`.  A
two-subgroup of `Hhat` centralizing `U` lies in `O2(Hhat)` by Theorem 2.6,
and the previous lemma supplies the centralization. -/
private theorem fitting_twoCore_inter_le_twoCore_Hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (K0 F : Subgroup G)
    (hFnormalM : IsNormalIn F w.M)
    (hFne : F ≠ ⊥)
    (hjoinY : K0 ⊔ F = c.FU ⊓ w.M) :
    twoCoreOf (c.H ⊓ w.M) ≤ twoCoreOf c.Hhat := by
  let C : Subgroup G := c.H ⊓ w.M
  let P : Subgroup G := twoCoreOf C
  have hPp : IsPGroup 2 P := by
    change IsPGroup 2 ((pCore 2 C).map C.subtype)
    exact (pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hPleHhat : P ≤ c.Hhat := by
    intro p hp
    rcases Subgroup.mem_map.mp hp with ⟨pC, hpC, rfl⟩
    exact c.H_le_Hhat pC.2.1
  have hPcentU : P ≤ Subgroup.centralizer (c.U : Set G) := by
    simpa [P, C] using
      fitting_twoCore_inter_centralizes_U
        hmin c w K0 F hFnormalM hFne hjoinY
  exact twoSubgroup_le_twoCoreOf_Hhat_of_centralizes_U
    c (theorem_2_6 hmin c) P hPp hPleHhat hPcentU

/-- Equation (7), reverse containment: `O2(Hhat)` lies in
`O2(H ∩ M)`.  Theorem 2.6 places `O2(Hhat)` in `H ∩ C_G(U)`; the
equation-(6) identity `N_G(F) = M` places it in `M`, after which normal
two-subgroup maximality gives containment in `O2(H ∩ M)`. -/
private theorem fitting_twoCore_Hhat_le_twoCore_inter
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (K0 F : Subgroup G)
    (hFnormalM : IsNormalIn F w.M)
    (hFne : F ≠ ⊥)
    (hjoinY : K0 ⊔ F = c.FU ⊓ w.M) :
    twoCoreOf c.Hhat ≤ twoCoreOf (c.H ⊓ w.M) := by
  classical
  let C : Subgroup G := c.H ⊓ w.M
  let O : Subgroup G := twoCoreOf c.Hhat
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have hOcentU : O ≤ Subgroup.centralizer (c.U : Set G) := by
    change twoCoreOf c.Hhat ≤ Subgroup.centralizer (c.U : Set G)
    rw [← h26.2.1]
    exact inf_le_right
  have hOleH : O ≤ c.H := by
    change twoCoreOf c.Hhat ≤ c.H
    rw [← h26.2.1]
    exact inf_le_left.trans (centralizerSetup_S_le_H c)
  have hFleU : F ≤ c.U := by
    intro f hf
    have hfY : f ∈ c.FU ⊓ w.M := by
      rw [← hjoinY]
      exact (le_sup_right : F ≤ K0 ⊔ F) hf
    exact fittingSubgroupOf_le c.U hfY.1
  have hOcentF : O ≤ Subgroup.centralizer (F : Set G) :=
    hOcentU.trans (Subgroup.centralizer_le (SetLike.coe_mono hFleU))
  have hNFeq : Subgroup.normalizer (F : Set G) = w.M :=
    secondCase_normalizer_fitting_fixed_eq_M hmin c w F hFne hFnormalM
  have hOleM : O ≤ w.M := by
    intro x hx
    have hxN := Subgroup.centralizer_le_normalizer (F : Set G) (hOcentF hx)
    rwa [hNFeq] at hxN
  have hOleC : O ≤ C := fun x hx => ⟨hOleH hx, hOleM hx⟩
  have hOnormalHhat : IsNormalIn O c.Hhat := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · intro z hz x hx
      rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨(⟨z, hz⟩ : c.Hhat) * x0 * (⟨z, hz⟩ : c.Hhat)⁻¹,
          (pCore_normal (p := 2) (G := c.Hhat)).conj_mem
            x0 hx0 (⟨z, hz⟩ : c.Hhat), rfl⟩
  have hCleHhat : C ≤ c.Hhat :=
    inf_le_left.trans c.H_le_Hhat
  have hOnormalC : IsNormalIn O C := by
    refine ⟨hOleC, ?_⟩
    intro z hz x hx
    exact hOnormalHhat.2 z (hCleHhat hz) x hx
  let OC : Subgroup C := O.subgroupOf C
  have hOCnormal : OC.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hOleC]
    intro x z hx hz
    exact hOnormalC.2 z hz x hx
  have hOp : IsPGroup 2 O := by
    change IsPGroup 2 ((pCore 2 c.Hhat).map c.Hhat.subtype)
    exact (pCore_isPGroup (p := 2) (G := c.Hhat)).map c.Hhat.subtype
  have hOCp : IsPGroup 2 OC :=
    hOp.of_equiv (Subgroup.subgroupOfEquivOfLe hOleC).symm
  have hOCle : OC ≤ pCore 2 C := le_sSup ⟨hOCnormal, hOCp⟩
  have hmaple := Subgroup.map_mono (f := C.subtype) hOCle
  have hmapOC : OC.map C.subtype = O :=
    Subgroup.map_subgroupOf_eq_of_le hOleC
  simpa [O, C, twoCoreOf, hmapOC] using hmaple

/-- The equations-(5)--(7) package, obtained PSL₂-independently from the
legitimate equation-(4) component-centralization hypothesis `F ≤ C_G(d.E)`
and the normalizer-layer control `componentLayerOf (N_G(X)) = d.E` for
every nontrivial `X ≤ F`.

The conclusion provides the full structural chain that unlocks choosing the
prime `p` (a prime divisor of the nontrivial cyclic group `F`) and the
rank-two subgroup `A` of `F × K0`:

* `F` is normal in `M` and in `Y = F(U) ∩ M` (equation (4));
* `F ≠ 1` and `N_G(F) = M` (equation (5));
* `F ∩ F^g = 1` for every `g ∉ M` (equation (6), first half);
* `F` is cyclic and `|F| ≤ |K0|`, so `K0 ≠ 1` (equation (6), second half);
* `O2(H ∩ M) = O2(Hhat)` (equation (7), two-core half).
-/
public theorem secondCase_fitting_equation5_7_of_component_centralization
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K K0 F : Subgroup G)
    (s : d.E)
    (hKcyc : IsCyclic K)
    (hK0le : K0 ≤ K)
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E) :
    IsNormalIn F w.M ∧
    IsNormalIn F (fittingSubgroupOf c.U ⊓ w.M) ∧
    F ≠ ⊥ ∧
    Subgroup.normalizer (F : Set G) = w.M ∧
    (∀ g : G, g ∉ w.M → F ⊓ conjugateSubgroup F g = ⊥) ∧
    IsCyclic F ∧
    Nat.card F ≤ Nat.card K0 ∧
    K0 ≠ ⊥ ∧
    twoCoreOf (c.H ⊓ w.M) = twoCoreOf c.Hhat := by
  classical
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
  have hFleY : F ≤ Y := by
    intro f hf
    rw [hF_eq, centralizerIn] at hf
    exact hf.1
  have hFleFU : F ≤ fittingSubgroupOf c.U := hFleY.trans inf_le_left
  have hFleM : F ≤ w.M := hFleY.trans inf_le_right
  have hFnormalM : IsNormalIn F w.M :=
    fitting_fixed_normal_in_M_of_component_centralization
      c w d F hFleFU hFleM s hFcentE hF_eq
  have hFnormalY : IsNormalIn F Y := by
    refine ⟨hFleY, ?_⟩
    intro y hy f hf
    exact hFnormalM.2 y hy.2 f hf
  have hFne : F ≠ ⊥ :=
    secondCase_fitting_fixed_ne_bot hmin c w K K0 F hKcyc hK0le hjoin
  have hNF : Subgroup.normalizer (F : Set G) = w.M :=
    secondCase_normalizer_fitting_fixed_eq_M hmin c w F hFne hFnormalM
  have hTI : ∀ g : G, g ∉ w.M → F ⊓ conjugateSubgroup F g = ⊥ :=
    fitting_fixed_TI_of_normalizer_layer hmin c w d F hLayer
  have hK0cyc : IsCyclic K0 := by
    let : IsCyclic K := hKcyc
    exact Subgroup.isCyclic_of_le hK0le
  have hcycCard : IsCyclic F ∧ Nat.card F ≤ Nat.card K0 :=
    fitting_fixed_cyclic_and_card_le_of_normalizer_layer
      hmin c w d K0 F hK0cyc hFleFU hFnormalM hjoin hLayer
  have hK0ne : K0 ≠ ⊥ := by
    intro hK0bot
    have hK0card1 : Nat.card K0 = 1 := by rw [hK0bot]; simp
    have hFcard_le1 : Nat.card F ≤ 1 := by
      simpa [hK0card1] using hcycCard.2
    have : Nonempty F := ⟨⟨1, F.one_mem⟩⟩
    have hFcard_pos : 1 ≤ Nat.card F := Nat.card_pos
    have hFcard1 : Nat.card F = 1 := by omega
    exact hFne ((Subgroup.eq_bot_iff_card (H := F)).mpr hFcard1)
  have hO2 : twoCoreOf (c.H ⊓ w.M) = twoCoreOf c.Hhat := by
    apply le_antisymm
    · exact fitting_twoCore_inter_le_twoCore_Hhat
        hmin c w K0 F hFnormalM hFne hjoin
    · exact fitting_twoCore_Hhat_le_twoCore_inter
        hmin c w K0 F hFnormalM hFne hjoin
  have hFnormalY' : IsNormalIn F (fittingSubgroupOf c.U ⊓ w.M) := by
    simpa [Y] using hFnormalY
  exact ⟨hFnormalM, hFnormalY', hFne, hNF, hTI, hcycCard.1, hcycCard.2,
    hK0ne, hO2⟩

end CFSG.GorensteinWalter
