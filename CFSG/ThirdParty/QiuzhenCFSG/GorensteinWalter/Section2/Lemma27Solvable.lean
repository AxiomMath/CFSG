module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorLePiCompl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorNotLeFU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PiCoreCharacteristic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarCommute
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingOddCoreEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.7, solvability of `M`

The first conjunct gives `[M,t] ≤ F_{πᶜ}(M)`.  Since `π` contains `2`, the
π-complement core is an odd normal subgroup of `M`, hence lies in
`O₂'(M)`.  Therefore the image of `t` is a nontrivial central involution in
the `D`-group quotient `M/O₂'(M)`; the preamble central-involution lemma
forces that quotient to be a `2`-group, and an odd kernel plus a `2`-group
quotient is solvable.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- `[M, t]` lies in the odd core `O₂'(M)` under the Lemma 2.7 hypotheses. -/
private theorem commutator_le_pPrimeCore_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    let M' : Type u := ↥M
    let tM : M' :=
      ⟨c.t, t_mem_M_of_centralizerStructure c M hM (theorem_2_6 hmin c)⟩
    ⁅(⊤ : Subgroup M'), Subgroup.zpowers tM⁆ ≤ pPrimeCore 2 M' := by
  classical
  intro M' tM
  let : Group M' := M.toGroup
  let π := primesOfOrder (fittingSubgroupOf c.Hhat)
  let A : Subgroup G := piCoreOf (fittingSubgroupOf M) πᶜ
  have hCommAmb : ⁅M, Subgroup.zpowers c.t⁆ ≤ A :=
    lemma_2_7_commutator_le_piCore_compl hmin c M hM
  have hAodd : Nat.Coprime 2 (Nat.card (↥A)) :=
    piCore_compl_odd_card_of_Lemma27Hypothesis hmin c M hM
  have hA_le_F : A ≤ fittingSubgroupOf M :=
    piCoreOf_le (fittingSubgroupOf M) πᶜ
  have hF_le_M : fittingSubgroupOf M ≤ M :=
    (fittingSubgroupOf_isNormalIn M).1
  have hAnorm : IsNormalIn A M := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := M) (F := fittingSubgroupOf M)
      (K := piCore πᶜ (↥(fittingSubgroupOf M)))
      (piCore_characteristic πᶜ)
      (by simpa [fittingSubgroupOf] using fittingSubgroupOf_isNormalIn M)
    simpa [A, piCoreOf] using h
  have hA_le_Oamb : A ≤ (pPrimeCore 2 M').map M.subtype :=
    le_oddCoreOf_of_normal_of_coprime M A (hA_le_F.trans hF_le_M) hAnorm hAodd
  rw [Subgroup.commutator_le]
  intro m hm z hz
  have hzM : (z : M') ∈ Subgroup.zpowers tM := by
    simpa [tM] using hz
  have hmG : (m : G) ∈ M := m.2
  have hzG : (z : G) ∈ Subgroup.zpowers c.t := by
    rcases Subgroup.mem_zpowers_iff.mp hzM with ⟨n, rfl⟩
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    change (c.t : G) ^ n = c.t ^ n
    rfl
  let cm : M' := ⁅(m : M'), (z : M')⁆
  have hcommA : (cm : G) ∈ A := by
    change (⁅(m : G), (z : G)⁆ : G) ∈ A
    exact Subgroup.commutator_le.mp hCommAmb (m : G) hmG (z : G) hzG
  have hcommOamb : (cm : G) ∈
      (pPrimeCore 2 M').map M.subtype := hA_le_Oamb hcommA
  rcases Subgroup.mem_map.mp hcommOamb with ⟨o, ho, heq⟩
  have hsub : cm = o := by
    apply Subtype.ext
    exact heq.symm
  change cm ∈ pPrimeCore 2 M'
  rw [hsub]
  exact ho

/-- A central involution in the odd-core quotient of a `D`-group forces that
quotient to be a `2`-group.  This is the preamble branch elimination applied
directly to the quotient, avoiding a separate `IsDGroup` construction. -/
private theorem quotient_two_of_central_involution_of_isDGroup
    {M' : Type u} [Group M'] [Finite M']
    (hD : IsDGroup M')
    (tb : M' ⧸ pPrimeCore 2 M')
    (htbcenter : tb ∈ Subgroup.center (M' ⧸ pPrimeCore 2 M'))
    (htb2 : tb ^ 2 = 1) (htbne : tb ≠ 1) :
    IsPGroup 2 (M' ⧸ pPrimeCore 2 M') := by
  classical
  let Q : Type u := M' ⧸ pPrimeCore 2 M'
  rcases hD with ⟨_hS, htwo⟩ | ⟨_hS, e7⟩ |
      ⟨_hS, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
  · simpa [Q] using htwo
  · have hecenter : e7.some tb ∈ Subgroup.center (alternatingGroup (Fin 7)) :=
      preambleCenter_mem_map e7.some htbcenter
    have heone : e7.some tb = 1 := by
      have hempty : e7.some tb ∈ (⊥ : Subgroup (alternatingGroup (Fin 7))) := by
        simpa [preambleCenter_eq_bot_A7] using hecenter
      exact Subgroup.mem_bot.mp hempty
    exfalso
    apply htbne
    exact e7.some.injective (by simpa using heone)
  · let : L.Normal := hLnormal
    have htL : tb ∈ L := preamble_mem_of_odd_index L hLnormal hLindex htb2
    let tbL : ↥L := ⟨tb, htL⟩
    have htLc : tbL ∈ Subgroup.center (↥L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp htbcenter) (y : Q)
    rcases hLmodel with hpsl | hpgl
    · have hmodelc : hpsl.some tbL ∈ Subgroup.center (PSL2 K) :=
        preambleCenter_mem_map hpsl.some htLc
      have hmodelone : hpsl.some tbL = 1 := by
        have hmempty : hpsl.some tbL ∈ (⊥ : Subgroup (PSL2 K)) := by
          simpa [psl2_center_eq_bot] using hmodelc
        exact Subgroup.mem_bot.mp hmempty
      exfalso
      apply htbne
      have htbLeone : tbL = 1 := hpsl.some.injective (by simpa using hmodelone)
      simpa [tbL] using congrArg (fun z : ↥L => (z : Q)) htbLeone
    · have hmodelc : hpgl.some tbL ∈ Subgroup.center (PGL2 K) :=
        preambleCenter_mem_map hpgl.some htLc
      have hmodelone : hpgl.some tbL = 1 := by
        have hmempty : hpgl.some tbL ∈ (⊥ : Subgroup (PGL2 K)) := by
          simpa [pgl2_center_eq_bot] using hmodelc
        exact Subgroup.mem_bot.mp hmempty
      exfalso
      apply htbne
      have htbLeone : tbL = 1 := hpgl.some.injective (by simpa using hmodelone)
      simpa [tbL] using congrArg (fun z : ↥L => (z : Q)) htbLeone

/-- `M` is solvable under the Lemma 2.7 hypotheses. -/
public theorem isSolvable_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    IsSolvable M := by
  classical
  let M' : Type u := ↥M
  let : Group M' := M.toGroup
  let O : Subgroup M' := pPrimeCore 2 M'
  let : O.Normal := pPrimeCore_normal
  let Q : Type u := M' ⧸ O
  let : Group Q := inferInstance
  have htM : c.t ∈ M :=
    t_mem_M_of_centralizerStructure c M hM (theorem_2_6 hmin c)
  let tM : M' := ⟨c.t, htM⟩
  have htM2 : tM ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    simpa [pow_two] using c.t_involution.2
  have hCommO : ⁅(⊤ : Subgroup M'), Subgroup.zpowers tM⁆ ≤ O := by
    simpa [O] using commutator_le_pPrimeCore_of_Lemma27Hypothesis hmin c M hM
  let q : M' →* Q := QuotientGroup.mk' O
  let tb : Q := q tM
  have hCommQbot : ⁅(⊤ : Subgroup Q), Subgroup.zpowers tb⁆ = ⊥ := by
    have hmap : (⁅(⊤ : Subgroup M'), Subgroup.zpowers tM⁆).map q =
        ⁅(⊤ : Subgroup Q), Subgroup.zpowers tb⁆ := by
      rw [Subgroup.map_commutator]
      rw [Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective O)]
      simp [tb, q]
    have himage : (⁅(⊤ : Subgroup M'), Subgroup.zpowers tM⁆).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff
        (H := ⁅(⊤ : Subgroup M'), Subgroup.zpowers tM⁆) (f := q)).mpr
      intro x hx
      exact (QuotientGroup.eq_one_iff (N := O) (x := x)).2 (hCommO hx)
    simpa [hmap] using himage
  have hQleC : (⊤ : Subgroup Q) ≤ Subgroup.centralizer
      ((Subgroup.zpowers tb : Subgroup Q) : Set Q) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := (⊤ : Subgroup Q)) (H₂ := Subgroup.zpowers tb)).1 hCommQbot
  have htbcenter : tb ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hyC : y ∈ Subgroup.centralizer
        ((Subgroup.zpowers tb : Subgroup Q) : Set Q) := hQleC (by trivial)
    exact (Subgroup.mem_centralizer_iff.mp hyC tb (Subgroup.mem_zpowers tb)).symm
  have htb2 : tb ^ 2 = 1 := by
    simpa [tb, q] using congrArg q htM2
  have hOcop : Nat.Coprime 2 (Nat.card (↥O)) :=
    pPrimeCore_coprime_card (p := 2) (G := M')
  have htMne : tM ≠ 1 := by
    intro h
    apply c.t_involution.1
    exact congrArg Subtype.val h
  have htbne : tb ≠ 1 := by
    intro h
    have hq : q tM = 1 := by simpa [tb, q] using h
    have htO : tM ∈ O := (QuotientGroup.eq_one_iff (N := O) (x := tM)).1 hq
    have hOel : (⟨tM, htO⟩ : O) ^ 2 = 1 := by
      apply Subtype.ext
      exact htM2
    have hOone : (⟨tM, htO⟩ : O) = 1 :=
      eq_one_of_sq_eq_one_of_coprime_two (G := O) hOcop hOel
    exact htMne (congrArg Subtype.val hOone)
  have hDM : IsDGroup M' := properSubgroups_areDGroups hmin M hM.1
  have hQ2 : IsPGroup 2 Q :=
    quotient_two_of_central_involution_of_isDGroup hDM tb htbcenter htb2 htbne
  have hOodd : Odd (Nat.card (↥O)) := Nat.coprime_two_left.mp hOcop
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  have hQsolv : IsSolvable Q := isSolvable_of_isPGroup hQ2
  exact isSolvable_of_normal_solvable_quotient_solvable O hOsolv hQsolv

end CFSG.GorensteinWalter
