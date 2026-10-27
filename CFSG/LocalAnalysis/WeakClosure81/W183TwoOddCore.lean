module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoOddSub
public import CFSG.Open.FusionDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

private theorem w183b5_fusionOddCore_characteristic (H : Type*) [Group H] :
    (fusionOddCore H).Characteristic := by
  refine Subgroup.characteristic_iff_le_comap.2 fun φ => sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map _ φ.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective φ.injective]
  exact hN.2

private theorem w183b5_odd_natCard_fusionOddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext L
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem pCore_oddClassSub_eq_bot {Y : Type} [Group Y] [Finite Y] (a : Y)
    (hpc : CFSG.pCore 2 Y = ⊥) : CFSG.pCore 2 ↥(oddClassSub a) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X := oddClassSub a
  let N := Subgroup.normalClosure ({a} : Set Y)
  let R := CFSG.pCore 2 ↥X
  let R' := R.map X.subtype
  change R = ⊥
  have hXN : X ≤ N := oddClassSub_le_normalClosure a
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hXn : (X.subgroupOf N).Normal := normal_subgroupOf_oddClassSub a
  have hNX : N ≤ Subgroup.normalizer (X : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mp hXn
  have hRchar : R.Characteristic :=
    CFSG.LieType.BorelTits.pCore_characteristic (G := ↥X) 2
  have hR'norm : N ≤ Subgroup.normalizer (R' : Set Y) :=
    hNX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := X) R)
  have hR'leN : R' ≤ N := (Subgroup.map_subtype_le R).trans hXN
  have hR'p : IsPGroup 2 R' :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) (r := 2)).map X.subtype
  have hR'le : R' ≤ CFSG.Open.pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) (N := R') (H := N)
      hR'leN hR'norm hR'p
  have hNcoreLe : CFSG.Open.pCoreOf 2 N ≤ CFSG.pCore 2 Y := by
    haveI : N.Normal := hNn
    haveI : (CFSG.pCore 2 ↥N).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic (G := ↥N) 2
    exact CFSG.LieType.BorelTits.le_pCore (r := 2) (G := Y)
      (N := CFSG.Open.pCoreOf 2 N)
      (ConjAct.normal_of_characteristic_of_normal (H := N) (K := CFSG.pCore 2 ↥N))
      ((CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥N) (r := 2)).map N.subtype)
  have hR'bot : R' = ⊥ := le_bot_iff.mp (hR'le.trans (hNcoreLe.trans (le_of_eq hpc)))
  exact (Subgroup.map_eq_bot_iff_of_injective (H := R) X.subtype_injective).mp hR'bot

theorem fusionOddCore_oddClassSub_eq_bot {Y : Type} [Group Y] [Finite Y] (a : Y)
    (hR : ∀ R : Subgroup Y, R.Normal → Group.IsSolvable ↥R → R = ⊥) :
    fusionOddCore ↥(oddClassSub a) = ⊥ := by
  let X := oddClassSub a
  let N := Subgroup.normalClosure ({a} : Set Y)
  let O := fusionOddCore ↥X
  let O' := O.map X.subtype
  let O_N := fusionOddCore ↥N
  change O = ⊥
  have hXN : X ≤ N := oddClassSub_le_normalClosure a
  have hNn : N.Normal := Subgroup.normalClosure_normal
  have hXn : (X.subgroupOf N).Normal := normal_subgroupOf_oddClassSub a
  have hNX : N ≤ Subgroup.normalizer (X : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mp hXn
  have hOchar : O.Characteristic := w183b5_fusionOddCore_characteristic ↥X
  haveI : O.Characteristic := hOchar
  have hO'norm : N ≤ Subgroup.normalizer (O' : Set Y) :=
    hNX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := X) O)
  have hO'leN : O' ≤ N := (Subgroup.map_subtype_le O).trans hXN
  have hO'sub : (O'.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO'leN).mpr hO'norm
  have hO'odd : Odd (Nat.card O') := by
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact w183b5_odd_natCard_fusionOddCore ↥X
  have hO'subOdd : Odd (Nat.card (O'.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO'leN).toEquiv]
    exact hO'odd
  have hO'sub_le : O'.subgroupOf N ≤ O_N := le_sSup ⟨hO'sub, hO'subOdd⟩
  have hO'le : O' ≤ O_N.map N.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hO'leN]
    exact Subgroup.map_mono hO'sub_le
  have hOcharN : O_N.Characteristic := w183b5_fusionOddCore_characteristic ↥N
  haveI : O_N.Characteristic := hOcharN
  haveI : N.Normal := hNn
  have hObarNormal : (O_N.map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := N) (K := O_N)
  have hObarOdd : Odd (Nat.card (O_N.map N.subtype)) := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact w183b5_odd_natCard_fusionOddCore ↥N
  have hObarSolv : Group.IsSolvable ↥(O_N.map N.subtype) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hObarOdd
  have hObarBot : O_N.map N.subtype = ⊥ := hR _ hObarNormal hObarSolv
  have hONbot : O_N = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := O_N) N.subtype_injective).mp hObarBot
  have hO'bot : O' = ⊥ := le_bot_iff.mp (hO'le.trans (le_of_eq hObarBot))
  exact (Subgroup.map_eq_bot_iff_of_injective (H := O) X.subtype_injective).mp hO'bot

end CFSG.LocalAnalysis.WeakClosure81

end
