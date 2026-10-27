module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.OddQuotientFixedPointFree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SelfCommutatorFixedPointFreeQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.InvolutionCentralizesNormalizedTwoSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.theorem_9_1
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped Pointwise commutatorElement

universe u

theorem fittingNormalizer_commutator_le_of_fixed {X : Type u} [Group X] [Finite X]
    (U : Subgroup X) {t : X}
    (hSylowTwo : ∀ S : Sylow 2 X, IsMulCommutative (S : Subgroup X))
    (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (hUinv : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (U : Set X))
    (hUcomm : ⁅U, Subgroup.zpowers t⁆ = U)
    (hfixedF : CFSG.fittingSubgroup X ⊓ Subgroup.centralizer ({t} : Set X) ≤
      CFSG.fittingSubgroup X ⊓ Subgroup.centralizer (U : Set X)) :
    ⁅CFSG.fittingSubgroup X ⊓ Subgroup.normalizer
        ((CFSG.fittingSubgroup X ⊓ Subgroup.centralizer (U : Set X) : Subgroup X) : Set X), U⁆ ≤
      CFSG.fittingSubgroup X ⊓ Subgroup.centralizer (U : Set X) := by
  classical
  let F : Subgroup X := CFSG.fittingSubgroup X
  let D : Subgroup X := F ⊓ Subgroup.centralizer (U : Set X)
  let R : Subgroup X := F ⊓ Subgroup.normalizer (D : Set X)
  change ⁅R, U⁆ ≤ D
  have hFnormal : F.Normal := CFSG.fittingSubgroup_normal
  have hFnil : Group.IsNilpotent F := CFSG.fittingSubgroup_nilpotent
  have hRleF : R ≤ F := inf_le_left
  have hRnormD : R ≤ Subgroup.normalizer (D : Set X) := inf_le_right
  have hUnormF : U ≤ Subgroup.normalizer (F : Set X) := Subgroup.le_normalizer_of_normal
  have hUnormCU : U ≤ Subgroup.normalizer (Subgroup.centralizer (U : Set X) : Set X) :=
    U.le_normalizer.trans (normalizer_le_normalizer_centralizer_subgroup U)
  have hUnormD : U ≤ Subgroup.normalizer (D : Set X) :=
    (le_inf hUnormF hUnormCU).trans Subgroup.inf_normalizer_le_normalizer_inf
  have htCent : t ∈ Subgroup.centralizer ({t} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htnormU : t ∈ Subgroup.normalizer (U : Set X) := hUinv htCent
  have htnormF : t ∈ Subgroup.normalizer (F : Set X) :=
    (Subgroup.le_normalizer_of_normal (H := F) (K := (⊤ : Subgroup X))) (by simp)
  have htnormCU : t ∈ Subgroup.normalizer (Subgroup.centralizer (U : Set X) : Set X) :=
    (normalizer_le_normalizer_centralizer_subgroup U) htnormU
  have htnormD : t ∈ Subgroup.normalizer (D : Set X) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htnormF, htnormCU⟩
  have hUnormR : U ≤ Subgroup.normalizer (R : Set X) := by
    have hUnormND : U ≤ Subgroup.normalizer (Subgroup.normalizer (D : Set X) : Set X) :=
      hUnormD.trans (Subgroup.normalizer (D : Set X)).le_normalizer
    exact (le_inf hUnormF hUnormND).trans Subgroup.inf_normalizer_le_normalizer_inf
  have htnormR : t ∈ Subgroup.normalizer (R : Set X) := by
    have htnormND : t ∈ Subgroup.normalizer (Subgroup.normalizer (D : Set X) : Set X) :=
      (Subgroup.normalizer (D : Set X)).le_normalizer htnormD
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨htnormF, htnormND⟩
  have hRnil : Group.IsNilpotent R := by
    have hsub : Group.IsNilpotent (R.subgroupOf F) := by infer_instance
    exact Group.nilpotent_of_mulEquiv (G := R.subgroupOf F) (G' := R) (_h := hsub)
      (Subgroup.subgroupOfEquivOfLe hRleF)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup R := pCore 2 R
  let K : Subgroup R := pPrimeCore 2 R
  let PX : Subgroup X := P.map R.subtype
  let KX : Subgroup X := K.map R.subtype
  have : P.Characteristic := by dsimp [P]; infer_instance
  have : K.Characteristic := by dsimp [K]; infer_instance
  have htop : (⊤ : Subgroup R) ≤ P ⊔ K := by
    simpa [P, K] using (nilpotent_top_le_pCore_sup_pPrimeCore (Q := R) (p := 2) hRnil)
  have hRle : R ≤ PX ⊔ KX := by
    intro x hxR
    have hxint : (⟨x, hxR⟩ : R) ∈ P ⊔ K := htop trivial
    have hxmap : x ∈ (P ⊔ K).map R.subtype := Subgroup.mem_map.mpr ⟨⟨x, hxR⟩, hxint, rfl⟩
    simpa [PX, KX, Subgroup.map_sup] using hxmap
  have hPXleR : PX ≤ R := by simpa [PX, P] using (Subgroup.map_subtype_le (H := R) (pCore 2 R))
  have hKXleR : KX ≤ R := by
    simpa [KX, K] using (Subgroup.map_subtype_le (H := R) (pPrimeCore 2 R))
  have hUnormKX : U ≤ Subgroup.normalizer (KX : Set X) :=
    hUnormR.trans (section9_normalizer_le_normalizer_map_subtype_of_characteristic (G := X) R K)
  have htnormPX : t ∈ Subgroup.normalizer (PX : Set X) :=
    (section9_normalizer_le_normalizer_map_subtype_of_characteristic (G := X) R P) htnormR
  have htnormKX : t ∈ Subgroup.normalizer (KX : Set X) :=
    (section9_normalizer_le_normalizer_map_subtype_of_characteristic (G := X) R K) htnormR
  have hPXtwo : IsPGroup 2 PX := by
    simpa [PX, P] using (IsPGroup.map (pCore_isPGroup (G := R) (p := 2)) R.subtype)
  have hPXcent : PX ≤ Subgroup.centralizer ({t} : Set X) :=
    twoSubgroup_le_centralizer_involution_of_hasAbelianSylow PX hSylowTwo hPXtwo ht htnormPX
  have hPXleD : PX ≤ D := fun x hx => hfixedF ⟨hRleF (hPXleR hx), hPXcent hx⟩
  have hPXU : ⁅PX, U⁆ ≤ D :=
    (Subgroup.commutator_mono hPXleD le_rfl).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left).mp hUnormD)
  have hKcardOdd : Odd (Nat.card K) :=
    Nat.coprime_two_left.mp (by simpa [K] using (pPrimeCore_coprime_card (G := R) (p := 2)))
  have hKXodd : Odd (Nat.card KX) := by
    rw [show Nat.card KX = Nat.card K from by
      simpa [KX] using (Subgroup.card_map_of_injective (K := K) (f := R.subtype)
        R.subtype_injective)]
    exact hKcardOdd
  have hKXsolv : Group.IsSolvable KX := by
    have : Group.IsNilpotent KX := by
      have hsub : Group.IsNilpotent (KX.subgroupOf R) := by infer_instance
      exact Group.nilpotent_of_mulEquiv (G := KX.subgroupOf R) (G' := KX) (_h := hsub)
        (Subgroup.subgroupOfEquivOfLe hKXleR)
    infer_instance
  let DK : Subgroup X := KX ⊓ D
  have hDKleKX : DK ≤ KX := inf_le_left
  have hKXnormD : KX ≤ Subgroup.normalizer (D : Set X) := hKXleR.trans hRnormD
  have hKXnormDK : KX ≤ Subgroup.normalizer (DK : Set X) :=
    (le_inf KX.le_normalizer hKXnormD).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hDKnormalKX : (DK.subgroupOf KX).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDKleKX]
    exact hKXnormDK
  have htnormDK : t ∈ Subgroup.normalizer (DK : Set X) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htnormKX, htnormD⟩
  have hUnormDK : U ≤ Subgroup.normalizer (DK : Set X) :=
    (le_inf hUnormKX hUnormD).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hfixedDK : KX ⊓ Subgroup.centralizer ({t} : Set X) ≤ DK := fun x hx =>
    ⟨hx.1, hfixedF ⟨hRleF (hKXleR hx.1), hx.2⟩⟩
  have hquotFixed : ∀ k : KX, t * (k : X) * t⁻¹ * (k : X)⁻¹ ∈ DK → (k : X) ∈ DK :=
    fixedPointFree_quotient_of_odd_solvable_and_fixedPoints_le
      KX DK hDKleKX hDKnormalKX htnormKX htnormDK ht hKXsolv hKXodd hfixedDK
  have hKXU_DK : ⁅KX, U⁆ ≤ DK :=
    commutator_le_of_selfCommutator_fixedPointFree_involution_quotient
      KX DK U hDKleKX hDKnormalKX hUnormKX htnormKX hUnormDK htnormDK ht hUcomm hquotFixed
  have hKXU : ⁅KX, U⁆ ≤ D := hKXU_DK.trans inf_le_right
  have hsupComm : ⁅PX ⊔ KX, U⁆ ≤ D :=
    commutator_sup_le_of_commutator_le_and_normalize PX KX U D hPXU hKXU
      (hPXleR.trans hRnormD) (hKXleR.trans hRnormD)
  exact (Subgroup.commutator_mono hRle le_rfl).trans hsupComm

theorem le_centralizer_fittingSubgroup_of_isPerfect {X : Type u} [Group X] [Finite X]
    (U : Subgroup X) {t : X}
    (hSylowTwo : ∀ S : Sylow 2 X, IsMulCommutative (S : Subgroup X))
    (ht : BenderSuzuki.PFAppendixIII.IsInvolution t)
    (hUinv : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (U : Set X))
    (hUcomm : ⁅U, Subgroup.zpowers t⁆ = U) (hUperf : Group.IsPerfect U)
    (hfixedF : CFSG.fittingSubgroup X ⊓ Subgroup.centralizer ({t} : Set X) ≤
      CFSG.fittingSubgroup X ⊓ Subgroup.centralizer (U : Set X)) :
    U ≤ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) := by
  classical
  set F : Subgroup X := CFSG.fittingSubgroup X with hF
  set D : Subgroup X := F ⊓ Subgroup.centralizer (U : Set X) with hD
  set R : Subgroup X := F ⊓ Subgroup.normalizer (D : Set X) with hR
  have hRU : ⁅R, U⁆ ≤ D :=
    fittingNormalizer_commutator_le_of_fixed U hSylowTwo ht hUinv hUcomm hfixedF
  have hDU : ⁅D, U⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hUR : ⁅U, R⁆ = ⊥ := by
    apply CFSG.LocalCores.perfect_double_commutator hUperf
    rw [← le_bot_iff, Subgroup.commutator_comm U R]
    calc ⁅⁅R, U⁆, U⁆ ≤ ⁅D, U⁆ := Subgroup.commutator_mono hRU le_rfl
      _ = ⊥ := hDU
  have hRcentU : R ≤ Subgroup.centralizer (U : Set X) := by
    rw [Subgroup.commutator_comm] at hUR
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUR
  have hDF : D ≤ F := inf_le_left
  have hRD : R = D := le_antisymm (fun x hx => ⟨hx.1, hRcentU hx⟩)
    (fun x hx => ⟨hDF hx, D.le_normalizer hx⟩)
  let D' : Subgroup F := D.subgroupOf F
  have hnorm_eq : (Subgroup.normalizer (D : Set X)).subgroupOf F =
      Subgroup.normalizer (D' : Set F) := Subgroup.subgroupOf_normalizer_eq hDF
  have hnormD' : Subgroup.normalizer (D' : Set F) = D' := by
    refine le_antisymm (fun x hx => ?_) D'.le_normalizer
    have hxN : (x : X) ∈ Subgroup.normalizer (D : Set X) := by
      rw [← hnorm_eq] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have hxR : (x : X) ∈ R := ⟨x.2, hxN⟩
    rw [hRD] at hxR
    exact hxR
  have : Group.IsNilpotent F := CFSG.fittingSubgroup_nilpotent
  have hD'top : D' = ⊤ := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := F))) D' hnormD'
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hfD : f ∈ D := by
    have : (⟨f, hf⟩ : F) ∈ D' := by rw [hD'top]; trivial
    exact this
  exact (Subgroup.mem_centralizer_iff.mp hfD.2 u hu).symm

end CFSG.Walter
