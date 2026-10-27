module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpModel
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalC3Attach
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.LeviAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C31Steps
public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.Quasithin.EmptyFaithful.R3c20A
public import CFSG.Quasithin.EmptyFaithful.R3c21A
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SBc5Aut
public import CFSG.Quasithin.EmptyFaithful.SzN17Abs
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Blk
public import CFSG.Quasithin.Vol2.KGFactC31HSCases
public import CFSG.Quasithin.Vol2.KGFactC31HSMod
public import CFSG.Quasithin.Vol2.KGFactC31Hat

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.B2SmallJ

open CFSG CFSG.Assembly.LowTwoRank

noncomputable def kappaDerived {X : Type*} [Group X] {k : Type} [Field k]
    (κ : StatedSp 2 k →* X) : ↥(commutator (StatedSp 2 k)) →* X :=
  κ.comp (commutator (StatedSp 2 k)).subtype

theorem range_kappaDerived {X : Type*} [Group X] {k : Type} [Field k]
    {κ : StatedSp 2 k →* X} {N : Subgroup X} (hκrange : κ.range = N) :
    (kappaDerived κ).range = ⁅N, N⁆ := by
  unfold kappaDerived
  rw [MonoidHom.range_comp, Subgroup.range_subtype, map_commutator_eq, hκrange]

theorem kappaDerived_injective {X : Type*} [Group X] {k : Type} [Field k]
    {κ : StatedSp 2 k →* X} (hκinj : Function.Injective κ) :
    Function.Injective (kappaDerived κ) :=
  hκinj.comp (Subgroup.subtype_injective _)

noncomputable def derivedRangeEquivAlt6 {X : Type*} [Group X] {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {κ : StatedSp 2 k →* X} {N : Subgroup X}
    (hκinj : Function.Injective κ) (hκrange : κ.range = N) :
    ↥⁅N, N⁆ ≃* alternatingGroup (Fin 6) :=
  ((MonoidHom.ofInjective (kappaDerived_injective hκinj)).trans
      (MulEquiv.subgroupCongr (range_kappaDerived hκrange))).symm.trans
    (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hk)

theorem isQuasisimple_derivedRange_sp4_two {X : Type*} [Group X] {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) {κ : StatedSp 2 k →* X} {N : Subgroup X}
    (hκinj : Function.Injective κ) (hκrange : κ.range = N) :
    CFSG.IsQuasisimple ↥⁅N, N⁆ := by
  let e : ↥(commutator (StatedSp 2 k)) ≃* ↥⁅N, N⁆ :=
    (MonoidHom.ofInjective (kappaDerived_injective hκinj)).trans
      (MulEquiv.subgroupCongr (range_kappaDerived hκrange))
  exact (CFSG.IsQuasisimple.congr e).mp
    (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_comm_sp_four_two hk).1

theorem eq_derived_range_of_component_le_fixed_sp4_two
    {X : Type*} [Group X] {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    (κ : StatedSp 2 k →* X) {model C N P : Subgroup X}
    (hκinj : Function.Injective κ) (hκrange : κ.range = N)
    (hNle_model : N ≤ model) (hNleC : N ≤ C)
    (hPcomp : CFSG.Assembly.IsComponentOf P C) (hPleN : P ≤ N) :
    P = ⁅N, N⁆ := by
  have hNd_le_model : ⁅N, N⁆ ≤ model := (Subgroup.commutator_le_self N).trans hNle_model
  have hNd_leC : ⁅N, N⁆ ≤ C := (Subgroup.commutator_le_self N).trans hNleC
  have hPperf : Group.IsPerfect ↥P :=
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥P).mp
      hPcomp.2.2).1
  have hPleNd : P ≤ ⁅N, N⁆ := by
    rw [← (Subgroup.isPerfect_iff (H := P)).mp hPperf]
    exact Subgroup.commutator_mono hPleN hPleN
  have hNq : CFSG.IsQuasisimple ↥⁅N, N⁆ :=
    isQuasisimple_derivedRange_sp4_two hk hκinj hκrange
  have hNdef : ⁅N, N⁆ = ⁅N, N⁆ ⊓ model :=
    le_antisymm (le_inf le_rfl hNd_le_model) inf_le_left
  have hΓle : ⁅model, model⁆ ≤ model := Subgroup.commutator_le_self model
  have hPleΓ : P ≤ ⁅model, model⁆ :=
    hPleNd.trans (Subgroup.commutator_mono hNle_model hNle_model)
  exact RationalC3Attach.eq_of_isComponentOf_of_fixed_quasisimple_of_le_actual
    (C := C) (M := model) (Γ := ⁅model, model⁆) (H := ⁅N, N⁆) (N := ⁅N, N⁆) (K := P)
    hNdef hΓle hNd_leC hNq hPcomp hPleNd hPleΓ hPcomp.2.2

noncomputable def equivAlt6_of_component_le_fixed_sp4_two
    {X : Type*} {J : Type*} {k : Type} [Group X] [Group J] [Field k] [Finite k] (hk : Nat.card k =
        2)
    (κ : StatedSp 2 k →* X) (η : J →* X) {model C N P : Subgroup X}
    (hκinj : Function.Injective κ) (hκrange : κ.range = N)
    (hNle_model : N ≤ model) (hNleC : N ≤ C)
    (hPcomp : CFSG.Assembly.IsComponentOf P C) (hPleN : P ≤ N)
    (hηinj : Function.Injective η) (hηrange : η.range = P) :
    J ≃* alternatingGroup (Fin 6) := by
  have hP : P = ⁅N, N⁆ :=
    eq_derived_range_of_component_le_fixed_sp4_two hk κ hκinj hκrange hNle_model hNleC
      hPcomp hPleN
  have hηrange' : η.range = ⁅N, N⁆ := by rw [hηrange, hP]
  exact (MonoidHom.ofInjective hηinj).trans
    ((MulEquiv.subgroupCongr hηrange').trans (derivedRangeEquivAlt6 hk hκinj hκrange))

theorem false_of_component_le_fixed_sp4_two
    {X : Type*} {J : Type*} {k : Type} [Group X] [Group J] [Field k] [Finite k] (hk : Nat.card k =
        2)
    (κ : StatedSp 2 k →* X) (η : J →* X) {model C N P : Subgroup X}
    (hκinj : Function.Injective κ) (hκrange : κ.range = N)
    (hNle_model : N ≤ model) (hNleC : N ≤ C)
    (hPcomp : CFSG.Assembly.IsComponentOf P C) (hPleN : P ≤ N)
    (hηinj : Function.Injective η) (hηrange : η.range = P)
    (h28 : IsEmpty (J ≃* alternatingGroup (Fin 6))) : False :=
  h28.false (equivAlt6_of_component_le_fixed_sp4_two hk κ η hκinj hκrange hNle_model hNleC
    hPcomp hPleN hηinj hηrange)

end CFSG.StandardType.F4ExplicitPos.B2SmallJ

end

end
