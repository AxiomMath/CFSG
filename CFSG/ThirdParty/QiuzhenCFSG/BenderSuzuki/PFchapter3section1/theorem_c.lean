module

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_15
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_11_16
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_d
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_e
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Existence
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_7
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIV.theorem
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter3section1

open PFchapter1section1 PFAppendixIII
open PFAppendixIV PFchapter1section3
open MatrixGroups
open Section5
open scoped LinearAlgebra.Projectivization Pointwise

universe u v

/-!
# Peterfalvi, Part II, Chapter III, Theorem C
-/

private theorem equivariantEquiv_of_stabilizer_iff
    {G M Omega X : Type*}
    [Group G] [Group M] [MulAction G Omega]
    (rho : M →* Equiv.Perm X) (eG : G ≃* M)
    (base : Omega) (modelBase : X)
    (htransG : ∀ w : Omega, ∃ g : G, g • base = w)
    (htransM : ∀ z : X, ∃ m : M, rho m modelBase = z)
    (hstab :
      ∀ g : G, g • base = base ↔ rho (eG g) modelBase = modelBase) :
    ∃ eOmega : Omega ≃ X,
      ∀ g : G, ∀ w : Omega,
        eOmega (g • w) = rho (eG g) (eOmega w) := by
  classical
  let rep : Omega → G := fun w => Classical.choose (htransG w)
  have hrep (w : Omega) : rep w • base = w :=
    Classical.choose_spec (htransG w)
  let toFun : Omega → X := fun w => rho (eG (rep w)) modelBase
  have hmodelFix_of_same_target (g h : G)
      (hgh : g • base = h • base) :
      rho (eG (h⁻¹ * g)) modelBase = modelBase := by
    apply (hstab (h⁻¹ * g)).mp
    calc
      (h⁻¹ * g) • base = h⁻¹ • (g • base) := by rw [mul_smul]
      _ = h⁻¹ • (h • base) := by rw [hgh]
      _ = base := inv_smul_smul h base
  have hsame_image (g h : G) (hgh : g • base = h • base) :
      rho (eG g) modelBase = rho (eG h) modelBase := by
    have hfix := hmodelFix_of_same_target g h hgh
    calc
      rho (eG g) modelBase =
          rho (eG h * eG (h⁻¹ * g)) modelBase := by
        congr 2
        rw [← eG.map_mul]
        congr
        group
      _ = rho (eG h) (rho (eG (h⁻¹ * g)) modelBase) := by
        rw [map_mul]
        rfl
      _ = rho (eG h) modelBase := by rw [hfix]
  have htoFun_injective : Function.Injective toFun := by
    intro w z hwz
    have hfixModel :
        rho (eG ((rep z)⁻¹ * rep w)) modelBase = modelBase := by
      calc
        rho (eG ((rep z)⁻¹ * rep w)) modelBase =
            (rho (eG (rep z)))⁻¹
              (rho (eG (rep w)) modelBase) := by
          rw [eG.map_mul, map_mul, eG.map_inv, map_inv]
          rfl
        _ = (rho (eG (rep z)))⁻¹
              (rho (eG (rep z)) modelBase) := by
          exact congrArg (fun y => (rho (eG (rep z)))⁻¹ y) hwz
        _ = modelBase := by simp
    have hfixGroup :
        ((rep z)⁻¹ * rep w) • base = base :=
      (hstab ((rep z)⁻¹ * rep w)).mpr hfixModel
    calc
      w = rep w • base := (hrep w).symm
      _ = rep z • (((rep z)⁻¹ * rep w) • base) := by
        simp [mul_smul]
      _ = rep z • base := by rw [hfixGroup]
      _ = z := hrep z
  have htoFun_surjective : Function.Surjective toFun := by
    intro z
    obtain ⟨m, hm⟩ := htransM z
    let w : Omega := eG.symm m • base
    refine ⟨w, ?_⟩
    change rho (eG (rep w)) modelBase = z
    calc
      rho (eG (rep w)) modelBase =
          rho (eG (eG.symm m)) modelBase := by
        apply hsame_image
        exact (hrep w).trans rfl
      _ = rho m modelBase := by rw [eG.apply_symm_apply]
      _ = z := hm
  let eOmega : Omega ≃ X :=
    Equiv.ofBijective toFun ⟨htoFun_injective, htoFun_surjective⟩
  refine ⟨eOmega, ?_⟩
  intro g w
  change rho (eG (rep (g • w))) modelBase =
    rho (eG g) (rho (eG (rep w)) modelBase)
  calc
    rho (eG (rep (g • w))) modelBase =
        rho (eG (g * rep w)) modelBase := by
      apply hsame_image
      calc
        rep (g • w) • base = g • w := hrep (g • w)
        _ = (g * rep w) • base := by rw [mul_smul, hrep w]
    _ = rho (eG g) (rho (eG (rep w)) modelBase) := by
      rw [eG.map_mul, map_mul]
      rfl


private theorem frobeniusKernel_unique_fixed_point
    {M X : Type*} [Group M] [MulAction M X]
    (htwo : MulAction.IsMultiplyPretransitive M X 2)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer M a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer M a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer M a)))
    (z : F) (hzne : z ≠ 1) :
    ∀ c : X,
      ((((z : MulAction.stabilizer M a) : M) • c = c) ↔ c = a) := by
  intro c
  constructor
  · intro hzc
    by_contra hca
    let cSub : SubMulAction.ofStabilizer M a := ⟨c, hca⟩
    have hzcSub :
        (z : MulAction.stabilizer M a) • cSub = cSub :=
      Subtype.ext hzc
    letI : MulAction.IsMultiplyPretransitive M X 2 := htwo
    letI : MulAction.IsPretransitive M X :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hstabMulti :
        MulAction.IsMultiplyPretransitive
            (MulAction.stabilizer M a)
            (SubMulAction.ofStabilizer M a) 1 :=
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := M) (a := a)).mp htwo
    have hpretrans :
        MulAction.IsPretransitive
          (MulAction.stabilizer M a)
          (SubMulAction.ofStabilizer M a) :=
      (MulAction.is_one_pretransitive_iff
        (G := MulAction.stabilizer M a)
        (α := SubMulAction.ofStabilizer M a)).mp hstabMulti
    have hregular :
        ∀ x y : SubMulAction.ofStabilizer M a,
          ∃! f : F, (f : MulAction.stabilizer M a) • x = y :=
      External.huppert_blackburn_XI_regular_of_isComplement_stabilizer
        hFrob.isComplement' hpretrans
    obtain ⟨k, _hk, hunique⟩ := hregular cSub cSub
    have hzk : z = k := hunique z hzcSub
    have honek : (1 : F) = k := hunique 1 (by simp)
    exact hzne (hzk.trans honek.symm)
  · intro hca
    rw [hca]
    exact (z : MulAction.stabilizer M a).property

private theorem frobeniusKernel_map_normalizer_eq_stabilizer
    {M X : Type*} [Group M] [Finite M] [MulAction M X]
    (htwo : MulAction.IsMultiplyPretransitive M X 2)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer M a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer M a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer M a))) :
    Subgroup.normalizer
        ((F.map (MulAction.stabilizer M a).subtype :
          Subgroup M) : Set M) =
      MulAction.stabilizer M a := by
  classical
  let H := MulAction.stabilizer M a
  let FM : Subgroup M := F.map H.subtype
  apply le_antisymm
  · intro g hg
    haveI : Nontrivial F :=
      (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot
    obtain ⟨zF, hzFne⟩ := exists_ne (1 : F)
    have hzFM : (((zF : H) : M)) ∈ FM :=
      ⟨(zF : H), zF.property, rfl⟩
    have hgInv :
        g⁻¹ ∈ Subgroup.normalizer (FM : Set M) :=
      (Subgroup.normalizer (FM : Set M)).inv_mem hg
    have hconjFM : g⁻¹ * ((zF : H) : M) * (g⁻¹)⁻¹ ∈ FM :=
      (Subgroup.mem_normalizer_iff.mp hgInv ((zF : H) : M)).mp hzFM
    rcases hconjFM with ⟨y, hyF, hyval⟩
    have hyval' : (y : M) = g⁻¹ * ((zF : H) : M) * g := by
      simpa using hyval
    have hfix : ((zF : H) : M) • (g • a) = g • a := by
      calc
        ((zF : H) : M) • (g • a) =
            g • ((g⁻¹ * ((zF : H) : M) * g) • a) := by
          simp [mul_smul, mul_assoc]
        _ = g • ((y : M) • a) := by
          rw [← hyval']
        _ = g • a := by
          exact congrArg (fun q => g • q) y.property
    have hga : g • a = a :=
      (frobeniusKernel_unique_fixed_point
        htwo a b hab F hFrob zF hzFne (g • a)).mp hfix
    exact MulAction.mem_stabilizer_iff.mpr hga
  · intro h hh
    apply Subgroup.le_normalizer_map H.subtype
    refine ⟨⟨h, hh⟩, ?_, rfl⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr hFrob.normal]
    trivial

private theorem transport_action_via_frobenius_kernel
    {G M Omega X : Type*}
    [Group G] [Finite G] [MulAction G Omega]
    [Group M] [Finite M] [MulAction M X]
    (H Q : Subgroup G) (base : Omega)
    (hHbase : H = MulAction.stabilizer G base)
    (hNQ : Subgroup.normalizer (Q : Set G) = H)
    (P : Sylow 2 G) (hQeq : Q = (P : Subgroup G))
    (hQp : IsPGroup 2 Q)
    (rho : M →* Equiv.Perm X)
    (haction : ∀ m : M, ∀ x : X, m • x = rho m x)
    (htwoG : MulAction.IsMultiplyPretransitive G Omega 2)
    (htwoM : MulAction.IsMultiplyPretransitive M X 2)
    (eG : G ≃* M)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer M a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer M a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer M a)))
    (hFcard : Nat.card F = Nat.card Q) :
    ∃ eG' : G ≃* M, ∃ eOmega : Omega ≃ X,
      ∀ g : G, ∀ w : Omega,
        eOmega (g • w) = rho (eG' g) (eOmega w) := by
  classical
  let HM := MulAction.stabilizer M a
  let FM : Subgroup M := F.map HM.subtype
  have hFMcard : Nat.card FM = Nat.card Q := by
    calc
      Nat.card FM = Nat.card F :=
        Subgroup.card_map_of_injective HM.subtype_injective
      _ = Nat.card Q := hFcard
  obtain ⟨r, hrQ⟩ := hQp.exists_card_eq
  have hFMp : IsPGroup 2 FM := by
    exact IsPGroup.of_card (by rw [hFMcard, hrQ])
  obtain ⟨Pstd, hFMle⟩ := hFMp.exists_le_sylow
  let Pmodel : Sylow 2 M :=
    P.mapSurjective (f := eG.toMonoidHom) eG.surjective
  have hPmodelCard : Nat.card Pmodel = Nat.card Q := by
    calc
      Nat.card Pmodel = Nat.card P := by
        simpa [Pmodel, Sylow.coe_mapSurjective] using
          Subgroup.card_map_of_injective
            (K := (P : Subgroup G)) (f := eG.toMonoidHom) eG.injective
      _ = Nat.card Q := by rw [hQeq]
  have hPstdCard : Nat.card Pstd = Nat.card Q := by
    calc
      Nat.card Pstd = Nat.card Pmodel :=
        Nat.card_congr (Sylow.equiv Pstd Pmodel).toEquiv
      _ = Nat.card Q := hPmodelCard
  have hFMeq : FM = (Pstd : Subgroup M) := by
    exact Subgroup.eq_of_le_of_card_ge hFMle (by
      rw [hPstdCard, hFMcard])
  let c : M := Classical.choose (MulAction.exists_smul_eq M Pmodel Pstd)
  have hc : c • Pmodel = Pstd :=
    Classical.choose_spec (MulAction.exists_smul_eq M Pmodel Pstd)
  let eG' : G ≃* M := eG.trans (MulAut.conj c)
  have hmapQ : Q.map eG'.toMonoidHom = FM := by
    calc
      Q.map eG'.toMonoidHom =
          (Q.map eG.toMonoidHom).map
            (MulAut.conj c).toMonoidHom := by
        rw [Subgroup.map_map]
        rfl
      _ = ((Pmodel : Sylow 2 M) : Subgroup M).map
            (MulAut.conj c).toMonoidHom := by
        rw [hQeq]
        simp [Pmodel, Sylow.coe_mapSurjective]
      _ = MulAut.conj c • ((Pmodel : Sylow 2 M) : Subgroup M) := rfl
      _ = ((c • Pmodel : Sylow 2 M) : Subgroup M) :=
        Sylow.coe_subgroup_smul.symm
      _ = (Pstd : Subgroup M) := by rw [hc]
      _ = FM := hFMeq.symm
  have hnormFM :
      Subgroup.normalizer (FM : Set M) = HM := by
    exact frobeniusKernel_map_normalizer_eq_stabilizer
      htwoM a b hab F hFrob
  have hmapH : H.map eG'.toMonoidHom = HM := by
    calc
      H.map eG'.toMonoidHom =
          (Subgroup.normalizer (Q : Set G)).map eG'.toMonoidHom := by
        rw [hNQ]
      _ = Subgroup.normalizer
          ((Q.map eG'.toMonoidHom : Subgroup M) : Set M) := by
        exact Subgroup.map_normalizer_eq_of_bijective Q eG'.bijective
      _ = Subgroup.normalizer (FM : Set M) := by rw [hmapQ]
      _ = HM := hnormFM
  have hstab :
      ∀ g : G, g • base = base ↔ rho (eG' g) a = a := by
    intro g
    rw [← MulAction.mem_stabilizer_iff]
    rw [← hHbase]
    constructor
    · intro hg
      have hmem : eG' g ∈ HM := by
        rw [← hmapH]
        exact ⟨g, hg, rfl⟩
      rw [← haction]
      exact MulAction.mem_stabilizer_iff.mp hmem
    · intro hg
      have hmemM : eG' g ∈ HM := by
        exact MulAction.mem_stabilizer_iff.mpr (by simpa [haction] using hg)
      rw [← hmapH] at hmemM
      rcases hmemM with ⟨y, hy, hyeq⟩
      have hyg : y = g := eG'.injective hyeq
      simpa [hyg] using hy
  have htransG : ∀ w : Omega, ∃ g : G, g • base = w := by
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwoG
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    intro w
    exact MulAction.exists_smul_eq G base w
  have htransM : ∀ z : X, ∃ m : M, rho m a = z := by
    letI : MulAction.IsMultiplyPretransitive M X 2 := htwoM
    letI : MulAction.IsPretransitive M X :=
      MulAction.isPretransitive_of_is_two_pretransitive
    intro z
    obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M a z
    exact ⟨m, by simpa [haction] using hm⟩
  obtain ⟨eOmega, heOmega⟩ :=
    equivariantEquiv_of_stabilizer_iff
      rho eG' base a htransG htransM hstab
  exact ⟨eG', eOmega, heOmega⟩

private theorem card_pgl2
    {K : Type*} [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let GL2 := GL (Fin 2) K
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalarInj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 =>
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range =
          Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalarInj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card PGL2 := by
    calc
      centerGL.index = mkPGL.ker.index := by
        rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card PGL2 := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card PGL2 =
        Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) *
        (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) *
        (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

private def specialLinearEquiv_of_ringEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    Matrix.SpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) L := by
  let f : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.SpecialLinearGroup (Fin 2) L :=
    Matrix.SpecialLinearGroup.map e.toRingHom
  let g : Matrix.SpecialLinearGroup (Fin 2) L →*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]
  · apply MonoidHom.ext
    intro A
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [f, g, Matrix.SpecialLinearGroup.map_apply_coe]

private def projectiveSpecialLinearEquiv_of_ringEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) L := by
  let eSL := specialLinearEquiv_of_ringEquiv e
  apply QuotientGroup.congr
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) L)) eSL
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (MulEquivClass.apply_mem_center_iff eSL).2 hB
  · intro hA
    refine ⟨eSL.symm A, ?_, eSL.apply_symm_apply A⟩
    exact (MulEquivClass.apply_mem_center_iff eSL.symm).2 hA

private noncomputable def finTwoSemilinearEquiv_of_ringEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    [RingHomInvPair e.toRingHom e.symm.toRingHom]
    [RingHomInvPair e.symm.toRingHom e.toRingHom] :
    (Fin 2 → K) ≃ₛₗ[e.toRingHom] (Fin 2 → L) where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := by
    ext i
    simp
  right_inv v := by
    ext i
    simp
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp

private noncomputable def projectiveEquiv_of_ringEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    ℙ K (Fin 2 → K) ≃ ℙ L (Fin 2 → L) := by
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  let eV := finTwoSemilinearEquiv_of_ringEquiv e
  let f : ℙ K (Fin 2 → K) → ℙ L (Fin 2 → L) :=
    Projectivization.map eV.toLinearMap eV.injective
  let g : ℙ L (Fin 2 → L) → ℙ K (Fin 2 → K) :=
    Projectivization.map eV.symm.toLinearMap eV.symm.injective
  refine ⟨f, g, ?_, ?_⟩
  · intro z
    induction z using Projectivization.ind with
    | h v hv =>
        change Projectivization.map eV.symm.toLinearMap eV.symm.injective
            (Projectivization.map eV.toLinearMap eV.injective
              (Projectivization.mk K v hv)) =
          Projectivization.mk K v hv
        rw [Projectivization.map_mk, Projectivization.map_mk,
          Projectivization.mk_eq_mk_iff']
        refine ⟨1, ?_⟩
        simp only [one_smul]
        change v = eV.invFun (eV.toFun v)
        exact (eV.left_inv v).symm
  · intro z
    induction z using Projectivization.ind with
    | h v hv =>
        change Projectivization.map eV.toLinearMap eV.injective
            (Projectivization.map eV.symm.toLinearMap eV.symm.injective
              (Projectivization.mk L v hv)) =
          Projectivization.mk L v hv
        rw [Projectivization.map_mk, Projectivization.map_mk,
          Projectivization.mk_eq_mk_iff']
        refine ⟨1, ?_⟩
        simp only [one_smul]
        change v = eV.toFun (eV.invFun v)
        exact (eV.right_inv v).symm

private theorem projectiveEquiv_natural
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (A : Matrix.SpecialLinearGroup (Fin 2) K)
    (z : ℙ K (Fin 2 → K)) :
    projectiveEquiv_of_ringEquiv e
        (Matrix.SpecialLinearGroup.toLin' A • z) =
      Matrix.SpecialLinearGroup.toLin'
        (Matrix.SpecialLinearGroup.map e.toRingHom A) •
          projectiveEquiv_of_ringEquiv e z := by
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e
  induction z using Projectivization.ind with
  | h v hv =>
      change Projectivization.map
          (finTwoSemilinearEquiv_of_ringEquiv e).toLinearMap
          (finTwoSemilinearEquiv_of_ringEquiv e).injective
          (Projectivization.mk K
            (Matrix.SpecialLinearGroup.toLin' A v) _) =
        Projectivization.mk L
          (Matrix.SpecialLinearGroup.toLin'
            (Matrix.SpecialLinearGroup.map e.toRingHom A)
            (finTwoSemilinearEquiv_of_ringEquiv e v)) _
      change Projectivization.mk L
          ((finTwoSemilinearEquiv_of_ringEquiv e).toLinearMap
            (Matrix.SpecialLinearGroup.toLin' A v)) _ = _
      apply (Projectivization.mk_eq_mk_iff' L _ _ _ _).2
      refine ⟨1, ?_⟩
      simp only [one_smul]
      ext i
      change
        (((A : Matrix (Fin 2) (Fin 2) K).map e.toRingHom).mulVec
            (e.toRingHom ∘ v)) i =
          e.toRingHom
            (((A : Matrix (Fin 2) (Fin 2) K).mulVec v) i)
      exact (RingHom.map_mulVec e.toRingHom
        (A : Matrix (Fin 2) (Fin 2) K) v i).symm

set_option maxHeartbeats 800000

/--
The opening case of Chapter III, Section 1: if V = 1, Proposition 6(c)
makes the action Zassenhaus and Huppert-Blackburn XI.11.16 gives the natural
PSL(2,q) or Suzuki action.  This is the complete assertion made immediately
before Hypothesis (C1) in docs/PFchapter3.tex.
-/
public theorem case_v_eq_bot
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q V : Subgroup G) (t : G)
    (hA : HypothesisA G Omega H D Q t)
    (hV_eq : V = peterfalviV D t) (hV_bot : V = ⊥) :
    zassenhausConclusion G Omega := by
  classical
  letI : FaithfulSMul G Omega := hA.A2
  letI : Fintype Omega := Fintype.ofFinite Omega
  have hdegreeNat : Nat.card Omega = Nat.card Q + 1 :=
    hypothesisA1_card_space_eq_card_Q_add_one_of_hypothesis H D Q t hA.A1
  have hdegree : Fintype.card Omega = Nat.card Q + 1 := by
    simpa [Nat.card_eq_fintype_card] using hdegreeNat
  have horder :
      Nat.card G =
        (Nat.card Q + 1) * Nat.card Q * Nat.card D := by
    haveI : MulAction.IsMultiplyPretransitive G Omega 2 :=
      hA.A1.two_transitive
    haveI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    obtain ⟨base, hHbase⟩ := hA.A1.point_stabilizer
    have hHindex : H.index = Nat.card Omega := by
      rw [hHbase]
      exact MulAction.index_stabilizer_of_transitive G base
    let QH : Subgroup H := Q.subgroupOf H
    let DH : Subgroup H := D.subgroupOf H
    haveI : QH.Normal := by
      simpa [QH] using hA.A1.Q_normal_in_H
    have hdisjH : Disjoint QH DH := by
      rw [Subgroup.disjoint_def]
      intro x hxQ hxD
      apply Subtype.ext
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
        (Subgroup.disjoint_def.mp hA.A1.Q_disjoint_D)
          (by simpa [QH, Subgroup.mem_subgroupOf] using hxQ)
          (by simpa [DH, Subgroup.mem_subgroupOf] using hxD)
      simpa using hxbot
    have hsupH : QH ⊔ DH = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA.A1.Q_le_H hA.A1.D_le_H]
      rw [hA.A1.Q_sup_D, Subgroup.subgroupOf_self]
    have hcompH : QH.IsComplement' DH :=
      isComplement'_of_disjoint_sup_eq_top_of_normal QH DH hdisjH hsupH
    have hHcard : Nat.card H = Nat.card Q * Nat.card D := by
      have hcard := hcompH.card_mul
      rw [natCard_subgroupOf_eq Q H hA.A1.Q_le_H,
        natCard_subgroupOf_eq D H hA.A1.D_le_H] at hcard
      exact hcard.symm
    calc
      Nat.card G = Nat.card H * H.index := H.card_mul_index.symm
      _ = (Nat.card Q * Nat.card D) * (Nat.card Q + 1) := by
        rw [hHcard, hHindex, hdegreeNat]
      _ = (Nat.card Q + 1) * Nat.card Q * Nat.card D := by ring
  obtain ⟨base, hHbase⟩ := hA.A1.point_stabilizer
  let beta : Omega := t⁻¹ • base
  have hbase_ne_beta : base ≠ beta := by
    intro heq
    apply hA.A1.t_not_mem_H
    have htinv : t⁻¹ ∈ MulAction.stabilizer G base := by
      change t⁻¹ • base = base
      exact heq.symm
    have htinvH : t⁻¹ ∈ H := by simpa [hHbase] using htinv
    simpa using H.inv_mem htinvH
  have hD_stabilizers :
      D = MulAction.stabilizer G base ⊓
        MulAction.stabilizer G beta := by
    simpa [beta, hHbase, rightConjugate_stabilizer] using hA.A1.D_eq
  have hatMostTwo :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c) := by
    intro g hg a b c hab hac hbc hfix
    obtain ⟨k, hka, hkb⟩ :=
      (MulAction.is_two_pretransitive_iff.mp hA.A1.two_transitive)
        hab hbase_ne_beta
    let x : G := k * g * k⁻¹
    have hxbase : x • base = base := by
      calc
        x • base = k • (g • (k⁻¹ • base)) := by
          simp [x, mul_smul, mul_assoc]
        _ = k • (g • a) := by
          apply congrArg (fun z => k • (g • z))
          simpa using congrArg (fun z => k⁻¹ • z) hka.symm
        _ = k • a := by rw [hfix.1]
        _ = base := hka
    have hxbeta : x • beta = beta := by
      calc
        x • beta = k • (g • (k⁻¹ • beta)) := by
          simp [x, mul_smul, mul_assoc]
        _ = k • (g • b) := by
          apply congrArg (fun z => k • (g • z))
          simpa using congrArg (fun z => k⁻¹ • z) hkb.symm
        _ = k • b := by rw [hfix.2.1]
        _ = beta := hkb
    have hxthird : x • (k • c) = k • c := by
      simp [x, mul_smul, mul_assoc, hfix.2.2]
    let X : Subgroup G := Subgroup.zpowers x
    have hXleD : X ≤ D := by
      rw [hD_stabilizers]
      exact le_inf
        (Subgroup.zpowers_le_of_mem
          (MulAction.mem_stabilizer_iff.mpr hxbase))
        (Subgroup.zpowers_le_of_mem
          (MulAction.mem_stabilizer_iff.mpr hxbeta))
    have hbaseFixed : base ∈ fixedPointsOfSubgroup G Omega X := by
      intro y hy
      exact MulAction.mem_stabilizer_iff.mp
        ((Subgroup.zpowers_le_of_mem
          (MulAction.mem_stabilizer_iff.mpr hxbase)) hy)
    have hbetaFixed : beta ∈ fixedPointsOfSubgroup G Omega X := by
      intro y hy
      exact MulAction.mem_stabilizer_iff.mp
        ((Subgroup.zpowers_le_of_mem
          (MulAction.mem_stabilizer_iff.mpr hxbeta)) hy)
    have hthirdFixed : k • c ∈ fixedPointsOfSubgroup G Omega X := by
      intro y hy
      exact MulAction.mem_stabilizer_iff.mp
        ((Subgroup.zpowers_le_of_mem
          (MulAction.mem_stabilizer_iff.mpr hxthird)) hy)
    have hbase_ne_third : base ≠ k • c := by
      intro heq
      apply hac
      apply (MulAction.toPerm k).injective
      simpa [hka] using heq
    have hbeta_ne_third : beta ≠ k • c := by
      intro heq
      apply hbc
      apply (MulAction.toPerm k).injective
      simpa [hkb] using heq
    let p0 : {w : Omega // w ∈ fixedPointsOfSubgroup G Omega X} :=
      ⟨base, hbaseFixed⟩
    let p1 : {w : Omega // w ∈ fixedPointsOfSubgroup G Omega X} :=
      ⟨beta, hbetaFixed⟩
    let p2 : {w : Omega // w ∈ fixedPointsOfSubgroup G Omega X} :=
      ⟨k • c, hthirdFixed⟩
    let f : Fin 3 →
        {w : Omega // w ∈ fixedPointsOfSubgroup G Omega X} :=
      ![p0, p1, p2]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso; exact hbase_ne_beta (by simpa [f, p0, p1] using hij)
      · exfalso; exact hbase_ne_third (by simpa [f, p0, p2] using hij)
      · exfalso; exact hbase_ne_beta (by simpa [f, p0, p1] using hij.symm)
      · rfl
      · exfalso; exact hbeta_ne_third (by simpa [f, p1, p2] using hij)
      · exfalso; exact hbase_ne_third (by simpa [f, p0, p2] using hij.symm)
      · exfalso; exact hbeta_ne_third (by simpa [f, p1, p2] using hij.symm)
      · rfl
    have hfixedCard :
        3 ≤ Nat.card
          {w : Omega // w ∈ fixedPointsOfSubgroup G Omega X} := by
      simpa using Nat.card_le_card_of_injective f hf
    obtain ⟨d, hd⟩ :=
      proposition_6_c H D Q X t hA.A1 hXleD hfixedCard
    have hdBot : rightConjugate X (d : G) ≤ ⊥ := by
      simpa [← hV_eq, hV_bot] using hd
    have hxConjBot :
        (MulAut.conj (d : G)⁻¹) x ∈ (⊥ : Subgroup G) := by
      apply hdBot
      exact ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hxone : x = 1 := by
      apply (MulAut.conj (d : G)⁻¹).injective
      simpa using hxConjBot
    apply hg
    have hconj := congrArg (fun y : G => k⁻¹ * y * k) hxone
    simpa [x, mul_assoc] using hconj
  have hcoreBot : pPrimeCore 2 G = ⊥ := by
    rw [proposition_1_e H D Q t hA.A1 hA.A3]
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      apply eq_of_smul_eq_smul (α := Omega)
      intro w
      have hxall : ∀ w : Omega, x • w = w := by
        simpa [pointStabilizerCore, MulAction.mem_stabilizer_iff] using hx
      simpa using hxall w
    · exact bot_le
  have hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b := by
    rintro ⟨R, hRnormal, hRne, hregular⟩
    let orbitMap : R → Omega := fun r => (r : G) • base
    have horbitBij : Function.Bijective orbitMap := by
      constructor
      · intro r s hrs
        obtain ⟨u, hu, hu_unique⟩ := hregular base (orbitMap r)
        have hur : u = r := (hu_unique r rfl).symm
        have hus : u = s :=
          (hu_unique s (by simpa [orbitMap] using hrs.symm)).symm
        exact hur.symm.trans hus
      · intro w
        obtain ⟨r, hr, _⟩ := hregular base w
        exact ⟨r, hr⟩
    have hRcard : Nat.card R = Nat.card Omega :=
      Nat.card_congr (Equiv.ofBijective orbitMap horbitBij)
    have hRodd : Odd (Nat.card R) := by
      rw [hRcard, hdegreeNat]
      exact hA.A1.Q_even.add_one
    have hRbot :
        R = ⊥ :=
      (pPrimeCore_eq_bot_iff.mp hcoreBot) R hRnormal
        hRodd.coprime_two_left
    exact hRne hRbot
  have hQgt : 2 < Nat.card Q := by
    rcases hA.A3 with ⟨E, hEcard, hEsq⟩
    have hEp : IsPGroup 2 E := by
      exact IsPGroup.of_card (n := 2) (by simp [hEcard])
    obtain ⟨SE, hEle⟩ := hEp.exists_le_sylow
    obtain ⟨P, hPleQ⟩ := proposition_1_c H D Q t hA.A1
    have hE_le_SE : Nat.card E ≤ Nat.card SE :=
      Nat.card_le_card_of_injective
        (fun x : E => (⟨x, hEle x.property⟩ : SE))
        (fun x y h => Subtype.ext
          (show (x : G) = (y : G) from
            congrArg (fun z : SE => (z : G)) h))
    have hSE_eq_P : Nat.card SE = Nat.card P :=
      Nat.card_congr (Sylow.equiv SE P).toEquiv
    have hP_le_Q : Nat.card P ≤ Nat.card Q :=
      Nat.card_le_card_of_injective
        (fun x : P => (⟨x, hPleQ x.property⟩ : Q))
        (fun x y h => Subtype.ext
          (show (x : G) = (y : G) from
            congrArg (fun z : Q => (z : G)) h))
    omega
  obtain ⟨p, f, hp, hf, hn, hcases⟩ :=
    External.huppert_blackburn_XI_11_16_zassenhaus_classification.{u, v, 0}
      (Nat.card Q) (Nat.card D)
      hdegree horder hA.A1.two_transitive hatMostTwo hnoRegularNormal
  have hpTwo : p = 2 := by
    rcases hp.eq_two_or_odd' with hp2 | hpodd
    · exact hp2
    · have hQodd : Odd (Nat.card Q) := by
        rw [hn]
        exact hpodd.pow
      exact (Nat.not_even_iff_odd.mpr hQodd hA.A1.Q_even).elim
  have hQp : IsPGroup 2 Q := by
    exact IsPGroup.of_card (by rw [hn, hpTwo])
  obtain ⟨P, hPleQ⟩ := proposition_1_c H D Q t hA.A1
  have hQeq : Q = (P : Subgroup G) :=
    P.is_maximal' hQp hPleQ
  have hNQ : Subgroup.normalizer (Q : Set G) = H :=
    (proposition_1_d H D Q t hA.A1).1
  rcases hcases with hPGL | hPSL | hsharp | hSuzuki
  · rcases hPGL with
      ⟨K, hKfield, hKfinite, hKcard, ⟨eG⟩⟩
    letI : Field K := hKfield
    letI : Finite K := hKfinite
    letI : Fintype K := Fintype.ofFinite K
    letI : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk
        Matrix.ProjGenLinGroup.mk_surjective
    have hKcardPow : Nat.card K = 2 ^ f := by
      calc
        Nat.card K = Nat.card Q := hKcard
        _ = p ^ f := hn
        _ = 2 ^ f := by rw [hpTwo]
    letI : CharP K 2 :=
      charP_of_card_eq_prime_pow (by
        simpa [Nat.card_eq_fintype_card] using hKcardPow)
    rcases External.huppert_blackburn_XI_example_1_3_a K with
      ⟨hProjCard, rhoPGL, iota, hrhoPGL, hiota,
        hiotaApply, hrhoPGLApply, _hiotaNormal, _hiotaIndex,
        hsharpTriple, hlarge, _hsmallTwo, _hsmallThree⟩
    obtain ⟨rhoK, hrhoK, hrhoKApply, htwoK⟩ :=
      External.huppert_II_6_11_projective_action
        (K := K) 2 (by omega)
    have hcompatK
        (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
        rhoPGL (iota x) = rhoK x := by
      rcases QuotientGroup.mk'_surjective
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) x with
        ⟨A, rfl⟩
      apply Equiv.ext
      intro z
      rw [hiotaApply]
      rw [hrhoPGLApply _ _ _ rfl, hrhoKApply]
    letI : MulAction
        (Matrix.ProjGenLinGroup (Fin 2) K)
        (ℙ K (Fin 2 → K)) :=
      MulAction.compHom (ℙ K (Fin 2 → K)) rhoPGL
    letI : FaithfulSMul
        (Matrix.ProjGenLinGroup (Fin 2) K)
        (ℙ K (Fin 2 → K)) :=
      faithfulSMul_iff.mpr (by
        intro g hg
        apply hrhoPGL
        apply Equiv.ext
        intro z
        have hgz := hg z
        change rhoPGL g z = z at hgz
        calc
          rhoPGL g z = z := hgz
          _ = rhoPGL 1 z := by rw [map_one]; rfl)
    have htwoPGL :
        MulAction.IsMultiplyPretransitive
          (Matrix.ProjGenLinGroup (Fin 2) K)
          (ℙ K (Fin 2 → K)) 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro a b c d hab hcd
      rcases htwoK a b c d hab hcd with ⟨x, hxa, hxb⟩
      refine ⟨iota x, ?_, ?_⟩
      · change rhoPGL (iota x) a = c
        rw [hcompatK]
        exact hxa
      · change rhoPGL (iota x) b = d
        rw [hcompatK]
        exact hxb
    have hatMostTwoPGL :
        ∀ g : Matrix.ProjGenLinGroup (Fin 2) K, g ≠ 1 →
          ∀ a b c : ℙ K (Fin 2 → K),
            a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c) := by
      intro g hg a b c hab hac hbc hfix
      have hu :=
        hsharpTriple a b c a b c hab hac hbc hab hac hbc
      apply hg
      change rhoPGL g a = a ∧ rhoPGL g b = b ∧ rhoPGL g c = c at hfix
      have honeFix :
          rhoPGL (1 : Matrix.ProjGenLinGroup (Fin 2) K) a = a ∧
            rhoPGL (1 : Matrix.ProjGenLinGroup (Fin 2) K) b = b ∧
              rhoPGL (1 : Matrix.ProjGenLinGroup (Fin 2) K) c = c := by
        rw [map_one]
        exact ⟨rfl, rfl, rfl⟩
      exact hu.unique hfix honeFix
    have hKgtThree : 3 < Nat.card K := by
      rw [hKcard]
      rcases hA.A1.Q_even with ⟨k, hk⟩
      omega
    rcases hlarge hKgtThree with
      ⟨_hsimple, _hnoncomm, hnoRegularPGL⟩
    letI : Fintype (ℙ K (Fin 2 → K)) :=
      Fintype.ofFinite (ℙ K (Fin 2 → K))
    have hProjCardQ :
        Fintype.card (ℙ K (Fin 2 → K)) = Nat.card Q + 1 := by
      rw [← Nat.card_eq_fintype_card, hProjCard, hKcard]
    have hProjGt :
        1 < Fintype.card (ℙ K (Fin 2 → K)) := by
      rw [hProjCardQ]
      omega
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hProjGt
    have hnoRegularPGL' :
        ¬ ∃ R : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K),
          R.Normal ∧ R ≠ ⊥ ∧
            ∀ x y : ℙ K (Fin 2 → K), ∃! r : R,
              (r : Matrix.ProjGenLinGroup (Fin 2) K) • x = y := by
      change ¬ ∃ R : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K),
        R.Normal ∧ R ≠ ⊥ ∧
          ∀ x y : ℙ K (Fin 2 → K), ∃! r : R,
            rhoPGL (r : Matrix.ProjGenLinGroup (Fin 2) K) x = y
      exact hnoRegularPGL
    obtain ⟨F, hFrob⟩ :=
      External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
        htwoPGL hatMostTwoPGL hnoRegularPGL' a b hab
    have hFcard :
        Nat.card F = Nat.card Q :=
      External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
        (Nat.card Q) hProjCardQ htwoPGL a b hab F hFrob
    have hactionPGL :
        ∀ g : Matrix.ProjGenLinGroup (Fin 2) K,
          ∀ z : ℙ K (Fin 2 → K), g • z = rhoPGL g z := by
      intro g z
      rfl
    obtain ⟨eGPGL, eOmegaK, hequivK⟩ :=
      transport_action_via_frobenius_kernel
        H Q base hHbase hNQ P hQeq hQp
        rhoPGL hactionPGL hA.A1.two_transitive htwoPGL
        eG a b hab F hFrob hFcard
    have htwoZero : (2 : K) = 0 :=
      CharP.cast_eq_zero K 2
    have hnegOne : (-1 : K) = 1 := by
      apply (neg_eq_iff_add_eq_zero).2
      rw [show (1 : K) + 1 = 2 by norm_num, htwoZero]
    have hcenter :
        Nat.card
            (Subgroup.center
              (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 :=
      External.huppert614_card_center_of_neg_one_eq_one hnegOne
    have hPSLcard :=
      External.huppert614_card_psl_mul_center (K := K)
    rw [hcenter, mul_one] at hPSLcard
    have hPSLPGLcard :
        Nat.card
            (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
          Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) :=
      hPSLcard.trans card_pgl2.symm
    let ePSLPGL :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
          Matrix.ProjGenLinGroup (Fin 2) K :=
      MulEquiv.ofBijective iota
        ((Nat.bijective_iff_injective_and_card iota).2
          ⟨hiota, hPSLPGLcard⟩)
    have hePSLPGLApply
        (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
        ePSLPGL x = iota x := rfl
    have hcompatEquivK
        (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
        rhoPGL (ePSLPGL x) = rhoK x := by
      rw [hePSLPGLApply, hcompatK]
    let KB := BinaryGaloisField f
    letI : Fintype KB := Fintype.ofFinite KB
    have hKBcard : Nat.card KB = 2 ^ f := by
      simpa [KB, BinaryGaloisField] using
        GaloisField.card 2 f (Nat.ne_of_gt hf)
    let eK : K ≃+* KB :=
      FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          hKcardPow, hKBcard])
    let ePSL :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) KB :=
      projectiveSpecialLinearEquiv_of_ringEquiv eK
    let eProj :
        ℙ K (Fin 2 → K) ≃ ℙ KB (Fin 2 → KB) :=
      projectiveEquiv_of_ringEquiv eK
    obtain ⟨rhoB, _hrhoB, hrhoBApply, _htwoB⟩ :=
      External.huppert_II_6_11_projective_action
        (K := KB) 2 (by omega)
    have hfieldCompat
        (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
        (z : ℙ K (Fin 2 → K)) :
        eProj (rhoK x z) = rhoB (ePSL x) (eProj z) := by
      rcases QuotientGroup.mk'_surjective
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) x with
        ⟨A, rfl⟩
      rw [hrhoKApply]
      change
        projectiveEquiv_of_ringEquiv eK
            (Matrix.SpecialLinearGroup.toLin' A • z) =
          rhoB (QuotientGroup.mk'
            (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) KB))
            (Matrix.SpecialLinearGroup.map eK.toRingHom A))
            (projectiveEquiv_of_ringEquiv eK z)
      rw [hrhoBApply]
      change
        projectiveEquiv_of_ringEquiv eK
            (Matrix.SpecialLinearGroup.toLin' A • z) =
          Matrix.SpecialLinearGroup.toLin'
              (Matrix.SpecialLinearGroup.map eK.toRingHom A) •
            projectiveEquiv_of_ringEquiv eK z
      exact projectiveEquiv_natural eK A z
    let eModel :
        G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) KB :=
      (eGPGL.trans ePSLPGL.symm).trans ePSL
    let eOmega : Omega ≃ ℙ KB (Fin 2 → KB) :=
      eOmegaK.trans eProj
    have hequivModel :
        ∀ g : G, ∀ w : Omega,
          eOmega (g • w) = rhoB (eModel g) (eOmega w) := by
      intro g w
      change eProj (eOmegaK (g • w)) =
        rhoB (ePSL (ePSLPGL.symm (eGPGL g)))
          (eProj (eOmegaK w))
      rw [hequivK]
      have hpglCompat :
          rhoPGL (eGPGL g) =
            rhoK (ePSLPGL.symm (eGPGL g)) := by
        rw [← hcompatEquivK]
        simp
      rw [hpglCompat]
      exact hfieldCompat (ePSLPGL.symm (eGPGL g)) (eOmegaK w)
    refine ⟨Nat.card Q, ⟨f, by rw [hn, hpTwo]⟩, hQgt, Or.inl ?_⟩
    refine ⟨f, Nat.ne_of_gt hf, by rw [hn, hpTwo], ?_⟩
    let eTop :
        (⊤ : Subgroup G) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) KB :=
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).trans eModel
    refine ⟨eTop, rhoB, eOmega, ?_, ?_⟩
    · intro A z
      exact hrhoBApply A z
    · intro l w
      simpa [eTop, eModel, eOmega] using hequivModel (l : G) w
  · have hoddTwo : Odd 2 := by simpa [hpTwo] using hPSL.1
    rcases hoddTwo with ⟨k, hk⟩
    omega
  · have hoddTwo : Odd 2 := by simpa [hpTwo] using hsharp.1
    rcases hoddTwo with ⟨k, hk⟩
    omega
  · rcases hSuzuki with
      ⟨_hp2, m, hm, hQcardSuzuki, ⟨eG⟩⟩
    let K := BinaryGaloisField (2 * m + 1)
    let pi : K ≃+* K :=
      iterateFrobeniusEquiv K 2 (m + 1)
    have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
      intro x
      exact iterateFrobeniusEquiv_def K 2 (m + 1) x
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let pcoord : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (m + 1)) * x ^ 2 +
            y ^ (2 ^ (m + 1)), y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => pcoord z.1 z.2
    have hnatural :=
      External.huppert_blackburn_XI_3_3 m hm pi hpi
    rcases hnatural with
      ⟨hpresRaw, _hfull, hfaithfulRaw, htwoRaw,
        hthreeRaw, hOcardRaw, hMcardRaw, _hstabilizer⟩
    have hpres :
        ∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
          ((Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv • z) ∈ O := by
      simpa only [K, pinf, pcoord, O, hpi] using hpresRaw
    have hOcard :
        Nat.card {z : ℙ K (Fin 4 → K) // z ∈ O} =
          (2 ^ (2 * m + 1)) ^ 2 + 1 := by
      simpa only [K, pinf, pcoord, O, hpi] using hOcardRaw
    have hMcard :
        Nat.card (SuzukiMatrixGroup m) =
          ((2 ^ (2 * m + 1)) ^ 2 + 1) *
            (2 ^ (2 * m + 1)) ^ 2 *
              (2 ^ (2 * m + 1) - 1) := by
      simpa only [K] using hMcardRaw
    let linRep : SuzukiMatrixGroup m →*
        LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
      Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
        (SuzukiMatrixGroup m).subtype
    letI : MulAction (SuzukiMatrixGroup m)
        (ℙ K (Fin 4 → K)) :=
      MulAction.compHom (ℙ K (Fin 4 → K)) linRep
    let Xmodel : SubMulAction (SuzukiMatrixGroup m)
        (ℙ K (Fin 4 → K)) :=
      { carrier := O
        smul_mem' := by
          intro g z hz
          exact hpres g z hz }
    let xAction : MulAction (SuzukiMatrixGroup m) Xmodel :=
      Xmodel.mulAction
    letI : MulAction (SuzukiMatrixGroup m) Xmodel := xAction
    let smulX : SuzukiMatrixGroup m → Xmodel → Xmodel :=
      xAction.smul
    let rho : SuzukiMatrixGroup m →* Equiv.Perm Xmodel :=
      MulAction.toPermHom (SuzukiMatrixGroup m) Xmodel
    have haction :
        ∀ g : SuzukiMatrixGroup m, ∀ z : Xmodel,
          smulX g z = rho g z := by
      intro g z
      rfl
    have hfaithfulX :
        ∀ g : SuzukiMatrixGroup m,
          (∀ z : Xmodel, smulX g z = z) → g = 1 := by
      intro g hg
      apply hfaithfulRaw g
      intro z hz
      let zX : Xmodel := ⟨z, hz⟩
      have hfix := congrArg Subtype.val (hg zX)
      change
        ((Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv • z) = z at hfix
      exact hfix
    have htwoModel :
        MulAction.IsMultiplyPretransitive
          (SuzukiMatrixGroup m) Xmodel 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro a b c d hab hcd
      have habRaw : (a : ℙ K (Fin 4 → K)) ≠ b := by
        intro h
        exact hab (Subtype.ext h)
      have hcdRaw : (c : ℙ K (Fin 4 → K)) ≠ d := by
        intro h
        exact hcd (Subtype.ext h)
      rcases htwoRaw (a : ℙ K (Fin 4 → K)) b c d
          a.property b.property c.property d.property
          habRaw hcdRaw with
        ⟨g, hga, hgb⟩
      exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩
    have hatMostTwoModel :
        ∀ g : SuzukiMatrixGroup m, g ≠ 1 →
          ∀ a b c : Xmodel,
            a ≠ b → a ≠ c → b ≠ c →
            ¬ (smulX g a = a ∧ smulX g b = b ∧ smulX g c = c) := by
      intro g hg a b c hab hac hbc hfix
      apply hg
      apply hthreeRaw g
      refine ⟨a, b, c, a.property, b.property, c.property, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · intro h
        exact hab (Subtype.ext h)
      · intro h
        exact hac (Subtype.ext h)
      · intro h
        exact hbc (Subtype.ext h)
      · exact congrArg Subtype.val hfix.1
      · exact congrArg Subtype.val hfix.2.1
      · exact congrArg Subtype.val hfix.2.2
    letI : Fintype Xmodel := Fintype.ofFinite Xmodel
    have hXcard :
        Nat.card Xmodel = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
      change Nat.card {z : ℙ K (Fin 4 → K) // z ∈ O} =
        (2 ^ (2 * m + 1)) ^ 2 + 1
      exact hOcard
    have hXcardGt : 1 < Fintype.card Xmodel := by
      rw [← Nat.card_eq_fintype_card, hXcard]
      omega
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hXcardGt
    have hnoRegularModel :
        ¬ ∃ R : Subgroup (SuzukiMatrixGroup m),
          R.Normal ∧ R ≠ ⊥ ∧
            ∀ x y : Xmodel, ∃! r : R,
              smulX (r : SuzukiMatrixGroup m) x = y := by
      rintro ⟨R, hRnormal, hRne, hregular⟩
      haveI : IsSimpleGroup (SuzukiMatrixGroup m) :=
        (External.huppert_blackburn_XI_3_6 m hm).1
      have hRtop : R = ⊤ :=
        (haveI := hRnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal R).resolve_left hRne
      let orbitMap : R → Xmodel := fun r =>
        smulX (r : SuzukiMatrixGroup m) a
      have horbitBij : Function.Bijective orbitMap := by
        constructor
        · intro r s hrs
          obtain ⟨u, hu, hu_unique⟩ := hregular a (orbitMap r)
          have hur : u = r := (hu_unique r rfl).symm
          have hus : u = s :=
            (hu_unique s (by simpa [orbitMap] using hrs.symm)).symm
          exact hur.symm.trans hus
        · intro z
          obtain ⟨r, hr, _⟩ := hregular a z
          exact ⟨r, hr⟩
      have hRcard : Nat.card R = Nat.card Xmodel :=
        Nat.card_congr (Equiv.ofBijective orbitMap horbitBij)
      have hcardEq :
          Nat.card (SuzukiMatrixGroup m) =
            (2 ^ (2 * m + 1)) ^ 2 + 1 := by
        calc
          Nat.card (SuzukiMatrixGroup m) = Nat.card R := by
            rw [hRtop]
            simp
          _ = Nat.card Xmodel := hRcard
          _ = (2 ^ (2 * m + 1)) ^ 2 + 1 := hXcard
      let q0 := 2 ^ (2 * m + 1)
      have hq0gt : 2 < q0 := by
        dsimp [q0]
        have : 3 ≤ 2 * m + 1 := by omega
        exact lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2)
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hcancel :
          (q0 ^ 2 + 1) * (q0 ^ 2 * (q0 - 1)) =
            (q0 ^ 2 + 1) * 1 := by
        simpa [q0, mul_assoc] using hMcard.symm.trans hcardEq
      have hone : q0 ^ 2 * (q0 - 1) = 1 :=
        Nat.eq_of_mul_eq_mul_left (by omega : 0 < q0 ^ 2 + 1) hcancel
      have hlarge : 4 ≤ q0 ^ 2 * (q0 - 1) := by
        have hsq : 2 ≤ q0 ^ 2 := by
          exact le_trans (by norm_num) (Nat.pow_le_pow_left hq0gt.le 2)
        have hsub : 2 ≤ q0 - 1 := by omega
        nlinarith
      omega
    obtain ⟨F, hFrob⟩ :=
      @External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists.{0, 0}
        (SuzukiMatrixGroup m) Xmodel
        (inferInstance : Group (SuzukiMatrixGroup m))
        (inferInstance : Finite (SuzukiMatrixGroup m))
        xAction
          (show @FaithfulSMul.{0, 0}
              (SuzukiMatrixGroup m) Xmodel xAction.toSMul from
            @FaithfulSMul.mk.{0, 0} (SuzukiMatrixGroup m) Xmodel xAction.toSMul (by
              intro g₁ g₂ hsame
              have hfix :
                  ∀ z : Xmodel, xAction.smul (g₂⁻¹ * g₁) z = z := by
                intro z
                calc
                  xAction.smul (g₂⁻¹ * g₁) z =
                      xAction.smul g₂⁻¹ (xAction.smul g₁ z) :=
                    xAction.mul_smul g₂⁻¹ g₁ z
                  _ = xAction.smul g₂⁻¹ (xAction.smul g₂ z) :=
                    congrArg (xAction.smul g₂⁻¹) (hsame z)
                  _ = xAction.smul (g₂⁻¹ * g₂) z :=
                    (xAction.mul_smul g₂⁻¹ g₂ z).symm
                  _ = xAction.smul 1 z := by simp
                  _ = z := xAction.one_smul z
              have hunit := hfaithfulX (g₂⁻¹ * g₁) hfix
              calc
                g₁ = g₂ * (g₂⁻¹ * g₁) := by simp
                _ = g₂ * 1 := by rw [hunit]
                _ = g₂ := mul_one g₂) )
          (inferInstance : Finite Xmodel)
        htwoModel hatMostTwoModel hnoRegularModel a b hab
    have hdegreeModel :
        Fintype.card Xmodel = Nat.card Q + 1 := by
      rw [← Nat.card_eq_fintype_card, hXcard, hQcardSuzuki]
    have hFcard :
        Nat.card F = Nat.card Q :=
      External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
        (Nat.card Q) hdegreeModel htwoModel a b hab F hFrob
    obtain ⟨eG', eOmega, hequiv⟩ :=
      transport_action_via_frobenius_kernel
        H Q base hHbase hNQ P hQeq hQp
        rho haction hA.A1.two_transitive htwoModel
        eG a b hab F hFrob hFcard
    let q0 := 2 ^ (2 * m + 1)
    have hq0gt : 2 < q0 := by
      dsimp [q0]
      have : 3 ≤ 2 * m + 1 := by omega
      exact lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine ⟨q0, ⟨2 * m + 1, rfl⟩, hq0gt, Or.inr ?_⟩
    refine ⟨m, Nat.ne_of_gt hm, rfl, ?_⟩
    let eTop : (⊤ : Subgroup G) ≃* SuzukiMatrixGroup m :=
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).trans eG'
    refine ⟨eTop, rho, eOmega, ?_, ?_⟩
    · intro g z
      rfl
    · intro l w
      change eOmega ((l : G) • w) = rho (eG' (l : G)) (eOmega w)
      exact hequiv (l : G) w

private theorem theorem_c_Q_hasPrimePowerOrder_of_Q1_eq_bot
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hch : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
    HypothesisC1 G V)
    (hQ1 : Q1 = ⊥) :
    ∃ n : ℕ, Nat.card Q = 2 ^ n := by
  classical
  obtain ⟨P, hS_eq⟩ := hch.1.section2.S_sylow_in_Q
  have hS_eq_Q : S = Q := by
    simpa [hQ1] using hch.1.section2.Q_decomp
  have hP_two : ∃ n : ℕ, Nat.card (P : Subgroup Q) = 2 ^ n := by
    exact P.isPGroup'.exists_card_eq
  rcases hP_two with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have hcard_map :
      Nat.card ((P : Subgroup Q).map Q.subtype) = Nat.card (P : Subgroup Q) :=
    Subgroup.card_map_of_injective
      (K := (P : Subgroup Q)) (f := Q.subtype) Q.subtype_injective
  rw [← hS_eq_Q, hS_eq, hcard_map, hn]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Theorem C: under (C1), `Q` is a `2`-group. -/
private theorem theorem_c_of_Q1_ne_bot
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hch : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
    HypothesisC1 G V)
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              ∃ (M : Subgroup L) (_ : M.Normal) (q : ℕ),
                Odd (Nat.card (L ⧸ M)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
                  ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : M ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : ΩL ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : M, ∀ ω : ΩL,
      eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : M ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : ΩL ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : M ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : ΩL ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω))))
    (hQ1 : Q1 ≠ ⊥) :
    IsPGroup 2 Q := by
  classical
  have hQ1_normal_in_H : (Q1.subgroupOf H).Normal := by
    let QH : Subgroup H := Q.subgroupOf H
    let SH : Subgroup H := S.subgroupOf H
    let Q1H : Subgroup H := Q1.subgroupOf H
    have hSHleQH : SH ≤ QH := by
      intro x hx
      exact hch.1.section2.S_le_Q hx
    have hQ1HleQH : Q1H ≤ QH := by
      intro x hx
      exact hch.1.section2.Q1_le_Q hx
    have hsup : SH ⊔ Q1H = QH := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup]
      change (S.subgroupOf H).map H.subtype ⊔
          (Q1.subgroupOf H).map H.subtype =
        (Q.subgroupOf H).map H.subtype
      rw [Subgroup.map_subgroupOf_eq_of_le
          (hch.1.section2.S_le_Q.trans hch.1.section2.hA.A1.Q_le_H),
        Subgroup.map_subgroupOf_eq_of_le
          (hch.1.section2.Q1_le_Q.trans hch.1.section2.hA.A1.Q_le_H),
        Subgroup.map_subgroupOf_eq_of_le hch.1.section2.hA.A1.Q_le_H]
      exact hch.1.section2.Q_decomp
    have hSH_normalizes_Q1H :
        SH ≤ Subgroup.normalizer (Q1H : Set H) := by
      refine subgroup_le_normalizer_of_conj_mem Q1H SH ?_
      intro s q hq
      change (s : G) * (q : G) * (s : G)⁻¹ ∈ Q1
      have hsS : (s : G) ∈ S := s.property
      have hqQ1 : (q : G) ∈ Q1 := hq
      have hsq : (s : G) * (q : G) = (q : G) * (s : G) :=
        hch.1.section2.S_commutes_Q1 (s : G) hsS (q : G) hqQ1
      rw [hsq]
      simpa using hqQ1
    let Q1Q : Subgroup QH := Q1H.subgroupOf QH
    have hQ1Qnormal : Q1Q.Normal := by
      have hnormalSup : (Q1H.subgroupOf (SH ⊔ Q1H)).Normal :=
        Subgroup.normal_subgroupOf_sup_of_le_normalizer hSH_normalizes_Q1H
      rw [hsup] at hnormalSup
      exact hnormalSup
    letI : Q1Q.Normal := hQ1Qnormal
    have hinf : Q1H ⊓ SH = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxG : (x : G) ∈ S ⊓ Q1 := ⟨hx.2, hx.1⟩
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
        hch.1.section2.S_disjoint_Q1.le_bot hxG
      simpa using hxbot
    let hsemi : Section2.IsInternalSemidirectProduct QH Q1H SH :=
      { left_le := hQ1HleQH
        right_le := hSHleQH
        right_normalizes_left := by
          intro s hs q hq
          have hsq : (s : G) * (q : G) = (q : G) * (s : G) :=
            hch.1.section2.S_commutes_Q1 (s : G) hs (q : G) hq
          have hsqH : s * q = q * s := Subtype.ext hsq
          change s * q * s⁻¹ ∈ Q1H
          rw [hsqH]
          simpa using hq
        inf_eq_bot := hinf
        mul_surjective := by
          intro q hq
          have hqSup : q ∈ SH ⊔ Q1H := by
            rw [hsup]
            exact hq
          have hqProd : q ∈ (SH : Set H) * (Q1H : Set H) := by
            rw [← Subgroup.coe_mul_of_left_le_normalizer_right
              SH Q1H hSH_normalizes_Q1H]
            exact hqSup
          rcases hqProd with ⟨s, hs, q1, hq1, hprod⟩
          have hsq : (s : G) * (q1 : G) = (q1 : G) * (s : G) :=
            hch.1.section2.S_commutes_Q1 (s : G) hs (q1 : G) hq1
          have hsqH : s * q1 = q1 * s := Subtype.ext hsq
          exact ⟨q1, hq1, s, hs, hprod.symm.trans hsqH⟩ }
    have hcardQ1Q : Nat.card Q1Q = Nat.card Q1 := by
      calc
        Nat.card Q1Q = Nat.card Q1H :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe hQ1HleQH).toEquiv
        _ = Nat.card Q1 :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe
              (hch.1.section2.Q1_le_Q.trans
                hch.1.section2.hA.A1.Q_le_H)).toEquiv
    have hcardSH : Nat.card SH = Nat.card S := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (hch.1.section2.S_le_Q.trans
            hch.1.section2.hA.A1.Q_le_H)).toEquiv
    have hindexQ1Q : Q1Q.index = Nat.card S := by
      calc
        Q1Q.index = Nat.card SH := by
          simpa [Q1Q, Subgroup.relIndex] using
            Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
        _ = Nat.card S := hcardSH
    have hSpgroup : IsPGroup 2 S := by
      obtain ⟨P, hS⟩ := hch.1.section2.S_sylow_in_Q
      rw [hS]
      exact P.isPGroup'.map Q.subtype
    have hcop : Nat.Coprime (Nat.card Q1) (Nat.card S) := by
      obtain ⟨n, hn⟩ := hSpgroup.exists_card_eq
      rw [hn]
      exact hch.1.section2.Q1_odd_order.coprime_two_right.pow_right n
    let pi : Set Nat.Primes := {p | p.val ∣ Nat.card Q1}
    have hHall : IsHallSubgroup pi Q1Q := by
      refine isHallSubgroup_of pi Q1Q ?_ ?_
      · intro p hp
        rw [hcardQ1Q] at hp
        simpa [pi] using hp
      · intro p hp hpIndex
        have hpQ1 : p.val ∣ Nat.card Q1 := by
          simpa [pi] using hp
        have hpS : p.val ∣ Nat.card S := by
          simpa [hindexQ1Q] using hpIndex
        have hself : Nat.Coprime p.val p.val :=
          Nat.Coprime.of_dvd hpQ1 hpS hcop
        exact p.property.ne_one ((Nat.coprime_self p.val).mp hself)
    have hchar : Q1Q.Characteristic := by
      rw [Subgroup.characteristic_iff_map_eq]
      intro e
      exact hHall.eq_of_normal (hHall.map_mulAut e)
    letI : QH.Normal := hch.1.section2.hA.A1.Q_normal_in_H
    letI : Q1Q.Characteristic := hchar
    have hmapNormal : (Q1Q.map QH.subtype).Normal := inferInstance
    have hmap : Q1Q.map QH.subtype = Q1H := by
      ext x
      simp [Q1Q, Q1H, QH, hQ1HleQH]
    rw [hmap] at hmapNormal
    exact hmapNormal
  have hfixed_cover :
      ∀ (X : Subgroup G) (a b z : Ω),
        a ∈ fixedPointsOfSubgroup G Ω X →
          b ∈ fixedPointsOfSubgroup G Ω X →
            z ∈ fixedPointsOfSubgroup G Ω X →
              a ≠ b →
                Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} ≤ 2 →
                  z = a ∨ z = b := by
    intro X a b z ha hb hz hab hcard
    by_contra hcover
    have hza : z ≠ a := by
      intro h
      exact hcover (Or.inl h)
    have hzb : z ≠ b := by
      intro h
      exact hcover (Or.inr h)
    let Fixed : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
    let pa : Fixed := ⟨a, ha⟩
    let pb : Fixed := ⟨b, hb⟩
    let pz : Fixed := ⟨z, hz⟩
    have hcardFixed_le : Nat.card Fixed ≤ 2 := by
      simpa [Fixed] using hcard
    have hpa_ne_pb : pa ≠ pb := by
      intro h
      exact hab (congrArg Subtype.val h)
    have hpa_ne_pz : pa ≠ pz := by
      intro h
      exact hza (congrArg Subtype.val h).symm
    have hpb_ne_pz : pb ≠ pz := by
      intro h
      exact hzb (congrArg Subtype.val h).symm
    let f : Fin 3 → Fixed := fun i =>
      if i = 0 then pa else if i = 1 then pb else pz
    have hf_inj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [f, hpa_ne_pb, hpa_ne_pb.symm, hpa_ne_pz, hpa_ne_pz.symm,
          hpb_ne_pz, hpb_ne_pz.symm] at hij ⊢
    have hthree_le : 3 ≤ Nat.card Fixed := by
      letI : Fintype Fixed := Fintype.ofFinite Fixed
      have hle := Fintype.card_le_of_injective f hf_inj
      simpa [Nat.card_eq_fintype_card] using hle
    omega
  have hfixed_small :
      ∀ P : Subgroup G, P ≤ D →
        Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P} ≤ 2 →
          Subgroup.centralizer (P : Set G) ⊓ Q1 = ⊥ := by
    intro P hPD hfixed
    rw [eq_bot_iff]
    intro y hy
    have hA1 := hch.1.section2.hA.A1
    obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
    let beta : Ω := t⁻¹ • base
    have hbase_fixed : base ∈ fixedPointsOfSubgroup G Ω P := by
      intro x hx
      have hxH : x ∈ H := hA1.D_le_H (hPD hx)
      have hxstab : x ∈ MulAction.stabilizer G base := by
        simpa [hHbase] using hxH
      simpa using hxstab
    have hbeta_fixed : beta ∈ fixedPointsOfSubgroup G Ω P := by
      intro x hx
      have hxD : x ∈ D := hPD hx
      have hx' : x ∈ H ⊓ rightConjugate H t := by
        simpa [hA1.D_eq] using hxD
      have hconj :
          rightConjugate H t = MulAction.stabilizer G beta := by
        dsimp [beta]
        rw [hHbase]
        exact rightConjugate_stabilizer base t
      have hxstab : x ∈ MulAction.stabilizer G beta := by
        simpa [hconj] using hx'.2
      simpa using hxstab
    have hbase_ne_beta : base ≠ beta := by
      intro h
      have ht_inv_H : t⁻¹ ∈ H := by
        have ht_inv_stab : t⁻¹ ∈ MulAction.stabilizer G base := by
          change t⁻¹ • base = base
          exact h.symm
        simpa [hHbase] using ht_inv_stab
      have htH : t ∈ H := by
        simpa using H.inv_mem ht_inv_H
      exact hA1.t_not_mem_H htH
    have hyQ : y ∈ Q := hch.1.section2.Q1_le_Q hy.2
    have hyH : y ∈ H := hA1.Q_le_H hyQ
    have hy_base : y • base = base := by
      have hystab : y ∈ MulAction.stabilizer G base := by
        simpa [hHbase] using hyH
      simpa using hystab
    have hy_beta_fixed : y • beta ∈ fixedPointsOfSubgroup G Ω P := by
      intro x hx
      have hcomm : x * y = y * x :=
        (Subgroup.mem_centralizer_iff.mp hy.1) x hx
      calc
        x • (y • beta) = (x * y) • beta := by rw [mul_smul]
        _ = (y * x) • beta := by rw [hcomm]
        _ = y • (x • beta) := by rw [mul_smul]
        _ = y • beta := by rw [hbeta_fixed x hx]
    have hy_beta_cases : y • beta = base ∨ y • beta = beta :=
      hfixed_cover P base beta (y • beta)
        hbase_fixed hbeta_fixed hy_beta_fixed hbase_ne_beta hfixed
    have hy_beta : y • beta = beta := by
      rcases hy_beta_cases with hyb | hyb
      · exfalso
        have hpre : y⁻¹ • (y • beta) = y⁻¹ • (y • base) := by
          rw [hyb, hy_base]
        have hbeta_base : beta = base := by
          simpa [smul_smul] using hpre
        exact hbase_ne_beta hbeta_base.symm
      · exact hyb
    have hy_right : y ∈ rightConjugate H t := by
      have hy_stab : y ∈ MulAction.stabilizer G beta := by
        simpa using hy_beta
      have hconj :
          rightConjugate H t = MulAction.stabilizer G beta := by
        dsimp [beta]
        rw [hHbase]
        exact rightConjugate_stabilizer base t
      simpa [hconj] using hy_stab
    have hyD : y ∈ D := by
      rw [hA1.D_eq]
      exact ⟨hyH, hy_right⟩
    have hy_bot : y ∈ (⊥ : Subgroup G) := by
      exact hA1.Q_disjoint_D.le_bot ⟨hyQ, hyD⟩
    simpa using hy_bot
  have hfixed_large :
      ∀ P : Subgroup G, P ≤ D →
        (∃ p : ℕ, Nat.Prime p ∧ Nat.card P = p) →
          3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P} →
            Subgroup.centralizer (P : Set G) ⊓ Q1 = ⊥ := by
    intro P hPD hPprime hfixed
    obtain ⟨d, hdV⟩ :=
      PFchapter1section1.proposition_6_c H D Q P t
        hch.1.section2.hA.A1 hPD hfixed
    let X : Subgroup G := rightConjugate P (d : G)
    have hXleV : X ≤ V := by
      rw [hch.1.section2.V_eq]
      exact hdV
    obtain ⟨p, hp, hPcard⟩ := hPprime
    have hXcard : Nat.card X = Nat.card P := by
      change Nat.card (rightConjugate P (d : G)) = Nat.card P
      rw [rightConjugate, Subgroup.conjBy]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective P
          (MulAut.conj (d : G)⁻¹).toMonoidHom
          (MulAut.conj (d : G)⁻¹).injective).symm.toEquiv
    have hXprime : ∃ p : ℕ, Nat.Prime p ∧ Nat.card X = p :=
      ⟨p, hp, hXcard.trans hPcard⟩
    have hXne : X ≠ ⊥ := by
      intro hXbot
      apply hp.ne_one
      calc
        p = Nat.card P := hPcard.symm
        _ = Nat.card X := hXcard.symm
        _ = 1 := by rw [hXbot]; simp
    have h2rank : TwoRankAtLeastTwo (Subgroup.centralizer (X : Set G)) :=
      hch.2.centralizers_two_rank X hXleV hXprime
    have hcentralX : Subgroup.centralizer (X : Set G) ⊓ Q1 = ⊥ :=
      (PFchapter1section3.proposition_1_c.{u, v}
        H D Q K V W Q0 S Q1 X t s
        hch.1 hind hXne hXleV h2rank).1
    rw [eq_bot_iff]
    intro y hy
    let dH : H :=
      ⟨(d : G), hch.1.section2.hA.A1.D_le_H d.property⟩
    let yH : H :=
      ⟨y, hch.1.section2.hA.A1.Q_le_H
        (hch.1.section2.Q1_le_Q hy.2)⟩
    have hyQ1H : yH ∈ Q1.subgroupOf H := hy.2
    have hyConjQ1H :
        dH⁻¹ * yH * (dH⁻¹)⁻¹ ∈ Q1.subgroupOf H :=
      hQ1_normal_in_H.conj_mem yH hyQ1H dH⁻¹
    have hyConjQ1 : rightConjugateElem y (d : G) ∈ Q1 := by
      have hmem :
          (((dH⁻¹ * yH * (dH⁻¹)⁻¹ : H) : G)) ∈ Q1 :=
        hyConjQ1H
      simpa only [rightConjugateElem, Subgroup.coe_mul,
        Subgroup.coe_inv, dH, yH, inv_inv] using hmem
    have hyConjCentral :
        rightConjugateElem y (d : G) ∈
          Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      change x ∈ rightConjugate P (d : G) at hx
      rw [rightConjugate] at hx
      change x ∈ P.map (MulAut.conj (d : G)⁻¹).toMonoidHom at hx
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      have hay : a * y = y * a :=
        (Subgroup.mem_centralizer_iff.mp hy.1) a ha
      have hconj :=
        congrArg (fun z : G => (d : G)⁻¹ * z * (d : G)) hay
      simpa [MulAut.conj_apply, rightConjugateElem, mul_assoc] using hconj
    have hyConjBot :
        rightConjugateElem y (d : G) ∈ (⊥ : Subgroup G) := by
      rw [← hcentralX]
      exact ⟨hyConjCentral, hyConjQ1⟩
    have hyConjOne : rightConjugateElem y (d : G) = 1 := by
      simpa using hyConjBot
    calc
      y = (d : G) * rightConjugateElem y (d : G) * (d : G)⁻¹ := by
        simp [rightConjugateElem, mul_assoc]
      _ = 1 := by rw [hyConjOne]; simp
  have hD_prime_fixedPointFree :
      ∀ P : Subgroup G, P ≤ D →
        (∃ p : ℕ, Nat.Prime p ∧ Nat.card P = p) →
          Subgroup.centralizer (P : Set G) ⊓ Q1 = ⊥ := by
    intro P hPD hPprime
    by_cases hfixed :
        Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P} ≤ 2
    · exact hfixed_small P hPD hfixed
    · exact hfixed_large P hPD hPprime (by omega)
  have hQ_TI :
      ∀ g : G, g ∉ H → Disjoint Q (rightConjugate Q g) := by
    intro g hgH
    obtain ⟨h, hHD, _hodd⟩ :=
      PFchapter1section1.proposition_1_a H D Q t
        hch.1.section2.hA.A1 g hgH
    have hQDconj_bot : Q ⊓ rightConjugate D (h : G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases hx.2 with ⟨d, hdD, rfl⟩
      have hxQH : (h : G)⁻¹ * d * (h : G) ∈ Q := by
        simpa [MulAut.conj_apply] using hx.1
      have hxQsub :
          (⟨(h : G)⁻¹ * d * (h : G),
            hch.1.section2.hA.A1.Q_le_H hxQH⟩ : H) ∈
            Q.subgroupOf H := hxQH
      have hconjQ :
          (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ ∈ Q := by
        exact hch.1.section2.hA.A1.Q_normal_in_H.conj_mem
          (⟨(h : G)⁻¹ * d * (h : G),
            hch.1.section2.hA.A1.Q_le_H hxQH⟩ : H)
          hxQsub h
      have hconjD :
          (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ ∈ D := by
        simpa [mul_assoc] using hdD
      have hbot :
          (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ = 1 := by
        have hmem :
            (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ ∈ Q ⊓ D :=
          ⟨hconjQ, hconjD⟩
        simpa using hch.1.section2.hA.A1.Q_disjoint_D.le_bot hmem
      have hd_one : d = 1 := by
        calc
          d = (h : G) * ((h : G)⁻¹ * d * (h : G)) * (h : G)⁻¹ := by group
          _ = 1 := hbot
      simp [hd_one]
    rw [Subgroup.disjoint_def]
    intro x hxQ hxQg
    have hxHg : x ∈ rightConjugate H g := by
      rcases hxQg with ⟨q, hqQ, rfl⟩
      exact ⟨q, hch.1.section2.hA.A1.Q_le_H hqQ, rfl⟩
    have hxDconj : x ∈ rightConjugate D (h : G) := by
      rw [← hHD]
      exact ⟨hxHg, hch.1.section2.hA.A1.Q_le_H hxQ⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hQDconj_bot]
      exact ⟨hxQ, hxDconj⟩
    simpa using hxbot
  have hDfixed :
      ∀ d : G, d ∈ D → d ≠ 1 → ∀ q : G, q ∈ Q1 →
        d * q * d⁻¹ = q → q = 1 := by
    intro d hdD hdne q hqQ1 hfix
    have horder_ne : orderOf d ≠ 1 := by
      simpa [orderOf_eq_one_iff] using hdne
    obtain ⟨p, hp, hpOrder⟩ :=
      Nat.ne_one_iff_exists_prime_dvd.mp horder_ne
    let Z : Subgroup G := Subgroup.zpowers d
    have hpZ : p ∣ Nat.card Z := by
      simpa [Z, Nat.card_zpowers] using hpOrder
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, huOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := Z) p hpZ
    let a : G := (u : Z)
    let P : Subgroup G := Subgroup.zpowers a
    have haZ : a ∈ Z := u.property
    have hZleD : Z ≤ D := Subgroup.zpowers_le.mpr hdD
    have hPleZ : P ≤ Z := Subgroup.zpowers_le.mpr haZ
    have hPleD : P ≤ D := hPleZ.trans hZleD
    have haOrder : orderOf a = p := by
      simpa [a] using huOrder
    have hPcard : Nat.card P = p := by
      simpa [P, Nat.card_zpowers] using haOrder
    have hdq : Commute d q := by
      change d * q = q * d
      have h := congrArg (fun z : G => z * d) hfix
      simpa [mul_assoc] using h
    have hqCentral : q ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxZ : x ∈ Z := hPleZ hx
      rcases Subgroup.mem_zpowers_iff.mp hxZ with ⟨k, rfl⟩
      exact (hdq.zpow_left k).eq
    have hqBot : q ∈ (⊥ : Subgroup G) := by
      rw [← hD_prime_fixedPointFree P hPleD ⟨p, hp, hPcard⟩]
      exact ⟨hqCentral, hqQ1⟩
    simpa using hqBot
  have hDnormQ1 : D ≤ Subgroup.normalizer (Q1 : Set G) := by
    refine subgroup_le_normalizer_of_conj_mem Q1 D ?_
    intro d q hq
    let dH : H :=
      ⟨(d : G), hch.1.section2.hA.A1.D_le_H d.property⟩
    let qH : H :=
      ⟨q, hch.1.section2.hA.A1.Q_le_H
        (hch.1.section2.Q1_le_Q hq)⟩
    have hqH : qH ∈ Q1.subgroupOf H := hq
    have hconj := hQ1_normal_in_H.conj_mem qH hqH dH
    change (d : G) * q * (d : G)⁻¹ ∈ Q1
    change (d : G) * q * (d : G)⁻¹ ∈ Q1 at hconj
    exact hconj
  have hfeitSibleyData :
      ∃ (d : FeitSibleyData G)
          (chars : Finset (Section1.ClassFunction d.H)),
        d.H = H ∧
          d.QInG = Q ∧
          d.D.map d.H.subtype = D ∧
          d.S.map d.H.subtype = S ∧
          d.Q1.map d.H.subtype = Q1 ∧
          IsFeitSibleyExceptionalFamily d chars ∧
          Odd (Nat.card d.D) := by
    have hcardSQ1 : Nat.Coprime (Nat.card S) (Nat.card Q1) := by
      obtain ⟨P, hS⟩ := hch.1.section2.S_sylow_in_Q
      have hSpgroup : IsPGroup 2 S := by
        rw [hS]
        exact P.isPGroup'.map Q.subtype
      obtain ⟨n, hn⟩ := hSpgroup.exists_card_eq
      rw [hn]
      exact hch.1.section2.Q1_odd_order.coprime_two_left.pow_left n
    have hcardQD : Nat.Coprime (Nat.card Q) (Nat.card D) := by
      let Q1Q : Subgroup Q := Q1.subgroupOf Q
      let SQ : Subgroup Q := S.subgroupOf Q
      have hQ1Qnormal : Q1Q.Normal := by
        constructor
        intro n hn g
        let nH : H :=
          ⟨(n : G), hch.1.section2.hA.A1.Q_le_H n.property⟩
        let gH : H :=
          ⟨(g : G), hch.1.section2.hA.A1.Q_le_H g.property⟩
        have hnH : nH ∈ Q1.subgroupOf H := hn
        have hconj := hQ1_normal_in_H.conj_mem nH hnH gH
        exact hconj
      letI : Q1Q.Normal := hQ1Qnormal
      have hdisjQ : Disjoint Q1Q SQ := by
        rw [Subgroup.disjoint_def]
        intro x hxQ1 hxS
        apply Subtype.ext
        exact (Subgroup.disjoint_def.mp hch.1.section2.S_disjoint_Q1)
          hxS hxQ1
      have hsupQ : Q1Q ⊔ SQ = ⊤ := by
        rw [sup_comm, ← Subgroup.subgroupOf_sup
          hch.1.section2.S_le_Q hch.1.section2.Q1_le_Q,
          hch.1.section2.Q_decomp]
        exact Subgroup.subgroupOf_self Q
      have hcomp : Q1Q.IsComplement' SQ :=
        isComplement'_of_disjoint_sup_eq_top_of_normal Q1Q SQ hdisjQ hsupQ
      have hcardQ : Nat.card Q = Nat.card S * Nat.card Q1 := by
        have hcard := hcomp.card_mul
        simpa [Q1Q, SQ,
          natCard_subgroupOf_eq Q1 Q hch.1.section2.Q1_le_Q,
          natCard_subgroupOf_eq S Q hch.1.section2.S_le_Q,
          Nat.mul_comm] using hcard.symm
      apply Nat.coprime_of_dvd
      intro p hp hpQ hpD
      rw [hcardQ] at hpQ
      rcases hp.dvd_mul.mp hpQ with hpS | hpQ1
      · obtain ⟨P2, hS⟩ := hch.1.section2.S_sylow_in_Q
        have hSpgroup : IsPGroup 2 S := by
          rw [hS]
          exact P2.isPGroup'.map Q.subtype
        obtain ⟨n, hn⟩ := hSpgroup.exists_card_eq
        rw [hn] at hpS
        have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpS
        have hpeq : p = 2 :=
          (Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left hp.ne_one
        subst p
        exact hch.1.section2.hA.A1.D_odd.not_two_dvd_nat hpD
      · letI : Fact p.Prime := ⟨hp⟩
        obtain ⟨x, hxorder⟩ :=
          exists_prime_orderOf_dvd_card' (G := D) p hpD
        let xG : G := x
        let P : Subgroup G := Subgroup.zpowers xG
        have hxGorder : orderOf xG = p := by
          simpa [xG] using hxorder
        have hxGne : xG ≠ 1 := by
          intro hx
          apply hp.ne_one
          rw [← hxGorder, hx, orderOf_one]
        have hPcard : Nat.card P = p := by
          simpa [P, Nat.card_zpowers] using hxGorder
        have hPleD : P ≤ D := by
          apply Subgroup.zpowers_le.mpr
          exact x.property
        have hPnormQ1 : P ≤ Subgroup.normalizer (Q1 : Set G) :=
          hPleD.trans hDnormQ1
        letI : MulDistribMulAction P Q1 :=
          Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) P Q1
            hPnormQ1
        have hfixedOne :
            ∀ z : MulAction.fixedPoints P Q1, (z : Q1) = 1 := by
          intro z
          let xP : P := ⟨xG, Subgroup.mem_zpowers xG⟩
          have hzfix : xP • (z : Q1) = (z : Q1) := z.property xP
          have hzfixG :
              xG * (z : G) * xG⁻¹ = (z : G) := by
            rw [← Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
              P Q1 hPnormQ1 xP (z : Q1)]
            exact congrArg (fun y : Q1 => (y : G)) hzfix
          apply Subtype.ext
          exact hDfixed xG x.property hxGne (z : G)
            (z : Q1).property hzfixG
        have hfixedSubsingleton :
            Subsingleton (MulAction.fixedPoints P Q1) := by
          constructor
          intro a b
          apply Subtype.ext
          rw [hfixedOne a, hfixedOne b]
        have hfixedNonempty :
            Nonempty (MulAction.fixedPoints P Q1) := by
          refine ⟨⟨1, ?_⟩⟩
          intro y
          simp
        have hfixedCard :
            Nat.card (MulAction.fixedPoints P Q1) = 1 :=
          Nat.card_eq_one_iff_unique.mpr
            ⟨hfixedSubsingleton, hfixedNonempty⟩
        have hPpgroup : IsPGroup p P :=
          IsPGroup.of_card (n := 1) (by simpa using hPcard)
        have hmod : Nat.card Q1 ≡ 1 [MOD p] := by
          simpa [hfixedCard] using
            (IsPGroup.card_modEq_card_fixedPoints
              (G := P) (p := p) hPpgroup Q1)
        exact hp.not_dvd_one ((hmod.dvd_iff (dvd_refl p)).mp hpQ1)
    have hQ1not2 : ¬ IsPGroup 2 Q1 := by
      intro hQ1two
      obtain ⟨n, hn⟩ := hQ1two.exists_card_eq
      cases n with
      | zero =>
          apply hQ1
          rw [← Subgroup.card_le_one_iff_eq_bot, hn]
          simp
      | succ n =>
          have heven : Even (Nat.card Q1) := by
            rw [hn, pow_succ]
            rw [Nat.mul_comm]
            exact even_two_mul (2 ^ n)
          exact (Nat.not_even_iff_odd.mpr hch.1.section2.Q1_odd_order) heven
    have hSnil : Group.IsNilpotent S := by
      obtain ⟨P, hS⟩ := hch.1.section2.S_sylow_in_Q
      have hSpgroup : IsPGroup 2 S := by
        rw [hS]
        exact P.isPGroup'.map Q.subtype
      exact IsPGroup.isNilpotent hSpgroup
    have hexceptional :
        ∀ d : FeitSibleyData G,
          ∃ chars : Finset (Section1.ClassFunction d.H),
            IsFeitSibleyExceptionalFamily d chars := by
      intro d
      rcases Theory.Character.irreducible_characters_form_basis (G := d.H) with
        ⟨ι, hι, χ, hχ, _b, _hb⟩
      letI : Fintype ι := hι
      rcases hχ with ⟨hirr, hall, _hinj⟩
      let ψ : ι → Section1.ClassFunction d.H :=
        fun i => Section1.ofConjClassFunction (χ i)
      have hψirr :
          ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
        intro i
        exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup
          (hirr i)
      let chars : Finset (Section1.ClassFunction d.H) :=
        (Finset.univ.filter fun i =>
          ¬ Section1.subgroupInKernel' (ψ i) d.Q1).image ψ
      refine ⟨chars, ?_⟩
      intro theta
      constructor
      · intro htheta
        rcases Finset.mem_image.mp htheta with ⟨i, hi, rfl⟩
        exact ⟨hψirr i, (Finset.mem_filter.mp hi).2⟩
      · rintro ⟨hthetaIrr, hthetaKernel⟩
        have hthetaClass : Section1.IsClassFunction theta := by
          rcases hthetaIrr with ⟨n, rho, _hrho, htheta⟩
          rw [htheta]
          intro x g
          simpa [mul_assoc] using
            Representation.char_conj (ρ := rho) g x
        have hthetaRepIrr :
            Theory.Character.IsIrreducibleConjCharacter
              (Section1.toConjClassFunction theta hthetaClass) :=
          Section1.toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
            hthetaClass hthetaIrr
        obtain ⟨i, hi⟩ := hall
          (Section1.toConjClassFunction theta hthetaClass) hthetaRepIrr
        have hψtheta : ψ i = theta := by
          ext g
          have hval := congrFun hi (ConjClasses.mk g)
          simpa [ψ, Section1.ofConjClassFunction_apply,
            Section1.toConjClassFunction_apply] using hval
        apply Finset.mem_image.mpr
        refine ⟨i, ?_, hψtheta⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, by simpa [hψtheta] using hthetaKernel⟩
    let QH : Subgroup H := Q.subgroupOf H
    let DH : Subgroup H := D.subgroupOf H
    let SH : Subgroup H := S.subgroupOf H
    let Q1H : Subgroup H := Q1.subgroupOf H
    have hQHsupDH : QH ⊔ DH = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup]
      change (Q.subgroupOf H).map H.subtype ⊔
          (D.subgroupOf H).map H.subtype =
        (⊤ : Subgroup H).map H.subtype
      have htopmap : (⊤ : Subgroup H).map H.subtype = H := by
        ext x
        simp
      rw [Subgroup.map_subgroupOf_eq_of_le
          hch.1.section2.hA.A1.Q_le_H,
        Subgroup.map_subgroupOf_eq_of_le
          hch.1.section2.hA.A1.D_le_H,
        htopmap]
      exact hch.1.section2.hA.A1.Q_sup_D
    have hQHDHdisj : Disjoint QH DH := by
      rw [Subgroup.disjoint_def]
      intro x hxQ hxD
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
        hch.1.section2.hA.A1.Q_disjoint_D.le_bot ⟨hxQ, hxD⟩
      simpa using hxbot
    have hSHleQH : SH ≤ QH :=
      fun _ hx => hch.1.section2.S_le_Q hx
    have hQ1HleQH : Q1H ≤ QH :=
      fun _ hx => hch.1.section2.Q1_le_Q hx
    have hSHsupQ1H : SH ⊔ Q1H = QH := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup]
      change (S.subgroupOf H).map H.subtype ⊔
          (Q1.subgroupOf H).map H.subtype =
        (Q.subgroupOf H).map H.subtype
      rw [Subgroup.map_subgroupOf_eq_of_le
          (hch.1.section2.S_le_Q.trans hch.1.section2.hA.A1.Q_le_H),
        Subgroup.map_subgroupOf_eq_of_le
          (hch.1.section2.Q1_le_Q.trans
            hch.1.section2.hA.A1.Q_le_H),
        Subgroup.map_subgroupOf_eq_of_le hch.1.section2.hA.A1.Q_le_H]
      exact hch.1.section2.Q_decomp
    have hSHQ1Hdisj : Disjoint SH Q1H := by
      rw [Subgroup.disjoint_def]
      intro x hxS hxQ1
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
        hch.1.section2.S_disjoint_Q1.le_bot ⟨hxS, hxQ1⟩
      simpa using hxbot
    have hcardQH : Nat.card QH = Nat.card Q :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hch.1.section2.hA.A1.Q_le_H).toEquiv
    have hcardDH : Nat.card DH = Nat.card D :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe hch.1.section2.hA.A1.D_le_H).toEquiv
    have hcardSH : Nat.card SH = Nat.card S :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (hch.1.section2.S_le_Q.trans
            hch.1.section2.hA.A1.Q_le_H)).toEquiv
    have hcardQ1H : Nat.card Q1H = Nat.card Q1 :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (hch.1.section2.Q1_le_Q.trans
            hch.1.section2.hA.A1.Q_le_H)).toEquiv
    have hQ1normalQH : (Q1H.subgroupOf QH).Normal :=
      hQ1_normal_in_H.subgroupOf QH
    have hHne : H ≠ ⊤ := by
      intro hH
      apply hch.1.section2.hA.A1.t_not_mem_H
      rw [hH]
      trivial
    let data : FeitSibleyData G :=
      { H := H
        Q := QH
        D := DH
        S := SH
        Q1 := Q1H
        H_ne_top := hHne
        Q_normal := hch.1.section2.hA.A1.Q_normal_in_H
        H_eq_Q_sup_D := hQHsupDH
        Q_disjoint_D := hQHDHdisj
        S_le_Q := hSHleQH
        Q1_le_Q := hQ1HleQH
        Q_eq_S_sup_Q1 := hSHsupQ1H
        S_disjoint_Q1 := hSHQ1Hdisj
        S_commutes_Q1 := by
          intro s q hs hq
          apply Subtype.ext
          exact hch.1.section2.S_commutes_Q1 (s : G) hs (q : G) hq
        card_Q_coprime_card_D := by
          simpa [hcardQH, hcardDH] using hcardQD
        card_S_coprime_card_Q1 := by
          simpa [hcardSH, hcardQ1H] using hcardSQ1
        Q1_normal_in_Q := hQ1normalQH
        D_normalizes_Q1 := by
          intro d q
          exact hQ1_normal_in_H.conj_mem q q.property d
        D_fixedPointFree_on_Q1 := by
          intro d hd q hfix
          apply Subtype.ext
          apply Subtype.ext
          exact hDfixed (d : G) d.property
            (fun hdG => hd (Subtype.ext hdG)) (q : G) q.property
            (congrArg (fun x : H => (x : G)) hfix)
        Q_TI_in_G := by
          intro g hg
          simpa [QH, FeitSibleyData.QInG,
            Subgroup.map_subgroupOf_eq_of_le hch.1.section2.hA.A1.Q_le_H] using
            hQ_TI g hg
        Q1_not_two_group := by
          intro hp
          apply hQ1not2
          exact hp.of_equiv
            (Subgroup.subgroupOfEquivOfLe
              (hch.1.section2.Q1_le_Q.trans
                hch.1.section2.hA.A1.Q_le_H))
        Q1_odd := by simpa [hcardQ1H] using hch.1.section2.Q1_odd_order
        S_nilpotent := by
          letI : Group.IsNilpotent S := hSnil
          exact Group.nilpotent_of_mulEquiv
            (Subgroup.subgroupOfEquivOfLe
              (hch.1.section2.S_le_Q.trans
                hch.1.section2.hA.A1.Q_le_H)).symm }
    obtain ⟨chars, hchars⟩ := hexceptional data
    refine ⟨data, chars, rfl, ?_, ?_, ?_, ?_, hchars, ?_⟩
    · exact Subgroup.map_subgroupOf_eq_of_le hch.1.section2.hA.A1.Q_le_H
    · exact Subgroup.map_subgroupOf_eq_of_le hch.1.section2.hA.A1.D_le_H
    · exact Subgroup.map_subgroupOf_eq_of_le
        (hch.1.section2.S_le_Q.trans hch.1.section2.hA.A1.Q_le_H)
    · exact Subgroup.map_subgroupOf_eq_of_le
        (hch.1.section2.Q1_le_Q.trans hch.1.section2.hA.A1.Q_le_H)
    · simpa [data, hcardDH] using hch.1.section2.hA.A1.D_odd
  obtain ⟨d, chars, hdH, hdQ, hdD, hdS, hdQ1, hchars, hdDodd⟩ :=
    hfeitSibleyData
  have hcoherent :
      IsCoherentTriple puncturedSet chars
        (Section1.inducedCFLinear d.H) :=
    feitSibley_theorem d chars hchars hdDodd
  have hkernel_character :
      ∃ f : Section1.ClassFunction G,
        Section1.IsIrreducibleCharacterOnGroup f ∧
          f ≠ Section1.principalCharacter G ∧
            Section1.subgroupInKernel' f Q1 := by
    rcases hcoherent with
      ⟨hsource, hspanNonempty, T', hTiso, hTvirtual, hTagree⟩
    let avoidsExtension (f : Section1.ClassFunction G) : Prop :=
      ∀ chi : Section1.ClassFunction d.H, chi ∈ chars →
        f ≠ T' chi ∧ f ≠ -T' chi
    let fusionInvariant (lambda : Section1.ClassFunction d.H) : Prop :=
      ∀ (x : d.H) (g : G) (hxg : g * (x : G) * g⁻¹ ∈ d.H),
        lambda ⟨g * (x : G) * g⁻¹, hxg⟩ = lambda x
    have hlinear_character_data :
        ∃ lambda : Section1.ClassFunction d.H,
          Section1.IsIrreducibleCharacterOnGroup lambda ∧
            lambda ≠ Section1.principalCharacter d.H ∧
              Section1.degree lambda = 1 ∧
                Section1.subgroupInKernel' lambda d.Q1 ∧
                  Section1.IsCharacter (Section1.inducedCF d.H lambda) ∧
                  Section1.scalarProduct G
                      (Section1.inducedCF d.H lambda)
                      (Section1.inducedCF d.H lambda) = 2 ∧
                    Section1.scalarProduct G
                      (Section1.inducedCF d.H lambda)
                      (Section1.principalCharacter G) = 0 := by
      let QK : Subgroup d.H := d.Q ⊔ K.subgroupOf d.H
      have hQK_normal : QK.Normal := by
        letI : d.Q.Normal := d.Q_normal
        have hKnormalD : (K.subgroupOf D).Normal :=
          (PFchapter1section2.proposition_2 H D Q K V W Q0 S Q1 t
            hch.1.section2).2
        refine ⟨?_⟩
        intro x hx g
        have hg : g ∈ d.Q ⊔ d.D := by
          rw [d.H_eq_Q_sup_D]
          trivial
        rcases Subgroup.mem_sup_of_normal_left.mp hg with
          ⟨q, hq, e, he, hqe⟩
        have hxQK : x ∈ d.Q ⊔ K.subgroupOf d.H := hx
        rcases Subgroup.mem_sup_of_normal_left.mp hxQK with
          ⟨q0, hq0, k, hk, hq0k⟩
        have heD : ((e : d.H) : G) ∈ D := by
          have heMap : ((e : d.H) : G) ∈ d.D.map d.H.subtype :=
            ⟨e, he, rfl⟩
          simpa [hdD] using heMap
        let eD : D := ⟨((e : d.H) : G), heD⟩
        let kD : D :=
          ⟨((k : d.H) : G), hch.1.section2.K_le_D hk⟩
        have heq0 : e * q0 * e⁻¹ ∈ d.Q :=
          d.Q_normal.conj_mem q0 hq0 e
        have hek : e * k * e⁻¹ ∈ K.subgroupOf d.H := by
          change
            ((eD : G) * (kD : G) * (eD : G)⁻¹) ∈ K
          exact hKnormalD.conj_mem kD (by
            simpa [kD, Subgroup.mem_subgroupOf] using hk) eD
        have hex : e * x * e⁻¹ ∈ QK := by
          rw [← hq0k]
          have hprod :
              (e * q0 * e⁻¹) * (e * k * e⁻¹) ∈ QK :=
            QK.mul_mem (Subgroup.mem_sup_left heq0)
              (Subgroup.mem_sup_right hek)
          convert hprod using 1 ;
            group
        have hqQK : q ∈ QK := Subgroup.mem_sup_left hq
        have hconj : q * (e * x * e⁻¹) * q⁻¹ ∈ QK :=
          QK.mul_mem (QK.mul_mem hqQK hex) (QK.inv_mem hqQK)
        rw [← hqe]
        simpa only [mul_inv_rev, mul_assoc] using hconj
      letI : QK.Normal := hQK_normal
      have hquotient_solvable : Group.IsSolvable (d.H ⧸ QK) := by
        letI : Group.IsSolvable d.D := _root_.CFSG.odd_order_theorem d.D hdDodd
        let pi : d.H →* d.H ⧸ QK := QuotientGroup.mk' QK
        let piD : d.D →* d.H ⧸ QK := pi.comp d.D.subtype
        letI : d.Q.Normal := d.Q_normal
        have hpiD_surjective : Function.Surjective piD := by
          intro z
          obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective QK z
          have hx : x ∈ d.Q ⊔ d.D := by
            rw [d.H_eq_Q_sup_D]
            trivial
          rcases Subgroup.mem_sup_of_normal_left.mp hx with
            ⟨q, hq, e, he, hqe⟩
          refine ⟨⟨e, he⟩, ?_⟩
          change pi e = pi x
          rw [← hqe, map_mul]
          have hqQK : q ∈ QK := Subgroup.mem_sup_left hq
          have hpiq : pi q = 1 := (QuotientGroup.eq_one_iff q).2 hqQK
          simp [hpiq]
        exact Group.isSolvable_of_surjective (f := piD) hpiD_surjective
      have hquotient_nontrivial : Nontrivial (d.H ⧸ QK) := by
        rw [QuotientGroup.nontrivial_iff]
        intro hQKtop
        have hVleD : V ≤ D := by
          intro v hv
          rw [hch.1.section2.V_eq] at hv
          exact hv.1
        obtain ⟨v, hvV, hvne⟩ :=
          SetLike.exists_of_lt (show (⊥ : Subgroup G) < V from
            bot_lt_iff_ne_bot.mpr hch.2.V_ne_bot)
        have hvH : v ∈ d.H := by
          rw [hdH]
          exact hch.1.section2.hA.A1.D_le_H (hVleD hvV)
        let vH : d.H := ⟨v, hvH⟩
        have hvQK : vH ∈ QK := by
          rw [hQKtop]
          trivial
        letI : d.Q.Normal := d.Q_normal
        rcases Subgroup.mem_sup_of_normal_left.mp hvQK with
          ⟨q, hq, k, hk, hvqk⟩
        have hqGQ : ((q : d.H) : G) ∈ Q := by
          have hqMap : ((q : d.H) : G) ∈ d.Q.map d.H.subtype :=
            ⟨q, hq, rfl⟩
          rw [← hdQ]
          exact hqMap
        have hkGD : ((k : d.H) : G) ∈ D :=
          hch.1.section2.K_le_D hk
        have hq_eq : q = vH * k⁻¹ := by
          calc
            q = (q * k) * k⁻¹ := by group
            _ = vH * k⁻¹ := by rw [hvqk]
        have hqGD : ((q : d.H) : G) ∈ D := by
          rw [hq_eq]
          exact D.mul_mem (hVleD hvV) (D.inv_mem hkGD)
        have hq_one : q = 1 := by
          apply Subtype.ext
          have hqbot : ((q : d.H) : G) ∈ (⊥ : Subgroup G) :=
            hch.1.section2.hA.A1.Q_disjoint_D.le_bot ⟨hqGQ, hqGD⟩
          simpa using hqbot
        have hvK : v ∈ K := by
          have hvk' : k = vH := by
            simpa [hq_one] using hvqk
          have hvk : vH = k := hvk'.symm
          have hvkG : v = ((k : d.H) : G) := by
            simpa [vH] using congrArg (fun z : d.H => (z : G)) hvk
          have hkK : ((k : d.H) : G) ∈ K := hk
          rw [← hvkG] at hkK
          exact hkK
        have hvFixed : rightConjugateElem v t = v := by
          have hvPeterfalvi : v ∈ peterfalviV D t := by
            rw [← hch.1.section2.V_eq]
            exact hvV
          have hcomm : v * t = t * v :=
            Subgroup.mem_centralizer_singleton_iff.mp hvPeterfalvi.2
          calc
            rightConjugateElem v t = t * v * t := by
              simp [rightConjugateElem,
                hch.1.section2.hA.A1.involution_t.inv_eq_self]
            _ = v * t * t := by rw [← hcomm]
            _ = v * (t * t) := by simp [mul_assoc]
            _ = v * 1 := by
              rw [← pow_two, hch.1.section2.hA.A1.involution_t.sq_eq_one]
            _ = v := mul_one v
        have hvInv : rightConjugateElem v t = v⁻¹ :=
          (hch.1.section2.K_def v).mp hvK |>.2
        have hvEqInv : v = v⁻¹ := hvFixed.symm.trans hvInv
        have hvSq : v ^ 2 = 1 := by
          rw [pow_two]
          nth_rw 2 [hvEqInv]
          exact mul_inv_cancel v
        let vD : D := ⟨v, hVleD hvV⟩
        have hvDsq : vD ^ 2 = 1 := by
          apply Subtype.ext
          exact hvSq
        have hvDone : v = 1 := by
          by_contra hvne'
          have hvDne : vD ≠ 1 := by
            intro h
            exact hvne' (congrArg Subtype.val h)
          have htwo : 2 ∣ orderOf vD := by
            rw [orderOf_eq_prime hvDsq hvDne]
          have horderOdd : Odd (orderOf vD) :=
            Odd.of_dvd_nat hch.1.section2.hA.A1.D_odd
              (orderOf_dvd_natCard vD)
          exact horderOdd.not_two_dvd_nat htwo
        exact hvne (by simp [hvDone])
      letI : Group.IsSolvable (d.H ⧸ QK) := hquotient_solvable
      letI : Nontrivial (d.H ⧸ QK) := hquotient_nontrivial
      obtain ⟨eta, hetaNe⟩ :=
        Section6.exists_nontrivial_linear_character_of_solvable (d.H ⧸ QK)
      let lambda : Section1.ClassFunction d.H :=
        Section1.characterInflationByHom (QuotientGroup.mk' QK) eta
      have hlambdaIrr :
          Section1.IsIrreducibleCharacterOnGroup lambda := by
        exact Section1.characterInflationByHom_isIrreducibleCharacterOnGroup
          (QuotientGroup.mk' QK) eta
      have hlambdaNe : lambda ≠ Section1.principalCharacter d.H := by
        intro hlambdaPrincipal
        apply hetaNe
        apply QuotientGroup.monoidHom_ext
        apply MonoidHom.ext
        intro x
        apply Units.ext
        have hx := congrFun hlambdaPrincipal x
        simpa [lambda, Section1.characterInflationByHom,
          Section1.principalCharacter] using hx
      have hlambdaDegree : Section1.degree lambda = 1 := by
        simp [lambda, Section1.degree, Section1.characterInflationByHom]
      have hlambdaQ1Kernel :
          Section1.subgroupInKernel' lambda d.Q1 := by
        intro q
        have hqQK : (q : d.H) ∈ QK :=
          Subgroup.mem_sup_left (d.Q1_le_Q q.property)
        have hqOne :
            QuotientGroup.mk' QK (q : d.H) = 1 :=
          (QuotientGroup.eq_one_iff _).2 hqQK
        simp [lambda, Section1.characterInflationByHom, hqOne,
          Section1.degree]
      have hlambdaFusion : fusionInvariant lambda := by
        let pi : Set Nat.Primes := subgroupPrimeSet QK
        let VH : Subgroup d.H := V.subgroupOf d.H
        have hVleD : V ≤ D := by
          intro v hv
          rw [hch.1.section2.V_eq] at hv
          exact hv.1
        have hKdisjV : Disjoint K V := by
          rw [Subgroup.disjoint_def]
          intro x hxK hxV
          have hxFixed : rightConjugateElem x t = x := by
            have hxPeter : x ∈ peterfalviV D t := by
              rw [← hch.1.section2.V_eq]
              exact hxV
            have hcomm : t * x = x * t :=
              (Subgroup.mem_centralizer_singleton_iff.mp hxPeter.2).symm
            calc
              rightConjugateElem x t = t * x * t := by
                simp [rightConjugateElem,
                  hch.1.section2.hA.A1.involution_t.inv_eq_self]
              _ = x * (t * t) := by rw [hcomm, mul_assoc]
              _ = x := by
                rw [← pow_two,
                  hch.1.section2.hA.A1.involution_t.sq_eq_one, mul_one]
          have hxInv : rightConjugateElem x t = x⁻¹ :=
            (hch.1.section2.K_def x).mp hxK |>.2
          have hxSq : x ^ 2 = 1 := by
            have hxEqInv : x = x⁻¹ := hxFixed.symm.trans hxInv
            rw [pow_two]
            nth_rw 2 [hxEqInv]
            exact mul_inv_cancel x
          let xD : D := ⟨x, hch.1.section2.K_le_D hxK⟩
          have hxDSq : xD ^ 2 = 1 := Subtype.ext hxSq
          by_contra hxNe
          have hxDNe : xD ≠ 1 := by
            intro h
            exact hxNe (congrArg Subtype.val h)
          have htwo : 2 ∣ orderOf xD := by
            rw [orderOf_eq_prime hxDSq hxDNe]
          have horderOdd : Odd (orderOf xD) :=
            Odd.of_dvd_nat hch.1.section2.hA.A1.D_odd
              (orderOf_dvd_natCard xD)
          exact horderOdd.not_two_dvd_nat htwo
        have hcardKVCoprime : Nat.Coprime (Nat.card K) (Nat.card V) := by
          let KD : Subgroup D := K.subgroupOf D
          let VD : Subgroup D := V.subgroupOf D
          have hKleD : K ≤ D := hch.1.section2.K_le_D
          have hKDcard : Nat.card KD = Nat.card K :=
            natCard_subgroupOf_eq K D hKleD
          have hVDcard : Nat.card VD = Nat.card V :=
            natCard_subgroupOf_eq V D hVleD
          have hKDVD : Disjoint KD VD := by
            rw [Subgroup.disjoint_def]
            intro x hxK hxV
            apply Subtype.ext
            simpa using hKdisjV.le_bot ⟨hxK, hxV⟩
          have hprop2 :=
            PFchapter1section2.proposition_2 H D Q K V W Q0 S Q1 t
              hch.1.section2
          have hKDcyclic : IsCyclic KD :=
            (Subgroup.subgroupOfEquivOfLe hKleD).isCyclic.mpr hprop2.1
          letI : KD.Normal := by
            simpa [KD] using hprop2.2
          letI : MulDistribMulAction D Q1 :=
            Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) D Q1
              hDnormQ1
          let rho : D →* MulAut Q1 := MulDistribMulAction.toMulAut D Q1
          have hfixedRho :
              ∀ a : D, a ≠ 1 → ∀ q : Q1, rho a q = q → q = 1 := by
            intro a ha q hfix
            have hsmul : a • q = q := by
              simpa [rho, MulDistribMulAction.toMulAut_apply] using hfix
            have hfixG :
                (a : G) * (q : G) * (a : G)⁻¹ = (q : G) := by
              rw [← Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
                D Q1 hDnormQ1 a q]
              exact congrArg Subtype.val hsmul
            apply Subtype.ext
            exact hDfixed (a : G) a.property
              (fun haG => ha (Subtype.ext haG)) (q : G) q.property hfixG
          have hrho : Function.Injective rho := by
            rw [← MonoidHom.ker_eq_bot_iff]
            rw [Subgroup.eq_bot_iff_forall]
            intro a ha
            by_contra haOne
            obtain ⟨q, hqQ1, hqne⟩ :=
              SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hQ1)
            let qQ1 : Q1 := ⟨q, hqQ1⟩
            have hrhoa : rho a = 1 := MonoidHom.mem_ker.mp ha
            have hfix : rho a qQ1 = qQ1 := by rw [hrhoa]; rfl
            have hqOne := hfixedRho a haOne qQ1 hfix
            exact hqne (by
              simpa [qQ1] using congrArg Subtype.val hqOne)
          by_contra hcop
          obtain ⟨p, hp, hpK, hpV⟩ :=
            Nat.Prime.not_coprime_iff_dvd.mp hcop
          letI : Fact p.Prime := ⟨hp⟩
          letI : IsCyclic KD := hKDcyclic
          letI : CommGroup KD := hKDcyclic.commGroup
          have hpKD : p ∣ Nat.card KD := by simpa [hKDcard] using hpK
          have hpVD : p ∣ Nat.card VD := by simpa [hVDcard] using hpV
          let OmegaK : Subgroup KD := omega₁ (G := KD) (p := p)
          have hOmegaK_eq :
              OmegaK = (powMonoidHom p : KD →* KD).ker := by
            apply le_antisymm
            · dsimp [OmegaK, omega₁]
              rw [omega]
              refine
                (Subgroup.closure_le
                  (K := (powMonoidHom p : KD →* KD).ker)).2 ?_
              intro x hx
              change x ^ (p ^ 1) = 1 at hx
              simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
            · intro x hx
              dsimp [OmegaK, omega₁]
              rw [omega]
              refine Subgroup.subset_closure ?_
              simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
          have hOmegaKcard : Nat.card OmegaK = p := by
            calc
              Nat.card OmegaK =
                  Nat.card (powMonoidHom p : KD →* KD).ker := by
                    rw [hOmegaK_eq]
              _ = (Nat.card KD).gcd p :=
                IsCyclic.card_powMonoidHom_ker (G := KD) p
              _ = p := Nat.gcd_eq_right_iff_dvd.mpr hpKD
          letI : OmegaK.Characteristic := by
            simpa [OmegaK] using
              (omega₁_characteristic (G := KD) (p := p))
          let KP : Subgroup D := OmegaK.map KD.subtype
          letI : KP.Normal := by
            dsimp [KP]
            infer_instance
          have hKPcard : Nat.card KP = p := by
            dsimp [KP]
            rw [Subgroup.card_map_of_injective KD.subtype_injective,
              hOmegaKcard]
          have hKPleKD : KP ≤ KD := by
            intro x hx
            rcases hx with ⟨y, hy, rfl⟩
            exact y.property
          obtain ⟨v, hvorder⟩ :=
            exists_prime_orderOf_dvd_card' (G := VD) p hpVD
          let vD : D := VD.subtype v
          let VP : Subgroup D := Subgroup.zpowers vD
          have hVPcard : Nat.card VP = p := by
            dsimp [VP]
            rw [Nat.card_zpowers]
            dsimp [vD]
            rw [Subgroup.orderOf_coe, hvorder]
          have hVPleVD : VP ≤ VD := by
            apply Subgroup.zpowers_le.mpr
            exact v.property
          have hKPVP : Disjoint KP VP := hKDVD.mono hKPleKD hVPleVD
          let P0 : Subgroup D := KP ⊔ VP
          let K0 : Subgroup P0 := KP.subgroupOf P0
          let V0 : Subgroup P0 := VP.subgroupOf P0
          have hKPleP0 : KP ≤ P0 := le_sup_left
          have hVPleP0 : VP ≤ P0 := le_sup_right
          have hK0card : Nat.card K0 = p := by
            simpa [K0, natCard_subgroupOf_eq KP P0 hKPleP0] using hKPcard
          have hV0card : Nat.card V0 = p := by
            simpa [V0, natCard_subgroupOf_eq VP P0 hVPleP0] using hVPcard
          have hK0V0 : Disjoint K0 V0 := by
            rw [Subgroup.disjoint_def]
            intro x hxK hxV
            apply Subtype.ext
            simpa using hKPVP.le_bot ⟨hxK, hxV⟩
          have hK0supV0 : K0 ⊔ V0 = ⊤ := by
            calc
              K0 ⊔ V0 = (KP ⊔ VP).subgroupOf P0 := by
                exact (Subgroup.subgroupOf_sup hKPleP0 hVPleP0).symm
              _ = ⊤ := by simp [P0]
          letI : K0.Normal := (inferInstance : KP.Normal).subgroupOf P0
          have hP0card : Nat.card P0 = p * p := by
            have hcomp : K0.IsComplement' V0 :=
              isComplement'_of_disjoint_sup_eq_top_of_normal
                K0 V0 hK0V0 hK0supV0
            simpa [hK0card, hV0card] using hcomp.card_mul.symm
          let A : Subgroup (MulAut Q1) := rho.range
          have hfixedA :
              ∀ phi : A, phi ≠ 1 → ∀ q : Q1,
                (phi : MulAut Q1) q = q → q = 1 := by
            intro phi hphi q hq
            rcases phi.property with ⟨a, hpa⟩
            apply hfixedRho a
            · intro haOne
              apply hphi
              apply Subtype.ext
              simpa [haOne] using hpa.symm
            · simpa [hpa] using hq
          have hclass :=
            External.huppert_V_8_15_fixedPointFree_automorphism_subgroup_classification
              A hfixedA
          have hP0map_leA : P0.map rho ≤ A := by
            intro x hx
            rcases hx with ⟨a, ha, rfl⟩
            exact ⟨a, rfl⟩
          let PA : Subgroup A := (P0.map rho).subgroupOf A
          have hPAcard : Nat.card PA = p * p := by
            calc
              Nat.card PA = Nat.card (P0.map rho) :=
                natCard_subgroupOf_eq (P0.map rho) A hP0map_leA
              _ = Nat.card P0 := Subgroup.card_map_of_injective hrho
              _ = p * p := hP0card
          have hPAcyclic : IsCyclic PA :=
            hclass.2.2 p p hp hp PA hPAcard
          have hP0mapcyclic : IsCyclic (P0.map rho) :=
            (Subgroup.subgroupOfEquivOfLe hP0map_leA).isCyclic.mp hPAcyclic
          have hP0cyclic : IsCyclic P0 :=
            (Subgroup.equivMapOfInjective P0 rho hrho).isCyclic.mpr
              hP0mapcyclic
          letI : IsCyclic P0 := hP0cyclic
          letI : CommGroup P0 := hP0cyclic.commGroup
          let OmegaP0 : Subgroup P0 := omega₁ (G := P0) (p := p)
          have hOmegaP0_eq :
              OmegaP0 = (powMonoidHom p : P0 →* P0).ker := by
            apply le_antisymm
            · dsimp [OmegaP0, omega₁]
              rw [omega]
              refine
                (Subgroup.closure_le
                  (K := (powMonoidHom p : P0 →* P0).ker)).2 ?_
              intro x hx
              change x ^ (p ^ 1) = 1 at hx
              simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
            · intro x hx
              dsimp [OmegaP0, omega₁]
              rw [omega]
              refine Subgroup.subset_closure ?_
              simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
          have hOmegaP0card : Nat.card OmegaP0 = p := by
            calc
              Nat.card OmegaP0 =
                  Nat.card (powMonoidHom p : P0 →* P0).ker := by
                    rw [hOmegaP0_eq]
              _ = (Nat.card P0).gcd p :=
                IsCyclic.card_powMonoidHom_ker (G := P0) p
              _ = p := by simp [hP0card]
          have hK0leOmega : K0 ≤ OmegaP0 := by
            intro x hx
            dsimp [OmegaP0, omega₁]
            rw [omega]
            apply Subgroup.subset_closure
            have hxpow :
                (⟨x, hx⟩ : K0) ^ Nat.card K0 = 1 := pow_card_eq_one'
            have hxpow' : x ^ p = 1 := by
              simpa [hK0card] using congrArg Subtype.val hxpow
            simpa [pow_one] using hxpow'
          have hV0leOmega : V0 ≤ OmegaP0 := by
            intro x hx
            dsimp [OmegaP0, omega₁]
            rw [omega]
            apply Subgroup.subset_closure
            have hxpow :
                (⟨x, hx⟩ : V0) ^ Nat.card V0 = 1 := pow_card_eq_one'
            have hxpow' : x ^ p = 1 := by
              simpa [hV0card] using congrArg Subtype.val hxpow
            simpa [pow_one] using hxpow'
          have hK0eq : K0 = OmegaP0 := by
            apply Subgroup.eq_of_le_of_card_ge hK0leOmega
            rw [hOmegaP0card, hK0card]
          have hV0eq : V0 = OmegaP0 := by
            apply Subgroup.eq_of_le_of_card_ge hV0leOmega
            rw [hOmegaP0card, hV0card]
          have hK0bot : K0 = ⊥ := by
            rw [hK0eq, hV0eq] at hK0V0
            exact hK0eq.trans (disjoint_self.mp hK0V0)
          have hpOne : p = 1 := by
            rw [← hK0card, hK0bot]
            simp
          exact hp.ne_one hpOne
        have hQKVComplement : QK.IsComplement' VH := by
          have hVleH : V ≤ d.H := by
            rw [hdH]
            exact hVleD.trans hch.1.section2.hA.A1.D_le_H
          have hKleH : K ≤ d.H := by
            rw [hdH]
            exact hch.1.section2.K_le_D.trans
              hch.1.section2.hA.A1.D_le_H
          let KH : Subgroup d.H := K.subgroupOf d.H
          have hDmem : ∀ a : d.H, a ∈ d.D ↔ (a : G) ∈ D := by
            intro a
            constructor
            · intro ha
              have hmap : (a : G) ∈ d.D.map d.H.subtype := ⟨a, ha, rfl⟩
              simpa [hdD] using hmap
            · intro ha
              have hmap : (a : G) ∈ d.D.map d.H.subtype := by
                simpa [hdD] using ha
              rcases hmap with ⟨b, hb, hba⟩
              have : b = a := Subtype.ext hba
              simpa [this] using hb
          have htNormD : t ∈ Subgroup.normalizer (D : Set G) := by
            rw [Subgroup.mem_normalizer_iff]
            intro e
            have htInv : t⁻¹ = t :=
              hch.1.section2.hA.A1.involution_t.inv_eq_self
            have htSq : t * t = 1 := by
              simpa [pow_two] using
                hch.1.section2.hA.A1.involution_t.sq_eq_one
            have hforward :
                ∀ a : G, a ∈ D → t * a * t⁻¹ ∈ D := by
              intro a haD
              have haInf : a ∈ H ⊓ rightConjugate H t := by
                simpa [hch.1.section2.hA.A1.D_eq] using haD
              rw [hch.1.section2.hA.A1.D_eq]
              have haRight : a ∈ rightConjugate H t := haInf.2
              rcases (show a ∈ H.conjBy t⁻¹ from by
                simpa [rightConjugate] using haRight) with
                ⟨h, hhH, hmap⟩
              have haEq : t⁻¹ * h * t = a := by
                simpa [MulAut.conj_apply] using hmap
              have htarget : t * a * t⁻¹ = h := by
                calc
                  t * a * t⁻¹ = t * (t⁻¹ * h * t) * t⁻¹ := by rw [haEq]
                  _ = h := by simp [mul_assoc]
              constructor
              · simpa [htarget] using hhH
              · change t * a * t⁻¹ ∈ H.conjBy t⁻¹
                refine ⟨a, haInf.1, ?_⟩
                calc
                  (MulAut.conj t⁻¹) a = t⁻¹ * a * (t⁻¹)⁻¹ := rfl
                  _ = t * a * t⁻¹ := by simp [htInv]
            constructor
            · exact hforward e
            · intro hteD
              have hback := hforward (t * e * t⁻¹) hteD
              have hcollapse : t * (t * (e * (t * t))) = e := by
                calc
                  t * (t * (e * (t * t))) =
                      (t * t) * (e * (t * t)) := by rw [← mul_assoc]
                  _ = e := by simp [htSq]
              simpa [htInv, hcollapse, mul_assoc] using hback
          have hDdecomp :
              ∀ e : G, e ∈ D →
                ∃ v k : G, v ∈ V ∧ k ∈ K ∧ e = v * k := by
            intro e heD
            let Y : Subgroup G := D ⊓ Subgroup.centralizer ({t} : Set G)
            let Z : Set G :=
              {z : G | z ∈ D ∧ rightConjugateElem z t = z⁻¹}
            have hbij :
                Set.BijOn (fun p : Y × Z => (p.1 : G) * (p.2 : G))
                  Set.univ (D : Set G) := by
              simpa [Y, Z] using
                (PFchapter1section1.lemma_a (M := G) t D
                  hch.1.section2.hA.A1.involution_t
                  hch.1.section2.hA.A1.D_odd htNormD).1
            rcases hbij.2.2 heD with ⟨p, _hp, hpEq⟩
            have hvV : (p.1 : G) ∈ V := by
              rw [hch.1.section2.V_eq]
              exact p.1.property
            have hkK : (p.2 : G) ∈ K :=
              (hch.1.section2.K_def (p.2 : G)).mpr p.2.property
            exact ⟨p.1, p.2, hvV, hkK, hpEq.symm⟩
          have hdisj : Disjoint QK VH := by
            rw [Subgroup.disjoint_def]
            intro x hxQK hxV
            letI : d.Q.Normal := d.Q_normal
            rcases Subgroup.mem_sup_of_normal_left.mp hxQK with
              ⟨q, hqQ, k, hkK, hqk⟩
            have hxD : x ∈ d.D := by
              rw [hDmem]
              exact hVleD hxV
            have hkD : k ∈ d.D := by
              rw [hDmem]
              exact hch.1.section2.K_le_D hkK
            have hqEq : q = x * k⁻¹ := by
              calc
                q = (q * k) * k⁻¹ := by group
                _ = x * k⁻¹ := by rw [hqk]
            have hqD : q ∈ d.D := by
              rw [hqEq]
              exact d.D.mul_mem hxD (d.D.inv_mem hkD)
            have hqOne : q = 1 := by
              have hqBot : q ∈ (⊥ : Subgroup d.H) :=
                d.Q_disjoint_D.le_bot ⟨hqQ, hqD⟩
              simpa using hqBot
            have hxEqK : x = k := by simpa [hqOne] using hqk.symm
            have hkV : (k : G) ∈ V := by
              change (x : G) ∈ V at hxV
              rw [hxEqK] at hxV
              exact hxV
            have hkBot : (k : G) ∈ (⊥ : Subgroup G) :=
              hKdisjV.le_bot ⟨hkK, hkV⟩
            apply Subtype.ext
            simpa [hxEqK] using hkBot
          have hsup : QK ⊔ VH = ⊤ := by
            rw [eq_top_iff]
            intro x _hx
            have hxQD : x ∈ d.Q ⊔ d.D := by
              rw [d.H_eq_Q_sup_D]
              trivial
            letI : d.Q.Normal := d.Q_normal
            rcases Subgroup.mem_sup_of_normal_left.mp hxQD with
              ⟨q, hqQ, e, heD, hqe⟩
            obtain ⟨v, k, hvV, hkK, hvk⟩ :=
              hDdecomp (e : G) ((hDmem e).mp heD)
            let vH : d.H := ⟨v, hVleH hvV⟩
            let kH : d.H := ⟨k, hKleH hkK⟩
            have hvMem : vH ∈ VH := hvV
            have hkMem : kH ∈ QK := Subgroup.mem_sup_right hkK
            have hqMem : q ∈ QK := Subgroup.mem_sup_left hqQ
            have hprod : q * vH * kH ∈ QK ⊔ VH :=
              (QK ⊔ VH).mul_mem
                ((QK ⊔ VH).mul_mem
                  (Subgroup.mem_sup_left hqMem)
                  (Subgroup.mem_sup_right hvMem))
                (Subgroup.mem_sup_left hkMem)
            convert hprod using 1
            apply Subtype.ext
            rw [← hqe]
            change (q : G) * (e : G) = (q : G) * v * k
            rw [hvk]
            group
          exact isComplement'_of_disjoint_sup_eq_top_of_normal QK VH hdisj hsup
        have hcardQKVHCoprime :
            Nat.Coprime (Nat.card QK) (Nat.card VH) := by
          have hVleD : V ≤ D := by
            intro v hv
            rw [hch.1.section2.V_eq] at hv
            exact hv.1
          have hVleH : V ≤ d.H := by
            rw [hdH]
            exact hVleD.trans hch.1.section2.hA.A1.D_le_H
          have hKleH : K ≤ d.H := by
            rw [hdH]
            exact hch.1.section2.K_le_D.trans
              hch.1.section2.hA.A1.D_le_H
          let KH : Subgroup d.H := K.subgroupOf d.H
          have hVHleD : VH ≤ d.D := by
            intro v hv
            change (v : G) ∈ V at hv
            have hvD : (v : G) ∈ D := hVleD hv
            have hmap : (v : G) ∈ d.D.map d.H.subtype := by
              simpa [hdD] using hvD
            rcases hmap with ⟨w, hw, hwv⟩
            have : w = v := Subtype.ext hwv
            simpa [this] using hw
          have hcopQVH :
              Nat.Coprime (Nat.card d.Q) (Nat.card VH) :=
            Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hVHleD)
              d.card_Q_coprime_card_D
          have hcardKH : Nat.card KH = Nat.card K :=
            natCard_subgroupOf_eq K d.H hKleH
          have hcardVH : Nat.card VH = Nat.card V :=
            natCard_subgroupOf_eq V d.H hVleH
          have hcopKVH : Nat.Coprime (Nat.card KH) (Nat.card VH) := by
            simpa [hcardKH, hcardVH] using hcardKVCoprime
          let QQK : Subgroup QK := d.Q.subgroupOf QK
          let KQK : Subgroup QK := KH.subgroupOf QK
          have hQQKle : d.Q ≤ QK := le_sup_left
          have hKQKle : KH ≤ QK := le_sup_right
          have hdisjQK : Disjoint QQK KQK := by
            rw [Subgroup.disjoint_def]
            intro x hxQ hxK
            have hxD : (x : d.H) ∈ d.D := by
              have hxDG : (x : G) ∈ D :=
                hch.1.section2.K_le_D hxK
              have hmap : (x : G) ∈ d.D.map d.H.subtype := by
                simpa [hdD] using hxDG
              rcases hmap with ⟨y, hy, hyx⟩
              have : y = (x : d.H) := Subtype.ext hyx
              simpa [this] using hy
            have hxBot : (x : d.H) ∈ (⊥ : Subgroup d.H) :=
              d.Q_disjoint_D.le_bot ⟨hxQ, hxD⟩
            apply Subtype.ext
            simpa using hxBot
          have hsupQK : QQK ⊔ KQK = ⊤ := by
            calc
              QQK ⊔ KQK = (d.Q ⊔ KH).subgroupOf QK := by
                exact (Subgroup.subgroupOf_sup hQQKle hKQKle).symm
              _ = ⊤ := by
                apply Subgroup.subgroupOf_eq_top.mpr
                intro x hx
                exact hx
          letI : QQK.Normal := d.Q_normal.subgroupOf QK
          have hcompQK : QQK.IsComplement' KQK :=
            isComplement'_of_disjoint_sup_eq_top_of_normal
              QQK KQK hdisjQK hsupQK
          have hcardQQK : Nat.card QQK = Nat.card d.Q :=
            natCard_subgroupOf_eq d.Q QK hQQKle
          have hcardKQK : Nat.card KQK = Nat.card KH :=
            natCard_subgroupOf_eq KH QK hKQKle
          have hcardQK : Nat.card QK = Nat.card d.Q * Nat.card KH := by
            simpa [hcardQQK, hcardKQK] using hcompQK.card_mul.symm
          rw [hcardQK]
          exact Nat.Coprime.mul_left hcopQVH hcopKVH
        have hQKHall : IsHallSubgroup pi QK := by
          refine isHallSubgroup_of (G := d.H) pi QK ?_ ?_
          · intro p hp
            simpa [pi, subgroupPrimeSet] using hp
          · intro p hpPi hpIndex
            have hpQK : p.val ∣ Nat.card QK := by
              simpa [pi, subgroupPrimeSet] using hpPi
            have hpVH : p.val ∣ Nat.card VH := by
              rw [← hQKVComplement.symm.index_eq_card]
              exact hpIndex
            exact (Nat.Prime.not_coprime_iff_dvd.mpr
              ⟨p.val, p.property, hpQK, hpVH⟩) hcardQKVHCoprime
        have hVHall : IsHallSubgroup piᶜ VH := by
          refine isHallSubgroup_of (G := d.H) piᶜ VH ?_ ?_
          · intro p hpVH
            have hpNotPi : p ∉ pi := by
              intro hpPi
              have hpQK : p.val ∣ Nat.card QK := by
                simpa [pi, subgroupPrimeSet] using hpPi
              exact (Nat.Prime.not_coprime_iff_dvd.mpr
                ⟨p.val, p.property, hpQK, hpVH⟩) hcardQKVHCoprime
            simpa using hpNotPi
          · intro p hpCompl hpIndex
            have hpQK : p.val ∣ Nat.card QK := by
              rw [← hQKVComplement.index_eq_card]
              exact hpIndex
            have hpPi : p ∈ pi := by
              simpa [pi, subgroupPrimeSet] using hpQK
            exact hpCompl hpPi
        have hHsolvable : Group.IsSolvable d.H := by
          have hsolvableSup :
              ∀ {L : Type u} [Group L] (N R : Subgroup L) [N.Normal],
                Group.IsSolvable N → Group.IsSolvable R →
                  Group.IsSolvable ↥(N ⊔ R : Subgroup L) := by
            intro L _ N R _ hNsolv hRsolv
            let T : Subgroup L := N ⊔ R
            have hNT : N ≤ T := le_sup_left
            have hRT : R ≤ T := le_sup_right
            let NT : Subgroup T := N.subgroupOf T
            haveI : NT.Normal := (inferInstance : N.Normal).subgroupOf T
            have hNTsolv : Group.IsSolvable NT := by
              let eNT : NT ≃* N := Subgroup.subgroupOfEquivOfLe hNT
              letI : Group.IsSolvable N := hNsolv
              exact Group.isSolvable_of_isSolvable_injective
                (f := eNT.toMonoidHom) eNT.injective
            let f : R →* T ⧸ NT :=
              (QuotientGroup.mk' NT).comp (Subgroup.inclusion hRT)
            have hf : Function.Surjective f := by
              intro z
              obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective NT z
              rcases Subgroup.mem_sup_of_normal_left.mp w.property with
                ⟨n, hn, r, hr, hnr⟩
              let rR : R := ⟨r, hr⟩
              refine ⟨rR, ?_⟩
              change QuotientGroup.mk' NT (⟨r, hRT hr⟩ : T) =
                QuotientGroup.mk' NT w
              have hnrT :
                  (⟨n, hNT hn⟩ : T) * ⟨r, hRT hr⟩ = w :=
                Subtype.ext hnr
              rw [← hnrT, map_mul]
              have hnNT : (⟨n, hNT hn⟩ : T) ∈ NT := hn
              have hmkN :
                  QuotientGroup.mk' NT (⟨n, hNT hn⟩ : T) = 1 :=
                (QuotientGroup.eq_one_iff _).2 hnNT
              rw [hmkN, one_mul]
            have hquotSolv : Group.IsSolvable (T ⧸ NT) := by
              letI : Group.IsSolvable R := hRsolv
              exact Group.isSolvable_of_surjective (f := f) hf
            letI : Group.IsSolvable NT := hNTsolv
            letI : Group.IsSolvable (T ⧸ NT) := hquotSolv
            exact Group.isSolvable_of_ker_le_range NT.subtype
              (QuotientGroup.mk' NT) (by
                rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
          letI : d.Q1.Normal := d.Q1_normal
          have hQ1solv : Group.IsSolvable d.Q1 :=
            _root_.CFSG.odd_order_theorem d.Q1 d.Q1_odd
          have hSsolv : Group.IsSolvable d.S := by
            letI : Group.IsNilpotent d.S := d.S_nilpotent
            exact IsNilpotent.to_isSolvable
          have hQsupSolv : Group.IsSolvable ↥(d.Q1 ⊔ d.S) :=
            hsolvableSup d.Q1 d.S hQ1solv hSsolv
          have hQeq : d.Q1 ⊔ d.S = d.Q := by
            rw [sup_comm, d.Q_eq_S_sup_Q1]
          have hQsolv : Group.IsSolvable d.Q := by
            rw [hQeq] at hQsupSolv
            exact hQsupSolv
          have hKleH : K ≤ d.H := by
            rw [hdH]
            exact hch.1.section2.K_le_D.trans
              hch.1.section2.hA.A1.D_le_H
          let KH : Subgroup d.H := K.subgroupOf d.H
          have hKHsolv : Group.IsSolvable KH := by
            have hKcyclic : IsCyclic K :=
              (PFchapter1section2.proposition_2 H D Q K V W Q0 S Q1 t
                hch.1.section2).1
            letI : IsCyclic K := hKcyclic
            letI : CommGroup K := IsCyclic.commGroup
            letI : Group.IsSolvable K := inferInstance
            let eKH : KH ≃* K := Subgroup.subgroupOfEquivOfLe hKleH
            exact Group.isSolvable_of_isSolvable_injective
              (f := eKH.toMonoidHom) eKH.injective
          letI : d.Q.Normal := d.Q_normal
          have hQKsolv : Group.IsSolvable QK := by
            have hsupSolv : Group.IsSolvable ↥(d.Q ⊔ KH) :=
              hsolvableSup d.Q KH hQsolv hKHsolv
            simpa [QK, KH] using hsupSolv
          letI : Group.IsSolvable QK := hQKsolv
          letI : Group.IsSolvable (d.H ⧸ QK) := hquotient_solvable
          exact Group.isSolvable_of_ker_le_range QK.subtype
            (QuotientGroup.mk' QK) (by
              rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
        have hcomponentPair :
            ∀ (x : d.H) (g : G) (hxg : g * (x : G) * g⁻¹ ∈ d.H),
              ∃ y z : d.H,
                Nat.Coprime (orderOf y) (Nat.card QK) ∧
                  Nat.Coprime (orderOf z) (Nat.card QK) ∧
                    lambda x = lambda y ∧
                      lambda ⟨g * (x : G) * g⁻¹, hxg⟩ = lambda z ∧
                        (z : G) = g * (y : G) * g⁻¹ := by
          have hcardH : Nat.card d.H = Nat.card QK * QK.index := by
            rw [Nat.mul_comm]
            exact (Subgroup.index_mul_card (H := QK)).symm
          have hcoprimeIndex : Nat.Coprime (Nat.card QK) QK.index :=
            hQKHall.card_coprime_index
          let e : ℕ := Nat.chineseRemainder hcoprimeIndex 0 1
          have heQK : e ≡ 0 [MOD Nat.card QK] :=
            (Nat.chineseRemainder hcoprimeIndex 0 1).property.1
          have heIndex : e ≡ 1 [MOD QK.index] :=
            (Nat.chineseRemainder hcoprimeIndex 0 1).property.2
          have hcomponentValue :
              ∀ a : d.H,
                Nat.Coprime (orderOf (a ^ e)) (Nat.card QK) ∧
                  lambda a = lambda (a ^ e) := by
            intro a
            have hacard : a ^ (Nat.card QK * QK.index) = 1 := by
              rw [← hcardH]
              exact pow_card_eq_one'
            have haeIndex : (a ^ e) ^ QK.index = 1 := by
              rw [← pow_mul]
              rw [Nat.modEq_zero_iff_dvd] at heQK
              obtain ⟨k, hk⟩ := heQK
              rw [hk]
              calc
                a ^ (Nat.card QK * k * QK.index) =
                    a ^ ((Nat.card QK * QK.index) * k) := by ring_nf
                _ = (a ^ (Nat.card QK * QK.index)) ^ k := by rw [pow_mul]
                _ = 1 := by rw [hacard, one_pow]
            have horderAe : orderOf (a ^ e) ∣ QK.index :=
              orderOf_dvd_of_pow_eq_one haeIndex
            have hcopAe :
                Nat.Coprime (orderOf (a ^ e)) (Nat.card QK) :=
              Nat.Coprime.of_dvd_left horderAe hcoprimeIndex.symm
            refine ⟨hcopAe, ?_⟩
            let c : d.H := a * (a ^ e)⁻¹
            have haQKIndex :
                (a ^ Nat.card QK) ^ QK.index = 1 := by
              rw [← pow_mul]
              exact hacard
            have haeQK :
                (a ^ e) ^ Nat.card QK = a ^ Nat.card QK := by
              calc
                (a ^ e) ^ Nat.card QK = (a ^ Nat.card QK) ^ e := by
                  simp only [← pow_mul]
                  rw [Nat.mul_comm]
                _ = (a ^ Nat.card QK) ^ 1 :=
                  pow_eq_pow_of_modEq heIndex haQKIndex
                _ = a ^ Nat.card QK := pow_one _
            have hcQK : c ^ Nat.card QK = 1 := by
              rw [Commute.mul_pow]
              · rw [inv_pow, haeQK, mul_inv_cancel]
              · exact (Commute.self_pow a e).inv_right
            have horderC : orderOf c ∣ Nat.card QK :=
              orderOf_dvd_of_pow_eq_one hcQK
            let q : d.H →* d.H ⧸ QK := QuotientGroup.mk' QK
            have horderMapQK : orderOf (q c) ∣ Nat.card QK :=
              (orderOf_map_dvd q c).trans horderC
            have horderMapIndex : orderOf (q c) ∣ QK.index := by
              simpa [q, Subgroup.index] using orderOf_dvd_natCard (q c)
            have horderMap : orderOf (q c) = 1 :=
              Nat.eq_one_of_dvd_coprimes hcoprimeIndex
                horderMapQK horderMapIndex
            have hcMem : c ∈ QK := by
              rw [← QuotientGroup.eq_one_iff]
              exact orderOf_eq_one_iff.mp horderMap
            have hetaC : eta ((QuotientGroup.mk' QK) c) = 1 := by
              simpa only [QuotientGroup.coe_mk', map_one] using
                congrArg eta
                  ((QuotientGroup.eq_one_iff (N := QK) c).2 hcMem)
            have hca : c * a ^ e = a := by
              simp [c]
            change
              (eta ((QuotientGroup.mk' QK) a) : ℂ) =
                (eta ((QuotientGroup.mk' QK) (a ^ e)) : ℂ)
            have hunit :
                eta ((QuotientGroup.mk' QK) a) =
                  eta ((QuotientGroup.mk' QK) (a ^ e)) := by
              calc
                eta ((QuotientGroup.mk' QK) a) =
                    eta ((QuotientGroup.mk' QK) (c * a ^ e)) := by
                  rw [hca]
                _ = eta ((QuotientGroup.mk' QK) c) *
                    eta ((QuotientGroup.mk' QK) (a ^ e)) := by
                  rw [map_mul, map_mul]
                _ = eta ((QuotientGroup.mk' QK) (a ^ e)) := by
                  rw [hetaC, one_mul]
            exact congrArg (fun u : ℂˣ => (u : ℂ)) hunit
          intro x g hxg
          let xg : d.H := ⟨g * (x : G) * g⁻¹, hxg⟩
          refine ⟨x ^ e, xg ^ e, (hcomponentValue x).1,
            (hcomponentValue xg).1, (hcomponentValue x).2,
            (hcomponentValue xg).2, ?_⟩
          change (g * (x : G) * g⁻¹) ^ e =
            g * ((x : G) ^ e) * g⁻¹
          exact (map_pow (MulAut.conj g) (x : G) e).symm
        have hHallConjugateIntoV :
            ∀ y : d.H, Nat.Coprime (orderOf y) (Nat.card QK) →
              ∃ h : d.H, ((h * y * h⁻¹ : d.H) : G) ∈ V := by
          intro y hyCoprime
          let Y : Subgroup d.H := Subgroup.zpowers y
          have hYpi : IsPiSubgroup piᶜ Y := by
            intro p hpY
            have hpOrder : p.val ∣ orderOf y := by
              simpa [Y, Nat.card_zpowers] using hpY
            have hpNotCard : ¬ p.val ∣ Nat.card QK := by
              intro hpCard
              exact (Nat.Prime.not_coprime_iff_dvd.mpr
                ⟨p.val, p.property, hpOrder, hpCard⟩) hyCoprime
            have hpNotPi : p ∉ pi := by
              simpa [pi, subgroupPrimeSet] using hpNotCard
            simpa using hpNotPi
          let A := Multiplicative (ZMod 1)
          let rho : A →* MulAut d.H := 1
          letI : MulDistribMulAction A d.H :=
            MulDistribMulAction.compHom d.H rho
          have hcopA : Nat.Coprime (Nat.card A) (Nat.card d.H) := by
            simp [A]
          have hYinv : IsInvariant A d.H Y := by
            refine ⟨?_⟩
            intro a x
            change x ∈ Y ↔ rho a x ∈ Y
            simp [rho]
          obtain ⟨J, hJHall, _hJinv, hYJ⟩ :=
            exists_isHallSubgroup_isInvariant_of_isPiSubgroup
              (G := d.H) (A := A) hHsolvable hcopA piᶜ Y hYpi hYinv
          obtain ⟨h, hconj⟩ :=
            exists_conj_eq_of_isHallSubgroup_of_solvable
              hHsolvable hJHall hVHall
          refine ⟨h, ?_⟩
          have hyJ : y ∈ J := hYJ (Subgroup.mem_zpowers y)
          have hyMap : (MulAut.conj h) y ∈
              J.map (MulAut.conj h).toMonoidHom :=
            Subgroup.mem_map_of_mem (MulAut.conj h).toMonoidHom hyJ
          rw [← hconj] at hyMap
          change ((h * y * h⁻¹ : d.H) : G) ∈ V
          change h * y * h⁻¹ ∈ V.subgroupOf d.H at hyMap
          exact hyMap
        have hVFusionValues :
            ∀ (y z : d.H),
              Nat.Coprime (orderOf y) (Nat.card QK) →
                Nat.Coprime (orderOf z) (Nat.card QK) →
                  (∃ g : G, (z : G) = g * (y : G) * g⁻¹) →
                    lambda z = lambda y := by
          have hVleD : V ≤ D := by
            intro v hv
            rw [hch.1.section2.V_eq] at hv
            exact hv.1
          have hVleH : V ≤ d.H := by
            rw [hdH]
            exact hVleD.trans hch.1.section2.hA.A1.D_le_H
          have hlambdaConj :
              ∀ a b : d.H, lambda (a * b * a⁻¹) = lambda b := by
            intro a b
            change
              (eta ((QuotientGroup.mk' QK) (a * b * a⁻¹)) : ℂ) =
                (eta ((QuotientGroup.mk' QK) b) : ℂ)
            congr 1
            simp only [map_mul, map_inv]
            calc
              eta ((QuotientGroup.mk' QK) a) *
                    eta ((QuotientGroup.mk' QK) b) *
                    (eta ((QuotientGroup.mk' QK) a))⁻¹ =
                  eta ((QuotientGroup.mk' QK) b) *
                    (eta ((QuotientGroup.mk' QK) a) *
                      (eta ((QuotientGroup.mk' QK) a))⁻¹) := by ac_rfl
              _ = eta ((QuotientGroup.mk' QK) b) := by simp
          intro y z hyCoprime hzCoprime hyz
          obtain ⟨hy, hyV⟩ := hHallConjugateIntoV y hyCoprime
          obtain ⟨hz, hzV⟩ := hHallConjugateIntoV z hzCoprime
          let yV : d.H := hy * y * hy⁻¹
          let zV : d.H := hz * z * hz⁻¹
          rcases hyz with ⟨g, hzg⟩
          let a : G := (hz : G) * g * (hy : G)⁻¹
          have hconjV : (zV : G) = a * (yV : G) * a⁻¹ := by
            dsimp [zV, yV, a]
            rw [hzg]
            group
          have hsetConj :
              ({(zV : G)} : Set G) =
                rightConjugateSet ({(yV : G)} : Set G) a⁻¹ := by
            ext w
            simp [rightConjugateSet, rightConjugateElem, hconjV]
          obtain ⟨v, hvSet⟩ :=
            PFchapter1section3.lemma_2 H D Q K V W Q0 S Q1 t s hch.1
              ({(yV : G)} : Set G) ({(zV : G)} : Set G)
              (by
                intro w hw
                have hw' : w = (yV : G) := by simpa using hw
                rw [hw']
                exact hyV)
              (by
                intro w hw
                have hw' : w = (zV : G) := by simpa using hw
                rw [hw']
                exact hzV)
              ⟨a⁻¹, hsetConj⟩
          have hpoint :
              (zV : G) = rightConjugateElem (yV : G) (v : G) := by
            have hzMem : (zV : G) ∈
                rightConjugateSet ({(yV : G)} : Set G) (v : G) := by
              rw [← hvSet]
              simp
            simpa [rightConjugateSet] using hzMem
          let vH : d.H := ⟨(v : G), hVleH v.property⟩
          have hpointH : zV = vH⁻¹ * yV * vH := by
            apply Subtype.ext
            simpa [vH, rightConjugateElem] using hpoint
          have hmid : lambda zV = lambda yV := by
            rw [hpointH]
            simpa using hlambdaConj vH⁻¹ yV
          have hyValue : lambda yV = lambda y := by
            exact hlambdaConj hy y
          have hzValue : lambda zV = lambda z := by
            exact hlambdaConj hz z
          exact hzValue.symm.trans (hmid.trans hyValue)
        intro x g hxg
        obtain ⟨y, z, hyCoprime, hzCoprime, hxy, hxgz, hyz⟩ :=
          hcomponentPair x g hxg
        rw [hxgz, hVFusionValues y z hyCoprime hzCoprime ⟨g, hyz⟩, ← hxy]
      have hlambdaChar :
          Section1.IsCharacter (Section1.inducedCF d.H lambda) := by
        exact Section1.isCharacter_inducedCF_of_isCharacter d.H lambda
          (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hlambdaIrr)
      have hprincipalInducedNorm :
          Section1.scalarProduct G
              (Section1.inducedCF d.H (Section1.principalCharacter d.H))
              (Section1.inducedCF d.H (Section1.principalCharacter d.H)) = 2 := by
        letI : Fintype (DoubleCoset.Quotient (d.H : Set G) d.H) :=
          Fintype.ofFinite _
        have hdoubleCosetCard :
            Nat.card (DoubleCoset.Quotient (d.H : Set G) d.H) = 2 := by
          letI : Finite (DoubleCoset.Quotient (d.H : Set G) d.H) :=
            Quotient.finite _
          obtain ⟨base, hHbase⟩ :=
            hch.1.section2.hA.A1.point_stabilizer
          have hdHbase : d.H = MulAction.stabilizer G base :=
            hdH.trans hHbase
          have htH : t ∉ d.H := by
            intro ht
            apply hch.1.section2.hA.A1.t_not_mem_H
            rw [← hdH]
            exact ht
          let q0 : DoubleCoset.Quotient (d.H : Set G) d.H :=
            DoubleCoset.mk d.H d.H 1
          let qt : DoubleCoset.Quotient (d.H : Set G) d.H :=
            DoubleCoset.mk d.H d.H t
          have htbase : t • base ≠ base := by
            intro htfix
            apply htH
            rw [hdHbase, MulAction.mem_stabilizer_iff]
            exact htfix
          have houtside :
              ∀ g : G, g ∉ d.H → DoubleCoset.mk d.H d.H g = qt := by
            intro g hgH
            have hgbase : g • base ≠ base := by
              intro hgfix
              apply hgH
              rw [hdHbase, MulAction.mem_stabilizer_iff]
              exact hgfix
            obtain ⟨h, hhtbase, hhbase⟩ :=
              (MulAction.is_two_pretransitive_iff.mp
                hch.1.section2.hA.A1.two_transitive) htbase hgbase
            have hhH : h ∈ d.H := by
              rw [hdHbase, MulAction.mem_stabilizer_iff]
              exact hhbase
            let k : G := g⁻¹ * h * t
            have hkfix : k • base = base := by
              calc
                k • base = g⁻¹ • (h • (t • base)) := by
                  simp [k, mul_smul]
                _ = g⁻¹ • (g • base) := by rw [hhtbase]
                _ = base := by simp
            have hkH : k ∈ d.H := by
              rw [hdHbase, MulAction.mem_stabilizer_iff]
              exact hkfix
            have hfactor : g = h * t * k⁻¹ := by
              dsimp [k]
              group
            change DoubleCoset.mk d.H d.H g = DoubleCoset.mk d.H d.H t
            exact ((DoubleCoset.eq (H := d.H) (K := d.H) (a := t) (b := g)).mpr
              ⟨h, hhH, k⁻¹, d.H.inv_mem hkH, hfactor⟩).symm
          have hcases :
              ∀ q : DoubleCoset.Quotient (d.H : Set G) d.H,
                q = q0 ∨ q = qt := by
            intro q
            by_cases hqH : q.out ∈ d.H
            · left
              calc
                q = DoubleCoset.mk d.H d.H q.out :=
                  (DoubleCoset.out_eq' (H := d.H) (K := d.H) q).symm
                _ = DoubleCoset.mk d.H d.H 1 := by
                  apply (DoubleCoset.eq (H := d.H) (K := d.H) (a := q.out) (b := 1)).mpr
                  exact ⟨q.out⁻¹, d.H.inv_mem hqH, 1, d.H.one_mem, by simp⟩
                _ = q0 := rfl
            · right
              calc
                q = DoubleCoset.mk d.H d.H q.out :=
                  (DoubleCoset.out_eq' (H := d.H) (K := d.H) q).symm
                _ = qt := houtside q.out hqH
          have hne : q0 ≠ qt := by
            intro heq
            apply htH
            change DoubleCoset.mk d.H d.H 1 =
              DoubleCoset.mk d.H d.H t at heq
            rcases (DoubleCoset.eq (H := d.H) (K := d.H) (a := 1) (b := t)).mp heq with
              ⟨h, hh, k, hk, ht⟩
            rw [ht]
            simpa using d.H.mul_mem hh hk
          rw [Nat.card_eq_two_iff]
          refine ⟨q0, qt, hne, ?_⟩
          ext q
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
            Set.mem_univ, iff_true]
          exact hcases q
        have hprincipalClass :
            Section1.IsClassFunction (Section1.principalCharacter d.H) := by
          intro x g
          simp [Section1.principalCharacter]
        have hsummand :
            ∀ q : DoubleCoset.Quotient (d.H : Set G) d.H,
              Section1.scalarProduct d.H
                  (Section1.principalCharacter d.H)
                  (Section1.mackeySummand d.H d.H q.out
                    (Section1.principalCharacter d.H)) = 1 := by
          intro q
          letI : Fintype (Section1.mackeyIntersection d.H d.H q.out) :=
            Fintype.ofFinite _
          rw [Section1.scalarProduct_mackeySummand_right d.H q.out
            (Section1.principalCharacter d.H)
            (Section1.principalCharacter d.H) hprincipalClass]
          simp [Section1.scalarProduct, Section1.subgroupRestriction,
            Section1.mackeyConjugateRestriction, Section1.principalCharacter]
        rw [Section1.scalarProduct_inducedCF_inducedCF_left d.H]
        rw [Section1.mackey_restriction_inducedCF d.H d.H
          (Section1.principalCharacter d.H) hprincipalClass]
        unfold Section1.mackeyRestrictionSum Section1.familySum
        rw [Section1.scalarProduct_fintype_sum_right]
        simp only [hsummand, Finset.sum_const, Finset.card_univ]
        have hdoubleComplex :=
          congrArg (fun n : ℕ => (n : ℂ)) hdoubleCosetCard
        simpa [Nat.card_eq_fintype_card] using hdoubleComplex
      have hinducedNormEqPrincipal :
          Section1.scalarProduct G
              (Section1.inducedCF d.H lambda)
              (Section1.inducedCF d.H lambda) =
            Section1.scalarProduct G
              (Section1.inducedCF d.H (Section1.principalCharacter d.H))
              (Section1.inducedCF d.H (Section1.principalCharacter d.H)) := by
        have hrestrictionTwist :
            Section1.subgroupRestriction d.H
                (Section1.inducedCF d.H lambda) =
              lambda * Section1.subgroupRestriction d.H
                (Section1.inducedCF d.H
                  (Section1.principalCharacter d.H)) := by
          letI : Fintype G := Fintype.ofFinite _
          ext x
          simp only [Section1.subgroupRestriction, Pi.mul_apply]
          change Section1.inducedClassFunction d.H lambda (x : G) =
            lambda x * Section1.inducedClassFunction d.H
              (Section1.principalCharacter d.H) (x : G)
          unfold Section1.inducedClassFunction
          have hsum :
              (∑ g : G,
                if hg : g * (x : G) * g⁻¹ ∈ d.H then
                  lambda ⟨g * (x : G) * g⁻¹, hg⟩
                else 0) =
                lambda x *
                  ∑ g : G,
                    if hg : g * (x : G) * g⁻¹ ∈ d.H then
                      (1 : ℂ)
                    else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro g _
            by_cases hg : g * (x : G) * g⁻¹ ∈ d.H
            · simpa [hg] using hlambdaFusion x g hg
            · simp [hg]
          simp only [Section1.principalCharacter]
          rw [hsum]
          ring
        have hlambdaUnitary :
            ∀ x : d.H, lambda x * star (lambda x) = 1 := by
          intro x
          have hfiniteQuotient :
              IsOfFinOrder ((QuotientGroup.mk' QK) x) :=
            isOfFinOrder_of_finite _
          have hfiniteEta :
              IsOfFinOrder (eta ((QuotientGroup.mk' QK) x)) :=
            eta.isOfFinOrder hfiniteQuotient
          have hfiniteComplex :
              IsOfFinOrder ((eta ((QuotientGroup.mk' QK) x) : ℂ)) :=
            (Units.coeHom ℂ).isOfFinOrder hfiniteEta
          have hnorm : ‖lambda x‖ = 1 := by
            simpa [lambda, Section1.characterInflationByHom] using
              hfiniteComplex.norm_eq_one
          simpa [hnorm] using Complex.mul_conj' (lambda x)
        rw [Section1.scalarProduct_inducedCF_inducedCF_left d.H,
          Section1.scalarProduct_inducedCF_inducedCF_left d.H,
          hrestrictionTwist]
        unfold Section1.scalarProduct
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        simp only [Pi.mul_apply, Section1.principalCharacter,
          one_mul]
        rw [star_mul]
        calc
          lambda x *
              (star (Section1.subgroupRestriction d.H
                  (Section1.inducedCF d.H
                    (Section1.principalCharacter d.H)) x) *
                star (lambda x)) =
            (lambda x * star (lambda x)) *
              star (Section1.subgroupRestriction d.H
                (Section1.inducedCF d.H
                  (Section1.principalCharacter d.H)) x) := by ring
          _ = star (Section1.subgroupRestriction d.H
              (Section1.inducedCF d.H
                (Section1.principalCharacter d.H)) x) := by
            rw [hlambdaUnitary x, one_mul]
      have hlambdaNorm :
          Section1.scalarProduct G
              (Section1.inducedCF d.H lambda)
              (Section1.inducedCF d.H lambda) = 2 := by
        rw [hinducedNormEqPrincipal]
        exact hprincipalInducedNorm
      have hlambdaPrincipal :
          Section1.scalarProduct G
              (Section1.inducedCF d.H lambda)
              (Section1.principalCharacter G) = 0 := by
        have hprincipalClass :
            Section1.IsClassFunction (Section1.principalCharacter G) := by
          intro x g
          simp [Section1.principalCharacter]
        rw [Section1.scalarProduct_inducedCF_left d.H lambda
          (Section1.principalCharacter G) hprincipalClass]
        have hprincipalRestriction :
            Section1.subgroupRestriction d.H
                (Section1.principalCharacter G) =
              Section1.principalCharacter d.H := by
          ext x
          rfl
        rw [hprincipalRestriction]
        exact
          Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
            hlambdaIrr hlambdaNe
      exact ⟨lambda, hlambdaIrr, hlambdaNe, hlambdaDegree,
        hlambdaQ1Kernel, hlambdaChar, hlambdaNorm, hlambdaPrincipal⟩
    obtain ⟨lambda, hlambdaIrr, hlambdaNe, hlambdaDegree,
      hlambdaQ1Kernel, hlambdaChar, hlambdaNorm, hlambdaPrincipal⟩ :=
        hlinear_character_data
    have hinduced_pair :
        ∃ (f1 f2 : Section1.ClassFunction G) (n1 n2 : ℕ),
          Section1.IsIrreducibleCharacterOnGroup f1 ∧
            Section1.IsIrreducibleCharacterOnGroup f2 ∧
              f1 ≠ f2 ∧
              f1 ≠ Section1.principalCharacter G ∧
                f2 ≠ Section1.principalCharacter G ∧
                  Section1.inducedCF d.H lambda = f1 + f2 ∧
                    Section1.degree f1 = (n1 : ℂ) ∧
                      Section1.degree f2 = (n2 : ℂ) ∧
                        n1 + n2 = Nat.card Q + 1 := by
      classical
      have hHindex : H.index = Nat.card Q + 1 := by
        obtain ⟨base, hHbase⟩ :=
          hch.1.section2.hA.A1.point_stabilizer
        let beta : Ω := t⁻¹ • base
        have hbetaNe : beta ≠ base := by
          intro hbeta
          apply hch.1.section2.hA.A1.t_not_mem_H
          rw [hHbase, MulAction.mem_stabilizer_iff]
          have htInv : t⁻¹ = t :=
            hch.1.section2.hA.A1.involution_t.inv_eq_self
          simpa [beta, htInv] using hbeta
        have hDbase :
            D = MulAction.stabilizer G base ⊓
              MulAction.stabilizer G beta := by
          simpa [beta, hHbase, rightConjugate_stabilizer] using
            hch.1.section2.hA.A1.D_eq
        have hcardRegular :=
          (hypothesisA1_Q_regular_on_complement
            (by simpa [hHbase] using hch.1.section2.hA.A1)
            hbetaNe hDbase).ncard_eq
        have hcardQ :
            Nat.card Q = ({w : Ω | w ≠ base} : Set Ω).ncard := by
          simpa using hcardRegular
        have hsum := Set.ncard_add_ncard_compl ({base} : Set Ω)
        rw [Set.ncard_singleton] at hsum
        have hcompl :
            ({base} : Set Ω)ᶜ = ({w : Ω | w ≠ base} : Set Ω) := by
          ext w
          simp
        have hcardOmega : Nat.card Ω = Nat.card Q + 1 := by
          rw [hcompl, ← hcardQ] at hsum
          simpa [Nat.add_comm] using hsum.symm
        calc
          H.index = (MulAction.stabilizer G base).index := by rw [hHbase]
          _ = Nat.card Ω := by
            letI : MulAction.IsMultiplyPretransitive G Ω 2 :=
              hch.1.section2.hA.A1.two_transitive
            haveI : MulAction.IsPretransitive G Ω :=
              MulAction.isPretransitive_of_is_two_pretransitive
            exact MulAction.index_stabilizer_of_transitive
              (G := G) (x := base)
          _ = Nat.card Q + 1 := hcardOmega
      have hindex : d.H.index = Nat.card Q + 1 := by
        rw [hdH]
        exact hHindex
      let phi := Section1.inducedCF d.H lambda
      have hphiNorm : Section1.scalarProduct G phi phi = 2 := by
        simpa [phi] using hlambdaNorm
      have hphiPrincipal :
          Section1.scalarProduct G phi
            (Section1.principalCharacter G) = 0 := by
        simpa [phi] using hlambdaPrincipal
      have hphiNe : phi ≠ 0 := by
        intro hzero
        have hnormZero : Section1.scalarProduct G phi phi = 0 := by
          rw [hzero]
          unfold Section1.scalarProduct
          simp
        norm_num [hnormZero] at hphiNorm
      rcases Section1.exists_positive_irreducible_decomposition_of_character
          phi hlambdaChar hphiNe with
        ⟨ι, hι, hdec, e, psi, i0, hepos, hpsiBook, hpair, hdecomp⟩
      letI : Fintype ι := hι
      letI : DecidableEq ι := hdec
      have hpsiIrr :
          ∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (psi i) := by
        intro i
        exact
          Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
            (psi i) (hpsiBook i)
      have horth : ∀ i j : ι,
          Section1.scalarProduct G (psi i) (psi j) =
            if i = j then 1 else 0 := by
        intro i j
        by_cases hij : i = j
        · subst j
          simp [Section1.scalarProduct_irreducibleCharacter_self (hpsiIrr i)]
        · rw [if_neg hij]
          exact
            Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
              (hpsiIrr i) (hpsiIrr j) (hpair hij)
      have hmult : ∀ i : ι,
          Section1.scalarProduct G phi (psi i) = (e i : ℂ) := by
        intro i
        exact Section1.proposition_1_7_multiplicity_from_decomposition
          e psi phi horth hdecomp i
      have hsumComplex :
          (∑ i : ι, ((e i : ℂ) * (e i : ℂ))) = 2 := by
        calc
          (∑ i : ι, ((e i : ℂ) * (e i : ℂ))) =
              ∑ i : ι, star (e i : ℂ) *
                Section1.scalarProduct G phi (psi i) := by
                  apply Finset.sum_congr rfl
                  intro i _hi
                  rw [hmult i]
                  simp
          _ = Section1.scalarProduct G phi
              (Section1.weightedFamilySum (fun i => (e i : ℂ)) psi) := by
                simpa only [show @Finset.univ ι (Fintype.ofFinite ι) =
                    @Finset.univ ι hι by ext; simp] using
                  (Section1.scalarProduct_weightedFamilySum_right
                    phi (fun i => (e i : ℂ)) psi).symm
          _ = Section1.scalarProduct G phi phi := by rw [← hdecomp]
          _ = 2 := hphiNorm
      have hsumNat : ∑ i : ι, e i ^ 2 = 2 := by
        have h : ∑ i : ι, e i * e i = 2 := by
          exact_mod_cast hsumComplex
        simpa [pow_two] using h
      have hei0SqLe : e i0 ^ 2 ≤ 2 := by
        calc
          e i0 ^ 2 ≤ ∑ i : ι, e i ^ 2 :=
            Finset.single_le_sum (f := fun i => e i ^ 2)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i0)
          _ = 2 := hsumNat
      have hei0 : e i0 = 1 := by
        have hi0pos := hepos i0
        nlinarith [hei0SqLe]
      have hrestSum :
          ∑ i ∈ (Finset.univ.erase i0), e i ^ 2 = 1 := by
        have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
          (fun i => e i ^ 2) (Finset.mem_univ i0)
        rw [hsumNat] at hsplit
        change (∑ i ∈ Finset.univ.erase i0, e i ^ 2) + e i0 ^ 2 = 2
          at hsplit
        rw [hei0] at hsplit
        norm_num at hsplit ⊢
        omega
      have hrestNonempty :
          (Finset.univ.erase i0 : Finset ι).Nonempty := by
        by_contra hnone
        have hempty : (Finset.univ.erase i0 : Finset ι) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnone
        rw [hempty] at hrestSum
        simp at hrestSum
      have hrestCardLe :
          (Finset.univ.erase i0 : Finset ι).card ≤ 1 := by
        calc
          (Finset.univ.erase i0 : Finset ι).card =
              ∑ _i ∈ (Finset.univ.erase i0 : Finset ι), 1 := by simp
          _ ≤ ∑ i ∈ (Finset.univ.erase i0 : Finset ι), e i ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hipos := hepos i
            nlinarith
          _ = 1 := hrestSum
      have hrestCard :
          (Finset.univ.erase i0 : Finset ι).card = 1 := by
        have hpos := Finset.card_pos.mpr hrestNonempty
        omega
      rcases Finset.card_eq_one.mp hrestCard with ⟨j, hrestEq⟩
      have hjmem : j ∈ Finset.univ.erase i0 := by rw [hrestEq]; simp
      have hij : i0 ≠ j := (Finset.mem_erase.mp hjmem).1.symm
      have hej : e j = 1 := by
        rw [hrestEq] at hrestSum
        simp at hrestSum
        have hjpos := hepos j
        nlinarith
      have huniv : (Finset.univ : Finset ι) = {i0, j} := by
        calc
          (Finset.univ : Finset ι) =
              insert i0 (Finset.univ.erase i0) :=
            (Finset.insert_erase (Finset.mem_univ i0)).symm
          _ = {i0, j} := by rw [hrestEq]
      let f1 := psi i0
      let f2 := psi j
      have hdecompPair : phi = f1 + f2 := by
        rw [hdecomp]
        ext g
        unfold Section1.weightedFamilySum
        rw [show @Finset.univ ι (Fintype.ofFinite ι) =
          @Finset.univ ι hι by ext; simp, huniv]
        simp [hei0, hej, hij, f1, f2]
      have hf1Irr : Section1.IsIrreducibleCharacterOnGroup f1 := hpsiIrr i0
      have hf2Irr : Section1.IsIrreducibleCharacterOnGroup f2 := hpsiIrr j
      have hf12 : f1 ≠ f2 := hpair hij
      have hf1Ne : f1 ≠ Section1.principalCharacter G := by
        intro hf1
        have hf2Ne : f2 ≠ Section1.principalCharacter G := by
          intro hf2
          exact hf12 (hf1.trans hf2.symm)
        have hsp1 :
            Section1.scalarProduct G f1
              (Section1.principalCharacter G) = 1 := by
          rw [← hf1]
          exact Section1.scalarProduct_irreducibleCharacter_self hf1Irr
        have hsp2 :
            Section1.scalarProduct G f2
              (Section1.principalCharacter G) = 0 :=
          Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
            hf2Irr hf2Ne
        have hzero := hphiPrincipal
        rw [hdecompPair, Section1.scalarProduct_add_left, hsp1, hsp2] at hzero
        norm_num at hzero
      have hf2Ne : f2 ≠ Section1.principalCharacter G := by
        intro hf2
        have hsp1 :
            Section1.scalarProduct G f1
              (Section1.principalCharacter G) = 0 :=
          Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
            hf1Irr hf1Ne
        have hsp2 :
            Section1.scalarProduct G f2
              (Section1.principalCharacter G) = 1 := by
          rw [← hf2]
          exact Section1.scalarProduct_irreducibleCharacter_self hf2Irr
        have hzero := hphiPrincipal
        rw [hdecompPair, Section1.scalarProduct_add_left, hsp1, hsp2] at hzero
        norm_num at hzero
      obtain ⟨n1, hn1, _hn1dvd⟩ :=
        Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter
          f1 (hpsiBook i0)
      obtain ⟨n2, hn2, _hn2dvd⟩ :=
        Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter
          f2 (hpsiBook j)
      have hdegreePhi : Section1.degree phi = (Nat.card Q + 1 : ℕ) := by
        dsimp [phi]
        rw [Section1.degree_inducedClassFunction, hlambdaDegree, hindex]
        simp
      have hdegreeSum : n1 + n2 = Nat.card Q + 1 := by
        exact_mod_cast
          (show (n1 + n2 : ℂ) = (Nat.card Q + 1 : ℕ) by
            calc
              (n1 + n2 : ℂ) =
                  Section1.degree f1 + Section1.degree f2 := by
                rw [hn1, hn2]
              _ = Section1.degree (f1 + f2) := rfl
              _ = Section1.degree phi := by rw [hdecompPair]
              _ = (Nat.card Q + 1 : ℕ) := hdegreePhi)
      exact ⟨f1, f2, n1, n2, hf1Irr, hf2Irr, hf12, hf1Ne, hf2Ne,
        hdecompPair, hn1, hn2, hdegreeSum⟩
    obtain ⟨f1, f2, n1, n2, hf1Irr, hf2Irr, hf12, hf1Ne, hf2Ne,
      hinduced, hf1Degree, hf2Degree, hdegreeSum⟩ := hinduced_pair
    have hpair_avoids_extension :
        avoidsExtension f1 ∧ avoidsExtension f2 := by
      have hcoherent_pair_data :
          ∀ chi : Section1.ClassFunction d.H, chi ∈ chars →
            Section1.conjugateCharacter chi ∈ chars ∧
              Section1.conjugateCharacter chi ≠ chi ∧
                Section3.IsSignedIrreducibleCharacter (T' chi) ∧
                  Section3.IsSignedIrreducibleCharacter
                    (T' (Section1.conjugateCharacter chi)) ∧
                    Section1.scalarProduct G (T' chi)
                      (T' (Section1.conjugateCharacter chi)) = 0 ∧
                      Section1.degree (T' chi) =
                        Section1.degree
                          (T' (Section1.conjugateCharacter chi)) := by
        intro chi hchi
        have hchiData := (hchars chi).mp hchi
        have hchiIrr := hchiData.1
        have hchiChar :=
          Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchiIrr
        have hbarMem : Section1.conjugateCharacter chi ∈ chars := by
          letI : d.Q.Normal := d.Q_normal
          rcases (lemma_2_a d chars hchars chi).mp hchi with
            ⟨phi, hphiIrr, hphiNotKernel, hind⟩
          apply (lemma_2_a d chars hchars
            (Section1.conjugateCharacter chi)).mpr
          refine ⟨Section1.conjugateCharacter phi,
            Section1.isIrreducibleCharacterOnGroup_conjugateCharacter
              hphiIrr, ?_, ?_⟩
          · intro hbarKernelQ1
            apply hphiNotKernel
            have hdouble :=
              Section6.subgroupInKernel'_conjugateCharacter
                (Section1.conjugateCharacter phi) hbarKernelQ1
            have hcc :
                Section1.conjugateCharacter
                    (Section1.conjugateCharacter phi) = phi := by
              ext q
              simp [Section1.conjugateCharacter]
            simpa [hcc] using hdouble
          · calc
              Section1.inducedCF d.Q
                    (Section1.conjugateCharacter phi) =
                  Section1.conjugateCharacter
                    (Section1.inducedCF d.Q phi) :=
                (Section1.conjugateCharacter_inducedCF d.Q phi).symm
              _ = Section1.conjugateCharacter chi := by rw [hind]
        have hbarNe : Section1.conjugateCharacter chi ≠ chi :=
          lemma_2_c d chars hchars hdDodd chi hchi
        have hbarIrr :=
          ((hchars (Section1.conjugateCharacter chi)).mp hbarMem).1
        have hsigned (theta : Section1.ClassFunction d.H)
            (htheta : theta ∈ chars)
            (hthetaIrr :
              Section1.IsIrreducibleCharacterOnGroup theta) :
            Section3.IsSignedIrreducibleCharacter (T' theta) := by
          apply Section5.signed_irreducible_of_virtual_norm_one_pf59
          · exact hTvirtual theta
              (Section5.integerSpan_of_mem chars htheta)
          · rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
                hTiso htheta htheta,
              Section1.scalarProduct_irreducibleCharacter_self hthetaIrr]
        have hchiSigned := hsigned chi hchi hchiIrr
        have hbarSigned :=
          hsigned (Section1.conjugateCharacter chi) hbarMem hbarIrr
        have horth :
            Section1.scalarProduct G (T' chi)
                (T' (Section1.conjugateCharacter chi)) = 0 := by
          rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
            hTiso hchi hbarMem]
          exact
            Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
              hchiIrr hbarIrr hbarNe.symm
        have hdiffOn :
            Section5.integerSpanOn chars Section5.puncturedSet
              (chi - Section1.conjugateCharacter chi) := by
          refine ⟨Section5.integerSpan_sub
            (Section5.integerSpan_of_mem chars hchi)
            (Section5.integerSpan_of_mem chars hbarMem), ?_⟩
          apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
          change Section1.degree chi -
            Section1.degree (Section1.conjugateCharacter chi) = 0
          rw [Section5.degree_conjugateCharacter_eq_of_isCharacter hchiChar]
          simp
        have hagree :=
          hTagree (chi - Section1.conjugateCharacter chi) hdiffOn
        have hsourceDegree :
            Section1.degree
                (Section1.inducedCF d.H
                  (chi - Section1.conjugateCharacter chi)) = 0 := by
          rw [Section1.degree_inducedClassFunction]
          have hdiffDegree :
              Section1.degree
                  (chi - Section1.conjugateCharacter chi) = 0 :=
            (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).mp
              hdiffOn.2
          rw [hdiffDegree]
          ring
        have htargetDegree :
            Section1.degree
                (T' chi - T' (Section1.conjugateCharacter chi)) = 0 := by
          calc
            Section1.degree
                  (T' chi - T' (Section1.conjugateCharacter chi)) =
                Section1.degree
                  (T' (chi - Section1.conjugateCharacter chi)) := by
              rw [map_sub]
            _ = Section1.degree
                (Section1.inducedCF d.H
                  (chi - Section1.conjugateCharacter chi)) :=
              congrArg Section1.degree hagree
            _ = 0 := hsourceDegree
        have hdegEq :
            Section1.degree (T' chi) =
              Section1.degree
                (T' (Section1.conjugateCharacter chi)) :=
          sub_eq_zero.mp htargetDegree
        exact ⟨hbarMem, hbarNe, hchiSigned, hbarSigned, horth,
          hdegEq⟩
      have hsource_pair_scalar_zero :
          ∀ chi : Section1.ClassFunction d.H, chi ∈ chars →
            Section1.scalarProduct G
              (Section1.inducedCF d.H lambda)
              (T' chi - T' (Section1.conjugateCharacter chi)) = 0 := by
        classical
        have hTI :
            ∀ g : G,
              ((fun x : G => g * x * g⁻¹) ''
                  (d.QInG : Set G) = d.QInG) ∨
                (((fun x : G => g * x * g⁻¹) ''
                    (d.QInG : Set G)) ∩ d.QInG ⊆
                  ({1} : Set G)) := by
          intro g
          by_cases hgH : g ∈ d.H
          · left
            ext y
            constructor
            · rintro ⟨x, hx, rfl⟩
              rcases hx with ⟨q, hq, rfl⟩
              let gh : d.H := ⟨g, hgH⟩
              refine ⟨gh * q * gh⁻¹,
                d.Q_normal.conj_mem q hq gh, ?_⟩
              rfl
            · intro hy
              rcases hy with ⟨q, hq, rfl⟩
              let gh : d.H := ⟨g, hgH⟩
              let q' : d.Q :=
                ⟨gh⁻¹ * q * gh, by
                  simpa using d.Q_normal.conj_mem q hq gh⁻¹⟩
              refine ⟨d.H.subtype q',
                ⟨q', q'.property, rfl⟩, ?_⟩
              dsimp [q', gh]
              group
          · right
            intro y hy
            rcases hy with ⟨⟨x, hx, rfl⟩, hyQ⟩
            have hgInv : g⁻¹ ∉ d.H := by
              intro hgInv
              exact hgH (by simpa using d.H.inv_mem hgInv)
            have hdis := d.Q_TI_in_G g⁻¹ hgInv
            have hyConj :
                g * x * g⁻¹ ∈
                  PFchapter1section1.rightConjugate d.QInG g⁻¹ := by
              change g * x * g⁻¹ ∈ d.QInG.conjBy (g⁻¹)⁻¹
              exact Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
            have hyBot : g * x * g⁻¹ ∈ (⊥ : Subgroup G) :=
              hdis.le_bot ⟨hyQ, hyConj⟩
            simpa using hyBot
        have hnorm :
            Subgroup.normalizer (d.QInG : Set G) = d.H := by
          have hQ1ne : d.Q1 ≠ ⊥ := by
            intro hQ1bot
            apply d.Q1_not_two_group
            exact hQ1bot.symm ▸ IsPGroup.of_bot (p := 2) (G := d.H)
          have hQne : d.Q ≠ ⊥ := by
            intro hQbot
            apply hQ1ne
            apply le_bot_iff.mp
            simpa [hQbot] using d.Q1_le_Q
          have hQInGne : d.QInG ≠ ⊥ :=
            (Subgroup.map_eq_bot_iff_of_injective
              (H := d.Q) (f := d.H.subtype)
              d.H.subtype_injective).not.mpr hQne
          apply le_antisymm
          · intro g hgNorm
            by_contra hgH
            have hgInv : g⁻¹ ∉ d.H := by
              intro hgInv
              exact hgH (by simpa using d.H.inv_mem hgInv)
            have hdis := d.Q_TI_in_G g⁻¹ hgInv
            have hnotle : ¬ d.QInG ≤ (⊥ : Subgroup G) := by
              intro hle
              exact hQInGne (le_bot_iff.mp hle)
            rcases SetLike.not_le_iff_exists.mp hnotle with
              ⟨q, hqQ, hqBot⟩
            have hqNe : q ≠ 1 := by simpa using hqBot
            have hconjQ : g * q * g⁻¹ ∈ d.QInG :=
              (Subgroup.mem_normalizer_iff.mp hgNorm q).1 hqQ
            have hconjRight :
                g * q * g⁻¹ ∈
                  PFchapter1section1.rightConjugate d.QInG g⁻¹ := by
              change g * q * g⁻¹ ∈ d.QInG.conjBy (g⁻¹)⁻¹
              exact Subgroup.mem_map.mpr ⟨q, hqQ, by simp⟩
            have hconjBot : g * q * g⁻¹ ∈ (⊥ : Subgroup G) :=
              hdis.le_bot ⟨hconjQ, hconjRight⟩
            have hconjOne : g * q * g⁻¹ = 1 := by
              simpa using hconjBot
            apply hqNe
            calc
              q = g⁻¹ * (g * q * g⁻¹) * g := by group
              _ = 1 := by rw [hconjOne]; simp
          · intro g hgH
            rw [Subgroup.mem_normalizer_iff]
            intro x
            constructor
            · intro hx
              rcases hx with ⟨q, hq, rfl⟩
              let gh : d.H := ⟨g, hgH⟩
              exact ⟨gh * q * gh⁻¹,
                d.Q_normal.conj_mem q hq gh, rfl⟩
            · intro hx
              rcases hx with ⟨q, hq, hqx⟩
              let gh : d.H := ⟨g, hgH⟩
              have hback : gh⁻¹ * q * gh ∈ d.Q := by
                simpa using d.Q_normal.conj_mem q hq gh⁻¹
              refine Subgroup.mem_map.mpr
                ⟨(gh⁻¹ * (q : d.H) * gh : d.H), hback, ?_⟩
              change g⁻¹ * (q : G) * g = x
              have h := congrArg (fun z : G => g⁻¹ * z * g) hqx
              simpa [mul_assoc] using h
        have hmemQInG (x : d.H) :
            (x : G) ∈ d.QInG ↔ x ∈ d.Q := by
          constructor
          · rintro ⟨q, hq, hqx⟩
            have hqxeq : q = x := d.H.subtype_injective hqx
            simpa [hqxeq] using hq
          · intro hx
            exact ⟨x, hx, rfl⟩
        have hpointOfIsaacs :
            ∀ {X : Set G} {L : Subgroup G},
              Subgroup.normalizer X = L →
                (∀ g : G,
                  ((fun x : G => g * x * g⁻¹) '' X = X) ∨
                    (((fun x : G => g * x * g⁻¹) '' X) ∩ X ⊆
                      ({1} : Set G))) →
                  ∀ {theta : Section1.ClassFunction L},
                    Section1.IsClassFunction theta →
                      (∀ n : L, (n : G) ∉ X → theta n = 0) →
                        theta 1 = 0 →
                          ∀ x : G, x ∈ X →
                            ∃ hxL : x ∈ L,
                              Section1.inducedCF L theta x =
                                theta ⟨x, hxL⟩ := by
          intro X L hnorm' hTI' theta hthetaClass hthetaVanish
            hthetaOne
          subst L
          exact
            (External.Isaacs.VII.isaacs_lemma_7_7 hTI'
              hthetaClass hthetaClass hthetaVanish hthetaVanish
              hthetaOne).1
        letI : d.Q.Normal := d.Q_normal
        have hQComplement : d.Q.IsComplement' d.D :=
          isComplement'_of_disjoint_sup_eq_top_of_normal
            d.Q d.D d.Q_disjoint_D d.H_eq_Q_sup_D
        have hQindex : d.Q.index = Nat.card d.D :=
          hQComplement.symm.index_eq_card
        have hconjugateIntoQ :
            ∀ x : d.H,
              (x : G) ∈ Section2.conjugateSet (d.QInG : Set G) →
                x ∈ d.Q := by
          intro x hx
          rcases hx with ⟨q, hqQ, g, hg⟩
          rcases hqQ with ⟨qQ, hqQ, hqEq⟩
          change g * q * g⁻¹ = (x : G) at hg
          have hsemiconj : SemiconjBy g q (x : G) := by
            change g * q = (x : G) * g
            calc
              g * q = (g * q * g⁻¹) * g := by group
              _ = (x : G) * g := by rw [hg]
          have horderConj : orderOf q = orderOf (x : G) :=
            SemiconjBy.orderOf_eq g hsemiconj
          let qSub : d.Q := ⟨qQ, hqQ⟩
          have hqSubEq : (qSub : G) = q := hqEq
          have hxOrder : orderOf x = orderOf qSub := by
            calc
              orderOf x = orderOf (x : G) := by simp
              _ = orderOf q := horderConj.symm
              _ = orderOf (qSub : G) := by rw [hqSubEq]
              _ = orderOf qSub := by simp
          have hxOrderDvdQ : orderOf x ∣ Nat.card d.Q := by
            rw [hxOrder]
            exact orderOf_dvd_natCard qSub
          let pi : d.H →* d.H ⧸ d.Q := QuotientGroup.mk' d.Q
          have hpiDvdQ : orderOf (pi x) ∣ Nat.card d.Q :=
            (orderOf_map_dvd pi x).trans hxOrderDvdQ
          have hquotCard : Nat.card (d.H ⧸ d.Q) = Nat.card d.D := by
            simpa [Subgroup.index] using hQindex
          have hpiDvdD : orderOf (pi x) ∣ Nat.card d.D := by
            simpa [hquotCard] using orderOf_dvd_natCard (pi x)
          have hpiOrder : orderOf (pi x) = 1 :=
            Nat.eq_one_of_dvd_coprimes d.card_Q_coprime_card_D
              hpiDvdQ hpiDvdD
          have hpione : pi x = 1 := orderOf_eq_one_iff.mp hpiOrder
          exact (QuotientGroup.eq_one_iff x).mp hpione
        intro chi hchi
        have hchiData := (hchars chi).mp hchi
        have hchiIrr := hchiData.1
        have hchiClass :=
          Section1.isCharacter_isClassFunction chi
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
              hchiIrr)
        have hbarMem := (hcoherent_pair_data chi hchi).1
        have hbarData :=
          (hchars (Section1.conjugateCharacter chi)).mp hbarMem
        have hbarIrr := hbarData.1
        have hbarClass :=
          Section1.isCharacter_isClassFunction
            (Section1.conjugateCharacter chi)
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
              hbarIrr)
        let theta := chi - Section1.conjugateCharacter chi
        have hthetaClass : Section1.IsClassFunction theta := by
          intro x g
          simp [theta, hchiClass x g, hbarClass x g]
        have hcharVanish :
            ∀ psi : Section1.ClassFunction d.H, psi ∈ chars →
              ∀ x : d.H, x ∉ d.Q → psi x = 0 := by
          intro psi hpsi x hx
          rcases (lemma_2_a d chars hchars psi).mp hpsi with
            ⟨phi, _hphi, _hnotker, hind⟩
          rw [← hind]
          simpa [Section1.inducedCF] using
            Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
              d.Q phi hx
        have hthetaVanish :
            ∀ x : d.H, x ∉ d.Q → theta x = 0 := by
          intro x hx
          simp [theta, hcharVanish chi hchi x hx,
            hcharVanish (Section1.conjugateCharacter chi) hbarMem x hx]
        have hthetaOne : theta 1 = 0 := by
          change Section1.degree chi -
            Section1.degree (Section1.conjugateCharacter chi) = 0
          rw [Section5.degree_conjugateCharacter_eq_of_isCharacter
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
              hchiIrr)]
          simp
        have hthetaCFOn :
            Section2.CFOn d.H (d.QInG : Set G) theta := by
          refine ⟨hthetaClass, ?_⟩
          intro x hx
          apply hthetaVanish x
          intro hxQ
          exact hx ((hmemQInG x).2 hxQ)
        have hrestriction :
            Section1.subgroupRestriction d.H
                (Section1.inducedCF d.H theta) = theta := by
          ext x
          by_cases hxQ : x ∈ d.Q
          · have hxX : (x : G) ∈ d.QInG := (hmemQInG x).2 hxQ
            rcases hpointOfIsaacs hnorm hTI hthetaClass hthetaCFOn.2
                hthetaOne (x : G) hxX with
              ⟨hxH, hpoint⟩
            have hxEq : (⟨(x : G), hxH⟩ : d.H) = x :=
              Subtype.ext rfl
            simpa [Section1.subgroupRestriction, hxEq] using hpoint
          · have hxNotConj :
                (x : G) ∉
                  Section2.conjugateSet (d.QInG : Set G) := by
              intro hx
              exact hxQ (hconjugateIntoQ x hx)
            have hindZero :
                Section1.inducedCF d.H theta (x : G) = 0 :=
              Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn
                d.H theta hthetaCFOn hxNotConj
            rw [hthetaVanish x hxQ]
            simpa [Section1.subgroupRestriction] using hindZero
        have hdiffOn :
            Section5.integerSpanOn chars Section5.puncturedSet theta := by
          refine ⟨Section5.integerSpan_sub
            (Section5.integerSpan_of_mem chars hchi)
            (Section5.integerSpan_of_mem chars hbarMem), ?_⟩
          exact
            (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
              hthetaOne
        have hagree := hTagree theta hdiffOn
        have hlambdaChi : lambda ≠ chi := by
          intro heq
          apply hchiData.2
          rw [← heq]
          exact hlambdaQ1Kernel
        have hlambdaBar :
            lambda ≠ Section1.conjugateCharacter chi := by
          intro heq
          apply hbarData.2
          rw [← heq]
          exact hlambdaQ1Kernel
        have hspChi :
            Section1.scalarProduct d.H lambda chi = 0 :=
          Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
            hlambdaIrr hchiIrr hlambdaChi
        have hspBar :
            Section1.scalarProduct d.H lambda
              (Section1.conjugateCharacter chi) = 0 :=
          Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
            hlambdaIrr hbarIrr hlambdaBar
        calc
          Section1.scalarProduct G (Section1.inducedCF d.H lambda)
                (T' chi - T' (Section1.conjugateCharacter chi)) =
              Section1.scalarProduct G
                (Section1.inducedCF d.H lambda) (T' theta) := by
            rw [map_sub]
          _ = Section1.scalarProduct G
                (Section1.inducedCF d.H lambda)
                (Section1.inducedCF d.H theta) := by
            rw [hagree]
            rfl
          _ = Section1.scalarProduct d.H lambda
                (Section1.subgroupRestriction d.H
                  (Section1.inducedCF d.H theta)) :=
            Section1.scalarProduct_inducedCF_left d.H lambda
              (Section1.inducedCF d.H theta)
              (Section1.inducedCF_isClassFunction d.H theta)
          _ = Section1.scalarProduct d.H lambda theta := by
            rw [hrestriction]
          _ = 0 := by
            rw [Section5.scalarProduct_sub_right, hspChi, hspBar,
              sub_zero]
      have hpair_algebra :
          ∀ (fa fb eps epsbar : Section1.ClassFunction G)
            (na nb total : ℕ),
            Section1.IsIrreducibleCharacterOnGroup fa →
              Section1.IsIrreducibleCharacterOnGroup fb →
                fa ≠ fb →
                  Section3.IsSignedIrreducibleCharacter eps →
                    Section3.IsSignedIrreducibleCharacter epsbar →
                      Section1.scalarProduct G eps epsbar = 0 →
                        Section1.scalarProduct G (fa + fb)
                            (eps - epsbar) = 0 →
                          Section1.degree eps =
                              Section1.degree epsbar →
                            Section1.degree fa = (na : ℂ) →
                              Section1.degree fb = (nb : ℂ) →
                                na + nb = total → Odd total →
                                  fa ≠ eps ∧ fa ≠ -eps := by
        intro fa fb eps epsbar na nb total hfaIrr hfbIrr hfab
          heps hepsbar horth hzero hdegEq hfaDegree hfbDegree hsum
          htotalOdd
        have hfaSelf : Section1.scalarProduct G fa fa = 1 :=
          Section1.scalarProduct_irreducibleCharacter_self hfaIrr
        have hfbSelf : Section1.scalarProduct G fb fb = 1 :=
          Section1.scalarProduct_irreducibleCharacter_self hfbIrr
        have hfbfa : Section1.scalarProduct G fb fa = 0 :=
          Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
            hfbIrr hfaIrr hfab.symm
        have hnegLeft (a b : Section1.ClassFunction G) :
            Section1.scalarProduct G (-a) b =
              -Section1.scalarProduct G a b := by
          rw [show -a = (-1 : ℂ) • a by ext; simp]
          rw [Section1.scalarProduct_smul_left]
          simp
        have hnegRight (a b : Section1.ClassFunction G) :
            Section1.scalarProduct G a (-b) =
              -Section1.scalarProduct G a b := by
          rw [show -b = (-1 : ℂ) • b by ext; simp]
          rw [Section1.scalarProduct_smul_right]
          simp
        constructor
        · intro hfaeps
          have hfaepsbar : Section1.scalarProduct G fa epsbar = 0 := by
            rw [hfaeps]
            exact horth
          have hfbeps : Section1.scalarProduct G fb eps = 0 := by
            rw [← hfaeps]
            exact hfbfa
          have hfbbar : Section1.scalarProduct G fb epsbar = 1 := by
            rw [Section1.scalarProduct_add_left,
              Section5.scalarProduct_sub_right,
              Section5.scalarProduct_sub_right, ← hfaeps,
              hfaSelf, hfaepsbar, hfbfa] at hzero
            linear_combination -hzero
          have hrevNe :
              Section1.scalarProduct G epsbar fb ≠ 0 :=
            (Section1.scalarProduct_ne_zero_swap epsbar fb).mpr (by
              rw [hfbbar]
              norm_num)
          rcases
              (Section12.scalarProduct_signed_irreducible_ne_zero_iff
                hepsbar hfbIrr).mp hrevNe with
            ⟨delta, hdelta, hepsbarEq⟩
          have hdeltaOne : delta = 1 := by
            rw [hepsbarEq, Section1.scalarProduct_smul_right,
              hfbSelf] at hfbbar
            rcases hdelta with rfl | rfl
            · rfl
            · norm_num at hfbbar
          have hepsbarfb : epsbar = fb := by
            simpa [hdeltaOne] using hepsbarEq
          have hnab : na = nb := by
            have hdegree : Section1.degree fa = Section1.degree fb := by
              calc
                Section1.degree fa = Section1.degree eps :=
                  congrArg Section1.degree hfaeps
                _ = Section1.degree epsbar := hdegEq
                _ = Section1.degree fb :=
                  congrArg Section1.degree hepsbarfb
            exact_mod_cast (show (na : ℂ) = (nb : ℂ) by
              rw [← hfaDegree, ← hfbDegree]
              exact hdegree)
          have htotalEven : Even total := by
            rw [← hsum, hnab]
            exact ⟨nb, rfl⟩
          exact (Nat.not_even_iff_odd.mpr htotalOdd) htotalEven
        · intro hfaNeg
          have hepsfa : eps = -fa := by
            rw [hfaNeg]
            simp
          have hfaepsbar : Section1.scalarProduct G fa epsbar = 0 := by
            have h := horth
            rw [hepsfa, hnegLeft] at h
            simpa using h
          have hfbeps : Section1.scalarProduct G fb eps = 0 := by
            rw [hepsfa, hnegRight, hfbfa]
            simp
          have hfaeps : Section1.scalarProduct G fa eps = -1 := by
            rw [hepsfa, hnegRight, hfaSelf]
          have hfbbar : Section1.scalarProduct G fb epsbar = -1 := by
            rw [Section1.scalarProduct_add_left,
              Section5.scalarProduct_sub_right,
              Section5.scalarProduct_sub_right, hfaeps, hfaepsbar,
              hfbeps] at hzero
            linear_combination -hzero
          have hrevNe :
              Section1.scalarProduct G epsbar fb ≠ 0 :=
            (Section1.scalarProduct_ne_zero_swap epsbar fb).mpr (by
              rw [hfbbar]
              norm_num)
          rcases
              (Section12.scalarProduct_signed_irreducible_ne_zero_iff
                hepsbar hfbIrr).mp hrevNe with
            ⟨delta, hdelta, hepsbarEq⟩
          have hdeltaNeg : delta = -1 := by
            rw [hepsbarEq, Section1.scalarProduct_smul_right,
              hfbSelf] at hfbbar
            rcases hdelta with rfl | rfl
            · norm_num at hfbbar
            · rfl
          have hepsbarfb : epsbar = -fb := by
            simpa [hdeltaNeg] using hepsbarEq
          have hnab : na = nb := by
            rw [hepsfa, hepsbarfb] at hdegEq
            change -Section1.degree fa = -Section1.degree fb at hdegEq
            have hdegree :
                Section1.degree fa = Section1.degree fb :=
              neg_injective hdegEq
            exact_mod_cast (show (na : ℂ) = (nb : ℂ) by
              simpa [hfaDegree, hfbDegree] using hdegree)
          have htotalEven : Even total := by
            rw [← hsum, hnab]
            exact ⟨nb, rfl⟩
          exact (Nat.not_even_iff_odd.mpr htotalOdd) htotalEven
      have htotalOdd : Odd (Nat.card Q + 1) :=
        hch.1.section2.hA.A1.Q_even.add_one
      constructor
      · intro chi hchi
        rcases hcoherent_pair_data chi hchi with
          ⟨_hbarMem, _hbarNe, hchiSigned, hbarSigned, horth,
            hdegEq⟩
        have hzero :
            Section1.scalarProduct G (f1 + f2)
                (T' chi - T' (Section1.conjugateCharacter chi)) = 0 := by
          rw [← hinduced]
          exact hsource_pair_scalar_zero chi hchi
        exact hpair_algebra f1 f2 (T' chi)
          (T' (Section1.conjugateCharacter chi)) n1 n2
          (Nat.card Q + 1) hf1Irr hf2Irr hf12 hchiSigned hbarSigned
          horth hzero hdegEq hf1Degree hf2Degree hdegreeSum htotalOdd
      · intro chi hchi
        rcases hcoherent_pair_data chi hchi with
          ⟨_hbarMem, _hbarNe, hchiSigned, hbarSigned, horth,
            hdegEq⟩
        have hzero :
            Section1.scalarProduct G (f2 + f1)
                (T' chi - T' (Section1.conjugateCharacter chi)) = 0 := by
          rw [add_comm, ← hinduced]
          exact hsource_pair_scalar_zero chi hchi
        exact hpair_algebra f2 f1 (T' chi)
          (T' (Section1.conjugateCharacter chi)) n2 n1
          (Nat.card Q + 1) hf2Irr hf1Irr hf12.symm hchiSigned
          hbarSigned horth hzero hdegEq hf2Degree hf1Degree
          (by simpa [Nat.add_comm] using hdegreeSum) htotalOdd
    have hrestriction_multiplicity :
        ∀ (f : Section1.ClassFunction G) (n : ℕ),
          Section1.IsIrreducibleCharacterOnGroup f →
            f ≠ Section1.principalCharacter G →
              Section1.degree f = (n : ℂ) →
                avoidsExtension f →
                  ∃ b : ℕ,
                    b * Nat.card S * (Nat.card Q1 - 1) ≤ n ∧
                      (b = 0 →
                        Section1.subgroupInKernel'
                          (Section1.subgroupRestriction d.H f) d.Q1) := by
      intro f n hfIrr _hfNe hfDegree hfAvoids
      let res : Section1.ClassFunction d.H :=
        Section1.subgroupRestriction d.H f
      have hresCharacter : Section1.IsCharacter res := by
        rcases Section1.isCharacter_of_isIrreducibleCharacterOnGroup
            hfIrr with
          ⟨Vf, _hadd, _hmodule, _hfd, rho, hrho⟩
        refine ⟨Vf, inferInstance, inferInstance, inferInstance,
          rho.comp d.H.subtype, ?_⟩
        ext x
        change f (x : G) = rho.character (x : G)
        exact congrFun hrho (x : G)
      have hexceptionalDegreePackage :
          ∃ chi0 : chars, ∃ a : chars → ℕ,
            a chi0 = 1 ∧
              (∀ chi : chars,
                Section1.degree (chi : Section1.ClassFunction d.H) =
                  (a chi * Nat.card d.D : ℕ)) ∧
                (∑ chi : chars,
                    a chi * (a chi * Nat.card d.D)) =
                  Nat.card d.S * (Nat.card d.Q1 - 1) := by
        classical
        letI : d.Q.Normal := d.Q_normal
        letI : d.Q1.Normal := d.Q1_normal
        have hprod : Section2.IsInternalDirectProduct d.Q d.S d.Q1 := by
          refine
            { left_le := d.S_le_Q
              right_le := d.Q1_le_Q
              commute := by
                intro s hs q hq
                exact d.S_commutes_Q1 s q hs hq
              inf_eq_bot := d.S_disjoint_Q1.eq_bot
              mul_surjective := ?_ }
          intro q hq
          have hqSup : q ∈ d.S ⊔ d.Q1 := by
            rw [d.Q_eq_S_sup_Q1]
            exact hq
          rcases Subgroup.mem_sup_of_normal_right.mp hqSup with
            ⟨s, hs, q1, hq1, hprod⟩
          exact ⟨s, hs, q1, hq1, hprod.symm⟩
        have hQComplement : d.Q.IsComplement' d.D :=
          isComplement'_of_disjoint_sup_eq_top_of_normal
            d.Q d.D d.Q_disjoint_D d.H_eq_Q_sup_D
        have hQindex : d.Q.index = Nat.card d.D :=
          hQComplement.symm.index_eq_card
        have hQ1ne : d.Q1 ≠ ⊥ := by
          intro hQ1bot
          apply d.Q1_not_two_group
          exact hQ1bot.symm ▸ IsPGroup.of_bot (p := 2) (G := d.H)
        letI : Nontrivial d.Q1 :=
          (Subgroup.nontrivial_iff_ne_bot d.Q1).2 hQ1ne
        have hQ1solv : Group.IsSolvable d.Q1 :=
          _root_.CFSG.odd_order_theorem d.Q1 d.Q1_odd
        letI : Group.IsSolvable d.Q1 := hQ1solv
        obtain ⟨eta0, heta0⟩ :=
          Section6.exists_nontrivial_linear_character_of_solvable d.Q1
        let phi0 : Section1.ClassFunction d.Q :=
          Section3.linearCharacterProductOverInternalDirectProduct
            hprod 1 eta0
        have hphi0Irr :
            Section1.IsIrreducibleCharacterOnGroup phi0 :=
          Section3.linearCharacterProductOverInternalDirectProduct_irreducible
            hprod 1 eta0
        have hphi0NotKernel :
            ¬ Section1.subgroupInKernel' phi0
              (d.Q1.subgroupOf d.Q) := by
          intro hker
          exact heta0
            ((Section3.linearCharacterProductOverInternalDirectProduct_leftKernel_iff
              hprod 1 eta0).mp hker)
        let chi0cf : Section1.ClassFunction d.H :=
          Section1.inducedCF d.Q phi0
        have hchi0Mem : chi0cf ∈ chars :=
          (lemma_2_a d chars hchars chi0cf).mpr
            ⟨phi0, hphi0Irr, hphi0NotKernel, rfl⟩
        let chi0 : chars := ⟨chi0cf, hchi0Mem⟩
        have hchi0Degree :
            Section1.degree
                (chi0 : Section1.ClassFunction d.H) =
              (Nat.card d.D : ℕ) := by
          change Section1.degree (Section1.inducedCF d.Q phi0) =
            (Nat.card d.D : ℕ)
          rw [Section1.degree_inducedClassFunction]
          rw [Section3.linearCharacterProductOverInternalDirectProduct_degree]
          simp [hQindex]
        have hfactor :
            ∀ chi : chars, ∃ m : ℕ, 0 < m ∧
              Section1.degree
                  (chi : Section1.ClassFunction d.H) =
                (m * Nat.card d.D : ℕ) := by
          intro chi
          rcases (lemma_2_a d chars hchars
              (chi : Section1.ClassFunction d.H)).mp chi.property with
            ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
          obtain ⟨m, hmDegree, _hmDvd⟩ :=
            Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter
              phi
              (Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
                hphiIrr)
          have hmPos : 0 < m := by
            by_contra hm
            have hm0 : m = 0 := by omega
            have hdeg0 : Section1.degree phi = 0 := by
              simpa [hm0] using hmDegree
            exact
              (Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup
                phi hphiIrr) hdeg0
          refine ⟨m, hmPos, ?_⟩
          rw [← hind, Section1.degree_inducedClassFunction, hmDegree]
          simp [hQindex, Nat.cast_mul]
          ring
        let a : chars → ℕ := fun chi =>
          Classical.choose (hfactor chi)
        have hdegreeA (chi : chars) :
            Section1.degree (chi : Section1.ClassFunction d.H) =
              (a chi * Nat.card d.D : ℕ) :=
          (Classical.choose_spec (hfactor chi)).2
        have ha0 : a chi0 = 1 := by
          have hnat :
              a chi0 * Nat.card d.D = Nat.card d.D := by
            exact_mod_cast (hdegreeA chi0).symm.trans hchi0Degree
          apply Nat.mul_right_cancel (Nat.card_pos (α := d.D))
          simpa using hnat
        obtain ⟨Xset, hXset, degX, hdegX, hsumX⟩ :=
          Section6.theorem_6_6_complete_nonkernel_degree_data
            (L := d.H) (Z := d.Q1)
        have hXeq : Xset = chars := by
          ext chi
          rw [hXset chi, hchars chi]
        subst Xset
        have hdegXeq : ∀ chi : chars,
            degX chi = a chi * Nat.card d.D := by
          intro chi
          exact_mod_cast (hdegX chi).symm.trans (hdegreeA chi)
        have hcardQ :
            Nat.card d.Q = Nat.card d.S * Nat.card d.Q1 := by
          let e : d.S × d.Q1 ≃* d.Q :=
            Section3.internalDirectProductMulEquiv hprod
          rw [← Nat.card_prod]
          exact (Nat.card_congr e.toEquiv).symm
        have hcardH :
            Nat.card d.H = Nat.card d.Q * Nat.card d.D :=
          hQComplement.card_mul.symm
        have hQ1index :
            d.Q1.index = Nat.card d.S * Nat.card d.D := by
          apply Nat.mul_left_cancel (Nat.card_pos (α := d.Q1))
          calc
            Nat.card d.Q1 * d.Q1.index = Nat.card d.H :=
              Subgroup.card_mul_index d.Q1
            _ = Nat.card d.Q * Nat.card d.D := hcardH
            _ = (Nat.card d.S * Nat.card d.Q1) *
                  Nat.card d.D := by rw [hcardQ]
            _ = Nat.card d.Q1 *
                  (Nat.card d.S * Nat.card d.D) := by ac_rfl
        have hquotCard :
            Nat.card (d.H ⧸ d.Q1) =
              Nat.card d.S * Nat.card d.D := by
          rw [← Subgroup.index_eq_card]
          exact hQ1index
        have hsquareSum :
            (∑ chi : chars, (a chi * Nat.card d.D) ^ 2) +
                Nat.card d.S * Nat.card d.D =
              Nat.card d.S * Nat.card d.Q1 * Nat.card d.D := by
          rw [hquotCard, hcardH, hcardQ] at hsumX
          simpa only [hdegXeq] using hsumX
        have hsquareFactor :
            (∑ chi : chars, (a chi * Nat.card d.D) ^ 2) =
              Nat.card d.D *
                ∑ chi : chars,
                  a chi * (a chi * Nat.card d.D) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro chi _hchi
          ring
        have hcardQ1Pos : 0 < Nat.card d.Q1 := Nat.card_pos
        have hcardQ1Split :
            Nat.card d.Q1 - 1 + 1 = Nat.card d.Q1 := by
          omega
        have htargetSum :
            Nat.card d.S * Nat.card d.Q1 * Nat.card d.D =
              Nat.card d.D *
                  (Nat.card d.S * (Nat.card d.Q1 - 1)) +
                Nat.card d.S * Nat.card d.D := by
          calc
            Nat.card d.S * Nat.card d.Q1 * Nat.card d.D =
                Nat.card d.S * (Nat.card d.Q1 - 1 + 1) *
                  Nat.card d.D := by rw [hcardQ1Split]
            _ = Nat.card d.D *
                  (Nat.card d.S * (Nat.card d.Q1 - 1)) +
                Nat.card d.S * Nat.card d.D := by ring
        have hmulEq :
            Nat.card d.D *
                (∑ chi : chars,
                  a chi * (a chi * Nat.card d.D)) =
              Nat.card d.D *
                (Nat.card d.S * (Nat.card d.Q1 - 1)) := by
          rw [hsquareFactor, htargetSum] at hsquareSum
          exact Nat.add_right_cancel hsquareSum
        have hsumA :
            (∑ chi : chars,
                a chi * (a chi * Nat.card d.D)) =
              Nat.card d.S * (Nat.card d.Q1 - 1) :=
          Nat.mul_left_cancel (Nat.card_pos (α := d.D)) hmulEq
        exact ⟨chi0, a, ha0, hdegreeA, hsumA⟩
      obtain ⟨chi0, a, ha0, hdegreeA, hdegreeSumA⟩ :=
        hexceptionalDegreePackage
      let mult : chars → ℕ := fun chi =>
        Classical.choose
          (Section1.scalarProduct_character_character_eq_nat
            res (chi : Section1.ClassFunction d.H) hresCharacter
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
              ((hchars (chi : Section1.ClassFunction d.H)).mp
                chi.property).1))
      have hmultEq :
          ∀ chi : chars,
            Section1.scalarProduct d.H res
                (chi : Section1.ClassFunction d.H) = (mult chi : ℂ) := by
        intro chi
        exact Classical.choose_spec
          (Section1.scalarProduct_character_character_eq_nat
            res (chi : Section1.ClassFunction d.H) hresCharacter
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
              ((hchars (chi : Section1.ClassFunction d.H)).mp
                chi.property).1))
      let b : ℕ := mult chi0
      have hmultRatio :
          ∀ chi : chars, mult chi = b * a chi := by
        classical
        have hfClass : Section1.IsClassFunction f :=
          Section1.isCharacter_isClassFunction f
            (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hfIrr)
        have himageOrth : ∀ chi : chars,
            Section1.scalarProduct G f
              (T' (chi : Section1.ClassFunction d.H)) = 0 := by
          intro chi
          by_contra hne
          have hswap :
              Section1.scalarProduct G
                (T' (chi : Section1.ClassFunction d.H)) f ≠ 0 :=
            (Section1.scalarProduct_ne_zero_swap
              (T' (chi : Section1.ClassFunction d.H)) f).mpr hne
          have hsigned :
              Section3.IsSignedIrreducibleCharacter
                (T' (chi : Section1.ClassFunction d.H)) := by
            apply Section5.signed_irreducible_of_virtual_norm_one_pf59
            · exact hTvirtual (chi : Section1.ClassFunction d.H)
                (Section5.integerSpan_of_mem chars chi.property)
            · rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
                    hTiso chi.property chi.property,
                  Section1.scalarProduct_irreducibleCharacter_self
                    ((hchars (chi : Section1.ClassFunction d.H)).mp
                      chi.property).1]
          rcases
              (Section12.scalarProduct_signed_irreducible_ne_zero_iff
                hsigned hfIrr).mp hswap with
            ⟨delta, hdelta, hEq⟩
          rcases hdelta with rfl | rfl
          · exact
              (hfAvoids (chi : Section1.ClassFunction d.H)
                chi.property).1 (by simpa using hEq.symm)
          · exact
              (hfAvoids (chi : Section1.ClassFunction d.H)
                chi.property).2 (by rw [hEq]; simp)
        intro chi
        let theta : Section1.ClassFunction d.H :=
          (chi : Section1.ClassFunction d.H) -
            (a chi : ℂ) • (chi0 : Section1.ClassFunction d.H)
        have hthetaOn :
            Section5.integerSpanOn chars Section5.puncturedSet theta := by
          refine ⟨Section5.integerSpan_sub
            (Section5.integerSpan_of_mem chars chi.property) ?_, ?_⟩
          · simpa using
              (Section5.integerSpan_zsmul (S := chars)
                (φ := (chi0 : Section1.ClassFunction d.H))
                (a chi : ℤ)
                (Section5.integerSpan_of_mem chars chi0.property))
          · apply
              (Section5.supportedOn_puncturedSet_iff_degree_eq_zero _).2
            change
              Section1.degree (chi : Section1.ClassFunction d.H) -
                (a chi : ℂ) *
                  Section1.degree
                    (chi0 : Section1.ClassFunction d.H) = 0
            rw [hdegreeA chi, hdegreeA chi0, ha0]
            push_cast
            ring
        have hagree := hTagree theta hthetaOn
        have htargetZero :
            Section1.scalarProduct G f (T' theta) = 0 := by
          simp [theta, map_sub, Section5.scalarProduct_sub_right,
            Section1.scalarProduct_smul_right, himageOrth]
        have hindZero :
            Section1.scalarProduct G f
              (Section1.inducedCF d.H theta) = 0 := by
          rw [← show T' theta = Section1.inducedCF d.H theta by
            simpa [Section1.inducedCFLinear] using hagree]
          exact htargetZero
        have hresZero :
            Section1.scalarProduct d.H res theta = 0 := by
          change Section1.scalarProduct d.H
            (Section1.subgroupRestriction d.H f) theta = 0
          calc
            Section1.scalarProduct d.H
                  (Section1.subgroupRestriction d.H f) theta =
                Section1.scalarProduct G f
                  (Section1.inducedCF d.H theta) :=
              (Section1.inducedClassFunction_frobenius_right
                d.H theta f hfClass).symm
            _ = 0 := hindZero
        have hrelC :
            (mult chi : ℂ) =
              (a chi : ℂ) * (mult chi0 : ℂ) := by
          have hz := hresZero
          change Section1.scalarProduct d.H res
              ((chi : Section1.ClassFunction d.H) -
                (a chi : ℂ) •
                  (chi0 : Section1.ClassFunction d.H)) = 0 at hz
          rw [Section5.scalarProduct_sub_right,
            Section1.scalarProduct_smul_right, hmultEq chi,
            hmultEq chi0] at hz
          simpa using sub_eq_zero.mp hz
        have hrelNat : mult chi = mult chi0 * a chi := by
          exact_mod_cast hrelC.trans (mul_comm _ _)
        simpa [b] using hrelNat
      rcases Section1.character_irreducible_decomposition_all
          res hresCharacter with
        ⟨ι, hι, hdec, e, psi, hpsiBook, hpair, hdecomp⟩
      letI : Fintype ι := hι
      letI : DecidableEq ι := hdec
      have hpsiIrr : ∀ i : ι,
          Section1.IsIrreducibleCharacterOnGroup (psi i) := by
        intro i
        exact
          Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
            (psi i) (hpsiBook i)
      have horth : ∀ i j : ι,
          Section1.scalarProduct d.H (psi i) (psi j) =
            if i = j then 1 else 0 := by
        intro i j
        by_cases hij : i = j
        · subst j
          simp [Section1.scalarProduct_irreducibleCharacter_self
            (hpsiIrr i)]
        · rw [if_neg hij]
          exact
            Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
              (hpsiIrr i) (hpsiIrr j) (hpair hij)
      have hmultPsi : ∀ i : ι,
          Section1.scalarProduct d.H res (psi i) = (e i : ℂ) := by
        intro i
        exact Section1.proposition_1_7_multiplicity_from_decomposition
          e psi res horth hdecomp i
      let degPsi : ι → ℕ := fun i =>
        Classical.choose
          (Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter
            (psi i) (hpsiBook i))
      have hdegPsi : ∀ i : ι,
          Section1.degree (psi i) = (degPsi i : ℂ) := by
        intro i
        exact (Classical.choose_spec
          (Section1.degree_nat_dvd_card_of_isBookIrreducibleCharacter
            (psi i) (hpsiBook i))).1
      have hresDegree : Section1.degree res = (n : ℂ) := by
        simpa [res, Section1.subgroupRestriction, Section1.degree]
          using hfDegree
      have hdegreeSumPsi : ∑ i : ι, e i * degPsi i = n := by
        exact_mod_cast (show
          (∑ i : ι, ((e i * degPsi i : ℕ) : ℂ)) = (n : ℂ) by
          calc
            (∑ i : ι, ((e i * degPsi i : ℕ) : ℂ)) =
                ∑ i : ι,
                  (e i : ℂ) * Section1.degree (psi i) := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [hdegPsi i]
              push_cast
              rfl
            _ = Section1.degree
                  (Section1.weightedFamilySum
                    (fun i => (e i : ℂ)) psi) := by
              unfold Section1.degree Section1.weightedFamilySum
              apply Finset.sum_congr
              · ext i
                simp
              · intro i _hi
                rfl
            _ = Section1.degree res := by rw [← hdecomp]
            _ = (n : ℂ) := hresDegree)
      have hdegreeLower :
          b * Nat.card d.S * (Nat.card d.Q1 - 1) ≤ n := by
        by_cases hb : b = 0
        · simp [hb]
        have hbPos : 0 < b := Nat.pos_of_ne_zero hb
        have haPos : ∀ chi : chars, 0 < a chi := by
          intro chi
          have hdegNe :=
            Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup
              (chi : Section1.ClassFunction d.H)
              ((hchars _).mp chi.property).1
          by_contra ha
          have haZero : a chi = 0 := by omega
          apply hdegNe
          rw [hdegreeA chi, haZero]
          simp
        have hexIdx : ∀ chi : chars, ∃ i : ι,
            psi i = (chi : Section1.ClassFunction d.H) := by
          intro chi
          by_contra hnone
          push Not at hnone
          have hzero :
              Section1.scalarProduct d.H res
                (chi : Section1.ClassFunction d.H) = 0 := by
            rw [hdecomp,
              Section1.scalarProduct_weightedFamilySum_left]
            apply Finset.sum_eq_zero
            intro i _hi
            rw [Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
              (hpsiIrr i) ((hchars _).mp chi.property).1 (hnone i)]
            simp
          have hpositive : 0 < mult chi := by
            rw [hmultRatio chi]
            exact Nat.mul_pos hbPos (haPos chi)
          rw [hmultEq chi] at hzero
          exact (Nat.ne_of_gt hpositive) (by exact_mod_cast hzero)
        let idx : chars → ι := fun chi =>
          Classical.choose (hexIdx chi)
        have hidxEq : ∀ chi : chars,
            psi (idx chi) =
              (chi : Section1.ClassFunction d.H) := by
          intro chi
          exact Classical.choose_spec (hexIdx chi)
        have hidxInj : Function.Injective idx := by
          intro chi zeta hEq
          apply Subtype.ext
          calc
            (chi : Section1.ClassFunction d.H) = psi (idx chi) :=
              (hidxEq chi).symm
            _ = psi (idx zeta) := by rw [hEq]
            _ = (zeta : Section1.ClassFunction d.H) := hidxEq zeta
        have hidxCoeff : ∀ chi : chars,
            e (idx chi) = b * a chi := by
          intro chi
          have hcomplex :
              (e (idx chi) : ℂ) = (mult chi : ℂ) := by
            rw [← hmultPsi (idx chi), hidxEq chi, hmultEq chi]
          have hnat : e (idx chi) = mult chi := by
            exact_mod_cast hcomplex
          rw [hnat, hmultRatio chi]
        have hidxDegree : ∀ chi : chars,
            degPsi (idx chi) = a chi * Nat.card d.D := by
          intro chi
          exact_mod_cast (hdegPsi (idx chi)).symm.trans
            ((congrArg Section1.degree (hidxEq chi)).trans
              (hdegreeA chi))
        calc
          b * Nat.card d.S * (Nat.card d.Q1 - 1) =
              b * (Nat.card d.S * (Nat.card d.Q1 - 1)) := by
            ring
          _ = b *
                (∑ chi : chars,
                  a chi * (a chi * Nat.card d.D)) := by
            rw [hdegreeSumA]
          _ = ∑ chi : chars,
                e (idx chi) * degPsi (idx chi) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro chi _hchi
            rw [hidxCoeff chi, hidxDegree chi]
            ring
          _ = ∑ i ∈ (Finset.univ : Finset chars).image idx,
                e i * degPsi i := by
            exact (Finset.sum_image
              (f := fun i : ι => e i * degPsi i) (g := idx)
              hidxInj.injOn).symm
          _ ≤ ∑ i : ι, e i * degPsi i := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ _)
              (fun i _hi _hnot => Nat.zero_le (e i * degPsi i))
          _ = n := hdegreeSumPsi
      have hkernelZero :
          b = 0 → Section1.subgroupInKernel' res d.Q1 := by
        intro hb
        have hpsiKernel : ∀ i : ι, e i ≠ 0 →
            Section1.subgroupInKernel' (psi i) d.Q1 := by
          intro i hei
          by_contra hnotker
          have hpsiMem : psi i ∈ chars :=
            (hchars (psi i)).mpr ⟨hpsiIrr i, hnotker⟩
          let chi : chars := ⟨psi i, hpsiMem⟩
          have heq : e i = mult chi := by
            exact_mod_cast (hmultPsi i).symm.trans (hmultEq chi)
          apply hei
          rw [heq, hmultRatio chi, hb]
          simp
        intro q
        rw [hdecomp]
        unfold Section1.weightedFamilySum
        apply Finset.sum_congr rfl
        intro i _hi
        by_cases hei : e i = 0
        · simp [hei]
        · rw [hpsiKernel i hei q, Section1.degree_apply]
      have hcarddS : Nat.card d.S = Nat.card S := by
        calc
          Nat.card d.S = Nat.card (d.S.map d.H.subtype) :=
            (Subgroup.card_map_of_injective
              (K := d.S) (f := d.H.subtype)
              d.H.subtype_injective).symm
          _ = Nat.card S := by rw [hdS]
      have hcarddQ1 : Nat.card d.Q1 = Nat.card Q1 := by
        calc
          Nat.card d.Q1 = Nat.card (d.Q1.map d.H.subtype) :=
            (Subgroup.card_map_of_injective
              (K := d.Q1) (f := d.H.subtype)
              d.H.subtype_injective).symm
          _ = Nat.card Q1 := by rw [hdQ1]
      refine ⟨b, ?_, hkernelZero⟩
      rw [hcarddS, hcarddQ1] at hdegreeLower
      exact hdegreeLower
    obtain ⟨b1, hb1Degree, hb1Kernel⟩ :=
      hrestriction_multiplicity f1 n1 hf1Irr hf1Ne hf1Degree
        hpair_avoids_extension.1
    obtain ⟨b2, hb2Degree, hb2Kernel⟩ :=
      hrestriction_multiplicity f2 n2 hf2Irr hf2Ne hf2Degree
        hpair_avoids_extension.2
    have hcoefficient_sum_bound :
        (b1 + b2) * (Nat.card Q1 - 1) ≤ Nat.card Q1 := by
      let hprod : Section2.IsInternalDirectProduct d.Q d.S d.Q1 :=
        { left_le := d.S_le_Q
          right_le := d.Q1_le_Q
          commute := by
            intro s hs q hq
            exact d.S_commutes_Q1 s q hs hq
          inf_eq_bot := d.S_disjoint_Q1.eq_bot
          mul_surjective := by
            intro q hq
            have hqSup : q ∈ d.S ⊔ d.Q1 := by
              rw [d.Q_eq_S_sup_Q1]
              exact hq
            have hnorm : d.S ≤ Subgroup.normalizer (d.Q1 : Set d.H) := by
              refine subgroup_le_normalizer_of_conj_mem d.Q1 d.S ?_
              intro s q hq
              have hcomm :=
                d.S_commutes_Q1 (s : d.H) q s.property hq
              rw [hcomm]
              simpa using hq
            have hqProd : q ∈ (d.S : Set d.H) * (d.Q1 : Set d.H) := by
              rw [← Subgroup.coe_mul_of_left_le_normalizer_right
                d.S d.Q1 hnorm]
              exact hqSup
            rcases hqProd with ⟨s, hs, q1, hq1, rfl⟩
            exact ⟨s, hs, q1, hq1, rfl⟩ }
      let e : d.S × d.Q1 ≃* d.Q :=
        Section3.internalDirectProductMulEquiv hprod
      have hcarddQ : Nat.card d.Q = Nat.card d.S * Nat.card d.Q1 := by
        rw [← Nat.card_prod]
        exact (Nat.card_congr e.toEquiv).symm
      have hcarddS : Nat.card d.S = Nat.card S := by
        calc
          Nat.card d.S = Nat.card (d.S.map d.H.subtype) :=
            (Subgroup.card_map_of_injective
              (K := d.S) (f := d.H.subtype) d.H.subtype_injective).symm
          _ = Nat.card S := by rw [hdS]
      have hcarddQ1 : Nat.card d.Q1 = Nat.card Q1 := by
        calc
          Nat.card d.Q1 = Nat.card (d.Q1.map d.H.subtype) :=
            (Subgroup.card_map_of_injective
              (K := d.Q1) (f := d.H.subtype) d.H.subtype_injective).symm
          _ = Nat.card Q1 := by rw [hdQ1]
      have hcardQ : Nat.card Q = Nat.card S * Nat.card Q1 := by
        calc
          Nat.card Q = Nat.card d.Q := by
            rw [← hdQ]
            exact Subgroup.card_map_of_injective
              (K := d.Q) (f := d.H.subtype) d.H.subtype_injective
          _ = Nat.card d.S * Nat.card d.Q1 := hcarddQ
          _ = Nat.card S * Nat.card Q1 := by rw [hcarddS, hcarddQ1]
      have hcardSPos : 0 < Nat.card S := Nat.card_pos
      have hcardSNeOne : Nat.card S ≠ 1 := by
        intro hSone
        have hQeven : Even (Nat.card Q) := hch.1.section2.hA.A1.Q_even
        rw [hcardQ, hSone, one_mul] at hQeven
        exact (Nat.not_even_iff_odd.mpr hch.1.section2.Q1_odd_order) hQeven
      have hcardSTwo : 2 ≤ Nat.card S := by omega
      have hsum := Nat.add_le_add hb1Degree hb2Degree
      have hsum' :
          (b1 + b2) * Nat.card S * (Nat.card Q1 - 1) ≤
            Nat.card S * Nat.card Q1 + 1 := by
        calc
          (b1 + b2) * Nat.card S * (Nat.card Q1 - 1) =
              b1 * Nat.card S * (Nat.card Q1 - 1) +
                b2 * Nat.card S * (Nat.card Q1 - 1) := by ring
          _ ≤ n1 + n2 := hsum
          _ = Nat.card S * Nat.card Q1 + 1 := by
            rw [← hcardQ, ← hdegreeSum]
      by_contra hnot
      have hlarge :
          Nat.card Q1 + 1 ≤ (b1 + b2) * (Nat.card Q1 - 1) := by
        omega
      have hmul := Nat.mul_le_mul_right (Nat.card S) hlarge
      have hsum'' :
          Nat.card S * ((b1 + b2) * (Nat.card Q1 - 1)) ≤
            Nat.card S * Nat.card Q1 + 1 := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hsum'
      have hbound :
          (Nat.card ↥Q1 + 1) * Nat.card ↥S ≤
            Nat.card ↥S * Nat.card ↥Q1 + 1 :=
        hmul.trans (by
          simpa [Nat.mul_comm] using hsum'')
      have hSle : Nat.card ↥S ≤ 1 := by
        apply Nat.le_of_add_le_add_left
        calc
          Nat.card ↥Q1 * Nat.card ↥S + Nat.card ↥S =
              (Nat.card ↥Q1 + 1) * Nat.card ↥S := by
                simp [Nat.add_mul]
          _ ≤ Nat.card ↥S * Nat.card ↥Q1 + 1 := hbound
          _ = Nat.card ↥Q1 * Nat.card ↥S + 1 := by
                rw [Nat.mul_comm (Nat.card ↥S) (Nat.card ↥Q1)]
      omega
    have hQ1card : 1 < Nat.card Q1 :=
      (Subgroup.one_lt_card_iff_ne_bot Q1).2 hQ1
    have hQ1odd : Odd (Nat.card Q1) := hch.1.section2.Q1_odd_order
    have hQ1cardNeTwo : Nat.card Q1 ≠ 2 := by
      rcases hQ1odd with ⟨k, hk⟩
      omega
    have hQ1cardLarge : 2 < Nat.card Q1 := by omega
    have hbzero : b1 = 0 ∨ b2 = 0 := by
      by_contra hnone
      push Not at hnone
      have hsumPos : 2 ≤ b1 + b2 := by omega
      have hmul := Nat.mul_le_mul_right (Nat.card Q1 - 1) hsumPos
      have hcontra : 2 * (Nat.card Q1 - 1) ≤ Nat.card Q1 :=
        hmul.trans hcoefficient_sum_bound
      omega
    have hrestriction_kernel_to_ambient :
        ∀ f : Section1.ClassFunction G,
          Section1.subgroupInKernel'
              (Section1.subgroupRestriction d.H f) d.Q1 →
            Section1.subgroupInKernel' f Q1 := by
      intro f hf q
      have hqMap : (q : G) ∈ d.Q1.map d.H.subtype := by
        rw [hdQ1]
        exact q.property
      rcases hqMap with ⟨qH, hqH, hqEq⟩
      have hqKernel := hf ⟨qH, hqH⟩
      change f (q : G) = f 1
      rw [← hqEq]
      simpa [Section1.subgroupRestriction, Section1.degree] using hqKernel
    rcases hbzero with hb1 | hb2
    · exact ⟨f1, hf1Irr, hf1Ne,
        hrestriction_kernel_to_ambient f1 (hb1Kernel hb1)⟩
    · exact ⟨f2, hf2Irr, hf2Ne,
        hrestriction_kernel_to_ambient f2 (hb2Kernel hb2)⟩
  have hnonsimple :
      ∃ L : Subgroup G, L.Normal ∧ L ≠ ⊥ ∧ L ≠ ⊤ := by
    letI : Fintype G := Fintype.ofFinite G
    obtain ⟨f, hfirr, hfne, hfQ1⟩ := hkernel_character
    have hf_not_top :
        ¬ Section1.subgroupInKernel' f (⊤ : Subgroup G) := by
      intro hker
      have horth :
          Section1.scalarProduct G f (Section1.principalCharacter G) = 0 :=
        Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
          hfirr hfne
      have hspdeg :
          Section1.scalarProduct G f (Section1.principalCharacter G) =
            Section1.degree f := by
        unfold Section1.scalarProduct Section1.principalCharacter Section1.degree
        have hsum :
            (∑ g : G, f g * star (1 : ℂ)) = ∑ _g : G, f 1 := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          have hg := hker ⟨g, by simp⟩
          change f g = f 1 at hg
          rw [star_one, mul_one]
          exact hg
        rw [hsum]
        simp
      have hdeg0 : Section1.degree f = 0 := by
        rw [← hspdeg, horth]
      rcases hfirr with ⟨_n, rho, hrhoirr, hfeq⟩
      have hself : Section1.scalarProduct G f f = 1 := by
        rw [hfeq]
        exact Section1.scalarProduct_representation_char_self rho hrhoirr
      have hself0 : Section1.scalarProduct G f f = 0 := by
        unfold Section1.scalarProduct Section1.degree at hdeg0
        unfold Section1.scalarProduct
        have hzero : ∀ g : G, f g = 0 := by
          intro g
          have hg := hker ⟨g, by simp⟩
          simpa [Section1.degree, hdeg0] using hg
        simp [hzero]
      norm_num [hself0] at hself
    rcases hfirr with ⟨n, rho, _hrhoirr, hfeq⟩
    have hQ1ker : Section1.subgroupInRepresentationKernel rho Q1 := by
      apply
        (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
          rho Q1).mp
      simpa [hfeq] using hfQ1
    let N : Subgroup G := rho.ker
    have hQ1leN : Q1 ≤ N := by
      intro q hq
      exact hQ1ker ⟨q, hq⟩
    have hNne : N ≠ ⊥ := by
      intro hN
      apply hQ1
      apply le_antisymm
      · intro q hq
        have : q ∈ (⊥ : Subgroup G) := by
          rw [← hN]
          exact hQ1leN hq
        simpa using this
      · exact bot_le
    have hNtop : N ≠ ⊤ := by
      intro hN
      apply hf_not_top
      rw [hfeq]
      apply
        (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
          rho ⊤).mpr
      intro g
      change (g : G) ∈ N
      rw [hN]
      trivial
    exact ⟨N, inferInstance, hNne, hNtop⟩
  rcases PFchapter1section3.proposition_2.{u, v}
      H D Q K V W Q0 S Q1 t s hch.1 hind hnonsimple with
    ⟨L, hLnormal, q, hodd, hq, hq_gt, hmodel⟩
  exact (PFchapter1section3.lemma_1.{u, v}
    H D Q K V W Q0 S Q1 t s hch.1 L hLnormal q
      hodd hq hq_gt hmodel).1


set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Theorem C: under (C1), `Q` is a `2`-group. -/
public theorem theorem_c
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hch : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
    HypothesisC1 G V)
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              ∃ (M : Subgroup L) (_ : M.Normal) (q : ℕ),
                Odd (Nat.card (L ⧸ M)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
                  ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : M ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : ΩL ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : M, ∀ ω : ΩL,
      eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : M ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : ΩL ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : M ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : ΩL ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)))) :
    IsPGroup 2 Q := by
  classical
  by_cases hQ1 : Q1 = ⊥
  · rcases theorem_c_Q_hasPrimePowerOrder_of_Q1_eq_bot
      H D Q K V W Q0 S Q1 t s hch hQ1 with ⟨n, hn⟩
    exact IsPGroup.of_card hn
  · exact theorem_c_of_Q1_ne_bot
      H D Q K V W Q0 S Q1 t s hch hind hQ1


end PFchapter3section1
end CFSG.BenderSuzuki
