module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCCoreDefs
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCSplit
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCOrthCent
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCOrthBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCOrthBlockFacts
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCOrthComp
import CFSG.LocalAnalysis.StandardType.GGQTwoTBCTransfer
import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.StandardType

open Polynomial CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem ggTBCReflCoreIn_orthDerived [Finite (V ≃ₗ[ZMod 2] V)] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * n)
    (hV : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even n) :
    GGTBCReflCoreIn n (orthDerived Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro H hHL hH hcard d hdH hd1 J hJ φ hφ hφr
  have hdL : d ∈ orthDerived Q := hHL hdH
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hH.2 d hdH) hd1
  have hd : OddOrderIsometry Q 3 d :=
    oddOrderIsometry_of_orthDerived Nat.prime_three (by rw [ZMod.ringChar_zmod_n]; decide) hQ
      ⟨d, hdL⟩ (by rw [Subgroup.orderOf_mk]; exact hd3)
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hHL.trans orthDerived_le_orthogonalGroup
  have hHC : H ≤ isometryCentralizer Q d := fun h hh =>
    Subgroup.mem_inf.mpr ⟨hHO hh, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hH.1.is_comm.comm ⟨h, hh⟩ ⟨d, hdH⟩))⟩
  have heq : orthDerived Q ⊓ Subgroup.centralizer {d} =
      orthDerived Q ⊓ isometryCentralizer Q d := by
    rw [isometryCentralizer, ← inf_assoc, inf_eq_left.mpr orthDerived_le_orthogonalGroup]
  rw [heq] at hφ
  refine ggTBC_refl_split (C := isometryCentralizer Q d) (A := supportedBlock Q d (X - 1))
    (B := supportedBlock Q d (X ^ 2 + X + 1)) (Ω := orthDerived Q) hH hHC
    (supportedBlock_le_isometryCentralizer _) (supportedBlock_le_isometryCentralizer _)
    (fun a ha b hb => ggTBC_block_commute hd hd1 ha hb) (ggTBC_block_inf_eq_bot hd hd1)
    (fun g hg => ggTBC_block_decomp hd hd1 hg)
    (fun g hg hgH => ggTBC_orth_mem_of_commute hQ hdim hHO hH hcard (Subgroup.mem_inf.mp hg).1 hgH)
    hHL ?_ hφ hφr
  rcases ggTBC_orth_comp_cases (F := ZMod 2) (Nat.card_zmod 2) hQ hdim hdL hd3 hJ with
    rfl | ⟨rfl, h6 | ⟨hdimW, hminus⟩⟩
  · exact Or.inr ⟨specialBlock_le_supportedBlock _,
      fun b hb => ggTBC_pow_three_mem_specialBlock hd hd1 hb⟩
  · exact Or.inl ⟨supportedFixedDerived_le_supportedBlock, ggTBC_orthDerived_inf_block_le hQ hd h6⟩
  · exfalso
    obtain ⟨-, s, hs, -, htype⟩ :=
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.dims hd
        (by rw [Nat.card_zmod]) hd1 hdim hV
    have hs2 : s = 2 := by omega
    exact hminus ((htype (by omega)).2 (hs2.symm ▸ even_two))

theorem ggTBCReflCoreIn_of_quotient_orthDerived {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {Q : QuadraticForm (ZMod 2) V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : Module.finrank (ZMod 2) V = 2 * n)
    (hV : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even n)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(orthDerived Q))
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L)) :
    GGTBCReflCoreIn n L := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) fun a b h =>
      LinearEquiv.ext (congrFun h)
  have hcore : GGTBCReflCore ↥(orthDerived Q) n :=
    (ggTBCReflCoreIn_iff (orthDerived Q)).mp (ggTBCReflCoreIn_orthDerived hQ hdim hV)
  let f : ↥L →* ↥(orthDerived Q) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Surjective f := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center ↥L := by
    ext l
    rw [MonoidHom.mem_ker]
    change θ (QuotientGroup.mk l) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine (ggTBCReflCoreIn_iff L).mpr (ggTBCReflCore_of_surjective f hf hker.le ?_ hcore)
  rw [hker]
  exact hZ

end CFSG.StandardType

end
