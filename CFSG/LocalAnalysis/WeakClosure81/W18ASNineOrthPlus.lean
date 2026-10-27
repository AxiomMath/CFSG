module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthBridge
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineWr
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
import CFSG.RankThree.PartOne.K159.Klein
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.RankThree.PartOne.K159 CFSG.RankThree.PartOne.K159.Klein
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
open Matrix (SpecialLinearGroup)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.SeitzReduction.F4Pilot (charP_two_of_natCard_eq_two_pow one_le_of_natCard_eq_two_pow)

theorem kleinCommutatorOrthogonalSix {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K W) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank K W = 6)
    (hts : ∃ U : Submodule K W, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nonempty (commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≃* StatedSL 4 K) := by
  obtain ⟨e⟩ := exists_isometry_quadPlus_three Q hQ hd hts
  obtain ⟨hs, hp⟩ := sl4_isSimpleGroup_and_perfect (K := K)
  have hρinj := transportHom_injective e (Klein.rho : SpecialLinearGroup (Fin 4) K →* _)
    rho_injective
  have hρmem := transportHom_mem e (Klein.rho : SpecialLinearGroup (Fin 4) K →* _) rho_mem
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set ρ := transportHom e (Klein.rho : SpecialLinearGroup (Fin 4) K →* _) with hρ
  have hle : ρ.range ≤ O := by
    rintro _ ⟨g, rfl⟩
    exact hρmem g
  have hcard : Nat.card O = 2 * Nat.card (SpecialLinearGroup (Fin 4) K) := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr e,
      card_orthogonalGroup_quadPlus_three]
  obtain ⟨-, -, -, -, -, -, hcomm, -⟩ := derived_of_index_two_model O ρ hρinj hle hcard
  have h1 : (commutator ↥O).map O.subtype = ρ.range := by
    rw [Subgroup.map_subtype_commutator, hcomm]
  let e1 : commutator ↥O ≃* ρ.range :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr h1)
  let e2 : ρ.range ≃* SpecialLinearGroup (Fin 4) K := (MonoidHom.ofInjective hρinj).symm
  exact ⟨e1.trans (e2.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K))⟩

theorem noSocle185Factor_orthogonalPlus_two (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    NoSocle185Factor ↥(CFSG.PGLModel.orthogonalPlus 2 F) := by
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hle : (OmegaPlusCell.jProd (F := F)).range ≤ orthGroup (StatedQuadPlus 2 F) := by
    rintro _ ⟨x, rfl⟩
    exact OmegaPlusCell.jProd_mem_orthGroup x
  show NoSocle185Factor ↥(orthGroup (StatedQuadPlus 2 F))
  refine NoSocle185Factor.of_index_two
    ((OmegaPlusCell.jProd (F := F)).range.subgroupOf (orthGroup (StatedQuadPlus 2 F)))
    OmegaPlusCell.relIndex_jProd_range ?_
  exact NoSocle185Factor.of_mulEquiv
    ((MonoidHom.ofInjective OmegaPlusCell.jProd_injective).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm)
    ((noSocle185Factor_sl2 hO hF).prod (noSocle185Factor_sl2 hO hF))

theorem noSocle185Factor_statedOmega_quadPlus_three (hO : LieOrderFormulasInput) {F : Type}
    [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    NoSocle185Factor ↥(StatedOmega (StatedQuadPlus 3 F)) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  obtain ⟨hnd, hts⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := F) (n := 3) le_rfl
  obtain ⟨eK⟩ := kleinCommutatorOrthogonalSix (quadPlus 3 F) hnd (by simp) hts
  let E : ↥(StatedOmega (StatedQuadPlus 3 F)) ≃* Matrix.SpecialLinearGroup (Fin 4) F :=
    (statedOmegaEquivCommutator (coe_quadPlus 3 F)).trans
      (eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 F).symm)
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) F) :=
    (CFSG.RankThree.PartOne.K159.Klein.sl4_isSimpleGroup_and_perfect (K := F)).1
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadPlus 3 F)) := E.isSimpleGroup
  refine NoSocle185Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
  have hadm : StatedLieAdmissible .PSL 4 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
      fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
  have hM : Nat.card T * lieOrderDivisor .PSL 4 (2 ^ n) = lieOrderNumerator .PSL 4 (2 ^ n) := by
    rw [lieOrderDivisor_psl_four_two_pow hn, mul_one, ← Nat.card_congr e.toEquiv,
      Nat.card_congr E.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
    rfl
  rcases hT.crossChar hO hadm hM with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
  · omega
  · omega
  · exact absurd h (by decide)

theorem noSocle185Factor_orthogonalPlus_three (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    NoSocle185Factor ↥(CFSG.PGLModel.orthogonalPlus 3 F) :=
  noSocle185Factor_orthogonalPlus_of_statedOmega 3
    (noSocle185Factor_statedOmega_quadPlus_three hO hF)

end CFSG.LocalAnalysis.WeakClosure81

end
