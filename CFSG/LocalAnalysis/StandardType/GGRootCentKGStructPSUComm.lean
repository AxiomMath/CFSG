module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructPSUBlock
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSU
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructND
import CFSG.LocalAnalysis.StandardType.GGRootCentKGPiece
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUModel
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.LeviAssembly
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpModel
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympTypes
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.B1
import CFSG.Quasithin.Background.C1GNC124
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.C31Steps
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2Three
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.Background.GoldschmidtS146RArith2
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.R3c20A
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S151YC
import CFSG.Quasithin.EmptyFaithful.S151cA2
import CFSG.Quasithin.EmptyFaithful.S151cCases
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.S153H32
import CFSG.Quasithin.EmptyFaithful.SBc5Aut
import CFSG.Quasithin.EmptyFaithful.SzN17Abs
import CFSG.Quasithin.EmptyFaithful.T1515Top9
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.J4Classes
import CFSG.Quasithin.H13.J4Core
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Recognition.CertTwoLocalPair
import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
import CFSG.Quasithin.Vol2.KGFactC31A7
import CFSG.Quasithin.Vol2.KGFactC31Blk
import CFSG.Quasithin.Vol2.KGFactC31HSCases
import CFSG.Quasithin.Vol2.KGFactC31HSMod
import CFSG.Quasithin.Vol2.KGFactC31Hat
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.Sporadic.Schreier.J4SNoCompCover
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.Universal.Unitary.SUExtras (mat mat_apply mat_injective)
open scoped commutatorElement

namespace KGPSU

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

private noncomputable def cornerUnits (σ : K ≃+* K) (k : ℕ) :
    ↥(Subgroup.centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) →* Kˣ :=
  (MonoidHom.fst Kˣ (Matrix (Fin k) (Fin k) K)).comp (RCSTSU.cornerMid σ k)

private theorem coe_cornerUnits (σ : K ≃+* K) (k : ℕ)
    (x : ↥(Subgroup.centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))) :
    ((cornerUnits (K := K) σ k x : Kˣ) : K) =
      mat σ (k + 2) (x : SU σ (k + 2)) (Fin.last (k + 1)) (Fin.last (k + 1)) := rfl

private theorem corner_commutator {σ : K ≃+* K} {k : ℕ} {x y : SU σ (k + 2)}
    (hx : x ∈ Subgroup.centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (hy : y ∈ Subgroup.centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :
    mat σ (k + 2) ⁅x, y⁆ (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 := by
  let x' : ↥(Subgroup.centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :=
    ⟨x, hx⟩
  let y' : ↥(Subgroup.centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2)))) :=
    ⟨y, hy⟩
  have hmap := map_commutatorElement (cornerUnits (K := K) σ k) x' y'
  have hcomm1 : ⁅cornerUnits (K := K) σ k x', cornerUnits (K := K) σ k y'⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [hcomm1] at hmap
  have h2 := congrArg (fun u : Kˣ => (u : K)) hmap
  rw [coe_cornerUnits] at h2
  have h4 : ((⁅x', y'⁆ : ↥(Subgroup.centralizer
      ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))) : SU σ (k + 2)) = ⁅x, y⁆ := rfl
  rwa [h4] at h2

theorem commutator_centralizer_rootU_le (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k) :
    ⁅Subgroup.centralizer {AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))},
      Subgroup.centralizer {AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))}⁆ ≤
      radical h (k + 1) ⊔ suBlock h k := by
  have hsurj : Function.Surjective (AutPSU.projU h (n := k + 2)) :=
    (QuotientGroup.mk'_surjective _).comp (AutPSU.suEquiv h).surjective
  have hZc := projU_ker_le_center (K := K) (f := f) h (k + 1)
  have hZ := projU_ker_odd (K := K) (f := f) h (k + 1)
  have hroot2 := rootU_mul_self (K := K) (f := f) k
  have hcomm : ⁅Subgroup.centralizer ({AutPSU.rootU (K := K) (f := f) (k + 1)} :
      Set (SU (unitaryInvolution K 2 f) (k + 2))),
      Subgroup.centralizer ({AutPSU.rootU (K := K) (f := f) (k + 1)} :
      Set (SU (unitaryInvolution K 2 f) (k + 2)))⁆ ≤
      RCSTSU.suRad (unitaryInvolution K 2 f) k ⊔
        (iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : x ∈ Subgroup.centralizer ({ggInvSU (unitaryInvolution K 2 f) (k + 2) 1} :
        Set (SU (unitaryInvolution K 2 f) (k + 2))) := hx
    have hy' : y ∈ Subgroup.centralizer ({ggInvSU (unitaryInvolution K 2 f) (k + 2) 1} :
        Set (SU (unitaryInvolution K 2 f) (k + 2))) := hy
    have hmem : ⁅x, y⁆ ∈ Subgroup.centralizer
        ({ggInvSU (unitaryInvolution K 2 f) (k + 2) 1} :
          Set (SU (unitaryInvolution K 2 f) (k + 2))) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx' hy') (Subgroup.inv_mem _ hx'))
        (Subgroup.inv_mem _ hy')
    exact RCSTSU.mem_suRad_sup_of_corner (σ := unitaryInvolution K 2 f) hmem
      (corner_commutator hx' hy')
  have hR : (RCSTSU.suRad (unitaryInvolution K 2 f) k).map (AutPSU.projU h) =
      radical h (k + 1) := by
    rw [suRad_eq_suR h hk, radical_of_le]
  have hL : ((iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range).map (AutPSU.projU h) =
      suBlock h k := by
    rw [← MonoidHom.range_comp]
    rfl
  calc ⁅Subgroup.centralizer {AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))},
        Subgroup.centralizer {AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))}⁆
      = (⁅Subgroup.centralizer ({AutPSU.rootU (K := K) (f := f) (k + 1)} :
            Set (SU (unitaryInvolution K 2 f) (k + 2))),
          Subgroup.centralizer ({AutPSU.rootU (K := K) (f := f) (k + 1)} :
            Set (SU (unitaryInvolution K 2 f) (k + 2)))⁆).map (AutPSU.projU h) := by
        rw [← map_centralizer_of_involution (AutPSU.projU h) hsurj hZc hZ hroot2,
          Subgroup.map_commutator]
    _ ≤ ((RCSTSU.suRad (unitaryInvolution K 2 f) k ⊔
          (iotaHom (σ := unitaryInvolution K 2 f) (m := k)).range)).map (AutPSU.projU h) :=
        Subgroup.map_mono hcomm
    _ = radical h (k + 1) ⊔ suBlock h k := by
        rw [Subgroup.map_sup, hR, hL]

theorem blockHom_injective (h : UnitaryFieldData 2 f K) (k : ℕ) :
    Function.Injective (blockHom h k) := by
  have hinj : ∀ B : SU (unitaryInvolution K 2 f) k, blockHom h k B = 1 → B = 1 := by
    intro B hB
    have hz : AutPSU.projU h ((iotaHom (σ := unitaryInvolution K 2 f) (m := k)) B) = 1 := hB
    have hzZ : AutPSU.suEquiv h ((iotaHom (σ := unitaryInvolution K 2 f) (m := k)) B) ∈
        normOneScalars h (AutPSU.XJ h (k + 2)) (k + 2) := by
      rw [← QuotientGroup.eq_one_iff]
      simpa [AutPSU.projU_apply] using hz
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp hzZ
    have hmat : mat (unitaryInvolution K 2 f) (k + 2)
        ((iotaHom (σ := unitaryInvolution K 2 f) (m := k)) B) =
        Matrix.scalar (Fin (k + 2)) (c : K) := by
      rw [mat_apply, ← AutPSU.coe_suEquiv (h := h) (x := _), hc,
        Matrix.GeneralLinearGroup.coe_scalar]
    have hcorner : (c : K) = 1 := by
      have h1 := RCSTSU.corner_iotaHom (σ := unitaryInvolution K 2 f) (k := k) B
      rw [hmat] at h1
      simpa [Matrix.scalar_apply] using h1
    have hmat1 : mat (unitaryInvolution K 2 f) (k + 2)
        ((iotaHom (σ := unitaryInvolution K 2 f) (m := k)) B) = 1 := by
      rw [hmat, hcorner, Matrix.scalar_apply, Matrix.diagonal_one]
    have hI1 : (iotaHom (σ := unitaryInvolution K 2 f) (m := k)) B = 1 :=
      mat_injective hmat1
    exact CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom_injective
      (by rw [hI1, map_one])
  intro B B' hBB'
  have h : B * B'⁻¹ = 1 := hinj _ (by rw [map_mul, map_inv, hBB', mul_inv_cancel])
  rwa [mul_inv_eq_one] at h

private theorem quasisimpleHyp {k : ℕ} (hk : 2 ≤ k) (hkq : 4 ≤ k ∨ 2 ≤ f) :
    (3 ≤ k ∧ (k, 2 ^ f) ≠ (3, 2)) ∨ (k = 2 ∧ 4 ≤ 2 ^ f) := by
  rcases hkq with h4 | hf2
  · exact Or.inl ⟨by omega, fun h => by
      simp only [Prod.mk.injEq] at h
      omega⟩
  · rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk2 : k = 2 := by omega
      subst hk2
      exact Or.inr ⟨rfl, by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2⟩
    · exact Or.inl ⟨hk3, fun h => by
        simp only [Prod.mk.injEq] at h
        have h4 : 4 ≤ 2 ^ f := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
        omega⟩

theorem isQuasisimple_suBlock (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k)
    (hkq : 4 ≤ k ∨ 2 ≤ f) : CFSG.Assembly.IsQuasisimple ↥(suBlock h k) := by
  have hq : CFSG.IsQuasisimple (SU (unitaryInvolution K 2 f) k) :=
    RCSTSU.isQuasisimple_su (F := K) h.card_eq_sq (quasisimpleHyp (f := f) hk hkq)
  let e : SU (unitaryInvolution K 2 f) k ≃* ↥(suBlock h k) :=
    MonoidHom.ofInjective (blockHom_injective h k)
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)

theorem largeEvenMarking_suBlock (h : UnitaryFieldData 2 f K) {k : ℕ} (hk : 2 ≤ k)
    (hkq : 4 ≤ k ∨ 2 ≤ f) :
    LargeEvenMarking ↥(suBlock h k) (fun lab R _ I _ θ => GGChevStTag lab ∧
      ∀ α ∈ KGND.suConjSet (blockOnto h k), ∃ φ ∈ I, ∀ y : ↥(suBlock h k),
        φ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))) := by
  have hker : (blockOnto h k).ker ≤
      Subgroup.center ↥(SU (unitaryInvolution K 2 f) k) := by
    rw [show (blockOnto h k).ker = (blockHom h k).ker from MonoidHom.ker_rangeRestrict _]
    exact RCSTSU.ker_comp_iotaHom_le (AutPSU.projU h) (projU_ker_le_center h (k + 1))
  refine KGND.largeEvenMarking_suConjSet (F := K) h.card_eq_sq h.one_le hk ?_
    (blockOnto h k) (blockOnto_surjective h k) hker
  intro hk3
  rcases hkq with h4 | h2
  · omega
  · exact h2

private theorem isSolvable_sup_of_le_normalizer {G : Type} [Group G] {B S : Subgroup G}
    (hSB : S ≤ Subgroup.normalizer (B : Set G)) (hdisj : B ⊓ S = ⊥)
    (hB : Group.IsSolvable ↥B) (hS : Group.IsSolvable ↥S) :
    Group.IsSolvable ↥(B ⊔ S) := by
  obtain ⟨π, -, hπker, -⟩ := exists_sup_proj hSB hdisj
  haveI : Group.IsSolvable ↥B := hB
  haveI : Group.IsSolvable ↥S := hS
  let φ : ↥B →* ↥(B.subgroupOf (B ⊔ S)) :=
    (Subgroup.subgroupOfEquivOfLe le_sup_left).symm.toMonoidHom
  have hφ : Function.Surjective φ := (Subgroup.subgroupOfEquivOfLe le_sup_left).symm.surjective
  haveI : Group.IsSolvable ↥(B.subgroupOf (B ⊔ S)) :=
    Group.isSolvable_of_surjective (f := φ) hφ
  exact Group.isSolvable_of_ker_le_range (B.subgroupOf (B ⊔ S)).subtype π (by
    rw [hπker, Subgroup.range_subtype])

theorem isSolvable_centralizer_rootU (h : UnitaryFieldData 2 f K) (hf : f = 1) {k : ℕ}
    (hk : 2 ≤ k) (hk3 : k ≤ 3) :
    Group.IsSolvable ↥(Subgroup.centralizer
      {AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))}) := by
  have hk23 : k = 2 ∨ k = 3 := by omega
  have hR2 : IsPGroup 2 ↥(radical h (k + 1)) := by
    rw [radical_of_le]
    exact (suR_isPGroup (K := K) (f := f) h (show 1 ≤ k + 1 by omega)).map (AutPSU.projU h)
  have hRsolv : Group.IsSolvable ↥(radical h (k + 1)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥(radical h (k + 1)) := IsPGroup.isNilpotent hR2
    exact IsNilpotent.to_isSolvable
  have hLsolv : Group.IsSolvable ↥(suBlock h k) := by
    rcases hk23 with rfl | rfl
    · haveI : Group.IsSolvable ↥(SU (unitaryInvolution K 2 f) 2) :=
        CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.su_two_solvable h.card_eq_sq hf
      exact Group.isSolvable_of_surjective (f := blockOnto h 2) (blockOnto_surjective h 2)
    · haveI : Group.IsSolvable ↥(SU (unitaryInvolution K 2 f) 3) :=
        CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.su_three_solvable h.card_eq_sq hf
      exact Group.isSolvable_of_surjective (f := blockOnto h 3) (blockOnto_surjective h 3)
  have hRLsolv : Group.IsSolvable ↥(radical h (k + 1) ⊔ suBlock h k) :=
    isSolvable_sup_of_le_normalizer (suBlock_le_normalizer_radical h hk)
      (radical_inf_suBlock h hk) hRsolv hLsolv
  set C : Subgroup (AutPSU.PJ h (k + 2)) :=
    Subgroup.centralizer {AutPSU.projU h (AutPSU.rootU (K := K) (f := f) (k + 1))} with hC
  change Group.IsSolvable ↥C
  have hcomm : ⁅C, C⁆ ≤ radical h (k + 1) ⊔ suBlock h k := by
    rw [hC]
    exact commutator_centralizer_rootU_le h hk
  haveI : Group.IsSolvable ↥(radical h (k + 1) ⊔ suBlock h k) := hRLsolv
  have hCommSolv : Group.IsSolvable ↥(commutator ↥C) := by
    have hmap : (commutator ↥C).map C.subtype = ⁅C, C⁆ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    have hle : (commutator ↥C).map C.subtype ≤ radical h (k + 1) ⊔ suBlock h k := by
      rw [hmap]
      exact hcomm
    let e := Subgroup.equivMapOfInjective (commutator ↥C) C.subtype
      (Subgroup.subtype_injective C)
    let g : ↥(commutator ↥C) →* ↥(radical h (k + 1) ⊔ suBlock h k) :=
      (Subgroup.inclusion hle).comp e.toMonoidHom
    exact Group.isSolvable_of_isSolvable_injective (f := g)
      ((Subgroup.inclusion_injective hle).comp e.injective)
  exact (Group.isSolvable_commutator_iff (G := ↥C)).mp hCommSolv

end KGPSU

namespace KGND

theorem kgPiecesD_of_isSolvable {U : Type} [Group U] {𝒟 : Subgroup (MulAut U)} {z : U}
    (hsol : Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set U))) : KGPiecesD 𝒟 z := by
  classical
  intro G _ _ ψ hψ E hE _
  have hC₀ : ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G) =
      (Subgroup.centralizer ({z} : Set U)).map ψ :=
    RCSTSp.range_inf_centralizer_of_injective hψ z
  haveI hC₀solv : Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G)) := by
    rw [hC₀]
    haveI : Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set U)) := hsol
    have h1 : Group.IsSolvable
        ↥((ψ.comp (Subgroup.centralizer ({z} : Set U)).subtype).range) :=
      Group.isSolvable_of_surjective
        (f := (ψ.comp (Subgroup.centralizer ({z} : Set U)).subtype).rangeRestrict)
        (MonoidHom.rangeRestrict_surjective _)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
  refine ⟨∅, ?_, ?_⟩
  · intro P hP hperf
    rw [sSup_empty, le_bot_iff]
    haveI : Group.IsSolvable
        ↥(P.subgroupOf (ψ.range ⊓ Subgroup.centralizer ({ψ z} : Set G))) := inferInstance
    have hsurj : Function.Surjective
        ((Subgroup.subgroupOfEquivOfLe hP).toMonoidHom) :=
      (Subgroup.subgroupOfEquivOfLe hP).surjective
    have h1 : Group.IsSolvable ↥P :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hP).toMonoidHom) hsurj
    haveI : Group.IsSolvable ↥P := h1
    by_contra hne
    haveI : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
    haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
    exact Group.IsPerfect.not_isSolvable ↥P inferInstance
  · intro J hJ
    simp at hJ

end KGND

end CFSG.StandardType
