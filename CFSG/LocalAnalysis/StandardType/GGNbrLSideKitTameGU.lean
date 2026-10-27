module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitComm
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial
import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Assembly.OpenBridges
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)

private theorem kitTame_card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem kitTame_isSolvable_of_card_two_three {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : Nat.card G = 2 ^ a * 3 ^ b) : Group.IsSolvable G :=
  CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (h ▸ kitTame_card_primeFactors_two_three a b ha hb)

private theorem kitTame_finite_generalLinearGroup {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] : Finite (LinearMap.GeneralLinearGroup E W) := by
  have := hE.finite
  have : Finite W := Module.finite_of_finite E
  have : Finite (Module.End E W) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
  exact Finite.of_injective _ Units.val_injective

private theorem kitTame_isSolvable_sesqUnitaryGroup_of_small {ℓ g : ℕ} {E : Type} [Field E]
    (hE : UnitaryFieldData ℓ g E) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm)
    (hHfl : Hf.SeparatingLeft)
    (hsmall : Module.finrank E W ≤ 1 ∨ (¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧
      (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)))) : Group.IsSolvable ↥(sesqUnitaryGroup Hf) := by
  have hq2 : 2 ≤ ℓ ^ g := by
    have := Nat.one_lt_pow (by have := hE.one_le; omega : g ≠ 0) hE.prime.one_lt
    omega
  haveI := kitTame_finite_generalLinearGroup hE (W := W)
  by_cases hm : 2 ≤ Module.finrank E W
  · have hq : ¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ g) ∧ (Module.finrank E W = 3 → 3 ≤ ℓ ^ g)) := by
      rcases hsmall with h | h
      · omega
      · exact h
    obtain ⟨hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl
      rfl (by omega : 1 ≤ Module.finrank E W)
    have hexc : (Module.finrank E W = 2 ∧ ℓ ^ g = 2) ∨ (Module.finrank E W = 2 ∧ ℓ ^ g = 3) ∨
        (Module.finrank E W = 3 ∧ ℓ ^ g = 2) := by
      by_contra hn
      push Not at hn
      obtain ⟨h1, h2, h3⟩ := hn
      refine hq ⟨fun h2' => ?_, fun h3' => ?_⟩
      · by_contra hlt
        rcases (show ℓ ^ g = 2 ∨ ℓ ^ g = 3 by omega) with hQ | hQ
        · exact h1 h2' hQ
        · exact h2 h2' hQ
      · by_contra hlt
        exact h3 h3' (by omega)
    rcases hexc with ⟨hm2, hQ⟩ | ⟨hm2, hQ⟩ | ⟨hm3, hQ⟩
    · rw [hm2, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 18 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h18 : Nat.card ↥(sesqUnitaryGroup Hf) = 18 := by exact_mod_cast hcard.trans e
      exact kitTame_isSolvable_of_card_two_three (a := 1) (b := 2) (by norm_num) (by norm_num)
        (by rw [h18]; norm_num)
    · rw [hm2, hQ] at hcard
      have e : ((3 : ℕ) : ℤ) ^ (2 * (2 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 2, (((3 : ℕ) : ℤ) ^ i - (-1) ^ i) = 96 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h96 : Nat.card ↥(sesqUnitaryGroup Hf) = 96 := by exact_mod_cast hcard.trans e
      exact kitTame_isSolvable_of_card_two_three (a := 5) (b := 1) (by norm_num) (by norm_num)
        (by rw [h96]; norm_num)
    · rw [hm3, hQ] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 1 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 648 := by
        norm_num [Finset.prod_Icc_succ_top]
      have h648 : Nat.card ↥(sesqUnitaryGroup Hf) = 648 := by exact_mod_cast hcard.trans e
      exact kitTame_isSolvable_of_card_two_three (a := 3) (b := 4) (by norm_num) (by norm_num)
        (by rw [h648]; norm_num)
  · refine Group.isSolvable_of_comm fun a b => Subtype.ext (Units.ext ?_)
    have := (CFSG.RankThree.PartOne.KCUnitary.End_commute_of_finrank_le_one (E := E) (W := W)
      (by omega) ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
      ((b : LinearMap.GeneralLinearGroup E W) : Module.End E W)).eq
    simpa [Subgroup.coe_mul, Units.val_mul] using this

private theorem kitTame_map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) :
    (commutator A).map φ.toMonoidHom = commutator B := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 φ.surjective]

private theorem kitTame_group_heldGU {r n : ℕ} {K E : Type} [Field K] [Finite K]
    [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    (hEc : Nat.card E = Nat.card K ^ 2) (hτQ : ∀ y, τ y = y ^ Nat.card K) :
    CFSG.IsQuasisimple ↥(commutator (heldGU r E τ hτ)) ∨
      Group.IsSolvable (heldGU r E τ hτ) := by
  classical
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite E
  have hE : UnitaryFieldData 2 n E :=
    { prime := Nat.prime_two
      one_le := hn
      card := by
        rw [hEc, hK, ← pow_mul, show n * 2 = 2 * n by omega] }
  let ρE : E ≃+* E :=
    { toFun := hE.bar, invFun := hE.bar, left_inv := hE.bar_bar, right_inv := hE.bar_bar,
      map_mul' := hE.bar.map_mul, map_add' := hE.bar.map_add }
  have hρE : ∀ y, ρE (ρE y) = y := hE.bar_bar
  have hτbar : τ = ρE := by
    refine RingEquiv.ext fun y => ?_
    rw [hτQ y, hK]
    change y ^ 2 ^ n = hE.bar y
    rw [hE.bar_apply]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := hE.charP
  let B : (Fin r → E) →ₛₗ[hE.bar] (Fin r → E) →ₗ[E] E :=
    CFSG.LinearGroups.stdHermForm hE r
  have hB : B.IsSymm := CFSG.LinearGroups.stdHermForm_isSymm hE r
  have hBl : B.SeparatingLeft := CFSG.LinearGroups.stdHermForm_separatingLeft hE r
  let b : Module.Basis (Fin r) E (Fin r → E) := Pi.basisFun E (Fin r)
  have hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    change (CFSG.LinearGroups.stdHermForm hE r (b i)) (b j) = if i = j then 1 else 0
    rw [CFSG.LinearGroups.stdHermForm_apply]
    by_cases h : i = j <;> simp [b, Pi.basisFun_apply, Pi.single_apply, h, eq_comm]
  obtain ⟨eU⟩ := CFSG.LieType.SemisimpleCentralizers.HeldUCD.nonempty_mulEquiv_heldGU
    ρE hρE B b hb
  have eG : heldGU r E τ hτ ≃* heldGU r E ρE hρE := by
    have h : (heldGU r E τ hτ : Subgroup (GL (Fin r) E)) = heldGU r E ρE hρE := by
      subst hτbar
      rfl
    exact MulEquiv.subgroupCongr h
  let φU : heldGU r E τ hτ ≃* sesqUnitaryGroup B := eG.trans eU.symm
  have hfind : Module.finrank E (Fin r → E) = r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  by_cases hsmall : Module.finrank E (Fin r → E) ≤ 1 ∨
      ¬ ((Module.finrank E (Fin r → E) = 2 → 4 ≤ 2 ^ n) ∧
        (Module.finrank E (Fin r → E) = 3 → 3 ≤ 2 ^ n))
  · right
    haveI : Group.IsSolvable ↥(sesqUnitaryGroup B) :=
      kitTame_isSolvable_sesqUnitaryGroup_of_small hE hB hBl hsmall
    exact Group.isSolvable_of_surjective (f := φU.symm.toMonoidHom) φU.symm.surjective
  · left
    have hnot1 : ¬ Module.finrank E (Fin r → E) ≤ 1 := fun h => hsmall (Or.inl h)
    have hq : (Module.finrank E (Fin r → E) = 2 → 4 ≤ 2 ^ n) ∧
        (Module.finrank E (Fin r → E) = 3 → 3 ≤ 2 ^ n) := by
      by_contra hc
      exact hsmall (Or.inr hc)
    rw [hfind] at hnot1
    have hm : 2 ≤ r := by omega
    have hqSL : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroup B) :=
      CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
        hE hB hBl (by rw [hfind]; exact hm) hq
    have hker : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitarySpecial (h := hE) B =
        (sesqSpecialUnitaryGroup B).subgroupOf (sesqUnitaryGroup B) := by
      ext δ
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_unitarySpecial (h := hE),
        Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup]
      exact ⟨fun h => ⟨δ.2, h⟩, fun h => h.2⟩
    have hle : ⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ ≤ sesqSpecialUnitaryGroup B := by
      rw [← Subgroup.map_subtype_commutator (sesqUnitaryGroup B)]
      refine Subgroup.map_le_iff_le_comap.2 ?_
      rw [Subgroup.comap_subtype, ← hker]
      exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.commutator_le_unitarySpecial (h := hE) B
    have hss_eq : (sesqSpecialUnitaryGroup B) =
        ⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ := by
      refine le_antisymm ?_ hle
      have hperf : ⁅(sesqSpecialUnitaryGroup B), (sesqSpecialUnitaryGroup B)⁆ =
          sesqSpecialUnitaryGroup B := Subgroup.isPerfect_iff.mp hqSL.1
      rw [← hperf]
      exact Subgroup.commutator_mono (sesqSpecialUnitaryGroup_le B) (sesqSpecialUnitaryGroup_le B)
    have hqU : CFSG.IsQuasisimple ↥⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hss_eq) hqSL
    have e2 : ↥(commutator (sesqUnitaryGroup B)) ≃*
        ↥⁅(sesqUnitaryGroup B), (sesqUnitaryGroup B)⁆ :=
      (Subgroup.equivMapOfInjective (commutator (sesqUnitaryGroup B))
        (sesqUnitaryGroup B).subtype Subtype.val_injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (sesqUnitaryGroup B)))
    have hqH : CFSG.IsQuasisimple ↥(commutator (sesqUnitaryGroup B)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e2.symm hqU
    have hmap : (commutator (heldGU r E τ hτ)).map φU.toMonoidHom =
        commutator (sesqUnitaryGroup B) :=
      kitTame_map_commutator_mulEquiv φU
    have eC : ↥(commutator (heldGU r E τ hτ)) ≃*
        ↥(commutator (sesqUnitaryGroup B)) :=
      (Subgroup.equivMapOfInjective (commutator (heldGU r E τ hτ)) φU φU.injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eC.symm hqH

theorem ggNbrLSideTame_gu {X : Type} [Group X] {A : Subgroup X} {r n : ℕ} {K E : Type} [Field K]
    [Finite K] [Field E] [Finite E] {τ : E ≃+* E} {hτ : ∀ y, τ (τ y) = y}
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hEc : Nat.card E = Nat.card K ^ 2)
    (hτQ : ∀ y, τ y = y ^ Nat.card K) (φ : ↥A ≃* heldGU r E τ hτ) :
    CFSG.IsQuasisimple ↥⁅A, A⁆ ∨ Group.IsSolvable ↥A := by
  exact CFSG.StandardType.GGNbrLSideKit.tame_of_mulEquiv φ
    (kitTame_group_heldGU hK hn hEc hτQ)

end CFSG.StandardType
