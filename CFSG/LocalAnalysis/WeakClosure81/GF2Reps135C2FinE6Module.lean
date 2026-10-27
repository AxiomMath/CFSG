module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NoIrrFF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Hat
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcE
public import CFSG.Open.StatedDefs
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutModel
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Tr2
public import CFSG.Quasithin.Background.SmithB42L2L32
public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB51LnRealB
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley CFSG.Quasithin.SmithCurtis CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

theorem nonempty_ringHom_of_card_two {K k : Type} [Field K] [Finite K] [Field k] [CharP k 2]
    (hK : Nat.card K = 2) : Nonempty (K →+* k) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  exact ⟨(ZMod.castHom (dvd_refl 2) k).comp (FiniteField.ringEquivOfCardEq hc).toRingHom⟩


theorem exists_adjointEquiv_of_lieModel {G : Type} [Group G] (h : LieModel G .E6 0 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ∧
      Nonempty (G ≃* ↥(adjointGroup .E6 K)) := by
  have hm := (h.chevalleyExceptionalModel (by decide)).2
  obtain ⟨K, hKf, hKfin, hcard, ⟨e0⟩⟩ := hm
  have hc : Nat.card K = 2 := by simpa using hcard
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 1) le_rfl (by simpa using hc)
  exact ⟨K, hKf, hKfin, inferInstance, hc,
    ⟨e0.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E6 K)⟩⟩

theorem exists_hatData_of_adjointEquiv {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (eS : L ⧸ Subgroup.center L ≃* ↥(adjointGroup .E6 K)) :
    ∃ D : HatData K L, ∀ x : L, D.f x = eS (QuotientGroup.mk x) := by
  classical
  have hK2 : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hGfin : Finite ↥(e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  let f : L →* ↥(adjointGroup .E6 K) :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hf : Function.Surjective f := eS.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker ≤ Subgroup.center L := by
    intro x hx
    have h0 : eS (QuotientGroup.mk x) = 1 := hx
    have h1 : (QuotientGroup.mk x : L ⧸ Subgroup.center L) = 1 :=
      eS.injective (h0.trans (map_one eS).symm)
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hperf' : commutator L = ⊤ := Group.isPerfect_def.1 hperf
  obtain ⟨π, hπs, hπf⟩ := exists_hat (Isogeny.e6IsogenyT K) f hf hfk hperf'
    (fun E' _ _ p hp hc =>
      CFSG.StandardType.LayerCycExc.e6_minGroup_exists_section hK2 E' p hp hc)
    (Isogeny.e6IsogenyT_surjective (k := K))
  exact ⟨⟨f, hf, hfk, hperf', π, hπs, hπf⟩, fun _ => rfl⟩

@[expose] def IsE6TwentySevenType {K : Type} [Field K] [Finite K] [CharP K 2] {k : Type} [Field k]
    [Algebra K k] {m : ℕ} (ρ : Representation k ↥(e6Data_valid.minGroup K) (Fin m → k)) : Prop :=
  ∃ (y : Fin m → k) (χ : ↥(e6Data_valid.minGroup K) → k) (s : N6),
    (s = ⟨0, by decide⟩ ∨ s = ⟨5, by decide⟩) ∧
      IsCoverType (e6CoverRankOne K) ρ y χ (Finset.univ.erase s) ∧
      ∀ (i : N6) (u : Kˣ),
        χ (e6Data_valid.hm K i u) = if i = s then algebraMap K k (u : K) else 1

theorem isE6TwentySevenType_of_isSimpleRep {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k] {m : ℕ}
    (ρ : Representation k ↥(e6Data_valid.minGroup K) (Fin m → k)) (hρ : IsSimpleRep ρ)
    (hnt : ∃ (x : ↥(e6Data_valid.minGroup K)) (v : Fin m → k), ρ x v ≠ v) (hm : m ≤ 27) :
    m = 27 ∧ IsE6TwentySevenType ρ := by
  classical
  have hK2 : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  obtain ⟨y, χ, J, ht⟩ := e6_exists_isCoverType hρ
  have hper : ∀ (i : N6) (u : Kˣ),
      χ (e6Data_valid.hm K i u) ^ (2 ^ 1) = χ (e6Data_valid.hm K i u) :=
    fun i u => chi_hm_pow_card hρ ht hK2 i u
  have hTB : E6TypeBound K 1 := e6_typeBound (K := K) (n := 1) le_rfl hK2
  obtain ⟨hb1, -⟩ := hTB k m ρ y χ J 1 hρ hnt ht le_rfl (dvd_refl 1) hper
  rcases hb1 (by norm_num) with ⟨s, b, hs, hb, hJ, hχ⟩ | h79
  · rcases hs with h0 | h5 | h1
    · have hm27 : m = 27 :=
        (e6Surv27_holds K 1 le_rfl hK2 k m ρ y χ J s b hρ ht (Or.inl h0) hb hJ hχ).1
      obtain rfl : b = 0 := by omega
      simp only [pow_zero, pow_one] at hχ
      exact ⟨hm27, y, χ, s, Or.inl h0, hJ ▸ ht, hχ⟩
    · have hm27 : m = 27 :=
        (e6Surv27_holds K 1 le_rfl hK2 k m ρ y χ J s b hρ ht (Or.inr h5) hb hJ hχ).1
      obtain rfl : b = 0 := by omega
      simp only [pow_zero, pow_one] at hχ
      exact ⟨hm27, y, χ, s, Or.inr h5, hJ ▸ ht, hχ⟩
    · subst h1
      exact absurd (e6Surv78_holds K 1 le_rfl hK2 k m ρ y χ J b hρ ht hb hJ hχ).1 (by omega)
  · omega

end CFSG.LocalAnalysis.WeakClosure81
