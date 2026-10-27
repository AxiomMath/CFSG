module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Frame
public import CFSG.LocalAnalysis.StandardType.GGSelectedRootMatch
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameWittType
import CFSG.ClassicalInvolution.Models.OrthogonalPairs.FrameFieldEquiv
import CFSG.LieType.Universal.SpinOmega.RootPosition
import CFSG.LocalAnalysis.StandardType.GGSelectedPOmegaMinusLongField
import CFSG.LocalAnalysis.StandardType.GGRankOneTagsA
import CFSG.Adapters.LinearFieldTransport
import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinPlus
import CFSG.ClassicalInvolution.ModelFacts.MF15Basic
import CFSG.ClassicalInvolution.ModelFacts.MF15Lin
import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv

public noncomputable section

open Module QuadraticMap Subgroup

namespace CFSG.StandardType.OrthTorus

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
open CFSG.ClassicalGroups.Orthogonal
open CFSG.GroupTheory.WeirSylow
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.CurtisTits
open CFSG.Assembly.LowTwoRank


theorem OrthWeakFrame.exists_nativeSpin_selected_at_pair
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L : Subgroup G} (Φ : OrthWeakFrame p Bs L)
    (i j : Fin Φ.r) (hij : i ≠ j) :
    ∃ (t : StatedLieTag) (lambda : (ggU t Φ.r Φ.f).K →* G),
      (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedLieAdmissible t Φ.r 2 Φ.f ∧ 2 ≤ (ggU t Φ.r Φ.f).D.rank ∧
      lambda.ker ≤ Subgroup.center (ggU t Φ.r Φ.f).K ∧ lambda.range = L ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
        (delta : Fin (ggU t Φ.r Φ.f).D.rank → ℤ)
        (model : SelectedRoot.SelectedSL2Model (ggU t Φ.r Φ.f).D k delta),
        (lambda.comp model.phi).range =
          ((Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q)).map Φ.ψ := by
  classical
  have hr := Φ.hr
  have hf := Φ.hf
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _hspan, hF⟩ := Φ.exists_rankOne_frame hp2 i j hij
  let K := GaloisField 2 Φ.f
  let e : K ≃+* Φ.F :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField Φ.F 2 Φ.f (by omega) Φ.hcard).symm
  let : Finite Φ.V := Module.finite_of_finite Φ.F
  let : Module K Φ.V := Module.compHom Φ.V e.toRingHom
  let : FiniteDimensional K Φ.V := Module.Finite.of_finite
  have hsmul : ∀ (c : K) (v : Φ.V), c • v = e c • v := fun _ _ => rfl
  let Q₀ := formOfRingEquiv e hsmul Φ.Q
  let F₀ := fieldFrame e hsmul F
  let E : ↥(orthDerived Q₀) ≃* ↥(orthDerived Φ.Q) := derivedFieldEquiv e hsmul Φ.Q
  have hQ₀ : (polarBilin Q₀).Nondegenerate :=
    nondegenerate_formOfRingEquiv (Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix)
  have hdim : finrank K Φ.V = 2 * Φ.r :=
    (finrank_eq_of_finiteFields_ringEquiv e).trans
      (Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix)
  have hwitt : IsPlusType Q₀ ↔ IsPlusType Φ.Q := by
    exact isPlusType_formOfRingEquiv e hsmul Φ.Q
  have hfield : (F₀.La.range.subgroupOf (orthDerived Q₀)).map E.toMonoidHom =
      (Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q) := by
    rw [fieldFrame_La_subgroupOf_map, hF]
  rcases Φ.wittType with ⟨hplus, _heven⟩ | ⟨hminus, _hodd⟩
  · have hn3 : 3 ≤ Φ.r := by omega
    obtain ⟨mu, hmu⟩ := exists_spinPlus_root_position Φ.hr hQ₀ hdim (hwitt.mpr hplus) F₀
    let N := mu.trans E
    let lambda := Φ.ψ.comp N.toMonoidHom
    have hker : lambda.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff lambda).mpr (Φ.hinj.comp N.injective)
    have hrange : lambda.range = L := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr N.surjective,
        Subgroup.map_top, Φ.hrange]
    let a : Fin Φ.r := ⟨0, by omega⟩
    have hpos : (rankOne (plusDatum Φ.r K hn3).rootGroup a).map lambda =
        ((Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q)).map Φ.ψ := by
      change (rankOne (plusDatum Φ.r K hn3).rootGroup a).map
        (Φ.ψ.comp (E.toMonoidHom.comp mu.toMonoidHom)) = _
      rw [← Subgroup.map_map, ← Subgroup.map_map, hmu, hfield]
    have hadm : StatedLieAdmissible .POmegaPlus Φ.r 2 Φ.f :=
      ⟨Nat.prime_two, by omega, Φ.hr⟩
    have hU := ggU_pOmegaPlus (f := Φ.f) hn3
    have hM := ggRankOneModel_POmegaPlus hadm (by simpa [bnRank] using hn3)
    rw [hU] at hM
    obtain ⟨model, hmodel⟩ := SelectedRoot.exists_model_of_rankOneModel hM a
    refine ⟨.POmegaPlus, ?_⟩
    rw [hU]
    refine ⟨lambda, Or.inl rfl, hadm, ?_, hker ▸ bot_le, hrange,
      K, inferInstance, inferInstance, inferInstance, Pi.single a 1, model, ?_⟩
    · change 2 ≤ Φ.r
      omega
    · rw [MonoidHom.range_comp, hmodel, hpos]
  · have hirr := minusCoeffs_irr 2 Φ.f
    obtain ⟨mu, hmu⟩ := exists_spinMinus_root_position Φ.hr hirr hQ₀ hdim
      (fun h => hminus (hwitt.mp h)) F₀
    let N := mu.trans E
    let lambda := Φ.ψ.comp N.toMonoidHom
    have hker : lambda.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff lambda).mpr (Φ.hinj.comp N.injective)
    have hrange : lambda.range = L := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr N.surjective,
        Subgroup.map_top, Φ.hrange]
    let a : Fin (Φ.r - 1) := ⟨0, by omega⟩
    have ha : a.val + 1 < Φ.r - 1 := by dsimp [a]; omega
    have hpos : (rankOne (minusDatum Φ.r hirr).rootGroup a).map lambda =
        ((Φ.Δ.rankOne i j).subgroupOf (orthDerived Φ.Q)).map Φ.ψ := by
      change (rankOne (minusDatum Φ.r hirr).rootGroup a).map
        (Φ.ψ.comp (E.toMonoidHom.comp mu.toMonoidHom)) = _
      rw [← Subgroup.map_map, ← Subgroup.map_map, hmu, hfield]
    obtain ⟨model, hmodel, _hlower⟩ :=
      SelectedRoot.exists_selectedSL2Model_minusDatum_long_range Φ.hr hirr ha
    have hU : ggU .POmegaMinus Φ.r Φ.f =
        ⟨spinGroup (quadMinus Φ.r K (minusCoeffs 2 Φ.f).1 (minusCoeffs 2 Φ.f).2),
          minusDatum Φ.r hirr⟩ := rfl
    refine ⟨.POmegaMinus, ?_⟩
    rw [hU]
    refine ⟨lambda, Or.inr rfl, ⟨Nat.prime_two, by omega, Φ.hr⟩, ?_,
      hker ▸ bot_le, hrange, K, inferInstance, inferInstance, inferInstance,
      Pi.single a 1, model, ?_⟩
    · change 2 ≤ Φ.r - 1
      omega
    · rw [MonoidHom.range_comp, hmodel, hpos]

theorem OrthWeakFrame.exists_nativeSpin_selected_pair
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L : Subgroup G} (Φ : OrthWeakFrame p Bs L) :
    ∃ (t : StatedLieTag) (lambda : (ggU t Φ.r Φ.f).K →* G),
      (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedLieAdmissible t Φ.r 2 Φ.f ∧ 2 ≤ (ggU t Φ.r Φ.f).D.rank ∧
      lambda.ker ≤ Subgroup.center (ggU t Φ.r Φ.f).K ∧ lambda.range = L ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
        (delta : Fin (ggU t Φ.r Φ.f).D.rank → ℤ)
        (model : SelectedRoot.SelectedSL2Model (ggU t Φ.r Φ.f).D k delta),
        (lambda.comp model.phi).range =
          ((Φ.Δ.rankOne (⟨0, by have := Φ.hr; omega⟩ : Fin Φ.r)
            (⟨1, by have := Φ.hr; omega⟩ : Fin Φ.r)).subgroupOf
              (orthDerived Φ.Q)).map Φ.ψ := by
  have hr := Φ.hr
  exact Φ.exists_nativeSpin_selected_at_pair hp2
    (⟨0, by omega⟩ : Fin Φ.r) (⟨1, by omega⟩ : Fin Φ.r)
    (by intro h; exact Nat.zero_ne_one (congrArg Fin.val h))

end CFSG.StandardType.OrthTorus

end
