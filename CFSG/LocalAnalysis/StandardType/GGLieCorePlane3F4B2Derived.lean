module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddKernelOrbit
import CFSG.LieType.Universal.Symplectic
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2SmallJ
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieF4B2_derived
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hΓ : D.Γ = D.model)
    (hmodel : GGLieSp4Model ↥(rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f) :
    (f = 1 ∧ Nat.card (↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ⧸
        Subgroup.center ↥(GGLieF4PlaneRat D ρ a₁ a₂ i)) = 360) ∨
      LieModel (↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ⧸
        Subgroup.center ↥(GGLieF4PlaneRat D ρ a₁ a₂ i)) .PSp 2 2 f := by
  classical
  let S : Subgroup (ModGL Tag.F4 L) :=
    rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model
  have hratOrbit : ratOrbit (fun u => ρ u)
      (componentRoots (jointChar a₁ a₂) i) = componentRoots (jointChar a₁ a₂) i :=
    CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.ratOrbit_eq_of_image_eq
      (ρ := fun u => ρ u) hρΨ
  have hRcomm : GGLieF4PlaneRat D ρ a₁ a₂ i = ⁅S, S⁆ := by
    change GGLieF4PlaneRat D ρ a₁ a₂ i =
      ⁅rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model,
       rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model⁆
    simp only [GGLieF4PlaneRat, ratComp, hratOrbit, hΓ]
  have hcommS : ⁅S, S⁆ = (commutator ↥S).map S.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : Field K := hK
  let : Finite K := hfin
  change ↥S ≃* ↥(CFSG.Open.StatedSp 2 K) at e
  by_cases hf1 : f = 1
  · left
    have hk : Nat.card K = 2 := by rw [hcard, hf1]; norm_num
    have hAlt : ↥(commutator ↥S) ≃* alternatingGroup (Fin 6) :=
      (MulEquiv.subgroupCongr (commutator_def ↥S)).trans
        (CFSG.StandardType.F4ExplicitPos.B2SmallJ.derivedRangeEquivAlt6
          (X := ↥S) (k := K) hk (κ := e.symm.toMonoidHom) (N := ⊤)
          e.symm.injective (MonoidHom.range_eq_top.mpr e.symm.surjective))
    have hRAlt : ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ≃* alternatingGroup (Fin 6) :=
      (MulEquiv.subgroupCongr hRcomm).trans
        (((MulEquiv.subgroupCongr hcommS).trans
          (Subgroup.equivMapOfInjective (commutator ↥S) S.subtype
            S.subtype_injective).symm).trans hAlt)
    have hZAlt : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ := by
      have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      have hcardAlt : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]; decide
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (alternatingGroup (Fin 6))) with h | h
      · exact h
      · exfalso
        have hcomm : ∀ a b : alternatingGroup (Fin 6), a * b = b * a := fun a b =>
          (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
        let : CommGroup (alternatingGroup (Fin 6)) :=
          { (inferInstance : Group (alternatingGroup (Fin 6))) with mul_comm := hcomm }
        have hp := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 6))
        rw [hcardAlt] at hp
        exact (by norm_num : ¬ (360 : ℕ).Prime) hp
    refine ⟨hf1, ?_⟩
    have eQuot : ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ⧸
          Subgroup.center ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ≃*
        alternatingGroup (Fin 6) ⧸ Subgroup.center (alternatingGroup (Fin 6)) :=
      QuotientGroup.congr _ _ hRAlt (Subgroup.map_center_eq hRAlt)
    have h1 : Nat.card (↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ⧸
          Subgroup.center ↥(GGLieF4PlaneRat D ρ a₁ a₂ i)) =
        Nat.card (alternatingGroup (Fin 6) ⧸
          Subgroup.center (alternatingGroup (Fin 6))) :=
      Nat.card_congr eQuot.toEquiv
    rw [h1, hZAlt]
    exact (Nat.card_congr
      (QuotientGroup.quotientBot (G := alternatingGroup (Fin 6))).toEquiv).trans
      (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide)
  · right
    have h2f : 2 ≤ f := by omega
    have hpow : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2f
    have h4 : 4 ≤ Nat.card K := by rw [hcard]; simpa using hpow
    have hqs := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num)
      (Or.inl (Or.inr h4))
    have : Group.IsPerfect ↥(CFSG.Open.StatedSp 2 K) := hqs.1
    have hperfS : Group.IsPerfect ↥S :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hSeq : ⁅S, S⁆ = S := (Subgroup.isPerfect_iff (H := S)).mp hperfS
    have hRS : GGLieF4PlaneRat D ρ a₁ a₂ i = S := hRcomm.trans hSeq
    have hadm : CFSG.Open.StatedLieAdmissible .PSp 2 2 f := by
      refine ⟨Nat.prime_two, hf, le_rfl, ?_⟩
      intro hEq
      have hne : (2 : ℕ) ^ f ≠ 2 := by
        intro h
        have h42 : (4 : ℕ) ≤ 2 := by
          rw [h] at hpow
          exact hpow
        omega
      exact hne (congrArg Prod.snd hEq)
    have hclass : CFSG.Open.StatedClassicalModel
        (↥(CFSG.Open.StatedSp 2 K) ⧸
          Subgroup.center ↥(CFSG.Open.StatedSp 2 K)) .PSp 2 2 f :=
      CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient
        (n := 2) (F := K) hadm hcard
    have hLie : LieModel
        (↥(CFSG.Open.StatedSp 2 K) ⧸
          Subgroup.center ↥(CFSG.Open.StatedSp 2 K)) .PSp 2 2 f :=
      Or.inl ⟨by decide, hclass⟩
    have hLieS : LieModel (↥S ⧸ Subgroup.center ↥S) .PSp 2 2 f :=
      LieModel.quotient_center_of_mulEquiv e.symm hLie
    rw [hRS]
    exact hLieS

end CFSG.StandardType.LieCore
