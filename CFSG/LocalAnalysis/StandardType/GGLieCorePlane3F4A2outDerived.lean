module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
import CFSG.LocalAnalysis.StandardType.GGFamSLRecogDefs
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RawStability
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieF4A2out_derived
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hΓ : D.Γ = D.model)
    (hmodel : GGLieSU3Model ↥(rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f) :
    Group.IsSolvable ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ∨
      LieModel (↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ⧸
        Subgroup.center ↥(GGLieF4PlaneRat D ρ a₁ a₂ i)) .PSU 3 2 f := by
  classical
  let Ψ : Set (Fin Tag.F4.rank → ℤ) := componentRoots (jointChar a₁ a₂) i
  let S : Subgroup (ModGL Tag.F4 L) := rootSpan Tag.F4 L Ψ ⊓ D.model
  have hmodelS : GGLieSU3Model ↥S f := hmodel
  have hrat : ratOrbit (fun u => ρ u) (componentRoots (jointChar a₁ a₂) i) =
      componentRoots (jointChar a₁ a₂) i :=
    CFSG.StandardType.F4ExplicitPos.RawStability.ratOrbit_eq_of_image_eq
      (ρ := fun u => ρ u) hρΨ
  have hR : GGLieF4PlaneRat D ρ a₁ a₂ i = ⁅S, S⁆ := by
    unfold GGLieF4PlaneRat ratComp
    rw [hΓ, hrat]
  rcases eq_or_lt_of_le hf with hf1 | hf2
  ·
    subst f
    have hle : GGLieF4PlaneRat D ρ a₁ a₂ i ≤ S := by
      rw [hR]; exact Subgroup.commutator_le_self S
    have hsolS : Group.IsSolvable ↥S := by
      obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hmodelS
      let : Field K := hKfield
      let : Finite K := hKfin
      have : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) :=
        CFSG.Quasithin.isSolvable_statedSU_one (F := K) hKcard
      exact Group.isSolvable_of_surjective
        (f := (e.symm : ↥(CFSG.Open.StatedSU 3 (2 ^ 1) K) →* ↥S)) e.symm.surjective
    have : Group.IsSolvable ↥S := hsolS
    exact Or.inl (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle))
  ·
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hmodelS
    let : Field K := hKfield
    let : Finite K := hKfin
    let : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = (2 ^ f) ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hKcard
    have h32 : (3, 2 ^ f) ≠ (3, 2) := by
      intro hcon
      have h2 : 2 ^ f = 2 := (Prod.mk.injEq 3 (2 ^ f) 3 2).mp hcon |>.2
      have hle : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [h2] at hle
      norm_num at hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hqs : CFSG.IsQuasisimple ↥(CFSG.Open.StatedSU 3 (2 ^ f) K) :=
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
        (F := K) (p := 2) (f := f) hKcard (by norm_num) h32).1
    have hqsS : CFSG.IsQuasisimple ↥S := CFSG.IsQuasisimple.of_mulEquiv e hqs
    have hcomm : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp hqsS.1
    have hRS : GGLieF4PlaneRat D ρ a₁ a₂ i = S := by rw [hR, hcomm]
    refine Or.inr ?_
    rw [hRS]
    exact CFSG.StandardType.TableCRes.lieModel_of_suCover (X := S) (K := K) (ν := 3)
      hf hKcard (by norm_num) h32 e.symm e.symm.surjective (by
        rw [(MonoidHom.ker_eq_bot_iff _).mpr e.symm.injective]; exact bot_le)

end CFSG.StandardType.LieCore
