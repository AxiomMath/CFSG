module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

theorem ggLieF4_gamma_eq_model
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum Tag.F4 L)
    (hfin : Finite D.model) (hq : ∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) :
    D.Γ = D.model := by
  obtain ⟨f, hf1, hqf⟩ := hq
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.F4 L D
  obtain ⟨S, hSD, _hSρ⟩ := exists_langSetup_of_datum D ρ hρ hfin hf1 hqf
  obtain ⟨Fr, hFr, hΦ⟩ := S.exists_frobenius_of_steinberg (by decide) (by decide)
  obtain ⟨K, hKf, hKfin, hKa, hKq⟩ := S.exists_fixedField
  let : Field K := hKf
  let : Finite K := hKfin
  let : Algebra K L := hKa
  have hbij : Function.Bijective Fr := S.frobenius_bijective hFr
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hKq]; exact hFr c
  have hfix : S.D.fix = (adjointGroup Tag.F4 K).map (baseChangeGL (algebraMap K L)) := by
    change adjointGroup Tag.F4 L ⊓ S.D.Φ.eqLocus (MonoidHom.id _) = _
    rw [hΦ]
    exact CFSG.RankThree.Chevalley.frobenius_fixed_eq_map_of_bijective (k := K) (M := L)
      (Or.inr rfl) Fr hFrK hbij
  have hperfFix : ⁅S.D.fix, S.D.fix⁆ = S.D.fix := by
    rw [hfix, ← Subgroup.map_commutator,
      commutator_self_eq_of_commutator_top
        (CFSG.HardMathSupport.Timmesfeld.CrossChar.commutator_adjointGroup_F4_eq_top K)]
  have hmain : S.D.Γ = S.D.model := by
    have hmodel : S.D.model = S.D.fix.map (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
      LangDescent.model_eq S.D
    rw [LangDatum.Γ, hmodel, ← Subgroup.map_commutator, hperfFix, ← hmodel]
  simpa [hSD] using hmain

end CFSG.StandardType.LieCore
