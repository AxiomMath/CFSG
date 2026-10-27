module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1KGField
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1Labels
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinCont
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinComp
import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
import CFSG.LocalAnalysis.StandardType.KGLangTorAFields
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem kgFieldCompContLinAux_recipe {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    {l n : ℕ} (h6 : (p = 3 ∧ (l = 2 ∨ l = 5)) ∨ (p = 5 ∧ l = 4))
    (hn : 1 ≤ n) (hpn : p ∣ n)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) :
    KGFieldCompCont p ⟨.A, l, n⟩
      (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) F))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) F)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (l + 1)) F))) := by
  classical
  have hl : 2 ≤ l := by rcases h6 with ⟨-, h | h⟩ | ⟨-, h⟩ <;> omega
  let d : ℕ := l + 1
  let R : Type := LargeEvenProj (LargeEvenSLGroup (Fin d) F)
  let I : Set (MulAut R) :=
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ
  let Fd : Set (MulAut R) :=
    LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F))
  have hd : 3 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  change KGFieldCompCont p ⟨.A, l, n⟩ R I Fd
  intro φ hφ hφI hφp J₀ hJ₀
  obtain ⟨u, hu, f, hf, hφeq⟩ := hφ
  have hφIp : (u * f) ^ p = 1 := by rw [← hφeq]; exact hφp
  have hφIf : u * f ∉ I := by rw [← hφeq]; exact hφI
  have hsimple : IsSimpleGroup R := LinearFieldFix.isSimpleGroup_proj hd F
  have hna : ∃ a b : R, a * b ≠ b * a := LinearFieldFix.exists_noncomm_proj hd F
  have hFC : GGRawFieldConj p R I Fd :=
    RecipeFieldLang.ggRawFieldConj_linear (d := d) (K := F) hd2 (Or.inl hd) hp
  obtain ⟨f', hf'F, u', hu'I, hord', heq⟩ := hFC hsimple hna u hu f hf hφIf hφIp
  have hφu' : φ = u' * f' * u'⁻¹ := hφeq.trans heq
  let E : MulAut R ≃* MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d F) :=
    MulAut.congr (TypeA.recipeEquiv d F)
  obtain ⟨σ, hσE⟩ := RecipeFieldLinear.congr_field_eq hf'F
  have hfield_inj : Function.Injective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut d F) := by
    intro a b hab
    have hab' : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut d F (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d F (1 : GL (Fin d) F) *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut d F (a * b⁻¹) = 1 := by
      rw [hab', mul_one, map_one]
    obtain ⟨h, -⟩ := RecipeFieldLinear.eq_one_of_conjAut_mul_fieldAut_eq_one' (n := d)
      (by omega) (Or.inl hd) 1 (a * b⁻¹) h1
    exact mul_inv_eq_one.mp h
  have hσord : orderOf σ = p := by
    have h1 : orderOf σ = orderOf f' := by
      rw [← orderOf_injective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut d F) hfield_inj σ, ← hσE]
      exact orderOf_injective E.toMonoidHom (MulEquiv.injective E) f'
    rw [h1, hord']
  let κ₀ : Matrix.SpecialLinearGroup (Fin d) F →* R :=
    (TypeA.recipeEquiv d F).symm.toMonoidHom.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d F)
  have hκ₀surj : Function.Surjective κ₀ :=
    (TypeA.recipeEquiv d F).symm.surjective.comp (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective d F)
  have hκ₀ker : κ₀.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have hproj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d F h = 1 := by
      have := congrArg (TypeA.recipeEquiv d F) hh
      simpa [κ₀] using this
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
    exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff).mp hproj
  have hf'_act : ∀ h, f' (κ₀ h) = κ₀ (Matrix.SpecialLinearGroup.map σ.toRingHom h) := by
    intro h
    apply (TypeA.recipeEquiv d F).injective
    have h1 := congrArg (fun g : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d F) =>
      g (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj d F h)) hσE
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_proj] at h1
    simpa [κ₀, MulAut.congr_apply] using h1
  let κ'' : Matrix.SpecialLinearGroup (Fin d) F →* R := u'.toMonoidHom.comp κ₀
  have hκ''_apply : ∀ h, κ'' h = u' (κ₀ h) := fun h => rfl
  have hκ''surj : Function.Surjective κ'' :=
    (MulEquiv.surjective u').comp hκ₀surj
  have hκ''ker : κ''.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    intro h hh
    apply hκ₀ker
    rw [MonoidHom.mem_ker] at hh ⊢
    have hh' : u' (κ₀ h) = 1 := by
      rw [← hκ''_apply h]
      exact hh
    exact MulEquiv.injective u' (by rw [hh', map_one])
  have hξ'' : ∀ h, φ (κ'' h) = κ'' (Matrix.SpecialLinearGroup.map σ.toRingHom h) := by
    intro h
    rw [hφu', hκ''_apply h, hκ''_apply (Matrix.SpecialLinearGroup.map σ.toRingHom h)]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, hf'_act h]
  have hfix_eq : ggFixSub φ = MonoidHom.eqLocus (φ : R →* R) (MonoidHom.id R) := by
    ext x
    rw [mem_ggFixSub]
    change φ x = x ↔ x ∈ MonoidHom.eqLocusM (φ : R →* R) (MonoidHom.id R)
    rw [MonoidHom.mem_eqLocusM]
    rfl
  have hJ₀' : IsComponentOf J₀ (ggFixSub φ) := by
    rw [hfix_eq]
    exact hJ₀
  obtain ⟨ρ, -⟩ := kgLangS1A_lin_component (d := d) (F := F) (σ := σ) (K := R)
    hd κ'' hκ''surj hκ''ker hξ'' hJ₀'
  have hF₀card : Nat.card (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ) = 2 ^ (n / p) :=
    (kgLangTorA_card_fixed_linear (F := F) (n := n) (p := p) hn hF hσord).2
  refine ⟨⟨.A, l, n / p⟩, ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
  · dsimp only [LargeEvenInLambda2]
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
    · omega
    · intro h1; omega
  · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
    exact ⟨CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ, inferInstance, inferInstance, hF₀card,
      ⟨ρ.trans (TypeA.recipeEquiv d (CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ)).symm⟩⟩
  · exact Nat.div_mul_cancel hpn

theorem kgFieldCompCont_lin {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : GGNbrLangS1LinLabel p lab) :
    LargeEvenLabelAll lab (KGFieldCompCont p lab) := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hsix, -, hpn, htag⟩ := hS
  dsimp only at htag
  subst htag
  have hn : 1 ≤ n := hlab.1
  have h6 : (p = 3 ∧ (l = 2 ∨ l = 5)) ∨ (p = 5 ∧ l = 4) := hsix.2
  dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
  exact NbrGraphLinear.recipeLinear_all (d := l + 1) (N := 2 ^ n)
    (Q := KGFieldCompCont p ⟨.A, l, n⟩) (Q₀ := Q)
    (fun F _ _ hF => kgFieldCompContLinAux_recipe hp hp2 h6 hn hpn F hF) hQ

end CFSG.StandardType
