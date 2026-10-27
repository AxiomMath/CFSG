module

public import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBigHeart
public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeSixAbs
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeSixForm
import CFSG.LocalAnalysis.StandardType.GGWAutOrthOdd
import CFSG.LocalAnalysis.StandardType.GGWAutOrthCosets
import CFSG.LocalAnalysis.StandardType.GGWAutCommon

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin
open CFSG.ClassicalGroups.Orthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggQ2TN6_le (hK : GGReflClassOmegaInput) [Module.Finite (ZMod 3) V]
    (A 𝓜 : Subgroup (V ≃ₗ[ZMod 3] V)) (h𝓜A : 𝓜 ≤ A) (hTF : TransvectionFree A)
    (hdim : Module.finrank (ZMod 3) V = 5) (c : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3))
    (s : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hs𝓜 : ∀ i, s i ∈ 𝓜)
    (x : V) (hxH : x ∉ Submodule.span (ZMod 3) (Set.range c)) (hxfix : ∀ i, α i x = 0)
    (hΓ : ∀ g ∈ A, g x = x → g ∈ 𝓜) (t : V ≃ₗ[ZMod 3] V) (ht𝓜 : t ∈ 𝓜) (htR : IsReflLin t)
    (htx : t x ∉ Submodule.span (ZMod 3) {x}) : A ≤ 𝓜 := by
  classical
  have hαc : ∀ i, α i (c i) = 2 := by
    intro i
    rw [hpair i i]
    simp [CartanMatrix.A]
  have hsRefl : ∀ i, IsReflLin (s i) := by
    intro i
    refine ⟨c i, α i, hαc i, ?_⟩
    ext v
    rw [Module.reflection_apply, hs i v]
  set R₀ : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range s ∪ {t}) with hR₀def
  have hsR₀ : ∀ i, s i ∈ R₀ := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have htR₀ : t ∈ R₀ := Subgroup.subset_closure (Or.inr rfl)
  have hR₀𝓜 : R₀ ≤ 𝓜 := by
    rw [hR₀def, Subgroup.closure_le]
    rintro g (⟨i, rfl⟩ | rfl)
    · exact hs𝓜 i
    · exact ht𝓜
  have hR₀A : R₀ ≤ A := hR₀𝓜.trans h𝓜A
  have habs₀ : ZS.AbsIrred 3 R₀ :=
    ggQ2TN6_absIrred A hTF hdim c α hpair s hs (fun i => h𝓜A (hs𝓜 i)) x hxH hxfix t (h𝓜A ht𝓜)
      htR htx
  have hgen₀ : R₀ = Subgroup.closure {r | r ∈ R₀ ∧ GGLinRefl r} := by
    apply le_antisymm
    · rw [hR₀def, Subgroup.closure_le]
      rintro g (⟨i, rfl⟩ | rfl)
      · exact Subgroup.subset_closure ⟨hsR₀ i, (ggLinRefl_iff_isReflLin _).mpr (hsRefl i)⟩
      · exact Subgroup.subset_closure ⟨htR₀, (ggLinRefl_iff_isReflLin _).mpr htR⟩
    · exact (Subgroup.closure_le R₀).mpr fun r hr => hr.1
  set R : Subgroup (V ≃ₗ[ZMod 3] V) := reflGp A with hRdef
  have hRA : R ≤ A := ggWAut_reflGp_le A
  have hR₀R : R₀ ≤ R := by
    rw [hR₀def, Subgroup.closure_le]
    rintro g (⟨i, rfl⟩ | rfl)
    · exact Subgroup.subset_closure ⟨h𝓜A (hs𝓜 i), hsRefl i⟩
    · exact Subgroup.subset_closure ⟨h𝓜A ht𝓜, htR⟩
  have habs : ZS.AbsIrred 3 R := ggWAut_absIrred_of_le hR₀R habs₀
  have horth : ∀ R' : Subgroup (V ≃ₗ[ZMod 3] V), R' ≤ A → (∀ i, s i ∈ R') → ZS.AbsIrred 3 R' →
      R' = Subgroup.closure {r | r ∈ R' ∧ GGLinRefl r} → GGOrthType R' := by
    intro R' hR'A hsR' habs' hgen'
    rcases hK.2 V 5 hdim (by norm_num) (by norm_num) R' habs' hgen' with
      h1 | h2 | h3 | h4 | h5 | h6 | h7
    · exact (ggQ2TN6_not_imprimitive hdim c α hpair s hs R' hsR' habs' hgen' h1).elim
    · exact (ggWAut_SL_has_transvection (by omega) A (fun g hg => hR'A (h2.1 g hg)) hTF).elim
    · exact h3.1
    · exact absurd (by norm_num : 3 ∣ 5 + 1) h4.1
    · exact absurd h5.1 (by norm_num)
    · exact absurd h6.1 (by norm_num)
    · exact absurd h7.1 (by norm_num)
  obtain ⟨Q, hQ, hR₀Q, hcomm⟩ := horth R₀ hR₀A hsR₀ habs₀ hgen₀
  obtain ⟨Q', hQ', hRQ', -⟩ :=
    horth R hRA (fun i => hR₀R (hsR₀ i)) habs (ggWAut_reflGp_closure A)
  have hΩ : ggOmega Q ≤ R₀ := by
    rw [ggOmega, Subgroup.closure_le]
    rintro _ ⟨g, h, hg, hh, rfl⟩
    exact hcomm g h hg hh
  obtain ⟨κ, hκ, hQ'Q⟩ :=
    ggWAut_form_unique R₀ habs₀ Q Q' hQ hQ' hR₀Q (fun g hg => hRQ' g (hR₀R hg))
  have hRQ : ∀ g ∈ R, ZS.IsIsom 3 Q g := by
    intro g hg v
    have h := hRQ' g hg v
    rw [hQ'Q, hQ'Q] at h
    exact mul_left_cancel₀ hκ h
  have hAQ : ∀ a ∈ A, ZS.IsIsom 3 Q a := by
    intro a ha
    refine ggWAut_normalizer_isom_odd (by rw [hdim]; decide) R habs Q hQ hRQ a ?_
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · exact ggWAut_reflGp_conj A ha
    · intro hr
      have h := ggWAut_reflGp_conj A (inv_mem ha) hr
      rwa [show a⁻¹ * (a * r * a⁻¹) * a⁻¹⁻¹ = r by group] at h
  obtain ⟨hu, hw, hns, hux, hwx⟩ :=
    ggQ2TN6_form Q hQ c α hpair s hs (fun i => hR₀Q _ (hsR₀ i)) x hxfix
  intro a ha
  obtain ⟨ω, hω, hcases⟩ := ggWAut_orth_cosets_of_not_isSquare Q hQ hu hw hns a (hAQ a ha)
  have hω𝓜 : ω ∈ 𝓜 := hR₀𝓜 (hΩ hω)
  have key : ∀ r : V ≃ₗ[ZMod 3] V, a = ω * r → r x = x → a ∈ 𝓜 := by
    intro r har hrx
    have hrA : r ∈ A := by
      have hr : r = ω⁻¹ * a := by rw [har]; group
      rw [hr]
      exact mul_mem (inv_mem (h𝓜A hω𝓜)) ha
    rw [har]
    exact mul_mem hω𝓜 (hΓ r hrA hrx)
  rcases hcases with h | h | h | h
  · rw [h]
    exact hω𝓜
  · exact key _ h hux
  · exact key _ h hwx
  · refine key _ h ?_
    rw [LinearEquiv.mul_apply, hwx, hux]

end CFSG.StandardType

end
