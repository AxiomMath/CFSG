module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedLiteralPart2
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcPin

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.F4ExplicitPos.JointShapes
open CFSG.StandardType.F4ExplicitPos.SelectedLiteral

private lemma l10lF2_compRank_le_ncard (Ψ : Set (Fin Tag.F4.rank → ℤ)) (hΨ : Ψ.Finite) :
    compRank Ψ ≤ Ψ.ncard := by
  set s : Set (Fin Tag.F4.rank → ℚ) :=
    (fun γ (i : Fin Tag.F4.rank) => (γ i : ℚ)) '' Ψ with hs
  have hfin : s.Finite := hΨ.image _
  have : Fintype ↥s := hfin.fintype
  have hle := finrank_span_le_card (R := ℚ) s
  rw [Set.toFinset_card, ← Nat.card_eq_fintype_card] at hle
  calc compRank Ψ = Module.finrank ℚ (Submodule.span ℚ s) := rfl
    _ ≤ s.ncard := hle
    _ ≤ Ψ.ncard := Set.ncard_image_le hΨ

private lemma l10lF2_compRank_pair_le (j : Fin Tag.F4.rank) :
    compRank ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)) ≤ 2 := by
  have hfin : ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  have hcard : ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)).ncard ≤ 2 := by
    have h := Set.ncard_insert_le (Pi.single j 1)
      ({-Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))
    rw [Set.ncard_singleton] at h
    omega
  exact (l10lF2_compRank_le_ncard _ hfin).trans hcard

private lemma l10lF2_compRank_parabolicRoots_of_two
    {J : Set (Fin Tag.F4.rank)} {C : Finset (Option (Fin Tag.F4.rank))}
    (hnone : none ∉ C) (hCJ : ∀ j, some j ∈ C ↔ j ∈ J) (hcard : C.card = 2) :
    compRank (parabolicRoots Tag.F4 J) = 2 := by
  have hroots := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootsOf_eq_parabolicRoots_narrow
    CFSG.HardMathSupport.Timmesfeld.CrossChar.kacF4
    CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_F4 hnone hCJ
  calc compRank (parabolicRoots Tag.F4 J)
      = compRank (CFSG.HardMathSupport.Timmesfeld.CrossChar.kacF4.rootsOf
          (C : Set (Option (Fin Tag.F4.rank)))) := by rw [← hroots]
    _ = C.card := CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank_rootsOf
        CFSG.HardMathSupport.Timmesfeld.CrossChar.kacF4
        CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_F4 ⟨none, hnone⟩
    _ = 2 := hcard

private lemma l10lF2_compRank_f4LongSupport :
    compRank (parabolicRoots Tag.F4 CFSG.RankThree.PartOne.KF4.f4LongSupport) = 2 := by
  refine l10lF2_compRank_parabolicRoots_of_two
    (C := ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank)))) ?_ ?_ ?_
  · decide
  · intro j
    rw [CFSG.RankThree.PartOne.KF4.mem_f4LongSupport]
    revert j
    decide
  · decide

private lemma l10lF2_compRank_f4ShortSupport :
    compRank (parabolicRoots Tag.F4 CFSG.RankThree.PartOne.KF4.f4ShortSupport) = 2 := by
  refine l10lF2_compRank_parabolicRoots_of_two
    (C := ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank)))) ?_ ?_ ?_
  · decide
  · intro j
    rw [CFSG.RankThree.PartOne.KF4.mem_f4ShortSupport]
    revert j
    decide
  · decide

private lemma l10lF2_compRank_b2LeviRoots :
    compRank CFSG.SeitzReduction.F4Pilot.b2LeviRoots = 2 := by
  rw [CFSG.SeitzReduction.F4Pilot.b2LeviRoots]
  refine l10lF2_compRank_parabolicRoots_of_two
    (C := ({some 1, some 2} : Finset (Option (Fin Tag.F4.rank)))) ?_ ?_ ?_
  · decide
  · intro j
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_nodesTU]
    revert j
    decide
  · decide

private lemma l10lF2_false_of_levi_shape
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    (i : KernelComponent (jointChar a₁ a₂))
    (w : WeylGroup Tag.F4) (J : Set (Fin Tag.F4.rank)) (j₀ : Fin Tag.F4.rank)
    (hj₀ : ∀ j, j ≠ j₀ → j ∈ J)
    (hΨ : componentRoots (jointChar a₁ a₂) i =
      (fun α => w • α) '' parabolicRoots Tag.F4 J) :
    False := by
  have hker : ∀ j, j ≠ j₀ →
      rootChar a₁ (w • Pi.single j 1) = 1 ∧ rootChar a₂ (w • Pi.single j 1) = 1 := by
    intro j hj
    have hmem : w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) ∈
        componentRoots (jointChar a₁ a₂) i := by
      rw [hΨ]
      exact ⟨Pi.single j 1, single_mem_parabolicRoots (hj₀ j hj), rfl⟩
    obtain ⟨hk, -⟩ := hmem
    have hchar := hk.2
    rw [jointChar, MonoidHom.prod_apply, Prod.mk_eq_one] at hchar
    exact hchar
  have hb₁ : weylTuple w⁻¹ a₁ = Pi.mulSingle j₀ (weylTuple w⁻¹ a₁ j₀) := by
    funext j
    by_cases hj : j = j₀
    · subst hj; rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj, weylTuple, inv_inv]
      exact (hker j hj).1
  have hb₂ : weylTuple w⁻¹ a₂ = Pi.mulSingle j₀ (weylTuple w⁻¹ a₂ j₀) := by
    funext j
    by_cases hj : j = j₀
    · subst hj; rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj, weylTuple, inv_inv]
      exact (hker j hj).2
  let φ : rootsOfUnity 3 L →* (Fin Tag.F4.rank → Lˣ) :=
    (MonoidHom.mulSingle (fun _ : Fin Tag.F4.rank => Lˣ) j₀).comp (rootsOfUnity 3 L).subtype
  let ψ : rootsOfUnity 3 L →* ModGL Tag.F4 L := (rootDiagUnitHom Tag.F4 L).comp φ
  let g : ModGL Tag.F4 L := canonicalRep (coxeterSystem Tag.F4) L w
  let θ : rootsOfUnity 3 L →* ModGL Tag.F4 L := (MulAut.conj g).toMonoidHom.comp ψ
  have hmem₁ : weylTuple w⁻¹ a₁ j₀ ∈ rootsOfUnity 3 L :=
    (mem_rootsOfUnity 3 (weylTuple w⁻¹ a₁ j₀)).2 (by
      rw [weylTuple, inv_inv]
      exact CFSG.StandardType.TableCRes.rootChar_pow_eq_one_of_forall
        (pow_eq_one_of_rootDiagUnit_pow h.pow₁) (w • Pi.single j₀ 1))
  have hmem₂ : weylTuple w⁻¹ a₂ j₀ ∈ rootsOfUnity 3 L :=
    (mem_rootsOfUnity 3 (weylTuple w⁻¹ a₂ j₀)).2 (by
      rw [weylTuple, inv_inv]
      exact CFSG.StandardType.TableCRes.rootChar_pow_eq_one_of_forall
        (pow_eq_one_of_rootDiagUnit_pow h.pow₂) (w • Pi.single j₀ 1))
  let μ₁ : rootsOfUnity 3 L := ⟨weylTuple w⁻¹ a₁ j₀, hmem₁⟩
  let μ₂ : rootsOfUnity 3 L := ⟨weylTuple w⁻¹ a₂ j₀, hmem₂⟩
  have hb₁φ : weylTuple w⁻¹ a₁ = φ μ₁ := by
    rw [hb₁]; rfl
  have hb₂φ : weylTuple w⁻¹ a₂ = φ μ₂ := by
    rw [hb₂]; rfl
  have ha₁ : rootDiagUnit Tag.F4 a₁ = θ μ₁ := by
    have hconj := canonicalRep_conj_rootDiagUnit (τ := Tag.F4) (K := L) w (weylTuple w⁻¹ a₁)
    have hw : weylTuple w (weylTuple w⁻¹ a₁) = a₁ := by
      rw [weylTuple_weylTuple, mul_inv_cancel, weylTuple_one]
    rw [hw, hb₁φ] at hconj
    exact hconj.symm
  have ha₂ : rootDiagUnit Tag.F4 a₂ = θ μ₂ := by
    have hconj := canonicalRep_conj_rootDiagUnit (τ := Tag.F4) (K := L) w (weylTuple w⁻¹ a₂)
    have hw : weylTuple w (weylTuple w⁻¹ a₂) = a₂ := by
      rw [weylTuple_weylTuple, mul_inv_cancel, weylTuple_one]
    rw [hw, hb₂φ] at hconj
    exact hconj.symm
  have hcl : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
      Set (ModGL Tag.F4 L)) ≤ θ.range := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact MonoidHom.mem_range.mpr ⟨μ₁, ha₁.symm⟩
    · exact MonoidHom.mem_range.mpr ⟨μ₂, ha₂.symm⟩
  have hsurj : Function.Surjective
      (fun μ : rootsOfUnity 3 L => (⟨θ μ, MonoidHom.mem_range.mpr ⟨μ, rfl⟩⟩ : ↥θ.range)) :=
    fun y => by
      obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp y.2
      exact ⟨μ, Subtype.ext hμ⟩
  have : Finite ↥θ.range := Finite.of_surjective _ hsurj
  have h1 : Nat.card ↥(Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
      Set (ModGL Tag.F4 L))) ≤ Nat.card ↥θ.range := Subgroup.card_le_of_le hcl
  have h2 : Nat.card ↥θ.range ≤ Nat.card ↥(rootsOfUnity 3 L) :=
    Nat.card_le_card_of_surjective _ hsurj
  have h3 : Nat.card ↥(rootsOfUnity 3 L) ≤ 3 := card_rootsOfUnity L 3
  have hc9 : Nat.card ↥(Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
      Set (ModGL Tag.F4 L))) = 3 ^ 2 := h.card
  rw [hc9] at h1
  omega

theorem ggLieF4Plane_not_rank_three
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    (i : KernelComponent (jointChar a₁ a₂)) :
    ¬ (compRank (componentRoots (jointChar a₁ a₂) i) = 3 ∧
        (componentRoots (jointChar a₁ a₂) i).ncard = 18) := by
  rintro ⟨hr, hc⟩
  have hne : rootDiagUnit Tag.F4 a₁ ≠ 1 ∨ rootDiagUnit Tag.F4 a₂ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hbot : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 L)) = ⊥ := by
      rw [eq_bot_iff, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_bot.mpr h1
      · exact Subgroup.mem_bot.mpr h2
    have hc0 : Nat.card ↥(Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
        Set (ModGL Tag.F4 L))) = 3 ^ 2 := h.card
    rw [hbot, Subgroup.card_bot] at hc0
    norm_num at hc0
  obtain ⟨w, hshape⟩ := f4_joint_component_six_shape (p := 3) (by norm_num) (by norm_num)
    a₁ a₂ (pow_eq_one_of_rootDiagUnit_pow h.pow₁) (pow_eq_one_of_rootDiagUnit_pow h.pow₂) hne i
  rcases hshape with hA1 | hlong | hshort | hb2 | hB3 | hC3
  · obtain ⟨j, hj⟩ := hA1
    rw [hj, compRank_image] at hr
    have := l10lF2_compRank_pair_le j
    omega
  · rw [hlong, compRank_image, l10lF2_compRank_f4LongSupport] at hr
    omega
  · rw [hshort, compRank_image, l10lF2_compRank_f4ShortSupport] at hr
    omega
  · rw [hb2, compRank_image, l10lF2_compRank_b2LeviRoots] at hr
    omega
  · exact l10lF2_false_of_levi_shape h i w _ ⟨3, by decide⟩ (by
      intro j hj
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_f4LeviB3_narrow]
      have hlt : j.val < 4 := j.isLt
      have hne3 : j.val ≠ 3 := by intro hval; exact hj (Fin.ext hval)
      omega) hB3
  · exact l10lF2_false_of_levi_shape h i w _ ⟨0, by decide⟩ (by
      intro j hj
      rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_f4LeviC3_narrow]
      have hne0 : j.val ≠ 0 := by intro hval; exact hj (Fin.ext hval)
      omega) hC3

end CFSG.StandardType.LieCore

end
