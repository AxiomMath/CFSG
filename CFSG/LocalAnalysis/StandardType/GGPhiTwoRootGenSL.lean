module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenFrame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7SL2
public import CFSG.LieType.HighestRoot.CentTrialityThree
public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldTwo
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHR2
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly

private theorem units_map_entrywiseHom_weylElt_one
    {τ : Tag} {K : Type} [Field K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (i : Fin τ.rank) :
    Units.map (entrywiseHom Fr) (weylElt τ (AlgebraicClosure K) i 1) =
      weylElt τ (AlgebraicClosure K) i 1 := by
  rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul,
    CFSG.LieType.Chevalley.units_map_entrywiseHom_xUnit,
    CFSG.LieType.Chevalley.units_map_entrywiseHom_yUnit, inv_one, Units.val_one]
  simp only [map_one, map_neg]

private theorem units_map_entrywiseHom_canonicalRep
    {τ : Tag} {K : Type} [Field K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (w : WeylGroup τ) :
    Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => units_map_entrywiseHom_weylElt_one Fr i)

private theorem exists_twisted_rootSL2_fixed_canonicalRep
    {τ : Tag} {K : Type} [Field K]
    [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hwβ : w • β = -β) :
    ∃ P : GL (Fin 2) (AlgebraicClosure K), ∀ B : SL2 (AlgebraicClosure K),
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
          Units.map (entrywiseHom Fr) (rootSL2 τ (AlgebraicClosure K) β B) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
          rootSL2 τ (AlgebraicClosure K) β B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
          (CFSG.RankThree.Classical.conjSL P) := by
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  have hm : canonicalRep (coxeterSystem τ) (AlgebraicClosure K)
        ((coxeterSystem τ).wordProd ω) =
      CFSG.LieType.AlgebraicGroups.wordWeylMatrix τ (AlgebraicClosure K) ω.reverse := by
    rw [canonicalRep_wordProd hω, CFSG.LieType.AlgebraicGroups.wordWeylMatrix,
      List.reverse_reverse]
  have hw : ToralSign.wordElt τ ω.reverse • β = -β := by
    rw [ToralSign.wordElt, List.reverse_reverse]
    exact hwβ
  obtain ⟨P, hP⟩ := CFSG.ComponentClassification.Burgoyne.E2.TwE7.exists_twisted_rootSL2_fixed
    (K := K) Fr hFr ω.reverse hβ hw
  rw [← hm] at hP
  exact ⟨P, hP⟩

private theorem units_map_entrywiseHom_baseChangeGL
    {τ : Tag} {K : Type} [Field K]
    [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (y : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K (AlgebraicClosure K)) y) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) y := by
  have : Fintype K := Fintype.ofFinite K
  have hcomp : Fr.comp (algebraMap K (AlgebraicClosure K)) = algebraMap K (AlgebraicClosure K) := by
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
    CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]

private theorem map_conj_mul_canonicalRep
    {τ : Tag} {K : Type} [Field K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {w : WeylGroup τ}
    {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (X : ModGL τ (AlgebraicClosure K)) :
    Units.map (entrywiseHom Fr) (g0 * X * g0⁻¹) =
      g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
        Units.map (entrywiseHom Fr) X *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ := by
  rw [map_mul, map_mul, map_inv, hg0]
  group

private theorem range_rootSL2_eq_rootSpan_pair
    {τ : Tag} {K : Type} [Field K]
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    (rootSL2 τ (AlgebraicClosure K) β).range =
      rootSpan τ (AlgebraicClosure K) {β, -β} := by
  rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβ,
    CFSG.LieType.HighestRoot.rootSpan_pair_eq]

private noncomputable def phiTwoTheta
    {τ : Tag} {K : Type} [Field K]
    (g0 : ModGL τ (AlgebraicClosure K))
    (β : Fin τ.rank → ℤ) : phiTwoComp g0 β →* ModGL τ (AlgebraicClosure K) :=
  (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      ((adjointGroup τ K).subtype.comp (phiTwoComp g0 β).subtype))

private theorem phiTwoTheta_apply
    {τ : Tag} {K : Type} [Field K]
    (g0 : ModGL τ (AlgebraicClosure K))
    (β : Fin τ.rank → ℤ) (x : phiTwoComp g0 β) :
    phiTwoTheta g0 β x = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup τ K) : ModGL τ K) * g0 := rfl

private theorem specialLinearMap_injective
    {K : Type} [Field K] :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (algebraMap K (AlgebraicClosure K))) := by
  intro A B h
  ext i j
  have h1 := congrArg (fun X : SL2 (AlgebraicClosure K) =>
    (X : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at h1
  exact (algebraMap K (AlgebraicClosure K)).injective h1

private theorem conjSL_injective
    {K : Type} [Field K] (P : GL (Fin 2) (AlgebraicClosure K)) :
    Function.Injective (CFSG.RankThree.Classical.conjSL P) := by
  intro A B h
  have h1 := congrArg (CFSG.RankThree.Classical.conjSL P⁻¹) h
  rwa [← CFSG.RankThree.Classical.conjSL_mul, ← CFSG.RankThree.Classical.conjSL_mul,
    inv_mul_cancel, CFSG.RankThree.Classical.conjSL_one,
    CFSG.RankThree.Classical.conjSL_one] at h1

private theorem exists_conj_rootSL2_of_mem_phiTwoComp
    {τ : Tag} {K : Type} [Field K]
    [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {P : GL (Fin 2) (AlgebraicClosure K)}
    (hP : ∀ B : SL2 (AlgebraicClosure K),
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
          Units.map (entrywiseHom Fr) (rootSL2 τ (AlgebraicClosure K) β B) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
          rootSL2 τ (AlgebraicClosure K) β B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
          (CFSG.RankThree.Classical.conjSL P))
    {x : adjointGroup τ K} (hx : x ∈ phiTwoComp g0 β) :
    ∃ B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
        (CFSG.RankThree.Classical.conjSL P),
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) =
          g0 * rootSL2 τ (AlgebraicClosure K) β B * g0⁻¹ := by
  have hmem := (mem_phiTwoComp_iff (g0 := g0) (β := β) (x := x)).1 hx
  rw [← range_rootSL2_eq_rootSpan_pair hβ] at hmem
  obtain ⟨B, hB⟩ := hmem
  have hxL : g0 * rootSL2 τ (AlgebraicClosure K) β B * g0⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) := by
    rw [hB]; group
  refine ⟨B, ?_, hxL.symm⟩
  apply (hP B).1
  have hfix := units_map_entrywiseHom_baseChangeGL (K := K) hFr
    ((x : adjointGroup τ K) : ModGL τ K)
  have h3 := map_conj_mul_canonicalRep (K := K) (Fr := Fr) (w := w) hg0
    (rootSL2 τ (AlgebraicClosure K) β B)
  have h4 : g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
      Units.map (entrywiseHom Fr) (rootSL2 τ (AlgebraicClosure K) β B) *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) := by
    rw [← h3, hxL]
    exact hfix
  have h6 : g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
      Units.map (entrywiseHom Fr) (rootSL2 τ (AlgebraicClosure K) β B) *
        (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ =
      g0 * rootSL2 τ (AlgebraicClosure K) β B * g0⁻¹ := h4.trans hxL.symm
  calc canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
        Units.map (entrywiseHom Fr) (rootSL2 τ (AlgebraicClosure K) β B) *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹
      = g0⁻¹ * (g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
          Units.map (entrywiseHom Fr) (rootSL2 τ (AlgebraicClosure K) β B) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹) * g0⁻¹) * g0 := by
        group
    _ = g0⁻¹ * (g0 * rootSL2 τ (AlgebraicClosure K) β B * g0⁻¹) * g0 := by rw [h6]
    _ = rootSL2 τ (AlgebraicClosure K) β B := by group

private theorem exists_mem_phiTwoComp_of_mem_conjSL
    {τ : Tag} {K : Type} [Field K]
    [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
        (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
          X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {P : GL (Fin 2) (AlgebraicClosure K)}
    (hP : ∀ B : SL2 (AlgebraicClosure K),
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
          Units.map (entrywiseHom Fr) (rootSL2 τ (AlgebraicClosure K) β B) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
          rootSL2 τ (AlgebraicClosure K) β B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
          (CFSG.RankThree.Classical.conjSL P))
    {B : SL2 (AlgebraicClosure K)}
    (hB : B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
        (CFSG.RankThree.Classical.conjSL P)) :
    ∃ x ∈ phiTwoComp g0 β,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) =
          g0 * rootSL2 τ (AlgebraicClosure K) β B * g0⁻¹ := by
  classical
  have hφinj : Function.Injective (rootSL2 τ (AlgebraicClosure K) β) :=
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field β
  have hρG : ∀ A : SL2 (AlgebraicClosure K),
      rootSL2 τ (AlgebraicClosure K) β A ∈ adjointGroup τ (AlgebraicClosure K) :=
    fun A => (exceptional_Lang_root_rank_one_data τ (AlgebraicClosure K) β).2.2.2.2.1 A
  set SK : Subgroup (SL2 (AlgebraicClosure K)) :=
    (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
      (CFSG.RankThree.Classical.conjSL P) with hSK
  set X : Subgroup (ModGL τ (AlgebraicClosure K)) :=
    (SK.map (rootSL2 τ (AlgebraicClosure K) β)).map (MulAut.conj g0).toMonoidHom with hX
  have hSKfin : Finite SK := by
    haveI : Fintype K := Fintype.ofFinite K
    exact Finite.of_equiv (SL2 K) ((MonoidHom.ofInjective specialLinearMap_injective).trans
      (Subgroup.equivMapOfInjective _ _ (conjSL_injective P))).toEquiv
  have hSKmap : Finite (SK.map (rootSL2 τ (AlgebraicClosure K) β)) :=
    Finite.of_equiv SK ((Subgroup.equivMapOfInjective SK _ hφinj).toEquiv)
  have hXfin : Finite X := by
    rw [hX]
    exact Finite.of_equiv _ ((Subgroup.equivMapOfInjective _
      (MulAut.conj g0).toMonoidHom (MulAut.conj g0).injective).toEquiv)
  have hXC : X ≤ adjointGroup τ (AlgebraicClosure K) := by
    rw [hX]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨B', hB', rfl⟩ := hz
    exact mul_mem (mul_mem hg0C (hρG B')) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
    rw [hX]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨B', hB', rfl⟩ := hz
    change Units.map (entrywiseHom Fr) (g0 * rootSL2 τ (AlgebraicClosure K) β B' * g0⁻¹) =
      g0 * rootSL2 τ (AlgebraicClosure K) β B' * g0⁻¹
    rw [map_conj_mul_canonicalRep (K := K) hg0, (hP B').2 hB']
  have hmemX : g0 * rootSL2 τ (AlgebraicClosure K) β B * g0⁻¹ ∈ X := by
    rw [hX]
    exact Subgroup.mem_map.2 ⟨rootSL2 τ (AlgebraicClosure K) β B,
      Subgroup.mem_map.2 ⟨B, hB, rfl⟩, rfl⟩
  obtain ⟨n, hnC, hnL⟩ := hrat X hXfin hXC hXF hmemX
  refine ⟨⟨n, hnC⟩, ?_, hnL⟩
  rw [mem_phiTwoComp_iff, hnL,
    show g0⁻¹ * (g0 * rootSL2 τ (AlgebraicClosure K) β B * g0⁻¹) * g0 =
      rootSL2 τ (AlgebraicClosure K) β B from by group,
    ← range_rootSL2_eq_rootSpan_pair hβ]
  exact ⟨B, rfl⟩

private theorem phiTwoCompNonemptyMulEquiv
    {τ : Tag} {K : Type} [Field K]
    [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) →
        (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
          X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {P : GL (Fin 2) (AlgebraicClosure K)}
    (hP : ∀ B : SL2 (AlgebraicClosure K),
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
          Units.map (entrywiseHom Fr) (rootSL2 τ (AlgebraicClosure K) β B) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
          rootSL2 τ (AlgebraicClosure K) β B ↔
        B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
          (CFSG.RankThree.Classical.conjSL P)) :
    Nonempty (phiTwoComp g0 β ≃* SL2 K) := by
  classical
  have hφinj : Function.Injective (rootSL2 τ (AlgebraicClosure K) β) :=
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field β
  set SK : Subgroup (SL2 (AlgebraicClosure K)) :=
    (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
      (CFSG.RankThree.Classical.conjSL P) with hSK
  have hθinj : Function.Injective (phiTwoTheta (K := K) g0 β) := by
    intro x y hxy
    have hbase : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y : adjointGroup τ K) : ModGL τ K) := by
      calc baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x : adjointGroup τ K) : ModGL τ K)
          = g0 * phiTwoTheta g0 β x * g0⁻¹ := by
            rw [phiTwoTheta_apply]; group
        _ = g0 * phiTwoTheta g0 β y * g0⁻¹ := by rw [hxy]
        _ = baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((y : adjointGroup τ K) : ModGL τ K) := by
            rw [phiTwoTheta_apply]; group
    exact Subtype.ext (Subtype.ext (CFSG.LieType.Chevalley.baseChangeGL_injective
      (algebraMap K (AlgebraicClosure K)) hbase))
  have hrange : (phiTwoTheta (K := K) g0 β).range =
      SK.map (rootSL2 τ (AlgebraicClosure K) β) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨B, hB, hBx⟩ := exists_conj_rootSL2_of_mem_phiTwoComp (K := K) hFr hg0 hβ hP x.2
      refine Subgroup.mem_map.2 ⟨B, hB, ?_⟩
      rw [phiTwoTheta_apply, hBx]
      group
    · rintro _ ⟨B, hB, rfl⟩
      obtain ⟨x, hx, hxL⟩ :=
        exists_mem_phiTwoComp_of_mem_conjSL (K := K) hrat hg0C hg0 hβ hP hB
      exact ⟨⟨x, hx⟩, by rw [phiTwoTheta_apply, hxL]; group⟩
  have e1 : phiTwoComp g0 β ≃* SK.map (rootSL2 τ (AlgebraicClosure K) β) := by
    rw [← hrange]
    exact MonoidHom.ofInjective hθinj
  have e2 : SK.map (rootSL2 τ (AlgebraicClosure K) β) ≃* SK :=
    (Subgroup.equivMapOfInjective SK _ hφinj).symm
  have e3 : SK ≃* SL2 K :=
    ((MonoidHom.ofInjective specialLinearMap_injective).trans
      (Subgroup.equivMapOfInjective _ _ (conjSL_injective P))).symm
  exact ⟨e1.trans (e2.trans e3)⟩

private theorem map_conj_canonicalRep_rootReflection
    {τ : Tag} {K : Type} [Field K]
    [CharP K 2]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    {w : WeylGroup τ} (hcent : ∀ v : WeylGroup τ, v * w = w * v)
    {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {β : Fin τ.rank → ℤ} :
    Units.map (entrywiseHom Fr)
        (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) * g0⁻¹) =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) * g0⁻¹ := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  rw [map_conj_mul_canonicalRep (K := K) hg0, units_map_entrywiseHom_canonicalRep]
  have hv : w * rootReflection β * w⁻¹ = rootReflection β := by
    rw [← hcent (rootReflection β), mul_assoc, mul_inv_cancel, mul_one]
  have h1 : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (w * rootReflection β * w⁻¹) =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (w * rootReflection β) *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w⁻¹ :=
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo _ _
  have h2 : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (w * rootReflection β) =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) :=
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo _ _
  have h3 : (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w⁻¹ :=
    CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_inv_of_charTwo w
  have hmain : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
        canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) := by
    calc canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
          canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) *
            (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹
        = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (w * rootReflection β * w⁻¹) := by
          rw [h1, h2, h3]
      _ = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) := by rw [hv]
  rw [hmain]

theorem nonempty_mulEquiv_phiTwoComp
    {τ : Tag} {K : Type} [Field K]
    [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hwβ : w • β = -β) :
    Nonempty (phiTwoComp g0 β ≃* SL2 K) := by
  obtain ⟨P, hP⟩ := exists_twisted_rootSL2_fixed_canonicalRep (K := K) hFr hβ hwβ
  exact phiTwoCompNonemptyMulEquiv hFr hrat hg0C hg0 hβ hP

theorem isQuasisimple_phiTwoComp
    {τ : Tag} {K : Type} [Field K]
    [Finite K] (hK4 : 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hwβ : w • β = -β) :
    IsQuasisimple (phiTwoComp g0 β) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_phiTwoComp (K := K) (Fr := Fr) hFr hrat hg0C hg0 hβ hwβ
  have hSL2 : CFSG.IsQuasisimple (SL2 K) :=
    CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le hK4
  exact CFSG.IsQuasisimple.of_mulEquiv e hSL2

theorem dvd_card_phiTwoComp
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    [Finite K] (hpq : p ∣ Nat.card K + 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hwβ : w • β = -β) :
    p ∣ Nat.card (phiTwoComp g0 β) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_phiTwoComp (K := K) (Fr := Fr) hFr hrat hg0C hg0 hβ hwβ
  rw [Nat.card_congr e.toEquiv, CFSG.CGT.PushingUpLit.BHS6.card_SL2_eq]
  have h1 : Nat.card K + 1 ∣ Nat.card K ^ 2 - 1 := by
    have hsq : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      simpa using (Nat.sq_sub_sq (Nat.card K) 1)
    exact ⟨Nat.card K - 1, hsq⟩
  exact hpq.trans (dvd_mul_of_dvd_right h1 (Nat.card K))

theorem exists_phiTwoWeyl
    {τ : Tag} {K : Type} [Field K]
    [CharP K 2] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} (hcent : ∀ v : WeylGroup τ, v * w = w * v)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ n ∈ phiTwoComp g0 β,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) ((n : adjointGroup τ K) : ModGL τ K) =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) * g0⁻¹ := by
  classical
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set nv := canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) with hnv
  set g := g0 * nv * g0⁻¹ with hg
  have hF : Units.map (entrywiseHom Fr) g = g :=
    map_conj_canonicalRep_rootReflection (K := K) (β := β) hcent hg0
  have hnv2 : nv * nv = 1 := by
    rw [hnv, ← CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
      rootReflection_mul_self hβ, canonicalRep_one]
  have hg2 : g ^ 2 = 1 := by
    rw [hg, pow_two]
    calc (g0 * nv * g0⁻¹) * (g0 * nv * g0⁻¹) = g0 * (nv * nv) * g0⁻¹ := by group
      _ = 1 := by rw [hnv2]; group
  have hfin : Finite (Subgroup.zpowers g) :=
    IsOfFinOrder.finite_zpowers (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, hg2⟩)
  have hnvC : nv ∈ adjointGroup τ (AlgebraicClosure K) :=
    canonicalRep_mem_adjointGroup (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β)
  have hgC : g ∈ adjointGroup τ (AlgebraicClosure K) :=
    mul_mem (mul_mem hg0C hnvC) (inv_mem hg0C)
  have hC : Subgroup.zpowers g ≤ adjointGroup τ (AlgebraicClosure K) := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact Subgroup.zpow_mem (adjointGroup τ (AlgebraicClosure K)) hgC k
  have hFix : ∀ x ∈ Subgroup.zpowers g, Units.map (entrywiseHom Fr) x = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow]
    exact congrArg (fun y => y ^ k) hF
  obtain ⟨n, hnC, hnL⟩ := hrat (Subgroup.zpowers g) hfin hC hFix (Subgroup.mem_zpowers g)
  refine ⟨⟨n, hnC⟩, ?_, hnL⟩
  rw [mem_phiTwoComp_iff, hnL, hg, hnv,
    show g0⁻¹ * (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β) *
        g0⁻¹) * g0 = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection β)
      from by group,
    ← range_rootSL2_eq_rootSpan_pair hβ,
    ← CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo hβ]
  exact ⟨nSL 1, rfl⟩

end CFSG.StandardType.PhiTwoRootGen

end
