module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.PrimaryConjScalar
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinProj
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTableBTypeALift
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.CALinearPrimary

private lemma linShape_recipeEquiv_conj
    {K : Type} [Field K] {N : ℕ} {d : GL (Fin N) K} {δ' : MulAut (PSLg N K)}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ') :
    MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K) δ' =
      LinearFlag.conjAut N K d := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective N K x
  set h : LargeEvenSLGroup (Fin N) K := (CFSG.StandardType.TypeA.slKerEquiv N K).symm g
  have hg : (CFSG.StandardType.TypeA.slKerEquiv N K) h = g :=
    MulEquiv.apply_symm_apply _ _
  have hmem : d * (h : GL (Fin N) K) * d⁻¹ ∈ LargeEvenSLGroup (Fin N) K := by
    rw [CFSG.StandardType.TypeA.mem_largeEvenSLGroup_iff,
      ← Matrix.GeneralLinearGroup.val_det_apply]
    rw [map_mul, map_mul, map_inv]
    have hdet : Matrix.GeneralLinearGroup.det (h : GL (Fin N) K) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply,
        CFSG.StandardType.TypeA.mem_largeEvenSLGroup_iff.mp h.2]
      rfl
    rw [hdet, mul_one, mul_inv_cancel]
    rfl
  let h' : LargeEvenSLGroup (Fin N) K := ⟨d * (h : GL (Fin N) K) * d⁻¹, hmem⟩
  have hrel : (h' : GL (Fin N) K) = d * h * d⁻¹ := rfl
  have h1 : δ' (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h' := hd h h' hrel
  have h2 : (CFSG.StandardType.TypeA.slKerEquiv N K) h' =
      (ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K d)
        ((CFSG.StandardType.TypeA.slKerEquiv N K) h) := by
    apply Subtype.ext
    simp only [CFSG.StandardType.TypeA.coe_slKerEquiv,
      LinearFlag.coe_slConjugation]
    rfl
  have hx : LinearFlag.proj N K g =
      (CFSG.StandardType.TypeA.recipeEquiv N K)
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) := by
    rw [← hg, ← CFSG.StandardType.TypeA.recipeEquiv_mk h]
  rw [hx]
  calc (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K) δ')
        ((CFSG.StandardType.TypeA.recipeEquiv N K)
          (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h))
      = (CFSG.StandardType.TypeA.recipeEquiv N K)
          (δ' (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h)) := by
        simp [MulAut.congr_apply, MulEquiv.trans_apply]
    _ = (CFSG.StandardType.TypeA.recipeEquiv N K)
          (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h') := by rw [h1]
    _ = LinearFlag.proj N K ((CFSG.StandardType.TypeA.slKerEquiv N K) h') :=
        CFSG.StandardType.TypeA.recipeEquiv_mk h'
    _ = LinearFlag.proj N K
          ((ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K d)
            ((CFSG.StandardType.TypeA.slKerEquiv N K) h)) := by rw [h2]
    _ = LinearFlag.conjAut N K d
          (LinearFlag.proj N K ((CFSG.StandardType.TypeA.slKerEquiv N K) h)) :=
        (LinearFlag.conjAut_proj d _).symm
    _ = LinearFlag.conjAut N K d
          ((CFSG.StandardType.TypeA.recipeEquiv N K)
            (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h)) := by
        rw [CFSG.StandardType.TypeA.recipeEquiv_mk]

private lemma linShape_specialFactor_image_ne
    {K : Type} [Field K] [Finite K] {N : ℕ} {d : GL (Fin N) K}
    (hsq : Squarefree (minpoly K (glA d : Module.End K (Fin N → K))))
    {h h₂ : Polynomial K}
    (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K)))
    (hh₂ : h₂ ∈ primaryFactors (glA d : Module.End K (Fin N → K)))
    (hne : h ≠ h₂) (hgood : IsGoodFactor d h)
    (hmap : (specialFactor d h).map (LinearFlag.proj N K) =
            (specialFactor d h₂).map (LinearFlag.proj N K)) : False := by
  have hF : specialFactor d h ⊔ LinearFlag.scalars N K =
      specialFactor d h₂ ⊔ LinearFlag.scalars N K := by
    have h := congrArg (Subgroup.comap (LinearFlag.proj N K)) hmap
    rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, LinearFlag.ker_proj] at h
  have hle : specialFactor d h ≤ specialFactor d h₂ ⊔ LinearFlag.scalars N K := by
    rw [← hF]; exact le_sup_left
  have hscalar : ∀ x ∈ specialFactor d h, ∃ c : K,
      ∀ v ∈ primaryComponent (glA d : Module.End K (Fin N → K)) h,
        (slGL N K x : Module.End K (Fin N → K)) v = c • v := by
    intro x hx
    have hxsup := hle hx
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right).mp hxsup
    obtain ⟨c, -, hzmat⟩ := LinearFlag.mem_scalars.mp hz
    refine ⟨(c : K), fun v hv => ?_⟩
    have hyid : (slGL N K y : Module.End K (Fin N → K)) v = v :=
      (mem_linearSpecialBlock.mp hy).2.1 h hh hne v hv
    have hzsm : (slGL N K z : Module.End K (Fin N → K)) v = (c : K) • v := by
      have hz' : (slGL N K z : Module.End K (Fin N → K)) = (c : K) • 1 := by
        change (Matrix.toLin' ((z : Matrix (Fin N) (Fin N) K)) :
          (Fin N → K) →ₗ[K] (Fin N → K)) = (c : K) • 1
        rw [hzmat]
        ext w i
        simp [Matrix.toLin'_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal]
      rw [hz']
      rfl
    calc (slGL N K x : Module.End K (Fin N → K)) v
        = (slGL N K (y * z) : Module.End K (Fin N → K)) v := by rw [hyz]
      _ = (slGL N K y : Module.End K (Fin N → K))
            ((slGL N K z : Module.End K (Fin N → K)) v) := by
            simp [map_mul, Module.End.mul_apply]
      _ = (slGL N K y : Module.End K (Fin N → K)) ((c : K) • v) := by rw [hzsm]
      _ = (c : K) • (slGL N K y : Module.End K (Fin N → K)) v := map_smul _ _ _
      _ = (c : K) • v := by rw [hyid]
  have hcomm : ∀ x ∈ specialFactor d h, ∀ y ∈ specialFactor d h,
      x * y = y * x := by
    intro x hx y hy
    apply slGL_injective
    apply Units.ext
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    apply ext_primaryComponent hsq
    intro aa haa v hv
    by_cases hah : aa = h
    · rw [hah] at hv
      obtain ⟨cx, hcx⟩ := hscalar x hx
      obtain ⟨cy, hcy⟩ := hscalar y hy
      simp only [Module.End.mul_apply]
      calc (slGL N K x : Module.End K (Fin N → K))
              ((slGL N K y : Module.End K (Fin N → K)) v)
          = (slGL N K x : Module.End K (Fin N → K)) (cy • v) := by rw [hcy v hv]
        _ = cy • (slGL N K x : Module.End K (Fin N → K)) v := map_smul _ _ _
        _ = cy • (cx • v) := by rw [hcx v hv]
        _ = (cy * cx) • v := by rw [smul_smul]
        _ = (cx * cy) • v := by rw [mul_comm]
        _ = cx • (cy • v) := by rw [smul_smul]
        _ = cx • (slGL N K y : Module.End K (Fin N → K)) v := by rw [hcy v hv]
        _ = (slGL N K y : Module.End K (Fin N → K)) (cx • v) := (map_smul _ _ _).symm
        _ = (slGL N K y : Module.End K (Fin N → K))
              ((slGL N K x : Module.End K (Fin N → K)) v) := by rw [hcx v hv]
    · have hxid : (slGL N K x : Module.End K (Fin N → K)) v = v :=
        (mem_linearSpecialBlock.mp hx).2.1 aa haa hah v hv
      have hyid : (slGL N K y : Module.End K (Fin N → K)) v = v :=
        (mem_linearSpecialBlock.mp hy).2.1 aa haa hah v hv
      simp only [Module.End.mul_apply]
      rw [hyid, hxid, hyid]
  obtain ⟨x, y, hxy⟩ := (isQuasisimple_specialFactor hsq hh hgood).2.2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(specialFactor d h)) x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(specialFactor d h)) y
  refine hxy ?_
  rw [← map_mul, ← map_mul]
  exact congrArg (QuotientGroup.mk' (Subgroup.center ↥(specialFactor d h)))
    (Subtype.ext (hcomm x'.1 x'.2 y'.1 y'.2))

private lemma linShape_cubic_no_deg_two_factor
    {K : Type} [Field K] {c ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {h : Polynomial K} (hmon : h.Monic) (hirr : Irreducible h) (hdeg : h.natDegree = 2)
    (hdvd : h ∣ X ^ 3 - C c) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hω : IsPrimitiveRoot ω 3 := by
    refine IsPrimitiveRoot.mk hω3 (fun l hl => ?_)
    have ho : orderOf ω = 3 := orderOf_eq_prime_iff.mpr ⟨hω3, hω1⟩
    rw [← ho]
    exact orderOf_dvd_iff_pow_eq_one.mpr hl
  have hnotirr : ¬ Irreducible (X ^ 3 - C c : Polynomial K) := by
    intro hc
    have hassoc : Associated h (X ^ 3 - C c) := hirr.associated_of_dvd hc hdvd
    have hle1 : h.natDegree ≤ (X ^ 3 - C c : Polynomial K).natDegree :=
      Polynomial.natDegree_le_of_dvd hassoc.dvd
        (Polynomial.X_pow_sub_C_ne_zero (by norm_num) c)
    have hle2 : (X ^ 3 - C c : Polynomial K).natDegree ≤ h.natDegree :=
      Polynomial.natDegree_le_of_dvd hassoc.symm.dvd hmon.ne_zero
    rw [Polynomial.natDegree_X_pow_sub_C, hdeg] at hle1 hle2
    omega
  obtain ⟨b, hbroot⟩ : ∃ b : K, (X ^ 3 - C c : Polynomial K).IsRoot b := by
    by_contra h
    rw [not_exists] at h
    exact hnotirr (Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by rw [Polynomial.natDegree_X_pow_sub_C]; norm_num) (fun x hx => h x hx))
  have hb : b ^ 3 = c := by
    have h1 := hbroot
    rw [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at h1
    exact h1
  have hsplit : (X ^ 3 - C c : Polynomial K).Splits :=
    X_pow_sub_C_splits_of_isPrimitiveRoot hω hb
  have hsplit_h : h.Splits :=
    hsplit.of_dvd (Polynomial.X_pow_sub_C_ne_zero (by norm_num) c) hdvd
  have h1 := hsplit_h.natDegree_eq_one_of_irreducible hirr
  omega

theorem linShape_rank_support
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {Ā : Subgroup (MulAut (PSLg N K))}
    {δ' : MulAut (PSLg N K)}
    {J' : Subgroup (PSLg N K)} (hR : RDatum Ā δ' J')
    (hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      Set.univ)
    {d : GL (Fin N) K}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ')
    {lam : Ā →* Kˣ} {g : Ā → GL (Fin N) K}
    (hgraph : ∀ a : Ā, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      (fun h h' => (h' : GL (Fin N) K) = g a * h * (g a)⁻¹) (a : MulAut (PSLg N K)))
    (hlam3 : ∀ a : Ā, (lam a) ^ 3 = 1)
    (hg : ∀ a : Ā, ((g a * d * (g a)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          (lam a : K) • (d : Matrix (Fin N) (Fin N) K))
    {h : Polynomial K} (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K))) (hgood : IsGoodFactor d h)
    {e : PSLg N K ≃* LinearFlag.projectiveSL N K}
    (heJ : J' = Subgroup.comap e.toMonoidHom ((specialFactor d h).map (LinearFlag.proj N K)))
    {j : ℕ} (hj : j = h.natDegree) :
    (j ≠ 3 → lam = 1) ∧ Nat.card (Ā ⧸ lam.ker) ≤ 3 := by
  have hcard : Nat.card (Ā ⧸ lam.ker) ≤ 3 := by
    have hle : lam.range ≤ rootsOfUnity 3 K := by
      rintro x ⟨a, rfl⟩
      rw [mem_rootsOfUnity]
      exact hlam3 a
    have h1 : Nat.card lam.range ≤ Nat.card (rootsOfUnity 3 K) :=
      Nat.card_mono (Set.toFinite _) hle
    have h2 : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K 3
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange lam)).trans_le (h1.trans h2)
  refine ⟨?_, hcard⟩
  intro hjne
  by_contra hlam_ne
  obtain ⟨a, ha⟩ : ∃ a : Ā, lam a ≠ 1 := by
    by_contra h
    rw [not_exists] at h
    simp only [not_not] at h
    exact hlam_ne (MonoidHom.ext h)
  have h3ne : (3 : K) ≠ 0 := by
    intro h3
    apply ha
    have hla3 : ((lam a : K)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hlam3 a]
      rfl
    have h3' : (3 : K) = 0 := h3
    have h1 : ((lam a : K) - 1) ^ 3 = 0 := by
      have h2 : ((lam a : K) - 1) ^ 3 = (lam a : K) ^ 3 - 1 := by
        ring_nf
        simp [h3']
      rw [h2, hla3, sub_self]
    have h2 : (lam a : K) - 1 = 0 := by
      by_contra hne
      exact (pow_ne_zero 3 hne) h1
    exact Units.ext (by simpa using sub_eq_zero.mp h2)
  have hN0 : 0 < N := by
    have hmult : 2 ≤ primaryMultiplicity (glA d : Module.End K (Fin N → K)) h := by
      rcases hgood with h3 | ⟨h2, -⟩ <;> omega
    haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
    have hfin : primaryMultiplicity (glA d : Module.End K (Fin N → K)) h ≤
        Module.finrank K (primaryComponent (glA d : Module.End K (Fin N → K)) h) := by
      rw [finrank_primaryComponent]
      exact Nat.le_mul_of_pos_left _ (Fact.out : Irreducible h).natDegree_pos
    have hle : Module.finrank K (primaryComponent (glA d : Module.End K (Fin N → K)) h) ≤ N := by
      have := Submodule.finrank_le (primaryComponent (glA d : Module.End K (Fin N → K)) h)
      simpa using this
    omega
  have hcanon_d := linShape_recipeEquiv_conj hd
  have hδ3 : δ' ^ 3 = 1 := hR.elem.2 δ' hR.mem
  have hconj3 : LinearFlag.conjAut N K (d ^ 3) = 1 := by
    rw [map_pow, ← hcanon_d, ← map_pow, hδ3, map_one]
  obtain ⟨c, hc⟩ := CFSG.StandardType.TypeA.exists_scalar_of_conjAut_eq_one hconj3
  obtain ⟨u, hu⟩ := CFSG.StandardType.TypeA.exists_unit_of_scalar hN0 hc
  have hsq : Squarefree (minpoly K (glA d : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA h3ne hu
  have hdvd : h ∣ X ^ 3 - C (u : K) := by
    have h1 : h ∣ minpoly K (glA d : Module.End K (Fin N → K)) :=
      (mem_primaryFactors.mp hh).2.2
    have h2 : minpoly K (glA d : Module.End K (Fin N → K)) ∣ X ^ 3 - C (u : K) := by
      apply minpoly.dvd
      have hgl : (glA d : Module.End K (Fin N → K)) ^ 3 = (u : K) • 1 := by
        have h1 : ((glA d : LinearMap.GeneralLinearGroup K (Fin N → K)) :
            Module.End K (Fin N → K)) = Matrix.toLin' (d : Matrix (Fin N) (Fin N) K) := rfl
        rw [h1, ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hu]
        ext v i
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.toLin'_apply, Matrix.scalar_apply,
          Matrix.mulVec_diagonal]
      rw [map_sub, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, hgl, sub_self]
    exact h1.trans h2
  have hdeg3 : h.natDegree ≤ 3 := by
    have := Polynomial.natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero (by norm_num) (u : K))
    rwa [Polynomial.natDegree_X_pow_sub_C] at this
  have hdeg1 : 1 ≤ h.natDegree := (irreducible_of_mem_primaryFactors hh).natDegree_pos
  have hjne3 : h.natDegree ≠ 3 := by
    intro h3; exact hjne (by rw [hj, h3])
  have hcase : h.natDegree = 1 ∨ h.natDegree = 2 := by omega
  rcases hcase with hj1 | hj2
  ·
    have hmonic : h.Monic := monic_of_mem_primaryFactors hh
    have hform0 : h = X + C (h.coeff 0) := hmonic.eq_X_add_C hj1
    set u₀ : K := -(h.coeff 0) with hu₀def
    have hform : h = X - C u₀ := by rw [hform0]; simp [u₀, sub_eq_add_neg]
    have hu₀ : u₀ ≠ 0 := by
      intro hu0
      have hVne := primaryComponent_ne_bot hsq hh
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
      have hv' : (glA d : Module.End K (Fin N → K)) v = u₀ • v := by
        have hmem := (mem_primaryComponent.mp hv)
        rw [hform, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at hmem
        simpa [sub_eq_zero] using hmem
      rw [hu0, zero_smul] at hv'
      exact hv0 (by
        have hinj : Function.Injective (glA d : Module.End K (Fin N → K)) :=
          (LinearMap.GeneralLinearGroup.toLinearEquiv (glA d)).injective
        exact hinj (by rw [hv', map_zero]))
    have hconj : g a * d * (g a)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin N) (lam a) * d := by
      apply Units.ext
      rw [hg a, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, one_mul]
    have hMV := map_primaryComponent_X_sub_C_of_conj_eq_scalar_mul (D := d) (Mb := g a)
      (ζ := lam a) hconj hform
    have hVne : primaryComponent (glA d : Module.End K (Fin N → K)) h ≠ ⊥ :=
      primaryComponent_ne_bot hsq hh
    obtain ⟨hh₂, hne₂⟩ := mem_primaryFactors_X_sub_C_div_and_ne_of_map_primaryComponent
      (D := d) (Mb := g a) (ζ := lam a) (f := h) (ε := u₀) hform ha hu₀ hVne hMV
    have hdeg₂ : (X - C (u₀ / (lam a : K)) : Polynomial K).natDegree = 1 := by
      rw [Polynomial.natDegree_X_sub_C]
    have hmult : primaryMultiplicity (glA d : Module.End K (Fin N → K))
          (X - C (u₀ / (lam a : K))) =
        primaryMultiplicity (glA d : Module.End K (Fin N → K)) h := by
      haveI : Fact (Irreducible (X - C (u₀ / (lam a : K)) : Polynomial K)) :=
        ⟨Polynomial.irreducible_X_sub_C _⟩
      haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
      have hfin : Module.finrank K (primaryComponent (glA d : Module.End K (Fin N → K))
            (X - C (u₀ / (lam a : K)))) =
          Module.finrank K (primaryComponent (glA d : Module.End K (Fin N → K)) h) := by
        rw [← hMV]
        exact LinearEquiv.finrank_map_eq
          (LinearMap.GeneralLinearGroup.toLinearEquiv (glA (g a))) _
      have h1 : primaryMultiplicity (glA d : Module.End K (Fin N → K)) h =
          Module.finrank K (primaryComponent (glA d : Module.End K (Fin N → K)) h) := by
        have := finrank_primaryComponent (glA d : Module.End K (Fin N → K)) h
        rw [hj1, one_mul] at this
        exact this.symm
      have h2 : primaryMultiplicity (glA d : Module.End K (Fin N → K))
            (X - C (u₀ / (lam a : K))) =
          Module.finrank K (primaryComponent (glA d : Module.End K (Fin N → K))
            (X - C (u₀ / (lam a : K)))) := by
        have := finrank_primaryComponent (glA d : Module.End K (Fin N → K))
          (X - C (u₀ / (lam a : K)))
        rw [hdeg₂, one_mul] at this
        exact this.symm
      rw [h1, h2, hfin]
    have hgood₂ : IsGoodFactor d (X - C (u₀ / (lam a : K))) := by
      haveI : Fact (Irreducible (X - C (u₀ / (lam a : K)) : Polynomial K)) :=
        ⟨Polynomial.irreducible_X_sub_C _⟩
      haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
      rcases hgood with h3 | ⟨h2, h4⟩
      · exact Or.inl (by rw [hmult]; exact h3)
      · refine Or.inr ⟨by rw [hmult]; exact h2, ?_⟩
        have hcard₂ := CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot
          (X - C (u₀ / (lam a : K)) : Polynomial K)
        rw [hdeg₂, pow_one] at hcard₂
        have hcardh := CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h
        rw [hj1, pow_one] at hcardh
        rw [hcard₂, ← hcardh]
        exact h4
    set canon := CFSG.StandardType.TypeA.recipeEquiv N K with hcanon_def
    have hcanon_d : MulAut.congr canon δ' = LinearFlag.conjAut N K d := by
      rw [hcanon_def]; exact linShape_recipeEquiv_conj hd
    have hconj_canon : ∀ x, LinearFlag.conjAut N K d x = canon (δ' (canon.symm x)) := by
      intro x
      have := congrArg (fun f : MulAut (LinearFlag.projectiveSL N K) => f x) hcanon_d
      simpa [MulAut.congr_apply, MulEquiv.trans_apply] using this.symm
    have hcomap : Subgroup.map canon.symm.toMonoidHom
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (LinearFlag.conjAut N K d)) =
        ggAutFixedSubgroup δ' := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rw [← hyx]
        show δ' (canon.symm y) = canon.symm y
        apply canon.injective
        rw [← hconj_canon y, MulEquiv.apply_symm_apply]
        exact hy
      · intro hx
        refine ⟨canon x, ?_, canon.symm_apply_apply x⟩
        show LinearFlag.conjAut N K d (canon x) = canon x
        rw [hconj_canon (canon x), MulEquiv.symm_apply_apply, hx]
    have hcomp_h : IsComponentOf
        (Subgroup.map canon.symm.toMonoidHom
          (Subgroup.map (LinearFlag.proj N K) (specialFactor d h)))
        (ggAutFixedSubgroup δ') := by
      have h1 := (CFSG.Assembly.isComponentOf_iff_open).mpr
        (CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin.isComponentOf_map_specialFactor (A := d)
          hsq hh hgood)
      have h2 := CFSG.StandardType.isComponentOf_map_mulEquiv' canon.symm h1
      rwa [hcomap] at h2
    have hcomp_h₂ : IsComponentOf
        (Subgroup.map canon.symm.toMonoidHom
          (Subgroup.map (LinearFlag.proj N K)
            (specialFactor d (X - C (u₀ / (lam a : K))))))
        (ggAutFixedSubgroup δ') := by
      have h1 := (CFSG.Assembly.isComponentOf_iff_open).mpr
        (CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin.isComponentOf_map_specialFactor (A := d)
          hsq hh₂ hgood₂)
      have h2 := CFSG.StandardType.isComponentOf_map_mulEquiv' canon.symm h1
      rwa [hcomap] at h2
    have heq : Subgroup.map (LinearFlag.proj N K) (specialFactor d h) =
        Subgroup.map (LinearFlag.proj N K) (specialFactor d (X - C (u₀ / (lam a : K)))) :=
      Subgroup.map_injective canon.symm.injective
        ((hR.uniq _ hcomp_h).trans (hR.uniq _ hcomp_h₂).symm)
    exact linShape_specialFactor_image_ne hsq hh hh₂ hne₂.symm hgood heq
  ·
    have hω3 : ((lam a : K)) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hlam3 a]; rfl
    have hω1 : (lam a : K) ≠ 1 := by
      intro h; exact ha (Units.ext h)
    exact linShape_cubic_no_deg_two_factor hω3 hω1 (monic_of_mem_primaryFactors hh)
      (irreducible_of_mem_primaryFactors hh) hj2 hdvd

end CFSG.StandardType.TablePThreeKG

end
