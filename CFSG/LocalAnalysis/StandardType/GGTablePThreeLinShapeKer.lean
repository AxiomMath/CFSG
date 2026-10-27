module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadKey
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgLinear
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsLin
import CFSG.LocalAnalysis.StandardType.GGTableBLinear
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLIDPSL
import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenBasic
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma27Aux1
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.BasicAuxGen
import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinProj
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015NLLinear
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonL2Holds
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoAutK
import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
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
import CFSG.HardMathSupport.Dickson.Sec6.I1431
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.BlocksAbstract
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadBlocks
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadEigen
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslSplit
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Inner
import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleCommutator

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.CALinearPrimary

private noncomputable def actRestrict {R : Type} [Group R] (A : Subgroup (MulAut R))
    (J : Subgroup R) (h : ∀ a ∈ A, ∀ j ∈ J, (a : MulAut R) j ∈ J) : A →* MulAut ↥J where
  toFun a :=
    { toFun := fun j => ⟨(a : MulAut R) j.1, h a a.2 j.1 j.2⟩
      invFun := fun j => ⟨((a : MulAut R)⁻¹) j.1, h a⁻¹ (a⁻¹).2 j.1 j.2⟩
      left_inv := by
        intro j; ext
        exact (a : MulAut R).symm_apply_apply j.1
      right_inv := by
        intro j; ext
        exact (a : MulAut R).apply_symm_apply j.1
      map_mul' := by
        intro j k; ext
        exact map_mul (a : MulAut R) j.1 k.1 }
  map_one' := by
    ext j; rfl
  map_mul' := by
    intro a b; ext j; rfl

private lemma slKerEquiv_conjNormal {K : Type} [Field K] {N : ℕ} (d : GL (Fin N) K)
    (h : ↥(LargeEvenSLGroup (Fin N) K)) :
    TypeA.slKerEquiv N K ((MulAut.conjNormal (H := LargeEvenSLGroup (Fin N) K) d) h) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K d (TypeA.slKerEquiv N K h) := by
  haveI : (LargeEvenSLGroup (Fin N) K).Normal := TableB.largeEvenSLGroup_normal (Fin N) K
  ext1
  rw [TypeA.coe_slKerEquiv, MulAut.conjNormal_apply]
  have hto := CFSG.StandardType.LinUnitL.toGL_slConjugation (K := K) (d := N) d
    (TypeA.slKerEquiv N K h)
  have hcoe : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N K d
      (TypeA.slKerEquiv N K h) : Matrix.SpecialLinearGroup (Fin N) K) :
        Matrix (Fin N) (Fin N) K) =
      d * ((TypeA.slKerEquiv N K h : Matrix.SpecialLinearGroup (Fin N) K) :
        Matrix (Fin N) (Fin N) K) * d⁻¹ :=
    congrArg (fun x : GL (Fin N) K => (x : Matrix (Fin N) (Fin N) K)) hto
  rw [hcoe, TypeA.coe_slKerEquiv]
  rfl

private lemma recipeEquiv_graphAut {K : Type} [Field K] {N : ℕ} {d : GL (Fin N) K}
    {δ' : MulAut (PSLg N K)}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ') :
    MulAut.congr (TypeA.recipeEquiv N K) δ' = LinearFlag.conjAut N K d := by
  haveI : (LargeEvenSLGroup (Fin N) K).Normal := TableB.largeEvenSLGroup_normal (Fin N) K
  ext x
  obtain ⟨m, rfl⟩ := LinearFlag.proj_surjective N K x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, LinearFlag.conjAut_proj]
  have hs : (TypeA.recipeEquiv N K).symm (LinearFlag.proj N K m) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) ((TypeA.slKerEquiv N K).symm m) := by
    rw [MulEquiv.symm_apply_eq, TypeA.recipeEquiv_mk, MulEquiv.apply_symm_apply]
  have hstep := hd ((TypeA.slKerEquiv N K).symm m)
    ((MulAut.conjNormal (H := LargeEvenSLGroup (Fin N) K) d) ((TypeA.slKerEquiv N K).symm m))
    (MulAut.conjNormal_apply d _)
  rw [hs, hstep, TypeA.recipeEquiv_mk, slKerEquiv_conjNormal, MulEquiv.apply_symm_apply]

private lemma graphAut_cube_mem_scalars {K : Type} [Field K] [Finite K] {N : ℕ}
    {A : GL (Fin N) K} {φ : MulAut (PSLg N K)} (hN : 2 ≤ N)
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = A * h * A⁻¹) φ)
    (h3 : φ ^ 3 = 1) :
    A ^ 3 ∈ LargeEvenScalars (Fin N) K := by
  have hconj : LinearFlag.conjAut N K (A ^ 3) = 1 := by
    have h : MulAut.congr (TypeA.recipeEquiv N K) (φ ^ 3) =
        LinearFlag.conjAut N K (A ^ 3) := by
      rw [map_pow, recipeEquiv_graphAut hd, map_pow]
    rw [h3, map_one] at h
    exact h.symm
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Dickson.Sec6.exists_scalar_of_conjAut_eq_one (K := K) hN hconj
  rw [largeEvenScalars_def]
  exact ⟨c, hc⟩

theorem linShape_rank_kernel
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {Ā : Subgroup (MulAut (PSLg N K))}
    {δ' : MulAut (PSLg N K)}
    {J' : Subgroup (PSLg N K)} (hchar : CharP K 2) (hN : 2 ≤ N)
    (hR : RDatum Ā δ' J')
    {d : GL (Fin N) K}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ')
    (hdns : d ∉ LargeEvenScalars (Fin N) K)
    {lam : Ā →* Kˣ} {g : Ā → GL (Fin N) K}
    (hgraph : ∀ a : Ā, LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      (fun h h' => (h' : GL (Fin N) K) = g a * h * (g a)⁻¹) (a : MulAut (PSLg N K)))
    (hlam3 : ∀ a : Ā, (lam a) ^ 3 = 1)
    (hg : ∀ a : Ā, ((g a * d * (g a)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
          (lam a : K) • (d : Matrix (Fin N) (Fin N) K))
    {h : Polynomial K} (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K))) (hgood : IsGoodFactor d h)
    {e : PSLg N K ≃* LinearFlag.projectiveSL N K}
    (heJ : J' = Subgroup.comap e.toMonoidHom ((specialFactor d h).map (LinearFlag.proj N K)))
    {E : Type} [Field E] [Finite E] (hcharE : CharP E 2) {m : ℕ}
    (hm : m = 2)
    (hmult : m = primaryMultiplicity (glA d : Module.End K (Fin N → K)) h)
    (hmE : 4 ≤ Nat.card E)
    {f : Matrix.SpecialLinearGroup (Fin m) E →* ↥J'}
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center _)
    (hpgl : ∀ B : Subgroup (MulAut (PSLg 2 E)),
      B ≤ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) E)) Set.univ →
      IsElemAbelian 3 B → Nat.card B ≤ 3) :
    Nat.card (lam.ker) ≤ 9 := by
  subst hm
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 := hchar
  have hδ'3 : δ' ^ 3 = 1 :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma27.pow_eq_one_of_isElemAbelian hR.elem hR.mem
  have hd3 : d ^ 3 ∈ LargeEvenScalars (Fin N) K := graphAut_cube_mem_scalars hN hd hδ'3
  rw [largeEvenScalars_def] at hd3
  obtain ⟨c, hc⟩ := hd3
  have hsq : Squarefree (minpoly K (glA d : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA (p := 3)
      (by
        have h3 : ((3 : ℕ) : K) ≠ 0 := by
          intro h
          rw [CharP.cast_eq_zero_iff K 2 3] at h
          norm_num at h
        simpa using h3) hc.symm
  let canonMap : Matrix.SpecialLinearGroup (Fin N) K →* PSLg N K :=
    (TypeA.recipeEquiv N K).symm.toMonoidHom.comp (LinearFlag.proj N K)
  let Jcan : Subgroup (PSLg N K) := (specialFactor d h).map canonMap
  have hcompat : MulAut.congr (TypeA.recipeEquiv N K) δ' = LinearFlag.conjAut N K d :=
    recipeEquiv_graphAut hd
  have hfix : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (LinearFlag.conjAut N K d)).map
      (TypeA.recipeEquiv N K).symm.toMonoidHom = ggAutFixedSubgroup δ' := by
    ext y
    rw [Subgroup.mem_map, mem_ggAutFixedSubgroup]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : LinearFlag.conjAut N K d z = z := hz
      have h := congrArg (fun f : MulAut (LinearFlag.projectiveSL N K) => f z) hcompat
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hz'] at h
      exact (TypeA.recipeEquiv N K).injective
        (h.trans ((TypeA.recipeEquiv N K).apply_symm_apply z).symm)
    · intro hy
      have hy' : δ' y = y := hy
      refine ⟨(TypeA.recipeEquiv N K) y, ?_, (TypeA.recipeEquiv N K).symm_apply_apply y⟩
      have h := congrArg (fun f : MulAut (LinearFlag.projectiveSL N K) =>
        f ((TypeA.recipeEquiv N K) y)) hcompat.symm
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply] at h
      rw [MulEquiv.symm_apply_apply, hy'] at h
      exact h
  have hKcan : CFSG.Open.IsComponentOf ((specialFactor d h).map (LinearFlag.proj N K))
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (LinearFlag.conjAut N K d)) :=
    CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin.isComponentOf_map_specialFactor hsq hh hgood
  have hJcan : CFSG.Open.IsComponentOf Jcan (ggAutFixedSubgroup δ') := by
    have h := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv
      (TypeA.recipeEquiv N K).symm hKcan
    rw [hfix, Subgroup.map_map] at h
    exact h
  have hcomp : CFSG.Assembly.IsComponentOf Jcan (ggAutFixedSubgroup δ') := by
    refine ⟨hJcan.1, ?_, ?_⟩
    · rw [CFSG.StandardType.ggAssemblyIsSubnormal_iff hJcan.1]
      exact (CFSG.Open.IsSubnormal.iff_subgroupOf hJcan.1).mp hJcan.2.1
    · exact hJcan.2.2
  have hJ'eq : J' = Jcan := (hR.uniq Jcan hcomp).symm
  let φ : Ā →* MulAut ↥J' := actRestrict Ā J' hR.norm
  have hinner : ∀ a : Ā, a ∈ lam.ker → φ a ∈ Set.range (MulAut.conj : ↥J' →* MulAut ↥J') := by
    intro a ha
    have hlam1 : lam a = 1 := MonoidHom.mem_ker.mp ha
    have hcomm : g a * d = d * g a := by
      have h := hg a
      rw [hlam1] at h
      simp only [Units.val_one, one_smul] at h
      have hgl : (g a * d * (g a)⁻¹ : GL (Fin N) K) = d :=
        Matrix.GeneralLinearGroup.ext (fun i j => by rw [h])
      calc g a * d = (g a * d * (g a)⁻¹) * g a := by group
        _ = d * g a := by rw [hgl]
    have ha3 : (a : MulAut (PSLg N K)) ^ 3 = 1 := by
      have h := hR.elem.2 (a : Ā) (a : Ā).2
      exact h
    have h3 : (g a) ^ 3 ∈ LargeEvenScalars (Fin N) K :=
      graphAut_cube_mem_scalars hN (hgraph a) ha3
    rw [largeEvenScalars_def] at h3
    obtain ⟨ν, hν⟩ := h3
    have hm2 : primaryMultiplicity (glA d : Module.End K (Fin N → K)) h = 2 := hmult.symm
    obtain ⟨s, hs, hsc⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.I1431.key_specialFactor hsq hh hm2 hcomm hν.symm
    refine ⟨⟨canonMap s, ?_⟩, ?_⟩
    · rw [hJ'eq]; exact Subgroup.mem_map_of_mem canonMap hs
    · ext y
      have hyJcan : y.1 ∈ Jcan := by rw [← hJ'eq]; exact y.2
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hyJcan
      have hy_eq : y = ⟨canonMap m, hJ'eq ▸ Subgroup.mem_map_of_mem canonMap hm⟩ :=
        Subtype.ext hmy.symm
      rw [hy_eq]
      have hae : (a : MulAut (PSLg N K))
            ((TypeA.recipeEquiv N K).symm (LinearFlag.proj N K m)) =
          (TypeA.recipeEquiv N K).symm
            (LinearFlag.conjAut N K (g a) (LinearFlag.proj N K m)) := by
        have h := congrArg (fun f : MulAut (LinearFlag.projectiveSL N K) =>
          f (LinearFlag.proj N K m)) (recipeEquiv_graphAut (hgraph a))
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply] at h
        rw [← h, MulEquiv.symm_apply_apply]
      change canonMap s * canonMap m * (canonMap s)⁻¹ =
        (a : MulAut (PSLg N K)) (canonMap m)
      have hmae : (a : MulAut (PSLg N K)) (canonMap m) = canonMap (s * m * s⁻¹) := by
        rw [show canonMap m = (TypeA.recipeEquiv N K).symm (LinearFlag.proj N K m) from rfl, hae,
          LinearFlag.conjAut_proj, hsc m hm]
        rfl
      rw [hmae]
      simp only [map_mul, map_inv]
  have hcenter_le : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E) ≤ ⊥ := by
    intro z hz
    rw [Subgroup.mem_bot]
    exact CFSG.StandardType.PsiDiag.sl2_eq_one_of_mem_center hz
  have hf_inj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hker.trans hcenter_le)
  let fEquiv : Matrix.SpecialLinearGroup (Fin 2) E ≃* ↥J' := MulEquiv.ofBijective f ⟨hf_inj, hf⟩
  have hproj_ker : (LinearFlag.proj 2 E).ker = ⊥ := by
    rw [LinearFlag.ker_proj, LinearCover.scalars_two_eq_bot]
  let gEquiv : Matrix.SpecialLinearGroup (Fin 2) E ≃* PSLg 2 E :=
    (MulEquiv.ofBijective (LinearFlag.proj 2 E)
      ⟨(MonoidHom.ker_eq_bot_iff _).mp hproj_ker, LinearFlag.proj_surjective 2 E⟩).trans
      (TypeA.recipeEquiv 2 E).symm
  let α : ↥J' ≃* PSLg 2 E := fEquiv.symm.trans gEquiv
  have hcongr_conj : ∀ x : ↥J', MulAut.congr α (MulAut.conj x) = MulAut.conj (α x) := by
    intro x; ext y
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.conj_apply,
      MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hconj_mem : ∀ r : PSLg 2 E,
      MulAut.conj r ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) E)) Set.univ := by
    intro r
    obtain ⟨S, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin 2) E).subgroupOf (LargeEvenSLGroup (Fin 2) E)) r
    refine ⟨(S : GL (Fin 2) E), Set.mem_univ _, ?_⟩
    intro h h' hh
    simp only [MulAut.conj_apply, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext hh.symm
  let B : Subgroup (MulAut (PSLg 2 E)) :=
    ((lam.ker).map φ).map (MulAut.congr α).toMonoidHom
  have hB_le : B ≤
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) E)) Set.univ := by
    intro b hb
    change b ∈ ((lam.ker).map φ).map (MulAut.congr α).toMonoidHom at hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    rw [Subgroup.mem_map] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    obtain ⟨x, hx⟩ := hinner a ha
    rw [← hx]
    change MulAut.congr α (MulAut.conj x) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) E)) Set.univ
    rw [hcongr_conj]
    exact hconj_mem (α x)
  have hea_ker : IsElemAbelian 3 (lam.ker : Subgroup Ā) := by
    refine ⟨?_, ?_⟩
    · letI : IsMulCommutative ↥Ā := hR.elem.1
      infer_instance
    · intro x _
      exact Subtype.ext (hR.elem.2 (x : Ā) (x.2))
  have hB_ea : IsElemAbelian 3 B :=
    CFSG.StandardType.ggIsElemAbelian_map
      (CFSG.StandardType.ggIsElemAbelian_map hea_ker φ)
      (MulAut.congr α).toMonoidHom
  have hB_card : Nat.card B ≤ 3 := hpgl B hB_le hB_ea
  let ψ : ↥(lam.ker) →* MulAut ↥J' :=
    φ.comp (Subgroup.topEquiv.toMonoidHom.comp (Subgroup.inclusion le_top))
  have hψ_range : ψ.range = (lam.ker).map φ := by
    ext b; constructor
    · intro hb; rw [MonoidHom.mem_range] at hb; obtain ⟨a, rfl⟩ := hb
      exact ⟨a, a.2, rfl⟩
    · intro hb; rw [Subgroup.mem_map] at hb; obtain ⟨a, ha, rfl⟩ := hb
      exact MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
  have hψ_ker : ψ.ker ≤ ((Subgroup.zpowers δ').subgroupOf Ā).subgroupOf lam.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [MonoidHom.mem_ker] at hx
    refine hR.ker (x : Ā) (x.1).2 (fun j hj => ?_)
    have hxj : ψ x = 1 := hx
    have := congrArg (fun f : MulAut ↥J' => f ⟨j, hj⟩) hxj
    rw [MulAut.one_apply] at this
    exact congrArg Subtype.val this
  have hker_card : Nat.card ψ.ker ≤ 3 := by
    have hinj : Function.Injective (fun x : ↥(ψ.ker) =>
        (⟨((x : ↥(lam.ker)) : Ā),
          Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (hψ_ker x.2))⟩ :
          Subgroup.zpowers δ')) := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
    have h1 : Nat.card ↥(ψ.ker) ≤ Nat.card ↥(Subgroup.zpowers δ') :=
      Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card ↥(Subgroup.zpowers δ') ≤ 3 := by
      by_cases h1 : δ' = 1
      · rw [Subgroup.zpowers_eq_bot.mpr h1]
        simp
      · rw [CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6Gen.card_zpowers_of_pow_eq_one
          (p := 3) Nat.prime_three hδ'3 h1]
    exact h1.trans h2
  have hmap_card : Nat.card ((lam.ker).map φ) = Nat.card B :=
    (Subgroup.card_map_of_injective (K := (lam.ker).map φ)
      (MulAut.congr α).injective).symm
  calc Nat.card (lam.ker)
      = Nat.card ψ.range * Nat.card ψ.ker := (TableB.card_range_mul_card_ker ψ).symm
    _ = Nat.card ((lam.ker).map φ) * Nat.card ψ.ker := by rw [hψ_range]
    _ = Nat.card B * Nat.card ψ.ker := by rw [hmap_card]
    _ ≤ 3 * 3 := Nat.mul_le_mul hB_card hker_card
    _ = 9 := by norm_num

end CFSG.StandardType.TablePThreeKG

end

