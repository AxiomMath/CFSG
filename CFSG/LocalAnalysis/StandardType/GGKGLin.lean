module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynClassical

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem kgLin_holds :
    KGSimpleOn FamLin := by
  intro p hp hp2 S _ _ lab α K hF hlab hcen hin hαp hα1 hK k f hk hlabK
  exfalso
  have hfix : ggFixSub α = fixSubgroup α := by ext x; rfl
  rw [hfix] at hK
  have hKo : CFSG.Open.IsComponentOf K (fixSubgroup α) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hK
  classical
  obtain ⟨F, hF', hFf, d, hd, hcard, A, u, e, hαu, hu⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.innDiag_linear_data hcen hF hin
  have h2 : (2 : F) = 0 := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.two_eq_zero_of_card hcard
  have hue : MulAut.congr e α = u := by
    ext z
    obtain ⟨l, rfl⟩ := e.surjective z
    show e (α (e.symm (e l))) = u (e l)
    rw [MulEquiv.symm_apply_apply]
    exact hαu l
  have hupow : u ^ p = 1 := by rw [← hue, ← map_pow, hαp, map_one]
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.isScalar_of_pow_trivial
    h2 A p u hu hupow
  have hodd := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 hd A
    (hp.odd_of_ne_two hp2) hc
  have hord := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  have hJ' := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport e α hKo
  rw [hue] at hJ'
  obtain ⟨M, hM, hMJ⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.exists_isComponentOf_lift
    (LargeEvenProjMk (StatedSL d F)) (QuotientGroup.mk'_surjective _)
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.conjSL A) u
    (fun x => (hu x (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.conjSL A x) rfl).symm) hJ'
  have hMinj : Function.Injective (StatedSL d F).subtype := Subtype.val_injective
  have hM' : CFSG.Open.IsComponentOf (M.map (StatedSL d F).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) F)) ⊓ StatedSL d F) := by
    rw [← CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.map_fixSubgroup_conjSL A]
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map _ (fun g hg => ?_) hM
    rw [show g = 1 from hMinj (by simpa using hg)]
    exact one_mem _
  obtain ⟨a, E, hEf, hEalg, hEfin, ha, ⟨eM⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.held_linear_components_gl
      CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds A hord _ hM'
  obtain ⟨eJM⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.nonempty_centerQuot_of_map_eq
    (LargeEvenProjMk (StatedSL d F))
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center hM.2.2.1 hMJ
  obtain ⟨eMZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
    (Subgroup.equivMapOfInjective M _ hMinj)
  letI := hEf
  letI := hEalg
  obtain ⟨kE, hkE⟩ := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.exists_card_eq_two_pow
    (F := F) (E := E) h2
  have hlabK' : GGHasLabel ⟨.C, k, f⟩
      ((K.map e.toMonoidHom) ⧸ Subgroup.center (K.map e.toMonoidHom)) :=
    ggHasLabel_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center K) (Subgroup.center (K.map e.toMonoidHom))
        (K.equivMapOfInjective e.toMonoidHom e.injective) (Subgroup.map_center_eq _))
      hlabK
  exact kg_false_of_quot_sl hJ'.2.2 ha hkE ⟨(eJM.trans eMZ).trans eM⟩ hk hlabK'

end CFSG.StandardType.KG
