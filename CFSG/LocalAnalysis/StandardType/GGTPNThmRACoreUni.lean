module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRADescent
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeCases
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryFieldType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.Timmesfeld.Bridge.RootStructR2ManySection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SKUniComp
public import CFSG.RankThree.PartOne.S15K.CommonEigen
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.LocalAnalysis.GLTheoremA.T263.SK
open TableBU TablePThreeKG CFSG.RankThree.PartOne.KCUnitaryModel
open Polynomial Module Matrix

private theorem raUni_exists_unitary_model {p : ℕ} {X : Type} [Group X]
    {A : Subgroup (MulAut X)} {labX : LargeEvenLabel} (hA : labX.tag = .twA)
    (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ labX.n) ^ 2 ∧
      ∃ θ : X ⧸ Subgroup.center X ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin (labX.rank + 1)) K (2 ^ labX.n)),
        GGInducedInn A θ (LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin (labX.rank + 1)) K (2 ^ labX.n)))
          (LargeEvenGUSet (Fin (labX.rank + 1)) K (2 ^ labX.n))) := by
  classical
  rw [GGTPNMarked, LargeEvenMarking] at hm
  obtain ⟨-, lab, hlab, hraw⟩ := hm
  obtain ⟨t, l, n⟩ := labX
  subst hA
  obtain ⟨R, _, I, F, -, -, θ₀, hlab, -, -⟩ := largeEvenRawDatum_exists hraw
  subst hlab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfin, hcard, hQ⟩ := hraw
  obtain ⟨-, -, θ, -, hhalf, hind⟩ := hQ
  exact ⟨K, hKfield, hKfin, hcard, θ, hind⟩

private theorem raUni_exists_unitary_lift {N n : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] {σ : MulAut X}
    (hUF : UnitaryFieldData 2 n K)
    {θ : X ⧸ Subgroup.center X ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    (hσI : ggInducedAut θ σ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      (LargeEvenGUSet (Fin N) K (2 ^ n))) :
    ∃ d ∈ primeFormUnitary hUF (idGram K N), IsConjBy d (ggInducedAut θ σ) := by
  classical
  have hS : LargeEvenGUSet (Fin N) K (2 ^ n) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer (d := N) hUF
  obtain ⟨M, hM, hMeq⟩ := TableB.exists_eq_projConj hS hσI
  obtain ⟨u, hu⟩ := TableBU63.exists_unitary_of_gu (n := n) (d := N) hUF hM
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin N) u * M, hu, ?_⟩
  intro g g' hgg'
  rw [hMeq]
  show (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      ((LargeEvenSUGroup (Fin N) K (2 ^ n)).normalizerMonoidHom ⟨M, hS hM⟩ g) =
    (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n))) g'
  congr 1
  apply Subtype.ext
  show M * (g : GL (Fin N) K) * M⁻¹ = (g' : GL (Fin N) K)
  rw [hgg', InndiagSU.scalar_mul_conj]

private theorem raUni_projConj_eq_of_isConjBy {N n : ℕ} {K : Type} [Field K] {d : GL (Fin N) K}
    (hN : d ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)))
    {δ' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))}
    (hδ : IsConjBy d δ') :
    δ' = TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨d, hN⟩ := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ n))) x
  show δ' ((g : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))) =
    TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨d, hN⟩
      (g : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))
  rw [TableB.projConj_mk]
  exact hδ g _ rfl

private theorem raUni_pow_scalar_of_isConjBy {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hN3 : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    {δ' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))}
    (hδ : IsConjBy d δ') (hδp : δ' ^ p = 1) :
    ∃ c : Kˣ, d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
  classical
  have hdGU : d ∈ LargeEvenGUSet (Fin N) K (2 ^ n) :=
    TableBUD.mem_guSet_of_mem_primeFormUnitary hUF hd
  have hN : d ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer (d := N) hUF hdGU
  have hδeq := raUni_projConj_eq_of_isConjBy hN hδ
  have hpow : TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n))
      (⟨d, hN⟩ ^ p) = 1 := by
    rw [map_pow, ← hδeq, hδp]
  have hscal := TableBUE.mem_scalars_of_projConj_eq_one (h := hUF) hK hN3 hNq hp hpq hpow
  rw [largeEvenScalars_def] at hscal
  obtain ⟨c, hc⟩ := hscal
  refine ⟨c, ?_⟩
  change Matrix.GeneralLinearGroup.scalar (Fin N) c = d ^ p at hc
  exact hc.symm

private theorem raUni_component_unique {p N n : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] {σ : MulAut X}
    (hUF : UnitaryFieldData 2 n K) (hN1 : 1 ≤ N)
    {θ : X ⧸ Subgroup.center X ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    {Jbar : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))}
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hTJ : T = Jbar.map (InndiagSU.projEquiv hUF hN1).toMonoidHom)
    (hfix : Subgroup.map (InndiagSU.projEquiv hUF hN1).toMonoidHom
        (ggAutFixedSubgroup (ggInducedAut θ σ)) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩))
    (huniqJ : ∀ Q : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))),
      CFSG.Assembly.IsComponentOf Q (ggAutFixedSubgroup (ggInducedAut θ σ)) →
      p ∣ Nat.card Q → Q = Jbar) :
    ∀ Q : Subgroup (primeFormP hUF (idGram K N)),
      CFSG.Open.IsComponentOf Q
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) →
      p ∣ Nat.card Q → Q = T := by
  classical
  let e := InndiagSU.projEquiv hUF hN1
  let δ' := ggInducedAut θ σ
  intro Q hQ hQp
  have hQ' : CFSG.Assembly.IsComponentOf (Q.map e.symm.toMonoidHom)
      (ggAutFixedSubgroup δ') := by
    have hcompQ : CFSG.Assembly.IsComponentOf Q
        (Subgroup.map e.toMonoidHom (ggAutFixedSubgroup δ')) := by
      rw [hfix]
      exact (CFSG.Assembly.isComponentOf_iff_open).mpr hQ
    have hmap : CFSG.Assembly.IsComponentOf (Q.map e.symm.toMonoidHom)
        ((Subgroup.map e.toMonoidHom (ggAutFixedSubgroup δ')).map e.symm.toMonoidHom) :=
      ⟨Subgroup.map_mono hcompQ.1,
        CFSG.Assembly.IsSubnormal.map e.symm.toMonoidHom hcompQ.2.1,
        CFSG.Assembly.IsQuasisimple.of_mulEquiv
          (Subgroup.equivMapOfInjective Q e.symm.toMonoidHom e.symm.injective).symm
          hcompQ.2.2⟩
    have hcancel : (Subgroup.map e.toMonoidHom (ggAutFixedSubgroup δ')).map
        e.symm.toMonoidHom = ggAutFixedSubgroup δ' := by
      rw [Subgroup.map_map]
      have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    rwa [hcancel] at hmap
  have hQp' : p ∣ Nat.card (Q.map e.symm.toMonoidHom) := by
    have hc : Nat.card (Q.map e.symm.toMonoidHom) = Nat.card Q :=
      (Nat.card_congr (Subgroup.equivMapOfInjective Q e.symm.toMonoidHom
        e.symm.injective).toEquiv).symm
    rwa [hc]
  have hEq := huniqJ _ hQ' hQp'
  have h1 : (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  rw [← h1, hEq]
  exact hTJ.symm

private theorem raUni_component_primeForm_basic {N n : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] {σ : MulAut X} {J : Subgroup X}
    (hX : commutator X = ⊤) (hN1 : 1 ≤ N)
    (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup σ))
    (hUF : UnitaryFieldData 2 n K)
    {θ : X ⧸ Subgroup.center X ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdconj : IsConjBy d (ggInducedAut θ σ)) :
    ∃ T : Subgroup (primeFormP hUF (idGram K N)),
      Subgroup.map (InndiagSU.projEquiv hUF hN1).toMonoidHom
          (ggAutFixedSubgroup (ggInducedAut θ σ)) =
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩) ∧
      T = (J.map (TablePThreeKG.proj θ)).map
        (InndiagSU.projEquiv hUF hN1).toMonoidHom ∧
      CFSG.Open.IsComponentOf T
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥T ⧸ Subgroup.center ↥T) := by
  classical
  let e : LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ≃*
      primeFormP hUF (idGram K N) := InndiagSU.projEquiv hUF hN1
  let δ' : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) := ggInducedAut θ σ
  let Jbar : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) :=
    J.map (TablePThreeKG.proj θ)
  let T : Subgroup (primeFormP hUF (idGram K N)) := Jbar.map e.toMonoidHom
  obtain ⟨hJbar, hisoJ⟩ := ggTPNComponent_map_proj_congr hX hJ θ
  have hfix : Subgroup.map e.toMonoidHom (ggAutFixedSubgroup δ') =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩) := by
    ext y
    rw [Subgroup.mem_map_equiv]
    have h := TablePThreeKG.uni_cube_fixSubgroup_projEquiv hUF hN1 hdconj hd (e.symm y)
    simpa only [e, MulEquiv.apply_symm_apply] using h
  have hfixcongr : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (MulAut.congr e δ') =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
    exact hfix
  have hcomp : CFSG.Assembly.IsComponentOf T
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.congr e δ')) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr]
    refine ⟨Subgroup.map_mono hJbar.1, CFSG.Assembly.IsSubnormal.map e.toMonoidHom hJbar.2.1, ?_⟩
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective Jbar e.toMonoidHom e.injective).symm hJbar.2.2
  have hT : CFSG.Open.IsComponentOf T
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) := by
    rw [← hfixcongr, ← CFSG.Assembly.isComponentOf_iff_open]
    exact hcomp
  let eJ : Jbar ≃* Jbar.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective Jbar e.toMonoidHom e.injective
  have hcenter : (Subgroup.center Jbar).map eJ.toMonoidHom =
      Subgroup.center (Jbar.map e.toMonoidHom) := Subgroup.map_center_eq eJ
  exact ⟨T, hfix, rfl, hT, ⟨hisoJ.some.trans (QuotientGroup.congr _ _ eJ hcenter)⟩⟩

private theorem raUni_component_primeForm {p N n : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hp : p.Prime) (hX : commutator X = ⊤) (hN1 : 1 ≤ N)
    (hloc : GGTPNLocalCore p A σ J) (h8 : GGTPNOnlyComp p σ J)
    (hUF : UnitaryFieldData 2 n K)
    {θ : X ⧸ Subgroup.center X ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdconj : IsConjBy d (ggInducedAut θ σ)) :
    ∃ (Jbar : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))))
      (T : Subgroup (primeFormP hUF (idGram K N))),
      CFSG.Assembly.IsComponentOf Jbar (ggAutFixedSubgroup (ggInducedAut θ σ)) ∧
      T = Jbar.map (InndiagSU.projEquiv hUF hN1).toMonoidHom ∧
      CFSG.Open.IsComponentOf T
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) ∧
      (∀ Q : Subgroup (primeFormP hUF (idGram K N)),
        CFSG.Open.IsComponentOf Q
          (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
            (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) →
        p ∣ Nat.card Q → Q = T) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥T ⧸ Subgroup.center ↥T) := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hfix, hTJ, hT, hiso⟩ :=
    raUni_component_primeForm_basic hX hN1 hloc.2.2.2.1 hUF hd hdconj
  let Jbar : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))) :=
    J.map (TablePThreeKG.proj θ)
  have hdes := ggTPNOnlyComp_map_proj hX hloc.2.2.2.1 h8 θ
  have huniq := raUni_component_unique (hUF := hUF) (hN1 := hN1)
    (hd := hd) (Jbar := Jbar) (T := T) hTJ hfix hdes.2.1
  exact ⟨Jbar, T, hdes.1, hTJ, hT, huniq, hiso⟩

private theorem raUni_nonSplit_label_A {p N n : ℕ} {K F : Type} [Field K] [Finite K]
    [Field F] [Fintype F] (hUF : UnitaryFieldData 2 n K) (hnp3 : 3 ≤ n * p)
    (hcardF : Fintype.card F = 2 ^ (n * p))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    {g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    LargeEvenInLambda2 ⟨.A, 1, p * n⟩ ∧
      GGHasLabel ⟨.A, 1, p * n⟩ (↥T ⧸ Subgroup.center ↥T) := by
  have hcardF' : Nat.card F = 2 ^ (n * p) := by
    rw [Nat.card_eq_fintype_card, hcardF]
  have h4F : 4 ≤ Nat.card F := by
    rw [hcardF']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨CFSG.Timmesfeld.Bridge.RootMany.commutator_SL2_eq_top
      (m := n * p) (by omega) hcardF'⟩
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central g hg hperf hgk
  let eZ : (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ≃*
      StatedProj (StatedSL 2 F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  have hadm : StatedLieAdmissible .PSL 2 2 (n * p) := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    · intro h1
      have h' : 2 ^ (n * p) = 2 := (Prod.mk.inj h1).2
      omega
    · intro h1
      have h' : 2 ^ (n * p) = 3 := (Prod.mk.inj h1).2
      have hdvd : 2 ∣ 2 ^ (n * p) := dvd_pow_self 2 (by omega)
      rw [h'] at hdvd
      norm_num at hdvd
  have hSC : StatedClassicalModel (↥T ⧸ Subgroup.center ↥T) .PSL 2 2 (n * p) :=
    ⟨hadm, F, inferInstance, inferInstance, hcardF', ⟨e1.symm.trans eZ⟩⟩
  exact ⟨by simpa [Nat.mul_comm] using largeEvenInLambda2_typeA hSC,
    by simpa [Nat.mul_comm] using ggHasLabel_typeA hSC⟩

private theorem raUni_nonSplit_label_twA {p N n : ℕ} {K E : Type} [Field K] [Finite K]
    [Field E] [Fintype E] (hUF : UnitaryFieldData 2 n K) (h3Np : 3 ≤ N / p)
    (hpn3 : 3 ≤ p * n) (hcardE : Fintype.card E = (2 ^ (n * p)) ^ 2)
    {T : Subgroup (primeFormP hUF (idGram K N))}
    {g : ↥(StatedSU (N / p) (2 ^ (n * p)) E) →* ↥T}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center ↥(StatedSU (N / p) (2 ^ (n * p)) E)) :
    LargeEvenInLambda2 ⟨.twA, N / p - 1, p * n⟩ ∧
      GGHasLabel ⟨.twA, N / p - 1, p * n⟩ (↥T ⧸ Subgroup.center ↥T) := by
  have hnp3 : 3 ≤ n * p := by simpa [Nat.mul_comm] using hpn3
  have hEcard' : Nat.card E = (2 ^ (n * p)) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hcardE]
  have hne : (N / p, 2 ^ (n * p)) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ (n * p) = 2 := congrArg Prod.snd h
    have h8 : 8 ≤ 2 ^ (n * p) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n * p) := Nat.pow_le_pow_right (by norm_num) hnp3
    omega
  have hqSU := (isQuasisimple_statedSU_of_card hEcard' h3Np hne).1
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central g hg hqSU.1 hgk
  have hZ := (isQuasisimple_statedSU_of_card hEcard' h3Np hne).2
  let e2 : (↥(StatedSU (N / p) (2 ^ (n * p)) E) ⧸
        Subgroup.center ↥(StatedSU (N / p) (2 ^ (n * p)) E)) ≃*
      StatedProj (StatedSU (N / p) (2 ^ (n * p)) E) :=
    QuotientGroup.quotientMulEquivOfEq hZ
  have e3 : (↥T ⧸ Subgroup.center ↥T) ≃*
      StatedProj (StatedSU (N / p - 1 + 1) (2 ^ (p * n)) E) := by
    rw [show N / p - 1 + 1 = N / p from Nat.sub_add_cancel (by omega),
      show 2 ^ (p * n) = 2 ^ (n * p) by rw [Nat.mul_comm]]
    exact e1.symm.trans e2
  have hlab : GGHasLabel ⟨.twA, N / p - 1, p * n⟩ (↥T ⧸ Subgroup.center ↥T) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA (b := N / p - 1) (m := p * n)
      (by simpa [Nat.mul_comm] using hEcard') e3
  have hΛ : LargeEvenInLambda2 ⟨.twA, N / p - 1, p * n⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA
      (le_trans (by norm_num) hpn3) (by omega)
      (fun _ => le_trans (by norm_num) hpn3)
  exact ⟨hΛ, hlab⟩

private theorem raUni_nonSplit_component {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpN : p ∣ N) (h2Np : 2 ≤ N / p)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) {c : Kˣ}
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hT : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩))) :
    (N / p = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, p * n⟩ ∧
        GGHasLabel ⟨.A, 1, p * n⟩ (↥T ⧸ Subgroup.center ↥T)) ∨
      (3 ≤ N / p ∧ LargeEvenInLambda2 ⟨.twA, N / p - 1, p * n⟩ ∧
        GGHasLabel ⟨.twA, N / p - 1, p * n⟩ (↥T ⧸ Subgroup.center ↥T)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2ne : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hUF.one_le hpq
  have hp2 : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by omega
  have hpn3 : 3 ≤ p * n := by
    calc 3 = 3 * 1 := by norm_num
      _ ≤ p * n := Nat.mul_le_mul hp3 hUF.one_le
  have hnp3 : 3 ≤ n * p := by rw [Nat.mul_comm]; exact hpn3
  have hTq : CFSG.IsQuasisimple ↥T :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native T).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open T).mpr hT.2.2)
  obtain ⟨-, -, -, hcase⟩ :=
    unitary_fieldType_component (p := p) (ℓ := 2) (f := n) (n := N) hp hUF
      (TableBU.ne_two_of_dvd_two_pow_add_one hUF.one_le hpq)
      ⟨d, hd⟩ hdp hc hT
  rcases hcase with ⟨hNp2, F, hF, hFt, hcardF, g, hg, hgk⟩ |
    ⟨h3Np, E, hE, hEt, hcardE, g, hg, hgk⟩
  · letI : Field F := hF
    letI : Fintype F := hFt
    exact Or.inl ⟨hNp2, raUni_nonSplit_label_A (hUF := hUF) hnp3 hcardF hg hgk⟩
  · letI : Field E := hE
    letI : Fintype E := hEt
    exact Or.inr ⟨h3Np, raUni_nonSplit_label_twA (hUF := hUF) h3Np hpn3 hcardE hg hgk⟩

private theorem raUni_frame_diag_contradiction {p N : ℕ} {K : Type} [Field K]
    (hN : 0 < N) {P M d : GL (Fin N) K} {u c : Kˣ}
    (hMdiag : ((P⁻¹ * M * P : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).IsDiag)
    (hM_eq : M = Matrix.GeneralLinearGroup.scalar (Fin N) u * d)
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K)) : False := by
  have hDdiag : ((P⁻¹ * d * P : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K).IsDiag := by
    have hcu : ∀ v : Kˣ, P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin N) v =
        Matrix.GeneralLinearGroup.scalar (Fin N) v * P⁻¹ := fun v =>
      Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin N) v) P⁻¹
    have hGL : (P⁻¹ * M * P : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) u * (P⁻¹ * d * P : GL (Fin N) K) := by
      rw [hM_eq]
      calc P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin N) u * d) * P =
          (P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin N) u) * d * P := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin N) u * P⁻¹) * d * P := by rw [← hcu u]
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) u * (P⁻¹ * d * P) := by group
    rw [hGL, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at hMdiag
    intro i j hij
    have h0 := hMdiag (i := i) (j := j) hij
    change (Matrix.diagonal (fun _ : Fin N => (u : K)) *
      ((P⁻¹ * d * P : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) i j = 0 at h0
    rw [← Matrix.smul_eq_diagonal_mul, Matrix.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (Units.ne_zero u)
  have hDp : (P⁻¹ * d * P : GL (Fin N) K) ^ p =
      Matrix.GeneralLinearGroup.scalar (Fin N) c := by
    have hcomm : Matrix.GeneralLinearGroup.scalar (Fin N) c * P =
        P * Matrix.GeneralLinearGroup.scalar (Fin N) c :=
      (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin N) c) P).symm
    rw [show (P⁻¹ * d * P : GL (Fin N) K) = MulAut.conj (P⁻¹) d by
      rw [MulAut.conj_apply, inv_inv]]
    rw [← map_pow, hdp, MulAut.conj_apply, inv_inv]
    calc (P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin N) c) * P =
        P⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin N) c * P) := by group
      _ = P⁻¹ * (P * Matrix.GeneralLinearGroup.scalar (Fin N) c) := by rw [hcomm]
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) c := by group
  have hDp_mat : ((P⁻¹ * d * P : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) ^ p = Matrix.scalar (Fin N) (c : K) := by
    have h := congrArg (fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K)) hDp
    simpa [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] using h
  let i : Fin N := ⟨0, hN⟩
  have hii : (((P⁻¹ * d * P : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) i i) ^ p = (c : K) := by
    have h := congrFun (congrFun hDp_mat i) i
    rw [← hDdiag.diagonal_diag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq,
      Pi.pow_apply, Matrix.diag_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
    exact h
  exact hc _ hii

private theorem raUni_nonSplit_bound_elemAbelian {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hN3 : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2))
    {Ab : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))))}
    (hAb : IsElemAbelian p Ab)
    (hAbI : ∀ a ∈ Ab, a ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      (LargeEvenGUSet (Fin N) K (2 ^ n)))
    {aa : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n)))} (haa : aa ∈ Ab)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    {hNd : d ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K))}
    (hdconj : aa = TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨d, hNd⟩)
    {c : Kˣ} (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K)) :
    Nat.card Ab ≤ p ^ (N / p + 1) := by
  classical
  by_contra hle
  push Not at hle
  haveI : Fact p.Prime := ⟨hp⟩
  have hApg : IsPGroup p Ab := hAb.isPGroup
  obtain ⟨t, ht⟩ := hApg.exists_card_eq
  have ht2 : p ^ (N / p + 2) ≤ Nat.card Ab := by
    rw [ht]
    apply Nat.pow_le_pow_right hp.pos
    have h : N / p + 1 < t := by
      rw [ht] at hle
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hle
    omega
  obtain ⟨P, hP, hframe⟩ :=
    TableBUD.exists_unitary_frame hUF hcard hN3 hNq hp hpq hAb hAbI ht2
  obtain ⟨M, hM, hMdiag, hMeq⟩ := hframe aa haa
  have hNdM : M ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer (d := N) hUF hM
  have hMeq'' : aa = TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨M, hNdM⟩ := hMeq
  have hMeq' : TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨M, hNdM⟩ =
      TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨d, hNd⟩ := by
    rw [← hMeq'', hdconj]
  have hprod : TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n))
      (⟨M, hNdM⟩ * (⟨d, hNd⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, hMeq']
    exact mul_inv_cancel _
  have hscal := TableBUE.mem_scalars_of_projConj_eq_one (h := hUF) hcard hN3 hNq hp hpq hprod
  rw [largeEvenScalars_def] at hscal
  obtain ⟨u, hu⟩ := hscal
  have hu' : M * d⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) u := hu.symm
  have hM_eq : M = Matrix.GeneralLinearGroup.scalar (Fin N) u * d := by
    rw [← hu']; group
  exact raUni_frame_diag_contradiction (p := p) (hN := by omega)
    hMdiag hM_eq hdp hc

private theorem raUni_two_pow_le_of_dvd {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n + 1) : 2 ≤ 2 ^ n := by
  have h1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at hpq
      norm_num at hpq
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpq)
    · exact h
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1

private theorem raUni_two_pow_sq_sub_one (n : ℕ) :
    (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
  rw [mul_comm, ← Nat.sq_sub_sq (2 ^ n) 1]

private theorem raUni_primaryFactor_linear {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hdp : d ^ p = 1)
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))) :
    ∃ μ : K, a = X - C μ := by
  have hpK : p ∣ Nat.card K - 1 := by
    rw [hcard, raUni_two_pow_sq_sub_one n]
    exact Dvd.dvd.mul_left hpq _
  obtain ⟨ω, hω⟩ := CFSG.RankThree.PartOne.S15K.exists_isPrimitiveRoot_of_dvd hp hpK
  exact exists_eq_X_sub_C_of_mem_primaryFactors hp.ne_zero hω hdp ha

private theorem raUni_primaryFactor_selfDual {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hdp : d ^ p = 1)
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))) :
    dualPoly hUF.bar a = a := by
  obtain ⟨μ, rfl⟩ := raUni_primaryFactor_linear hUF hcard hp hp2 hpq hdp ha
  have hxp : ((Matrix.GeneralLinearGroup.toLin d : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)) ^ p = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.toLin d) ^ p = 1 := by
      rw [← map_pow, hdp, map_one]
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have hdvd : (X - C μ : K[X]) ∣ X ^ p - C (1 : K) := by
    refine (mem_primaryFactors.mp ha).2.2.trans (minpoly.dvd K _ ?_)
    rw [map_sub, map_pow, aeval_X, aeval_C, hxp, map_one, sub_self]
  have hμp : μ ^ p = 1 := by
    have hroot : (X ^ p - C (1 : K)).IsRoot μ := dvd_iff_isRoot.mp hdvd
    exact sub_eq_zero.mp (by simpa using hroot)
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hμp
    exact zero_ne_one hμp
  obtain ⟨k, hk⟩ := hpq
  have hμq1 : μ ^ (2 ^ n + 1) = 1 := by rw [hk, pow_mul, hμp, one_pow]
  have hbar : hUF.bar μ = μ ^ (2 ^ n) := hUF.bar_apply μ
  have hbar0 : hUF.bar μ ≠ 0 := by rw [hbar]; exact pow_ne_zero _ hμ0
  rw [RankThree.PartOne.KCUnitaryBlock.dualPoly_X_sub_C hbar0, hbar]
  congr 2
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hμq1])


private theorem raUni_dvd_card_specialBlock {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (H : UnitaryPrimaryData hUF.bar (idForm hUF N) x)
    {a : primaryFactors (x : Module.End K (Fin N → K))}
    (hself : dualPoly hUF.bar (a : K[X]) = a) (hdeg : (a : K[X]).natDegree = 1)
    (ha : IsGoodBlock hUF x a) :
    p ∣ Nat.card (specialBlock (idForm hUF N) x (a : K[X])) := by
  have hnat : p ∣ (2 ^ n) ^ 2 - 1 := by
    rw [raUni_two_pow_sq_sub_one n]
    exact Dvd.dvd.mul_left hpq _
  have hpj : (p : ℤ) ∣ (((2 ^ n) : ℤ)) ^ 2 - (-1 : ℤ) ^ 2 := by
    have hcast : (((2 ^ n) ^ 2 - 1 : ℕ) : ℤ) = (((2 ^ n) : ℤ)) ^ 2 - (-1 : ℤ) ^ 2 := by
      rw [Nat.cast_sub (Nat.one_le_pow 2 (2 ^ n) (by positivity))]
      push_cast
      norm_num
    rw [← hcast]
    exact_mod_cast hnat
  refine dvd_card_specialBlock_selfDual (j := 2) H a hself (by norm_num) ?_ ?_
  · simpa [hdeg] using ha.1
  · simpa [hdeg, pow_one] using hpj

private theorem raUni_specialBlock_apply_eq_self {ℓ f N : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData ℓ f K} {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    {a b : K[X]} (hself : dualPoly h.bar a = a)
    (hb : b ∈ primaryFactors (x : Module.End K (Fin N → K))) (hba : b ≠ a)
    {g : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (hg : g ∈ specialBlock (idForm h N) x a) {v : Fin N → K}
    (hv : v ∈ primaryComponent x b) :
    (g : Module.End K (Fin N → K)) v = v := by
  have h1 : g ∈ supportedUnitary (idForm h N) x ({a, dualPoly h.bar a} : Set K[X]) :=
    (mem_specialBlock.mp hg).1
  exact h1.2 b hb (by simp [hself, hba]) v hv

private theorem raUni_specialBlock_commutative_of_scalar {ℓ f N : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData ℓ f K} {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (hsq : Squarefree (minpoly K (x : Module.End K (Fin N → K))))
    {a : K[X]} (hself : dualPoly h.bar a = a)
    (hcon : ∀ (g : LinearMap.GeneralLinearGroup K (Fin N → K)),
      g ∈ specialBlock (idForm h N) x a →
      ∀ v ∈ primaryComponent x a, ∃ c : K, (g : Module.End K (Fin N → K)) v = c • v) :
    ∀ g ∈ specialBlock (idForm h N) x a, ∀ g' ∈ specialBlock (idForm h N) x a,
      g * g' = g' * g := by
  intro g hg g' hg'
  have key : ∀ b ∈ primaryFactors (x : Module.End K (Fin N → K)),
      ∀ v ∈ primaryComponent x b,
      ((g * g' : LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) v =
      ((g' * g : LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) v := by
    intro b hb v hv
    by_cases hba : b = a
    · subst hba
      obtain ⟨c, hc⟩ := hcon g hg v hv
      obtain ⟨c', hc'⟩ := hcon g' hg' v hv
      have hL : ((g * g' : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) v = (c' * c) • v := by
        rw [Units.val_mul, Module.End.mul_apply, hc', LinearMap.map_smul, hc, smul_smul]
      have hR : ((g' * g : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) v = (c * c') • v := by
        rw [Units.val_mul, Module.End.mul_apply, hc, LinearMap.map_smul, hc', smul_smul]
      rw [hL, hR, mul_comm]
    · have hgv : ((g : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) v = v :=
        raUni_specialBlock_apply_eq_self hself hb hba hg hv
      have hg'v : ((g' : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) v = v :=
        raUni_specialBlock_apply_eq_self hself hb hba hg' hv
      rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
        hg'v, hgv, hg'v]
  exact Units.ext (ext_primaryComponent hsq key)

private theorem raUni_exists_nonScalarOn {ℓ f N : ℕ} {K : Type} [Field K] [Finite K]
    {h : UnitaryFieldData ℓ f K} {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (H : UnitaryPrimaryData h.bar (idForm h N) x) (hq : 2 ≤ ℓ ^ f)
    {a : primaryFactors (x : Module.End K (Fin N → K))}
    (hself : dualPoly h.bar (a : K[X]) = a) (ha : IsGoodBlock h x a) :
    ∃ g ∈ unitaryPreimageBlock h (x := x) (a : K[X]),
      ∃ v ∈ primaryComponent x (a : K[X]),
      ∀ c : K, ((toLinSU h N g : LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) v ≠ c • v := by
  by_contra hcon
  push Not at hcon
  have hconS : ∀ g ∈ specialBlock (idForm h N) x (a : K[X]),
      ∀ v ∈ primaryComponent x (a : K[X]), ∃ c : K, (g : Module.End K (Fin N → K)) v = c • v := by
    intro g hg v hv
    obtain ⟨c, hc⟩ := hcon ((specialBlockEquiv h H a hq ha).symm ⟨g, hg⟩)
      ((specialBlockEquiv h H a hq ha).symm ⟨g, hg⟩).2 v hv
    refine ⟨c, ?_⟩
    have h2 : ((specialBlockEquiv h H a hq ha ((specialBlockEquiv h H a hq ha).symm ⟨g, hg⟩) :
        ↥(specialBlock (idForm h N) x (a : K[X]))) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) = g := by
      rw [MulEquiv.apply_symm_apply]
    rw [← h2, specialBlockEquiv_apply_coe h H a hq ha]
    exact hc
  have hcommS := raUni_specialBlock_commutative_of_scalar (h := h) (x := x) H.squarefree
    hself hconS
  have hcomm : ∀ g g' : ↥(unitaryPreimageBlock h (x := x) (a : K[X])), g * g' = g' * g := by
    intro g g'
    refine (specialBlockEquiv h H a hq ha).injective ?_
    rw [map_mul, map_mul]
    exact Subtype.ext (hcommS _ (specialBlockEquiv h H a hq ha g).2 _
      (specialBlockEquiv h H a hq ha g').2)
  have hqS : CFSG.IsQuasisimple ↥(unitaryPreimageBlock h (x := x) (a : K[X])) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (specialBlockEquiv h H a hq ha).symm
      ((specialBlockFacts_of_good H hq a ha).quasisimple ha.1)
  haveI := CFSG.LocalCores.isQuasisimple_nontrivial hqS
  have hbot : commutator ↥(unitaryPreimageBlock h (x := x) (a : K[X])) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y _
    rw [Subgroup.mem_centralizer_iff]
    intro z _
    simpa using hcomm z y
  exact (bot_ne_top : (⊥ : Subgroup ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) ≠ ⊤)
    (hbot.symm.trans hqS.1.commutator_eq_top)

private theorem raUni_primaryFactor_natDegree {p N n : ℕ} {K : Type} [Field K]
    [Finite K] (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hdp : d ^ p = 1)
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))) :
    a.natDegree = 1 := by
  obtain ⟨μ, rfl⟩ := raUni_primaryFactor_linear hUF hcard hp hp2 hpq hdp ha
  simp

private theorem raUni_card_primaryFactors_le {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hdp : d ^ p = 1) :
    (primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))).card ≤ p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hxp : ((Matrix.GeneralLinearGroup.toLin d : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)) ^ p = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.toLin d) ^ p = 1 := by
      rw [← map_pow, hdp, map_one]
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  choose r hr using fun (a : K[X]) (ha : a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
    Module.End K (Fin N → K))) => raUni_primaryFactor_linear hUF hcard hp hp2 hpq hdp ha
  have hmem : ∀ a : ↥(primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))), (r a.1 a.2) ^ p = 1 := by
    intro a
    have hdvd : (X - C (r a.1 a.2) : K[X]) ∣ X ^ p - C (1 : K) := by
      rw [← hr a.1 a.2]
      refine (mem_primaryFactors.mp a.2).2.2.trans (minpoly.dvd K _ ?_)
      rw [map_sub, map_pow, aeval_X, aeval_C, hxp, map_one, sub_self]
    have hroot : (X ^ p - C (1 : K)).IsRoot (r a.1 a.2) := dvd_iff_isRoot.mp hdvd
    exact sub_eq_zero.mp (by simpa using hroot)
  have hinj : Function.Injective (fun a : ↥(primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))) => rootsOfUnity.mkOfPowEq (r a.1 a.2) (hmem a)) := by
    intro a b hab
    have h : r a.1 a.2 = r b.1 b.2 := by
      simpa using congrArg (fun z : rootsOfUnity p K => ((z : Kˣ) : K)) hab
    exact Subtype.ext (by rw [hr a.1 a.2, hr b.1 b.2, h])
  calc (primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))).card
      = Nat.card ↥(primaryFactors (Matrix.GeneralLinearGroup.toLin d :
          Module.End K (Fin N → K))) := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ Nat.card (rootsOfUnity p K) := Nat.card_le_card_of_injective _ hinj
    _ ≤ p := card_rootsOfUnity K p

private theorem raUni_toLin_scalar_apply {N : ℕ} {K : Type} [Field K] (c : Kˣ)
    (v : Fin N → K) :
    ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin N) c) :
      LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) v = (c : K) • v := by
  ext i
  simp [Matrix.GeneralLinearGroup.coe_toLin, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mulVec_diagonal, Units.smul_def]

private theorem raUni_primeFormConjHom_eq_one_of_scalar {ℓ f n : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData ℓ f K} {A : primeFormUnitary h (idGram K n)} {c : Kˣ}
    (hA : (A : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    primeFormConjHom h (idGram K n) A = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (normOneScalars h (gramSU h (idGram K n)) n) x
  rw [QuotientGroup.mk'_apply (normOneScalars h (gramSU h (idGram K n)) n) g,
    primeFormConjHom_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show (A : GL (Fin n) K) * (g : GL (Fin n) K) * (A : GL (Fin n) K)⁻¹ = (g : GL (Fin n) K)
  rw [hA, (commute_scalar c (g : GL (Fin n) K)).eq.symm, mul_assoc, mul_inv_cancel, mul_one]

private theorem raUni_preimageBlock_quasisimple {ℓ f N : ℕ} {K : Type} [Field K]
    [Finite K] {h : UnitaryFieldData ℓ f K}
    {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (H : UnitaryPrimaryData h.bar (idForm h N) x) (hq : 2 ≤ ℓ ^ f)
    (a : primaryFactors (x : Module.End K (Fin N → K))) (ha : IsGoodBlock h x a) :
    CFSG.IsQuasisimple ↥(unitaryPreimageBlock h (x := x) (a : K[X])) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (specialBlockEquiv h H a hq ha).symm
    ((specialBlockFacts_of_good H hq a ha).quasisimple ha.1)

private theorem raUni_le_of_map_mk'_le {G : Type*} [Group G] {Z F₁ F₂ : Subgroup G}
    [Z.Normal] (hZ : Z ≤ Subgroup.center G) (hperf : Group.IsPerfect ↥F₁)
    (h : F₁.map (QuotientGroup.mk' Z) ≤ F₂.map (QuotientGroup.mk' Z)) : F₁ ≤ F₂ := by
  have hperf' : ⁅F₁, F₁⁆ = F₁ := by
    rw [← Subgroup.map_subtype_commutator F₁, hperf.commutator_eq_top, Subgroup.map_top]
    exact Subgroup.range_subtype F₁
  rw [← hperf']
  refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
  obtain ⟨g₁', hg₁', hg₁''⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem _ hg₁))
  obtain ⟨g₂', hg₂', hg₂''⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem _ hg₂))
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hg₁'' hg₂''
  have hz₁ : g₁'⁻¹ * g₁ ∈ Z := (QuotientGroup.eq).mp hg₁''
  have hz₂ : g₂'⁻¹ * g₂ ∈ Z := (QuotientGroup.eq).mp hg₂''
  have hc₁ : Commute (g₁'⁻¹ * g₁) g₂' := (Subgroup.mem_center_iff.mp (hZ hz₁) g₂').symm
  have hc₁₂ : Commute (g₁'⁻¹ * g₁) (g₂'⁻¹ * g₂) :=
    (Subgroup.mem_center_iff.mp (hZ hz₁) _).symm
  have hc₂ : Commute (g₂'⁻¹ * g₂) g₁' := (Subgroup.mem_center_iff.mp (hZ hz₂) g₁').symm
  have hcomm := commutatorElement_mul_mul' hc₁ hc₁₂ hc₂
  rw [show g₁ = g₁' * (g₁'⁻¹ * g₁) from (mul_inv_cancel_left g₁' g₁).symm,
    show g₂ = g₂' * (g₂'⁻¹ * g₂) from (mul_inv_cancel_left g₂' g₂).symm, hcomm]
  exact Subgroup.commutator_le_self F₂ (Subgroup.commutator_mem_commutator hg₁' hg₂')

private theorem raUni_components_ne {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) (hdp : d ^ p = 1)
    {a b : primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))}
    (hselfa : dualPoly hUF.bar (a : K[X]) = a)
    (hselfb : dualPoly hUF.bar (b : K[X]) = b)
    (hgood : IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) a)
    (hab : (a : K[X]) ≠ (b : K[X])) :
    unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d) (a : K[X]) ≠
      unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d) (b : K[X]) := by
  intro heq
  have H : UnitaryPrimaryData hUF.bar (idForm hUF N)
      (Matrix.GeneralLinearGroup.toLin d) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      hUF hd hp hp2 (by rw [hdp, map_one])
  have hq : 2 ≤ 2 ^ n := raUni_two_pow_le_of_dvd hp hp2 hpq
  have hqA := raUni_preimageBlock_quasisimple (h := hUF) (x :=
    Matrix.GeneralLinearGroup.toLin d) H hq a hgood
  have hle : unitaryPreimageBlock hUF (x := Matrix.GeneralLinearGroup.toLin d) (a : K[X]) ≤
      unitaryPreimageBlock hUF (x := Matrix.GeneralLinearGroup.toLin d) (b : K[X]) := by
    refine raUni_le_of_map_mk'_le (Z := unitaryNormOneScalars hUF N)
      (normOneScalars_le_center hUF _ N) hqA.1 ?_
    exact heq.le
  obtain ⟨g, hg, v, hv, hgv⟩ := raUni_exists_nonScalarOn (h := hUF) (x :=
    Matrix.GeneralLinearGroup.toLin d) H hq hselfa hgood
  have hsb : toLinSU hUF N g ∈ specialBlock (idForm hUF N)
      (Matrix.GeneralLinearGroup.toLin d) (b : K[X]) := Subgroup.mem_comap.mp (hle hg)
  have hfix : ((toLinSU hUF N g : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)) v = v :=
    raUni_specialBlock_apply_eq_self (h := hUF) (x :=
      Matrix.GeneralLinearGroup.toLin d) hselfb a.2 hab hsb hv
  exact hgv 1 (by rw [hfix, one_smul])

private theorem raUni_unique_good {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) (hdp : d ^ p = 1)
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hTonly : ∀ Q : Subgroup (primeFormP hUF (idGram K N)),
      CFSG.Open.IsComponentOf Q (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) →
      p ∣ Nat.card Q → Q = T)
    (a₀ : {a : primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)) // IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) a})
    (haT : T = unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d)
      (a₀.1 : K[X]))
    {b : primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))}
    (hb : b ≠ a₀.1) :
    ¬ IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) b := by
  intro hbgood
  have H : UnitaryPrimaryData hUF.bar (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      hUF hd hp hp2 (by rw [hdp, map_one])
  have hq : 2 ≤ 2 ^ n := raUni_two_pow_le_of_dvd hp hp2 hpq
  have hselfb : dualPoly hUF.bar (b : K[X]) = b :=
    raUni_primaryFactor_selfDual hUF hcard hp hp2 hpq hdp b.2
  have hselfa : dualPoly hUF.bar (a₀.1 : K[X]) = a₀.1 :=
    raUni_primaryFactor_selfDual hUF hcard hp hp2 hpq hdp a₀.1.2
  have hdegb : (b : K[X]).natDegree = 1 :=
    raUni_primaryFactor_natDegree hUF hcard hp hp2 hpq hdp b.2
  have hpF : p ∣ Nat.card (specialBlock (idForm hUF N)
      (Matrix.GeneralLinearGroup.toLin d) (b : K[X])) :=
    raUni_dvd_card_specialBlock hUF hp hpq H hselfb hdegb hbgood
  have hJcomp : CFSG.Open.IsComponentOf (unitaryBlockComponent hUF
      (x := Matrix.GeneralLinearGroup.toLin d) (b : K[X]))
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) :=
    isComponentOf_unitaryBlockComponent hUF (A := ⟨d, hd⟩) H hq b hbgood
  have hpZ := dvd_card_centerQuot_unitaryBlockComponent hUF (A := ⟨d, hd⟩) H hq b hbgood hp hpF
  have hpJ : p ∣ Nat.card (unitaryBlockComponent hUF
      (x := Matrix.GeneralLinearGroup.toLin d) (b : K[X])) :=
    hpZ.trans (Subgroup.card_quotient_dvd_card _)
  have hJeq : unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d) (b : K[X]) =
      unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X]) := by
    rw [← haT]
    exact hTonly _ hJcomp hpJ
  exact raUni_components_ne hUF hp hp2 hpq hd hdp hselfb hselfa hbgood
    (fun h => hb (Subtype.ext h)) hJeq

private theorem raUni_selfDual_block_field {ℓ f : ℕ} {K : Type} [Field K]
    {h : UnitaryFieldData ℓ f K} {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    {x : LinearMap.GeneralLinearGroup K V}
    (hq : 2 ≤ ℓ ^ f) (H : UnitaryPrimaryData h.bar B x)
    {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly h.bar (a : K[X]) = a) (hdeg : (a : K[X]).natDegree = 1)
    (ha : IsGoodBlock h x a) :
    (primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = ℓ ^ f ∧
          4 ≤ Fintype.card F ∧
          Nonempty (↥(specialBlock B x (a : K[X])) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (ℓ ^ f) ^ 2 ∧
        3 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) ∧
        (primaryMultiplicity (x : Module.End K V) (a : K[X]), ℓ ^ f) ≠ (3, 2) ∧
        Nonempty (↥(specialBlock B x (a : K[X])) ≃*
          ↥(StatedSU (primaryMultiplicity (x : Module.End K V) (a : K[X])) (ℓ ^ f) E))) := by
  classical
  haveI : Finite K := h.finite
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
  obtain ⟨hE, Hf, hHf, hHfl, Φ, -, -⟩ :=
    exists_selfDual_specialBlock_mulEquiv_sesqSpecialUnitary H hself
      (CFSG.RankThree.PartOne.selfDualPrimaryBlock H a hself)
  have hnum := isGoodBlock_numeric hq hself ha
  have hcardE : Fintype.card (AdjoinRoot (a : K[X])) = (ℓ ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hE.card_eq_sq, hdeg, mul_one]
  rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
  · have hm2 : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by
      have hb := ha.1
      omega
    have hV : Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := hm2
    obtain ⟨e2⟩ :=
      CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
    haveI : Finite hE.fixedField := inferInstance
    letI : Fintype hE.fixedField := Fintype.ofFinite _
    have hcardF : Fintype.card hE.fixedField = ℓ ^ f := by
      rw [← Nat.card_eq_fintype_card, hE.card_fixedField, hdeg, mul_one]
    have h4 : 4 ≤ Fintype.card hE.fixedField := by
      rw [hcardF]
      simpa [hdeg] using hnum.1 hm2
    exact Or.inl ⟨hm2, hE.fixedField, inferInstance, inferInstance, hcardF, h4, ⟨Φ.trans e2⟩⟩
  · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
    obtain ⟨e3⟩ := CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
      (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))))
        (Fin (Module.finrank (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
      (fun i j => by rw [hb i j, Matrix.one_apply])
    refine Or.inr ⟨AdjoinRoot (a : K[X]), inferInstance, inferInstance, hcardE, hm, ?_, ?_⟩
    · intro hc
      have h1 : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 3 := congrArg Prod.fst hc
      have h2 : ℓ ^ f = 2 := congrArg Prod.snd hc
      have h3 : 3 ≤ ℓ ^ f := by simpa [hdeg] using hnum.2 h1
      omega
    · rw [← show ℓ ^ (f * (a : K[X]).natDegree) = ℓ ^ f from by rw [hdeg, mul_one]]
      exact ⟨(Φ.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)⟩

private theorem raUni_eq_scalar_of_single_primaryFactor {p N n : ℕ} {K : Type} [Field K]
    [Finite K] (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hdp : d ^ p = 1)
    (H : UnitaryPrimaryData hUF.bar (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d))
    {a : K[X]} (ha : a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)))
    (hS : primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K)) = {a}) :
    ∃ c : Kˣ, (d : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
  obtain ⟨μ, rfl⟩ := raUni_primaryFactor_linear hUF hcard hp hp2 hpq hdp ha
  have hμ0 : μ ≠ 0 := by
    have h := coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha
    simpa using h
  have hmin : minpoly K ((Matrix.GeneralLinearGroup.toLin d :
      LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) = X - C μ := by
    rw [← prod_primaryFactors H.squarefree, hS]
    simp
  have hxscal : ((Matrix.GeneralLinearGroup.toLin d :
      LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) = μ • 1 := by
    have h := minpoly.aeval K ((Matrix.GeneralLinearGroup.toLin d :
      LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K))
    rw [hmin, map_sub, aeval_X, aeval_C] at h
    exact sub_eq_zero.mp (by simpa [Algebra.algebraMap_eq_smul_one] using h)
  refine ⟨Units.mk0 μ hμ0, ?_⟩
  apply Matrix.GeneralLinearGroup.toLin.injective
  apply Units.ext
  rw [hxscal]
  refine LinearMap.ext fun v => ?_
  rw [raUni_toLin_scalar_apply, Units.val_mk0]
  simp

section
attribute [local instance] Classical.decEq

private theorem raUni_erase_toList_ne_nil {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) (hdp : d ^ p = 1)
    (hdne : primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ ≠ 1)
    (a₀ : {a : primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)) // IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) a}) :
    ((primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))).erase
      (a₀.1 : K[X])).toList.map (fun a => primaryMultiplicity
        (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K)) a) ≠ [] := by
  classical
  intro hnil
  have hcard0 : ((primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))).erase (a₀.1 : K[X])).card = 0 := by
    have h1 : (((primaryFactors (Matrix.GeneralLinearGroup.toLin d :
        Module.End K (Fin N → K))).erase (a₀.1 : K[X])).toList.map
          (fun a => primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
            Module.End K (Fin N → K)) a)).length = ((primaryFactors
              (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))).erase
                (a₀.1 : K[X])).card := by
      rw [List.length_map, Finset.length_toList]
    rw [← h1, hnil]
    simp
  have hempty : (primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))).erase (a₀.1 : K[X]) = ∅ := Finset.card_eq_zero.mp hcard0
  have hsingle : primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
      = {(a₀.1 : K[X])} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨a₀.1.2, fun b hb => ?_⟩
    by_contra hne'
    exact absurd (Finset.mem_erase.mpr ⟨hne', hb⟩) (by rw [hempty]; simp)
  obtain ⟨c, hc⟩ := raUni_eq_scalar_of_single_primaryFactor hUF hcard hp hp2 hpq hdp
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      hUF hd hp hp2 (by rw [hdp, map_one])) a₀.1.2 hsingle
  exact hdne (raUni_primeFormConjHom_eq_one_of_scalar (A := ⟨d, hd⟩) hc)

private theorem raUni_entries {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) (hdp : d ^ p = 1)
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hTonly : ∀ Q : Subgroup (primeFormP hUF (idGram K N)),
      CFSG.Open.IsComponentOf Q (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) →
      p ∣ Nat.card Q → Q = T)
    (a₀ : {a : primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)) // IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) a})
    (haT : T = unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d)
      (a₀.1 : K[X])) :
    ∀ x ∈ ((primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))).erase
      (a₀.1 : K[X])).toList.map (fun a => primaryMultiplicity
        (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K)) a),
      x = 1 ∨ (n = 1 ∧ (x = 2 ∨ x = 3)) := by
  classical
  have H : UnitaryPrimaryData hUF.bar (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      hUF hd hp hp2 (by rw [hdp, map_one])
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    have hb' : b ∈ (primaryFactors (Matrix.GeneralLinearGroup.toLin d :
        Module.End K (Fin N → K))).erase (a₀.1 : K[X]) := Finset.mem_toList.mp hb
    have hbS : b ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
        Module.End K (Fin N → K)) := Finset.mem_of_mem_erase hb'
    have hbne : (⟨b, hbS⟩ : primaryFactors (Matrix.GeneralLinearGroup.toLin d :
        Module.End K (Fin N → K))) ≠ a₀.1 := by
      intro h
      exact (Finset.ne_of_mem_erase hb') (congrArg Subtype.val h)
    have hng : ¬ IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) ⟨b, hbS⟩ :=
      raUni_unique_good hUF hcard hp hp2 hpq hd hdp hTonly a₀ haT hbne
    have hpos : 0 < primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
        Module.End K (Fin N → K)) b := primaryMultiplicity_pos H.squarefree ⟨b, hbS⟩
    have hdegb : b.natDegree = 1 :=
      raUni_primaryFactor_natDegree hUF hcard hp hp2 hpq hdp hbS
    have hselfb : dualPoly hUF.bar b = b :=
      raUni_primaryFactor_selfDual hUF hcard hp hp2 hpq hdp hbS
    by_cases hm : 2 ≤ primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
        Module.End K (Fin N → K)) b
    · have hmem : (primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
          Module.End K (Fin N → K)) b, 2 ^ n) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
        by_contra hc
        exact hng ⟨hm, fun _ => by simpa [hdegb] using hc⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inr ⟨?_, Or.inl h1⟩
        refine Nat.pow_right_injective (a := 2) (by norm_num) ?_
        simpa using h2
      · exfalso
        have h2' : 2 ∣ 2 ^ n := dvd_pow_self 2 (by intro hn0; rw [hn0] at h2; norm_num at h2)
        rw [h2] at h2'
        norm_num at h2'
      · refine Or.inr ⟨?_, Or.inr h1⟩
        refine Nat.pow_right_injective (a := 2) (by norm_num) ?_
        simpa using h2
    · exact Or.inl (by omega)


private theorem raUni_map_toList_length_lt {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) (hdp : d ^ p = 1)
    (a₀ : {a : primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)) // IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) a}) :
    (((primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))).erase
      (a₀.1 : K[X])).toList.map (fun a => primaryMultiplicity
        (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K)) a)).length < p := by
  have hcardS : (primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))).card ≤ p :=
    raUni_card_primaryFactors_le hUF hcard hp hp2 hpq hdp
  have hpos : 0 < (primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))).card := Finset.card_pos.mpr ⟨_, a₀.1.2⟩
  have h1 : (((primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))).erase (a₀.1 : K[X])).toList.map
        (fun a => primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
          Module.End K (Fin N → K)) a)).length = ((primaryFactors
            (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))).erase
              (a₀.1 : K[X])).card := by
    rw [List.length_map, Finset.length_toList]
  rw [h1, Finset.card_erase_of_mem a₀.1.2]
  omega

end

private theorem raUni_split_count {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) (hdp : d ^ p = 1)
    (hdne : primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ ≠ 1)
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hTonly : ∀ Q : Subgroup (primeFormP hUF (idGram K N)),
      CFSG.Open.IsComponentOf Q (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) →
      p ∣ Nat.card Q → Q = T)
    (a₀ : {a : primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)) // IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) a})
    (haT : T = unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d)
      (a₀.1 : K[X])) :
    ∃ ds : List ℕ,
      N = primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
          (a₀.1 : K[X]) + ds.sum ∧
        ds ≠ [] ∧ ds.length < p ∧ (∀ x ∈ ds, x = 1 ∨ (n = 1 ∧ (x = 2 ∨ x = 3))) := by
  classical
  have H : UnitaryPrimaryData hUF.bar (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      hUF hd hp hp2 (by rw [hdp, map_one])
  have hdegS : ∀ a ∈ primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)), a.natDegree = 1 := fun a ha =>
    raUni_primaryFactor_natDegree hUF hcard hp hp2 hpq hdp ha
  have hsumN : N = ∑ a : ↥(primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))), primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
        Module.End K (Fin N → K)) (a : K[X]) := by
    have hsum := finrank_eq_sum_degree_mul_multiplicity (x := (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K))) H.squarefree
    rw [show Module.finrank K (Fin N → K) = N from by simp] at hsum
    refine hsum.trans ?_
    exact Finset.sum_congr rfl fun a _ => by rw [hdegS a a.2, one_mul]
  refine ⟨((primaryFactors (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))).erase
    (a₀.1 : K[X])).toList.map (fun a => primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)) a), ?_, ?_, ?_, ?_⟩
  · have hNsplit : (∑ a : ↥(primaryFactors (Matrix.GeneralLinearGroup.toLin d :
        Module.End K (Fin N → K))), primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
          Module.End K (Fin N → K)) (a : K[X])) =
        primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
            (a₀.1 : K[X]) +
          (((primaryFactors (Matrix.GeneralLinearGroup.toLin d :
            Module.End K (Fin N → K))).erase (a₀.1 : K[X])).toList.map
              (fun a => primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
                Module.End K (Fin N → K)) a)).sum := by
      rw [Finset.sum_coe_sort (primaryFactors (Matrix.GeneralLinearGroup.toLin d :
          Module.End K (Fin N → K))) (fun a => primaryMultiplicity
            (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K)) a),
        ← Finset.sum_erase_add (primaryFactors (Matrix.GeneralLinearGroup.toLin d :
          Module.End K (Fin N → K))) (fun a => primaryMultiplicity
            (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K)) a) a₀.1.2,
        Finset.sum_map_toList]
      omega
    exact hsumN.trans hNsplit
  · exact raUni_erase_toList_ne_nil hUF hcard hp hp2 hpq hd hdp hdne a₀
  · exact raUni_map_toList_length_lt hUF hcard hp hp2 hpq hd hdp a₀
  · exact raUni_entries hUF hcard hp hp2 hpq hd hdp hTonly a₀ haT

private theorem raUni_split_component {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) (hdp : d ^ p = 1)
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (a₀ : {a : primaryFactors (Matrix.GeneralLinearGroup.toLin d :
      Module.End K (Fin N → K)) // IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d) a})
    (haT : T = unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d)
      (a₀.1 : K[X])) :
    ((primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
          (a₀.1 : K[X]) = 2 ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
          4 ≤ Fintype.card F ∧
          ∃ g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T, Function.Surjective g ∧
            g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (3 ≤ primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
            Module.End K (Fin N → K)) (a₀.1 : K[X]) ∧
        (primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
            (a₀.1 : K[X]), 2 ^ n) ≠ (3, 2) ∧
        ∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (2 ^ n) ^ 2 ∧
          ∃ g : ↥(StatedSU (primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d :
              Module.End K (Fin N → K)) (a₀.1 : K[X])) (2 ^ n) E) →* ↥T,
            Function.Surjective g ∧
              g.ker ≤ Subgroup.center ↥(StatedSU (primaryMultiplicity
                (Matrix.GeneralLinearGroup.toLin d : Module.End K (Fin N → K))
                  (a₀.1 : K[X])) (2 ^ n) E))) := by
  classical
  have H : UnitaryPrimaryData hUF.bar (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      hUF hd hp hp2 (by rw [hdp, map_one])
  have hq : 2 ≤ 2 ^ n := raUni_two_pow_le_of_dvd hp hp2 hpq
  subst haT
  have hdega : (a₀.1 : K[X]).natDegree = 1 :=
    raUni_primaryFactor_natDegree hUF hcard hp hp2 hpq hdp a₀.1.2
  have hselfa : dualPoly hUF.bar (a₀.1 : K[X]) = a₀.1 :=
    raUni_primaryFactor_selfDual hUF hcard hp hp2 hpq hdp a₀.1.2
  obtain ⟨hsub, hkernel⟩ :=
    subgroupMap_mk'_surjective_ker_le_center hUF (x := Matrix.GeneralLinearGroup.toLin d) a₀
  let ψ : ↥(specialBlock (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X])) →*
      ↥(unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X])) :=
    (MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars hUF N))
      (unitaryPreimageBlock hUF (x := Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X]))).comp
      (specialBlockEquiv hUF H a₀ hq a₀.2).symm.toMonoidHom
  have hψsurj : Function.Surjective ψ :=
    hsub.comp (specialBlockEquiv hUF H a₀ hq a₀.2).symm.surjective
  have hψker : ψ.ker ≤ Subgroup.center ↥(specialBlock (idForm hUF N)
      (Matrix.GeneralLinearGroup.toLin d) (a₀.1 : K[X])) := by
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hkernel).trans
      (Subgroup.comap_center_le_center (f := (specialBlockEquiv hUF H a₀ hq a₀.2).symm.toMonoidHom)
        (specialBlockEquiv hUF H a₀ hq a₀.2).symm.injective)
  rcases raUni_selfDual_block_field (B := idForm hUF N) hq H hselfa hdega a₀.2 with
    ⟨hm2, F, hF, hFt, hcardF, h4, ⟨e⟩⟩ | ⟨E, hE, hEt, hcardE, hm, hne, ⟨e⟩⟩
  · letI : Field F := hF
    letI : Fintype F := hFt
    refine Or.inl ⟨hm2, F, hF, hFt, hcardF, h4, ψ.comp e.symm.toMonoidHom,
      hψsurj.comp e.symm.surjective, ?_⟩
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hψker).trans
      (Subgroup.comap_center_le_center (f := e.symm.toMonoidHom) e.symm.injective)
  · letI : Field E := hE
    letI : Fintype E := hEt
    refine Or.inr ⟨hm, hne, E, hE, hEt, hcardE, ψ.comp e.symm.toMonoidHom,
      hψsurj.comp e.symm.surjective, ?_⟩
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hψker).trans
      (Subgroup.comap_center_le_center (f := e.symm.toMonoidHom) e.symm.injective)

private theorem raUni_marking {p : ℕ} {X : Type} [Group X] {A : Subgroup (MulAut X)}
    {labX : LargeEvenLabel} (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    commutator X = ⊤ ∧ LargeEvenInLambda2 labX := by
  rw [GGTPNMarked, LargeEvenMarking] at hm
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hm
  obtain ⟨R, _, I, F, -, -, θ₀, hlabX, -, -⟩ := largeEvenRawDatum_exists hraw
  subst hlabX
  exact ⟨hcomm, hlab⟩

private theorem raUni_label_eq_twA {lab : LargeEvenLabel} (h : lab.tag = .twA) :
    lab = ⟨.twA, lab.rank, lab.n⟩ := by
  cases lab
  simp only at h
  rw [h]

private theorem raUni_conjHom_scalar_mul {N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) {d : GL (Fin N) K}
    (hd : d ∈ primeFormUnitary hUF (idGram K N)) {u : Kˣ} (hu : hUF.norm (u : K) = 1) :
    primeFormConjHom hUF (idGram K N)
        ⟨Matrix.GeneralLinearGroup.scalar (Fin N) u * d,
          Subgroup.mul_mem _ (scalar_mem_primeFormUnitary_one (h := hUF) (n := N) hu) hd⟩ =
      primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [primeFormConjHom_mk, primeFormConjHom_mk]
    congr 1
    exact Subtype.ext (InndiagSU.scalar_mul_conj u d (g : GL (Fin N) K))

private theorem raUni_pow_norm {p n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {b : K} (hb0 : b ≠ 0) {c : K}
    (hbc : b ^ p = c) (hcn : hUF.norm c = 1) :
    b ^ (2 ^ n + 1) = 1 := by
  classical
  have hn : 1 ≤ n := hUF.one_le
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  letI : Fintype K := Fintype.ofFinite K
  have hFcard : Fintype.card K = 2 ^ n * 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, hcard, pow_two]
  have hbcard : b ^ (2 ^ n * 2 ^ n - 1) = 1 := by
    simpa only [hFcard] using FiniteField.pow_card_sub_one_eq_one b hb0
  have hcq : c ^ (2 ^ n + 1) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hcn
    rw [pow_succ, mul_comm]
    exact hcn
  have hzp : (b ^ (2 ^ n + 1)) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hbc, hcq]
  have hmul : (2 ^ n + 1) * (2 ^ n - 1) = 2 ^ n * 2 ^ n - 1 := by
    calc (2 ^ n + 1) * (2 ^ n - 1) = (2 ^ n) ^ 2 - 1 ^ 2 :=
          (Nat.sq_sub_sq (2 ^ n) 1).symm
      _ = 2 ^ n * 2 ^ n - 1 := by rw [one_pow, pow_two]
  have hzq : (b ^ (2 ^ n + 1)) ^ (2 ^ n - 1) = 1 := by
    rw [← pow_mul, hmul]
    exact hbcard
  have hcop : Nat.Coprime p (2 ^ n - 1) := by
    refine (hp.coprime_iff_not_dvd).mpr ?_
    intro hdvd
    have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpq hdvd
    have hsub : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rw [hsub] at h2
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    exact ne_two_of_dvd_two_pow_add_one hn hpq hp2
  have hord : orderOf (b ^ (2 ^ n + 1)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_iff_pow_eq_one.mpr hzp) (orderOf_dvd_iff_pow_eq_one.mpr hzq)
  exact orderOf_eq_one_iff.mp hord

private theorem raUni_rescale {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    {d : GL (Fin N) K} {c : Kˣ}
    (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hcn : hUF.norm (c : K) = 1)
    (hb : ∃ b : K, b ^ p = (c : K)) :
    ∃ (d' : GL (Fin N) K) (hd' : d' ∈ primeFormUnitary hUF (idGram K N)) (u : Kˣ),
      d' ^ p = 1 ∧ d' = Matrix.GeneralLinearGroup.scalar (Fin N) u * d ∧
        primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩ =
          primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ := by
  obtain ⟨b, hb⟩ := hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : (0 : K) ^ p = (c : K) := hb
    rw [zero_pow hp.ne_zero] at h0
    exact c.ne_zero h0.symm
  let u : Kˣ := Units.mk0 b hb0
  have hu : (u : K) = b := rfl
  have hunion : b ^ (2 ^ n + 1) = 1 := raUni_pow_norm hUF hcard hp hpq hb0 hb hcn
  have hbnorm : hUF.norm (b : K) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← pow_succ']
    exact hunion
  have hunorm : hUF.norm ((u⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val,
      CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq hUF, hu, hbnorm, inv_one]
  have hbup : u ^ p = c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu, hb]
  have hsu : Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹ ∈
      primeFormUnitary hUF (idGram K N) :=
    scalar_mem_primeFormUnitary_one (h := hUF) (n := N) hunorm
  let d' : GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹ * d
  have hd' : d' ∈ primeFormUnitary hUF (idGram K N) := Subgroup.mul_mem _ hsu hd
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹) d :=
    (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin N) u⁻¹) d).symm
  have hd'p : d' ^ p = 1 := by
    calc d' ^ p = (Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹) ^ p * d ^ p := by
          change (Matrix.GeneralLinearGroup.scalar (Fin N) u⁻¹ * d) ^ p = _
          rw [hcomm.mul_pow]
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) ((u⁻¹) ^ p) *
            Matrix.GeneralLinearGroup.scalar (Fin N) c := by rw [← map_pow, hdp]
      _ = Matrix.GeneralLinearGroup.scalar (Fin N) ((u⁻¹) ^ p * c) := by rw [← map_mul]
      _ = 1 := by
            rw [inv_pow, hbup, inv_mul_cancel, map_one]
  have hconj : primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩ =
      primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ :=
    raUni_conjHom_scalar_mul (hUF := hUF) (hd := hd) (u := u⁻¹) hunorm
  exact ⟨d', hd', u⁻¹, hd'p, rfl, hconj⟩

private theorem raUni_ne_two {p n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hpq : p ∣ 2 ^ n + 1) : p ≠ 2 :=
  ne_two_of_dvd_two_pow_add_one hUF.one_le hpq

private theorem raUni_conjAut_ne_one {p N n : ℕ} {K : Type} [Field K] [Finite K]
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hUF : UnitaryFieldData 2 n K) (hN1 : 1 ≤ N)
    (hloc : GGTPNLocalCore p A σ J) (hcomm : commutator X = ⊤)
    {θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hδ : IsConjBy d (ggInducedAut θ σ)) :
    primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ ≠ 1 := by
  intro h1
  have hinj := ggInducedAut_injective_of_perfect hcomm θ
  have hσ1 : ggInducedAut θ σ = 1 := by
    ext x
    have hx : InndiagSU.projEquiv hUF hN1 x ∈
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩) := by
      rw [h1, CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
      rfl
    have hfixed : x ∈ ggAutFixedSubgroup (ggInducedAut θ σ) :=
      (uni_cube_fixSubgroup_projEquiv hUF hN1 hδ hd x).mpr hx
    have hx' := (mem_ggAutFixedSubgroup (ggInducedAut θ σ) x).mp hfixed
    simpa using hx'
  exact hloc.2.2.1 (hinj (by rw [hσ1, map_one]))

private theorem raUni_split_label_A {n : ℕ} {R S : Type} [Group R] [Group S]
    {F : Type} [Field F] [Fintype F]
    (hFcard : Fintype.card F = 2 ^ n) (hF4 : 4 ≤ Fintype.card F)
    {g : Matrix.SpecialLinearGroup (Fin 2) F →* S}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    (e : R ≃* (S ⧸ Subgroup.center S)) :
    LargeEvenInLambda2 ⟨.A, 1, n⟩ ∧ GGHasLabel ⟨.A, 1, n⟩ R := by
  have hn : 2 ≤ n := by
    by_contra h
    have hn1 : n ≤ 1 := by omega
    have hle : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    have h4 : 4 ≤ 2 ^ n := by rw [← hFcard]; exact hF4
    omega
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨CFSG.Timmesfeld.Bridge.RootMany.commutator_SL2_eq_top (m := n) hn (by
      rw [Nat.card_eq_fintype_card]; exact hFcard)⟩
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central g hg hperf hgk
  let eZ : (Matrix.SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ≃*
      StatedProj (StatedSL 2 F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  have hadm : StatedLieAdmissible .PSL 2 2 n := by
    refine ⟨Nat.prime_two, by omega, by norm_num, ?_, ?_⟩
    · intro h
      have h2 : 2 ^ n = 2 := (Prod.mk.inj h).2
      have h4 : 4 ≤ 2 ^ n := by rw [← hFcard]; exact hF4
      omega
    · intro h
      have h2 : 2 ^ n = 3 := (Prod.mk.inj h).2
      have h4 : 4 ≤ 2 ^ n := by rw [← hFcard]; exact hF4
      omega
  have hSC : StatedClassicalModel R .PSL 2 2 n :=
    ⟨hadm, F, inferInstance, inferInstance, by rwa [Nat.card_eq_fintype_card],
      ⟨e.trans (e1.symm.trans eZ)⟩⟩
  exact ⟨largeEvenInLambda2_typeA hSC, ggHasLabel_typeA hSC⟩

private theorem raUni_split_label_twA {a n : ℕ} {R S : Type} [Group R] [Group S]
    {E : Type} [Field E] [Fintype E]
    (hE : Fintype.card E = (2 ^ n) ^ 2) (hn : 1 ≤ n) (h3a : 3 ≤ a)
    (hane : (a, 2 ^ n) ≠ (3, 2))
    {g : ↥(StatedSU a (2 ^ n) E) →* S}
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center ↥(StatedSU a (2 ^ n) E))
    (e : R ≃* (S ⧸ Subgroup.center S)) :
    LargeEvenInLambda2 ⟨.twA, a - 1, n⟩ ∧ GGHasLabel ⟨.twA, a - 1, n⟩ R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEnat : Nat.card E = (2 ^ n) ^ 2 := by
    rw [Nat.card_eq_fintype_card]; exact hE
  have hqSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := n) (F := E) hEnat h3a hane
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central
    g hg hqSU.1.1 hgk
  let e2 : (↥(StatedSU a (2 ^ n) E) ⧸
      Subgroup.center ↥(StatedSU a (2 ^ n) E)) ≃*
      StatedProj (StatedSU a (2 ^ n) E) :=
    QuotientGroup.quotientMulEquivOfEq hqSU.2
  have hb : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
  have eT : S ⧸ Subgroup.center S ≃*
      StatedProj (StatedSU (a - 1 + 1) (2 ^ n) E) := by
    rw [hb]; exact e1.symm.trans e2
  have hlabS : GGHasLabel ⟨.twA, a - 1, n⟩ (S ⧸ Subgroup.center S) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA (b := a - 1) (m := n)
      hEnat eT
  have hΛ : LargeEvenInLambda2 ⟨.twA, a - 1, n⟩ := by
    refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA
      (b := a - 1) (m := n) hn (by omega) ?_
    intro hb2
    have ha3 : a = 3 := by omega
    by_contra hn2
    have hn1 : n = 1 := by omega
    exact hane (by rw [ha3, hn1]; norm_num)
  exact ⟨hΛ, ggHasLabel_of_mulEquiv e.symm hlabS⟩

private theorem raUni_nonSplit_bound {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hN3 : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2))
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (hcomm : commutator X = ⊤)
    {θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    (hind : GGInducedInn A θ (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      (LargeEvenGUSet (Fin N) K (2 ^ n))))
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdconj : IsConjBy d (ggInducedAut θ σ)) {c : Kˣ}
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K)) :
    Nat.card A ≤ p ^ (N / p + 1) := by
  have hXcard : Nat.card (A.map (ggInducedAut θ)) = Nat.card A :=
    Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hcomm θ)
  have hXeab : IsElemAbelian p (A.map (ggInducedAut θ)) :=
    TableB.isElemAbelian_map hloc.1 (ggInducedAut θ)
  have hXr : ∀ x ∈ A.map (ggInducedAut θ),
      x ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
        (LargeEvenGUSet (Fin N) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact hind a ha
  have hNd : d ∈ Subgroup.normalizer
      (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)) :=
    TableBUE.gu_subset_normalizer (d := N) hUF
      (TableBUD.mem_guSet_of_mem_primeFormUnitary hUF hd)
  have hσmem : ggInducedAut θ σ ∈ A.map (ggInducedAut θ) :=
    Subgroup.mem_map_of_mem _ hloc.2.1
  have hdconj' : ggInducedAut θ σ = TableB.projConj
      (LargeEvenSUGroup (Fin N) K (2 ^ n)) ⟨d, hNd⟩ :=
    raUni_projConj_eq_of_isConjBy hNd hdconj
  have h := raUni_nonSplit_bound_elemAbelian hUF hcard hp hpq hN3 hNq hXeab hXr hσmem
    hd hdconj' hdp hc
  rwa [hXcard] at h

private theorem raUni_nonSplit_component_label {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpN : p ∣ N)
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N)) {c : Kˣ}
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hT : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)))
    {R : Type} [Group R] (e : R ≃* (↥T ⧸ Subgroup.center ↥T)) :
    2 ≤ N / p ∧
      ((N / p = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, p * n⟩ ∧
          GGHasLabel ⟨.A, 1, p * n⟩ R) ∨
        (3 ≤ N / p ∧ LargeEvenInLambda2 ⟨.twA, N / p - 1, p * n⟩ ∧
          GGHasLabel ⟨.twA, N / p - 1, p * n⟩ R)) := by
  have h2Np : 2 ≤ N / p := by
    obtain ⟨-, h2, -, -⟩ := unitary_fieldType_component (p := p) (ℓ := 2) (f := n)
      (n := N) hp hUF (raUni_ne_two hUF hpq) ⟨d, hd⟩ hdp hc hT
    exact h2
  rcases raUni_nonSplit_component hUF hcard hp hpq hpN h2Np hd hdp hc hT with
    ⟨hNp2, hΛ, hlab⟩ | ⟨h3Np, hΛ, hlab⟩
  · exact ⟨h2Np, Or.inl ⟨hNp2, hΛ, ggHasLabel_of_mulEquiv e.symm hlab⟩⟩
  · exact ⟨h2Np, Or.inr ⟨h3Np, hΛ, ggHasLabel_of_mulEquiv e.symm hlab⟩⟩

private theorem raUni_nonSplit_case {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpN : p ∣ N) (hN3 : 3 ≤ N)
    (hNq : (N, 2 ^ n) ≠ (3, 2))
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (hcomm : commutator X = ⊤)
    {θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    (hind : GGInducedInn A θ (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      (LargeEvenGUSet (Fin N) K (2 ^ n))))
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdconj : IsConjBy d (ggInducedAut θ σ)) {c : Kˣ}
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hT : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)))
    (hequiv : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥T ⧸ Subgroup.center ↥T)) :
    2 ≤ N / p ∧ Nat.card A ≤ p ^ (N / p + 1) ∧
      ((N / p = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, p * n⟩ ∧
          GGHasLabel ⟨.A, 1, p * n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
        (3 ≤ N / p ∧ LargeEvenInLambda2 ⟨.twA, N / p - 1, p * n⟩ ∧
          GGHasLabel ⟨.twA, N / p - 1, p * n⟩
            (↥J ⧸ Subgroup.center ↥J))) := by
  obtain ⟨eJZ⟩ := hequiv
  obtain ⟨h2Np, hlabels⟩ :=
    raUni_nonSplit_component_label hUF hcard hp hpq hpN hd hdp hc hT eJZ
  have hbound := raUni_nonSplit_bound hUF hcard hp hpq hN3 hNq hloc hcomm hind hd hdconj
    hdp hc
  exact ⟨h2Np, hbound, hlabels⟩

private theorem raUni_split_component_label {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hN1 : 1 ≤ N)
    {d : GL (Fin N) K} {c : Kˣ}
    (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hsplit : ∃ b : K, b ^ p = (c : K))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hT : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)))
    {R : Type} [Group R] (e : R ≃* (↥T ⧸ Subgroup.center ↥T)) :
    ∃ (d' : GL (Fin N) K) (hd' : d' ∈ primeFormUnitary hUF (idGram K N)) (u : Kˣ)
      (a₀ : {a : primaryFactors (Matrix.GeneralLinearGroup.toLin d' :
        Module.End K (Fin N → K)) // IsGoodBlock hUF (Matrix.GeneralLinearGroup.toLin d') a})
      (a : ℕ),
      d' ^ p = 1 ∧ d' = Matrix.GeneralLinearGroup.scalar (Fin N) u * d ∧
      primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩ =
        primeFormConjHom hUF (idGram K N) ⟨d, hd⟩ ∧
      T = unitaryBlockComponent hUF (x := Matrix.GeneralLinearGroup.toLin d')
        (a₀.1 : K[X]) ∧
      a = primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d' : Module.End K (Fin N → K))
        (a₀.1 : K[X]) ∧
      ((a = 2 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
          Fintype.card F = 2 ^ n ∧ 4 ≤ Fintype.card F ∧
          ∃ g : Matrix.SpecialLinearGroup (Fin 2) F →* ↥T, Function.Surjective g ∧
            g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (3 ≤ a ∧ (a, 2 ^ n) ≠ (3, 2) ∧ ∃ (E : Type) (_ : Field E) (_ : Fintype E),
          Fintype.card E = (2 ^ n) ^ 2 ∧
          ∃ g : ↥(StatedSU a (2 ^ n) E) →* ↥T, Function.Surjective g ∧
            g.ker ≤ Subgroup.center ↥(StatedSU a (2 ^ n) E))) ∧
      ((LargeEvenInLambda2 ⟨.twA, a - 1, n⟩ ∧ GGHasLabel ⟨.twA, a - 1, n⟩ R) ∨
        (a = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, n⟩ ∧ GGHasLabel ⟨.A, 1, n⟩ R)) := by
  classical
  have hc_mem : Matrix.GeneralLinearGroup.scalar (Fin N) c ∈
      primeFormUnitary hUF (idGram K N) := by
    rw [← hdp]
    exact Subgroup.pow_mem _ hd p
  have hcn : hUF.norm (c : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary hUF hN1 (1 : GL (Fin N) K) hc_mem
  have hp2 : p ≠ 2 := raUni_ne_two hUF hpq
  obtain ⟨d', hd', u, hd'p, hd'eq, hconj⟩ :=
    raUni_rescale hUF hcard hp hpq hd hdp hcn hsplit
  have hT' : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩)) := by
    rw [hconj]; exact hT
  have hq : 2 ≤ 2 ^ n := raUni_two_pow_le_of_dvd hp hp2 hpq
  have H : UnitaryPrimaryData hUF.bar (idForm hUF N) (Matrix.GeneralLinearGroup.toLin d') :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      hUF hd' hp hp2 (by rw [hd'p, map_one])
  obtain ⟨a₀, ha₀⟩ := exists_good_primaryFactor_of_component hq ⟨d', hd'⟩ rfl H T hT'
  let a := primaryMultiplicity (Matrix.GeneralLinearGroup.toLin d' : Module.End K (Fin N → K))
    (a₀.1 : K[X])
  have hstruct := raUni_split_component hUF hcard hp hp2 hpq hd' hd'p a₀ ha₀
  refine ⟨d', hd', u, a₀, a, hd'p, hd'eq, hconj, ha₀, rfl, hstruct, ?_⟩
  rcases hstruct with ⟨ha2, F, hF, hFt, hcardF, h4, g, hgsurj, hgker⟩ |
    ⟨h3a, hane, E, hE, hEt, hcardE, g, hgsurj, hgker⟩
  · let _ : Field F := hF
    let _ : Fintype F := hFt
    exact Or.inr ⟨ha2, raUni_split_label_A (n := n) (R := R) (S := ↥T)
      hcardF h4 hgsurj hgker e⟩
  · let _ : Field E := hE
    let _ : Fintype E := hEt
    exact Or.inl (raUni_split_label_twA (a := a) (n := n) (R := R) (S := ↥T)
      hcardE hUF.one_le h3a hane hgsurj hgker e)

private theorem raUni_split_case {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hN1 : 1 ≤ N)
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (hcomm : commutator X = ⊤)
    {θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdconj : IsConjBy d (ggInducedAut θ σ)) {c : Kˣ}
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hsplit : ∃ b : K, b ^ p = (c : K))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hT : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)))
    (huniq : ∀ Q : Subgroup (primeFormP hUF (idGram K N)),
      CFSG.Open.IsComponentOf Q
        (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) →
      p ∣ Nat.card Q → Q = T)
    (hequiv : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥T ⧸ Subgroup.center ↥T)) :
    ∃ a ds, N = a + ds.sum ∧ ds ≠ [] ∧ ds.length < p ∧
      (∀ x ∈ ds, x = 1 ∨ (n = 1 ∧ (x = 2 ∨ x = 3))) ∧
      ((LargeEvenInLambda2 ⟨.twA, a - 1, n⟩ ∧
          GGHasLabel ⟨.twA, a - 1, n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
        (a = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, n⟩ ∧
          GGHasLabel ⟨.A, 1, n⟩ (↥J ⧸ Subgroup.center ↥J))) := by
  obtain ⟨eJZ⟩ := hequiv
  obtain ⟨d', hd', u, a₀, a, hd'p, hd'eq, hconj, haT, ha, -, hlabels⟩ :=
    raUni_split_component_label hUF hcard hp hpq hN1 hd hdp hsplit hT eJZ
  have hδ' : IsConjBy d' (ggInducedAut θ σ) := by
    intro h h' hrel
    refine hdconj h h' ?_
    show (h' : GL (Fin N) K) = d * (h : GL (Fin N) K) * d⁻¹
    rw [hrel, hd'eq]
    exact InndiagSU.scalar_mul_conj u d (h : GL (Fin N) K)
  have hdne : primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩ ≠ 1 :=
    raUni_conjAut_ne_one hUF hN1 hloc hcomm hd' hδ'
  have hT' : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩)) := by
    rw [hconj]; exact hT
  have huniq' : ∀ Q : Subgroup (primeFormP hUF (idGram K N)),
      CFSG.Open.IsComponentOf Q
        (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d', hd'⟩)) →
      p ∣ Nat.card Q → Q = T := by
    rw [hconj]; exact huniq
  obtain ⟨ds, hN, hdsne, hdslt, hdscond⟩ :=
    raUni_split_count hUF hcard hp (raUni_ne_two hUF hpq) hpq
      hd' hd'p hdne huniq' a₀ haT
  exact ⟨a, ds, by rw [ha]; exact hN, hdsne, hdslt, hdscond, hlabels⟩

private theorem raUni_split_branch {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hN1 : 1 ≤ N)
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (hcomm : commutator X = ⊤)
    {θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdconj : IsConjBy d (ggInducedAut θ σ)) {c : Kˣ}
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hsplit : ∃ b : K, b ^ p = (c : K))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hT : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)))
    (huniq : ∀ Q : Subgroup (primeFormP hUF (idGram K N)),
      CFSG.Open.IsComponentOf Q
        (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)) →
      p ∣ Nat.card Q → Q = T)
    (hequiv : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥T ⧸ Subgroup.center ↥T))
    {labX : LargeEvenLabel} (hA : labX.tag = .twA) (hN : N = labX.rank + 1) :
    (∃ (a : ℕ) (ds : List ℕ), labX.rank + 1 = a + ds.sum ∧ ds ≠ [] ∧ ds.length < p ∧
        (∀ x ∈ ds, x = 1 ∨ (labX.tag = .twA ∧ n = 1 ∧ (x = 2 ∨ x = 3))) ∧
        ((LargeEvenInLambda2 ⟨labX.tag, a - 1, n⟩ ∧
            GGHasLabel ⟨labX.tag, a - 1, n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
          (labX.tag = .twA ∧ a = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, n⟩ ∧
            GGHasLabel ⟨.A, 1, n⟩ (↥J ⧸ Subgroup.center ↥J)))) := by
  obtain ⟨a, ds, hNsum, hdsne, hdslt, hdscond, hcase⟩ :=
    raUni_split_case hUF hcard hp hpq hN1 hloc hcomm hd hdconj hdp hsplit
      hT huniq hequiv
  refine ⟨a, ds, ?_, hdsne, hdslt, ?_, ?_⟩
  · rw [← hN]
    exact hNsum
  · intro x hx
    rcases hdscond x hx with h1 | ⟨hn1, hx23⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hA, hn1, hx23⟩
  · rcases hcase with ⟨hΛ, hlab⟩ | ⟨ha2, hΛ, hlab⟩
    · rw [hA]
      exact Or.inl ⟨hΛ, hlab⟩
    · rw [hA]
      exact Or.inr ⟨rfl, ha2, hΛ, hlab⟩

private theorem raUni_nonSplit_branch {p N n : ℕ} {K : Type} [Field K] [Finite K]
    (hUF : UnitaryFieldData 2 n K) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpN : p ∣ N) (hN3 : 3 ≤ N)
    (hNq : (N, 2 ^ n) ≠ (3, 2))
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (hcomm : commutator X = ⊤)
    {θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    (hind : GGInducedInn A θ (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n)))
      (LargeEvenGUSet (Fin N) K (2 ^ n))))
    {d : GL (Fin N) K} (hd : d ∈ primeFormUnitary hUF (idGram K N))
    (hdconj : IsConjBy d (ggInducedAut θ σ)) {c : Kˣ}
    (hdp : d ^ p = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hc : ∀ b : K, b ^ p ≠ (c : K))
    {T : Subgroup (primeFormP hUF (idGram K N))}
    (hT : CFSG.Open.IsComponentOf T
      (fixSubgroup (primeFormConjHom hUF (idGram K N) ⟨d, hd⟩)))
    (hequiv : Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥T ⧸ Subgroup.center ↥T))
    {labX : LargeEvenLabel} (hA : labX.tag = .twA) (hN : N = labX.rank + 1) :
    (2 ≤ (labX.rank + 1) / p ∧ Nat.card A ≤ p ^ ((labX.rank + 1) / p + 1) ∧
      (((labX.tag = .A ∨ (labX.rank + 1) / p = 2) ∧
          LargeEvenInLambda2 ⟨.A, (labX.rank + 1) / p - 1, p * n⟩ ∧
          GGHasLabel ⟨.A, (labX.rank + 1) / p - 1, p * n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
        (labX.tag = .twA ∧ 3 ≤ (labX.rank + 1) / p ∧
          LargeEvenInLambda2 ⟨.twA, (labX.rank + 1) / p - 1, p * n⟩ ∧
          GGHasLabel ⟨.twA, (labX.rank + 1) / p - 1, p * n⟩
            (↥J ⧸ Subgroup.center ↥J)))) := by
  obtain ⟨h2Np, hbound, hlabels⟩ :=
    raUni_nonSplit_case hUF hcard hp hpq hpN hN3 hNq hloc hcomm hind hd hdconj
      hdp hc hT hequiv
  refine ⟨?_, ?_, ?_⟩
  · rw [← hN]
    exact h2Np
  · rw [← hN]
    exact hbound
  · rcases hlabels with ⟨hNp2, hΛ, hlab⟩ | ⟨h3Np, hΛ, hlab⟩
    · have hNp2' : (labX.rank + 1) / p = 2 := by
        rw [← hN]
        exact hNp2
      refine Or.inl ⟨Or.inr hNp2', ?_, ?_⟩
      · rw [hNp2']
        exact hΛ
      · rw [hNp2']
        exact hlab
    · have h3Np' : 3 ≤ (labX.rank + 1) / p := by
        rw [← hN]
        exact h3Np
      refine Or.inr ⟨hA, h3Np', ?_, ?_⟩
      · rw [← hN]
        exact hΛ
      · rw [← hN]
        exact hlab

theorem split_or_fieldType_of_ggKacRA_unitary {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hloc : GGTPNLocalCore p A σ J) (h8 : GGTPNOnlyComp p σ J) {labX : LargeEvenLabel}
    (hA : labX.tag = .twA) (hRA : GGKacRA labX p) (hm : GGTPNMarked p (fun _ lab => lab = labX) A) :
    (∃ (a : ℕ) (ds : List ℕ), labX.rank + 1 = a + ds.sum ∧ ds ≠ [] ∧ ds.length < p ∧
        (∀ x ∈ ds, x = 1 ∨ (labX.tag = .twA ∧ labX.n = 1 ∧ (x = 2 ∨ x = 3))) ∧
        ((LargeEvenInLambda2 ⟨labX.tag, a - 1, labX.n⟩ ∧
            GGHasLabel ⟨labX.tag, a - 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
          (labX.tag = .twA ∧ a = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, labX.n⟩ ∧
            GGHasLabel ⟨.A, 1, labX.n⟩ (↥J ⧸ Subgroup.center ↥J)))) ∨
    (2 ≤ (labX.rank + 1) / p ∧ Nat.card A ≤ p ^ ((labX.rank + 1) / p + 1) ∧
      (((labX.tag = .A ∨ (labX.rank + 1) / p = 2) ∧
          LargeEvenInLambda2 ⟨.A, (labX.rank + 1) / p - 1, p * labX.n⟩ ∧
          GGHasLabel ⟨.A, (labX.rank + 1) / p - 1, p * labX.n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
        (labX.tag = .twA ∧ 3 ≤ (labX.rank + 1) / p ∧
          LargeEvenInLambda2 ⟨.twA, (labX.rank + 1) / p - 1, p * labX.n⟩ ∧
          GGHasLabel ⟨.twA, (labX.rank + 1) / p - 1, p * labX.n⟩
            (↥J ⧸ Subgroup.center ↥J)))) := by
  classical
  obtain ⟨hcomm, hΛX⟩ := raUni_marking hm
  obtain ⟨K, hFld, hFin, hcard, θ, hind⟩ := raUni_exists_unitary_model hA hm
  let _ : Field K := hFld
  have _ : Finite K := hFin
  let N : ℕ := labX.rank + 1
  have hN1 : 1 ≤ N := by omega
  have hUF : UnitaryFieldData 2 labX.n K := unitaryFieldData_of_card hcard hΛX.1
  have hσA : σ ∈ A := hloc.2.1
  have hσpow : σ ^ p = 1 := hloc.1.2 σ hσA
  have hδp : (ggInducedAut θ σ) ^ p = 1 := by rw [← map_pow, hσpow, map_one]
  obtain ⟨d, hd, hdconj⟩ := raUni_exists_unitary_lift hUF (hind σ hσA)
  have hlabel : labX = ⟨.twA, labX.rank, labX.n⟩ := raUni_label_eq_twA hA
  have hΛX' := hΛX
  rw [hlabel] at hΛX'
  have hΛX'' : 1 ≤ labX.n ∧ 2 ≤ labX.rank ∧ (labX.rank = 2 → 2 ≤ labX.n) := hΛX'
  have hN3 : 3 ≤ N := by have := hΛX''.2.1; omega
  have hNq : (N, 2 ^ labX.n) ≠ (3, 2) := by
    intro h
    have hN3' : N = 3 := congrArg Prod.fst h
    have h2n : 2 ^ labX.n = 2 := congrArg Prod.snd h
    have hn2 : 2 ≤ labX.n := hΛX''.2.2 (by omega)
    have h4 : 4 ≤ 2 ^ labX.n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ labX.n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hRA' := hRA
  rw [hlabel] at hRA'
  have hpq : p ∣ 2 ^ labX.n + 1 := by
    rcases hRA' with ⟨hAc, -⟩ | ⟨-, -, hpq⟩
    · cases hAc
    · exact hpq
  have hpN : p ∣ N := by
    rcases hRA' with ⟨hAc, -⟩ | ⟨-, hpN, -⟩
    · cases hAc
    · exact hpN
  obtain ⟨c, hdp⟩ :=
    raUni_pow_scalar_of_isConjBy hUF hcard hN3 hNq hp hpq hd hdconj hδp
  obtain ⟨Jbar, T, hJbar, hTeq, hT, huniq, hequiv⟩ :=
    raUni_component_primeForm hp hcomm hN1 hloc h8 hUF hd hdconj
  by_cases hsplit : ∃ b : K, b ^ p = (c : K)
  · exact Or.inl (raUni_split_branch hUF hcard hp hpq hN1 hloc hcomm hd hdconj
      hdp hsplit hT huniq hequiv hA rfl)
  · have hc : ∀ b : K, b ^ p ≠ (c : K) := fun b hb => hsplit ⟨b, hb⟩
    exact Or.inr (raUni_nonSplit_branch hUF hcard hp hpq hpN hN3 hNq hloc hcomm hind
      hd hdconj hdp hc hT hequiv hA rfl)

theorem ggKacRA_unitary_component_label {p N n : ℕ} (hp : p.Prime) {K : Type} [Field K]
    [Finite K] (hcard : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n + 1)
    (hpN : p ∣ N) (hN3 : 3 ≤ N) (hNq : (N, 2 ^ n) ≠ (3, 2)) {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤)
    {θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ n))}
    {σ : MulAut X} (hσp : σ ^ p = 1)
    (hσI : ggInducedAut θ σ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ n))) (LargeEvenGUSet (Fin N) K (2 ^ n)))
    {J : Subgroup X} (hJ : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup σ)) :
    (∃ m : ℕ, LargeEvenInLambda2 ⟨.twA, m, n⟩ ∧
        GGHasLabel ⟨.twA, m, n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (LargeEvenInLambda2 ⟨.A, 1, n⟩ ∧ GGHasLabel ⟨.A, 1, n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (N / p = 2 ∧ LargeEvenInLambda2 ⟨.A, 1, p * n⟩ ∧
        GGHasLabel ⟨.A, 1, p * n⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (LargeEvenInLambda2 ⟨.twA, N / p - 1, p * n⟩ ∧
        GGHasLabel ⟨.twA, N / p - 1, p * n⟩ (↥J ⧸ Subgroup.center ↥J)) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hUF : UnitaryFieldData 2 n K := unitaryFieldData_of_card hcard hn
  have hδp : (ggInducedAut θ σ) ^ p = 1 := by rw [← map_pow, hσp, map_one]
  obtain ⟨d, hd, hdconj⟩ := raUni_exists_unitary_lift hUF hσI
  obtain ⟨c, hdp⟩ :=
    raUni_pow_scalar_of_isConjBy hUF hcard hN3 hNq hp hpq hd hdconj hδp
  obtain ⟨T, -, -, hT, hequiv⟩ := raUni_component_primeForm_basic hX hN1 hJ hUF hd hdconj
  obtain ⟨eJ⟩ := hequiv
  by_cases hsplit : ∃ b : K, b ^ p = (c : K)
  · obtain ⟨-, -, -, -, a, -, -, -, -, -, -, hlabels⟩ :=
      raUni_split_component_label hUF hcard hp hpq hN1 hd hdp hsplit hT eJ
    rcases hlabels with ⟨hΛ, hlab⟩ | ⟨-, hΛ, hlab⟩
    · exact Or.inl ⟨a - 1, hΛ, hlab⟩
    · exact Or.inr (Or.inl ⟨hΛ, hlab⟩)
  · have hc : ∀ b : K, b ^ p ≠ (c : K) := fun b hb => hsplit ⟨b, hb⟩
    obtain ⟨-, hlabels⟩ :=
      raUni_nonSplit_component_label hUF hcard hp hpq hpN hd hdp hc hT eJ
    rcases hlabels with ⟨hNp2, hΛ, hlab⟩ | ⟨-, hΛ, hlab⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hNp2, hΛ, hlab⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hΛ, hlab⟩))

end CFSG.StandardType

end
