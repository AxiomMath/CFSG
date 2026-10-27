module

public import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryPieces1615
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkClass
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryDvdNode
public import CFSG.RankThree.PartOne.S11d.LieComponentTransfer
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RALabels
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma117
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType.KD2Pieces1615

open CFSG CFSG.Assembly CFSG.StandardType S2MathAs3_1615
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

private theorem ltrcu1_ker_projMk_le_center {d n : ℕ} {K : Type} [Field K] :
    (LargeEvenProjMk (unitarySU 2 n K d)).ker ≤
      Subgroup.center (↥(unitarySU 2 n K d)) := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : ((x : ↥(unitarySU 2 n K d)) : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hx)
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (TableB.scalars_le_center h1) (y : GL (Fin d) K)

private theorem ltrcu1_isQuasisimple_native {Q : Type*} [Group Q]
    (h : CFSG.Assembly.IsQuasisimple Q) : CFSG.IsQuasisimple Q :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Q).1 h

private theorem ltrcu1_not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  haveI : Group.IsPerfect Q := hperf
  exact Group.IsPerfect.not_isSolvable Q

private theorem ltrcu1_not_labelIso_twA_A {c n m : ℕ} :
    ¬ GGLabelIso (⟨.twA, c, n⟩ : LargeEvenLabel) ⟨.A, 1, m⟩ := by
  intro h
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;>
    simp_all [LargeEvenLabel.mk.injEq]

private theorem ltrcu1_blockSU_card_eq_two
    {d n : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
    {I : Finset (Fin d)} (hI2 : 2 ≤ I.card)
    (hQq : CFSG.IsQuasisimple ↥(TableBUE.blockSU (K := K) (n := n) I))
    {J₀ : Subgroup (LargeEvenProj (unitarySU 2 n K d))}
    (hmap : (TableBUE.blockSU (K := K) (n := n) I).map
      (LargeEvenProjMk (unitarySU 2 n K d)) = J₀)
    (hJ₀ : CFSG.IsQuasisimple ↥J₀)
    (hker : (LargeEvenProjMk (unitarySU 2 n K d)).ker ≤
      Subgroup.center (↥(unitarySU 2 n K d)))
    {m : ℕ} (hlabel : GGHasLabel (⟨.A, 1, m⟩ : LargeEvenLabel) (↥J₀ ⧸ Subgroup.center ↥J₀)) :
    I.card = 2 := by
  classical
  by_contra hne
  have hc3 : 3 ≤ I.card := by omega
  let S : Subgroup (GL (Fin d) K) := unitarySU 2 n K d
  let π : ↥S →* LargeEvenProj S := LargeEvenProjMk S
  let Q : Subgroup ↥S := TableBUE.blockSU (K := K) (n := n) I
  have hmap' : Q.map π = J₀ := hmap
  have hQq' : CFSG.IsQuasisimple ↥Q := hQq
  have hmemψ : ∀ q : ↥Q, (π.comp Q.subtype) q ∈ Q.map π := fun q =>
    Subgroup.mem_map.mpr ⟨Q.subtype q, q.2, rfl⟩
  let ψ : ↥Q →* ↥(Q.map π) := (π.comp Q.subtype).codRestrict _ hmemψ
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨s, hs, hys⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨s, hs⟩, Subtype.ext hys⟩
  let eJ : ↥(Q.map π) ≃* ↥J₀ := MulEquiv.subgroupCongr hmap'
  let φ : ↥Q →* ↥J₀ := eJ.toMonoidHom.comp ψ
  have hφsurj : Function.Surjective φ := eJ.surjective.comp hψsurj
  have hφker : ∀ q, φ q = 1 → q ∈ Subgroup.center ↥Q := by
    intro q hq
    have hqψ : ψ q = 1 := by
      have h' := congrArg eJ.symm hq
      simpa [φ] using h'
    have hq1 : (π.comp Q.subtype) q = 1 := by
      have h' := congrArg (fun y : ↥(Q.map π) => (y : LargeEvenProj S)) hqψ
      simpa [ψ] using h'
    have hqker : Q.subtype q ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact hq1
    have hqS : (Q.subtype q : ↥S) ∈ Subgroup.center ↥S := hker hqker
    rw [Subgroup.mem_center_iff] at hqS ⊢
    intro y
    apply Subtype.ext
    exact hqS (Q.subtype y)
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.S11.y10xF_quot_center_equiv_of_surj
    φ hφsurj hQq'.1.commutator_eq_top hφker
  let eSU : ↥Q ≃* ↥(unitarySU 2 n K I.card) := (TableBUE.blockSUEquiv (K := K) (n := n) I h).symm
  have hZmap : (Subgroup.center ↥Q).map (eSU : ↥Q →* ↥(unitarySU 2 n K I.card)) =
      Subgroup.center ↥(unitarySU 2 n K I.card) := Subgroup.map_center_eq eSU
  let eQ : ↥Q ⧸ Subgroup.center ↥Q ≃* ↥(unitarySU 2 n K I.card) ⧸
      Subgroup.center ↥(unitarySU 2 n K I.card) :=
    QuotientGroup.congr (Subgroup.center ↥Q) (Subgroup.center ↥(unitarySU 2 n K I.card)) eSU hZmap
  let τ' : K ≃+* K := RingEquiv.ofBijective h.bar (Function.Involutive.bijective h.bar_bar)
  have hτ' : ∀ x, τ' (τ' x) = x := fun x => h.bar_bar x
  have hτ'm : ∀ x, τ' x = x ^ (2 ^ n) := fun x => h.bar_apply x
  have hE : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, Nat.mul_comm]
  have ham : (I.card, 2 ^ n) ≠ (3, 2) := by
    intro hcon
    have hcard3 : I.card = 3 := by simpa using congrArg Prod.fst hcon
    have hpow : 2 ^ n = 2 := by simpa using congrArg Prod.snd hcon
    exfalso
    have hn1 : n = 1 := by
      have h2 : (2 : ℕ) ^ n = 2 ^ 1 := by simpa using hpow
      exact Nat.pow_right_injective (by norm_num) h2
    subst hn1
    haveI : Group.IsSolvable ↥(unitarySU 2 1 K I.card) :=
      WitSU.isSolvable_unitarySU_two_one h (by omega) (by omega)
    haveI hsolQ : Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := 1) I) :=
      Group.isSolvable_of_surjective (f := (TableBUE.blockSUEquiv I h).toMonoidHom)
        (TableBUE.blockSUEquiv I h).surjective
    haveI hsolJ : Group.IsSolvable ↥J₀ := by
      have hres := Group.isSolvable_of_surjective
        (f := (π.comp (TableBUE.blockSU (K := K) (n := 1) I).subtype).rangeRestrict)
        (MonoidHom.rangeRestrict_surjective _)
      rw [MonoidHom.range_comp, Subgroup.range_subtype] at hres
      rw [hmap] at hres
      exact hres
    exact (ltrcu1_not_isSolvable_of_isQuasisimple hJ₀) hsolJ
  obtain ⟨e2'⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ' hτ' hτ'm hE hc3 ham
  have hH : CFSG.LieType.SemisimpleCentralizers.Held.heldSU I.card K τ' hτ' =
      unitarySU 2 n K I.card :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU (Q := 2 ^ n) hτ'm
  have hZmap2 : (Subgroup.center ↥(unitarySU 2 n K I.card)).map
      ((MulEquiv.subgroupCongr hH).symm : ↥(unitarySU 2 n K I.card) →*
        ↥(CFSG.LieType.SemisimpleCentralizers.Held.heldSU I.card K τ' hτ')) =
      Subgroup.center ↥(CFSG.LieType.SemisimpleCentralizers.Held.heldSU I.card K τ' hτ') :=
    Subgroup.map_center_eq _
  let eU : ↥(unitarySU 2 n K I.card) ⧸ Subgroup.center ↥(unitarySU 2 n K I.card) ≃*
      ↥(CFSG.LieType.SemisimpleCentralizers.Held.heldSU I.card K τ' hτ') ⧸
        Subgroup.center ↥(CFSG.LieType.SemisimpleCentralizers.Held.heldSU I.card K τ' hτ') :=
    QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hH).symm hZmap2
  let e2 : ↥(unitarySU 2 n K I.card) ⧸ Subgroup.center ↥(unitarySU 2 n K I.card) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU I.card (2 ^ n) K) := eU.trans e2'
  let e : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU I.card (2 ^ n) K) :=
    e1.symm.trans (eQ.trans e2)
  have hEq : I.card - 1 + 1 = I.card := Nat.sub_add_cancel (by omega : 1 ≤ I.card)
  have hlabel_twA : GGHasLabel (⟨.twA, I.card - 1, n⟩ : LargeEvenLabel)
      (↥J₀ ⧸ Subgroup.center ↥J₀) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA (E := K) (b := I.card - 1) (m := n)
      hE (hEq.symm ▸ e)
  have hbm : I.card - 1 = 2 → 2 ≤ n := by
    intro hI2
    have hc3' : I.card = 3 := by omega
    have h2n : 2 ^ n ≠ 2 := fun hp => ham (Prod.ext hc3' hp)
    have h1n : 1 ≤ n := h.one_le
    have : n ≠ 1 := fun hn1 => h2n (by rw [hn1]; norm_num)
    omega
  have hlam_twA : LargeEvenInLambda2 (⟨.twA, I.card - 1, n⟩ : LargeEvenLabel) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA h.one_le (by omega) hbm
  have hlam_A : LargeEvenInLambda2 (⟨.A, 1, m⟩ : LargeEvenLabel) := by
    obtain ⟨E, hfE, hfinE, hEcard, ⟨e0⟩⟩ := by
      simpa only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear] using hlabel
    letI : Field E := hfE
    letI : Finite E := hfinE
    haveI : IsSimpleGroup (↥J₀ ⧸ Subgroup.center ↥J₀) := hJ₀.2.1
    have hSL : CFSG.Assembly.LargeEvenSLGroup (Fin (1 + 1)) E = CFSG.Open.StatedSL 2 E :=
      CFSG.Assembly.largeEvenSLGroup_eq_statedSL 2
    have e0' : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 E) := hSL ▸ e0
    exact (S2MathAs51600RALabels.admissible_typeA_of_psl (Q := ↥J₀ ⧸ Subgroup.center ↥J₀)
      (a := 2) (m := m) (E := E) (by norm_num) hEcard e0').1
  exact ltrcu1_not_labelIso_twA_A
    (ggLabelRigidInput_holds (lab := ⟨.twA, I.card - 1, n⟩) (lab' := ⟨.A, 1, m⟩)
      (R := ↥J₀ ⧸ Subgroup.center ↥J₀) hlam_twA hlam_A hlabel_twA hlabel)

theorem unitaryBlockOfComponent_holds :
    UnitaryBlockOfComponent := by
  classical
  intro d n _ K _ _ h h3 τ hτ D hDnorm hD J₀ hJ₀ m hlabel
  let S : Subgroup (GL (Fin d) K) := unitarySU 2 n K d
  let π : ↥S →* LargeEvenProj S := LargeEvenProjMk S
  let A : Subgroup.normalizer (S : Set (GL (Fin d) K)) := ⟨D, hDnorm⟩
  let α : MulAut ↥S := S.normalizerMonoidHom A
  let cD : MulAut (LargeEvenProj S) := TableB.projConj S A
  have hker : π.ker ≤ Subgroup.center ↥S := ltrcu1_ker_projMk_le_center
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hc : ∀ l : ↥S, cD (π l) = π (α l) := fun l => TableB.projConj_mk S A l
  obtain ⟨hQ, hQmap⟩ :=
    USixTwo.isComponentOf_lift_fix (π := π) (a := α) (ab := cD) hπ hker hc hJ₀
  have ht : ∀ i, (τ i : K) ≠ 0 := fun i => Units.ne_zero (τ i)
  have hαcoe : ∀ s : ↥S, ((α s : ↥S) : GL (Fin d) K) = D * (s : GL (Fin d) K) * D⁻¹ := by
    intro s
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hmat : (D : Matrix (Fin d) (Fin d) K) = Matrix.diagonal (fun i => (τ i : K)) := by
    rw [hD, CFSG.SectionRank.OddCover.coe_diagHom]
  have hδ : ∀ s : ↥S,
      (((α s : ↥S) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          Matrix.diagonal (fun i => (τ i : K)) =
        Matrix.diagonal (fun i => (τ i : K)) *
          ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro s
    rw [hαcoe s, ← hmat]
    have h1 : (D * (s : GL (Fin d) K) * D⁻¹ : GL (Fin d) K) * D =
        D * (s : GL (Fin d) K) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    have h2 := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) h1
    simpa [Units.val_mul] using h2
  obtain ⟨i₀, hIcard2raw, hQblkRaw⟩ :=
    eq_blockSU_of_isComponentOf_ggFix_diag (hKd := h) (t := fun i => (τ i : K)) ht α hδ hQ
  let I : Finset (Fin d) := Finset.univ.filter (fun i => (τ i : K) = (τ i₀ : K))
  have hIcard2 : 2 ≤ I.card := hIcard2raw
  have hQblk : ⁅J₀.comap π, J₀.comap π⁆ = TableBUE.blockSU (K := K) (n := n) I := hQblkRaw
  have hIclosed : ∀ i ∈ I, ∀ j, τ j = τ i → j ∈ I := by
    intro i hi j hj
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [show (τ j : K) = (τ i : K) from congrArg (fun u : Kˣ => (u : K)) hj, hi]
  have hIconst : ∀ i ∈ I, ∀ j ∈ I, τ i = τ j := by
    intro i hi j hj
    apply Units.ext
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rw [hi, hj]
  have hJ₀eq : J₀ = (TableBUE.blockSU (K := K) (n := n) I).map π := by
    rw [← hQmap, hQblk]
  have hIcard_eq : I.card = 2 :=
    ltrcu1_blockSU_card_eq_two h hIcard2
      (ltrcu1_isQuasisimple_native (hQblk ▸ hQ.2.2)) hJ₀eq.symm
      (ltrcu1_isQuasisimple_native hJ₀.2.2) hker hlabel
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with hn | hn
    · exfalso
      have h1n : 1 ≤ n := h.one_le
      have hn1 : n = 1 := by omega
      subst hn1
      haveI : Group.IsSolvable ↥(unitarySU 2 1 K I.card) :=
        WitSU.isSolvable_unitarySU_two_one h (by omega) (by omega)
      haveI hsolQ : Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := 1) I) :=
        Group.isSolvable_of_surjective (f := (TableBUE.blockSUEquiv I h).toMonoidHom)
          (TableBUE.blockSUEquiv I h).surjective
      haveI hsolJ : Group.IsSolvable ↥J₀ := by
        have hres := Group.isSolvable_of_surjective
          (f := (π.comp (TableBUE.blockSU (K := K) (n := 1) I).subtype).rangeRestrict)
          (MonoidHom.rangeRestrict_surjective _)
        rw [MonoidHom.range_comp, Subgroup.range_subtype] at hres
        rw [← hJ₀eq] at hres
        exact hres
      exact (ltrcu1_not_isSolvable_of_isQuasisimple
        (ltrcu1_isQuasisimple_native hJ₀.2.2)) hsolJ
    · exact hn
  exact ⟨hn2, I, hIcard_eq, hIclosed, hIconst, hJ₀eq⟩

end CFSG.StandardType.KD2Pieces1615

end
