module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.GGTCJLabel
public import CFSG.LocalAnalysis.StandardType.GGTCJDivides
public import CFSG.LocalAnalysis.StandardType.GGTCJDivOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10GField

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nL4d_tag_ne_of_ggLabelIso {lab lab' : LargeEvenLabel}
    (h : GGLabelIso lab lab') (h2 : lab'.tag ≠ .G2) (h3 : lab'.tag ≠ .triD4) :
    lab.tag ≠ .G2 ∧ lab.tag ≠ .triD4 := by
  rcases h with h | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · cases h; exact ⟨h2, h3⟩
  · obtain ⟨hB, hB', -, -⟩ := hBC
    constructor
    · intro hh
      rw [hh] at hB
      rcases hB with hB | hB <;> exact absurd hB (by decide)
    · intro hh
      rw [hh] at hB
      rcases hB with hB | hB <;> exact absurd hB (by decide)
  · obtain ⟨h1, -⟩ := hDA; rw [h1]; simp
  · obtain ⟨h1, -⟩ := hAD; rw [h1]; simp
  · obtain ⟨h1, -⟩ := hD3A3; rw [h1]; simp
  · obtain ⟨h1, -⟩ := hA3D3; rw [h1]; simp
  · obtain ⟨h1, -⟩ := hD2A1; rw [h1]; simp
  · obtain ⟨-, h1⟩ := hA1D2; rw [h1]; simp

private theorem l05nL4d_nonabelian_of_central_extension
    {L' R : Type} [Group L'] [Group R] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (J : Subgroup L') (hJsimple : IsSimpleGroup (J ⧸ Subgroup.center J)) :
    ∃ a b : R, a * b ≠ b * a := by
  by_contra hnab
  push Not at hnab
  haveI : IsMulCommutative R := isMulCommutative_iff.mpr hnab
  have hRcomm : commutator R = ⊥ := (commutator_eq_bot_iff R).mpr inferInstance
  have hmap : (commutator L').map ψ = ⊥ := by
    have h1 : (commutator L').map ψ = commutator R := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective _ hψ, commutator_def]
    rw [h1, hRcomm]
  have hle : commutator L' ≤ ψ.ker := by
    intro x hx
    have hx' : ψ x ∈ (commutator L').map ψ := ⟨x, hx, rfl⟩
    rw [hmap] at hx'
    exact hx'
  have hcenter : commutator L' ≤ Subgroup.center L' := hle.trans hker
  have hZtop : Subgroup.center L' = ⊤ := top_le_iff.mp (hperf ▸ hcenter)
  have hcommL' : commutator L' = ⊥ :=
    (commutator_eq_bot_iff L').mpr (isMulCommutative_iff.mpr fun a b =>
      (Subgroup.mem_center_iff.mp (hZtop.symm ▸ Subgroup.mem_top a) b).symm)
  have htopbot : (⊤ : Subgroup L') = ⊥ := by rw [← hperf, hcommL']
  haveI : Subsingleton L' := ⟨fun a b => by
    have ha : a = 1 := Subgroup.mem_bot.mp (by rw [← htopbot]; exact Subgroup.mem_top a)
    have hb : b = 1 := Subgroup.mem_bot.mp (by rw [← htopbot]; exact Subgroup.mem_top b)
    rw [ha, hb]⟩
  haveI : Subsingleton J := ⟨fun a b =>
    Subtype.ext (Subsingleton.elim (a : L') (b : L'))⟩
  haveI : Subsingleton (J ⧸ Subgroup.center J) := inferInstance
  haveI : Nontrivial (J ⧸ Subgroup.center J) := hJsimple.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (J ⧸ Subgroup.center J)
  exact hab (Subsingleton.elim a b)

private theorem l05nL4d_tag_of_orth_component
    (hRig : GGLabelRigidInput)
    {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn : LargeEvenInLambda2 (⟨.D, 4, n⟩ : LargeEvenLabel))
    (α : MulAut S) (hcen : Subgroup.center S = ⊥)
    (hin : InnDiagKind S (⟨.D, 4, n⟩ : LargeEvenLabel) α) (hα : α ^ 3 = 1)
    {K : Subgroup S} (hK : CFSG.Assembly.IsComponentOf K (ggFixSub α))
    {labJ : LargeEvenLabel} (hlabJ : LargeEvenInLambda2 labJ)
    (hhas : GGHasLabel labJ (K ⧸ Subgroup.center K)) :
    labJ.tag ≠ .G2 ∧ labJ.tag ≠ .triD4 := by
  have hFam : CFSG.LocalAnalysis.GLTheoremA.Y10GField.FamOrth (⟨.D, 4, n⟩ : LargeEvenLabel) :=
    Or.inl ⟨rfl, by norm_num⟩
  obtain ⟨hmodel, a, rfl⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthMark.innDiagKind_orth_data hcen hFam hin
  have hap : a ^ 3 = 1 := by
    have hc : a ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := DFunLike.congr_fun (show MulAut.conj (a ^ 3) = 1 by rw [map_pow, hα]) z
      rw [MulAut.conj_apply, MulAut.one_apply] at hz
      exact (mul_inv_eq_iff_eq_mul.mp hz).symm
    rw [hcen] at hc
    exact Subgroup.mem_bot.mp hc
  have hcan : (canonLabel (⟨.D, 4, n⟩ : LargeEvenLabel)).n = n := by simp [canonLabel]
  obtain ⟨t, ht, hG⟩ : ∃ t : StatedLieTag, (t = .POmegaPlus ∨ t = .POmegaMinus) ∧
      StatedClassicalModel S t 4 2 n := by
    rcases hmodel with hG | hG
    · exact ⟨_, Or.inl rfl, by simpa only [hcan] using hG⟩
    · exact ⟨_, Or.inr rfl, by simpa only [hcan] using hG⟩
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  rcases TCJ.tcjOrth_quotCenter_cases_of_component_conj_omega ht hG
      (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2) a hap
      ((CFSG.Assembly.isComponentOf_iff_open).mp hK) with
    hlin | huni | hsymp | horth
  ·
    obtain ⟨b, k, E, hfE, hfinE, hb, hE, -, hφ⟩ := hlin
    letI : Field E := hfE
    letI : Finite E := hfinE
    obtain ⟨eφ⟩ := hφ
    have hM0 : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL b 2 k :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.statedClassicalModel_psl_of_isSimpleGroup
        hb hE eφ
    have hM : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL (b - 1 + 1) 2 k := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ b)]
      exact hM0
    exact l05nL4d_tag_ne_of_ggLabelIso
      (hRig labJ (⟨.A, b - 1, k⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) hlabJ
        (largeEvenInLambda2_typeA hM) hhas (ggHasLabel_typeA hM))
      (show (.A : LargeEvenLieTag) ≠ .G2 by decide)
      (show (.A : LargeEvenLieTag) ≠ .triD4 by decide)
  ·
    obtain ⟨b, k, E, hfE, hfinE, τ, hτ, hb, hτk, hE, -, hφ⟩ := huni
    letI : Field E := hfE
    letI : Finite E := hfinE
    obtain ⟨eφ⟩ := hφ
    by_cases hb2 : b = 2
    · subst hb2
      obtain ⟨k', hfK', hfinK', hk', ⟨ψ⟩⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_quot_heldSU_two_equiv_psl τ hτ hτk hE
      letI : Field k' := hfK'
      letI : Finite k' := hfinK'
      have hM : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 2 2 k :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.statedClassicalModel_psl_of_isSimpleGroup
          (le_refl 2) hk' (eφ.trans ψ)
      exact l05nL4d_tag_ne_of_ggLabelIso
        (hRig labJ (⟨.A, 1, k⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) hlabJ
          (largeEvenInLambda2_typeA (n := 1) hM) hhas (ggHasLabel_typeA (n := 1) hM))
        (show (.A : LargeEvenLieTag) ≠ .G2 by decide)
        (show (.A : LargeEvenLieTag) ≠ .triD4 by decide)
    · by_cases h31 : b = 3 ∧ k = 1
      · exfalso
        obtain ⟨rfl, rfl⟩ := h31
        haveI := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.isSolvable_quot_heldSU_three_two
          τ hτ (fun x => by simpa using hτk x) (by simpa using hE)
        have hsolK : Group.IsSolvable (K ⧸ Subgroup.center K) :=
          solvable_of_surjective (f := eφ.symm.toMonoidHom) eφ.symm.surjective
        exact (CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.not_isSolvable_quot_center
          (J := K)) hsolK
      · have hb3 : 3 ≤ b := by omega
        have ham : (b, 2 ^ k) ≠ (3, 2) := by
          intro h
          obtain ⟨h1, h2⟩ := Prod.mk.inj h
          exact h31 ⟨h1, Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)⟩
        obtain ⟨ψ⟩ :=
          CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.nonempty_quot_heldSU_equiv_statedProj
            CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.uniScalar_holds τ hτ hτk hE hb3 ham
        have hk1 : 1 ≤ k := by
          by_contra hk
          have hk0 : k = 0 := by omega
          have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
          rw [hE, hk0] at h2
          norm_num at h2
        have hb' : b - 1 + 1 = b := Nat.sub_add_cancel (by omega : 1 ≤ b)
        have hlab' : LargeEvenInLambda2 (⟨.twA, b - 1, k⟩ : LargeEvenLabel) :=
          CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA hk1 (by omega)
            (fun hb2' => by
              have hb3' : b = 3 := by omega
              by_contra hk2
              have hk1' : k = 1 := by omega
              exact h31 ⟨hb3', hk1'⟩)
        have hhas' : GGHasLabel (⟨.twA, b - 1, k⟩ : LargeEvenLabel)
            (K ⧸ Subgroup.center K) := by
          refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA hE ?_
          rw [hb']
          exact eφ.trans ψ
        exact l05nL4d_tag_ne_of_ggLabelIso
          (hRig labJ (⟨.twA, b - 1, k⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) hlabJ
            hlab' hhas hhas')
          (show (.twA : LargeEvenLieTag) ≠ .G2 by decide)
          (show (.twA : LargeEvenLieTag) ≠ .triD4 by decide)
  ·
    obtain ⟨s, K', hfK', hfinK', hs, hK'card, hne, hφ⟩ := hsymp
    letI : Field K' := hfK'
    letI : Finite K' := hfinK'
    obtain ⟨eφ⟩ := hφ
    have hlab' : LargeEvenInLambda2 (⟨.B, s, n⟩ : LargeEvenLabel) := by
      refine CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.largeEvenInLambda2_typeB hn.1 hs ?_
      intro hs2
      by_contra hn2
      have hn1' : 1 ≤ n := hn.1
      have hn1 : n = 1 := by omega
      exact hne ⟨hs2, by rw [hK'card, hn1, pow_one]⟩
    have hhas' : GGHasLabel (⟨.B, s, n⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel.ggHasLabel_typeB hK'card eφ
    exact l05nL4d_tag_ne_of_ggLabelIso
      (hRig labJ (⟨.B, s, n⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) hlabJ
        hlab' hhas hhas')
      (show (.B : LargeEvenLieTag) ≠ .G2 by decide)
      (show (.B : LargeEvenLieTag) ≠ .triD4 by decide)
  ·
    rcases horth with ⟨s, hM | hM⟩
    · obtain ⟨-, -, hm⟩ := hM.1
      have hm3 : s ≠ 3 := by omega
      have hlab' : LargeEvenInLambda2 (⟨.D, s, n⟩ : LargeEvenLabel) := by
        show 1 ≤ n ∧ 3 ≤ s
        exact ⟨hn.1, by omega⟩
      have hhas' : GGHasLabel (⟨.D, s, n⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) := by
        show (if s = 3 then _ else _)
        rw [if_neg hm3]
        exact recipeOmegaPlus_of_statedClassicalModel hM
      exact l05nL4d_tag_ne_of_ggLabelIso
        (hRig labJ (⟨.D, s, n⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) hlabJ
          hlab' hhas hhas')
        (show (.D : LargeEvenLieTag) ≠ .G2 by decide)
        (show (.D : LargeEvenLieTag) ≠ .triD4 by decide)
    · obtain ⟨-, -, hm⟩ := hM.1
      have hm2 : s ≠ 2 := by omega
      have hm3 : s ≠ 3 := by omega
      have hlab' : LargeEvenInLambda2 (⟨.twD, s, n⟩ : LargeEvenLabel) := by
        show 1 ≤ n ∧ 2 ≤ s
        exact ⟨hn.1, by omega⟩
      have hhas' : GGHasLabel (⟨.twD, s, n⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) := by
        show (if s = 2 then _ else if s = 3 then _ else _)
        rw [if_neg hm2, if_neg hm3]
        exact recipeOmegaMinus_of_statedClassicalModel hM
      exact l05nL4d_tag_ne_of_ggLabelIso
        (hRig labJ (⟨.twD, s, n⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) hlabJ
          hlab' hhas hhas')
        (show (.twD : LargeEvenLieTag) ≠ .G2 by decide)
        (show (.twD : LargeEvenLieTag) ≠ .triD4 by decide)

@[expose] def GGTCJD4TagKnown : Prop :=
  ∀ n : ℕ, LargeEvenInLambda2 ⟨.D, 4, n⟩ →
    LargeEvenLabelAll ⟨.D, 4, n⟩ fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
            ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
              GGHasLabel labJ (J ⧸ Subgroup.center J) → labJ.tag ≠ .G2 ∧ labJ.tag ≠ .triD4

theorem ggTCJD4TagKnown_holds :
    GGTCJD4TagKnown := by
  intro n hn
  intro Q hQ
  refine largeEvenRawDatum_mono (fun R _ I F hqP => ⟨hqP.1, ?_⟩)
    (TCJ.ggTCJ_datum_marking hn Q hQ)
  intro L' _ _ ψ hψ hker hperf e he hφe J hJ
  let φ : MulAut R := hφe.choose
  have hφI : φ ∈ I := hφe.choose_spec.1
  have hφind : ∀ l : L', φ (ψ l) = ψ (e l) := hφe.choose_spec.2
  have hna : ∃ a b : R, a * b ≠ b * a :=
    l05nL4d_nonabelian_of_central_extension ψ hψ hker hperf J hJ.2.2.2
  haveI : Finite R := hqP.2.1
  have hRsimple : IsSimpleGroup R := (hqP.2.2 hna).1
  have hRinn : InnDiagKind R (⟨.D, 4, n⟩ : LargeEvenLabel) φ := (hqP.2.2 hna).2 φ hφI
  have hRcenter : Subgroup.center R = ⊥ := center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hpow : ∀ m : ℕ, ∀ l : L', (φ ^ m) (ψ l) = ψ ((e ^ m) l) := by
    intro m
    induction m with
    | zero => intro l; simp
    | succ m ih =>
        intro l
        rw [pow_succ, MulAut.mul_apply, hφind l, ih (e l), pow_succ, MulAut.mul_apply]
  have hφ3 : φ ^ 3 = 1 := by
    ext r
    obtain ⟨l, rfl⟩ := hψ r
    have hev : (e ^ 3) l = l := by simpa using congrArg (fun f : MulAut L' => f l) he
    rw [hpow 3 l, hev]
    rfl
  intro labJ hlabJ hhasJ
  obtain ⟨hKcomp, ⟨edesc⟩⟩ := TCJ.ggTCJ_descent ψ hψ hker e φ hφind J hJ
  have hhasK : GGHasLabel labJ ((J.map ψ) ⧸ Subgroup.center (J.map ψ)) :=
    ggHasLabel_of_mulEquiv edesc hhasJ
  exact l05nL4d_tag_of_orth_component ggLabelRigidInput_holds hn
    φ hRcenter hRinn hφ3 hKcomp hlabJ hhasK

end CFSG.StandardType
