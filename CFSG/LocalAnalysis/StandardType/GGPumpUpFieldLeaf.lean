module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158InnHolds2
import CFSG.Quasithin.EmptyFaithful.GoldschmidtEmbedBarQuot
import CFSG.Quasithin.EmptyFaithful.GoldschmidtEmbedLocA7Core
import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs
import CFSG.Quasithin.Vol2.Ch3xC58NSFinal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.YS09Field
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.Chevalley (Tag adjointGroup IsRoot)
open CFSG.LieType.Chevalley (entrywiseAdjointAut fixedFieldImage fixedFieldImage_le
  fixedFieldImageEquiv entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two
  center_adjointGroup_eq_bot fixSubfield)

private theorem ppt2_u33_noncomm :
    ∃ x y : CFSG.Quasithin.U33G, x * y ≠ y * x :=
  CFSG.Quasithin.C58NS.exists_noncomm_of_simple_of_not_prime
    CFSG.Quasithin.isSimpleGroup_u33Pres
    (by rw [CFSG.Quasithin.card_u33Pres]; norm_num)

private theorem ppt2_fixed_equiv
                            {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (σ : K ≃+* K) :
    Nonempty (adjointGroup Tag.G2 (fixSubfield σ) ≃*
      ↥(ggAutFixedSubgroup (entrywiseAdjointAut Tag.G2 σ))) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcharP : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hfix : ggAutFixedSubgroup (entrywiseAdjointAut Tag.G2 σ) =
      (fixedFieldImage Tag.G2 σ).subgroupOf (adjointGroup Tag.G2 K) := by
    rw [gff_ggAutFixedSubgroup_eq_entrywiseFixedGroup Tag.G2 σ,
      entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (Or.inl rfl) hchar σ]
  have hJC : fixedFieldImage Tag.G2 σ ≤ adjointGroup Tag.G2 K :=
    fun x hx => (fixedFieldImage_le hx).1
  exact ⟨(fixedFieldImageEquiv (τ := Tag.G2) σ).trans
    ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.subgroupCongr hfix.symm))⟩

private theorem ppt2_chevFixGroupOn
                            {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : 0 < p) :
    ChevFixGroupOn K Tag.G2 (IsRoot Tag.G2) n p := by
  suffices h : ∀ H : Subgroup (MarkChev.GLS (IsRoot Tag.G2) K), H = adjointGroup Tag.G2 K →
      ∀ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot Tag.G2) K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup Tag.G2 k ≃* ↥(ggFixSub f)) from
    h _ (chevH_false_eq_adjointGroup K Tag.G2)
  intro H hH f hf hford
  subst hH
  have hr : 0 < Tag.G2.rank := by decide
  obtain ⟨σ, hσ⟩ := RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField hf
  have hσp : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut hr σ, ← hσ,
      MulEquiv.orderOf_eq, hford]
  obtain ⟨-, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
    Nat.prime_two hn hK σ
  rw [hσp] at hcard
  obtain ⟨E⟩ := ppt2_fixed_equiv hn hK σ
  let m : LargeEvenCenterQuot (adjointGroup Tag.G2 K) ≃* adjointGroup Tag.G2 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have key : ∀ x, ((1 : MulAut (adjointGroup Tag.G2 K)) * entrywiseAdjointAut Tag.G2 σ * 1⁻¹)
      (m x) = m (f x) := by
    intro x
    rw [one_mul, inv_one, mul_one, ← hσ, RecipeExcLang.autEquiv, MulAut.congr_apply]
    simp only [m, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  obtain ⟨E'⟩ := gff_nonempty_equiv_fixed m f 1 (entrywiseAdjointAut Tag.G2 σ) key E
  exact ⟨↥(fixSubfield σ), inferInstance, inferInstance, hcard,
    ⟨E'.symm.trans (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))⟩⟩

private theorem ppt2_fixGroup
                            {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false))}
    (hf : f ∈ LargeEvenChevFieldImage LargeEvenCartanG2 K
    (LargeEvenChevH LargeEvenCartanG2 K false))
    (hord : orderOf f = p) :
    p ∣ n ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
      Nonempty (adjointGroup Tag.G2 k ≃* ↥(ggFixSub f)) := by
  refine ⟨dvd_of_chevField_order hn hK hp (LargeEvenChevH LargeEvenCartanG2 K false)
    (fun σ h hh => chevH_stable LargeEvenCartanG2 K false σ h hh) hf hord, ?_⟩
  have h := (ppt2_chevFixGroupOn hn hK hp.pos).of_eq (largeEvenIsRoot_eq_isRoot Tag.G2).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL LargeEvenCartanG2 K),
      H = MarkChev.chevH LargeEvenCartanG2 (LargeEvenIsRoot LargeEvenCartanG2) K false →
      ∀ f ∈ LargeEvenChevFieldImage LargeEvenCartanG2 K H, orderOf f = p →
        ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
          Nonempty (adjointGroup Tag.G2 k ≃* ↥(ggFixSub f)) from
    key _ (largeEvenChevH_eq LargeEvenCartanG2 K false) f hf hord
  intro H hH
  subst hH
  exact h

theorem fixGapG2_reduced_holds :
    FixGapG2 := by
  intro n p K _ _ hn hK hp _ f hf hord
  obtain ⟨hpn, k, hkF, hkfin, hk, ⟨E⟩⟩ := ppt2_fixGroup (by omega) hK hp hf hord
  have hdiv : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  refine ⟨hpn, ?_⟩
  rcases Nat.lt_or_ge (n / p) 2 with hlt | hge
  ·
    have h1 : n / p = 1 := by omega
    have hk2 : Nat.card k = 2 := by rw [hk, h1]; norm_num
    obtain ⟨eP⟩ := CFSG.Quasithin.g2_derived_mulEquiv_PSU3 k hk2
    obtain ⟨eU⟩ := CFSG.Quasithin.u33Pres_mulEquiv_PSU3
    haveI := CFSG.Quasithin.isSimpleGroup_u33Pres
    let eQ : ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ ≃* CFSG.Quasithin.U33G :=
      eP.trans eU.symm
    haveI : IsSimpleGroup ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ := eQ.isSimpleGroup
    have hZ : Subgroup.center ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆) with h | h
      · exact h
      · exfalso
        obtain ⟨x, y, hxy⟩ := ppt2_u33_noncomm
        apply hxy
        have hc : ∀ a b : ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆, a * b = b * a := by
          intro a b
          have ha : a ∈ Subgroup.center ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ := by
            rw [h]; exact Subgroup.mem_top a
          exact ((Subgroup.mem_center_iff.mp ha) b).symm
        have key := congrArg eQ (hc (eQ.symm x) (eQ.symm y))
        simpa using key
    have hsimp : IsSimpleGroup (LargeEvenCenterQuot ⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆)
    :=
      (centerQuotEquivOfBot hZ).isSimpleGroup
    have hnab : ∃ a b : LargeEvenCenterQuot ⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆,
        a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ := ppt2_u33_noncomm
      let eR := (centerQuotEquivOfBot hZ).trans eQ
      exact ⟨eR.symm x, eR.symm y, fun h => hxy (by simpa using congrArg eR h)⟩
    have hlab : GGHasLabel (⟨.G2der, 0, 1⟩ : LargeEvenLabel)
        (CFSG.Blueprint.DerivedCentralQuotient (adjointGroup Tag.G2 k)) := by
      unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      obtain ⟨eD⟩ := centerQuot_commutator_chevGroup_equiv k Tag.G2
      exact ⟨k, hkF, hkfin, hk2, ⟨eD.symm⟩⟩
    have e1 : ↥(ggFixDer f) ≃* ↥⁅adjointGroup Tag.G2 k, adjointGroup Tag.G2 k⁆ :=
      (ggCommutatorEquiv (ggFixSub f)).trans
        ((fixG2_commutator_mulEquiv E).some.symm.trans
          (ggCommutatorEquiv (adjointGroup Tag.G2 k)).symm)
    refine ⟨CFSG.Blueprint.DerivedCentralQuotient (adjointGroup Tag.G2 k), inferInstance,
      (⟨.G2der, 0, 1⟩ : LargeEvenLabel), hsimp, hnab, ⟨le_refl _, rfl, rfl⟩, ?_, hlab,
      ⟨e1.trans (centerQuotEquivOfBot hZ).symm⟩⟩
    rw [h1]
    rfl
  ·
    have h3 : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n / p) := Nat.pow_le_pow_right (by norm_num) hge
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card k h3
    haveI : Group.IsPerfect ↥(adjointGroup Tag.G2 k) := hq.1
    have hZ : Subgroup.center (adjointGroup Tag.G2 k) = ⊥ := center_adjointGroup_eq_bot
    have hPC : Group.IsPerfect ↥(ggFixSub f) :=
      Group.IsPerfect.ofSurjective (f := E.toMonoidHom) E.surjective
    have hdef : ggFixDer f = ggFixSub f := Subgroup.isPerfect_iff.1 hPC
    refine ⟨LargeEvenCenterQuot (adjointGroup Tag.G2 k), inferInstance,
      (⟨.G2, 0, n / p⟩ : LargeEvenLabel), hq.2.1, hq.2.2, ⟨hdiv, rfl, hge⟩, rfl, ?_, ?_⟩
    · unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
      obtain ⟨eC⟩ := centerQuot_chevGroup_equiv k Tag.G2
      exact ⟨k, hkF, hkfin, hk, ⟨eC.symm⟩⟩
    · exact ⟨(MulEquiv.subgroupCongr hdef).trans (E.symm.trans (centerQuotEquivOfBot hZ).symm)⟩

theorem fldPiece_reduced_holds :
    FldPiece :=
  fun S _ _ p α J labK labJ hp hp2 hcen hfld hnot hα hlabJ hJ =>
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.fld_of_families
      (CFSG.LocalAnalysis.GLTheoremA.Y10GField.fldLin_of_labelDict
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_holds)
      (CFSG.LocalAnalysis.GLTheoremA.Y10GFldUni.fldUni_of_sigmaPow
        CFSG.LocalAnalysis.GLTheoremA.Y10GFldUniSig.uniSigmaPowOne_holds)
      CFSG.LocalAnalysis.GLTheoremA.Y10GField.fldSymp_holds
      CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth.fldOrth_holds
      (CFSG.LocalAnalysis.GLTheoremA.Y10GField.fldExc_of_gaps
        fixGapG2_reduced_holds
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.fixGapE6_holds
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.fixGapTwE6_holds
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.fixGapTriD4_holds
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.fixGapTwB2_holds
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.fixGapTwF4_holds)
      S p α J labK labJ hp hp2 hcen hfld hnot hα hlabJ hJ

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
