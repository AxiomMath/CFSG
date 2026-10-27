module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofOneField
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldTransfer
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldGL3Twisted
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace HeringOF

theorem psuConj_eq_one_of_scalar {p f : ℕ} {F : Type} [Field F] {hF : UnitaryFieldData p f F}
    (A : unitaryIsom3 hF) {b : F}
    (hb : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = b • (1 : Matrix (Fin 3) (Fin 3) F)) :
    psuConj hF A = 1 := by
  have hcomm : ∀ g : GL (Fin 3) F, (A : GL (Fin 3) F) * g = g * (A : GL (Fin 3) F) := fun g =>
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, hb, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one])
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [coe_suConj]
    calc (A : GL (Fin 3) F) * (g : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ =
        (g : GL (Fin 3) F) * (A : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ := by rw [hcomm]
      _ = (g : GL (Fin 3) F) := by group

section Certs


theorem not_isType419_of_psuConj_fixed {p f : ℕ} {F : Type} [Field F]
    {hF : UnitaryFieldData p f F} (A : unitaryIsom3 hF) (hA1 : psuConj hF A ≠ 1)
    (hA3 : psuConj hF (A ^ 3) = 1) {K : Type} [Group K] (hK : IsType419 K)
    (hs : IsSimpleGroup K) (hZ : Subgroup.center K = ⊥)
    (T : Subgroup (unitarySU p f F 3)) (θ : T →* K) (hθ : Function.Surjective θ)
    (hker : ∀ t : T, θ t = 1 → (t : unitarySU p f F 3) ∈ unitaryScalars hF 3)
    (hfix : ∀ t : T, psuConj hF A (unitaryProj hF 3 t) = unitaryProj hF 3 t) : False := by
  haveI := hF.finite
  obtain ⟨-, c, -, hAc⟩ := eq_one_of_psuConj_mul_psuField_eq_one (A ^ 3) 1
    (by rw [map_one, mul_one]; exact hA3)
  have hA3m : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have h1 : ((A ^ 3 : unitaryIsom3 hF) : GL (Fin 3) F) = (A : GL (Fin 3) F) ^ 3 := rfl
    rw [h1] at hAc
    have h2 := congrArg Units.val hAc
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at h2
    exact h2
  have hAn : ∀ b : F, ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠
      b • (1 : Matrix (Fin 3) (Fin 3) F) := fun b hb => hA1 (psuConj_eq_one_of_scalar A hb)
  let ρ : T →* GL (Fin 3) F := (unitarySU p f F 3).subtype.comp T.subtype
  have hρ : Function.Injective ρ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  refine HeringOF.not_isType419_of_twisted_gl3 ρ hρ hK hs hZ θ hθ ?_ (A : GL (Fin 3) F) c hA3m
    hAn ?_
  · intro t ht
    obtain ⟨c', -, -, hc'⟩ := hker t ht
    exact ⟨c', hc'⟩
  · intro t
    have h1 : ((suConj hF A (t : unitarySU p f F 3) : unitarySU p f F 3) :
        unitaryPSU hF 3) = ((t : unitarySU p f F 3) : unitaryPSU hF 3) := hfix t
    obtain ⟨c', -, -, hc'⟩ := QuotientGroup.eq.mp h1
    refine ⟨c'⁻¹, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_suConj] at hc'
    change _ = (ρ t) * _
    have h2 : (A : GL (Fin 3) F) * (t : GL (Fin 3) F) * (A : GL (Fin 3) F)⁻¹ =
        (t : GL (Fin 3) F) * (Matrix.GeneralLinearGroup.scalar (Fin 3) c')⁻¹ := by
      rw [← hc']
      group
    rw [← map_inv] at h2
    exact h2

end Certs

end HeringOF

namespace HeringOF

theorem isInnerAut_centerDescend {S : Type*} [Group S] {τ : MulAut S} (h : IsInnerAut τ) :
    IsInnerAut (centerDescend S τ) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨(g : S ⧸ Subgroup.center S), ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H y => rfl

theorem descend_apply_proj {p f : ℕ} {F : Type} [Field F] {hF : UnitaryFieldData p f F}
    (hq : 2 < p ^ f) (τ : MulAut (unitarySU p f F 3)) (g : unitarySU p f F 3) :
    MulAut.congr (suCenterEquiv hF hq) (centerDescend _ τ) (unitaryProj hF 3 g) =
      unitaryProj hF 3 (τ g) := by
  have h1 : unitaryProj hF 3 g = suCenterEquiv hF hq (g : unitarySU p f F 3 ⧸
      Subgroup.center (unitarySU p f F 3)) := rfl
  rw [h1, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, centerDescend_mk]
  rfl

theorem isPerfect_unitarySU_three {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)
    (hq : 2 < p ^ f) : Group.IsPerfect (unitarySU p f F 3) := by
  have := hF.finite
  have : Fact p.Prime := ⟨hF.prime⟩
  have hcard : Nat.card F = (p ^ f) ^ 2 := by rw [hF.card, ← pow_mul, mul_comm]
  exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl
    (by intro hh; simp only [Prod.mk.injEq, true_and] at hh; omega)).1.1

end HeringOF

section Final


theorem k419OneFieldPSU3_holds : K419OneFieldPSU3 := by
  intro G _ _ L hL h46 p f F _ hF hq x a hx3 hxa hxk haL ha3 haC hdiag K hKle hKc ht
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU hF 3) := by
    rcases hxk with ⟨e, -⟩ | ⟨e, -⟩ <;> exact ⟨e⟩
  obtain ⟨e', A, hA⟩ : ∃ (e' : L ⧸ aschbacherSolvableCore 3 L ≃* unitaryPSU hF 3)
      (A : unitaryIsom3 hF), psuConj hF A = inducedAutHom L e' ⟨a, haL⟩ := by
    rcases hdiag with hin | ⟨e', hx', hd⟩
    · have hinner : IsInnerAut (inducedAutHom L e ⟨a, haL⟩) := by
        by_contra h
        exact hin ((not_isInnerAut_inducedAutHom_iff L e haL).mp h)
      obtain ⟨A, hA⟩ := (stdPinnedPSU3 hF).isInnerDiagonal_of_isInnerAut hinner
      exact ⟨e, A, hA⟩
    · obtain ⟨A, hA⟩ := hd.1
      exact ⟨e', A, hA⟩
  have hτ3 := inducedAutHom_pow_eq_one L e' haL ha3'
  have hA3 : psuConj hF (A ^ 3) = 1 := by rw [map_pow, hA]; exact hτ3
  have hA1 : psuConj hF A ≠ 1 := by
    intro h1
    apply haC
    refine Item419Res3.mem_centralizer_of_inducedAutHom_eq_one hL e' haL ?_
    rw [← hA, h1]
  obtain ⟨hs, hZ, ι, hι, hfix⟩ := HeringOF.exists_injective_fixSub haL hKle hKc ht e'
  let T : Subgroup (unitarySU p f F 3) := ι.range.comap (unitaryProj hF 3)
  let eι : K ≃* ι.range := MonoidHom.ofInjective hι
  let θ : T →* K := (eι.symm : ι.range →* K).comp
    (((unitaryProj hF 3).comp T.subtype).codRestrict ι.range fun t => t.2)
  refine HeringOF.not_isType419_of_psuConj_fixed A hA1 hA3 ht hs hZ T θ ?_ ?_ ?_
  · intro k
    obtain ⟨g, hg⟩ := unitaryProj_surjective hF 3 (ι k)
    refine ⟨⟨g, ⟨k, hg.symm⟩⟩, ?_⟩
    change eι.symm ⟨unitaryProj hF 3 g, _⟩ = k
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hg
  · intro t ht1
    have h1 : (⟨unitaryProj hF 3 (t : unitarySU p f F 3), t.2⟩ : ι.range) = 1 := by
      have : eι.symm ⟨unitaryProj hF 3 (t : unitarySU p f F 3), t.2⟩ = 1 := ht1
      exact (MulEquiv.map_eq_one_iff eι.symm).mp this
    have h2 : (t : unitarySU p f F 3) ∈ (unitaryProj hF 3).ker := congrArg Subtype.val h1
    rwa [ker_unitaryProj] at h2
  · intro t
    obtain ⟨k, hk⟩ := Subgroup.mem_comap.mp t.2
    rw [← hk, hA]
    exact Item426.mem_fixSub.mp (hfix k)

theorem k419OneFieldSU3_holds : K419OneFieldSU3 := by
  intro G _ _ L hL h46 p f F _ hF hq x a hx3 hxa hxk haL ha3 haC hdiag K hKle hKc ht
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f F 3) := by
    rcases hxk with ⟨e, -⟩ | ⟨e, -⟩ <;> exact ⟨e⟩
  haveI := HeringOF.isPerfect_unitarySU_three hF hq
  obtain ⟨e', A, hA⟩ : ∃ (e' : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU p f F 3)
      (A : unitaryIsom3 hF), psuConj hF A = MulAut.congr (suCenterEquiv hF hq)
        (centerDescend _ (inducedAutHom L e' ⟨a, haL⟩)) := by
    rcases hdiag with hin | ⟨e', hx', hd⟩
    · have hinner : IsInnerAut (inducedAutHom L e ⟨a, haL⟩) := by
        by_contra h
        exact hin ((not_isInnerAut_inducedAutHom_iff L e haL).mp h)
      have hinner' : IsInnerAut (MulAut.congr (suCenterEquiv hF hq)
          (centerDescend _ (inducedAutHom L e ⟨a, haL⟩))) :=
        (isInnerAut_congr _ _).mpr (HeringOF.isInnerAut_centerDescend hinner)
      obtain ⟨A, hA⟩ := (stdPinnedPSU3 hF).isInnerDiagonal_of_isInnerAut hinner'
      exact ⟨e, A, hA⟩
    · obtain ⟨A, hA⟩ := hd.1
      exact ⟨e', A, hA⟩
  set τ := inducedAutHom L e' ⟨a, haL⟩ with hτ
  have hτ3 : τ ^ 3 = 1 := inducedAutHom_pow_eq_one L e' haL ha3'
  have hA3 : psuConj hF (A ^ 3) = 1 := by
    rw [map_pow, hA, ← map_pow, ← map_pow, hτ3]
    simp only [map_one]
  have hA1 : psuConj hF A ≠ 1 := by
    intro h1
    apply haC
    refine Item419Res3.mem_centralizer_of_inducedAutHom_eq_one hL e' haL ?_
    rw [h1] at hA
    have hd1 : centerDescend _ τ = 1 := by
      apply (MulAut.congr (suCenterEquiv hF hq)).injective
      rw [map_one]
      exact hA.symm
    exact CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp τ hd1
  obtain ⟨hs, hZ, ι, hι, hfix⟩ := HeringOF.exists_injective_fixSub haL hKle hKc ht e'
  let eι : K ≃* ι.range := MonoidHom.ofInjective hι
  refine HeringOF.not_isType419_of_psuConj_fixed A hA1 hA3 ht hs hZ ι.range
    (eι.symm : ι.range →* K) eι.symm.surjective ?_ ?_
  · intro t ht1
    have h1 : t = 1 := (MulEquiv.map_eq_one_iff eι.symm).mp ht1
    rw [h1]
    exact one_mem _
  · intro t
    obtain ⟨k, hk⟩ := t.2
    rw [hA, ← hk, HeringOF.descend_apply_proj hq τ, Item426.mem_fixSub.mp (hfix k)]

end Final

end CFSG.RankThree.PartTwo.Sec4
