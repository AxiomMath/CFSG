module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

import CFSG.GroupTheory.IsComponentOfMap

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def KGFieldRestrictionCont (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ f ∈ F, orderOf f = p →
    ∀ h ∈ I, h ^ p = 1 → h * f = f * h →
      ∀ J₀ : Subgroup R,
        IsComponentOf J₀ (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)) →
        ∀ f' : MulAut J₀, (∀ j : J₀, (f' j : R) = f j) →
          GGMarkingAll (K := J₀) fun _ R' _ I' _ θ' => kgInducedAut θ' f' ∉ I'

@[expose] def KGFieldRestrictionOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    ¬ GGNbrLangT3Label p lab → S p lab → LargeEvenLabelAll lab (KGFieldRestrictionCont p)

private theorem l02qr1_eqLocus_conj {R : Type*} [Group R] (v h : MulAut R) :
    (MonoidHom.eqLocus (h : R →* R) (MonoidHom.id R)).map v.toMonoidHom =
      MonoidHom.eqLocus ((v * h * v⁻¹ : MulAut R) : R →* R) (MonoidHom.id R) := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : h y = y := hy
    change (v * h * v⁻¹) (v y) = v y
    simpa [MulAut.mul_apply] using congrArg (fun z => v z) hy'
  · intro hx
    have hx' : (v * h * v⁻¹) x = x := hx
    refine ⟨v⁻¹ x, ?_, by simp⟩
    change h (v⁻¹ x) = v⁻¹ x
    have := congrArg (fun z => v⁻¹ z) hx'
    simpa [MulAut.mul_apply] using this

private theorem l02qr1_centerQuotAut_naturality {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (a : MulAut X) (q : X ⧸ Subgroup.center X) :
    centerQuotCongr e (centerQuotAut X a q) =
      centerQuotAut Y (e.symm.trans (a.trans e)) (centerQuotCongr e q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp [centerQuotAut_mk, centerQuotCongr_mk]

private theorem l02qr1_centerQuotAut_transport {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (a : MulAut X) (q : X ⧸ Subgroup.center X) :
    centerQuotCongr e.symm
      (centerQuotAut Y (e.symm.trans (a.trans e)) (centerQuotCongr e q)) =
      centerQuotAut X a q := by
  have h := l02qr1_centerQuotAut_naturality e a q
  rw [← h]
  simp [centerQuotCongr_symm]

private theorem l02qr1_isComponentOf_map_mulEquiv {G H : Type} [Group G] [Group H]
    (e : G ≃* H) {L K : Subgroup G} (h : IsComponentOf L K) :
    IsComponentOf (L.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  isComponentOf_iff_open.mpr (CFSG.isComponentOf_map_mulEquiv e (isComponentOf_iff_open.mp h))

private theorem l02qr1_kgInducedAut_apply {K R : Type*} [Group K] [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (a : MulAut K) (q : K ⧸ Subgroup.center K) :
    kgInducedAut θ a (θ q) = θ (centerQuotAut K a q) := by
  simp [kgInducedAut, MulAut.congr_apply]

theorem kgFieldNotInnerCont_of_restriction {R : Type} [Group R] [IsSimpleGroup R]
    {I F : Set (MulAut R)} {p : ℕ} (hna : ∃ a b : R, a * b ≠ b * a)
    (hc : GGRawFieldConj p R I F) (hinn : GGRawInnField p R I F)
    (hres : KGFieldRestrictionCont p R I F) : KGFieldNotInnerCont p R I F := by
  intro α hαmem hαnot hαp h hh hhp hcomm J₀ hJ₀ α' hα'
  obtain ⟨u, hu, f, hf, rfl⟩ := hαmem
  obtain ⟨f', hf'F, u', hu'I, hord, heq⟩ :=
    hc inferInstance hna u hu f hf hαnot hαp
  obtain ⟨hmul, hinv, -, -⟩ := hinn inferInstance hna
  set v : MulAut R := u'⁻¹ with hv_def
  set h' : MulAut R := v * h * v⁻¹ with hh'_def
  have hu'inv : u'⁻¹ ∈ I := hinv u' hu'I
  have hh'I : h' ∈ I := by
    have hmem : u'⁻¹ * (h * u') ∈ I := hmul u'⁻¹ hu'inv (h * u') (hmul h hh u' hu'I)
    simpa [hh'_def, hv_def, mul_assoc] using hmem
  have hαv : (u * f : MulAut R) = v⁻¹ * f' * v := by
    rw [heq, hv_def]
    group
  have hhp' : h' ^ p = 1 := by
    rw [hh'_def, conj_pow, hhp, mul_one, mul_inv_cancel]
  have hcomm' : h' * f' = f' * h' := by
    have h1 := congrArg (fun x => v * x * v⁻¹) hcomm
    simpa [hαv, hh'_def, mul_assoc] using h1
  set J₀' : Subgroup R := J₀.map v.toMonoidHom with hJ₀'_def
  have hJ₀' : IsComponentOf J₀'
      (MonoidHom.eqLocus (h' : R →* R) (MonoidHom.id R)) := by
    have hm := l02qr1_isComponentOf_map_mulEquiv v hJ₀
    rw [l02qr1_eqLocus_conj v h] at hm
    simpa [hJ₀'_def, hh'_def] using hm
  let e : J₀ ≃* J₀' := Subgroup.equivMapOfInjective J₀ v.toMonoidHom v.injective
  let f'' : MulAut J₀' := e.symm.trans (α'.trans e)
  have hf'' : ∀ j : J₀', (f'' j : R) = f' j := by
    intro j
    have h1 : ((f'' j : J₀') : R) = v (((α' (e.symm j)) : J₀) : R) := by
      dsimp only [f'', e]
      rw [MulEquiv.trans_apply]
      rfl
    have h2 : ((α' (e.symm j) : J₀) : R) =
        (u * f) ((e.symm j : J₀) : R) := hα' (e.symm j)
    have h3 : v ((e.symm j : J₀) : R) = (j : R) := by
      have h := congrArg (fun z : J₀' => (z : R)) (e.apply_symm_apply j)
      dsimp only [e] at h ⊢
      exact h
    have h4 : (u * f) ((e.symm j : J₀) : R) =
        v⁻¹ (f' (v ((e.symm j : J₀) : R))) := by
      rw [hαv, MulAut.mul_apply, MulAut.mul_apply]
    calc (f'' j : R) = v (((α' (e.symm j)) : J₀) : R) := h1
      _ = v ((u * f) ((e.symm j : J₀) : R)) := by rw [h2]
      _ = v (v⁻¹ (f' (v ((e.symm j : J₀) : R)))) := by rw [h4]
      _ = f' (v ((e.symm j : J₀) : R)) := by simp
      _ = f' j := by rw [h3]
  have hres' := hres f' hf'F hord h' hh'I hhp' hcomm' J₀' hJ₀' f'' hf''
  refine ggMarkingAll_congr e.symm ?_ hres'
  intro lab R' _ I' F' θ hθ
  have hkg : kgInducedAut ((centerQuotCongr e.symm).trans θ) f'' =
      kgInducedAut θ α' := by
    ext x
    obtain ⟨q, rfl⟩ := θ.surjective x
    have hx : ((centerQuotCongr e.symm).trans θ) (centerQuotCongr e q) = θ q := by
      simp [MulEquiv.trans_apply, centerQuotCongr_symm]
    conv_lhs => rw [← hx]
    rw [l02qr1_kgInducedAut_apply, l02qr1_kgInducedAut_apply]
    simp only [MulEquiv.trans_apply]
    rw [l02qr1_centerQuotAut_transport e α' q]
  rw [hkg] at hθ
  exact hθ

theorem kgFieldNotInnerInputOn_of_restriction {S : ℕ → LargeEvenLabel → Prop}
    (hsim : KGFNIRawSimpleOn fun _ => True) (hres : KGFieldRestrictionOn S) :
    KGFieldNotInnerInputOn S := by
  intro p lab hp hp2 hlab ht3 hS
  have hconj : LargeEvenLabelAll lab (GGRawFieldConj p) :=
    ggRawFieldConjInputExc_holds p hp hp2 lab hlab ht3
  have hinn : LargeEvenLabelAll lab (GGRawInnField p) := ggRawInnFieldInput_holds p hp hp2 lab hlab
  have hsm : LargeEvenLabelAll lab fun R _ _ _ => IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a :=
    hsim lab hlab trivial
  refine LargeEvenLabelAll.mono (fun R _ I F h => ?_)
    (largeEvenLabelAll_and (largeEvenLabelAll_and (largeEvenLabelAll_and hsm hconj) hinn)
      (hres p lab hp hp2 hlab ht3 hS))
  obtain ⟨⟨⟨⟨hs, hna⟩, hc⟩, hi⟩, hr⟩ := h
  haveI := hs
  exact kgFieldNotInnerCont_of_restriction hna hc hi hr

end CFSG.StandardType
