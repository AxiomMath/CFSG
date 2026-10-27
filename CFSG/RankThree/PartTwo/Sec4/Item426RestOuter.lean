module

public import CFSG.RankThree.PartTwo.Sec4.Item426RestSetup
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree
public import CFSG.GH74.GLS.IVK.L2.Fixed
import CFSG.RankThree.PartTwo.Sec4.Item426RestLinear
import CFSG.RankThree.PartTwo.Sec4.Item426A6FieldSU
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.RankThree.PartTwo.Sec13.Item134Residual

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open CFSG.RankThree.PartTwo.Sec4.Item426 (fixSub mem_fixSub map_fixSub_eq quotThetaEquiv
  mulAut_eq_of_forall_inv_mul_mem_center eq_top_of_isPerfect_of_isSubnormal)
open Matrix

namespace ConfigRest

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem exists_scalar_of_forall_commute (h : ConfigRest X α P) {K : Type*} [Field K]
    (h3 : (3 : K) ≠ 0) (M : X →* GL (Fin 3) K) (hM : Function.Injective M)
    {A : Matrix (Fin 3) (Fin 3) K}
    (hA : ∀ x ∈ P, A * (M x : Matrix (Fin 3) (Fin 3) K) = (M x : Matrix (Fin 3) (Fin 3) K) * A) :
    ∃ μ : K, A = Matrix.scalar (Fin 3) μ := by
  have : Group.IsPerfect P := h.isPerfect
  obtain ⟨z, hzP, hzZ, hz1, hz3⟩ := h.central
  set N : X →* Matrix (Fin 3) (Fin 3) K := (Units.coeHom (Matrix (Fin 3) (Fin 3) K)).comp M
    with hN
  have hNinj : Function.Injective N := fun x x' hxx' => hM (Units.ext hxx')
  let ρ : P →* Matrix (Fin 3) (Fin 3) K := N.comp P.subtype
  have hρ : ∀ g : P, ρ g = N g := fun _ => rfl
  exact exists_scalar_of_perfect h3 ρ (z := ⟨z, hzP⟩)
    (fun g => by
      rw [hρ, hρ, ← map_mul, ← map_mul]
      exact congrArg N (Subgroup.mem_center_iff.mp hzZ (g : X)).symm)
    (by rw [hρ, ← map_pow]; exact congrArg N hz3 |>.trans (map_one N))
    (fun h1 => hz1 (hNinj (by rw [← hρ ⟨z, hzP⟩]; exact h1.trans (map_one N).symm)))
    (y := A) (fun g => hA g g.2)

theorem ne_bot_of_mulEquiv (h : ConfigRest X α P) {Y : Type*} [Group Y] {Q : Subgroup Y}
    (e : P ≃* Q) : Q ≠ ⊥ := by
  intro hQ
  apply h.ne_bot
  have h1 : Nat.card Q = 1 := by rw [hQ]; exact Subgroup.card_bot
  rw [← Nat.card_congr e.toEquiv] at h1
  exact Subgroup.eq_bot_of_card_eq P h1

theorem nonempty_quotTheta_equiv_of_mem (h : ConfigRest X α P) {S : Type} [Group S] [Finite S]
    (hSq : IsQuasisimple S) (hSθ : aschbacherSolvableCore 3 S = ⊥) {Q : Subgroup S}
    (hQ : Q ∈ thetaComponents 3 S) (eP : P ≃* Q) :
    Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* S) := by
  have hQtop : Q = ⊤ := eq_top_of_isPerfect_of_isSubnormal hSq hQ.1 hQ.2.1 (h.ne_bot_of_mulEquiv eP)
  exact ⟨(quotThetaEquiv (eP.trans ((MulEquiv.subgroupCongr hQtop).trans Subgroup.topEquiv))).trans
    ((QuotientGroup.quotientMulEquivOfEq hSθ).trans QuotientGroup.quotientBot)⟩

theorem outer_SL (h : ConfigRest X α P) (hout : ¬ IsInnerAut α) {K : Type} [Field K] [Finite K]
    (h3 : (3 : K) ≠ 0) (e : X ≃* SpecialLinearGroup (Fin 3) K) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃*
        SpecialLinearGroup (Fin 3) (CFSG.GH74.GLS.IVK.fixedField σ)) := by
  set α' := MulAut.congr e α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, h.pow_three, map_one]
  have hout' : ¬ IsInnerAut α' := fun h' => hout ((isInnerAut_congr e α).mp h')
  set τ := descendAut 3 K α' with hτ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, hα'3, map_one]
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) := by
    have := h.quasisimple.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hfix : ∀ x ∈ P, α' (e x) = e x := fun x hx => by
    rw [hα']
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, h.fixed hx]
  by_cases hD : τ ∈ linearAutGroup 3 K
  ·
    exfalso
    obtain ⟨A, hA⟩ : ∃ A, conjAut 3 K A = τ := by
      have hcl : linearAutGroup 3 K = (conjAut 3 K).range := by
        rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
      rw [hcl] at hD
      exact hD
    set σ := slConjugation 3 K A with hσ
    have hασ : σ = α' := by
      apply mulAut_eq_of_forall_inv_mul_mem_center hperf
      intro g
      rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv,
        inv_mul_eq_one]
      have h1 : descendAut 3 K σ (proj 3 K g) = proj 3 K (σ g) := descendAut_proj 3 K σ g
      have h2 : descendAut 3 K α' (proj 3 K g) = proj 3 K (α' g) := descendAut_proj 3 K α' g
      rw [← h1, ← h2]
      change conjAut 3 K A (proj 3 K g) = τ (proj 3 K g)
      rw [hA]
    let M : X →* GL (Fin 3) K := (Matrix.SpecialLinearGroup.toGL).comp e.toMonoidHom
    have hMinj : Function.Injective M :=
      Matrix.SpecialLinearGroup.toGL_injective.comp e.injective
    obtain ⟨μ, hμ⟩ := h.exists_scalar_of_forall_commute h3 M hMinj
      (A := (A : Matrix (Fin 3) (Fin 3) K)) (fun x hx => by
        have h1 : σ (e x) = e x := by rw [hασ]; exact hfix x hx
        have h2 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
          (g : Matrix (Fin 3) (Fin 3) K)) h1
        simp only [hσ, coe_slConjugation] at h2
        change (A : Matrix (Fin 3) (Fin 3) K) * ((e x : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = ((e x : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) * A
        calc (A : Matrix (Fin 3) (Fin 3) K) * ((e x : Matrix.SpecialLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) =
            (A : Matrix (Fin 3) (Fin 3) K) * ((e x : Matrix.SpecialLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                (A : Matrix (Fin 3) (Fin 3) K) := by
              rw [Matrix.mul_assoc _ ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
                ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
          _ = _ := by rw [h2])
    apply hout'
    rw [← hασ]
    have hσ1 : σ = 1 := by
      ext g : 1
      apply Subtype.ext
      rw [hσ, coe_slConjugation, MulAut.one_apply]
      have hcomm : (A : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
          (g : Matrix (Fin 3) (Fin 3) K) * A := by
        rw [hμ]
        exact Matrix.scalar_commute μ (fun _ => Commute.all _ _) _
      rw [hcomm, Matrix.mul_assoc]
      have hAinv' : (A : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hAinv', Matrix.mul_one]
    rw [hσ1]
    exact ⟨1, map_one _⟩
  ·
    obtain ⟨σ, hσo, H, hτH⟩ := linear_order_three_field_descent le_rfl τ hτ3 hD
    have hlift : α' = slConjugation 3 K H * slFieldAut (Fin 3) K σ * (slConjugation 3 K H)⁻¹ :=
      eq_of_descendAut_eq (by rw [← hτ, hτH, map_mul, map_mul, map_inv]; rfl)
    set K₀ := CFSG.GH74.GLS.IVK.fixedField σ with hK₀
    set ι : SpecialLinearGroup (Fin 3) K₀ →* SpecialLinearGroup (Fin 3) K :=
      ((slConjugation 3 K H : SpecialLinearGroup (Fin 3) K ≃*
        SpecialLinearGroup (Fin 3) K).toMonoidHom.comp (SpecialLinearGroup.map K₀.subtype))
      with hι
    have hιinj : Function.Injective ι :=
      (slConjugation 3 K H).injective.comp (sl_map_subtype_injective σ)
    have hrange : ι.range = fixSub α' := by
      ext z
      rw [mem_fixSub, hlift]
      exact mem_range_conj_comp_iff _ _ _ (mem_range_sl_map_subtype_iff σ) z
    let e₀ : SpecialLinearGroup (Fin 3) K₀ ≃* fixSub α' :=
      (MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hrange)
    have hP' : P.map e.toMonoidHom ∈ thetaComponentsIn (fixSub α') := by
      have hmem := map_mem_thetaComponentsIn e h.mem
      rwa [map_fixSub_eq] at hmem
    obtain ⟨Q, hQ, hQeq⟩ := hP'
    have hQ₂ := map_mulEquiv_mem_thetaComponents Nat.prime_three e₀.symm hQ
    set Q₂ := Q.map e₀.symm.toMonoidHom with hQ₂def
    let eP : P ≃* Q₂ :=
      ((P.equivMapOfInjective e.toMonoidHom e.injective).trans
        ((MulEquiv.subgroupCongr hQeq.symm).trans
          (Q.equivMapOfInjective (fixSub α').subtype (fixSub α').subtype_injective).symm)).trans
        (Q.equivMapOfInjective e₀.symm.toMonoidHom e₀.symm.injective)
    obtain ⟨hQq, hQθ⟩ := Item426.isQuasisimple_SL_three K₀
    exact ⟨σ, hσo, h.nonempty_quotTheta_equiv_of_mem hQq hQθ hQ₂ eP⟩

theorem three_dvd_of_orderOf {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    {σ : K ≃+* K} (hσo : orderOf σ = 3) : 3 ∣ f := by
  have : Finite K := hK.finite
  have hc := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσo, hK.card] at hc
  have hdvd : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ∣ p ^ (2 * f) :=
    ⟨Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ^ 2, by rw [← hc]; ring⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hK.prime).mp hdvd
  rw [hi, ← pow_mul] at hc
  have h3i := Nat.pow_right_injective hK.prime.two_le hc
  omega

theorem outer_SU (h : ConfigRest X α P) (hout : ¬ IsInnerAut α) {p f : ℕ} {K : Type} [Field K]
    (hK : UnitaryFieldData p f K) (hq : 2 < p ^ f) (hp3 : p ≠ 3) (e : X ≃* unitarySU p f K 3) :
    3 ∣ f ∧ 2 < p ^ (f / 3) ∧ ∃ (K₀ : Type) (_ : Field K₀), UnitaryFieldData p (f / 3) K₀ ∧
      Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* unitarySU p (f / 3) K₀ 3) := by
  have : Fact p.Prime := ⟨hK.prime⟩
  have : Finite K := hK.finite
  have : CharP K p := hK.charP
  have h3 : (3 : K) ≠ 0 := Item426.Config426.three_ne_zero_of_charP hK.prime hp3
  set α' := MulAut.congr e α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, h.pow_three, map_one]
  have hout' : ¬ IsInnerAut α' := fun h' => hout ((isInnerAut_congr e α).mp h')
  set τ := MulAut.congr (suCenterEquiv hK hq) (centerDescend _ α') with hτ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, ← map_pow, hα'3, map_one, map_one]
  have hperf : Group.IsPerfect (unitarySU p f K 3) := by
    have := h.quasisimple.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hfix : ∀ x ∈ P, α' (e x) = e x := fun x hx => by
    rw [hα']
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, h.fixed hx]
  by_cases hD : τ ∈ (psuConj hK).range
  ·
    exfalso
    obtain ⟨A, hA⟩ := hD
    set σ := suConj hK A with hσ
    have hασ : σ = α' := by
      apply mulAut_eq_of_forall_inv_mul_mem_center hperf
      intro g
      rw [center_unitarySU_three (h := hK) hq]
      have h1 : psuConj hK A (g : unitaryPSU hK 3) =
          ((σ g : unitarySU p f K 3) : unitaryPSU hK 3) := psuConj_mk A g
      have h2 : τ (g : unitaryPSU hK 3) = ((α' g : unitarySU p f K 3) : unitaryPSU hK 3) := rfl
      have h3' : ((σ g : unitarySU p f K 3) : unitaryPSU hK 3) =
          ((α' g : unitarySU p f K 3) : unitaryPSU hK 3) := by rw [← h1, ← h2, hA]
      exact QuotientGroup.eq.mp h3'
    let M : X →* GL (Fin 3) K := (unitarySU p f K 3).subtype.comp e.toMonoidHom
    have hMinj : Function.Injective M := Subtype.val_injective.comp e.injective
    set Am : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      with hAm
    set Ai : Matrix (Fin 3) (Fin 3) K := (((A⁻¹ : unitaryIsom3 hK) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) with hAi
    have hinv : Ai * Am = 1 := by
      rw [hAi, hAm, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
        Units.val_one]
    have hinv' : Am * Ai = 1 := by
      rw [hAi, hAm, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        Units.val_one]
    have hcommOf : ∀ {Xm : Matrix (Fin 3) (Fin 3) K}, Am * Xm * Ai = Xm → Am * Xm = Xm * Am :=
      fun {Xm} hX => by
        calc Am * Xm = Am * Xm * (Ai * Am) := by rw [hinv, Matrix.mul_one]
          _ = (Am * Xm * Ai) * Am := by rw [Matrix.mul_assoc (Am * Xm)]
          _ = Xm * Am := by rw [hX]
    obtain ⟨μ, hμ⟩ := h.exists_scalar_of_forall_commute h3 M hMinj (A := Am) (fun x hx => by
        have h1 : σ (e x) = e x := by rw [hασ]; exact hfix x hx
        have h2 := congrArg (fun g : unitarySU p f K 3 => ((g : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)) h1
        simp only [hσ, coe_suConj, Units.val_mul] at h2
        exact hcommOf h2)
    apply hout'
    rw [← hασ]
    have hσ1 : σ = 1 := by
      ext g : 1
      apply Subtype.ext
      apply Units.ext
      rw [hσ, coe_suConj, MulAut.one_apply, Units.val_mul, Units.val_mul]
      have hcomm : Am * (((g : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          (((g : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Am := by
        rw [hμ]
        exact Matrix.scalar_commute μ (fun _ => Commute.all _ _) _
      change Am * (((g : unitarySU p f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Ai = _
      rw [hcomm, Matrix.mul_assoc, hinv', Matrix.mul_one]
    rw [hσ1]
    exact ⟨1, map_one _⟩
  ·
    obtain ⟨σ, hσo, H, hτH⟩ := unitary_order_three_field_descent hq τ hτ3 hD
    set γ := suConj hK H with hγ
    set σs := suField hK σ with hσs
    have hα : γ * σs * γ⁻¹ = α' := by
      apply mulAut_eq_of_forall_inv_mul_mem_center hperf
      intro g
      rw [center_unitarySU_three (h := hK) hq]
      have h1 : (((γ * σs * γ⁻¹) g : unitarySU p f K 3) : unitaryPSU hK 3) =
          (psuConj hK H * psuField hK σ * (psuConj hK H)⁻¹) (g : unitaryPSU hK 3) := by
        rw [← map_inv (psuConj hK) H, ← map_inv (suConj hK) H]
        rfl
      have h2 : ((α' g : unitarySU p f K 3) : unitaryPSU hK 3) = τ (g : unitaryPSU hK 3) := rfl
      rw [hτH] at h2
      exact QuotientGroup.eq.mp (h1.trans h2.symm)
    have h3f : 3 ∣ f := three_dvd_of_orderOf hK hσo
    have hcongr : MulAut.congr γ σs = γ * σs * γ⁻¹ := by
      ext x
      rfl
    have hfixα : fixSub α' = (fixSub σs).map γ.toMonoidHom := by
      rw [← hα, ← hcongr, map_fixSub_eq]
    have hP' : P.map e.toMonoidHom ∈ thetaComponentsIn (fixSub α') := by
      have hmem := map_mem_thetaComponentsIn e h.mem
      rwa [map_fixSub_eq] at hmem
    rw [hfixα] at hP'
    have hP₁ := map_mem_thetaComponentsIn γ.symm hP'
    have hmm : ((fixSub σs).map γ.toMonoidHom).map γ.symm.toMonoidHom = fixSub σs := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id (fixSub σs)
      ext x
      simp
    rw [hmm] at hP₁
    obtain ⟨P₁', hP₁', hP₁eq⟩ := hP₁
    obtain ⟨e₀⟩ := Item426.nonempty_fixSub_suField_equiv hK hσo
    set K₀ := Item426.fixedField σ with hK₀def
    have hP₂ := map_mulEquiv_mem_thetaComponents Nat.prime_three e₀.symm hP₁'
    set P₂ := P₁'.map e₀.symm.toMonoidHom with hP₂def
    let eP : P ≃* P₂ :=
      (((P.equivMapOfInjective e.toMonoidHom e.injective).trans
        ((P.map e.toMonoidHom).equivMapOfInjective γ.symm.toMonoidHom γ.symm.injective)).trans
        ((MulEquiv.subgroupCongr hP₁eq.symm).trans
          (P₁'.equivMapOfInjective (fixSub σs).subtype (fixSub σs).subtype_injective).symm)).trans
        (P₁'.equivMapOfInjective e₀.symm.toMonoidHom e₀.symm.injective)
    have hP₂1 : P₂ ≠ ⊥ := h.ne_bot_of_mulEquiv eP
    have h₀ : UnitaryFieldData p (f / 3) K₀ :=
      CFSG.RankThree.Classical.fixSubfield_unitaryFieldData hK Nat.prime_three (by norm_num) hσo
    have : Finite K₀ := h₀.finite
    have : CharP K₀ p := h₀.charP
    have hK₀ : Nat.card K₀ = (p ^ (f / 3)) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
    have hr2 : 2 ≤ p ^ (f / 3) := by
      have hp := hK.prime.two_le
      have hf : 1 ≤ f / 3 := h₀.one_le
      have : p ≤ p ^ (f / 3) := Nat.le_self_pow (by omega) p
      omega
    by_cases hr : p ^ (f / 3) = 2
    ·
      exfalso
      have hp2 : p = 2 := by
        have hp := hK.prime.two_le
        have hf : 1 ≤ f / 3 := h₀.one_le
        have : p ≤ p ^ (f / 3) := Nat.le_self_pow (by omega) p
        omega
      have hf1 : f / 3 = 1 := by
        subst hp2
        exact Nat.pow_right_injective le_rfl (hr.trans (pow_one 2).symm)
      have h₂ : UnitaryFieldData 2 (f / 3) K₀ := hp2 ▸ h₀
      have hcardQ : Nat.card (unitarySU 2 (f / 3) K₀ 3) = 216 :=
        CFSG.RankThree.CentralLiftU.card_statedSU_three_two h₂ hf1
      have := Fintype.ofFinite (unitarySU 2 (f / 3) K₀ 3)
      have hsolv : Group.IsSolvable (unitarySU 2 (f / 3) K₀ 3) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3)
          (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hcardQ]; norm_num)
      subst hp2
      have : Group.IsSolvable P₂ :=
        Group.isSolvable_of_isSolvable_injective (f := P₂.subtype) P₂.subtype_injective
      have : Group.IsPerfect P₂ := hP₂.1
      have : Nontrivial P₂ := (Subgroup.nontrivial_iff_ne_bot P₂).mpr hP₂1
      exact Group.IsPerfect.not_isSolvable P₂ ‹_›
    ·
      have hnq₀ : ((3 : ℕ), p ^ (f / 3)) ≠ (3, 2) := fun h' => hr (Prod.mk.inj h').2
      obtain ⟨hQq, hQZ⟩ :=
        CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK₀ le_rfl hnq₀
      have hQθ : aschbacherSolvableCore 3 (unitarySU p (f / 3) K₀ 3) = ⊥ :=
        Sec13.aschbacherSolvableCore_eq_bot_of_isQuasisimple hQq
          (Item426.isPGroup_center_unitarySU h₀ hQZ)
      exact ⟨h3f, by omega, K₀, inferInstance, h₀,
        h.nonempty_quotTheta_equiv_of_mem hQq hQθ hP₂ eP⟩

end ConfigRest

end CFSG.RankThree.PartTwo.Sec4.Item426Rest
