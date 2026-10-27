module

public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutPSUOrderThree
import CFSG.RankThree.PartTwo.Sec4.Item426A6Linear
public import CFSG.RankThree.PartTwo.KFacts.K426A6
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

theorem mulAut_eq_of_forall_inv_mul_mem_center {S : Type*} [Group S] (hS : Group.IsPerfect S)
    {σ₁ σ₂ : MulAut S} (h : ∀ g, (σ₁ g)⁻¹ * σ₂ g ∈ Subgroup.center S) : σ₁ = σ₂ := by
  let χ : S →* Subgroup.center S :=
    { toFun := fun g => ⟨(σ₁ g)⁻¹ * σ₂ g, h g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g g' => by
        apply Subtype.ext
        simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
        have hc := Subgroup.mem_center_iff.mp (h g) (σ₁ g')⁻¹
        calc (σ₁ g')⁻¹ * (σ₁ g)⁻¹ * (σ₂ g * σ₂ g') =
            ((σ₁ g')⁻¹ * ((σ₁ g)⁻¹ * σ₂ g)) * σ₂ g' := by group
          _ = (((σ₁ g)⁻¹ * σ₂ g) * (σ₁ g')⁻¹) * σ₂ g' := by rw [hc]
          _ = (σ₁ g)⁻¹ * σ₂ g * ((σ₁ g')⁻¹ * σ₂ g') := by group }
  have hker : commutator S ≤ χ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp (χ y).2 _
  ext g
  have hg : χ g = 1 := (hker (hS.commutator_eq_top ▸ Subgroup.mem_top g) : g ∈ χ.ker)
  have hg' : (σ₁ g)⁻¹ * σ₂ g = 1 := congrArg Subtype.val hg
  exact (inv_mul_eq_one.mp hg')

theorem map_fixSub_eq {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (α : MulAut X) :
    (fixSub α).map e.toMonoidHom = fixSub (MulAut.congr e α) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    rw [mem_fixSub]
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx']
  · intro hy
    rw [mem_fixSub] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    have h1 : e (α (e.symm y)) = y := hy
    change α (e.symm y) = e.symm y
    apply e.injective
    rw [h1, MulEquiv.apply_symm_apply]

namespace Config426

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem false_of_center_eq_bot (h : Config426 X α P) (hZ : Subgroup.center X = ⊥) : False := by
  obtain ⟨a, -, b, -, hcZ, hc1, -⟩ := h.comm
  rw [hZ, Subgroup.mem_bot] at hcZ
  exact hc1 hcZ

theorem exists_scalar_of_forall_commute (h : Config426 X α P) {K : Type*} [Field K]
    (h3 : (3 : K) ≠ 0) (M : X →* GL (Fin 3) K) (hM : Function.Injective M)
    {A : Matrix (Fin 3) (Fin 3) K}
    (hA : ∀ x ∈ P, A * (M x : Matrix (Fin 3) (Fin 3) K) = (M x : Matrix (Fin 3) (Fin 3) K) * A) :
    ∃ μ : K, A = Matrix.scalar (Fin 3) μ := by
  obtain ⟨a, ha, b, hb, hcZ, hc1, hc3⟩ := h.comm
  set c := a * b * a⁻¹ * b⁻¹ with hc
  set N : X →* Matrix (Fin 3) (Fin 3) K := (Units.coeHom (Matrix (Fin 3) (Fin 3) K)).comp M
    with hN
  have hNinj : Function.Injective N := fun x x' hxx' => hM (Units.ext hxx')
  have hunit : ∀ x : X, IsUnit (N x).det := fun x => by
    have := (Matrix.GeneralLinearGroup.det (M x)).isUnit
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
  have hcomm : ∀ {u v : X}, u * v = v * u → N u * N v = N v * N u := fun huv => by
    rw [← map_mul, ← map_mul, huv]
  have habc : a * b = c * (b * a) := by rw [hc]; group
  have hca : c * a = a * c := (Subgroup.mem_center_iff.mp hcZ a).symm
  have hcb : c * b = b * c := (Subgroup.mem_center_iff.mp hcZ b).symm
  exact exists_scalar_of_commute h3 (hunit a) (hunit b)
    (by rw [← map_mul, ← map_mul, ← map_mul, habc]) (hcomm hca) (hcomm hcb)
    (by rw [← map_pow, hc3, map_one]) (fun h1 => hc1 (hNinj (by rw [h1, map_one])))
    (hA a ha) (hA b hb)

theorem map_facts (h : Config426 X α P) {Y : Type} [Group Y] (e : X ≃* Y) :
    P.map e.toMonoidHom ∈ thetaComponentsIn
        (MonoidHom.eqLocus (MulAut.congr e α).toMonoidHom (MonoidHom.id Y)) ∧
      IsTripleCover (P.map e.toMonoidHom ⧸ aschbacherSolvableCore 3 (P.map e.toMonoidHom))
        (alternatingGroup (Fin 6)) := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  refine ⟨?_, isTripleCover_of_mulEquiv
    (quotThetaEquiv (P.equivMapOfInjective e.toMonoidHom e.injective)) h.tripleCover⟩
  have hmem := map_mem_thetaComponentsIn e h.mem
  rwa [map_fixSub_eq] at hmem

theorem false_of_outer_SL (hSLF : K426.SLThreeFieldComponent) (h : Config426 X α P)
    (hout : ¬ IsInnerAut α) {K : Type} [Field K] [Finite K] (h3 : (3 : K) ≠ 0)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) : False := by
  set α' := MulAut.congr e α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, h.pow_three, map_one]
  have hout' : ¬ IsInnerAut α' := fun h' => hout ((isInnerAut_congr e α).mp h')
  set τ := descendAut 3 K α' with hτ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, hα'3, map_one]
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) := by
    have := h.quasisimple.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hfix : ∀ x ∈ P, α' (e x) = e x := fun x hx => by
    rw [hα']
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, h.fixed hx]
  by_cases hD : τ ∈ linearAutGroup 3 K
  ·
    obtain ⟨A, hA⟩ : ∃ A, conjAut 3 K A = τ := by
      have hcl : linearAutGroup 3 K = (conjAut 3 K).range := by
        rw [linearAutGroup, ← MonoidHom.coe_range, Subgroup.closure_eq]
      rw [hcl] at hD
      exact hD
    set σ := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
      with hσ
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
      have hAinv : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
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
    have hF := isField_of_pow_three_eq_one (n := 3) le_rfl hτ3 hD
    obtain ⟨hmem, htc⟩ := h.map_facts e
    exact hSLF K h3 α' hα'3 hF _ hmem htc

theorem three_ne_zero_of_charP {K : Type*} [Field K] {p : ℕ} [CharP K p] (hp : p.Prime)
    (hp3 : p ≠ 3) : (3 : K) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : K) = 0 := by rw [Nat.cast_ofNat]; exact h
  rw [CharP.cast_eq_zero_iff K p] at h'
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')

theorem false_of_outer_SU (hSUF : K426.SUThreeFieldComponent) (h : Config426 X α P)
    (hout : ¬ IsInnerAut α) {p f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) (hp3 : p ≠ 3) (e : X ≃* unitarySU p f K 3) : False := by
  have : Finite K := hK.finite
  have : CharP K p := hK.charP
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_charP hK.prime hp3
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
    have hF := isField_psu3_of_pow_three_eq_one hq hτ3 hD
    obtain ⟨hmem, htc⟩ := h.map_facts e
    exact hSUF p f K hK hq hp3 α' hα'3 hF _ hmem htc

end Config426

end CFSG.RankThree.PartTwo.Sec4.Item426
