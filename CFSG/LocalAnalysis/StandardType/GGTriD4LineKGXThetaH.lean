module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXFix
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineModel
import CFSG.RankThree.PartOne.KGD.D4T36Core

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

private lemma sigma_algebraMap_eq {K k : Type} [Field K] [Field k] [Algebra k K] {n : ℕ}
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hk : Nat.card k = 2 ^ n) (x : k) :
    σ (algebraMap k K x) = algebraMap k K x := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Fintype k := Fintype.ofFinite k
  have hx : x ^ (2 ^ n) = x := by
    rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rw [hσ, ← map_pow, hx]

private noncomputable def fixedFieldHom {K k : Type} [Field K] [Field k] [Algebra k K]
    {n : ℕ} (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hk : Nat.card k = 2 ^ n) :
    k →+* trialityFixedField K σ.toRingHom where
  toFun x := ⟨algebraMap k K x, by
    rw [mem_trialityFixedField]
    exact sigma_algebraMap_eq σ hσ hk x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

private lemma fixedFieldUnits_injective {K k : Type} [Field K] [Field k] [Algebra k K]
    {n : ℕ} (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (hk : Nat.card k = 2 ^ n) :
    Function.Injective (Units.map (fixedFieldHom σ hσ hk).toMonoidHom :
      kˣ →* (trialityFixedField K σ.toRingHom)ˣ) := by
  intro u v huv
  exact Units.ext ((algebraMap k K).injective
    (congrArg (fun w : (trialityFixedField K σ.toRingHom)ˣ => (w : K)) huv))

private lemma card_trialityFixedField {K : Type} [Field K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hn : 1 ≤ n) : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n :=
  card_fixSubfield_cube Nat.prime_two hn hK σ hσ

private lemma trialityFixedUnit_injective {K : Type} [Field K] (σ : K ≃+* K) :
    Function.Injective (trialityFixedUnit K σ) := by
  intro u v h
  exact Units.ext (Subtype.ext (congrArg (fun w : Kˣ => (w : K)) h))

private noncomputable def diagGL {k : Type} [Field k] (v : Fin 3 → kˣ) : GL (Fin 3) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => (v i : k))
    (by
      rw [Matrix.det_diagonal, ← Units.coe_prod]
      exact Units.ne_zero _)

private lemma diagGL_val {k : Type} [Field k] (v : Fin 3 → kˣ) :
    ((diagGL v : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal (fun i => (v i : k)) :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma diagGL_mul {k : Type} [Field k] (v w : Fin 3 → kˣ) :
    diagGL (v * w) = diagGL v * diagGL w := by
  refine Units.ext ?_
  rw [Units.val_mul, diagGL_val, diagGL_val, diagGL_val, Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext fun i => rfl)

private lemma vec3_zero {k : Type} (x y z : k) : (![x, y, z] : Fin 3 → k) 0 = x := rfl
private lemma vec3_one {k : Type} (x y z : k) : (![x, y, z] : Fin 3 → k) 1 = y := rfl
private lemma vec3_two {k : Type} (x y z : k) : (![x, y, z] : Fin 3 → k) 2 = z := rfl

private noncomputable def thetaDiag {K k : Type} [Field K] [Field k] [Algebra k K]
    (a : Kˣ) (c : kˣ) : GL (Fin 3) k :=
  diagGL ![(c ^ 2 : kˣ), Units.map (Algebra.norm k (S := K)) a, c]

private lemma thetaDiag_val {K k : Type} [Field K] [Field k] [Algebra k K]
    (a : Kˣ) (c : kˣ) :
    ((thetaDiag a c : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal ![(c : k) ^ 2, Algebra.norm k (a : K), (c : k)] := by
  rw [thetaDiag, diagGL_val]
  congr 1
  funext i
  fin_cases i <;> simp

private lemma thetaDiag_det {K k : Type} [Field K] [Field k] [Algebra k K]
    (hdeg : Module.finrank k K = 3) (a : Kˣ) (c : kˣ) :
    Matrix.GeneralLinearGroup.det (thetaDiag a c) =
      Units.map (Algebra.norm k (S := K))
        (Units.map (algebraMap k K).toMonoidHom c * a) := by
  refine Units.ext ?_
  change (thetaDiag a c : Matrix (Fin 3) (Fin 3) k).det =
    Algebra.norm k (algebraMap k K (c : k) * (a : K))
  rw [thetaDiag_val, Matrix.det_diagonal, Fin.prod_univ_three, vec3_zero, vec3_one, vec3_two]
  rw [map_mul, Algebra.norm_algebraMap, hdeg]
  ring

private lemma triD4LineMk_congr {K k : Type} [Field K] [Field k] [Algebra k K]
    {g g' : GL (Fin 3) k} {c c' : Kˣ} (hg : g = g') (hc : c = c')
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    triD4LineMk k K g c h = triD4LineMk k K g' c' h' := by
  cases hg
  cases hc
  unfold triD4LineMk
  exact congrArg QuotientGroup.mk (Subtype.ext rfl)

private noncomputable def thetaH0 {K k : Type} [Field K] [Field k] [Algebra k K]
    (hdeg : Module.finrank k K = 3) : Kˣ × kˣ →* TriD4LineX k K where
  toFun p := triD4LineMk k K (thetaDiag p.1 p.2)
    (Units.map (algebraMap k K).toMonoidHom p.2 * p.1) (thetaDiag_det hdeg p.1 p.2)
  map_one' := by
    refine (triD4LineMk_eq_one_iff k K (thetaDiag 1 1) _ _).2 ⟨1, ?_, ?_⟩
    · have h : thetaDiag (1 : Kˣ) (1 : kˣ) = 1 := by
        refine Matrix.GeneralLinearGroup.ext fun i j => ?_
        rw [thetaDiag_val, Matrix.GeneralLinearGroup.coe_one]
        fin_cases i <;> fin_cases j <;> simp
      rw [h, map_one]
    · simp
  map_mul' p q := by
    have h'' : Matrix.GeneralLinearGroup.det (thetaDiag p.1 p.2 * thetaDiag q.1 q.2) =
        Units.map (Algebra.norm k (S := K))
          ((Units.map (algebraMap k K).toMonoidHom p.2 * p.1) *
            (Units.map (algebraMap k K).toMonoidHom q.2 * q.1)) := by
      rw [map_mul, map_mul, thetaDiag_det hdeg p.1 p.2, thetaDiag_det hdeg q.1 q.2]
    rw [triD4LineMk_mul k K _ _ _ _ _ _ h'']
    refine triD4LineMk_congr ?_ ?_ _ _
    · rw [thetaDiag, thetaDiag, thetaDiag, ← diagGL_mul]
      congr 1
      funext i
      fin_cases i <;> simp [Pi.mul_apply, map_mul, mul_pow]
    · change Units.map (algebraMap k K).toMonoidHom (p.2 * q.2) * (p.1 * q.1) =
        (Units.map (algebraMap k K).toMonoidHom p.2 * p.1) *
          (Units.map (algebraMap k K).toMonoidHom q.2 * q.1)
      rw [map_mul]
      ac_rfl

private lemma thetaH0_injective {K k : Type} [Field K] [Field k] [Algebra k K]
    (hdeg : Module.finrank k K = 3) : Function.Injective (thetaH0 (k := k) (K := K) hdeg) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, c⟩ hp
  obtain ⟨μ, hg, hc⟩ :=
    (triD4LineMk_eq_one_iff k K (thetaDiag a c)
      (Units.map (algebraMap k K).toMonoidHom c * a) (thetaDiag_det hdeg a c)).1 hp
  have h0 := congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k) 0 0) hg
  have h2 := congrArg (fun A : GL (Fin 3) k => (A : Matrix (Fin 3) (Fin 3) k) 2 2) hg
  rw [thetaDiag_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, vec3_zero] at h0
  rw [thetaDiag_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, vec3_two] at h2
  have hcμ : c = μ := Units.ext h2
  have hc1 : c = 1 := by
    have hsq : (c : k) ^ 2 = (c : k) := by rw [← hcμ] at h0; exact h0
    have hsub : (c : k) * ((c : k) - 1) = 0 := by
      rw [mul_sub, mul_one, sub_eq_zero, ← sq]
      exact hsq
    rcases mul_eq_zero.1 hsub with h | h
    · exact absurd h (Units.ne_zero c)
    · exact Units.ext (sub_eq_zero.1 h)
  have hμ1 : μ = 1 := by rw [← hcμ, hc1]
  have ha1 : a = 1 := by
    rw [hc1, hμ1] at hc
    simpa using hc
  exact Prod.ext ha1 hc1

theorem triD4Line_exists_thetaH
    {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n) :
    ∃ θ : ↥(triD4LineH1 K σ) →* TriD4LineX k K, Function.Injective θ ∧
      ∀ (y : ↥(triD4LineH1 K σ)) (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) (c : kˣ),
        ((y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
            trialityTorusHom σ (a, b) →
        trialityFixedUnit K σ b = Units.map (algebraMap k K).toMonoidHom c →
        ∀ g : GL (Fin 3) k,
          (g : Matrix (Fin 3) (Fin 3) k) =
            Matrix.diagonal ![(c : k) ^ 2, Algebra.norm k (a : K), (c : k)] →
        ∀ hdet : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K))
            (Units.map (algebraMap k K).toMonoidHom c * a),
          θ y = triD4LineMk k K g (Units.map (algebraMap k K).toMonoidHom c * a) hdet := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · exfalso
      have h1 : Nat.card K = 1 := by rw [hK, hn0]; norm_num
      haveI : Fintype K := Fintype.ofFinite K
      have h2 : 1 < Fintype.card K := Fintype.one_lt_card
      rw [← Nat.card_eq_fintype_card, h1] at h2
      exact lt_irrefl 1 h2
    · exact hpos
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n * 3)
      (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_three_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hdeg : Module.finrank k K = 3 := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fintype k := Fintype.ofFinite k
    have hcard := Module.card_eq_pow_finrank (K := k) (V := K)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hK] at hcard
    have h2n : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact (Nat.pow_right_injective h2n hcard).symm
  obtain ⟨-, ⟨e, he⟩, -⟩ := even_triality_faithful_torus_coordinates (K := K) σ hσ3
  let ψ : kˣ →* (trialityFixedField K σ.toRingHom)ˣ :=
    Units.map (fixedFieldHom σ hσ hk).toMonoidHom
  have hψinj : Function.Injective ψ := fixedFieldUnits_injective σ hσ hk
  have hcardF : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n :=
    card_trialityFixedField hK σ hσ hn
  haveI : Finite (trialityFixedField K σ.toRingHom) :=
    Nat.finite_of_card_ne_zero (by rw [hcardF]; positivity)
  have hcard : Nat.card (trialityFixedField K σ.toRingHom)ˣ = Nat.card kˣ := by
    rw [Nat.card_units, Nat.card_units, hcardF, hk]
  have hψbij : Function.Bijective ψ := hψinj.bijective_of_nat_card_le (le_of_eq hcard)
  let iso : (trialityFixedField K σ.toRingHom)ˣ ≃* kˣ :=
    (MulEquiv.ofBijective ψ hψbij).symm
  let cH := Subgroup.subgroupOfEquivOfLe (graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom)
  let coords := (cH.trans e.symm).trans (MulEquiv.prodCongr (MulEquiv.refl Kˣ) iso)
  let Θ₀ : Kˣ × kˣ →* TriD4LineX k K := thetaH0 (k := k) (K := K) hdeg
  let θ : ↥(triD4LineH1 K σ) →* TriD4LineX k K := Θ₀.comp coords.toMonoidHom
  refine ⟨θ, ?_, ?_⟩
  · intro x y h
    exact coords.injective (thetaH0_injective hdeg h)
  · intro y a b c hy hb g hg hdet
    have hcy : (cH y : ModGL TwistTag.D4.tag K) = trialityTorusHom σ (a, b) :=
      (Subgroup.subgroupOfEquivOfLe_apply_coe
        (graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom) y).trans hy
    have h1 : e.symm (cH y) = (a, b) := by
      rw [MulEquiv.symm_apply_eq]
      refine Subtype.ext ?_
      rw [he, ← trialityTorusHom_apply]
      exact hcy
    have hψc : ψ c = b := by
      apply trialityFixedUnit_injective σ
      rw [hb]
      exact Units.ext rfl
    have h2 : iso b = c := by
      change (MulEquiv.ofBijective ψ hψbij).symm b = c
      rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply]
      exact hψc.symm
    have hcoord : coords y = (a, c) := by
      change MulEquiv.prodCongr (MulEquiv.refl Kˣ) iso (e.symm (cH y)) = (a, c)
      rw [h1]
      exact Prod.ext rfl h2
    rw [show θ y = Θ₀ (coords y) from rfl, hcoord]
    have hgt : g = thetaDiag a c := by
      refine Units.ext ?_
      rw [hg, thetaDiag_val]
    exact triD4LineMk_congr hgt.symm rfl (thetaDiag_det hdeg a c) hdet

end CFSG.StandardType
