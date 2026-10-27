module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaQ
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaH
import CFSG.GroupTheory.InternalSemidirectEquiv
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaAgree
import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaConj
import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaEquiv
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

private noncomputable def thetaDiag {K k : Type} [Field K] [Field k] [Algebra k K]
    [Module.Finite k K] (a : Kˣ) (c : kˣ) : GL (Fin 3) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![(c : k) ^ 2, Algebra.norm k (a : K), (c : k)])
    (by
      rw [Matrix.det_diagonal]
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro i _
      fin_cases i
      · exact pow_ne_zero 2 (Units.ne_zero c)
      · exact (Algebra.norm_ne_zero_iff).2 (Units.ne_zero a)
      · exact Units.ne_zero c)

private lemma thetaDiag_val {K k : Type} [Field K] [Field k] [Algebra k K]
    [Module.Finite k K] (a : Kˣ) (c : kˣ) :
    ((thetaDiag a c : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      Matrix.diagonal ![(c : k) ^ 2, Algebra.norm k (a : K), (c : k)] :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private lemma thetaDiag_det {K k : Type} [Field K] [Field k] [Algebra k K]
    [Module.Finite k K] (hdeg : Module.finrank k K = 3) (a : Kˣ) (c : kˣ) :
    Matrix.GeneralLinearGroup.det (thetaDiag a c) =
      Units.map (Algebra.norm k (S := K))
        (Units.map (algebraMap k K).toMonoidHom c * a) := by
  refine Units.ext ?_
  change (thetaDiag a c : Matrix (Fin 3) (Fin 3) k).det =
    Algebra.norm k (algebraMap k K (c : k) * (a : K))
  rw [thetaDiag_val, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [map_mul, Algebra.norm_algebraMap, hdeg]
  ring

private noncomputable def thetaTuple {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    Fin Tag.D4.rank → Kˣ :=
  ![a ^ 2 * B⁻¹, (Units.map σ.toMonoidHom a) ^ 2 * B⁻¹,
    (a * Units.map σ.toMonoidHom a * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a))⁻¹
      * B ^ 2, (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a)) ^ 2 * B⁻¹]

private lemma thetaTuple_apply_zero {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    thetaTuple σ a B 0 = a ^ 2 * B⁻¹ := rfl

private lemma thetaTuple_apply_one {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    thetaTuple σ a B 1 = (Units.map σ.toMonoidHom a) ^ 2 * B⁻¹ := rfl

private lemma thetaTuple_apply_two {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    thetaTuple σ a B 2 =
      (a * Units.map σ.toMonoidHom a * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a))⁻¹
        * B ^ 2 := rfl

private lemma thetaTuple_apply_three {K : Type} [Field K] (σ : K →+* K) (a B : Kˣ) :
    thetaTuple σ a B 3 = (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom a)) ^ 2 * B⁻¹ := rfl

private lemma exists_algebraMap_fixedUnit {K k : Type} [Field K] [Field k] [Algebra k K]
    [Finite K] (hdeg : Module.finrank k K = 3) (τ : K ≃ₐ[k] K)
    (hτorder : orderOf τ = 3) (σ : K ≃+* K) (hτ : ∀ c, τ c = σ c)
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    ∃ c : kˣ, trialityFixedUnit K σ b = Units.map (algebraMap k K).toMonoidHom c := by
  have hb : τ (b : K) = (b : K) := by
    rw [hτ]
    exact (mem_trialityFixedField).1 (b : trialityFixedField K σ.toRingHom).2
  obtain ⟨a, ha⟩ := triD4Line_exists_algebraMap_of_sigma_eq k K hdeg τ hτorder (b : K) hb
  have ha0 : a ≠ 0 := by
    intro h
    refine b.ne_zero (Subtype.ext ?_)
    change ((b : trialityFixedField K σ.toRingHom) : K) = (0 : K)
    rw [← ha, h, map_zero]
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  change ((b : trialityFixedField K σ.toRingHom) : K) = algebraMap k K a
  exact ha.symm

private lemma theta_sigma_algebraMap {K k : Type} [Field K] [Field k] [Algebra k K]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (x : k) :
    σ (algebraMap k K x) = algebraMap k K x := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Fintype k := Fintype.ofFinite k
  rw [hσ, ← map_pow,
    show x ^ 2 ^ n = x by rw [← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]]

private lemma theta_card_fixSubfield {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n := by
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 3 * n) hK3
  have hσfr : σ = fr ^ n := RingEquiv.ext fun c => by
    rw [hσ, CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hfr n c]
  have hσo : orderOf σ = 3 := by
    rw [hσfr, orderOf_pow_of_dvd (by omega) (by rw [hord]; exact Dvd.intro_left 3 rfl), hord,
      Nat.mul_div_cancel _ (by omega)]
  obtain ⟨-, hσcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by omega : 1 ≤ 3 * n) hK3 σ
  rw [hσo, Nat.mul_div_cancel_left _ (by norm_num)] at hσcard
  exact hσcard

theorem triD4Line_exists_theta
    {n : ℕ} (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (k : Type) [Field k] [Algebra k K]
    (hk : Nat.card k = 2 ^ n) (τ : K ≃ₐ[k] K) (hτ : ∀ c, τ c = σ c) (ω : Kˣ) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hz : trialityOuterTorus K σ ω ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ∃ Θ : Subgroup.centralizer {triD4LineZ0 K σ ω hz} ≃* TriD4LineX k K,
      ∀ (y : Subgroup.centralizer {triD4LineZ0 K σ ω hz})
        (hy : fieldActor (t := TwistTag.D4) σ σ y ∈ Subgroup.centralizer {triD4LineZ0 K σ ω hz}),
        Θ ⟨fieldActor (t := TwistTag.D4) σ σ y, hy⟩ = triD4LineSigma k K τ (Θ y) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · have h1 : Nat.card K = 1 := by rw [hK, h]; norm_num
      rw [Nat.card_eq_fintype_card] at h1
      have h2 := Fintype.one_lt_card (α := K)
      omega
    · exact h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_three_apply]
    have hcard : ∀ x : K, x ^ Nat.card K = x := fun x => by
      rw [Nat.card_eq_fintype_card]; exact FiniteField.pow_card x
    rw [hσ, hσ, hσ]
    calc ((c ^ 2 ^ n) ^ 2 ^ n) ^ 2 ^ n = c ^ ((2 ^ n) * (2 ^ n) * (2 ^ n)) := by
          rw [pow_mul, pow_mul]
      _ = c ^ Nat.card K := by congr 1; rw [hK]; ring
      _ = c := hcard c
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Fintype k := Fintype.ofFinite k
  have hdeg : Module.finrank k K = 3 := by
    have hcard := Module.card_eq_pow_finrank (K := k) (V := K)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hk, hK] at hcard
    have h2n : 2 ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
    exact (Nat.pow_right_injective h2n hcard).symm
  haveI : Module.Finite k K := Module.Finite.of_finite
  have hτ3 : τ ^ 3 = 1 := by
    refine AlgEquiv.ext fun c => ?_
    change τ (τ (τ c)) = c
    rw [hτ, hτ, hτ]
    have := congrArg (fun e : K ≃+* K => e c) hσ3
    simpa [ringEquiv_pow_three_apply] using this
  have hτne1 : τ ≠ 1 := by
    intro h1
    have hσ1 : σ = 1 := RingEquiv.ext fun c => by
      have := congrArg (fun e : K ≃ₐ[k] K => e c) h1
      simpa [hτ c] using this
    have hcardF : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ n :=
      theta_card_fixSubfield hn hK σ hσ
    have htop : trialityFixedField K σ.toRingHom = ⊤ := by
      ext x; simp [trialityFixedField, hσ1]
    have hcard : Nat.card (trialityFixedField K σ.toRingHom) = Nat.card K := by
      rw [htop]; exact Nat.card_congr (Subfield.topEquiv (K := K)).toEquiv
    have hEq : (2 ^ n) = (2 ^ n) ^ 3 := (hcardF.symm.trans hcard).trans hK
    have h2n : 2 ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
    have h13 : (1 : ℕ) = 3 := Nat.pow_right_injective h2n (by simpa using hEq)
    omega
  have hτorder : orderOf τ = 3 := orderOf_eq_prime hτ3 hτne1
  let L := AlgebraicClosure K
  obtain ⟨θQ0, hθQ0⟩ := triD4Line_exists_thetaQ (n := n) K hK σ hσ k hk L
  obtain ⟨θH, hθHinj, hθHspec⟩ := triD4Line_exists_thetaH (n := n) K hK σ hσ k hk
  have hCeq : Subgroup.centralizer {triD4LineZ0 K σ ω hz} =
      triD4LineH1 K σ ⊔ triD4LineNR K σ L :=
    triD4Line_centralizer_z0_eq (n := n) K hK σ hσ ω hω3 hω1 hz L
  let C := Subgroup.centralizer {triD4LineZ0 K σ ω hz}
  have hH1leC : triD4LineH1 K σ ≤ C := by
    change triD4LineH1 K σ ≤ Subgroup.centralizer {triD4LineZ0 K σ ω hz}
    rw [hCeq]
    exact le_sup_left
  have hNRleC : triD4LineNR K σ L ≤ C := by
    change triD4LineNR K σ L ≤ Subgroup.centralizer {triD4LineZ0 K σ ω hz}
    rw [hCeq]
    exact le_sup_right
  let Q := (triD4LineNR K σ L).subgroupOf C
  let N := (triD4LineH1 K σ).subgroupOf C
  let θQ : ↥Q ≃* ↥(triD4LineN0 k K) :=
    (Subgroup.subgroupOfEquivOfLe hNRleC).trans θQ0
  let θN : ↥N ≃* ↥θH.range :=
    (Subgroup.subgroupOfEquivOfLe hH1leC).trans (MonoidHom.ofInjective hθHinj)
  have hH1norm : triD4LineH1 K σ ≤ Subgroup.normalizer (triD4LineNR K σ L) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]; intro m
    change triEmb K σ L m ∈ d4A2Qv L triD4LineV ↔
      triEmb K σ L (y * m * y⁻¹) ∈ d4A2Qv L triD4LineV
    have hyT : (y : ModGL TwistTag.D4.tag K) ∈ torusGroup Tag.D4 K :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).1).1
    have hιy : triEmb K σ L y ∈ torusGroup Tag.D4 L := by
      rw [triEmb_apply]
      exact CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup (algebraMap K L) hyT
    have hιy' : triEmb K σ L y ∈ Subgroup.normalizer (d4A2Qv L triD4LineV : Set (ModGL Tag.D4 L)) :=
      torusGroup_le_normalizer_d4A2Qv (K := L) triD4LineV hιy
    have hconj := (Subgroup.mem_normalizer_iff.1 hιy') (triEmb K σ L m)
    rw [show triEmb K σ L (y * m * y⁻¹) =
      triEmb K σ L y * triEmb K σ L m * (triEmb K σ L y)⁻¹ by rw [map_mul, map_mul, map_inv]]
    exact hconj
  have hQnorm : Q.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNRleC]
    change Subgroup.centralizer {triD4LineZ0 K σ ω hz} ≤ _
    rw [hCeq]
    exact sup_le hH1norm Subgroup.le_normalizer
  have hQsupN : Q ⊔ N = ⊤ := by
    rw [show Q ⊔ N = N ⊔ Q by rw [sup_comm],
      (Subgroup.subgroupOf_sup hH1leC hNRleC).symm, ← hCeq, Subgroup.subgroupOf_self]
  have hQ'supN' : triD4LineN0 k K ⊔ θH.range = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨g, c, h, rfl⟩ := triD4LineMk_surjective k K x
    let Dg : GL (Fin 3) k := thetaDiag c (1 : kˣ)
    have hDg : Matrix.GeneralLinearGroup.det Dg =
        Units.map (Algebra.norm k (S := K)) c := by
      rw [thetaDiag_det hdeg c 1, map_one, one_mul]
    have h1 : Matrix.GeneralLinearGroup.det (g * Dg⁻¹) =
        Units.map (Algebra.norm k (S := K)) (1 : Kˣ) := by
      rw [map_mul, map_inv, h, hDg, mul_inv_cancel, map_one]
    have hprod : Matrix.GeneralLinearGroup.det (g * Dg⁻¹ * Dg) =
        Units.map (Algebra.norm k (S := K)) (1 * c) := by
      rw [map_mul, h1, hDg, map_one, one_mul, one_mul]
    have hmemN0 : triD4LineMk k K (g * Dg⁻¹) 1 h1 ∈ triD4LineN0 k K :=
      (triD4LineMk_mem_N0_iff k K hdeg (g * Dg⁻¹) 1 h1).2 ⟨1, by simp⟩
    have hmemRange : triD4LineMk k K Dg c hDg ∈ θH.range := by
      obtain ⟨-, ⟨e, he⟩, -⟩ := even_triality_faithful_torus_coordinates K σ hσ3
      let y : ↥(triD4LineH1 K σ) :=
        ⟨⟨e (c, 1), graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom (e (c, 1)).2⟩,
          Subgroup.mem_subgroupOf.2 (e (c, 1)).2⟩
      have hy : (↑↑y : ModGL TwistTag.D4.tag K) = trialityTorusHom σ (c, 1) := by
        rw [show (↑↑y : ModGL TwistTag.D4.tag K) = ↑(e (c, 1)) from rfl, trialityTorusHom_apply]
        exact he c 1
      refine ⟨y, ?_⟩
      rw [hθHspec y c 1 1 hy (by rw [map_one, map_one]) Dg (thetaDiag_val c 1)
        (by rw [map_one, one_mul]; exact hDg)]
      exact (triD4LineMk_eq_mk_iff k K Dg Dg
        (Units.map (algebraMap k K).toMonoidHom (1 : kˣ) * c) c _ hDg).2
        ⟨1, by rw [map_one, one_mul], by rw [map_one, one_mul, one_mul]⟩
    have hprodEq : triD4LineMk k K (g * Dg⁻¹) 1 h1 * triD4LineMk k K Dg c hDg =
        triD4LineMk k K g c h := by
      rw [triD4LineMk_mul k K (g * Dg⁻¹) Dg 1 c h1 hDg hprod]
      exact (triD4LineMk_eq_mk_iff k K (g * Dg⁻¹ * Dg) g (1 * c) c hprod h).2
        ⟨1, by rw [map_one, one_mul]; group, by rw [map_one, one_mul, one_mul]⟩
    rw [← hprodEq]
    exact Subgroup.mul_mem_sup hmemN0 hmemRange
  have coords : ∀ y : ↥(triD4LineH1 K σ),
      ∃ (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) (c : kˣ),
        (↑↑y : ModGL TwistTag.D4.tag K) = trialityTorusHom σ (a, b) ∧
        trialityFixedUnit K σ b = Units.map (algebraMap k K).toMonoidHom c ∧
        θH y = triD4LineMk k K (thetaDiag a c)
          (Units.map (algebraMap k K).toMonoidHom c * a) (thetaDiag_det hdeg a c) := by
    intro y
    obtain ⟨-, ⟨e, he⟩, -⟩ := even_triality_faithful_torus_coordinates K σ hσ3
    let cH := Subgroup.subgroupOfEquivOfLe (graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom)
    let ab := e.symm (cH y)
    have h2 : e ab = cH y := e.apply_symm_apply (cH y)
    have hy : (↑↑y : ModGL TwistTag.D4.tag K) = trialityTorusHom σ ab := by
      have h3 : (↑↑y : ModGL TwistTag.D4.tag K) = ↑(e ab) := by
        rw [← Subgroup.subgroupOfEquivOfLe_apply_coe
          (graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom) y, h2]
      rw [h3, trialityTorusHom_apply]
      exact he ab.1 ab.2
    obtain ⟨c, hc⟩ := exists_algebraMap_fixedUnit hdeg τ hτorder σ hτ ab.2
    refine ⟨ab.1, ab.2, c, hy, hc, ?_⟩
    rw [hθHspec y ab.1 ab.2 c hy hc (thetaDiag ab.1 c)
      (thetaDiag_val ab.1 c) (thetaDiag_det hdeg ab.1 c)]
  have hagree : ∀ (x : ↥C) (hxQ : x ∈ Q) (hxN : x ∈ N),
      ((θQ ⟨x, hxQ⟩ : ↥(triD4LineN0 k K)) : TriD4LineX k K) =
        ((θN ⟨x, hxN⟩ : ↥θH.range) : TriD4LineX k K) := by
    intro x hxQ hxN
    let y : ↥(triD4LineH1 K σ) := ⟨(x : ↥C), Subgroup.mem_subgroupOf.1 hxN⟩
    obtain ⟨a, b, c, hyT, hbc, hθHa⟩ := coords y
    obtain ⟨s, hs1, hs2⟩ := triD4LineTheta_agree K hK σ k τ hτ hdeg hτorder L y
      (Subgroup.mem_subgroupOf.1 hxQ) a b c hyT hbc (thetaDiag a c) (thetaDiag_val a c)
      (thetaDiag_det hdeg a c)
    have h1 := (hθQ0 ⟨(x : ↥C), Subgroup.mem_subgroupOf.1 hxQ⟩ s).2 hs1
    have eL : ((θQ ⟨x, hxQ⟩ : ↥(triD4LineN0 k K)) : TriD4LineX k K) =
        (θQ0 ⟨(x : ↥C), Subgroup.mem_subgroupOf.1 hxQ⟩ : TriD4LineX k K) := rfl
    rw [eL, show ((θN ⟨x, hxN⟩ : ↥θH.range) : TriD4LineX k K) = θH y from rfl,
      h1, hs2, hθHa]
  have hback : ∀ n : ↥N, ((θN n : ↥θH.range) : TriD4LineX k K) ∈ triD4LineN0 k K →
      (n : ↥C) ∈ Q := by
    intro n hn
    let y : ↥(triD4LineH1 K σ) := ⟨(n : ↥C), Subgroup.mem_subgroupOf.1 n.2⟩
    obtain ⟨a, b, c, hyT, hbc, hθHa⟩ := coords y
    have hn0 : triD4LineMk k K (thetaDiag a c)
        (Units.map (algebraMap k K).toMonoidHom c * a) (thetaDiag_det hdeg a c) ∈
        triD4LineN0 k K := by
      rw [← hθHa]
      exact hn
    obtain ⟨μ, hμ⟩ := (triD4LineMk_mem_N0_iff k K hdeg (thetaDiag a c)
      (Units.map (algebraMap k K).toMonoidHom c * a) (thetaDiag_det hdeg a c)).1 hn0
    have ha_img : ∃ a' : k, algebraMap k K a' = (a : K) := by
      refine ⟨↑(μ * c⁻¹), ?_⟩
      have h2 : Units.map (algebraMap k K).toMonoidHom (μ * c⁻¹) = a := by
        rw [map_mul, map_inv, ← hμ, mul_assoc, mul_comm a, ← mul_assoc, mul_inv_cancel, one_mul]
      exact congrArg Units.val h2
    obtain ⟨a', ha'⟩ := ha_img
    have hσa : σ (a : K) = (a : K) := by
      rw [← ha', theta_sigma_algebraMap hk σ hσ a']
    have hσua : Units.map ((σ : K →+* K).toMonoidHom) a = a := Units.ext hσa
    have hσ2a : σ (σ (a : K)) = (a : K) := by rw [hσa, hσa]
    have hσ2ua : Units.map ((σ : K →+* K).toMonoidHom)
        (Units.map ((σ : K →+* K).toMonoidHom) a) = a := Units.ext hσ2a
    have hιy : triEmb K σ L y ∈ d4A2Qv L triD4LineV := by
      have htri : triEmb K σ L y = rootDiagUnit Tag.D4
          (fun i => Units.map (algebraMap K L)
            (thetaTuple σ a (Units.map (algebraMap k K).toMonoidHom c) i)) := by
        rw [triEmb_apply, hyT, trialityTorusHom_apply, trialityOuter_mul_middle_eq, hbc]
        rw [baseChangeGL_rootDiagUnit]
        rfl
      rw [htri]
      refine (triD4Line_rootDiagUnit_mem_Qv_iff L _).2 ⟨?_, ?_⟩
      · rw [thetaTuple_apply_one, thetaTuple_apply_zero, hσua]
      · rw [thetaTuple_apply_three, thetaTuple_apply_zero, hσ2ua]
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_comap.2 hιy)
  have hconj : ∀ (n : ↥N) (q : ↥Q),
      ((θQ ⟨(n : ↥C) * q * (n : ↥C)⁻¹, hQnorm.conj_mem (q : ↥C) q.2 (n : ↥C)⟩ :
          ↥(triD4LineN0 k K)) : TriD4LineX k K) =
        ((θN n : ↥θH.range) : TriD4LineX k K) * ((θQ q : ↥(triD4LineN0 k K)) : TriD4LineX k K) *
          (((θN n : ↥θH.range)) : TriD4LineX k K)⁻¹ := by
    intro n q
    let y : ↥(triD4LineH1 K σ) := ⟨(n : ↥C), Subgroup.mem_subgroupOf.1 n.2⟩
    obtain ⟨a, b, c, hyT, hbc, hθHa⟩ := coords y
    let m : ↥(triD4LineNR K σ L) := ⟨(q : ↥C), Subgroup.mem_subgroupOf.1 q.2⟩
    let m' : ↥(triD4LineNR K σ L) := ⟨(n : ↥C) * q * (n : ↥C)⁻¹,
      Subgroup.mem_subgroupOf.1 (hQnorm.conj_mem (q : ↥C) q.2 (n : ↥C))⟩
    have hm1 : (θQ0 m : TriD4LineX k K) ∈ (triD4LineSL3 k K).range := by
      rw [triD4LineSL3_range]; exact (θQ0 m).2
    have hm2 : (θQ0 m' : TriD4LineX k K) ∈ (triD4LineSL3 k K).range := by
      rw [triD4LineSL3_range]; exact (θQ0 m').2
    obtain ⟨s, hs⟩ := hm1
    obtain ⟨s', hs'⟩ := hm2
    have key := triD4LineTheta_conj K hK σ k τ hτ hdeg hτorder L y a b c hyT hbc
      (thetaDiag a c) (thetaDiag_val a c) (thetaDiag_det hdeg a c) m m' rfl s s'
      ((hθQ0 m s).1 hs.symm) ((hθQ0 m' s').1 hs'.symm)
    have eL : ((θQ ⟨(n : ↥C) * q * (n : ↥C)⁻¹,
        hQnorm.conj_mem (q : ↥C) q.2 (n : ↥C)⟩ :
        ↥(triD4LineN0 k K)) : TriD4LineX k K) = (θQ0 m' : TriD4LineX k K) := rfl
    have eQ : ((θQ q : ↥(triD4LineN0 k K)) : TriD4LineX k K) =
        (θQ0 m : TriD4LineX k K) := rfl
    have eN : ((θN n : ↥θH.range) : TriD4LineX k K) = θH y := rfl
    rw [eL, hs'.symm, eN, hθHa, eQ, hs.symm]
    exact key.symm
  obtain ⟨ζ, hζQ, hζN⟩ := CFSG.GroupTheory.exists_mulEquiv_sup_glue_of_normal hQnorm
    (triD4LineN0_normal k K) θQ θN hagree hback hconj
  let e1 : ↥C ≃* ↥(Q ⊔ N) :=
    (Subgroup.topEquiv (G := ↥C)).symm.trans (MulEquiv.subgroupCongr hQsupN).symm
  let e2 : ↥(triD4LineN0 k K ⊔ θH.range) ≃* TriD4LineX k K :=
    (MulEquiv.subgroupCongr hQ'supN').trans (Subgroup.topEquiv (G := TriD4LineX k K))
  let Θ : ↥C ≃* TriD4LineX k K := e1.trans (ζ.trans e2)
  refine ⟨Θ, ?_⟩
  intro y hy
  let R := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hΘQ : ∀ q : ↥Q, Θ (q : ↥C) = (θQ q : TriD4LineX k K) := fun q => by
    have h1 : e1 (q : ↥C) = ⟨q, Subgroup.mem_sup_left q.2⟩ := Subtype.ext rfl
    rw [show Θ (q : ↥C) = e2 (ζ (e1 (q : ↥C))) from rfl, h1, ← hζQ q]; rfl
  have hΘN : ∀ n : ↥N, Θ (n : ↥C) = (θN n : TriD4LineX k K) := fun n => by
    have h1 : e1 (n : ↥C) = ⟨n, Subgroup.mem_sup_right n.2⟩ := Subtype.ext rfl
    rw [show Θ (n : ↥C) = e2 (ζ (e1 (n : ↥C))) from rfl, h1, ← hζN n]; rfl
  obtain ⟨q₀, hq₀, n₀, hn₀, hyqn⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Q) (t := N) (hs := hQnorm)).1
      (show (y : ↥C) ∈ Q ⊔ N by rw [hQsupN]; exact Subgroup.mem_top _)
  let q : ↥Q := ⟨q₀, hq₀⟩
  let n : ↥N := ⟨n₀, hn₀⟩
  have hyqn' : (q : ↥C) * (n : ↥C) = y := hyqn
  let nH : ↥(triD4LineH1 K σ) := ⟨(n : ↥C), Subgroup.mem_subgroupOf.1 n.2⟩
  obtain ⟨y', hy'val, hy'theta⟩ :=
    triD4LineTheta_equivariant_H1 K hK σ hσ k hk τ hτ hdeg hτorder θH hθHspec nH
  have hσy : fieldActor (t := TwistTag.D4) σ σ (y : R) = ((q : ↥C) : R) * (y' : R) := by
    rw [show (y : R) = ((q : ↥C) : R) * ((n : ↥C) : R) by rw [← hyqn', Subgroup.coe_mul],
      map_mul, triD4LineTheta_fieldActor_NR K hK σ hσ L
        ⟨(q : ↥C), Subgroup.mem_subgroupOf.1 q.2⟩, hy'val.symm]
  let yc : ↥C := ⟨(y' : R), hH1leC y'.2⟩
  have hyc : (⟨fieldActor (t := TwistTag.D4) σ σ (y : R), hy⟩ : ↥C) = (q : ↥C) * yc :=
    Subtype.ext hσy
  let nN : ↥N := ⟨yc, y'.2⟩
  have hθNnN : ((θN nN : ↥θH.range) : TriD4LineX k K) = θH y' := by
    have hsub : (Subgroup.subgroupOfEquivOfLe hH1leC) nN = y' := Subtype.ext rfl
    rw [show θN nN = (MonoidHom.ofInjective hθHinj)
        ((Subgroup.subgroupOfEquivOfLe hH1leC) nN) from rfl,
      MonoidHom.ofInjective_apply hθHinj, hsub]
  have hLHS : Θ (⟨fieldActor (t := TwistTag.D4) σ σ (y : R), hy⟩ : ↥C) =
      (θQ q : TriD4LineX k K) * triD4LineSigma k K τ (θH nH) := by
    rw [hyc, map_mul, hΘQ q, show yc = (nN : ↥C) from rfl, hΘN nN, hθNnN, hy'theta]
  have hRHS : triD4LineSigma k K τ (Θ y) =
      (θQ q : TriD4LineX k K) * triD4LineSigma k K τ (θH nH) := by
    rw [hyqn'.symm, map_mul, hΘQ q, hΘN n, map_mul,
      triD4LineSigma_eq_self_of_mem_N0 k K τ (θQ q).2,
      show ((θN n : ↥θH.range) : TriD4LineX k K) = θH nH from rfl]
  exact hLHS.trans hRHS.symm

end CFSG.StandardType
