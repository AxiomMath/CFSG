module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaQ
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXThetaH

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

private lemma triD4LineMk_congr {K k : Type} [Field K] [Field k] [Algebra k K]
    {g g' : GL (Fin 3) k} {c c' : Kˣ} (hg : g = g') (hc : c = c')
    (h : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K)) c)
    (h' : Matrix.GeneralLinearGroup.det g' = Units.map (Algebra.norm k (S := K)) c') :
    triD4LineMk k K g c h = triD4LineMk k K g' c' h' := by
  cases hg
  cases hc
  unfold triD4LineMk
  exact congrArg QuotientGroup.mk (Subtype.ext rfl)

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

private lemma theta_sigma_cube_eq_one {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    σ ^ 3 = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  refine RingEquiv.ext fun c => ?_
  rw [ringEquiv_pow_three_apply]
  have hcard : ∀ x : K, x ^ Nat.card K = x := fun x => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  rw [hσ, hσ, hσ]
  calc ((c ^ 2 ^ n) ^ 2 ^ n) ^ 2 ^ n = c ^ ((2 ^ n) * (2 ^ n) * (2 ^ n)) := by
        rw [pow_mul, pow_mul]
    _ = c ^ Nat.card K := by
        congr 1
        rw [hK]
        ring
    _ = c := hcard c

private lemma baseChangeGL_entrywise {τ : Tag} {K L : Type} [Field K] [Field L]
    (ι : K →+* L) (η : K →+* K) (η' : L →+* L) (hcomm : ∀ c, η' (ι c) = ι (η c))
    (x : ModGL τ K) :
    baseChangeGL ι (Units.map (entrywiseHom η) x) =
      Units.map (entrywiseHom η') (baseChangeGL ι x) := by
  refine Units.ext (end_ext_single fun b => ?_)
  have hfun : entrywiseHom η' (↑(baseChangeGL ι x) : Module.End L (RootModule τ L))
      = entrywise η' (↑(baseChangeGL ι x) : Module.End L (RootModule τ L)) := rfl
  have hLfun : (↑(Units.map (entrywiseHom η) x) : Module.End K (RootModule τ K))
      = entrywise η (x : Module.End K (RootModule τ K)) := rfl
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [baseChangeGL_apply_single, hfun, entrywise_single, baseChangeGL_apply_single]
  ext c
  rw [hLfun, entrywise_single]
  simp only [Finsupp.mapRange_apply, hcomm]

private lemma entrywise_trialityTorusHom {K : Type} [Field K]
    (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1)
    (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    Units.map (entrywiseHom σ.toRingHom) (trialityTorusHom σ (a, b)) =
      trialityTorusHom σ (Units.map σ.toMonoidHom a, b) := by
  simp only [trialityTorusHom_apply, trialityOuterTorus_eq, trialityMiddleTorus, map_mul,
    CFSG.LieType.Chevalley.entrywise_torusElt, units_map_three hσ3,
    units_map_trialityFixedUnit b]

theorem triD4LineTheta_fieldActor_NR
    {n : ℕ} (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (L : Type) [Field L] [Algebra K L]
    (m : ↥(triD4LineNR K σ L)) :
    fieldActor (t := TwistTag.D4) σ σ
        (m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      (m : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hcomm : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L (σ c) := by
    intro c
    rw [hFr, ← map_pow, hσ]
  have hmQ : triEmb K σ L m ∈ d4A2Qv L triD4LineV := Subgroup.mem_comap.1 m.2
  have hfix : twistHom TwistTag.D4 L Fr (triEmb K σ L m) = triEmb K σ L m :=
    triEmb_fixed Fr (RingHom.ext fun c => (hcomm c).symm) m
  have hentry := triD4Line_twistHom_eq_entrywise L Fr (triEmb K σ L m) hmQ
  have hFrFix : Units.map (entrywiseHom Fr) (triEmb K σ L m) = triEmb K σ L m :=
    hentry.symm.trans hfix
  apply triEmb_injective (K := K) (σ := σ) (L := L)
  rw [triEmb_apply, coe_fieldActor, triEmb_apply,
    baseChangeGL_entrywise (algebraMap K L) σ.toRingHom Fr hcomm]
  exact hFrFix

theorem triD4LineTheta_equivariant_H1
    {n : ℕ} (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (k : Type) [Field k] [Algebra k K]
    (hk : Nat.card k = 2 ^ n) (τ : K ≃ₐ[k] K) (hτ : ∀ c, τ c = σ c)
    (hdeg : Module.finrank k K = 3) (hτo : orderOf τ = 3)
    (θH : ↥(triD4LineH1 K σ) →* TriD4LineX k K)
    (hθH : ∀ (y : ↥(triD4LineH1 K σ)) (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ)
        (c : kˣ),
        ((y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
            trialityTorusHom σ (a, b) →
        trialityFixedUnit K σ b = Units.map (algebraMap k K).toMonoidHom c →
        ∀ g : GL (Fin 3) k,
          (g : Matrix (Fin 3) (Fin 3) k) =
            Matrix.diagonal ![(c : k) ^ 2, Algebra.norm k (a : K), (c : k)] →
        ∀ hdet : Matrix.GeneralLinearGroup.det g = Units.map (Algebra.norm k (S := K))
            (Units.map (algebraMap k K).toMonoidHom c * a),
          θH y = triD4LineMk k K g (Units.map (algebraMap k K).toMonoidHom c * a) hdet)
    (y : ↥(triD4LineH1 K σ)) :
    ∃ y' : ↥(triD4LineH1 K σ),
      (y' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
          fieldActor (t := TwistTag.D4) σ σ
            (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
        θH y' = triD4LineSigma k K τ (θH y) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have h1 : Nat.card K = 1 := by rw [hK, h]; norm_num
      rw [Nat.card_eq_fintype_card] at h1
      have h2 := Fintype.one_lt_card (α := K)
      omega
    · exact h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Module.Finite k K := Module.Finite.of_finite
  have hσ3 : σ ^ 3 = 1 := theta_sigma_cube_eq_one hK σ hσ
  obtain ⟨hTorusEq, ⟨e, he⟩, -⟩ := even_triality_faithful_torus_coordinates (K := K) σ hσ3
  let cH := Subgroup.subgroupOfEquivOfLe (graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom)
  let ab := e.symm (cH y)
  have hy : (↑↑y : ModGL TwistTag.D4.tag K) = trialityTorusHom σ ab := by
    have h2 : e ab = cH y := by
      change e (e.symm (cH y)) = cH y
      rw [MulEquiv.apply_symm_apply]
    have h3 : (↑↑y : ModGL TwistTag.D4.tag K) = ↑(e ab) := by
      rw [← Subgroup.subgroupOfEquivOfLe_apply_coe
        (graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom) y, h2]
    rw [h3, trialityTorusHom_apply]
    exact he ab.1 ab.2
  obtain ⟨c, hc⟩ := exists_algebraMap_fixedUnit hdeg τ hτo σ hτ ab.2
  let p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ := (Units.map σ.toMonoidHom ab.1, ab.2)
  have hmemT : trialityTorusHom σ p ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
    rw [← hTorusEq]
    exact trialityTorusHom_mem_graphFixedTorus (σ := σ) hσ3 p
  have hmemR : trialityTorusHom σ p ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootTorus_le TwistTag.D4 K σ.toRingHom hmemT
  let y' : ↥(triD4LineH1 K σ) := ⟨⟨trialityTorusHom σ p, hmemR⟩, hmemT⟩
  have hy'val : ((y' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K)
      = trialityTorusHom σ p := rfl
  have hyval : ((y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K)
      = trialityTorusHom σ ab := hy
  have hnorm : Algebra.norm k (σ (ab.1 : K)) = Algebra.norm k (ab.1 : K) := by
    rw [← hτ (ab.1 : K)]
    exact Algebra.norm_eq_of_algEquiv (R := k) τ (ab.1 : K)
  have hnormu : Units.map (Algebra.norm k (S := K)) (Units.map σ.toMonoidHom ab.1)
      = Units.map (Algebra.norm k) ab.1 := Units.ext hnorm
  have hdiag : thetaDiag (Units.map σ.toMonoidHom ab.1) c = thetaDiag ab.1 c := by
    refine Units.ext ?_
    rw [thetaDiag_val, thetaDiag_val]
    congr 1
    funext j
    fin_cases j <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
    · rfl
    · exact hnorm
    · rfl
  have hσc : Units.map σ.toMonoidHom (Units.map (algebraMap k K).toMonoidHom c)
      = Units.map (algebraMap k K).toMonoidHom c :=
    Units.ext (theta_sigma_algebraMap hk σ hσ (c : k))
  have hτu : ∀ x : Kˣ, Units.mapEquiv τ.toRingEquiv.toMulEquiv x
      = Units.map σ.toMonoidHom x := fun x => Units.ext (hτ (x : K))
  have hcoord : Units.mapEquiv τ.toRingEquiv.toMulEquiv
      (Units.map (algebraMap k K).toMonoidHom c * ab.1)
      = Units.map (algebraMap k K).toMonoidHom c * Units.map σ.toMonoidHom ab.1 := by
    rw [hτu, map_mul, hσc]
  refine ⟨y', ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_fieldActor, hyval, entrywise_trialityTorusHom σ hσ3 ab.1 ab.2]
  · have hθy : θH y = triD4LineMk k K (thetaDiag ab.1 c)
        (Units.map (algebraMap k K).toMonoidHom c * ab.1) (thetaDiag_det hdeg ab.1 c) :=
      hθH y ab.1 ab.2 c hy hc (thetaDiag ab.1 c) (thetaDiag_val ab.1 c)
        (thetaDiag_det hdeg ab.1 c)
    have hθy' : θH y' = triD4LineMk k K (thetaDiag (Units.map σ.toMonoidHom ab.1) c)
        (Units.map (algebraMap k K).toMonoidHom c * Units.map σ.toMonoidHom ab.1)
        (thetaDiag_det hdeg (Units.map σ.toMonoidHom ab.1) c) :=
      hθH y' (Units.map σ.toMonoidHom ab.1) ab.2 c hy'val hc
        (thetaDiag (Units.map σ.toMonoidHom ab.1) c)
        (thetaDiag_val (Units.map σ.toMonoidHom ab.1) c)
        (thetaDiag_det hdeg (Units.map σ.toMonoidHom ab.1) c)
    have hdetSigma : Matrix.GeneralLinearGroup.det (thetaDiag ab.1 c) =
        Units.map (Algebra.norm k (S := K))
          (Units.mapEquiv τ.toRingEquiv.toMulEquiv
            (Units.map (algebraMap k K).toMonoidHom c * ab.1)) := by
      calc Matrix.GeneralLinearGroup.det (thetaDiag ab.1 c)
          = Units.map (Algebra.norm k (S := K))
              (Units.map (algebraMap k K).toMonoidHom c * ab.1) :=
            thetaDiag_det hdeg ab.1 c
        _ = Units.map (Algebra.norm k (S := K))
              (Units.map (algebraMap k K).toMonoidHom c) *
              Units.map (Algebra.norm k (S := K)) ab.1 := by rw [map_mul]
        _ = Units.map (Algebra.norm k (S := K))
              (Units.map (algebraMap k K).toMonoidHom c) *
              Units.map (Algebra.norm k (S := K)) (Units.map σ.toMonoidHom ab.1) := by
            rw [hnormu]
        _ = Units.map (Algebra.norm k (S := K))
              (Units.mapEquiv τ.toRingEquiv.toMulEquiv
                (Units.map (algebraMap k K).toMonoidHom c * ab.1)) := by
            rw [hcoord, map_mul]
    have hsig := triD4LineSigma_mk k K τ (thetaDiag ab.1 c)
      (Units.map (algebraMap k K).toMonoidHom c * ab.1) (thetaDiag_det hdeg ab.1 c) hdetSigma
    rw [hθy', hθy, hsig]
    exact triD4LineMk_congr hdiag hcoord.symm
      (thetaDiag_det hdeg (Units.map σ.toMonoidHom ab.1) c) hdetSigma

end CFSG.StandardType
