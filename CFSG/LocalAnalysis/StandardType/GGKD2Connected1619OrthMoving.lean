module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelSelfDual
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockModels
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGKD2LinearLemmas1615
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
public import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Comp
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Struct
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallBlock
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocksComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Orth2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockProofFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgOrthogonalLie

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615
open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.T171Sh

private theorem ltromm_quotientInner_of_ggInnerOn {R : Type} [Group R] {C : Subgroup R}
    {β : MulAut R} (h : ∃ z ∈ C, ∀ j ∈ C, β j = z * j * z⁻¹) : QuotientInner C β := by
  obtain ⟨z, hzC, hz⟩ := h
  refine ⟨QuotientGroup.mk ⟨z, hzC⟩, ?_⟩
  intro c c' hcc
  have hval : (c' : R) = z * (c : R) * z⁻¹ := by rw [← hcc, hz c c.2]
  have hmem : (⟨z, hzC⟩ * c * ⟨z, hzC⟩⁻¹ : ↥C) = c' := Subtype.ext (by simpa using hval.symm)
  rw [show (QuotientGroup.mk ⟨z, hzC⟩ * (c : ↥C ⧸ Subgroup.center ↥C) *
        (QuotientGroup.mk ⟨z, hzC⟩)⁻¹ : ↥C ⧸ Subgroup.center ↥C) =
        QuotientGroup.mk (⟨z, hzC⟩ * c * ⟨z, hzC⟩⁻¹) from by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]]
  rw [hmem]

private theorem ltromm_ggInnerOn_of_map {R R' : Type} [Group R] [Group R'] (f : R →* R')
    (hf : Function.Injective f) {C : Subgroup R} {C' : Subgroup R'} (hC : C.map f = C')
    {β : MulAut R} {β' : MulAut R'} (hβ : ∀ c : R, f (β c) = β' (f c))
    (h : ∃ z ∈ C', ∀ j ∈ C', β' j = z * j * z⁻¹) :
    ∃ z ∈ C, ∀ j ∈ C, β j = z * j * z⁻¹ := by
  obtain ⟨z', hz'C', hz'⟩ := h
  have hz'C : z' ∈ C.map f := hC.symm ▸ hz'C'
  obtain ⟨z, hzC, hzf⟩ := Subgroup.mem_map.mp hz'C
  refine ⟨z, hzC, fun j hj => ?_⟩
  apply hf
  calc f (β j) = β' (f j) := hβ j
    _ = z' * f j * z'⁻¹ := hz' (f j) (hC ▸ Subgroup.mem_map_of_mem f hj)
    _ = f z * f j * (f z)⁻¹ := by rw [hzf]
    _ = f (z * j * z⁻¹) := by simp only [map_mul, map_inv]

private theorem ltromm_conj_comp {G H : Type} [Group G] [Group H] (f : G →* H) (y : G) :
    (MulAut.conj (f y)).toMonoidHom.comp f = f.comp (MulAut.conj y).toMonoidHom := by
  ext z
  simp [MulAut.conj_apply, map_mul]

private theorem ltromm_conj_comp_apply {G H : Type} [Group G] [Group H] (f : G →* H) (y c : G) :
    f (MulAut.conj y c) = MulAut.conj (f y) (f c) :=
  (congrArg (fun g : G →* H => g c) (ltromm_conj_comp f y)).symm

private theorem ltromm_factorization_504 : (504 : ℕ).factorization 2 = 3 := by
  rw [show (504 : ℕ) = 2 ^ 3 * 63 by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (p := 2) (n := 3) (by norm_num : Nat.Prime 2),
    Nat.factorization_eq_zero_of_not_dvd (p := 2) (n := 63) (by norm_num : ¬ 2 ∣ 63), add_zero]

private theorem ltromm_card_eq_504_of_label {Q : Type} [Group Q]
    (hQ : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) Q) : Nat.card Q = 504 := by
  dsimp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeLinear] at hQ
  obtain ⟨K₀, hfK₀, hfinK₀, hcardK₀, hQ0⟩ := hQ
  letI : Field K₀ := hfK₀
  letI : Finite K₀ := hfinK₀
  obtain ⟨eQ⟩ := hQ0
  have hK8 : Nat.card K₀ = 8 := by rw [hcardK₀]; norm_num
  have h : Nat.card (LargeEvenProj (LargeEvenSLGroup (Fin 2) K₀)) =
      Nat.card (StatedProj (StatedSL 2 K₀)) := by
    rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL]
  rw [Nat.card_congr eQ.toEquiv, h,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK8]
  norm_num

private theorem ltromm_specialBlock_le_orthDerived {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {x : V ≃ₗ[F] V} {h : Polynomial F}
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    specialBlock Q x h ≤ orthDerived Q := by
  haveI : Group.IsPerfect ↥(specialBlock Q x h) := ⟨hq.1.commutator_eq_top⟩
  have hleQ : specialBlock Q x h ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    fun g hg => (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer h hg)).1
  calc specialBlock Q x h = ⁅specialBlock Q x h, specialBlock Q x h⁆ :=
        (Subgroup.commutator_eq_self).symm
    _ ≤ orthDerived Q := Subgroup.commutator_mono hleQ hleQ

private theorem ltromm_paired_false {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[F] V)) {h : Polynomial F}
    [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ⧸
        Subgroup.center ↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))))
    (hnsd : h ≠ reciprocalPolynomial h) : False := by
  classical
  haveI hperf : Group.IsPerfect ↥(specialBlock Q (x : V ≃ₗ[F] V) h) :=
    ⟨hq.1.commutator_eq_top⟩
  have hleOrth : specialBlock Q (x : V ≃ₗ[F] V) h ≤ orthDerived Q := by
    have hleQ : specialBlock Q (x : V ≃ₗ[F] V) h ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
      fun g hg => (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer h hg)).1
    calc specialBlock Q (x : V ≃ₗ[F] V) h
        = ⁅specialBlock Q (x : V ≃ₗ[F] V) h, specialBlock Q (x : V ≃ₗ[F] V) h⁆ :=
          (Subgroup.commutator_eq_self).symm
      _ ≤ orthDerived Q := Subgroup.commutator_mono hleQ hleQ
  let L : Subgroup ↥(orthDerived Q) :=
    (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)
  let E : Type := AdjoinRoot h
  obtain ⟨eSL⟩ := hx.nonempty_specialBlock_mulEquiv_SL_paired hh hnsd
  haveI : CharP E 2 := by
    change CharP (AdjoinRoot h) 2
    exact charP_of_injective_algebraMap (algebraMap F (AdjoinRoot h)).injective 2
  let eL : ↥L ≃* ↥(specialBlock Q (x : V ≃ₗ[F] V) h) := Subgroup.subgroupOfEquivOfLe hleOrth
  let eSL' : ↥L ≃* StatedSL (primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap h) E :=
    (eL.trans eSL).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL
        (primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap h) E)
  obtain ⟨φ⟩ :=
    CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj eSL'
  have hm2 : 2 ≤ primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap h :=
    CFSG.StandardType.SevOmSmall.two_le_primaryMultiplicity hx hh hq
  have h2E : (2 : E) = 0 := CharP.cast_eq_zero E 2
  obtain ⟨hm_eq, hE8⟩ := CFSG.StandardType.KD2Pieces1615.kd2Lin_numerology h2E hm2 φ hlab
  obtain ⟨hlam0, hlam⟩ := hx.orderOf_root Nat.prime_three hh hne
  have hdvd : 3 ∣ Nat.card E - 1 := by
    rw [← hlam]
    simpa only [orderOf_units] using
      (CFSG.RankThree.Classical.orderOf_dvd_natCard_sub_one
        (z := (Units.mk0 (AdjoinRoot.root h) hlam0 : E)) hlam0)
  rw [hE8] at hdvd
  norm_num at hdvd

private theorem ltromm_cyc3_of_selfDual {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q 3 x) {h : Polynomial F}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) : h = X ^ 2 + X + 1 := by
  have hdvd' : h ∣ (X ^ 2 + X + 1 : Polynomial F) := by
    have h1 : h ∣ (X ^ 3 - 1 : Polynomial F) := hx.dvd_X_pow_sub_one hh
    rw [show (X ^ 3 - 1 : Polynomial F) = (X - 1) * (X ^ 2 + X + 1) by ring] at h1
    rcases (irreducible_of_mem_primaryFactors hh).prime.dvd_or_dvd h1 with h2 | h2
    · refine absurd ?_ hne
      have h3 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le (monic_of_mem_primaryFactors hh)
        (monic_X_sub_C 1) h2
        (by rw [Polynomial.natDegree_X_sub_C]
            exact Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors hh))
      exact h3.symm
    · exact h2
  have hdeg_le : h.natDegree ≤ 2 := by
    have h2 : (X ^ 2 + X + 1 : Polynomial F) ≠ 0 := by
      intro h0
      have h3 : (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 := by compute_degree!
      rw [h0] at h3
      simp at h3
    have := Polynomial.natDegree_le_of_dvd hdvd' h2
    rwa [show (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 by compute_degree!] at this
  have hdeg_ne_one : h.natDegree ≠ 1 := by
    intro hdeg1
    obtain ⟨a, ha0, b, hab⟩ := Polynomial.natDegree_eq_one.mp hdeg1
    have hcoeff : a = h.coeff 1 := by
      have := congrArg (fun p : Polynomial F => p.coeff 1) hab
      simpa using this
    have ha1 : a = 1 := by
      rw [hcoeff, ← hdeg1]
      exact (monic_of_mem_primaryFactors hh).coeff_natDegree
    have hb0 : b ≠ 0 := by
      have h0 := hx.coeff_zero_ne hh
      rw [← hab, ha1] at h0
      simpa using h0
    have hlin : h = X + C b := by
      rw [← hab, ha1]; simp
    have hrec : reciprocalPolynomial (X + C b : Polynomial F) = X + C b⁻¹ :=
      CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2.reciprocalPolynomial_X_add_C hb0
    have heq : (X + C b : Polynomial F) = X + C b⁻¹ := by
      have h' : h = reciprocalPolynomial h := hself
      rw [hlin, hrec] at h'
      exact h'
    have hb1 : b = b⁻¹ := by
      have := congrArg (fun p : Polynomial F => p.coeff 0) heq
      simpa using this
    have hb2 : b ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hb1]
      exact mul_inv_cancel₀ hb0
    have hb_one : b = 1 := by
      rcases sq_eq_one_iff.mp hb2 with hb | hb
      · exact hb
      · rw [CharTwo.neg_eq] at hb
        exact hb
    exact hne (by rw [hlin, hb_one, sub_eq_add_neg, CharTwo.neg_eq, Polynomial.C_1])
  have hdeg : h.natDegree = 2 := by
    have hpos := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors hh)
    omega
  have hmonic_q : (X ^ 2 + X + 1 : Polynomial F).Monic := by
    rw [show (X ^ 2 + X + 1 : Polynomial F) = X ^ 2 + (X + 1) by ring]
    exact Polynomial.monic_X_pow_add (by compute_degree!)
  have hdeg_qh : (X ^ 2 + X + 1 : Polynomial F).natDegree ≤ h.natDegree := by
    rw [show (X ^ 2 + X + 1 : Polynomial F).natDegree = 2 by compute_degree!, hdeg]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (monic_of_mem_primaryFactors hh)
    hmonic_q hdvd' hdeg_qh).symm

private theorem ltromm_numerology {f m : ℕ} (hm : 2 ≤ m) (h : f * (m * (m - 1) / 2) = 3) :
    (f = 3 ∧ m = 2) ∨ (f = 1 ∧ m = 3) := by
  have hdvd : m * (m - 1) / 2 ∣ 3 := ⟨f, by rw [mul_comm]; exact h.symm⟩
  have h2d : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self m))
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · left
    have hmul : m * (m - 1) = 2 := by rw [← h2d, h1]
    have hm2 : m = 2 := by
      have hle : m ≤ 2 := by
        by_contra hlt
        have hm3 : 3 ≤ m := by omega
        have h3' : 2 ≤ m - 1 := by omega
        have h6 : 6 ≤ m * (m - 1) := by
          calc 6 = 3 * 2 := by norm_num
            _ ≤ m * (m - 1) := Nat.mul_le_mul hm3 h3'
        omega
      omega
    rw [hm2] at h
    exact ⟨by omega, hm2⟩
  · right
    have hmul : m * (m - 1) = 6 := by rw [← h2d, h3]
    have hm3 : m = 3 := by
      have hle : m ≤ 3 := by
        by_contra hlt
        have hm4 : 4 ≤ m := by omega
        have h3' : 3 ≤ m - 1 := by omega
        have h12 : 12 ≤ m * (m - 1) := by
          calc 12 = 4 * 3 := by norm_num
            _ ≤ m * (m - 1) := Nat.mul_le_mul hm4 h3'
        omega
      have h2case : m ≠ 2 := by
        intro h2
        rw [h2] at hmul
        norm_num at hmul
      omega
    rw [hm3] at h
    exact ⟨by omega, hm3⟩

private theorem ltromm_card_block_eq {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[F] V))
    (hmem : (X ^ 2 + X + 1 : Polynomial F) ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)) ⧸
        Subgroup.center ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf
          (orthDerived Q)))) :
    Nat.card (specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)) =
        504 * Nat.card (Subgroup.center
          ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))) ∧
      Odd (Nat.card (Subgroup.center ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf
          (orthDerived Q)))) := by
  classical
  have hleOrth := ltromm_specialBlock_le_orthDerived hq
  let L : Subgroup ↥(orthDerived Q) :=
    (specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)
  let eL : ↥L ≃* ↥(specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)) :=
    Subgroup.subgroupOfEquivOfLe hleOrth
  have hcardL : Nat.card ↥L =
      Nat.card ↥(specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)) :=
    Nat.card_congr eL.toEquiv
  have hcardQ : Nat.card (↥L ⧸ Subgroup.center ↥L) = 504 :=
    ltromm_card_eq_504_of_label hlab
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
  refine ⟨by rw [← hcardL, hcard, hcardQ], ?_⟩
  have hm2 : 2 ≤ primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap (X ^ 2 + X + 1) :=
    CFSG.StandardType.SevOmSmall.two_le_primaryMultiplicity hx hmem hq
  have hodd_block : Odd (Nat.card (Subgroup.center
      ↥(specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)))) :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.odd_card_center_specialBlock_phi hx hmem hm2
  have eZ : ↥(Subgroup.center ↥L) ≃*
      ↥(Subgroup.center ↥(specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1))) :=
    (Subgroup.equivMapOfInjective (Subgroup.center ↥L) eL.toMonoidHom eL.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_center_eq eL))
  have hcardZ : Nat.card ↥(Subgroup.center ↥L) =
      Nat.card ↥(Subgroup.center ↥(specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1))) :=
    Nat.card_congr eZ.toEquiv
  rw [hcardZ]
  exact hodd_block

private theorem ltromm_not_one_three {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[F] V))
    (hmem : (X ^ 2 + X + 1 : Polynomial F) ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap)
    {f : ℕ} (hf : Nat.card F = 2 ^ f) (hf1 : f = 1)
    (hm : primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap (X ^ 2 + X + 1) = 3)
    (hcard : Nat.card (specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)) =
      504 * Nat.card (Subgroup.center ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf
        (orthDerived Q)))) : False := by
  have hcard_phi := CFSG.HardMathSupport.Dickson.Bal207.OrthFix.card_specialBlock_phi
    hx hmem (f := f) hf
  rw [hm, hf1] at hcard_phi
  rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1)] at hcard_phi
  simp only [Finset.Icc_self, Finset.prod_singleton] at hcard_phi
  norm_num at hcard_phi
  have h216 : Nat.card (specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)) = 216 := by
    exact_mod_cast hcard_phi
  have hZ1 : 1 ≤ Nat.card (Subgroup.center
      ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))) := by
    haveI : Nonempty ↥(Subgroup.center
        ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))) :=
      Nonempty.intro ⟨1, Subgroup.one_mem _⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  rw [hcard] at h216
  omega

private theorem ltromm_selfDual_finrank {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[F] V)) {h : Polynomial F}
    [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ⧸
        Subgroup.center ↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))))
    (hself : h = reciprocalPolynomial h) :
    Module.finrank (AdjoinRoot h)
      (primaryComponent (x : V ≃ₗ[F] V).toLinearMap h) = 2 := by
  classical
  have hphi : h = X ^ 2 + X + 1 := ltromm_cyc3_of_selfDual hx hh hne hself
  have hmem : (X ^ 2 + X + 1 : Polynomial F) ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap :=
    hphi ▸ hh
  have hq' : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)) :=
    hphi ▸ hq
  have hlab' : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q)) ⧸
        Subgroup.center ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf
          (orthDerived Q))) :=
    hphi ▸ hlab
  obtain ⟨hcard, hodd⟩ := ltromm_card_block_eq hx hmem hq' hlab'
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card F = 2 ^ f := by
    letI : Fintype F := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card (K := F) 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  have hm2 : 2 ≤ primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap (X ^ 2 + X + 1) :=
    CFSG.StandardType.SevOmSmall.two_le_primaryMultiplicity hx hmem hq'
  have hfac := CFSG.HardMathSupport.Dickson.Bal207.OrthFix.factorization_two_card_specialBlock
    hx hmem (f := f) hf
  have hfac_block :
      (Nat.card (specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1))).factorization 2 = 3 := by
    have hZnz : Nat.card (Subgroup.center
        ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))) ≠ 0 := by
      haveI : Nonempty ↥(Subgroup.center
          ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q))) :=
        Nonempty.intro ⟨1, Subgroup.one_mem _⟩
      exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    have hZfac : (Nat.card (Subgroup.center
        ↥((specialBlock Q (x : V ≃ₗ[F] V) (X ^ 2 + X + 1)).subgroupOf
          (orthDerived Q)))).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (p := 2) (n := _) (by
        intro hdvd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd))
    rw [hcard, Nat.factorization_mul (by norm_num : (504 : ℕ) ≠ 0) hZnz, Finsupp.add_apply,
      hZfac, add_zero]
    exact ltromm_factorization_504
  have hexp : f * (primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap (X ^ 2 + X + 1) *
      (primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap (X ^ 2 + X + 1) - 1) / 2) = 3 := by
    rw [← hfac]
    exact hfac_block
  rcases ltromm_numerology hm2 hexp with ⟨hf3, hm_eq⟩ | ⟨hf1, hm_eq⟩
  · rw [show Module.finrank (AdjoinRoot h) (primaryComponent (x : V ≃ₗ[F] V).toLinearMap h) =
        primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap h from rfl, hphi]
    exact hm_eq
  · exact (ltromm_not_one_three hx hmem hf hf1 hm_eq hcard).elim

private theorem ltromm_label_selfDual_finrank {F : Type} [Field F] [Finite F] [CharP F 2]
    {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    {x : ↥(orthDerived Q)} (hx : OddOrderIsometry Q 3 (x : V ≃ₗ[F] V)) {h : Polynomial F}
    [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ⧸
        Subgroup.center ↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)))) :
    h = reciprocalPolynomial h ∧
      Module.finrank (AdjoinRoot h)
        (primaryComponent (x : V ≃ₗ[F] V).toLinearMap h) = 2 := by
  by_cases hself : h = reciprocalPolynomial h
  · exact ⟨hself, ltromm_selfDual_finrank hx hh hne hq hlab hself⟩
  · exact (ltromm_paired_false hx hh hne hq hlab hself).elim

private theorem ltromm_movingBlock_ggInnerOn {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 8 ≤ Module.finrank F V)
    {x : ↥(orthDerived Q)} (hx : orderOf x = 3) {h : Polynomial F}
    (hh : h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) ⧸
        Subgroup.center ↥((specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))))
    {y : ↥(orthDerived Q)} (hxy : x * y = y * x)
    (hyL : ∀ c ∈ (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q),
      MulAut.conj y c ∈ (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q)) :
    ∃ z ∈ (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q),
      ∀ j ∈ (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q),
        MulAut.conj y j = z * j * z⁻¹ := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (Nat.lt_of_lt_of_le (by norm_num) hV)
  have hx' : OddOrderIsometry Q 3 (x : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three (by
      rw [ringChar.eq (R := F) 2]; norm_num) hQ x hx
  have hyc : (y : V ≃ₗ[F] V) ∈ isometryCentralizer Q (x : V ≃ₗ[F] V) := by
    rw [isometryCentralizer, Subgroup.mem_inf]
    refine ⟨orthDerived_le_orthogonalGroup y.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hxy
    simpa using h.symm
  obtain ⟨hself, hdim⟩ := ltromm_label_selfDual_finrank hx' hh hne hq hlab
  have hq' : CFSG.Open.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  set L : Subgroup ↥(orthDerived Q) :=
    (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q) with hLdef
  set J : Subgroup (ProjOrthDerived Q) := componentImage Q (x : V ≃ₗ[F] V) h with hJdef
  have hLJ : L.map (piOrth Q) = J := rfl
  have hLmap : L.map (MulAut.conj y).toMonoidHom = L := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hyL c hc
    · intro c hc
      have himg : MulAut.conj y '' (L : Set ↥(orthDerived Q)) = L := by
        refine Set.Finite.eq_of_subset_of_card_le (Set.toFinite (L : Set ↥(orthDerived Q)))
          (fun z hz => ?_) ?_
        · obtain ⟨d, hd, rfl⟩ := hz
          exact hyL d hd
        · rw [Nat.card_image_of_injective (MulAut.conj y).injective]
      rw [Subgroup.mem_map]
      exact (Set.mem_image (MulAut.conj y) (L : Set ↥(orthDerived Q)) c).mp (himg.symm ▸ hc)
  have hJ : MulAut.conj (piOrth Q y) ∈ CFSG.GroupActions.subgroupStabAut J := by
    change J.map (MulAut.conj (piOrth Q y)).toMonoidHom = J
    rw [← hLJ, Subgroup.map_map]
    have hcomp : (MulAut.conj (piOrth Q y)).toMonoidHom.comp (piOrth Q) =
        (piOrth Q).comp (MulAut.conj y).toMonoidHom :=
      ltromm_conj_comp (piOrth Q) y
    rw [hcomp, ← Subgroup.map_map, hLmap, hLJ]
  obtain ⟨ℓ, f, hU, B, hBs, hBl, hperf, g, π', hsurj, hker, hconj⟩ :=
    exists_sesqSUConjData hx' (by decide) hh hne hself hq' y hyc J rfl hJ
  haveI : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AdjoinRoot h)).injective 2
  obtain rfl : ℓ = 2 := CharP.eq (AdjoinRoot h) hU.charP inferInstance
  obtain ⟨s, hsconj⟩ := exists_special_sesqSUConj_eq (ℓ := 2) (f := f) (E := AdjoinRoot h)
    (M := primaryComponent (x : V ≃ₗ[F] V).toLinearMap h) (hE := hU) (B := B)
    hBs hBl hdim g
  have hInnerJ : ∃ z ∈ J, ∀ j ∈ J, MulAut.conj (piOrth Q y) j = z * j * z⁻¹ := by
    refine ⟨π' s, (π' s).2, fun j hj => ?_⟩
    obtain ⟨t, ht⟩ := hsurj ⟨j, hj⟩
    have htj : j = (π' t : ProjOrthDerived Q) := (congrArg Subtype.val ht).symm
    rw [htj]
    rw [← CFSG.GroupActions.subgroupStabRestrict_apply
      (α := ⟨MulAut.conj (piOrth Q y), hJ⟩) (x := π' t)]
    have hsu : sesqSUConj
        ⟨↑s, CFSG.LocalAnalysis.ComponentInitial.sesqSpecialUnitaryGroup_le B s.2⟩ t =
        s * t * s⁻¹ := by
      apply Subtype.ext
      rw [sesqSUConj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have h1 := congrArg (fun z : ↥J => (z : ProjOrthDerived Q)) (hconj t)
    rw [h1, hsconj, hsu]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  obtain ⟨z, hzL, hz⟩ := ltromm_ggInnerOn_of_map (piOrth Q) (piOrth_injective hQ) hLJ
    (fun c => ltromm_conj_comp_apply (piOrth Q) y c) hInnerJ
  exact ⟨z, hzL, hz⟩

theorem orthMovingBlock_action {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 8 ≤ Module.finrank F V)
    {x : ↥(orthDerived Q)} (hx : orderOf x = 3) {h : Polynomial F}
    (hh : h ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap) (hne : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q (x : V ≃ₗ[F] V) h))
    {L : Subgroup ↥(orthDerived Q)}
    (hL : L = (specialBlock Q (x : V ≃ₗ[F] V) h).subgroupOf (orthDerived Q))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    {y : ↥(orthDerived Q)} (hxy : x * y = y * x) (hyL : ∀ c ∈ L, MulAut.conj y c ∈ L) :
    QuotientInner L (MulAut.conj y) := by
  subst hL
  exact ltromm_quotientInner_of_ggInnerOn
    (ltromm_movingBlock_ggInnerOn hQ hV hx hh hne hq hlab hxy hyL)

end S2MathAs3_1619Final

end
