module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie5ProofConjRep
public import CFSG.RankThree.PartOne.KGD.D4Frame

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
open scoped MatrixGroups

theorem exists_conj_HSL_of_pow_three {L : Type} [Field L] [IsAlgClosed L] {ζ : Lˣ}
    (hζ : orderOf ζ = 3) {A : SL2 L} (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) :
    ∃ (P : SL2 L) (m : ℕ), (m = 1 ∨ m = 2) ∧ A = P * HSL (ζ ^ m) * P⁻¹ := by
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    have := three_ne_zero_of_orderOf hζ
    exact_mod_cast this
  obtain ⟨P, D, hD, hPD⟩ := exists_conj_diag_two h3 _ hA3
  obtain ⟨μ, rfl⟩ := eq_HSL_of_diag hD
  have hμ3 : μ ^ 3 = 1 := by
    have h1 : HSL μ ^ 3 = 1 := by
      have h2 : P * HSL μ ^ 3 * P⁻¹ = 1 := by
        rw [← conj_pow, ← hPD, hA3]
      calc HSL μ ^ 3 = P⁻¹ * (P * HSL μ ^ 3 * P⁻¹) * P := by group
        _ = 1 := by rw [h2]; group
    have h4 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_pow, coe_HSL, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h4
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h5 : (!![(μ : L), 0; 0, ((μ⁻¹ : Lˣ) : L)] ^ 3) 0 0 = (μ : L) ^ 3 := by
      simp [pow_succ]
    rw [← h5]
    exact h4
  obtain ⟨m, hm3, rfl⟩ := eq_pow_of_pow_three hζ hμ3
  refine ⟨P, m, ?_, hPD⟩
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with h0 | h1 | h2
  · exfalso
    apply hA1
    rw [hPD, h0, pow_zero]
    have hH1 : HSL (1 : Lˣ) = 1 := SL2_ext (by simp [coe_HSL]) (by simp [coe_HSL])
      (by simp [coe_HSL]) (by simp [coe_HSL])
    rw [hH1]
    group
  · exact Or.inl h1
  · exact Or.inr h2

variable
  {L : Type} [Field L]

variable (L) in
@[expose] noncomputable def outerTriple : SL2 L × SL2 L × SL2 L →* ModGL TwistTag.D4.tag L :=
  MonoidHom.mk' (fun A => rankOneHom TwistTag.D4 L n0 A.1 * rankOneHom TwistTag.D4 L n1 A.2.1 *
    rankOneHom TwistTag.D4 L n3 A.2.2) fun A B => by
    have h0 : n0 ∈ TwistTag.D4.orbit KS11Lie4Proof.d4Outer := by decide
    have h1 : n1 ∈ TwistTag.D4.orbit KS11Lie4Proof.d4Outer := by decide
    have h3 : n3 ∈ TwistTag.D4.orbit KS11Lie4Proof.d4Outer := by decide
    have c01 := commute_rankOneHom (K := L) h0 h1 (by decide) B.1 A.2.1
    have c03 := commute_rankOneHom (K := L) h0 h3 (by decide) B.1 A.2.2
    have c13 := commute_rankOneHom (K := L) h1 h3 (by decide) B.2.1 A.2.2
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    rw [c01.mul_mul_mul_comm, (c03.mul_left c13).mul_mul_mul_comm]

theorem outerTriple_apply (A : SL2 L × SL2 L × SL2 L) : outerTriple L A =
    rankOneHom TwistTag.D4 L n0 A.1 * rankOneHom TwistTag.D4 L n1 A.2.1 *
      rankOneHom TwistTag.D4 L n3 A.2.2 := rfl

theorem outerTriple_mem_adjointGroup (A : SL2 L × SL2 L × SL2 L) :
    outerTriple L A ∈ adjointGroup TwistTag.D4.tag L :=
  mul_mem (mul_mem (rankOneHom_mem_adjointGroup_D4 _ _) (rankOneHom_mem_adjointGroup_D4 _ _))
    (rankOneHom_mem_adjointGroup_D4 _ _)

@[expose] def outerExp (m₀ m₁ m₃ : ℕ) : Exp3 := fun j =>
  (m₀ : ZMod 3) * ((TwistTag.D4.tag.cartan n0 j : ℤ) : ZMod 3) +
    (m₁ : ZMod 3) * ((TwistTag.D4.tag.cartan n1 j : ℤ) : ZMod 3) +
      (m₃ : ZMod 3) * ((TwistTag.D4.tag.cartan n3 j : ℤ) : ZMod 3)

theorem outerTriple_HSL {ζ : Lˣ} (hζ : ζ ^ 3 = 1) (m₀ m₁ m₃ : ℕ) :
    outerTriple L (HSL (ζ ^ m₀), HSL (ζ ^ m₁), HSL (ζ ^ m₃)) =
      rootDiagUnit TwistTag.D4.tag (tup ζ (outerExp m₀ m₁ m₃)) := by
  rw [outerTriple_apply, rankOneHom_HSL, rankOneHom_HSL, rankOneHom_HSL,
    LieType.Chevalley.torusElt_eq_rootDiagUnit, LieType.Chevalley.torusElt_eq_rootDiagUnit,
    LieType.Chevalley.torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, tup, outerExp]
  rw [pow_zpow_eq_tup hζ, pow_zpow_eq_tup hζ, pow_zpow_eq_tup hζ, pow_val_add hζ,
    pow_val_add hζ]

theorem exists_word_outerExp {m₀ m₁ m₃ : ℕ} (h₀ : m₀ = 1 ∨ m₀ = 2) (h₁ : m₁ = 1 ∨ m₁ = 2)
    (h₃ : m₃ = 1 ∨ m₃ = 2) :
    ∃ ω : List (Fin TwistTag.D4.tag.rank), wordExp ω (outerExp m₀ m₁ m₃) = gA := by
  rcases h₀ with rfl | rfl <;> rcases h₁ with rfl | rfl <;> rcases h₃ with rfl | rfl
  · exact ⟨[1, 2, 3, 2, 1], by decide⟩
  · exact ⟨[3, 1, 2, 1], by decide⟩
  · exact ⟨[1, 2, 3, 2], by decide⟩
  · exact ⟨[3, 1, 2], by decide⟩
  · exact ⟨[1, 2, 3, 2, 1, 0], by decide⟩
  · exact ⟨[3, 1, 2, 1, 0], by decide⟩
  · exact ⟨[1, 2, 3, 2, 0], by decide⟩
  · exact ⟨[3, 1, 2, 0], by decide⟩

theorem triEmb_orbitRankOneHom_outer {K : Type} [Field K] [Algebra K L] (σ : K ≃+* K)
    (B : SL2 (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer)) :
    baseChangeGL (algebraMap K L)
        (orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer B) =
      outerTriple L
        (Matrix.SpecialLinearGroup.map ((algebraMap K L).comp
          ((σ.toRingHom ^ 0).comp (orbitField TwistTag.D4 K σ.toRingHom
            KS11Lie4Proof.d4Outer).subtype)) B,
        Matrix.SpecialLinearGroup.map ((algebraMap K L).comp
          ((σ.toRingHom ^ 1).comp (orbitField TwistTag.D4 K σ.toRingHom
            KS11Lie4Proof.d4Outer).subtype)) B,
        Matrix.SpecialLinearGroup.map ((algebraMap K L).comp
          ((σ.toRingHom ^ 2).comp (orbitField TwistTag.D4 K σ.toRingHom
            KS11Lie4Proof.d4Outer).subtype)) B) := by
  rw [orbitRankOneHom_apply]
  have hc : (TwistTag.D4.orbit KS11Lie4Proof.d4Outer).card = 3 := by decide
  have hm : TwistTag.D4.orbitMin KS11Lie4Proof.d4Outer = n0 := by decide
  have hp1 : (TwistTag.D4.perm ^ 1) n0 = n1 := by decide
  have hp2 : (TwistTag.D4.perm ^ 2) n0 = n3 := by decide
  have hp0 : (TwistTag.D4.perm ^ 0) n0 = n0 := rfl
  rw [hc, hm, show List.range 3 = [0, 1, 2] by rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hp0, hp1, hp2,
    map_mul, baseChangeGL_rankOneHom, outerTriple_apply]
  rw [← mul_assoc]
  rfl

theorem map_pow_three_ne_one {F E : Type} [Field F] [Field E] (φ : F →+* E) {B : SL2 F}
    (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) :
    Matrix.SpecialLinearGroup.map φ B ^ 3 = 1 ∧ Matrix.SpecialLinearGroup.map φ B ≠ 1 := by
  refine ⟨by rw [← map_pow, hB3, map_one], fun h => hB1 ?_⟩
  have h2 : ∀ i j, φ ((B : Matrix (Fin 2) (Fin 2) F) i j) =
      φ ((1 : Matrix (Fin 2) (Fin 2) F) i j) := by
    intro i j
    have := congrArg (fun X : SL2 E => (X : Matrix (Fin 2) (Fin 2) E) i j) h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.SpecialLinearGroup.coe_one] at this
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact Subtype.ext (Matrix.ext fun i j => φ.injective (h2 i j))

theorem exists_conj_dA_of_mem_short [IsAlgClosed L] {K : Type} [Field K] [Algebra K L]
    {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) {ζ : Lˣ} (hζ : orderOf ζ = 3)
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ x ∈ adjointGroup TwistTag.D4.tag L,
      triEmb K σ L z = x * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * x⁻¹ := by
  have hζ3 := pow_three_of_orderOf hζ
  obtain ⟨B, hB'⟩ := hzS
  have hB : orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer B =
      (z : ModGL TwistTag.D4.tag K) := hB'
  have hinj := orbitRankOneHom_injective_D4 hσ3 KS11Lie4Proof.d4Outer
  have hB3 : B ^ 3 = 1 := hinj (by
    rw [map_pow, hB, map_one, ← Subgroup.coe_pow, hz3, Subgroup.coe_one])
  have hB1 : B ≠ 1 := fun h => hz1 (Subtype.ext (by rw [Subgroup.coe_one, ← hB, h, map_one]))
  set φ₀ := (algebraMap K L).comp ((σ.toRingHom ^ 0).comp
    (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).subtype) with hφ₀
  set φ₁ := (algebraMap K L).comp ((σ.toRingHom ^ 1).comp
    (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).subtype) with hφ₁
  set φ₂ := (algebraMap K L).comp ((σ.toRingHom ^ 2).comp
    (orbitField TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer).subtype) with hφ₂
  obtain ⟨h₀3, h₀1⟩ := map_pow_three_ne_one φ₀ hB3 hB1
  obtain ⟨h₁3, h₁1⟩ := map_pow_three_ne_one φ₁ hB3 hB1
  obtain ⟨h₂3, h₂1⟩ := map_pow_three_ne_one φ₂ hB3 hB1
  obtain ⟨P₀, m₀, hm₀, h₀⟩ := exists_conj_HSL_of_pow_three hζ h₀3 h₀1
  obtain ⟨P₁, m₁, hm₁, h₁⟩ := exists_conj_HSL_of_pow_three hζ h₁3 h₁1
  obtain ⟨P₃, m₃, hm₃, h₃⟩ := exists_conj_HSL_of_pow_three hζ h₂3 h₂1
  obtain ⟨ω, hω⟩ := exists_word_outerExp hm₀ hm₁ hm₃
  refine ⟨outerTriple L (P₀, P₁, P₃) * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
    ((coxeterSystem TwistTag.D4.tag).wordProd ω))⁻¹,
    mul_mem (outerTriple_mem_adjointGroup _) (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_⟩
  have htri : (Matrix.SpecialLinearGroup.map φ₀ B, Matrix.SpecialLinearGroup.map φ₁ B,
      Matrix.SpecialLinearGroup.map φ₂ B) =
        (P₀, P₁, P₃) * (HSL (ζ ^ m₀), HSL (ζ ^ m₁), HSL (ζ ^ m₃)) * (P₀, P₁, P₃)⁻¹ := by
    simp only [Prod.mk_mul_mk, Prod.inv_mk]
    rw [← h₀, ← h₁, ← h₃]
  rw [triEmb_apply, ← hB, triEmb_orbitRankOneHom_outer, htri, map_mul, map_mul, map_inv,
    outerTriple_HSL hζ3, rootDiagUnit_tup_eq_conj hζ3 ω, hω]
  group

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
