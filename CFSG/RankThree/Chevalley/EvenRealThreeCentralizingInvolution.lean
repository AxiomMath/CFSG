module

public import CFSG.RankThree.Chevalley.EvenTrialityElementaryNine
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
public import CFSG.Blueprint.Catalog
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.RankThree.Chevalley.EvenFourCommutingSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

section Matrices

variable (F : Type*) [Field F] [CharP F 2]

@[expose] def swapSL : SL2 F :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

theorem swapSL_mul_self : swapSL F * swapSL F = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [swapSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapSL_mul_cubeSL_mul_swapSL :
    swapSL F * cubeSL F * swapSL F = cubeSL F * cubeSL F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [swapSL, cubeSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [one_add_one_eq_two, h2]

theorem swapSL_conj_cubeSL : swapSL F * cubeSL F * (swapSL F)⁻¹ = (cubeSL F)⁻¹ := by
  have hW : (swapSL F)⁻¹ = swapSL F := inv_eq_of_mul_eq_one_right (swapSL_mul_self F)
  have hM : (cubeSL F)⁻¹ = cubeSL F * cubeSL F :=
    inv_eq_of_mul_eq_one_right ((pow_three (cubeSL F)).symm.trans (cubeSL_pow_three F))
  rw [hW, hM, swapSL_mul_cubeSL_mul_swapSL]

theorem uSL_one_mul_self : (uSL (1 : F)) * uSL 1 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [uSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [one_add_one_eq_two, h2]

theorem orderOf_uSL_one : orderOf (uSL (1 : F)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [sq, uSL_one_mul_self]) fun h => ?_
  have := congrArg (fun C : SL2 F => (C : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [uSL] at this

end Matrices

@[expose] def RealThreeTriple {G : Type*} [Group G] (x z b : G) : Prop :=
  orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹

theorem exists_realThreeTriple_of_SL2 {F : Type*} [Field F] [CharP F 2] {G : Type*} [Group G]
    (ι : SL2 F →* G) (hι : Function.Injective ι) {z : G} (hz : orderOf z = 2)
    (hc : ∀ A, ι A * z = z * ι A) : ∃ x z' b : G, RealThreeTriple x z' b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨ι (cubeSL F), z, ι (swapSL F), ?_, hz, hc _, ?_⟩
  · rw [orderOf_injective ι hι, orderOf_eq_prime (cubeSL_pow_three F) (cubeSL_ne_one F)]
  · calc ι (swapSL F) * ι (cubeSL F) * (ι (swapSL F))⁻¹
        = ι (swapSL F * cubeSL F * (swapSL F)⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = (ι (cubeSL F))⁻¹ := by rw [swapSL_conj_cubeSL, map_inv]

theorem exists_realThreeTriple_of_injective {G S : Type*} [Group G] [Group S] (φ : G →* S)
    (hφ : Function.Injective φ) (h : ∃ x z b : G, RealThreeTriple x z b) :
    ∃ x z b : S, RealThreeTriple x z b := by
  obtain ⟨x, z, b, hx, hz, hxz, hb⟩ := h
  refine ⟨φ x, φ z, φ b, by rw [orderOf_injective φ hφ, hx], by rw [orderOf_injective φ hφ, hz],
    by rw [← map_mul, ← map_mul, hxz], ?_⟩
  calc φ b * φ x * (φ b)⁻¹ = φ (b * x * b⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = (φ x)⁻¹ := by rw [hb, map_inv]

theorem charP_two_of_natCard {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, h])

theorem exists_mulEquiv_adjointGroup_of_untwisted {S : Type} [Group S] {τ : Tag} {q : ℕ}
    (h : UntwistedChevalleyModel S τ q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
      Nonempty (adjointGroup τ K ≃* S) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨((QuotientGroup.quotientMulEquivOfEq
    center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot).symm.trans e.symm⟩⟩

theorem nonempty_derivedCentralQuotient_mulEquiv_of_eq {M : Type} [Group M] {H C : Subgroup M}
    (hHC : ⁅H, H⁆ = C) (hZ : Subgroup.center C = ⊥) :
    Nonempty (DerivedCentralQuotient H ≃* C) := by
  subst hHC
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

theorem exists_mulEquiv_graphFixedRootGroup_of_twisted {S : Type} [Group S] {t : TwistTag} {f : ℕ}
    (hf : 1 ≤ f) (h : TwistedChevalleyModel S t (2 ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K →+* K), Nat.card K = (2 ^ f) ^ t.order ∧
      (∀ c, σ c = c ^ (2 ^ f)) ∧ Nonempty (graphFixedRootGroup t K σ ≃* S) := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hperf := (finite_fixed_root_group_perfect t Nat.prime_two hf K hK σ hσ).2.2.1
  have hZ := center_graphFixedRootGroup_eq_bot (t := t) (K := K)
    (Finite.surjective_of_injective σ.injective)
  obtain ⟨E⟩ := nonempty_derivedCentralQuotient_mulEquiv_of_eq hperf hZ
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσ, ⟨E.symm.trans e.symm⟩⟩

theorem exists_realThreeTriple_of_untwisted {S : Type} [Group S] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (h : UntwistedChevalleyModel S τ (2 ^ f)) : ∃ x z b : S, RealThreeTriple x z b := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted h
  have : CharP K 2 := charP_two_of_natCard hK
  obtain ⟨ι, hinj, hcomm⟩ := even_higher_ordinary_exceptional_four_commuting_faithful_SL2 K τ hτ
  refine exists_realThreeTriple_of_injective e.toMonoidHom e.injective
    (exists_realThreeTriple_of_SL2 (ι 0) (hinj 0) (z := ι 1 (uSL 1)) ?_ fun A =>
      hcomm 0 1 (by decide) A (uSL 1))
  rw [orderOf_injective _ (hinj 1), orderOf_uSL_one]

theorem exists_realThreeTriple_of_G2 {S : Type} [Group S] {f : ℕ}
    (h : UntwistedChevalleyModel S .G2 (2 ^ f)) : ∃ x z b : S, RealThreeTriple x z b := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted h
  have : CharP K 2 := charP_two_of_natCard hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, ⟨ρ, -, -, hrange, hinj⟩, -, -, -, hcommL⟩ :=
    ComponentClassification.UnbalancedCatalog.even_G2_highest_long_root_centralizer K
  have hmem : ∀ A, ρ A ∈ ComponentClassification.UnbalancedCatalog.g2RankOne K
      ComponentClassification.UnbalancedCatalog.g2ir := fun A => by
    rw [← hrange]
    exact ⟨A, rfl⟩
  let ι : SL2 K →* adjointGroup .G2 K := ρ.codRestrict _ fun A =>
    ComponentClassification.UnbalancedCatalog.g2RankOne_le_adjointGroup _ (hmem A)
  let z : adjointGroup .G2 K :=
    ⟨pinnedX .G2 K ComponentClassification.UnbalancedCatalog.g2c 1, pinnedX_mem_adjointGroup _ _⟩
  have hz : orderOf z = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h1 => ?_
    · rw [Subgroup.coe_pow, sq, Subgroup.coe_one, ← pinnedX_add, one_add_one_eq_two,
        CharTwo.two_eq_zero, pinnedX_zero]
    · have h1' : pinnedX .G2 K ComponentClassification.UnbalancedCatalog.g2c 1 =
          pinnedX .G2 K ComponentClassification.UnbalancedCatalog.g2c 0 := by
        rw [pinnedX_zero]
        exact congrArg Subtype.val h1
      exact one_ne_zero (pinnedX_injective _ _ _ h1')
  refine exists_realThreeTriple_of_injective e.toMonoidHom e.injective
    (exists_realThreeTriple_of_SL2 ι (fun A B hAB => hinj (congrArg Subtype.val hAB)) hz
      fun A => Subtype.ext (hcommL (ρ A) (hmem A) 1))

theorem exists_realThreeTriple_of_twistedE6 {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel S .E6 (2 ^ f)) : ∃ x z b : S, RealThreeTriple x z b := by
  obtain ⟨K, _, _, σ, hK, -, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted hf h
  have : CharP K 2 := charP_two_of_natCard (by rw [hK, ← pow_mul])
  obtain ⟨ι, hinj, hcomm⟩ := even_twisted_E6_four_commuting_faithful_fixed_SL2 K σ
  refine exists_realThreeTriple_of_injective e.toMonoidHom e.injective
    (exists_realThreeTriple_of_SL2 (ι 0) (hinj 0) (z := ι 1 (uSL 1)) ?_ fun A =>
      hcomm 0 1 (by decide) A (uSL 1))
  rw [orderOf_injective _ (hinj 1), orderOf_uSL_one]

theorem exists_realThreeTriple_of_trialityD4 {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel S .D4 (2 ^ f)) : ∃ x z b : S, RealThreeTriple x z b := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted hf h
  have : CharP K 2 := charP_two_of_natCard (by rw [hK, ← pow_mul])
  have h3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    have := Fintype.ofFinite K
    have hord : TwistTag.D4.order = 3 := rfl
    have hc : Fintype.card K = 2 ^ f * (2 ^ f * 2 ^ f) := by
      rw [← Nat.card_eq_fintype_card, hK, hord]
      ring
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, ← hc, FiniteField.pow_card]
  obtain ⟨⟨Ψ, hΨ⟩, -⟩ := even_triality_commuting_rank_one_product_and_elementary_nine K σ h3
  let ι₁ : SL2 K →* graphFixedRootGroup .D4 K σ := Ψ.comp (MonoidHom.inl _ _)
  let ι₂ : SL2 (trialityFixedField K σ) →* graphFixedRootGroup .D4 K σ :=
    Ψ.comp (MonoidHom.inr _ _)
  have h₁ : Function.Injective ι₁ := fun A B hAB =>
    congrArg Prod.fst (hΨ (show Ψ (A, 1) = Ψ (B, 1) from hAB))
  have h₂ : Function.Injective ι₂ := fun A B hAB =>
    congrArg Prod.snd (hΨ (show Ψ (1, A) = Ψ (1, B) from hAB))
  refine exists_realThreeTriple_of_injective e.toMonoidHom e.injective
    (exists_realThreeTriple_of_SL2 ι₁ h₁ (z := ι₂ (uSL 1)) ?_ fun A => ?_)
  · rw [orderOf_injective _ h₂, orderOf_uSL_one]
  · change Ψ (A, 1) * Ψ (1, uSL 1) = Ψ (1, uSL 1) * Ψ (A, 1)
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_one, one_mul, one_mul,
      mul_one]

theorem even_Chevalley_exceptional_real_three_element_centralizing_involution (S : Type)
    [Group S] [Finite S] (t : StatedLieTag) (f : ℕ) (h : ChevalleyExceptionalModel S t 2 f) :
    ∃ x z b : S, orderOf x = 3 ∧ orderOf z = 2 ∧ x * z = z * x ∧ b * x * b⁻¹ = x⁻¹ ∧
      x ∈ Subgroup.centralizer (Subgroup.zpowers z : Set S) ∧
      Subgroup.centralizer (Subgroup.zpowers z : Set S) ≤
        Subgroup.normalizer (Subgroup.zpowers z : Set S) := by
  suffices hmain : ∃ x z b : S, RealThreeTriple x z b by
    obtain ⟨x, z, b, hx, hz, hxz, hb⟩ := hmain
    refine ⟨x, z, b, hx, hz, hxz, hb, Subgroup.mem_centralizer_iff.2 fun y hy => ?_,
      Subgroup.centralizer_le_normalizer _⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute z x from hxz.symm) k).eq
  obtain ⟨⟨-, hf, -⟩, hm⟩ := h
  cases t
  case G2 => exact exists_realThreeTriple_of_G2 hm
  case F4 => exact exists_realThreeTriple_of_untwisted (Or.inl rfl) hm
  case E6 => exact exists_realThreeTriple_of_untwisted (Or.inr (Or.inl rfl)) hm
  case E7 => exact exists_realThreeTriple_of_untwisted (Or.inr (Or.inr (Or.inl rfl))) hm
  case E8 => exact exists_realThreeTriple_of_untwisted (Or.inr (Or.inr (Or.inr rfl))) hm
  case twistedE6 => exact exists_realThreeTriple_of_twistedE6 hf hm
  case trialityD4 => exact exists_realThreeTriple_of_trialityD4 hf hm
  all_goals exact (hm : False).elim

end CFSG.RankThree.Chevalley
