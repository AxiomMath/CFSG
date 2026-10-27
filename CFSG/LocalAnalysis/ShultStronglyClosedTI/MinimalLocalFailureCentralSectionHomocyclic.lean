module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralSectionSquare
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_1

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem card_multiplicative_fin_zmod (r n : ℕ) :
    Nat.card (Multiplicative (Fin r → ZMod n)) = n ^ r := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

namespace FinalHyps

variable {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t : G}

theorem section_homocyclic
    (d : FinalHyps H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    ∀ e : ℕ, Nat.card (minimalLocalFailurePairActionPointHull H z) = 2 ^ e →
      Nonempty (A ≃* Multiplicative (Fin e → ZMod 4)) := by
  intro e hQe
  obtain ⟨hAH, hAN, hQA, hAM, hAQ, hA2⟩ := d.section_basic hA
  have hQltA := hA.2.2.1
  have hsq := hA.2.2.2.2.2.2
  obtain ⟨hQH, hQn, hQ, hQ4, -, hBH, hXB, -, hXcyc, -⟩ := d.point_data
  obtain ⟨-, hab⟩ := d.section_square_hom hA
  have hinv := d.section_involutions hA
  have hcardA := (d.section_index hA).2
  have hXN : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤
      Subgroup.normalizer (A : Set G) := (hXB.trans hBH).trans hAN
  let φ : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) →* MulAut A :=
    A.normalizerMonoidHom.comp (Subgroup.inclusion hXN)
  let : MulDistribMulAction (rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) A :=
    MulDistribMulAction.compHom A φ
  have hinvQ : ∀ a : A, a ∈ involutions A →
      (a : G) ∈ (minimalLocalFailurePairActionPointHull H z : Set G) \ {1} := by
    intro a ha
    rw [← hinv]
    refine ⟨a.2, ?_⟩
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime_iff.mpr ⟨ha.2, ha.1⟩
  have htrans : ∀ a : A, a ∈ involutions A → ∀ b : A, b ∈ involutions A →
      ∃ k : rightInvolutionCommutatorSubgroup t (pairOddCore H beta), b = k • a := by
    intro a ha b hb
    obtain ⟨haQ, ha1⟩ := hinvQ a ha
    obtain ⟨hbQ, hb1⟩ := hinvQ b hb
    obtain ⟨k, hk, -⟩ := d.X_regular (a : G) haQ ha1 (b : G) hbQ hb1
    refine ⟨k, Subtype.ext ?_⟩
    change (b : G) = ((φ k a : A) : G)
    exact hk.symm.trans
      (Subgroup.normalizerMonoidHom_apply_apply_coe A (Subgroup.inclusion hXN k) a).symm
  obtain ⟨f', r, hf', ⟨f⟩⟩ :=
    External.Higman.homocyclic_of_abelian_twoGroup_of_involutions_transitive hA2 hab htrans
  have h4 : ∀ v : Fin r → ZMod (2 ^ f'), 4 • v = 0 := by
    intro v
    have ha := (f.symm (Multiplicative.ofAdd v)).2
    have ha4 : ((f.symm (Multiplicative.ofAdd v)) ^ 4 : A) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      exact hQ.2 _ (hsq _ ha)
    have h := congrArg f ha4
    rw [map_pow, MulEquiv.apply_symm_apply, map_one, ← ofAdd_nsmul] at h
    exact h
  obtain ⟨a₀, ha₀A, ha₀Q⟩ := IsConcreteLE.exists_of_lt hQltA
  have ha₀sq : a₀ ^ 2 ≠ 1 := by
    intro h2
    have ha₀1 : a₀ ≠ 1 := fun h1 => ha₀Q (h1 ▸ (minimalLocalFailurePairActionPointHull H z).one_mem)
    have : a₀ ∈ {a : G | a ∈ A ∧ orderOf a = 2} := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact ⟨ha₀A, orderOf_eq_prime_iff.mpr ⟨h2, ha₀1⟩⟩
    rw [hinv] at this
    exact ha₀Q this.1
  have hcardf : Nat.card A = (2 ^ f') ^ r := by
    rw [Nat.card_congr f.toEquiv, card_multiplicative_fin_zmod]
  have hr : 0 < r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero, hcardA] at hcardf
    have : 4 ^ 2 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 :=
      Nat.pow_le_pow_left hQ4 2
    omega
  have hf'le : f' ≤ 2 := by
    have h := congrFun (h4 (Pi.single ⟨0, hr⟩ 1)) ⟨0, hr⟩
    simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, Pi.zero_apply] at h
    have h' : ((4 : ℕ) : ZMod (2 ^ f')) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff, show (4 : ℕ) = 2 ^ 2 from rfl] at h'
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h'
  have hf'ge : 2 ≤ f' := by
    by_contra hlt
    have hf1 : f' = 1 := by omega
    apply ha₀sq
    have h2 : ∀ v : Fin r → ZMod (2 ^ f'), 2 • v = 0 := by
      intro v
      funext i
      rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
      have : ((2 : ℕ) : ZMod (2 ^ f')) = 0 := by
        rw [ZMod.natCast_eq_zero_iff, hf1, pow_one]
      rw [this, zero_mul]
    have h := congrArg Subtype.val (show (⟨a₀, ha₀A⟩ ^ 2 : A) = 1 from by
      apply f.injective
      rw [map_pow, map_one]
      have h0 := h2 (Multiplicative.toAdd (f ⟨a₀, ha₀A⟩))
      calc f ⟨a₀, ha₀A⟩ ^ 2 = Multiplicative.ofAdd (2 • Multiplicative.toAdd (f ⟨a₀, ha₀A⟩)) := by
            rw [ofAdd_nsmul, ofAdd_toAdd]
        _ = 1 := by rw [h0, ofAdd_zero])
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using h
  have hf'2 : f' = 2 := le_antisymm hf'le hf'ge
  subst hf'2
  have hre : r = e := by
    rw [hcardA, hQe] at hcardf
    have h : 4 ^ e = 4 ^ r := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul, mul_comm 2 e]
      calc 2 ^ (e * 2) = (2 ^ e) ^ 2 := by rw [pow_mul]
        _ = (2 ^ 2) ^ r := hcardf
        _ = 2 ^ (2 * r) := by rw [← pow_mul]
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 4) h).symm
  subst hre
  exact ⟨f⟩

end FinalHyps

end CFSG.ShultStronglyClosedTI.FinalChain
