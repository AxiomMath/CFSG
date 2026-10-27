module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofE9
import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LieType.Chevalley (fixSubfield)
open Item8KFactsProof

namespace Item8KFactsProof

theorem exists_pair_autFix_fieldAut {K : Type*} [Field K] (σ : K ≃+* K) {ω : Kˣ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hσω : σ (ω : K) = ω) :
    ∃ u v : Sec4.autFix (fieldAut 3 K σ), u ≠ 1 ∧ u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v = v * u ∧
      v ∉ Subgroup.zpowers u := by
  set D : Matrix.SpecialLinearGroup (Fin 3) K := dHom (ω, 1) with hD
  have hDfix : Matrix.SpecialLinearGroup.map σ.toRingHom D = D := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hD, coe_dHom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hσω, map_inv₀]
  have hrfix : Matrix.SpecialLinearGroup.map σ.toRingHom (rSL : Matrix.SpecialLinearGroup
      (Fin 3) K) = rSL := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_rSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hafix : fieldAut 3 K σ (proj 3 K D) = proj 3 K D := by rw [fieldAut_proj, hDfix]
  have hbfix : fieldAut 3 K σ (proj 3 K rSL) = proj 3 K rSL := by rw [fieldAut_proj, hrfix]
  have hscal : dHom (ω, ω) ∈ scalars 3 K := by
    refine mem_scalars.mpr ⟨ω, hω3, ?_⟩
    rw [coe_dHom]
    have hinv : (((ω * ω)⁻¹ : Kˣ) : K) = ω := by
      have h : ω * ω * ω = 1 := by rw [← pow_three']; exact hω3
      rw [inv_eq_of_mul_eq_one_right h]
    rw [hinv, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hD3 : D ^ 3 = 1 := by
    rw [hD, ← map_pow]
    have : ((ω, 1) : Kˣ × Kˣ) ^ 3 = 1 := by ext <;> simp [hω3]
    rw [this, map_one]
  have hrot : rot ((ω, 1) : Kˣ × Kˣ) = (ω, ω) * (ω, 1) := by
    have h2 : ω⁻¹ = ω * ω := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_three', hω3]
    ext <;> simp [rot, h2]
  have hcomm : proj 3 K D * proj 3 K rSL = proj 3 K rSL * proj 3 K D := by
    have h1 : (rSL : Matrix.SpecialLinearGroup (Fin 3) K) * dHom (ω, 1) =
        dHom (ω, ω) * (dHom (ω, 1) * rSL) := by
      rw [rSL_mul_dHom, hrot, map_mul, mul_assoc]
    have h2 : proj 3 K (rSL * D) = proj 3 K (D * rSL) := by
      rw [hD, h1, map_mul, proj_eq_one_iff.mpr hscal, one_mul]
    rw [← map_mul, ← map_mul, h2]
  have hD1 : proj 3 K D ≠ 1 := by
    intro h
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
    rw [hD, coe_dHom] at hc
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    simp [Matrix.diagonal, Matrix.scalar_apply] at h0 h1
    exact hω1 (Units.ext (h0.trans h1.symm))
  have hr3 : (proj 3 K rSL) ^ 3 = 1 := by rw [← map_pow, rSL_pow_three, map_one]
  have hDpow : ∀ j : ℤ, ∃ p : Kˣ × Kˣ, D ^ j = dHom p := by
    intro j
    exact ⟨((ω, 1) : Kˣ × Kˣ) ^ j, by rw [hD, map_zpow]⟩
  have hrnot : proj 3 K rSL ∉ Subgroup.zpowers (proj 3 K D) := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    obtain ⟨p, hp⟩ := hDpow j
    rw [← map_zpow, hp, proj_eq_proj_iff] at hj
    obtain ⟨c, -, hc⟩ := mem_scalars.mp hj
    have h10 := congrFun (congrFun hc 1) 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv] at h10
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three, coe_dHom, coe_rSL,
      Matrix.scalar_apply, Matrix.diagonal] at h10
  refine ⟨⟨proj 3 K D, hafix⟩, ⟨proj 3 K rSL, hbfix⟩, fun h => hD1 (congrArg Subtype.val h),
    Subtype.ext ?_, Subtype.ext ?_, Subtype.ext hcomm, fun h => hrnot ?_⟩
  · rw [Subgroup.coe_pow]
    show (proj 3 K D) ^ 3 = 1
    rw [← map_pow, hD3, map_one]
  · rw [Subgroup.coe_pow]
    exact hr3
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    have := congrArg Subtype.val hj
    rw [Subgroup.coe_zpow] at this
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, this⟩

end Item8KFactsProof


@[expose] def KF82PSL3EvenModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (n : ℕ) (k : KFacts.AutKind),
    Even n → 2 ≤ n →
    Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) →
    KFacts.InducesStdKind L x k →
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        KFacts.InducesKindPSL 3 K L x k

theorem kF82LThreeWrong_of (hM : KF82PSL3EvenModel) : KF82LThreeWrong := by
  intro G _ _ L x n hn hn1 hiso hx3 hk
  have hn2 : 2 ≤ n := by
    obtain ⟨m, rfl⟩ := hn
    omega
  rcases hk with hk | hk
  · obtain ⟨K, _, _, hK, e, hxN, hkind⟩ := hM G L x n .field hn hn2 hiso hk
    set τ := KFacts.inducedAutHom L e ⟨x, hxN⟩ with hτ
    have hτ3 : τ ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one L e hxN hx3
    have hsep := KFacts.stdPinnedPSL_separated (K := K) (n := 3) le_rfl
    have hD := hsep.not_mem_inndiag_of_hasKind hkind (by decide) (by decide)
    obtain ⟨σ, hσ, H, hτH⟩ := KFacts.linear_order_three_field_descent le_rfl τ hτ3 hD
    obtain ⟨hdvd, hcardk⟩ :=
      CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK σ
    rw [hσ] at hdvd hcardk
    obtain ⟨m, rfl⟩ := hdvd
    rw [Nat.mul_div_cancel_left _ (by norm_num)] at hcardk
    have hm : Even m := by
      rcases Nat.even_or_odd m with hm | hm
      · exact hm
      · exact absurd hn (Nat.not_even_iff_odd.mpr (Odd.mul (by decide) hm))
    have : Finite (fixSubfield σ) := Subtype.finite
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    classical
    have h3 : 3 ∣ Nat.card (fixSubfield σ)ˣ := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcardk]
      obtain ⟨j, rfl⟩ := hm
      have : (2 : ℕ) ^ (j + j) % 3 = 1 := by
        rw [← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' 3 h3
    set ω : Kˣ := Units.map (fixSubfield σ).subtype.toMonoidHom ω₀ with hω
    have hω3 : ω ^ 3 = 1 := by
      rw [hω, ← map_pow, ← hω₀, pow_orderOf_eq_one, map_one]
    have hω1 : ω ≠ 1 := by
      intro h
      have h1 : ω₀ = 1 := Units.ext (Subtype.ext (by
        have := congrArg Units.val h
        simpa [hω] using this))
      rw [h1, orderOf_one] at hω₀
      omega
    have hσω : σ (ω : K) = ω := (ω₀ : fixSubfield σ).2
    obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := exists_pair_autFix_fieldAut σ hω3 hω1 hσω
    have hcongr : τ = MulAut.congr (conjAut 3 K H) (fieldAut 3 K σ) := by
      rw [hτH]
      ext y
      rfl
    have hpairτ := exists_pair_of_injective (hcongr ▸ (Sec4.autFixCongrEquiv (conjAut 3 K H)
      (fieldAut 3 K σ)).symm).toMonoidHom (hcongr ▸ (Sec4.autFixCongrEquiv (conjAut 3 K H)
      (fieldAut 3 K σ)).symm).injective ⟨u, v, hu1, hu3, hv3, huv, hvu⟩
    have hθ : τ = MulAut.congr e
        (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxN⟩)) := KFacts.inducedAutHom_apply L e _
    have hbar := Sec4.barCentralizer_zpowers_eq_autFix hxN
    obtain ⟨u', v', hu1', hu3', hv3', huv', hvu'⟩ := exists_pair_of_injective
      ((MulEquiv.subgroupCongr hbar).symm.toMonoidHom.comp
        (hθ ▸ Sec4.autFixCongrEquiv e _).toMonoidHom)
      ((MulEquiv.subgroupCongr hbar).symm.injective.comp (hθ ▸ Sec4.autFixCongrEquiv e _).injective)
      hpairτ
    exact e9Closed_of_commuting hu1' hu3' hv3' huv' hvu'
  · obtain ⟨K, _, _, hK, e, hxN, hkind⟩ := hM G L x n .graphField hn hn2 hiso hk
    have hτ3 : KFacts.inducedAutHom L e ⟨x, hxN⟩ ^ 3 = 1 :=
      KFacts.inducedAutHom_pow_eq_one L e hxN hx3
    have hsep := KFacts.stdPinnedPSL_separated (K := K) (n := 3) le_rfl
    have hD := hsep.not_mem_inndiag_of_hasKind hkind (by decide) (by decide)
    exact (hsep.not_isGraphField_of_isField (KFacts.isField_of_pow_three_eq_one le_rfl hτ3 hD)
      ((KFacts.stdPinnedPSL 3 K).hasKind_graphField.mp hkind)).elim

end CFSG.RankThree.PartTwo.Sec8
