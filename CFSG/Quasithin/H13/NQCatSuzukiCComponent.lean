module

public import CFSG.Quasithin.H13.NQBlockOddResidual
public import CFSG.Quasithin.H13.NQBlockResidualBar
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalPSLTwoSections
public import CFSG.RankThree.PartTwo.KFacts.KS14SzClassical
public import CFSG.LieType.Ree.SuzukiUnipotentStructure

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Assembly.LowTwoRank

theorem ker_eq_solvableRadical_of_surjective {D Q : Type} [Group D] [Finite D] [Group Q]
    [IsSimpleGroup Q] (hD : CFSG.IsCComponent (⊤ : Subgroup D)) (hQ : ∃ a b : Q, a * b ≠ b * a)
    (π : D →* Q) (hπ : Function.Surjective π) : π.ker = CFSG.solvableRadical D := by
  have hRad : Group.IsSolvable (CFSG.solvableRadical D) :=
    SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hRker : CFSG.solvableRadical D ≤ π.ker := by
    have hN : ((CFSG.solvableRadical D).map π).Normal := Normal.map inferInstance π hπ
    have hsol : Group.IsSolvable ((CFSG.solvableRadical D).map π) :=
      Group.isSolvable_of_surjective (π.subgroupMap_surjective (CFSG.solvableRadical D))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.solvableRadical D).map π) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have hQs : Group.IsSolvable Q :=
        Group.isSolvable_of_surjective (f := ((CFSG.solvableRadical D).map π).subtype)
          fun q => ⟨⟨q, by rw [h]; exact mem_top q⟩, rfl⟩
      obtain ⟨a, b, hab⟩ := hQ
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hQs a b)
  refine le_antisymm ?_ hRker
  obtain ⟨hDs, -⟩ := NQBlock.simple_radical_quotient_of_isCComponent_top hD
  have hN : (π.ker.map (QuotientGroup.mk' (CFSG.solvableRadical D))).Normal :=
    Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (π.ker.map (QuotientGroup.mk' (CFSG.solvableRadical D))) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have htop : ∀ x : D, π x = 1 := by
      intro x
      have hx : (QuotientGroup.mk' (CFSG.solvableRadical D) x) ∈
          π.ker.map (QuotientGroup.mk' (CFSG.solvableRadical D)) := by
        rw [h]
        exact mem_top _
      obtain ⟨y, hy, hyx⟩ := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      have h1 := mul_mem hy (hRker hyx)
      rwa [mul_inv_cancel_left] at h1
    obtain ⟨a, b, hab⟩ := hQ
    apply hab
    obtain ⟨x, rfl⟩ := hπ a
    obtain ⟨y, rfl⟩ := hπ b
    rw [htop x, htop y]

theorem exists_surjective_projective_two_ker_eq_solvableRadical
    {D : Type} [Group D] [Finite D] (hSQT : CFSG.IsStronglyQuasithin D)
    (hD : CFSG.IsCComponent (⊤ : Subgroup D))
    (hq : ¬ CFSG.IsQuasisimple (D ⧸ CFSG.pCore 2 D)) :
    ∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧
      ∃ π : D →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s),
        Function.Surjective π ∧ π.ker = CFSG.solvableRadical D := by
  classical
  obtain ⟨hSQT', hO2', hLC'⟩ := NQBlock.quotient_two_core_setup hSQT hD
  obtain ⟨-, hFne, hodd, hCF, hcomm, hcores⟩ :=
    NQBlock.odd_Fitting_cores_self hSQT' hO2' hLC' hq
  obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.mpr ((one_lt_card_iff_ne_bot _).mpr hFne)
  obtain ⟨-, hcrit⟩ := NQBlock.all_prime_critical_actions_core hLC' hCF hodd hcomm hcores
  obtain ⟨-, Dr, hDrc, hdata, -⟩ := hcrit r hr
  obtain ⟨s, hs, hs5, -, ⟨ψ⟩⟩ := hdata.projective
  obtain ⟨-, hJs, hJnab⟩ := hdata.isQuasisimple
  have := hJs
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (center (NQBlock.criticalAction Dr).range)).comp
        ((NQBlock.criticalAction Dr).rangeRestrict.comp
          (QuotientGroup.mk' (CFSG.pCore 2 D)))) :=
    (QuotientGroup.mk'_surjective _).comp
      ((NQBlock.criticalAction Dr).rangeRestrict_surjective.comp
        (QuotientGroup.mk'_surjective _))
  have hker := ker_eq_solvableRadical_of_surjective hD hJnab _ hsurj
  refine ⟨s, hs, hs5, ψ.toMonoidHom.comp _, ψ.surjective.comp hsurj, ?_⟩
  rw [← MonoidHom.comap_ker, (MonoidHom.ker_eq_bot_iff _).mpr ψ.injective, MonoidHom.comap_bot]
  exact hker

theorem suzukiZ0_isElementaryAbelian_card {a : ℕ} {k : Type}
    [Field k] [Finite k] (hk : Nat.card k = 2 ^ (2 * a + 1)) :
    CFSG.IsElementaryAbelian 2 (LieType.Ree.suzukiZ0 a k) ∧
      Nat.card (LieType.Ree.suzukiZ0 a k) = 2 ^ (2 * a + 1) := by
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hcoe := LieType.Ree.coe_suzukiZ0 (a := a) hk
  have hmem : ∀ z : LieType.Ree.suzukiZ0 a k, ∃ v : k, LieType.Ree.suzukiSElt a k 0 v = z :=
    fun z => (LieType.Ree.mem_suzukiZ0_iff hk).mp z.2
  refine ⟨{ toIsMulCommutative := ⟨⟨fun x y => Subtype.ext ?_⟩⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
              Subtype.ext ?_ }, ?_⟩
  · obtain ⟨v, hv⟩ := hmem x
    obtain ⟨w, hw⟩ := hmem y
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hv, ← hw, LieType.Ree.suzukiSElt_mul hk,
      LieType.Ree.suzukiSElt_mul hk]
    congr 1
    simp [zero_pow hθ0, add_comm]
  · obtain ⟨v, hv⟩ := hmem x
    rw [Subgroup.coe_pow, ← hv, sq, LieType.Ree.suzukiSElt_mul hk, OneMemClass.coe_one,
      ← LieType.Ree.suzukiSElt_zero_zero hk]
    obtain ⟨h2, -⟩ := LieType.Ree.suzuki_frob_data a hk
    congr 1
    · simp
    · rw [zero_pow hθ0, zero_mul, add_zero]
      linear_combination v * h2
  · have hinj : Function.Injective fun v : k => LieType.Ree.suzukiSElt a k 0 v :=
      fun v w h => (LieType.Ree.suzukiSElt_inj.mp h).2
    rw [← hk, ← SetLike.coe_sort_coe, hcoe, Nat.card_range_of_injective hinj]

theorem sqt_nonquasisimple_Ccomponent_prime_linear_radical_quotient_and_no_Suzuki_section
    {D : Type} [Group D] [Finite D] (hSQT : CFSG.IsStronglyQuasithin D)
    (hD : CFSG.IsCComponent (⊤ : Subgroup D)) :
    (¬ CFSG.IsQuasisimple (D ⧸ CFSG.pCore 2 D) →
      ∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧
        ∃ π : D →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s),
          Function.Surjective π ∧ π.ker = CFSG.solvableRadical D ∧
          3 ∣ Nat.card (D ⧸ CFSG.solvableRadical D)) ∧
    ∀ B : Subgroup D, Group.IsPerfect B →
      (∃ a : ℕ, 1 ≤ a ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = 2 ^ (2 * a + 1) ∧
        Nonempty (↥B ⧸ CFSG.solvableRadical ↥B ≃* Blueprint.suzukiGroup a k)) →
      CFSG.IsQuasisimple (D ⧸ CFSG.pCore 2 D) := by
  classical
  refine ⟨fun hq => ?_, fun B _ hBs => ?_⟩
  · obtain ⟨s, hs, hs5, π, hπ, hker⟩ :=
      exists_surjective_projective_two_ker_eq_solvableRadical hSQT hD hq
    refine ⟨s, hs, hs5, π, hπ, hker, ?_⟩
    have : Fact s.Prime := ⟨hs⟩
    have e : (D ⧸ CFSG.solvableRadical D) ≃* StatedProj (StatedSL 2 (ZMod s)) :=
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective π hπ)).trans
        (SectionRank.OddCover.pslEquiv (ZMod s))
    obtain ⟨y, hy⟩ := RankThree.PartTwo.KFacts.KS14.exists_orderOf_eq_three_statedProj_statedSL
      (K := ZMod s) (n := 2) le_rfl
    rw [Nat.card_congr e.toEquiv, ← hy]
    exact orderOf_dvd_natCard y
  · by_contra hq
    obtain ⟨s, hs, hs5, π₀, hπ₀, hker₀⟩ :=
      exists_surjective_projective_two_ker_eq_solvableRadical hSQT hD hq
    obtain ⟨a, ha, k, hk, hkf, hcard, ⟨η⟩⟩ := hBs
    have : Fact s.Prime := ⟨hs⟩
    set π : D →* StatedProj (StatedSL 2 (ZMod s)) :=
      (SectionRank.OddCover.pslEquiv (ZMod s)).toMonoidHom.comp π₀ with hπdef
    have hker : π.ker = CFSG.solvableRadical D := by
      rw [← hker₀]
      ext x
      simp [hπdef, MonoidHom.mem_ker]
    have hRad : Group.IsSolvable (CFSG.solvableRadical D) :=
      SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    have hBR : (CFSG.solvableRadical D).comap B.subtype ≤ CFSG.solvableRadical B := by
      refine SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical (Normal.comap inferInstance _)
        ?_
      let ι : ↥((CFSG.solvableRadical D).comap B.subtype) →* ↥(CFSG.solvableRadical D) :=
        (B.subtype.comp ((CFSG.solvableRadical D).comap B.subtype).subtype).codRestrict _
          fun x => x.2
      refine Group.isSolvable_of_isSolvable_injective (f := ι) fun x y hxy => ?_
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    set σ : ↥B →* Blueprint.suzukiGroup a k :=
      η.toMonoidHom.comp (QuotientGroup.mk' (CFSG.solvableRadical B)) with hσ
    have hσs : Function.Surjective σ := η.surjective.comp (QuotientGroup.mk'_surjective _)
    set Z₀ := LieType.Ree.suzukiZ0 a k with hZ₀
    obtain ⟨hZe, hZc⟩ := suzukiZ0_isElementaryAbelian_card (a := a) hcard
    set P₁ := Z₀.comap σ with hP₁
    set K₀ := (CFSG.solvableRadical B).subgroupOf P₁ with hK₀
    set χ : ↥P₁ →* ↥Z₀ := (σ.comp P₁.subtype).codRestrict Z₀ fun x => x.2 with hχ
    have hχs : Function.Surjective χ := by
      intro z
      obtain ⟨b, hb⟩ := hσs z
      exact ⟨⟨b, by rw [hP₁, mem_comap, hb]; exact z.2⟩, Subtype.ext hb⟩
    have hχk : χ.ker = K₀ := by
      ext x
      rw [MonoidHom.mem_ker, hK₀, mem_subgroupOf, ← QuotientGroup.eq_one_iff]
      constructor
      · intro h
        have h1 : σ x = 1 := congrArg Subtype.val h
        exact η.injective (by rw [map_one]; exact h1)
      · intro h
        apply Subtype.ext
        change σ x = 1
        rw [hσ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, h]
        exact map_one _
    set θ₀ : ↥P₁ →* StatedProj (StatedSL 2 (ZMod s)) :=
      π.comp (B.subtype.comp P₁.subtype) with hθ₀
    set A := θ₀.range with hA
    have hK₀n : K₀.Normal := Normal.subgroupOf inferInstance P₁
    set N : Subgroup ↥A := K₀.map θ₀.rangeRestrict with hN
    have hNn : N.Normal := Normal.map hK₀n _ θ₀.rangeRestrict_surjective
    set θ : ↥P₁ →* ↥A ⧸ N := (QuotientGroup.mk' N).comp θ₀.rangeRestrict with hθ
    have hθs : Function.Surjective θ :=
      (QuotientGroup.mk'_surjective N).comp θ₀.rangeRestrict_surjective
    have hθk : θ.ker = K₀ := by
      ext x
      rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have h1 : θ₀ (y⁻¹ * x) = 1 := by
          rw [map_mul, map_inv, inv_mul_eq_one]
          exact congrArg Subtype.val hyx
        have h2 : ((y⁻¹ * x : ↥P₁) : ↥B) ∈ CFSG.solvableRadical B := by
          refine hBR ?_
          rw [mem_comap, ← hker]
          exact h1
        have h3 : ((y : ↥P₁) : ↥B) ∈ CFSG.solvableRadical B := hy
        have h4 := mul_mem h3 h2
        rw [← Subgroup.coe_mul, mul_inv_cancel_left] at h4
        exact h4
      · intro hx
        exact ⟨x, hx, rfl⟩
    have e : (↥A ⧸ N) ≃* ↥Z₀ :=
      (QuotientGroup.quotientKerEquivOfSurjective θ hθs).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq (hθk.trans hχk.symm)).trans
          (QuotientGroup.quotientKerEquivOfSurjective χ hχs))
    have hEA : CFSG.IsElementaryAbelian 2 (↥A ⧸ N) :=
      { toIsMulCommutative := ⟨⟨fun x y => e.injective (by
          rw [map_mul, map_mul]
          exact hZe.toIsMulCommutative.is_comm.comm _ _)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => e.injective (by
          rw [map_pow, map_one]
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hZe.exponent_dvd_p _) }
    have hodd : Odd (Nat.card (ZMod s)) := by
      rw [Nat.card_zmod]
      exact hs.odd_of_ne_two (by omega)
    have h4 :=
      (ComponentClassification.OutcomeLocal.odd_projective_linear_two_elementary_two_sections
        hodd).2.2.1 A N hEA
    rw [Nat.card_congr e.toEquiv, hZc] at h4
    have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end CFSG.Quasithin.H13.NQCat
