module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

private lemma lr2ote_conj_ker_eq_center {C : Type} [Group C] :
    (MulAut.conj : C →* MulAut C).ker = Subgroup.center C := by
  ext z
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hz x
    have h : z * x * z⁻¹ = x := by
      have := congrArg (fun f : MulAut C => f x) hz
      simpa [MulAut.conj_apply] using this
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro hz
    ext x
    show z * x * z⁻¹ = x
    rw [(hz x).symm, mul_inv_cancel_right]

private lemma lr2ote_not_seven_dvd_card_of_cube_eq_one
    (Q : Type) [Group Q] [Finite Q] (h : ∀ a : Q, a ^ 3 = 1) :
    ¬ 7 ∣ Nat.card Q := by
  intro h7
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Q) 7 h7
  have h3 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (h a)
  rw [ha] at h3
  norm_num at h3

private lemma lr2ote_factorization_seven_eq_of_ker
    {C : Type} [Group C] [Finite C]
    {Q : Type} [Group Q]
    (Θ : MulAut C →* Q) (hQ7 : ¬ 7 ∣ Nat.card Q)
    (hcenter : Subgroup.center C = ⊥)
    (I : Subgroup (MulAut C)) [I.Normal] (KER : Subgroup (MulAut C))
    (hI : I = (MulAut.conj : C →* MulAut C).range)
    (hKER : KER = Θ.ker)
    (hI_le : I ≤ KER)
    (hcube : ∀ a : KER ⧸ I.subgroupOf KER, a ^ 3 = 1) :
    (Nat.card (MulAut C)).factorization 7 = (Nat.card C).factorization 7 := by
  haveI : Finite Θ.range :=
    Finite.of_surjective Θ.rangeRestrict Θ.rangeRestrict_surjective
  have hconj_inj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [← MonoidHom.ker_eq_bot_iff, lr2ote_conj_ker_eq_center, hcenter]
  have hIcard : Nat.card I = Nat.card C := by
    rw [hI]
    exact (Nat.card_congr (MonoidHom.ofInjective hconj_inj).toEquiv).symm
  have h7range : ¬ 7 ∣ Nat.card Θ.range :=
    fun h => hQ7 (h.trans (Subgroup.card_subgroup_dvd_card Θ.range))
  have hcard1 : Nat.card (MulAut C) = Nat.card Θ.ker * Nat.card Θ.range := by
    calc Nat.card (MulAut C)
        = Nat.card (MulAut C ⧸ Θ.ker) * Nat.card Θ.ker :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker
      _ = Nat.card Θ.range * Nat.card Θ.ker := by
          rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv]
      _ = Nat.card Θ.ker * Nat.card Θ.range := mul_comm _ _
  have hcard2 : Nat.card KER = Nat.card (KER ⧸ I.subgroupOf KER) * Nat.card C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (I.subgroupOf KER),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI_le).toEquiv, hIcard]
  have hQ7' : ¬ 7 ∣ Nat.card (KER ⧸ I.subgroupOf KER) :=
    lr2ote_not_seven_dvd_card_of_cube_eq_one _ hcube
  have h7prod : ¬ 7 ∣ Nat.card (KER ⧸ I.subgroupOf KER) * Nat.card Θ.range := by
    rw [Nat.Prime.dvd_mul Nat.prime_seven]
    exact not_or.mpr ⟨hQ7', h7range⟩
  have hcard3 : Nat.card (MulAut C) =
      Nat.card C * (Nat.card (KER ⧸ I.subgroupOf KER) * Nat.card Θ.range) := by
    rw [hcard1, ← hKER, hcard2]
    ring
  rw [hcard3,
    Nat.factorization_mul (Nat.card_pos (α := C)).ne'
      (mul_ne_zero (Nat.card_pos (α := KER ⧸ I.subgroupOf KER)).ne'
        (Nat.card_pos (α := Θ.range)).ne')]
  rw [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd h7prod, add_zero]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
private lemma lr2opte_card_orbitUnits_E6 {K : Type} [Field K]
    (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) :
    Nat.card ((a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) = 9 := by
  classical
  obtain ⟨σ', hσ', -, hcard', -, -, -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two (le_refl 1) K
      (by rw [hK]; rfl)
  have hσeq : σ' = σ := RingEquiv.ext fun c => by
    rw [hσ', hσ]
    norm_num
  have hcard : ∀ a, Nat.card (orbitField TwistTag.E6 K σ.toRingHom a) =
      2 ^ (TwistTag.E6.orbit a).card := by
    intro a
    rw [← hσeq]
    simpa using hcard' a
  rw [Nat.card_pi]
  have hprod : (∏ a : Fin TwistTag.E6.foldedTag.rank,
      Nat.card ((orbitField TwistTag.E6 K σ.toRingHom a)ˣ))
      = ∏ a : Fin TwistTag.E6.foldedTag.rank,
        (2 ^ (TwistTag.E6.orbit a).card - 1) := by
    apply Finset.prod_congr rfl
    intro a _
    rw [Nat.card_units, hcard a]
  rw [hprod]
  change (∏ a : Fin 4, (2 ^ (TwistTag.E6.orbit a).card - 1)) = 9
  rw [Fin.prod_univ_four]
  have h0 : (TwistTag.E6.orbit (0 : Fin 4)).card = 2 := by decide
  have h1 : (TwistTag.E6.orbit (1 : Fin 4)).card = 2 := by decide
  have h2 : (TwistTag.E6.orbit (2 : Fin 4)).card = 1 := by decide
  have h3 : (TwistTag.E6.orbit (3 : Fin 4)).card = 1 := by decide
  rw [h0, h1, h2, h3]
  norm_num

private lemma lr2opte_mulAut_dvd_eighteen
    {C : Type} [Group C]
    {Q : Type} [Group Q]
    (Θ : MulAut C →* Q) (hrange2 : Nat.card Θ.range ∣ 2)
    (hcenter : Subgroup.center C = ⊥)
    (I : Subgroup (MulAut C)) [I.Normal] (D : Subgroup (MulAut C))
    (hI : I = (MulAut.conj : C →* MulAut C).range)
    (hKER : Θ.ker = I ⊔ D)
    (hD : Nat.card D ∣ 9) :
    Nat.card (MulAut C) ∣ 18 * Nat.card C := by
  have hconj_inj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    rw [← MonoidHom.ker_eq_bot_iff, lr2ote_conj_ker_eq_center, hcenter]
  have hIcard : Nat.card I = Nat.card C := by
    rw [hI]
    exact (Nat.card_congr (MonoidHom.ofInjective hconj_inj).toEquiv).symm
  have hcard1 : Nat.card (MulAut C) = Nat.card Θ.ker * Nat.card Θ.range := by
    calc Nat.card (MulAut C)
        = Nat.card (MulAut C ⧸ Θ.ker) * Nat.card Θ.ker :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker
      _ = Nat.card Θ.range * Nat.card Θ.ker := by
          rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv]
      _ = Nat.card Θ.ker * Nat.card Θ.range := mul_comm _ _
  have hquot_dvd : Nat.card (↥(I ⊔ D) ⧸ I.subgroupOf (I ⊔ D)) ∣ Nat.card D := by
    have e := QuotientGroup.quotientInfEquivProdNormalQuotient D I
    have hcard : Nat.card (↥(I ⊔ D) ⧸ I.subgroupOf (I ⊔ D))
        = Nat.card (D ⧸ I.subgroupOf D) := by
      rw [sup_comm I D]
      exact (Nat.card_congr e.toEquiv).symm
    rw [hcard]
    exact Subgroup.card_quotient_dvd_card _
  have hsup_eq : Nat.card ↥(I ⊔ D) =
      Nat.card (↥(I ⊔ D) ⧸ I.subgroupOf (I ⊔ D)) * Nat.card I := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (I.subgroupOf (I ⊔ D)),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
  have hq : Nat.card (↥(I ⊔ D) ⧸ I.subgroupOf (I ⊔ D)) ∣ 9 := hquot_dvd.trans hD
  have hmain : Nat.card (MulAut C) =
      Nat.card (↥(I ⊔ D) ⧸ I.subgroupOf (I ⊔ D)) * Nat.card C * Nat.card Θ.range := by
    rw [hcard1, hKER, hsup_eq, hIcard]
  rw [hmain]
  have hstep : Nat.card (↥(I ⊔ D) ⧸ I.subgroupOf (I ⊔ D)) * Nat.card C * Nat.card Θ.range
      ∣ 9 * Nat.card C * 2 :=
    mul_dvd_mul (mul_dvd_mul hq (dvd_refl (Nat.card C))) hrange2
  have h18 : 9 * Nat.card C * 2 = 18 * Nat.card C := by ring_nf
  rwa [h18] at hstep

theorem ord7_card_mulAut_dvd_twistedE6_two
    {R : Type} [Group R] (hm : LieModel R .twistedE6 0 2 1) :
    Nat.card (MulAut R) ∣ 18 * Nat.card R := by
  rw [LieModel] at hm
  rcases hm with ⟨hc, -⟩ | ⟨-, -, hchev⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
  · exact absurd hc (by decide)
  · obtain ⟨K, hKfield, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
      CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hchev
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hmain :=
      CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form
        Nat.prime_two (le_refl 1) K hKcard σ hσ
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, -, -⟩, -, -, hZ, -, -⟩ := hmain
    have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
    have hσ2 : ∀ c, σ c = c ^ 2 := by intro c; rw [hσ]; norm_num
    let Inn := CFSG.LieType.Chevalley.twistedE6Inn K σ
    let Diag := CFSG.LieType.Chevalley.twistedE6Diag K σ
    have hI : Inn = (MulAut.conj : CFSG.LieType.Chevalley.twistedE6RootGroup K σ →*
        MulAut (CFSG.LieType.Chevalley.twistedE6RootGroup K σ)).range := rfl
    have hKER : Θ.ker = Inn ⊔ Diag := hΘker
    have hcardAut : Nat.card (RingAut K) = 2 := by
      have hK2 : Nat.card K = 2 ^ (2 * 1) := by rw [hKcard]; norm_num
      have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
        Nat.prime_two K hK2).1
      simpa using h
    have hrange2 : Nat.card Θ.range ∣ 2 := by
      have h := Subgroup.card_subgroup_dvd_card Θ.range
      rwa [hcardAut] at h
    have hDiag : Nat.card Diag ∣ 9 := by
      have hU : Nat.card ((a : Fin CFSG.Blueprint.Chevalley.TwistTag.E6.foldedTag.rank) →
          (CFSG.LieType.Chevalley.orbitField CFSG.Blueprint.Chevalley.TwistTag.E6 K
            σ.toRingHom a)ˣ) = 9 :=
        lr2opte_card_orbitUnits_E6 hK4 σ hσ2
      have h := Subgroup.card_range_dvd
        (CFSG.LieType.Chevalley.compatDiagAutHom
          CFSG.Blueprint.Chevalley.TwistTag.E6 K σ.toRingHom)
      rw [hU] at h
      exact h
    have hres := lr2opte_mulAut_dvd_eighteen Θ hrange2 hZ Inn Diag hI hKER hDiag
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
    exact hres
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)

theorem ord7Param_twistedE6
    {f : ℕ} (h7 : ¬ 7 ∣ f) : Ord7Param .twistedE6 0 2 f := by
  intro R _ _ _ hmodel
  rw [LieModel] at hmodel
  rcases hmodel with ⟨hc, -⟩ | ⟨-, -, hchev⟩ | ⟨-, hc, -⟩ | ⟨-, hc, -⟩
  · exact absurd hc (by decide)
  · obtain ⟨K, hKfield, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
      CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hchev
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hf : 1 ≤ f := hchev.1.2.1
    have hmain :=
      CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form
        Nat.prime_two hf K hKcard σ hσ
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hΘker, -, hΘexp, -⟩, -, -, hZ, -, -⟩ := hmain
    have hcardAut : Nat.card (RingAut K) = 2 * f := by
      have hK2 : Nat.card K = 2 ^ (2 * f) := by
        rw [hKcard, ← pow_mul]
        ring_nf
      exact (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
        Nat.prime_two K hK2).1
    have h7Aut : ¬ 7 ∣ Nat.card (RingAut K) := by
      rw [hcardAut]
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_seven).1 h with h2 | hf7
      · norm_num at h2
      · exact h7 hf7
    let Inn := CFSG.LieType.Chevalley.twistedE6Inn K σ
    let Diag := CFSG.LieType.Chevalley.twistedE6Diag K σ
    let KER := Inn ⊔ Diag
    have hI : Inn = (MulAut.conj : CFSG.LieType.Chevalley.twistedE6RootGroup K σ →*
        MulAut (CFSG.LieType.Chevalley.twistedE6RootGroup K σ)).range := rfl
    have hI_le : Inn ≤ KER := le_sup_left
    have hKER : KER = Θ.ker := hΘker.symm
    have hcube : ∀ a : KER ⧸ Inn.subgroupOf KER, a ^ 3 = 1 := hΘexp
    have hcardEq := lr2ote_factorization_seven_eq_of_ker Θ h7Aut hZ Inn KER hI hKER hI_le hcube
    have eC : R ≃* CFSG.LieType.Chevalley.twistedE6RootGroup K σ := e
    rw [Nat.card_congr (MulAut.congr eC).toEquiv, Nat.card_congr eC.toEquiv]
    exact le_of_eq hcardEq
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)

end CFSG.StandardType.SporadicShape