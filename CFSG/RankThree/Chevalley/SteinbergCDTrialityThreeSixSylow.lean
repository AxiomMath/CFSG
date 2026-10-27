module

public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLines

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice
open scoped Matrix

theorem threeSix_prime_not_dvd {Q ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : (p : ℤ) ∣ Q ^ 2 + ε * Q + 1) :
    ¬ (p : ℤ) ∣ Q ∧ ¬ (p : ℤ) ∣ Q ^ 2 - 1 ∧ ¬ (p : ℤ) ∣ Q ^ 2 - ε * Q + 1 ∧
      ¬ (p : ℤ) ∣ Q ^ 4 - Q ^ 2 + 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp1 : ¬ (p : ℤ) ∣ 1 := hpZ.not_dvd_one
  have hsmall : ∀ n : ℤ, 0 < n → n ≤ 3 → ¬ (p : ℤ) ∣ n := fun n hn hn3 h => by
    have := Int.le_of_dvd hn h
    omega
  have hq : ¬ (p : ℤ) ∣ Q := fun h => hp1 (by
    have h' := dvd_sub hpd (dvd_mul_of_dvd_left h (Q + ε))
    rwa [show Q ^ 2 + ε * Q + 1 - Q * (Q + ε) = 1 by ring] at h')
  refine ⟨hq, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h1 : (p : ℤ) ∣ ε * Q + 2 := by
      have h' := dvd_sub hpd h
      rwa [show Q ^ 2 + ε * Q + 1 - (Q ^ 2 - 1) = ε * Q + 2 by ring] at h'
    have h2 := dvd_sub h (dvd_mul_of_dvd_left h1 (ε * Q - 2))
    have h3 : Q ^ 2 - 1 - (ε * Q + 2) * (ε * Q - 2) = 3 := by
      rcases hε with rfl | rfl <;> ring
    rw [h3] at h2
    exact hsmall 3 (by norm_num) le_rfl h2
  · have h' := dvd_sub hpd h
    rw [show Q ^ 2 + ε * Q + 1 - (Q ^ 2 - ε * Q + 1) = 2 * ε * Q by ring] at h'
    rcases hpZ.dvd_or_dvd h' with h2 | h2
    · rcases hpZ.dvd_or_dvd h2 with h4 | h4
      · exact hsmall 2 (by norm_num) (by norm_num) h4
      · rcases hε with rfl | rfl
        · exact hp1 h4
        · exact hp1 (dvd_neg.1 h4)
    · exact hq h2
  · have h6 : (p : ℤ) ∣ Q ^ 4 + Q ^ 2 + 1 := by
      have h' := dvd_mul_of_dvd_left hpd (Q ^ 2 - ε * Q + 1)
      have heq : (Q ^ 2 + ε * Q + 1) * (Q ^ 2 - ε * Q + 1) = Q ^ 4 + Q ^ 2 + 1 := by
        rcases hε with rfl | rfl <;> ring
      rwa [heq] at h'
    have h' := dvd_sub h6 h
    rw [show Q ^ 4 + Q ^ 2 + 1 - (Q ^ 4 - Q ^ 2 + 1) = 2 * Q ^ 2 by ring] at h'
    rcases hpZ.dvd_or_dvd h' with h2 | h2
    · exact hsmall 2 (by norm_num) (by norm_num) h2
    · exact hq (hpZ.dvd_of_dvd_pow h2)

theorem not_dvd_index_threeSixTorus
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1) (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ d) (T : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hT : Nat.card T = d ^ 2) : ¬ p ∣ T.index := by
  have hcardC := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hcard := T.card_mul_index
  rw [hT, hcardC] at hcard
  have hcardZ : (d : ℤ) ^ 2 * T.index = ((ℓ ^ f : ℕ) : ℤ) ^ 12 * (((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) *
      (((ℓ ^ f : ℕ) : ℤ) ^ 6 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 8 + ((ℓ ^ f : ℕ) : ℤ) ^ 4 + 1) := by
    have h6 : 1 ≤ (ℓ ^ f) ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h6, Nat.cast_sub h2]
      at h
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h ⊢
    exact h
  have hD : (d : ℤ) ≠ 0 := by
    rw [hd]
    have : (1 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast hq1
    rcases hε with rfl | rfl <;> nlinarith
  have hidx : (T.index : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 12 * (((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) ^ 2 *
      (((ℓ ^ f : ℕ) : ℤ) ^ 2 - ε * (ℓ ^ f : ℕ) + 1) ^ 2 *
      (((ℓ ^ f : ℕ) : ℤ) ^ 4 - ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hD)
    rw [hcardZ, hd]
    rcases hε with rfl | rfl <;> ring
  intro hdvd
  have hpi : (p : ℤ) ∣ (T.index : ℤ) := by exact_mod_cast hdvd
  rw [hidx] at hpi
  have hpd' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1 := by
    rw [← hd]
    exact_mod_cast hpd
  obtain ⟨h1, h2, h3, h4⟩ := threeSix_prime_not_dvd hε hp hp3 hpd'
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpZ.dvd_or_dvd hpi with h | h
  · rcases hpZ.dvd_or_dvd h with h | h
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact h1 (hpZ.dvd_of_dvd_pow h)
      · exact h2 (hpZ.dvd_of_dvd_pow h)
    · exact h3 (hpZ.dvd_of_dvd_pow h)
  · exact h4 h

theorem eq_of_mem_of_card_eq_prime {G : Type*} [Group G] {M N : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hM : Nat.card M = p) (hN : Nat.card N = p) {h : G} (hhM : h ∈ M)
    (hhN : h ∈ N) (h1 : h ≠ 1) : M = N := by
  have hord : ∀ X : Subgroup G, Nat.card X = p → h ∈ X → Subgroup.zpowers h = X := by
    intro X hX hhX
    have : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; exact hp.ne_zero)
    have hdvd : orderOf h ∣ p := hX ▸ Subgroup.orderOf_dvd_natCard X hhX
    have ho : orderOf h = p :=
      ((Nat.dvd_prime hp).1 hdvd).resolve_left fun h' => h1 (orderOf_eq_one_iff.1 h')
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hhX)
      (by rw [hX, Nat.card_zpowers, ho])
  exact (hord M hM hhM).symm.trans (hord N hN hhN)

section Fixed

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : K ≃+* K)

@[expose] def threeSixEmb :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* ModGL TwistTag.D4.tag Ω :=
  (baseChangeGL (algebraMap K Ω)).comp (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype

@[expose] def threeSixFixedTorus
    (Fr : Ω →+* Ω) (ε : ℤ) (g : ModGL TwistTag.D4.tag Ω) :
    Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  ((threeSixTorus Ω Fr ε).map (MulAut.conj g).toMonoidHom).comap (threeSixEmb K Ω σ)

@[expose] def threeSixFixedTorsion
    (Fr : Ω →+* Ω) (ε : ℤ) (p : ℕ)
    (g : ModGL TwistTag.D4.tag Ω) : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  ((threeSixTorsion Ω Fr ε p).map (MulAut.conj g).toMonoidHom).comap (threeSixEmb K Ω σ)

end Fixed

theorem triality_three_six_tori_Sylow_and_root_kernels
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1) :
    threeSixN Ω ε ∈ adjointGroup TwistTag.D4.tag Ω ∧
    (∃ g ∈ adjointGroup TwistTag.D4.tag Ω, trialityFrob Ω Fr g = g * threeSixN Ω ε) ∧
    (∀ a : Fin TwistTag.D4.tag.rank → Ωˣ, rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε ↔
      ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
        rootChar a ((ε • twelveW ^ 4) *ᵥ v) = rootChar a v ^ (ℓ ^ f)) ∧
    ∀ g ∈ adjointGroup TwistTag.D4.tag Ω, trialityFrob Ω Fr g = g * threeSixN Ω ε →
      (threeSixTorus Ω Fr ε).map (MulAut.conj g).toMonoidHom ≤ (threeSixEmb K Ω σ).range ∧
      Nonempty (threeSixFixedTorus K Ω σ Fr ε g ≃*
        Multiplicative (ZMod d) × Multiplicative (ZMod d)) ∧
      ∀ p : ℕ, p.Prime → 3 < p → p ∣ d →
        (∃ S : Sylow p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
          (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
            threeSixFixedTorus K Ω σ Fr ε g) ∧
        (∀ P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p P →
          ∃ c, P.map (MulAut.conj c).toMonoidHom ≤ threeSixFixedTorus K Ω σ Fr ε g) ∧
        IsElementaryAbelian p (threeSixTorsion Ω Fr ε p) ∧
        Nat.card (threeSixTorsion Ω Fr ε p) = p ^ 2 ∧
        (∀ i, Nat.card (threeSixLine Ω Fr ε p i) = p) ∧
        (Pairwise fun i j => threeSixLine Ω Fr ε p i ≠ threeSixLine Ω Fr ε p j) ∧
        {M : Subgroup (ModGL TwistTag.D4.tag Ω) | M ≤ threeSixTorsion Ω Fr ε p ∧
          Nat.card M = p ∧ ∀ i, M ≠ threeSixLine Ω Fr ε p i}.ncard = p - 3 ∧
        (∀ a : Fin TwistTag.D4.tag.rank → Ωˣ,
          rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p →
          rootDiagUnit TwistTag.D4.tag a ≠ 1 →
          (∀ i, rootDiagUnit TwistTag.D4.tag a ∈ threeSixLine Ω Fr ε p i →
            survivingRoots a = trialitySigma i) ∧
          ((∀ i, rootDiagUnit TwistTag.D4.tag a ∉ threeSixLine Ω Fr ε p i) →
            survivingRoots a = ∅)) ∧
        (∀ a : Fin TwistTag.D4.tag.rank → Ωˣ,
          rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p →
          rootDiagUnit TwistTag.D4.tag a ≠ 1 → survivingRoots a = ∅ →
          ∀ x, threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ →
            Subgroup.centralizer {x} = threeSixFixedTorus K Ω σ Fr ε g ∧
              Odd (Nat.card (threeSixFixedTorus K Ω σ Fr ε g))) ∧
        ∀ A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsElementaryAbelian p A →
          Nat.card A = p ^ 2 →
          ∃ c, A.map (MulAut.conj c).toMonoidHom = threeSixFixedTorsion K Ω σ Fr ε p g ∧
            (∃ M ≤ A, Nat.card M = p ∧ ∀ x ∈ M, ∀ a : Fin TwistTag.D4.tag.rank → Ωˣ,
              threeSixEmb K Ω σ (c * x * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ →
                (survivingRoots a).Nonempty) ∧
            (∃ M ≤ A, Nat.card M = p ∧ ∀ x ∈ M, x ≠ 1 → ∀ a : Fin TwistTag.D4.tag.rank → Ωˣ,
              threeSixEmb K Ω σ (c * x * c⁻¹) = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ →
                survivingRoots a = ∅) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
  obtain ⟨-, hfix, -, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group ℓ f
    hℓ hf K hK Ω 1 (Or.inl rfl) σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) Fr hFr
  have hnG : threeSixN Ω ε ∈ adjointGroup TwistTag.D4.tag Ω := threeSixN_mem_adjointGroup hε
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity ℓ Ω f hf).2 TwistTag.D4 1
  have hFrob : iterateFrobenius Ω ℓ f = Fr :=
    RingHom.ext fun c => by rw [iterateFrobenius_def, hFr]
  have hexists : ∃ g ∈ adjointGroup TwistTag.D4.tag Ω, trialityFrob Ω Fr g = g * threeSixN Ω ε := by
    obtain ⟨h, hh⟩ := hLang ⟨threeSixN Ω ε, hnG⟩
    refine ⟨h, h.2, ?_⟩
    have h1 := congrArg Subtype.val hh
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hS, zpow_one, hFrob] at h1
    rw [trialityFrob_apply, h1, mul_inv_cancel_left]
  refine ⟨hnG, hexists, fun a => rootDiagUnit_mem_threeSixTorus_iff Fr hFr hε a,
    fun g hgG hFg => ?_⟩
  have hιinj : Function.Injective (threeSixEmb K Ω σ) :=
    (baseChangeGL_injective (τ := TwistTag.D4.tag) (algebraMap K Ω)).comp Subtype.val_injective
  have hrange : (threeSixEmb K Ω σ).range = adjointGroup TwistTag.D4.tag Ω ⊓
      (trialityFrob Ω Fr).eqLocus (MonoidHom.id _) := by
    rw [threeSixEmb, MonoidHom.range_comp, Subgroup.range_subtype]
    refine SetLike.coe_injective ?_
    rw [← hfix]
    ext x
    simp only [pow_one, Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf]
    rfl
  have hHG := torusGroup_le_adjointGroup_triality (L := Ω)
  have hT₀H : threeSixTorus Ω Fr ε ≤ torusGroup TwistTag.D4.tag Ω := inf_le_left
  have hconjF : ∀ u : ModGL TwistTag.D4.tag Ω, trialityFrob Ω Fr (g * u * g⁻¹) =
      g * (threeSixN Ω ε * trialityFrob Ω Fr u * (threeSixN Ω ε)⁻¹) * g⁻¹ := fun u => by
    rw [map_mul, map_mul, map_inv, hFg]
    group
  have hfixT₀ : ∀ u ∈ threeSixTorus Ω Fr ε,
      threeSixN Ω ε * trialityFrob Ω Fr u * (threeSixN Ω ε)⁻¹ = u := fun u hu => hu.2
  have hTcι : (threeSixTorus Ω Fr ε).map (MulAut.conj g).toMonoidHom ≤
      (threeSixEmb K Ω σ).range := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hrange]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG (hHG (hT₀H hu))) (inv_mem hgG), ?_⟩
    change trialityFrob Ω Fr (g * u * g⁻¹) = g * u * g⁻¹
    rw [hconjF, hfixT₀ u hu]
  have eT : threeSixFixedTorus K Ω σ Fr ε g ≃* threeSixTorus Ω Fr ε :=
    ((Subgroup.equivMapOfInjective _ (threeSixEmb K Ω σ) hιinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hTcι))).trans
      (Subgroup.equivMapOfInjective (threeSixTorus Ω Fr ε) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
  have hqΩ : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hqΩ' : (ℓ : Ω) ^ f = 0 := by rw [← Nat.cast_pow, hqΩ]
  have hdΩ : (d : Ω) = 1 := by
    have h := congrArg (Int.cast : ℤ → Ω) hd
    push_cast at h
    rw [h, hqΩ']
    ring
  have : NeZero (d : Ω) := ⟨by rw [hdΩ]; exact one_ne_zero⟩
  have : NeZero d := ⟨fun h0 => by simp [h0] at hdΩ⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := Ω) (n := d)
  have hcardμ : Nat.card (rootsOfUnity d Ω) = d := hζ.card_rootsOfUnity
  have eT₀ : threeSixTorus Ω Fr ε ≃* rootsOfUnity d Ω × rootsOfUnity d Ω :=
    ((MulEquiv.subgroupCongr (threeSixTorus_eq_map Fr hFr hε hd)).trans
      (Subgroup.equivMapOfInjective _ _ (injective_threeSixParam _ ε)).symm).trans
      (Subgroup.prodEquiv _ _)
  have eμ : rootsOfUnity d Ω ≃* Multiplicative (ZMod d) :=
    (zmodCyclicMulEquiv (rootsOfUnity.isCyclic Ω d)).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcardμ).toAddEquiv)
  have hcardT : Nat.card (threeSixFixedTorus K Ω σ Fr ε g) = d ^ 2 := by
    rw [Nat.card_congr (eT.trans eT₀).toEquiv, Nat.card_prod, hcardμ, sq]
  have hdodd : Odd d := by
    have hZ : Odd (d : ℤ) := by
      rw [hd]
      rcases hε with rfl | rfl
      · rw [show ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 * ((ℓ ^ f : ℕ) : ℤ) + 1 =
          ((ℓ ^ f : ℕ) : ℤ) * (((ℓ ^ f : ℕ) : ℤ) + 1) + 1 by ring]
        exact (Int.even_mul_succ_self _).add_one
      · rw [show ((ℓ ^ f : ℕ) : ℤ) ^ 2 + -1 * ((ℓ ^ f : ℕ) : ℤ) + 1 =
          (((ℓ ^ f : ℕ) : ℤ) - 1) * (((ℓ ^ f : ℕ) : ℤ) - 1 + 1) + 1 by ring]
        exact (Int.even_mul_succ_self _).add_one
    exact Int.odd_coe_nat d |>.1 hZ
  refine ⟨hTcι, ⟨(eT.trans eT₀).trans (MulEquiv.prodCongr eμ eμ)⟩, fun p hp hp3 hpd => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hidx := not_dvd_index_threeSixTorus hℓ hf hK σ hσ hε hd hp hp3 hpd _ hcardT
  have hSyl : ∃ S : Sylow p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (S : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≤
        threeSixFixedTorus K Ω σ Fr ε g := by
    obtain ⟨S₀⟩ : Nonempty (Sylow p (threeSixFixedTorus K Ω σ Fr ε g)) := inferInstance
    have hS : IsPGroup p ((S₀ : Subgroup _).map (threeSixFixedTorus K Ω σ Fr ε g).subtype) :=
      S₀.isPGroup'.map _
    have hSi : ¬ p ∣ ((S₀ : Subgroup _).map (threeSixFixedTorus K Ω σ Fr ε g).subtype).index := by
      rw [Subgroup.index_map_subtype]
      exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hidx
    exact ⟨hS.toSylow hSi, by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.map_subtype_le _⟩
  have hconjT : ∀ P : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p P →
      ∃ c, P.map (MulAut.conj c).toMonoidHom ≤ threeSixFixedTorus K Ω σ Fr ε g := fun P hP =>
    exists_conj_map_le_of_not_dvd_index hidx hP
  obtain ⟨hEA, hcardTp, hcardL, hne, hcount, hsurv⟩ :=
    threeSix_lines Fr hFr hqΩ hε hd hp hp3 hpd
  have hℓp : ℓ ≠ p := by
    rintro rfl
    have h1 : (ℓ : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast dvd_pow_self ℓ (by omega)
    have h2 : (ℓ : ℤ) ∣ (d : ℤ) := by exact_mod_cast hpd
    rw [hd] at h2
    have h3 := dvd_sub h2 (dvd_mul_of_dvd_left h1 (((ℓ ^ f : ℕ) : ℤ) + ε))
    rw [show ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1 -
      ((ℓ ^ f : ℕ) : ℤ) * (((ℓ ^ f : ℕ) : ℤ) + ε) = 1 by ring] at h3
    have h4 : (ℓ : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h3
    exact hℓ.one_lt.ne' (by exact_mod_cast h4)
  have hpΩ : ringChar Ω ≠ p := by
    rw [ringChar.eq Ω ℓ]
    exact hℓp
  have hHcomm := (triangular_borel_structure.{0, 0} TwistTag.D4.tag Ω).1
  have hTcomm : ∀ y ∈ threeSixFixedTorus K Ω σ Fr ε g, ∀ z ∈ threeSixFixedTorus K Ω σ Fr ε g,
      y * z = z * y := by
    intro y hy z hz
    apply hιinj
    obtain ⟨u, hu, hyu⟩ := hy
    obtain ⟨u', hu', hzu⟩ := hz
    rw [map_mul, map_mul, ← hyu, ← hzu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc := hHcomm u (hT₀H hu) u' (hT₀H hu')
    calc g * u * g⁻¹ * (g * u' * g⁻¹) = g * (u * u') * g⁻¹ := by group
      _ = g * (u' * u) * g⁻¹ := by rw [hc]
      _ = g * u' * g⁻¹ * (g * u * g⁻¹) := by group
  have hchar' : ∀ u ∈ torusGroup TwistTag.D4.tag Ω,
      (threeSixN Ω ε * trialityFrob Ω Fr u * (threeSixN Ω ε)⁻¹ = u ↔
        u ∈ threeSixTorus Ω Fr ε) := fun u hu => ⟨fun h => ⟨hu, h⟩, fun h => h.2⟩
  have hreg : ∀ a : Fin TwistTag.D4.tag.rank → Ωˣ,
      rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorsion Ω Fr ε p →
      rootDiagUnit TwistTag.D4.tag a ≠ 1 → survivingRoots a = ∅ →
      ∀ x, threeSixEmb K Ω σ x = g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ →
        Subgroup.centralizer {x} = threeSixFixedTorus K Ω σ Fr ε g ∧
          Odd (Nat.card (threeSixFixedTorus K Ω σ Fr ε g)) := by
    intro a ha ha1 hemp x hx
    have hoc : orderOf (rootDiagUnit TwistTag.D4.tag a) = p := orderOf_eq_prime ha.2 ha1
    have hreg' : ∀ α : Fin Tag.D4.rank → ℤ, IsRoot Tag.D4 α → rootChar a α ≠ 1 := by
      intro α hα h1
      have hmem : α ∈ survivingRoots a := ⟨hα, h1⟩
      rw [hemp] at hmem
      exact hmem
    have hX : toralCentralizer TwistTag.D4.tag Ω a = torusGroup TwistTag.D4.tag Ω := by
      obtain ⟨-, hiff⟩ := D4_odd_prime_regular_root_character_centralizer Ω p hp (by omega) hpΩ a
        hoc hreg'
      ext y
      rw [toralCentralizer, Subgroup.mem_inf, ← conj_eq_iff_mem_centralizer]
      exact hiff y
    have hxT : x ∈ threeSixFixedTorus K Ω σ Fr ε g :=
      ⟨rootDiagUnit TwistTag.D4.tag a, ha.1, hx.symm⟩
    refine ⟨le_antisymm (centralizer_le_comap_conj_twisted (threeSixEmb K Ω σ) (trialityFrob Ω Fr)
      hgG hFg hrange hchar' hx.symm hX) fun y hy => ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hTcomm z hxT y hy
    · rw [hcardT]
      exact hdodd.pow
  refine ⟨hSyl, hconjT, hEA, hcardTp, hcardL, hne, hcount, hsurv, hreg, fun A hA hAcard => ?_⟩
  have hcardTpC : Nat.card (threeSixFixedTorsion K Ω σ Fr ε p g) = p ^ 2 := by
    have hle : (threeSixTorsion Ω Fr ε p).map (MulAut.conj g).toMonoidHom ≤
        (threeSixEmb K Ω σ).range :=
      (Subgroup.map_mono (threeSixTorsion_le Fr ε p)).trans hTcι
    rw [← hcardTp, threeSixFixedTorsion, ← Subgroup.card_map_of_injective hιinj,
      Subgroup.map_comap_eq_self hle,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have := hA
  obtain ⟨c, hc⟩ := hconjT A (IsElementaryAbelian.isPGroup p A)
  have hle : A.map (MulAut.conj c).toMonoidHom ≤ threeSixFixedTorsion K Ω σ Fr ε p g := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, hux⟩ := hc ⟨x, hx, rfl⟩
    refine ⟨u, ⟨hu, ?_⟩, hux⟩
    have h1 : (MulAut.conj c).toMonoidHom x ^ p = 1 := by
      rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian x hx, map_one]
    have h2 : g * u ^ p * g⁻¹ = 1 := by
      have h3 : (MulAut.conj g).toMonoidHom (u ^ p) = 1 := by
        rw [map_pow, hux, ← map_pow, h1, map_one]
      exact h3
    calc u ^ p = g⁻¹ * (g * u ^ p * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h2]
      _ = 1 := by group
  have : Finite (threeSixFixedTorsion K Ω σ Fr ε p g) :=
    Nat.finite_of_card_ne_zero (by rw [hcardTpC]; exact pow_ne_zero _ hp.ne_zero)
  have hAeq : A.map (MulAut.conj c).toMonoidHom = threeSixFixedTorsion K Ω σ Fr ε p g := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcardTpC, Subgroup.card_map_of_injective (MulAut.conj c).injective, hAcard]
  have htransport : ∀ N : Subgroup (ModGL TwistTag.D4.tag Ω), N ≤ threeSixTorsion Ω Fr ε p →
      ((N.map (MulAut.conj g).toMonoidHom).comap (threeSixEmb K Ω σ)).map
          (MulAut.conj c⁻¹).toMonoidHom ≤ A ∧
        Nat.card ↥(((N.map (MulAut.conj g).toMonoidHom).comap (threeSixEmb K Ω σ)).map
          (MulAut.conj c⁻¹).toMonoidHom) = Nat.card N := by
    intro N hN
    have hNι : N.map (MulAut.conj g).toMonoidHom ≤ (threeSixEmb K Ω σ).range :=
      (Subgroup.map_mono (hN.trans (threeSixTorsion_le Fr ε p))).trans hTcι
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      have hyTp : y ∈ threeSixFixedTorsion K Ω σ Fr ε p g :=
        Subgroup.comap_mono (Subgroup.map_mono hN) hy
      rw [← hAeq] at hyTp
      obtain ⟨x, hx, rfl⟩ := hyTp
      change c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ ∈ A
      rw [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group]
      exact hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective,
        ← Subgroup.card_map_of_injective hιinj, Subgroup.map_comap_eq_self hNι,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hcy : ∀ y, c * (MulAut.conj c⁻¹).toMonoidHom y * c⁻¹ = y := fun y => by
    change c * (c⁻¹ * y * c⁻¹⁻¹) * c⁻¹ = y
    group
  have hconj_eq : ∀ {h h' : ModGL TwistTag.D4.tag Ω}, g * h * g⁻¹ = g * h' * g⁻¹ → h = h' :=
    fun h => by simpa using h
  refine ⟨c, hAeq, ?_, ?_⟩
  ·
    obtain ⟨hsA, hsc⟩ := htransport (threeSixLine Ω Fr ε p 0) inf_le_left
    refine ⟨_, hsA, hsc.trans (hcardL 0), ?_⟩
    rintro _ ⟨y, hy, rfl⟩ a ha
    rw [hcy] at ha
    obtain ⟨h, hh, hhy⟩ := hy
    have hha : h = rootDiagUnit TwistTag.D4.tag a := hconj_eq (hhy.trans ha)
    rw [hha] at hh
    obtain ⟨-, b, hb, hba⟩ := hh
    have hab : b = a := rootDiagUnit_injective hba
    rw [hab] at hb
    exact ⟨threeSixU 0, (isRootComponent_trialitySigma 0).isRoot _ (threeSixU_mem 0),
      hb _ (threeSixU_mem 0)⟩
  ·
    have hpos : (p - 3 : ℕ) ≠ 0 := by omega
    rw [← hcount] at hpos
    obtain ⟨N, hNle, hNcard, hNne⟩ := Set.nonempty_of_ncard_ne_zero hpos
    obtain ⟨hrA, hrc⟩ := htransport N hNle
    refine ⟨_, hrA, hrc.trans hNcard, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ hy1 a ha
    rw [hcy] at ha
    obtain ⟨h, hh, hhy⟩ := hy
    have hha : h = rootDiagUnit TwistTag.D4.tag a := hconj_eq (hhy.trans ha)
    have hh1 : h ≠ 1 := by
      rintro rfl
      apply hy1
      have hy' : threeSixEmb K Ω σ y = threeSixEmb K Ω σ 1 := by
        rw [← hhy, map_one, map_one]
      rw [hιinj hy', map_one]
    rw [hha] at hh hh1
    refine (hsurv a (hNle hh) hh1).2 fun i hi => hNne i ?_
    exact eq_of_mem_of_card_eq_prime hp hNcard (hcardL i) hh hi hh1

end CFSG.RankThree.Chevalley
