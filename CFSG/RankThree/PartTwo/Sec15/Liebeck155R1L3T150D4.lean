module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150NP
import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
import CFSG.RankThree.Chevalley.SteinbergBTTrialityCanonicalField
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2
import CFSG.Timmesfeld.Orders.Bang
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Timmesfeld

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

private theorem exists_pow_sq_eq_one {G : Type*} [Group G] {t : G} {m : ℕ} (htm : t ^ 2 ^ m = 1)
    (ht1 : t ≠ 1) : ∃ i : ℕ, (t ^ i) ^ 2 = 1 ∧ t ^ i ≠ 1 := by
  induction m with
  | zero =>
    rw [pow_zero, pow_one] at htm
    exact absurd htm ht1
  | succ m ih =>
    by_cases h : t ^ 2 ^ m = 1
    · exact ih h
    · refine ⟨2 ^ m, ?_, h⟩
      rw [← pow_mul, ← pow_succ]
      exact htm

private theorem mulAut_pow_apply_of_apply_eq {G : Type*} [Group G] {t : MulAut G} {x : G}
    (hx : t x = x) (i : ℕ) : (t ^ i) x = x := by
  induction i with
  | zero => rw [pow_zero, MulAut.one_apply]
  | succ i ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

private theorem exists_prime_dvd_linear_not_dvd_triality {e : ℕ} (he : 1 ≤ e) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ (2 ^ (2 * e)) ^ 3 * (((2 ^ (2 * e)) ^ 2 - 1) * ((2 ^ (2 * e)) ^ 3 - 1))
      ∧ ¬ ℓ ∣ 3 ∧ ¬ ℓ ∣ (2 ^ e) ^ 12 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 6 - 1) *
        ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) := by
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimitivePrimeDivisor (k := 4 * e) (by omega) (by omega)
  have hk : 0 < 4 * e := by omega
  have hp := hℓ.prime
  have hd : ℓ ∣ 2 ^ (4 * e) - 1 := hℓ.dvd
  have hq : (2 ^ (2 * e)) ^ 2 = 2 ^ (4 * e) := by rw [← pow_mul]; congr 1; ring
  have h3 : ¬ ℓ ∣ 3 := fun h => by have := hℓ.eq_two_of_dvd_three hk h; omega
  have h2 : ¬ ℓ ∣ 2 ^ e := fun h => by
    have := hp.dvd_of_dvd_pow h
    have h2' := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
    exact hℓ.ne_two hk h2'
  refine ⟨ℓ, hp, ?_, h3, ?_⟩
  · refine Dvd.dvd.mul_left (Dvd.dvd.mul_right ?_ _) _
    rw [hq]
    exact hd
  · intro h
    rcases hp.dvd_mul.1 h with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · rcases hp.dvd_mul.1 h with h | h
        · exact h2 (hp.dvd_of_dvd_pow h)
        ·
          rw [← pow_mul, show e * 2 = 2 * e by ring] at h
          have := (hℓ.dvd_sub_one_iff hk (2 * e)).1 h
          have := Nat.le_of_dvd (by omega) this
          omega
      · rw [← pow_mul, show e * 6 = 6 * e by ring] at h
        have := (hℓ.dvd_sub_one_iff hk (6 * e)).1 h
        obtain ⟨c, hc⟩ := this
        have h6 : 6 * e = (4 * c) * e := by rw [hc]; ring
        have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < e) h6
        omega
    ·
      have hX : (2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1 = (2 ^ (4 * e) - 1) * (2 ^ (4 * e) + 2) + 3 := by
        have h1 : 1 ≤ 2 ^ (4 * e) := Nat.one_le_two_pow
        have e8 : (2 ^ e) ^ 8 = (2 ^ (4 * e)) ^ 2 := by rw [← pow_mul, ← pow_mul]; congr 1; ring
        have e4 : (2 ^ e) ^ 4 = 2 ^ (4 * e) := by rw [← pow_mul]; congr 1; ring
        rw [e8, e4]
        generalize 2 ^ (4 * e) = X at h1 ⊢
        obtain ⟨Y, rfl⟩ : ∃ Y, X = Y + 1 := ⟨X - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      rw [hX] at h
      have h' : ℓ ∣ 3 := (Nat.dvd_add_right (Dvd.dvd.mul_right hd _)).1 h
      exact h3 h'


private theorem card_eqLocus_of_conj
    {e : ℕ} (he : 1 ≤ e) (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ (6 * e))
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ (2 * e))) (δ : F ≃+* F)
    (hδ : ∀ c, δ c = c ^ (2 ^ (3 * e)))
    (α ψ : MulAut (LieType.Chevalley.graphFixedRootGroup Blueprint.Chevalley.TwistTag.D4 F
      σ.toRingHom))
    (hψ : ψ * α * ψ⁻¹ = LieType.Chevalley.fieldActor σ δ) :
    Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id (LieType.Chevalley.graphFixedRootGroup
      Blueprint.Chevalley.TwistTag.D4 F σ.toRingHom))) =
      (2 ^ e) ^ 12 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 6 - 1) *
        ((2 ^ e) ^ 8 + (2 ^ e) ^ 4 + 1) := by
  obtain ⟨-, -, hcard₀, hres, -, -, hfixJ, hJs, -⟩ :=
    RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      (m := 2) Nat.prime_two he le_rfl (by norm_num) F (by rw [hF]; ring_nf) σ
      (fun c => by rw [hσ]; ring_nf) δ hδ
  set E := (LieType.Chevalley.fieldActor σ δ).toMonoidHom.eqLocus
    (MonoidHom.id (LieType.Chevalley.graphFixedRootGroup Blueprint.Chevalley.TwistTag.D4 F
      σ.toRingHom)) with hE
  have hmap := LocalAnalysis.SteinbergBM.map_eqLocus_mulAut_conj ψ α
  rw [hψ] at hmap
  let eα : α.toMonoidHom.eqLocus (MonoidHom.id (LieType.Chevalley.graphFixedRootGroup
      Blueprint.Chevalley.TwistTag.D4 F σ.toRingHom)) ≃* E :=
    ((α.toMonoidHom.eqLocus (MonoidHom.id (LieType.Chevalley.graphFixedRootGroup
      Blueprint.Chevalley.TwistTag.D4 F σ.toRingHom))).equivMapOfInjective _ ψ.injective).trans
        (MulEquiv.subgroupCongr hmap)
  let eJ : E ≃* LieType.Chevalley.trialityFieldImage σ δ :=
    (E.equivMapOfInjective _ (LieType.Chevalley.graphFixedRootGroup
      Blueprint.Chevalley.TwistTag.D4 F σ.toRingHom).subtype_injective).trans
        (MulEquiv.subgroupCongr hfixJ)
  have hcardS : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id (LieType.Chevalley.graphFixedRootGroup
      Blueprint.Chevalley.TwistTag.D4 F σ.toRingHom))) =
      Nat.card (LieType.Chevalley.trialityFieldImage σ δ) :=
    Nat.card_congr (eα.trans eJ).toEquiv
  have hσ₀ : ∀ c : LieType.Chevalley.fixSubfield δ,
      (LieType.Chevalley.fixSubfieldRestrict σ δ).toRingHom c = c ^ ((2 ^ e) ^ 2) :=
    fun c => Subtype.ext (by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hres, hσ, SubmonoidClass.coe_pow,
        ← pow_mul, mul_comm 2 e])
  obtain ⟨hJcard, -, -⟩ := LieType.Chevalley.triality_both_orientations_exact_finite_order 2 e
    Nat.prime_two he (LieType.Chevalley.fixSubfield δ) (by rw [hcard₀, ← pow_mul, mul_comm]) 2
    (Or.inr rfl) (LieType.Chevalley.fixSubfieldRestrict σ δ).toRingHom hσ₀
  rw [hcardS, LieType.Chevalley.trialityFieldImage,
    Subgroup.card_map_of_injective (LieType.Chevalley.baseChangeGL_injective _), hJcard]

private theorem two_pow_two_mul_mod_three (e : ℕ) : 2 ^ (2 * e) % 3 = 1 := by
  rw [pow_mul]
  norm_num [Nat.pow_mod]

theorem noTwoCentAut_of_survD4
    {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {K : Subgroup S} (hKs : IsSimpleGroup ↥K) (h : SurvD4 S σ K) : NoTwoCentAut K := by
  have hNP := noTwoNormalized_of_survD4 hKs h
  obtain ⟨n, hn, hK, hm, -⟩ := h
  have hnc := not_commutative_of_isoLThreePi hKs hn hK
  obtain ⟨F, _, _, _, σF, hF, hσF, hσ3, hf1, hsimp, ⟨φ⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hm
  intro t ⟨m, htm⟩ htK
  by_contra ht1
  obtain ⟨i, hi2, hi1⟩ := exists_pow_sq_eq_one htm ht1
  have hi : ∀ k ∈ K, (t ^ i) k = k := fun k hk => mulAut_pow_apply_of_apply_eq (htK k hk) i
  by_cases hin : KFacts.IsInnerAut (t ^ i)
  ·
    obtain ⟨s, hs⟩ := hin
    have hsimpS : IsSimpleGroup S := φ.isSimpleGroup
    have hZ : Subgroup.center S = ⊥ := by
      rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h0 | h0
      · exact h0
      · exfalso
        refine hnc fun a b => ?_
        have ha : (a : S) ∈ Subgroup.center S := h0 ▸ Subgroup.mem_top _
        exact Subtype.ext (Subgroup.mem_center_iff.1 ha b).symm
    have hs2 : s ^ 2 = 1 := by
      have h1 : (MulAut.conj s) ^ 2 = 1 := by rw [hs]; exact hi2
      have h2 : MulAut.conj (s ^ 2) = 1 := by rw [map_pow]; exact h1
      have h3 : s ^ 2 ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h4 := congrArg (fun f : MulAut S => f g) h2
        simp only [MulAut.conj_apply, MulAut.one_apply] at h4
        calc g * s ^ 2 = (s ^ 2 * g * (s ^ 2)⁻¹) * s ^ 2 := by rw [h4]
          _ = s ^ 2 * g := by group
      rw [hZ] at h3
      exact Subgroup.mem_bot.1 h3
    have hks : ∀ k ∈ K, k * s * k⁻¹ = s := fun k hk => by
      have h1 := hi k hk
      rw [← hs] at h1
      have h2 : s * k * s⁻¹ = k := by simpa [MulAut.conj_apply] using h1
      have h3 : k * s = s * k := calc
        k * s = (s * k * s⁻¹) * s := by rw [h2]
        _ = s * k := by group
      rw [h3]
      group
    have hW2 : IsPGroup 2 (Subgroup.zpowers s) := by
      rw [IsPGroup.iff_card, Nat.card_zpowers]
      have h1 : orderOf s ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one hs2
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
      exact ⟨j, hj⟩
    have hKW : ∀ k ∈ K, ∀ w ∈ Subgroup.zpowers s, k * w * k⁻¹ ∈ Subgroup.zpowers s := by
      intro k hk w hw
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      rw [← conj_zpow, hks k hk]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) j
    have hs1 : s = 1 := by
      have h1 : s ∈ Subgroup.zpowers s := Subgroup.mem_zpowers s
      rw [hNP _ hW2 hKW] at h1
      exact Subgroup.mem_bot.1 h1
    exact hi1 (by rw [← hs, hs1, map_one])
  ·
    set α : MulAut (LieType.Chevalley.graphFixedRootGroup Blueprint.Chevalley.TwistTag.D4 F
      σF.toRingHom) := MulAut.congr φ (t ^ i) with hα
    have hα2 : α ^ 2 = 1 := by rw [hα, ← map_pow, hi2, map_one]
    have hαo : α ∉ ComponentClassification.OuterAutomorphisms.inner _ := fun hmem =>
      hin ((KFacts.isInnerAut_congr φ (t ^ i)).1 hmem)
    obtain ⟨hev, δ, hδc, -, ψ, hψ, -⟩ :=
      LieType.Chevalley.even_triality_outer_involutions_canonical_field hf1 F hF σF hσF α hα2 hαo
    obtain ⟨e, he⟩ := hev
    have he2 : n = 2 * e := by omega
    subst he2
    have he1 : 1 ≤ e := by omega
    have hF' : Nat.card F = 2 ^ (6 * e) := by
      rw [hF, ← pow_mul]
      congr 1
      omega
    have hδ : ∀ c, δ c = c ^ (2 ^ (3 * e)) := fun c => by
      rw [hδc c]
      congr 2
      omega
    have hcard := card_eqLocus_of_conj he1 F hF' σF hσF δ hδ α ψ hψ
    let ι : ↥K →* ↥(α.toMonoidHom.eqLocus (MonoidHom.id (LieType.Chevalley.graphFixedRootGroup
        Blueprint.Chevalley.TwistTag.D4 F σF.toRingHom))) :=
      (φ.toMonoidHom.comp K.subtype).codRestrict _ (fun k => by
        change α (φ k) = φ k
        rw [hα, MulAut.congr_apply]
        change φ ((t ^ i) (φ.symm (φ k))) = φ k
        rw [MulEquiv.symm_apply_apply, hi k k.2])
    have hι : Function.Injective ι := fun a b hab =>
      Subtype.ext (φ.injective (congrArg Subtype.val hab))
    have hdvd := Subgroup.card_dvd_of_injective ι hι
    rcases hK with ⟨-, ⟨eK⟩⟩ | ⟨hmod, -⟩
    · have hq : Nat.card (GaloisField 2 (2 * e)) = 2 ^ (2 * e) :=
        GaloisField.card 2 (2 * e) (by omega)
      have hk := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 (2 * e))
      rw [hq, ← Nat.card_congr eK.toEquiv] at hk
      obtain ⟨ℓ, hℓ, hℓK, hℓ3, hℓJ⟩ := exists_prime_dvd_linear_not_dvd_triality he1
      have h1 : ℓ ∣ Nat.card ↥K * Nat.gcd 3 (2 ^ (2 * e) - 1) := hk ▸ hℓK
      rcases hℓ.dvd_mul.1 h1 with h2 | h2
      · exact hℓJ (hcard ▸ h2.trans hdvd)
      · exact hℓ3 (h2.trans (Nat.gcd_dvd_left _ _))
    · have := two_pow_two_mul_mod_three e
      omega

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150
