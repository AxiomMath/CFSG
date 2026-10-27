module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KE CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  Subgroup
open scoped MatrixGroups Pointwise commutatorElement

theorem map_SL2_injective {F E : Type} [Field F] [Field E] (φ : F →+* E) :
    Function.Injective (Matrix.SpecialLinearGroup.map φ : SL2 F →* SL2 E) := by
  intro X Y h
  refine Subtype.ext (Matrix.ext fun i j => φ.injective ?_)
  exact congrArg (fun W : SL2 E => (W : Matrix (Fin 2) (Fin 2) E) i j) h

theorem HSL_pow_units {L : Type} [Field L] (μ : Lˣ) (n : ℕ) :
    (HSL μ : SL2 L) ^ n = HSL (μ ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, HSL_units_one]
  | succ n ih => rw [pow_succ, ih, HSL_mul_units, pow_succ]

theorem eq_one_of_HSL_eq_one {L : Type} [Field L] {μ : Lˣ} (h : (HSL μ : SL2 L) = 1) : μ = 1 := by
  have h00 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 0 0) h
  simp only [coe_HSL, Matrix.SpecialLinearGroup.coe_one] at h00
  exact Units.ext (by simpa using h00)


theorem thetaPair_le_adjointGroup (L : Type) [Field L] :
    thetaPair L ≤ adjointGroup TwistTag.D4.tag L :=
  sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)

theorem pinnedX_theta_eq_commutator {L : Type} [Field L] {μ : Lˣ} (hμ : (μ : L) ^ 2 ≠ 1)
    {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : γ = thetaVec ∨ γ = -thetaVec) (c : L) :
    ∃ c' : L, pinnedX TwistTag.D4.tag L γ c =
      ⁅rootDiagUnit TwistTag.D4.tag (Pi.mulSingle n2 μ), pinnedX TwistTag.D4.tag L γ c'⁆ := by
  have hθ : IsRoot TwistTag.D4.tag thetaVec := by
    rw [← wordVec_theta, ← KS11Lie5Proof.wordProd_smul]
    exact IsRoot.smul (isRoot_single _ n2) _
  have hγr : IsRoot TwistTag.D4.tag γ := by
    rcases hγ with rfl | rfl
    · exact hθ
    · exact IsRoot.neg hθ
  have hchar : ((rootChar (Pi.mulSingle n2 μ) γ : Lˣ) : L) - 1 ≠ 0 := by
    have hm0 : (μ : L) ≠ 0 := Units.ne_zero μ
    have e : rootChar (Pi.mulSingle n2 μ) γ = μ ^ γ n2 := by
      rw [rootChar, Finset.prod_eq_single n2 (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj,
        _root_.one_zpow]) (by simp), Pi.mulSingle_eq_same]
    rw [e]
    rcases hγ with rfl | rfl
    · have : (thetaVec : Fin TwistTag.D4.tag.rank → ℤ) n2 = 2 := rfl
      rw [this, zpow_ofNat, Units.val_pow_eq_pow_val]
      exact sub_ne_zero.2 hμ
    · have : (-thetaVec : Fin TwistTag.D4.tag.rank → ℤ) n2 = -2 := rfl
      rw [this, _root_.zpow_neg, zpow_ofNat, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      intro h
      apply hμ
      have h1 : ((μ : L) ^ 2)⁻¹ = 1 := sub_eq_zero.1 h
      rw [inv_eq_one] at h1
      exact h1
  refine ⟨c / (((rootChar (Pi.mulSingle n2 μ) γ : Lˣ) : L) - 1), ?_⟩
  rw [commutatorElement_def, rootDiagUnit_conj_pinnedX _ hγr, pinnedX_neg,
    ← pinnedX_add]
  congr 1
  field_simp
  ring

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {σ : K ≃+* K}

theorem exists_short_conj_of_three (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hyS : y ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) {k : ℕ} (hk : y ^ 3 ^ k = 1)
    (hy3 : y ^ 3 ≠ 1) :
    ∃ (P : SL2 L) (μ : Lˣ), 9 ∣ orderOf μ ∧
      triEmb K σ L y = outerTriple L (frobTriple Fr P) *
        rootDiagUnit TwistTag.D4.tag (fun j => μ ^ shortExp ((ℓ ^ f : ℕ) : ℤ) j) *
          (outerTriple L (frobTriple Fr P))⁻¹ := by
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ] using this
  have hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c) := fun c => by
    rw [hσ, hFr, map_pow]
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨B, hB'⟩ := hyS
  have hB : orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer B =
      (y : ModGL TwistTag.D4.tag K) := hB'
  have hinj := orbitRankOneHom_injective_D4 hσ3 KS11Lie4Proof.d4Outer
  have hBk : B ^ 3 ^ k = 1 := hinj (by
    rw [map_pow, hB, map_one, ← Subgroup.coe_pow, hk, Subgroup.coe_one])
  have hB3 : B ^ 3 ≠ 1 := fun h => hy3 (Subtype.ext (by
    rw [Subgroup.coe_pow, ← hB, ← map_pow, h, map_one, Subgroup.coe_one]))
  set B₀ := Matrix.SpecialLinearGroup.map (outerEmb K σ L) B with hB₀
  have hB₀k : B₀ ^ 3 ^ k = 1 := by rw [hB₀, ← map_pow, hBk, map_one]
  have hB₀3 : B₀ ^ 3 ≠ 1 := fun h => hB3 (map_SL2_injective (outerEmb K σ L) (by
    rw [map_pow, ← hB₀, h, map_one]))
  obtain ⟨P, D, hD, hPD⟩ := exists_conj_diag_two (n := 3 ^ k)
    (by push_cast; exact pow_ne_zero _ h3L) B₀ hB₀k
  obtain ⟨μ, rfl⟩ := eq_HSL_of_diag hD
  have hpow : ∀ n : ℕ, B₀ ^ n = P * HSL (μ ^ n) * P⁻¹ := fun n => by
    rw [hPD, conj_pow, HSL_pow_units]
  have hμk : μ ^ 3 ^ k = 1 := by
    apply eq_one_of_HSL_eq_one (L := L)
    have h := hpow (3 ^ k)
    rw [hB₀k] at h
    calc HSL (μ ^ 3 ^ k) = P⁻¹ * (P * HSL (μ ^ 3 ^ k) * P⁻¹) * P := by group
      _ = 1 := by rw [← h]; group
  have hμ3 : μ ^ 3 ≠ 1 := fun h => hB₀3 (by rw [hpow, h, HSL_units_one, mul_one, mul_inv_cancel])
  have h9 : 9 ∣ orderOf μ := by
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hμk)
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · exfalso
      apply hμ3
      apply orderOf_dvd_iff_pow_eq_one.1
      rw [hjeq]
      interval_cases j <;> norm_num
    · rw [hjeq]
      exact (pow_dvd_pow 3 hj2 : 3 ^ 2 ∣ 3 ^ j)
  exact ⟨P, μ, h9, triEmb_short_eq_conj hcomm hFr hB hPD⟩

theorem commutator_centralizer_eq (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hyS : y ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) {k : ℕ} (hk : y ^ 3 ^ k = 1)
    (hy3 : y ^ 3 ≠ 1) :
    ⁅adjointGroup TwistTag.D4.tag L ⊓ centralizer {triEmb K σ L y},
      adjointGroup TwistTag.D4.tag L ⊓ centralizer {triEmb K σ L y}⁆ = thetaPair L := by
  have hℓ : ℓ.Prime := Fact.out
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  obtain ⟨P, μ, h9, hy⟩ := exists_short_conj_of_three hf hℓ3 hK hσ L hFr hyS hk hy3
  set X := outerTriple L (frobTriple Fr P) with hX
  set C' := adjointGroup TwistTag.D4.tag L ⊓ centralizer {triEmb K σ L y} with hC'
  have hXr : ∀ r ∈ thetaPair L, X * r * X⁻¹ = r := fun r hr => by
    rw [commute_outerTriple_of_mem_thetaPair _ hr, mul_inv_cancel_right]
  have hRC : thetaPair L ≤ C' := by
    intro r hr
    refine mem_inf.2 ⟨thetaPair_le_adjointGroup L hr, mem_centralizer_singleton_iff.2 ?_⟩
    obtain ⟨Y, hY⟩ := exists_triEmb_eq_outerTriple (L := L) hyS
    rw [hY]
    exact (commute_outerTriple_of_mem_thetaPair Y hr).symm
  refine le_antisymm ?_ ?_
  ·
    rw [commutator_le]
    intro a ha b hb
    have hconj : ∀ w ∈ C', X⁻¹ * w * X ∈ (torusGroup TwistTag.D4.tag L :
        Set (ModGL TwistTag.D4.tag L)) * (thetaPair L : Set (ModGL TwistTag.D4.tag L)) := by
      intro w hw
      obtain ⟨hwG, hwc⟩ := mem_inf.1 hw
      rw [mem_centralizer_singleton_iff] at hwc
      have hmem : X⁻¹ * w * X ∈
          toralCentralizer TwistTag.D4.tag L (fun j => μ ^ shortExp ((ℓ ^ f : ℕ) : ℤ) j) := by
        rw [mem_toralCentralizer]
        refine ⟨mul_mem (mul_mem (inv_mem (outerTriple_mem_adjointGroup _)) hwG)
          (outerTriple_mem_adjointGroup _), ?_⟩
        have h1 : rootDiagUnit TwistTag.D4.tag (fun j => μ ^ shortExp ((ℓ ^ f : ℕ) : ℤ) j) =
            X⁻¹ * triEmb K σ L y * X := by rw [hy]; group
        rw [h1]
        calc X⁻¹ * triEmb K σ L y * X * (X⁻¹ * w * X) * (X⁻¹ * triEmb K σ L y * X)⁻¹ =
            X⁻¹ * (triEmb K σ L y * w) * (triEmb K σ L y)⁻¹ * X := by group
          _ = X⁻¹ * w * X := by rw [← hwc]; group
      have h2 := toralCentralizer_short_le (q := ℓ ^ f) hq3 h9 hmem
      rwa [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
        (torusGroup_le_normalizer_thetaPair L)] at h2
    have hc := commutator_mem_of_mem_mul (torusGroup_le_normalizer_thetaPair L)
      (fun a ha b hb => torusGroup_mul_comm ha hb) (hconj a ha) (hconj b hb)
    have e : ⁅a, b⁆ = X * ((X⁻¹ * a * X) * (X⁻¹ * b * X) * (X⁻¹ * a * X)⁻¹ *
        (X⁻¹ * b * X)⁻¹) * X⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e, hXr _ hc]
    exact hc
  ·
    have hμ2 : (μ : L) ^ 2 ≠ 1 := by
      intro h
      have h2 : μ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      have := Nat.le_of_dvd (by norm_num) (h9.trans (orderOf_dvd_of_pow_eq_one h2))
      omega
    have hd : rootDiagUnit TwistTag.D4.tag (Pi.mulSingle n2 μ) ∈ C' :=
      hRC (rootDiagUnit_mulSingle_mem_thetaPair μ)
    have hγ : ∀ γ : Fin TwistTag.D4.tag.rank → ℤ, (γ = thetaVec ∨ γ = -thetaVec) →
        rootSubgroup TwistTag.D4.tag L γ ≤ ⁅C', C'⁆ := by
      intro γ hγ
      rw [rootSubgroup, closure_le]
      rintro _ ⟨c, rfl⟩
      obtain ⟨c', hc'⟩ := pinnedX_theta_eq_commutator hμ2 hγ c
      rw [SetLike.mem_coe, hc']
      refine commutator_mem_commutator hd (hRC ?_)
      rcases hγ with rfl | rfl
      · exact mem_sup_left (subset_closure ⟨c', rfl⟩)
      · exact mem_sup_right (subset_closure ⟨c', rfl⟩)
    exact sup_le (hγ _ (Or.inl rfl)) (hγ _ (Or.inr rfl))

theorem conj_mem_thetaPair (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {y₁ y₂ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hy₁S : y₁ ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) {k₁ : ℕ} (hk₁ : y₁ ^ 3 ^ k₁ = 1)
    (hy₁3 : y₁ ^ 3 ≠ 1) (hy₂S : y₂ ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom) {k₂ : ℕ}
    (hk₂ : y₂ ^ 3 ^ k₂ = 1) (hy₂3 : y₂ ^ 3 ≠ 1)
    {g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hg : g * y₁ * g⁻¹ = y₂)
    {r : ModGL TwistTag.D4.tag L} (hr : r ∈ thetaPair L) :
    triEmb K σ L g * r * (triEmb K σ L g)⁻¹ ∈ thetaPair L := by
  rw [← commutator_centralizer_eq hf hℓ3 hK hσ L hFr hy₁S hk₁ hy₁3] at hr
  rw [← commutator_centralizer_eq hf hℓ3 hK hσ L hFr hy₂S hk₂ hy₂3]
  set φ := (MulAut.conj (triEmb K σ L g)).toMonoidHom with hφ
  have hle : (adjointGroup TwistTag.D4.tag L ⊓ centralizer {triEmb K σ L y₁}).map φ ≤
      adjointGroup TwistTag.D4.tag L ⊓ centralizer {triEmb K σ L y₂} := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hwG, hwc⟩ := mem_inf.1 hw
    rw [mem_centralizer_singleton_iff] at hwc
    refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
    · exact mul_mem (mul_mem (triEmb_mem_adjointGroup g) hwG) (inv_mem (triEmb_mem_adjointGroup g))
    · rw [← hg, map_mul, map_mul, map_inv]
      change triEmb K σ L g * w * (triEmb K σ L g)⁻¹ *
          (triEmb K σ L g * triEmb K σ L y₁ * (triEmb K σ L g)⁻¹) =
        triEmb K σ L g * triEmb K σ L y₁ * (triEmb K σ L g)⁻¹ *
          (triEmb K σ L g * w * (triEmb K σ L g)⁻¹)
      calc triEmb K σ L g * w * (triEmb K σ L g)⁻¹ *
            (triEmb K σ L g * triEmb K σ L y₁ * (triEmb K σ L g)⁻¹) =
          triEmb K σ L g * (w * triEmb K σ L y₁) * (triEmb K σ L g)⁻¹ := by group
        _ = triEmb K σ L g * (triEmb K σ L y₁ * w) * (triEmb K σ L g)⁻¹ := by rw [hwc]
        _ = _ := by group
  have h1 : φ r ∈ (⁅adjointGroup TwistTag.D4.tag L ⊓ centralizer {triEmb K σ L y₁},
      adjointGroup TwistTag.D4.tag L ⊓ centralizer {triEmb K σ L y₁}⁆).map φ :=
    mem_map_of_mem φ hr
  rw [map_commutator] at h1
  exact commutator_mono hle hle h1

theorem d4NormCent_holds : KS11Lie4Proof.D4NormCent := by
  intro K _ _ q σ hK hσ h3 y hyS hyk hy3 g hg
  obtain ⟨ℓ, f, hℓ, hf, rfl⟩ := exists_prime_pow_of_card_eq_cube hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    exact h3 (dvd_pow_self 3 (by omega))
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K with hL
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨k, hk⟩ := hyk
  set y' := g * y * g⁻¹ with hy'
  have hy'S : y' ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
    (zpowers_le.2 hyS) hg
  have hy'k : y' ^ 3 ^ k = 1 := by rw [hy', conj_pow, hk, mul_one, mul_inv_cancel]
  have hy'3 : y' ^ 3 ≠ 1 := by
    rw [hy', conj_pow]
    intro h
    apply hy3
    calc y ^ 3 = g⁻¹ * (g * y ^ 3 * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hg' : g⁻¹ * y' * g⁻¹⁻¹ = y := by rw [hy']; group
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    apply mem_centralizer_of_triEmb_mem (L := L)
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_thetaPair hf hℓ3 hK hσ L hFr hyS hk hy3 hy'S hy'k hy'3 rfl
      (triEmb_mem_thetaPair_of_mem_centralizer hf hℓ3 hK hσ L hFr hn)
  · intro hn
    apply mem_centralizer_of_triEmb_mem (L := L)
    have h1 := conj_mem_thetaPair hf hℓ3 hK hσ L hFr hy'S hy'k hy'3 hyS hk hy3 hg'
      (triEmb_mem_thetaPair_of_mem_centralizer hf hℓ3 hK hσ L hFr hn)
    have e : triEmb K σ L n = triEmb K σ L g⁻¹ * triEmb K σ L (g * n * g⁻¹) *
        (triEmb K σ L g⁻¹)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact h1

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
