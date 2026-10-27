module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528
public import CFSG.Quasithin.Vol2.Ch1EightFourMain
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.Ch1Four

@[expose] def F4SzParabolicFact : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (X P B : Subgroup Q) (f : ℕ), Is2F4 f ↥X →
    IsParabolic2 X P → B = perfectCore P → IsSz f (ModO2 B) →
      (2 ^ f) ^ 10 ≤ Nat.card (CFSG.pCore 2 ↥B)

theorem card_sz_open (a : ℕ) :
    Nat.card (CFSG.Open.Sz a) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  rw [Nat.card_congr e.toEquiv,
    CFSG.LieType.Ree.suzuki_order (GaloisField.card 2 (2 * a + 1) (by omega))]

theorem eq_of_card_sz_eq {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) =
      (2 ^ g) ^ 2 * (2 ^ g - 1) * ((2 ^ g) ^ 2 + 1)) : f = g := by
  have ho : ∀ k, 1 ≤ k → Odd ((2 ^ k - 1) * ((2 ^ k) ^ 2 + 1)) := by
    intro k hk
    have hev : Even (2 ^ k) := (Nat.even_pow' (by omega)).mpr even_two
    exact (Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one).mul
      ((Nat.even_pow' two_ne_zero).mpr hev).add_one
  have e : 2 ^ (2 * f) * ((2 ^ f - 1) * ((2 ^ f) ^ 2 + 1)) =
      2 ^ (2 * g) * ((2 ^ g - 1) * ((2 ^ g) ^ 2 + 1)) := by
    rw [mul_comm 2 f, mul_comm 2 g, pow_mul, pow_mul, ← mul_assoc, ← mul_assoc, h]
  have := (two_pow_mul_odd_inj (ho f hf) (ho g hg) e).1
  omega

theorem stmt5_2_8_Sz_of
    (h526 : Stmt5_2_6) (h312 : A312ForSQTK)
    (hF4 : F4SzParabolicFact) : Stmt5_2_8_Sz := by
  intro G _ _ T M L V H B D L₂ n hyp hc Kh hlt hKh
  obtain ⟨-, -, -, ⟨a, hna, ⟨eSz⟩⟩, hQ10⟩ := hc
  have h := hyp.toHyp5_0_1
  obtain ⟨-, hL₂K, -⟩ := h526 G T M L V H B D L₂ n hyp
  have hKloc : quasithinIsLocal T (oTwoUpper H) := hyp.isLocal_oTwoUpper hL₂K
  have hTN : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  set K := oTwoUpper H with hKdef
  have hS : IsSylowTwoOf T (Kh ⊔ T) := ⟨le_sup_right, hKh.1.1, hKh.1.2.2.1⟩
  have hBH : K ≤ (Kh ⊔ T) := hlt.le.trans le_sup_left
  have hB : K ∈ lFamily T := mem_lFamily_of_isLocal hKloc
  obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hBH
  have hKq : Nat.card (ModO2 K) = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) :=
    (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans
      eSz).toEquiv).trans (by rw [card_sz_open, hna])
  have hKO2 : Nat.card (CFSG.pCore 2 ↥K) = (2 ^ n) ^ 10 := by
    rw [← hQ10]
    exact (Subgroup.card_map_of_injective K.subtype_injective).symm
  have hBq : Nat.card (ModO2 (modO2Image (Kh ⊔ T) K)) =
      (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := (Nat.card_congr e.toEquiv).symm.trans hKq
  have h3 : ¬ 3 ∣ Nat.card (ModO2 (modO2Image (Kh ⊔ T) K)) := by
    rw [hBq, hna, show (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) =
      (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1) by ring]
    exact not_three_dvd_sz a
  rcases lemma_1_2_4_list h.qtke h.simple h.nonabelian h312 hKh.1.2.2.2 hS hBH hB
      (cComp_of_isLocal hKh.1) hlt.le with heq | hcase | hnq
  · exact hlt.ne (eq_of_modO2Image_eq hKloc hKh.1 hlt.le heq)
  · rcases init3_of_a312Case hcase with hc3 | hI
    ·
      obtain ⟨f, hSzf, h2F4, P, hP, hKP⟩ := hc3
      have hO2 := hF4 _ _ P _ f h2F4 hP hKP hSzf
      obtain ⟨-, a', -, K', _, _, hf', hK', ⟨e'⟩⟩ := hSzf
      have hBq' : Nat.card (ModO2 (modO2Image (Kh ⊔ T) K)) =
          (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
        rw [Nat.card_congr e'.toEquiv, CFSG.LieType.Ree.suzuki_order (by rw [hK', hf']), hf']
      have hfn : f = n := eq_of_card_sz_eq (by omega) (by omega) (hBq'.symm.trans hBq)
      rw [hfn] at hO2
      have c1 : Nat.card ↥(modO2Image (Kh ⊔ T) K) = Nat.card (ModO2 (modO2Image (Kh ⊔ T) K)) *
          Nat.card (CFSG.pCore 2 ↥(modO2Image (Kh ⊔ T) K)) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      have c2 : Nat.card ↥K = Nat.card (ModO2 K) * Nat.card (CFSG.pCore 2 ↥K) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      set ρ := (QuotientGroup.mk' (CFSG.pCore 2 ↥(Kh ⊔ T))).subgroupMap
        (K.subgroupOf (Kh ⊔ T)) with hρ
      have hsurj : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ _
      have hcardS : Nat.card ↥(K.subgroupOf (Kh ⊔ T)) = Nat.card ↥K :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
      have hcardB : Nat.card ↥(modO2Image (Kh ⊔ T) K) = Nat.card ↥K := by
        refine le_antisymm ((Nat.card_le_card_of_surjective ρ hsurj).trans_eq hcardS) ?_
        rw [c1, c2, hBq, hKq, hKO2]
        exact Nat.mul_le_mul_left _ hO2
      have hinj : Function.Injective ρ :=
        (hsurj.bijective_of_nat_card_le (le_of_eq (hcardS.trans hcardB.symm))).1
      have hbot : K ⊓ pCoreOf 2 (Kh ⊔ T) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxK, hxO⟩ := Subgroup.mem_inf.mp hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxO
        have hyK : y ∈ K.subgroupOf (Kh ⊔ T) := hxK
        have h1 : ρ ⟨y, hyK⟩ = 1 := by
          apply Subtype.ext
          change QuotientGroup.mk' (CFSG.pCore 2 ↥(Kh ⊔ T)) y = 1
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hy
        have h2 : (⟨y, hyK⟩ : ↥(K.subgroupOf (Kh ⊔ T))) = 1 := hinj (h1.trans (map_one ρ).symm)
        have h3 : y = 1 := congrArg Subtype.val h2
        rw [Subgroup.mem_bot, h3]
        rfl
      have hOT : pCoreOf 2 (Kh ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hS
      have hKN : K ≤ Subgroup.normalizer (pCoreOf 2 (Kh ⊔ T) : Set G) :=
        hBH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Kh ⊔ T))
      have hcomm : ∀ x ∈ pCoreOf 2 (Kh ⊔ T), ∀ k ∈ K, x * k = k * x := by
        intro x hx k hk
        have hc1 : x * k * x⁻¹ * k⁻¹ ∈ K :=
          mul_mem ((Subgroup.mem_normalizer_iff.mp (hTN (hOT hx)) k).mp hk) (inv_mem hk)
        have hc2 : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (Kh ⊔ T) := by
          have h1 : k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (Kh ⊔ T) :=
            (Subgroup.mem_normalizer_iff.mp (hKN hk) x⁻¹).mp (inv_mem hx)
          have h2 := mul_mem hx h1
          simpa [mul_assoc] using h2
        have hc : x * k * x⁻¹ * k⁻¹ ∈ K ⊓ pCoreOf 2 (Kh ⊔ T) := Subgroup.mem_inf.mpr ⟨hc1, hc2⟩
        rw [hbot, Subgroup.mem_bot] at hc
        calc x * k = (x * k * x⁻¹ * k⁻¹) * (k * x) := by group
          _ = k * x := by rw [hc, one_mul]
      obtain ⟨S', hS'⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
      have hCT : CharTwo (Kh ⊔ T) := charTwo_of_inH h.qtke.2.1 S'
        ⟨by rw [hS']; exact le_sup_right, hKh.1.2.2.2⟩
      have hKO : K ≤ pCoreOf 2 (Kh ⊔ T) := fun k hk => hCT (Subgroup.mem_inf.mpr
        ⟨hBH hk, Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx k hk⟩)
      apply hKloc.2.1.1
      rw [eq_bot_iff, ← hbot]
      exact le_inf le_rfl hKO
    · exact h3 hI.three_dvd
  · have hperfB : Group.IsPerfect ↥(modO2Image (Kh ⊔ T) K) :=
      Subgroup.isPerfect_iff.mpr (modO2Image_mem_lFamily hS hBH hB).2.1
    have hBL : modO2Image (Kh ⊔ T) K ≤ modO2Image (Kh ⊔ T) Kh :=
      Subgroup.map_mono fun x hx => hlt.le hx
    exact h3 (init3_of_a312Nonquasi hBL hperfB hnq).three_dvd

end CFSG.Quasithin.H13
