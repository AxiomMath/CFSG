module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Quasithin.EmptyFaithful.S1421QA22Main

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace QA23

structure IsL45 (X : Type) [Group X] : Prop where
  simple : IsSimpleGroup X
  nonab : ∃ a b : X, a * b ≠ b * a
  card : Nat.card X = 20160 ∨ Nat.card X = 9999360
  a8 : Nat.card X = 20160 → Nonempty (X ≃* alternatingGroup (Fin 8))

theorem IsL45.of_isPSL {X : Type} [Group X] (h : IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X) : IsL45 X := by
  have hfin : Finite X := by
    rcases h with h | h
    · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel h
    · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel h
  have hsimple : IsSimpleGroup X := by
    rcases h with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 5 2 1 h).2
  have hcard : Nat.card X = 20160 ∨ Nat.card X = 9999360 := by
    rcases h with h | h
    · left
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl]
      decide
    · right
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl]
      decide
  refine ⟨hsimple, ?_, hcard, ?_⟩
  · by_contra hall
    push Not at hall
    have : IsMulCommutative X := ⟨⟨fun a b => hall a b⟩⟩
    have hp := IsSimpleGroup.prime_card (α := X)
    rcases hcard with h | h <;> rw [h] at hp <;> norm_num at hp
  · intro h20160
    rcases h with h | h
    · exact CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
        (Or.inl ⟨by decide, h⟩)
    · exfalso
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl] at h20160
      revert h20160
      decide

@[expose] def FactSporadicOrders : Prop :=
  Nat.card (NativeSporadic.Carrier .M23) = 10200960 ∧
    Nat.card (NativeSporadic.Carrier .J1) = 175560 ∧
    Nat.card (NativeSporadic.Carrier .J2) = 604800 ∧
    Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 ∧
    Nat.card (NativeSporadic.Carrier .HS) = 44352000 ∧
    Nat.card (NativeSporadic.Carrier .Ru) = 145926144000

theorem card_of_isSporadic {X : Type} [Group X] {s : TauCeti.SporadicName} (h : IsSporadic s X) :
    Nat.card X = Nat.card (NativeSporadic.Carrier s) := by
  obtain ⟨e⟩ := h
  exact Nat.card_congr e.toEquiv

theorem IsL45.center_eq_bot {X : Type} [Group X] (hX : IsL45 X) : Subgroup.center X = ⊥ := by
  have := hX.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX.nonab
    apply hab
    exact Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a

theorem IsL45.false_of_isHat {X : Type} [Group X] (hX : IsL45 X) {S : Type} [Group S]
    (h : IsHat X S) : False := by
  have h3 := h.2.1
  rw [hX.center_eq_bot, Subgroup.card_bot] at h3
  omega

theorem no_l2p (N p : ℕ) (hN : N = 20160 ∨ N = 9999360) (h : N * 2 = p * (p ^ 2 - 1)) :
    False := by
  have hp : p < 273 := by
    by_contra hge
    push Not at hge
    have h1 : 273 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hge 2
    have h2 : 273 ^ 2 * p ≤ p ^ 2 * p := Nat.mul_le_mul_right p h1
    have h3 : p * (p ^ 2 - 1) + p = p ^ 2 * p := by
      have : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))
      calc p * (p ^ 2 - 1) + p = p * (p ^ 2 - 1 + 1) := by ring
        _ = p ^ 2 * p := by rw [this]; ring
    rcases hN with rfl | rfl <;> omega
  interval_cases p <;> omega

theorem IsL45.false_of_sl3 {X : Type} [Group X] (hX : IsL45 X) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (h : IsSL3 (2 ^ n) X) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hc : Nat.card X = Nat.card K ^ 3 * (Nat.card K ^ 3 - 1) * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
      CFSG.QuasithinUnique.Bridge.Alt57.card_sl3_field]
  rw [hK] at hc
  rcases hn with rfl | rfl <;> rcases hX.card with h' | h' <;> rw [h'] at hc <;> norm_num at hc

theorem IsL45.false_of_psl3 {X : Type} [Group X] (hX : IsL45 X)
    {n : ℕ} (hn : n = 2 ∨ n = 3) (h : IsPSL 3 2 n X) : False := by
  obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data h
  rcases hn with rfl | rfl
  · rcases hX.card with h' | h'
    · obtain ⟨e⟩ := hX.a8 h'
      exact ((CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated X h).2.2
        (Fin 8) (by simp)).false e
    · rw [h'] at hN
      norm_num at hN
  · rcases hX.card with h' | h' <;> rw [h'] at hN <;> norm_num at hN

theorem IsL45.false_of_psp4 {X : Type} [Group X] (hX : IsL45 X) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (h : IsPSp4 2 n X) : False := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  rcases hn with rfl | rfl <;> rcases hX.card with h' | h' <;> rw [h'] at hc <;>
    revert hc <;> decide

theorem le_ordTwistedF4 {q : ℕ} (hq : 2 ≤ q) : q ^ 12 ≤ ordTwistedF4 q := by
  unfold ordTwistedF4
  have h4 : 1 ≤ q ^ 4 - 1 := by
    have : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    omega
  have h := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (le_refl (q ^ 12)) (by omega : 1 ≤ q ^ 6 + 1)) h4) (by omega : 1 ≤ q ^ 3 + 1))
    (by omega : 1 ≤ q - 1)
  simpa using h

theorem IsL45.false_of_twoF4
    {X : Type} [Group X] (hX : IsL45 X) {f : ℕ} (hf : 3 ≤ f)
    (h : Is2F4 f X) : False := by
  have hc := CFSG.ComponentClassification.CatLeafProof.card_of_reeTitsModel_twistedF4 h
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h1 := le_ordTwistedF4 (q := 2 ^ f) (by omega)
  have h2 : 8 ^ 12 ≤ (2 ^ f) ^ 12 := Nat.pow_le_pow_left h8 12
  rcases hX.card with h' | h' <;> rw [h'] at hc <;> omega

theorem IsL45.false_of_g2
    {X : Type} [Group X] (hX : IsL45 X) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (h : IsG2 2 n X) : False := by
  have hc : Nat.card X = ordG2 (2 ^ n) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  rcases hn with rfl | rfl <;> rcases hX.card with h' | h' <;> rw [h'] at hc <;> revert hc <;>
    decide

theorem IsL45.false_of_3d4
    {X : Type} [Group X] (hX : IsL45 X) {n : ℕ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3) (h : Is3D4 2 n X) : False := by
  have hc : Nat.card X = ordTrialityD4 (2 ^ n) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  rcases hn with rfl | rfl | rfl <;> rcases hX.card with h' | h' <;> rw [h'] at hc <;>
    revert hc <;> decide

theorem IsL45.false_of_twoF4_small
    {X : Type} [Group X] (hX : IsL45 X) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (h : Is2F4 n X) : False := by
  have hc := CFSG.ComponentClassification.CatLeafProof.card_of_reeTitsModel_twistedF4 h
  rcases hn with rfl | rfl <;> rcases hX.card with h' | h' <;> rw [h'] at hc <;> revert hc <;>
    decide

theorem card_quot_sl35 {X : Type} [Group X] (h : IsSL3 5 X) :
    Nat.card (X ⧸ Subgroup.center X) = 372000 := by
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := h
  let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    eK.trans (specialLinearGroupEquivStatedSL 3 K).symm
  let e₂ : X ⧸ Subgroup.center X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
  rw [Nat.card_congr (e₂.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  decide

theorem IsL45.false_of_sl3_five {X : Type} [Group X] (hX : IsL45 X) (b : Bool)
    (hb : IsSLEps3 b 5 X ∨ IsPSLEps3 b 5 1 X) : False := by
  have hZ := hX.center_eq_bot
  have hcZ : Nat.card (X ⧸ Subgroup.center X) = Nat.card X :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toEquiv
  cases b
  · rcases hb with hb | hb
    · obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hb
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hK' : Nat.card K = (5 ^ 1) ^ 2 := by rw [hK]; norm_num
      have hZ' : Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 5 K) =
          (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K).subgroupOf
            (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K) :=
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 5) (f := 1)
          hK' le_rfl (by norm_num)).2
      let e₂ : X ⧸ Subgroup.center X ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K) :=
        QuotientGroup.congr _ _ eK (by rw [Subgroup.map_center_eq eK, hZ'])
      have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_five le_rfl
        hK' (n := 3) (by norm_num)
      have h2 : Nat.card X = 126000 := by
        rw [← hcZ, Nat.card_congr e₂.toEquiv]
        exact h1.trans (by decide)
      rcases hX.card with h' | h' <;> omega
    · obtain ⟨-, -, -, -, hN⟩ := R3c6.psu3Data hb
      norm_num at hN
      rcases hX.card with h' | h' <;> omega
  · rcases hb with hb | hb
    · have h2 : Nat.card X = 372000 := by rw [← hcZ]; exact card_quot_sl35 hb
      rcases hX.card with h' | h' <;> omega
    · obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data hb
      norm_num at hN
      rcases hX.card with h' | h' <;> omega

theorem IsL45.false_of_three (hS : FactSporadicOrders) (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    {X : Type} [Group X] (hX : IsL45 X) (h : Vol2.Ch11.List11_1_1Three X) : False := by
  have hsimple := hX.simple
  rcases h with h7 | hHat7 | ⟨p, hp, h5, h8, hl2p⟩ | hl2sq | ⟨b, hb⟩ | hM22 | hHatM22 | hM23 |
      hJ1 | hJ2 | hJ4 | hHS | hRu | hcase4 | ⟨p, hp, h5, h8, hF, hE, hNat⟩
  · have := Vol2.Ch11.SecA.card_alt7 h7
    rcases hX.card with h' | h' <;> omega
  · exact hX.false_of_isHat hHat7
  · obtain ⟨-, -, -, hN⟩ := R3c6.psl2Data hl2p
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 :=
      Nat.gcd_eq_left (by
        rw [pow_one]
        exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
    rw [hg, pow_one] at hN
    exact no_l2p (Nat.card X) p hX.card hN
  · obtain ⟨-, -, -, hN⟩ := R3c6.psl2Data hl2sq
    norm_num at hN
    rcases hX.card with h' | h' <;> omega
  · exact hX.false_of_sl3_five b hb
  · have := card_of_isSporadic hM22
    rw [hM.2.1] at this
    rcases hX.card with h' | h' <;> omega
  · exact hX.false_of_isHat hHatM22
  · have := card_of_isSporadic hM23
    rw [hS.1] at this
    rcases hX.card with h' | h' <;> omega
  · have := card_of_isSporadic hJ1
    rw [hS.2.1] at this
    rcases hX.card with h' | h' <;> omega
  · have := card_of_isSporadic hJ2
    rw [hS.2.2.1] at this
    rcases hX.card with h' | h' <;> omega
  · have := card_of_isSporadic hJ4
    rw [hS.2.2.2.1] at this
    rcases hX.card with h' | h' <;> omega
  · have := card_of_isSporadic hHS
    rw [hS.2.2.2.2.1] at this
    rcases hX.card with h' | h' <;> omega
  · have := card_of_isSporadic hRu
    rw [hS.2.2.2.2.2] at this
    rcases hX.card with h' | h' <;> omega
  · obtain ⟨-, -, ⟨e⟩, -⟩ := hcase4
    have : Fact (2 < 5) := ⟨by norm_num⟩
    exact S1421.Core3Setup.false_of_simple_sl2 _ e
  · obtain ⟨-, ψ, hψ, hker, -⟩ := hNat
    have : Fact (2 < p) := ⟨by omega⟩
    exact S1421.Core3Setup.false_of_simple_sl2 _
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))

theorem pin_n {n N : ℕ} (hn : 2 ≤ n) (hN : N = 20160 ∨ N = 9999360)
    (h : Vol2.Ch11.SecA.oSL2 n ∣ N) : n = 2 ∨ n = 3 := by
  have h1 : Vol2.Ch11.SecA.oSL2 n ≤ N := Nat.le_of_dvd (by rcases hN with rfl | rfl <;> norm_num) h
  have hn12 : n < 12 := by
    by_contra hge
    push Not at hge
    have : 2 ^ 24 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    unfold Vol2.Ch11.SecA.oSL2 at h1
    rcases hN with rfl | rfl <;> omega
  rcases hN with rfl | rfl <;> interval_cases n <;> simp_all [Vol2.Ch11.SecA.oSL2]

theorem IsL45.false_of_concl1111
    (hS : FactSporadicOrders) (hM : Vol2.Ch11.SecB.FactMathieuOrders) {X : Type} [Group X]
    (hX : IsL45 X) {n : ℕ} (hn : n = 2 ∨ n = 3) (h : Vol2.Ch11.SecA.Concl1111 X n) : False := by
  rcases h with hTwo | ⟨-, hThree⟩
  · rcases hTwo with hSL | hPSL | hSp | hG2 | h2F4 | h3D4 | ⟨h3, h3D4'⟩
    · exact hX.false_of_sl3 hn hSL
    · exact hX.false_of_psl3 hn hPSL
    · exact hX.false_of_psp4 hn hSp
    · exact hX.false_of_g2 hn hG2
    · exact hX.false_of_twoF4_small hn h2F4
    · exact hX.false_of_3d4 (by omega) h3D4
    · rcases hn with rfl | rfl
      · omega
      · exact hX.false_of_3d4 (Or.inl rfl) h3D4'
  · exact hX.false_of_three hS hM hThree

end QA23

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.false_of_isPSL_four_five
    (hS : QA23.FactSporadicOrders) (hM : Vol2.Ch11.SecB.FactMathieuOrders)
    (hP : Vol2.Ch11.SecA.FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h37 : A37ForSQTK) (c : Core3Ctx T M H K1 L M₁)
    (hX : IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  have hX' := QA23.IsL45.of_isPSL hX
  rcases c.bender_cases hM hP h36 h312 h37 with ⟨n, hn, hK, hconc⟩ | ⟨f, -, hf3, hF⟩
  · obtain ⟨eB⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv c.lt_L.le
    obtain ⟨eF⟩ := sl2Equiv_of_isL2Quot hK
    have hD := Vol2.Ch11.SecA.barData_of_quot_SL2 hn (GaloisField.card 2 n (by omega))
      (eB.symm.trans eF)
    obtain ⟨a, ha⟩ := hD.card
    have hdvd : Vol2.Ch11.SecA.oSL2 n ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
      refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card (modO2Image L K1))
      rw [ha]
      exact dvd_mul_left _ _
    have hn23 := QA23.pin_n hn hX'.card hdvd
    exact hX'.false_of_concl1111 hS hM hn23 hconc
  · exact hX'.false_of_twoF4 hf3 hF

end S1421

end CFSG.Quasithin
