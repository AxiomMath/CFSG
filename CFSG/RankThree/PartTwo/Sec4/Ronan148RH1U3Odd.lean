module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1U4
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsU3Odd

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Transfer2


theorem row427_of_noCfg_on'
    {S : Type} [Group S] [Finite S]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥ ∨ ∀ x : L, x ^ 3 = 1 → x ∉ Subgroup.center L →
        Odd (Nat.card (Subgroup.centralizer ({x} : Set L))))
    (h : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → NoCfgS427 S')
    (hc : ∀ (S' : Type) [Group S'] [Finite S'], Nonempty (S' ≃* S) → ∀ y : S', y ≠ 1 →
      y ^ 3 = 1 → ∀ K : Subgroup S', K ≤ Subgroup.centralizer ({y} : Set S') → IsQuasisimple K →
        (K.subgroupOf (Subgroup.centralizer ({y} : Set S'))).IsSubnormal → y ∈ K →
          ¬ IsExtOf (K ⧸ CFSG.pCore 2 K) Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3))) :
    Row427 S := by
  intro G _ _ hG A hA _ hθ L hL ⟨e⟩ d hdA hd1 _ hLd K hK htype
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL) hdA
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    rw [hK', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (Subgroup.subtype_injective _)]
    exact hK.2
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hσ3 : descAut L ⟨d, hdN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [this, map_one]
  have hσ1 : descAut L ⟨d, hdN⟩ ≠ 1 := by
    intro h1
    apply hLd
    have hdC := (descAut_eq_one_iff hL.1.1 ⟨d, hdN⟩).mp h1
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hdC l hl
  have hle := map_le_autFix hdN (hK'M.trans inf_le_right)
  have hsn := isSubnormal_bar hdN hK'M hK'sn
  rcases htype with ⟨⟨φ⟩⟩ | ⟨hdK, hext⟩
  ·
    have hT : IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨(quotPCoreTwoCongr eK).symm.trans φ⟩
    have eKL : K'.subgroupOf L ≃* K' := Subgroup.subgroupOfEquivOfLe hK'L
    have hK₁q : IsQuasisimple (K'.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eKL.symm hK'q
    have hZK : Subgroup.center (K'.subgroupOf L ⧸ CFSG.pCore 2 (K'.subgroupOf L)) = ⊥ := by
      haveI := (isA5Type_quot_congr eKL hT).isSimpleGroup
      haveI : Group.IsPerfect (K'.subgroupOf L) := hK₁q.1
      exact center_eq_bot_of_isSimpleGroup_of_isPerfect
    have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ :=
      inf_eq_bot_of_center_eq_bot hK₁q hZK le_rfl hZ3
    have eB := equivBar hK'L hinf
    exact (h (L ⧸ Subgroup.center L) ⟨e⟩) _ hσ3 hσ1 _ hle
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q) hsn (isA5Type_quot_congr eB.symm hT)
  ·
    have hdK' : d ∈ K' := hK' ▸ hdK
    have hdL : d ∈ L := hK'L hdK'
    rcases hZS L (sectionFourHyp_subgroup hG L) hL.1 hZ3 ⟨e⟩ with hZ | hodd
    · have hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥ := by rw [hZ, inf_bot_eq]
      have eB := equivBar hK'L hinf
      set y : L ⧸ Subgroup.center L := ((⟨d, hdL⟩ : L) : L ⧸ Subgroup.center L) with hy
      have hσ : descAut L ⟨d, hdN⟩ = MulAut.conj y := Ronan148S.descAut_eq_conj hdL
      have hy1 : y ≠ 1 := by
        intro h1
        apply hσ1
        rw [hσ, h1, map_one]
      have hy3 : y ^ 3 = 1 := by
        rw [hy, ← QuotientGroup.mk_pow]
        have : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
        rw [this, QuotientGroup.mk_one]
      rw [hσ, autFix_conj] at hle hsn
      refine hc (L ⧸ Subgroup.center L) ⟨e⟩ y hy1 hy3 _ hle
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hK'q) hsn ⟨⟨d, hdL⟩, hdK', rfl⟩ ?_
      exact Ronan148S.isExtOf_congr (quotPCoreTwoCongr (eK.trans eB)) hext
    ·
      have hdZ : (⟨d, hdL⟩ : L) ∉ Subgroup.center L := by
        intro hz
        apply hLd
        intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
      have hd3' : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
      have hoddC := hodd _ hd3' hdZ
      have hle' : K'.subgroupOf L ≤ Subgroup.centralizer ({(⟨d, hdL⟩ : L)} : Set L) := by
        intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hK'M hk).2)
      have hdvd : Nat.card K' ∣ Nat.card (Subgroup.centralizer ({(⟨d, hdL⟩ : L)} : Set L)) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'L).toEquiv]
        exact Subgroup.card_dvd_of_le hle'
      obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := hext
      have hcardQ : Nat.card (K ⧸ CFSG.pCore 2 K) = 460815505920 * 3 := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr eQ.toEquiv,
          CFSG.Sporadic.ON.card_ON, Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card,
          Fintype.card_multiplicative, ZMod.card]
      have h2 : 2 ∣ Nat.card K := by
        have := Subgroup.card_quotient_dvd_card (CFSG.pCore 2 K)
        rw [hcardQ] at this
        exact (by norm_num : 2 ∣ 460815505920 * 3).trans this
      rw [← Nat.card_congr eK.toEquiv] at hdvd
      exact (Nat.not_even_iff_odd.mpr hoddC) (even_iff_two_dvd.mpr (h2.trans hdvd))

end Transfer2

namespace U3Odd

section SU3

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanEps
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem three_ne_zero_char_two : (3 : F) ≠ 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  intro h0
  have h1 : (1 : F) = 0 := by linear_combination h0 - h2
  exact one_ne_zero h1

theorem exists_form_of_involution {n : ℕ} (hPi : PiField false 2 n F) {B : GL (Fin 3) F} {c : F}
    (hBm3 : (B : Matrix (Fin 3) (Fin 3) F) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hBs : ∀ x : F, (B : Matrix (Fin 3) (Fin 3) F) ≠ x • (1 : Matrix (Fin 3) (Fin 3) F))
    {T : GL (Fin 3) F} (hT2 : T * T = 1) (hT1 : T ≠ 1) (hTB : T * B = B * T) :
    ∃ (τ μ : F) (g : Matrix (Fin 3) (Fin 3) F) (j : Fin 3), τ ^ 3 = 1 ∧ τ ≠ 1 ∧ μ ^ 3 = c ∧
      μ ≠ 0 ∧ IsUnit g ∧
      (((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)) * g = g * diagonal ![τ, τ ^ 2, 1] ∨
        ((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)) * g = g * diagonal ![τ, 1, 1] ∨
        ((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)) * g =
          g * diagonal ![τ ^ 2, 1, 1]) ∧
      ((T : Matrix (Fin 3) (Fin 3) F) - 1 ≠ 0 ∧
        ((T : Matrix (Fin 3) (Fin 3) F) - 1) * ((T : Matrix (Fin 3) (Fin 3) F) - 1) = 0 ∧
        ∀ r : F, ((T : Matrix (Fin 3) (Fin 3) F) - 1) * (r • (B : Matrix (Fin 3) (Fin 3) F)) =
          (r • (B : Matrix (Fin 3) (Fin 3) F)) * ((T : Matrix (Fin 3) (Fin 3) F) - 1)) := by
  obtain ⟨τ, hτ3, hτ1⟩ := KFacts.exists_primitive_cube_root hPi
  have hcommM : (T : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, hTB, Units.val_mul]
  have hTM2 : (T : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, hT2, Units.val_one]
  have hTM1 : (T : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h1 =>
    hT1 (Units.ext (by rw [h1, Units.val_one]))
  obtain ⟨μ, hμ⟩ := u3OddEps_exists_cube_root_of_comm_involution hBm3 hTM2 hTM1 hcommM
  have hc0 : c ≠ 0 := by
    intro h0
    have hdet := congrArg Matrix.det hBm3
    rw [h0, zero_smul, Matrix.det_zero, Matrix.det_pow] at hdet
    have hu : IsUnit (B : Matrix (Fin 3) (Fin 3) F).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp B.isUnit
    exact hu.ne_zero ((pow_eq_zero_iff (by norm_num)).mp hdet)
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hc0
    rw [← hμ, h0]
    norm_num
  set Y : Matrix (Fin 3) (Fin 3) F := μ⁻¹ • (B : Matrix (Fin 3) (Fin 3) F) with hY
  have hY3 : Y ^ 3 = 1 := by
    rw [hY, smul_pow, hBm3, smul_smul, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow, one_smul]
  have hYs : ∀ x : F, Y ≠ x • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro x hx
    apply hBs (μ * x)
    calc (B : Matrix (Fin 3) (Fin 3) F)
        = μ • (μ⁻¹ • (B : Matrix (Fin 3) (Fin 3) F)) := by
          rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
      _ = (μ * x) • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [← hY, hx, smul_smul]
  obtain ⟨g, j, hgU, hform⟩ := Sec4.exists_normal_form hτ3 hτ1 three_ne_zero_char_two hY3 hYs
  have h2 : ∀ M : Matrix (Fin 3) (Fin 3) F, M + M = 0 := fun M => by
    rw [← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  refine ⟨τ, μ, g, j, hτ3, hτ1, hμ, hμ0, hgU, ?_, sub_ne_zero.mpr hTM1, ?_, fun r => ?_⟩
  · simpa only [hY, smul_smul] using hform
  · calc ((T : Matrix (Fin 3) (Fin 3) F) - 1) * ((T : Matrix (Fin 3) (Fin 3) F) - 1)
        = (T : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) -
          ((T : Matrix (Fin 3) (Fin 3) F) + (T : Matrix (Fin 3) (Fin 3) F)) + 1 := by
          noncomm_ring
      _ = 0 := by rw [hTM2, h2 _, sub_zero, h2 1]
  · have hNB : ((T : Matrix (Fin 3) (Fin 3) F) - 1) * (B : Matrix (Fin 3) (Fin 3) F) =
        (B : Matrix (Fin 3) (Fin 3) F) * ((T : Matrix (Fin 3) (Fin 3) F) - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, hcommM]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hNB]

theorem exists_involution_of_even {q : ℕ} {B : GL (Fin 3) F}
    (h2 : 2 ∣ Nat.card (suCentralizer q B)) :
    ∃ T : GL (Fin 3) F, T * T = 1 ∧ T ≠ 1 ∧ T * B = B * T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨((t : CFSG.Open.StatedSU 3 q F) : GL (Fin 3) F), ?_, ?_, mem_suCentralizer.mp t.2⟩
  · have hTord : orderOf ((t : CFSG.Open.StatedSU 3 q F) : GL (Fin 3) F) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
    rw [← sq, ← hTord]
    exact pow_orderOf_eq_one _
  · intro h1
    have hTord : orderOf ((t : CFSG.Open.StatedSU 3 q F) : GL (Fin 3) F) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
    rw [h1, orderOf_one] at hTord
    norm_num at hTord

theorem odd_card_suCentralizer {n : ℕ} (hPi : PiField false 2 n F) {B : GL (Fin 3) F}
    (hdet : (B : Matrix (Fin 3) (Fin 3) F).det = 1) (hB3 : B ^ 3 = 1)
    (hBs : ∀ x : F, (B : Matrix (Fin 3) (Fin 3) F) ≠ x • (1 : Matrix (Fin 3) (Fin 3) F)) :
    Odd (Nat.card (suCentralizer (2 ^ n) B)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨T, hT2, hT1, hTB⟩ := exists_involution_of_even (even_iff_two_dvd.mp hev)
  have hBm3 : (B : Matrix (Fin 3) (Fin 3) F) ^ 3 = (1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [one_smul, ← Units.val_pow_eq_pow_val, hB3, Units.val_one]
  obtain ⟨τ, μ, g, j, hτ3, hτ1, hμ, hμ0, hgU, hform, hN0, hN2, hNX⟩ :=
    exists_form_of_involution hPi hBm3 hBs hT2 hT1 hTB
  have hgdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hgU).ne_zero
  have hdetS : ((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_smul, hdet, mul_one, Fintype.card_fin, mul_pow, ← pow_mul, mul_comm (j : ℕ) 3,
      pow_mul, hτ3, one_pow, one_mul, inv_pow, hμ, inv_one]
  have key : ∀ D : Matrix (Fin 3) (Fin 3) F,
      ((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)) * g = g * D → D.det = 1 := by
    intro D hD
    have h1 := congrArg Matrix.det hD
    rw [Matrix.det_mul, Matrix.det_mul, hdetS, one_mul] at h1
    exact mul_left_cancel₀ hgdet (h1.symm.trans (mul_one _).symm)
  rcases hform with hA | hB' | hC
  · exact hN0 (u3OddEps_eq_zero_of_regular (u3OddEps_distinct_tau hτ3 hτ1) hgU hA (hNX _) hN2)
  · have := key _ hB'
    rw [Matrix.det_diagonal, Fin.prod_univ_three] at this
    change τ * 1 * 1 = 1 at this
    rw [mul_one, mul_one] at this
    exact hτ1 this
  · have := key _ hC
    rw [Matrix.det_diagonal, Fin.prod_univ_three] at this
    change τ ^ 2 * 1 * 1 = 1 at this
    rw [mul_one, mul_one] at this
    exact (u3OddEps_tau_facts hτ3 hτ1).2.1 this

theorem exists_diag_of_rank_one {n : ℕ} {h : UnitaryFieldData 2 n F} (hPi : PiField false 2 n F)
    (hq : ModThree false (2 ^ n)) {B : unitaryIsom3 h} {c t : F} (hc0 : c ≠ 0) (ht1 : t ≠ 1)
    (ht3 : t ^ 3 = 1) {g : Matrix (Fin 3) (Fin 3) F} (hg : IsUnit g)
    (hBg : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * g = g * diagonal ![c * t, c, c]) :
    ∃ W : unitaryIsom3 h,
      (((W⁻¹ * B * W : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal ![c, c, c * t] ∧ c ≠ c * t := by
  have hσ : IsUnitaryInvolution (CFSG.LieType.BorelTits.unitaryInvolution F 2 n) :=
    isUnitaryInvolution_unitaryInvolution (by rw [hPi.card]; rfl)
  have hBu : conjTr (CFSG.LieType.BorelTits.unitaryInvolution F 2 n)
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [conjTr_unitaryInvolution_eq hPi]
    exact mem_unitaryIsom3.mp B.2
  have hσt : CFSG.LieType.BorelTits.unitaryInvolution F 2 n t * t = 1 := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ]
    exact pow_succ_eq_one_of_modThree hq ht3
  obtain ⟨g'', hg''u, hBg''⟩ :=
    u3OddEps_exists_unitary_of_rank_one (CFSG.LieType.BorelTits.unitaryInvolution F 2 n) hσ hBu
      hg hBg hc0 ht1 hσt
  have hgU : IsUnit g'' :=
    (Matrix.isUnit_iff_isUnit_det g'').mpr (Matrix.isUnit_det_of_left_inverse hg''u)
  obtain ⟨W, hWval⟩ : ∃ W : GL (Fin 3) F, (W : Matrix (Fin 3) (Fin 3) F) = g'' :=
    ⟨hgU.unit, hgU.unit_spec⟩
  have hWmem : W ∈ unitaryIsom3 h := by
    refine mem_unitaryIsom3.mpr ?_
    rw [hWval, ← conjTr_unitaryInvolution_eq hPi]
    exact hg''u
  refine ⟨⟨W, hWmem⟩, ?_, ?_⟩
  · have hBW : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (W : Matrix (Fin 3) (Fin 3) F) =
        (W : Matrix (Fin 3) (Fin 3) F) * diagonal ![c, c, c * t] := by
      rw [hWval]
      exact hBg''
    change ((W⁻¹ * (B : GL (Fin 3) F) * W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hBW, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  · intro h1
    apply ht1
    have h2 : c * (1 - t) = 0 := by linear_combination h1
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hc0)).symm

theorem exists_diag_of_even {n : ℕ} (hodd : Odd n) {h : UnitaryFieldData 2 n F}
    {B : unitaryIsom3 h} (hB3 : psuConj h B ^ 3 = 1) (hB1 : psuConj h B ≠ 1)
    (h2 : 2 ∣ Nat.card (suCentralizer (2 ^ n) (B : GL (Fin 3) F))) :
    ∃ (W : unitaryIsom3 h) (l m : F),
      (((W⁻¹ * B * W : unitaryIsom3 h) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal ![l, l, m] ∧ l ≠ m := by
  have hPi : PiField false 2 n F :=
    ⟨h.prime, h.one_le, by
      rw [h.card]
      change 2 ^ (2 * n) = (2 ^ n) ^ 2
      rw [← pow_mul, mul_comm]⟩
  have hq : ModThree false (2 ^ n) := by
    change 2 ^ n % 3 = 2
    exact two_pow_mod_three_of_odd hodd
  obtain ⟨c, hcB⟩ := exists_scalar_of_psuConj_pow_three B hB3
  have hBm3 : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := pow_three_matrix_eq_scalar hcB
  have hBs : ∀ x : F, ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠
      x • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro x hBx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have hdet := congrArg Matrix.det hBx
      rw [zero_smul, Matrix.det_zero] at hdet
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (B : GL (Fin 3) F).isUnit).ne_zero hdet
    have hscalar : (B : GL (Fin 3) F) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 x hx0) := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
      exact hBx
    exact hB1 (psuConj_eq_one_of_coe_eq_scalar hscalar)
  obtain ⟨T, hT2, hT1, hTB⟩ := exists_involution_of_even h2
  obtain ⟨τ, μ, g, j, hτ3, hτ1, -, hμ0, hgU, hform, hN0, hN2, hNX⟩ :=
    exists_form_of_involution hPi hBm3 hBs hT2 hT1 hTB
  obtain ⟨hτ0, hτ2, -⟩ := u3OddEps_tau_facts hτ3 hτ1
  have he : (τ ^ (j : ℕ) * μ⁻¹) ≠ 0 := mul_ne_zero (pow_ne_zero _ hτ0) (inv_ne_zero hμ0)
  have hτ3' : (τ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ3, one_pow]
  rcases hform with hA | hB' | hC
  · exact (hN0 (u3OddEps_eq_zero_of_regular (u3OddEps_distinct_tau hτ3 hτ1) hgU hA (hNX _)
      hN2)).elim
  · obtain ⟨W, hW, hlm⟩ := exists_diag_of_rank_one hPi hq (inv_ne_zero he) hτ1 hτ3 hgU
      (u3OddEps_mul_eq_diagonal_of_smul he hB')
    exact ⟨W, _, _, hW, hlm⟩
  · obtain ⟨W, hW, hlm⟩ := exists_diag_of_rank_one hPi hq (inv_ne_zero he) hτ2 hτ3' hgU
      (u3OddEps_mul_eq_diagonal_of_smul he hC)
    exact ⟨W, _, _, hW, hlm⟩

end SU3

end U3Odd

namespace U3Odd

theorem autFix_conj_map {X : Type*} [Group X] (β σ : MulAut X) :
    Sec4.autFix (β * σ * β⁻¹) = (Sec4.autFix σ).map β.toMonoidHom := by
  ext y
  rw [Sec4.mem_autFix, Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨β⁻¹ y, ?_, ?_⟩
    · rw [Sec4.mem_autFix]
      have h1 := congrArg (β⁻¹ : MulAut X) hy
      simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using h1
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self]
  · rintro ⟨x, hx, rfl⟩
    rw [Sec4.mem_autFix] at hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply_self, hx]

section PSU

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanEps
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {h : UnitaryFieldData 2 n F}

theorem sl2_card_ne_sixty {n : ℕ} (hn3 : 3 ≤ n) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 60 := by
  intro h60
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
  have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
  omega

theorem simple_of_psuConj (hodd : Odd n) (hn3 : 3 ≤ n) [Finite (unitaryPSU h 3)]
    {B : unitaryIsom3 h} (hB3 : psuConj h B ^ 3 = 1) (hB1 : psuConj h B ≠ 1)
    {K : Subgroup (unitaryPSU h 3)} (hKC : K ≤ Sec4.autFix (psuConj h B))
    (hKq : IsQuasisimple K) (hKs : (K.subgroupOf (Sec4.autFix (psuConj h B))).IsSubnormal) :
    IsSimpleGroup K ∧ Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  haveI : Group.IsPerfect K := hKq.1
  have h2K : 2 ∣ Nat.card K :=
    even_iff_two_dvd.mp (CFSG.RankThree.OddKernel.even_card_of_isQuasisimple hKq)
  have h2 : 2 ∣ Nat.card (suCentralizer (2 ^ n) (B : GL (Fin 3) F)) := by
    have hK₁ := commutator_le_suCentralizer B (K.comap (unitaryProj h 3))
      (forall_comm_scalar_of_le_autFix B K hKC)
    have hmap := u3OddEps_map_commutator_comap_eq_of_surjective (unitaryProj h 3)
      (unitaryProj_surjective h 3) K
    have h1 : Nat.card K ∣ Nat.card ↥⁅K.comap (unitaryProj h 3), K.comap (unitaryProj h 3)⁆ := by
      have := Subgroup.card_map_dvd ⁅K.comap (unitaryProj h 3), K.comap (unitaryProj h 3)⁆
        (unitaryProj h 3)
      rwa [hmap] at this
    exact h2K.trans (h1.trans (Subgroup.card_dvd_of_le hK₁))
  obtain ⟨W, l, m, hD, hlm⟩ := exists_diag_of_even hodd hB3 hB1 h2
  set B₀ : unitaryIsom3 h := W⁻¹ * B * W with hB₀
  set β : MulAut (unitaryPSU h 3) := psuConj h W⁻¹ with hβ
  have hconj : psuConj h B₀ = β * psuConj h B * β⁻¹ := by
    simp only [hB₀, hβ, map_mul, map_inv, inv_inv]
  have hfix : Sec4.autFix (psuConj h B₀) = (Sec4.autFix (psuConj h B)).map β.toMonoidHom := by
    rw [hconj, autFix_conj_map]
  set K₀ : Subgroup (unitaryPSU h 3) := K.map β.toMonoidHom with hK₀def
  have hK₀C : K₀ ≤ Sec4.autFix (psuConj h B₀) := hfix ▸ Subgroup.map_mono hKC
  let eK : K ≃* K₀ := K.equivMapOfInjective _ β.injective
  have hK₀q : IsQuasisimple K₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hKq
  have hK₀s : (K₀.subgroupOf (Sec4.autFix (psuConj h B₀))).IsSubnormal := by
    have := isSubnormal_subgroupOf_map β hKC hKs
    rwa [← hfix] at this
  have hq : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨F₀, _, _, hF₀, ⟨ι⟩⟩ := exists_perfectResidual_psuFixed_mulEquiv h hq hlm hD
  have hfix₀ : Sec4.autFix (psuConj h B₀) =
      (suCentralizer (2 ^ n) (B₀ : GL (Fin 3) F)).map (unitaryProj h 3) := by
    ext z
    rw [Sec4.mem_autFix, mem_map_suCentralizer_iff h hD z]
  set N := inSubgroup perfectResidual (Sec4.autFix (psuConj h B₀)) with hN
  have hNeq : N = inSubgroup perfectResidual
      ((suCentralizer (2 ^ n) (B₀ : GL (Fin 3) F)).map (unitaryProj h 3)) := by rw [hN, hfix₀]
  let ι' : N ≃* Matrix.SpecialLinearGroup (Fin 2) F₀ := (MulEquiv.subgroupCongr hNeq).trans ι
  have hNC : N ≤ Sec4.autFix (psuConj h B₀) := Subgroup.map_subtype_le _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F₀ := Fintype.ofFinite F₀
  haveI : CharP F₀ 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF₀])
  obtain ⟨hNs, -, hNcard⟩ := sl2_char_two_data (by rw [hF₀]; exact hq) ι'.symm
  have hK₀N : K₀ ≤ N := KFacts.le_inSubgroup_perfectResidual hK₀q.1 hK₀C
  have hK₀eq : K₀ = N := eq_of_subnormal_of_le_simple hK₀N hNC hK₀s hNs
    (ne_bot_of_isQuasisimple hK₀q)
  let eKN : K ≃* N := eK.trans (MulEquiv.subgroupCongr hK₀eq)
  haveI := hNs
  exact ⟨eKN.isSimpleGroup, by rw [Nat.card_congr eKN.toEquiv, hNcard, hF₀]⟩

theorem good427_psuConj (hodd : Odd n) (hn3 : 3 ≤ n) [Finite (unitaryPSU h 3)]
    {B : unitaryIsom3 h} (hB3 : psuConj h B ^ 3 = 1) (hB1 : psuConj h B ≠ 1) :
    Good427 (Sec4.autFix (psuConj h B)) := by
  intro K hKC hKq hKs hA5
  obtain ⟨hs, hcard⟩ := simple_of_psuConj hodd hn3 hB3 hB1 hKC hKq hKs
  haveI := hs
  exact not_isA5Type_of_simple (exists_ne_comm_of_isQuasisimple hKq)
    (by rw [hcard]; exact sl2_card_ne_sixty hn3) hA5

theorem onFree_inner (hodd : Odd n) (hn3 : 3 ≤ n) [Finite (unitaryPSU h 3)]
    (hZ : Subgroup.center (unitaryPSU h 3) = ⊥) {y : unitaryPSU h 3} (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) : OnFree (Subgroup.centralizer ({y} : Set (unitaryPSU h 3))) y := by
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 y
  have hconj := KFacts.conj_mk_eq_psuConj (h := h) g
  set B : unitaryIsom3 h := ⟨g, unitarySU_le_unitaryIsom3 (h := h) g.2⟩ with hBdef
  have hB3 : psuConj h B ^ 3 = 1 := by
    rw [← hconj, ← map_pow]
    have : (unitaryProj h 3 g) ^ 3 = 1 := hy3
    change MulAut.conj ((unitaryProj h 3 g) ^ 3) = 1
    rw [this, map_one]
  have hB1 : psuConj h B ≠ 1 := by
    rw [← hconj]
    intro h1
    apply hy1
    exact RonanKChevTwo.conj_injective_of_center_eq_bot hZ (h1.trans (map_one _).symm)
  have hC : Subgroup.centralizer ({(unitaryProj h 3 g : unitaryPSU h 3)} : Set (unitaryPSU h 3)) =
      Sec4.autFix (psuConj h B) := by
    rw [← hconj, autFix_conj]
    rfl
  refine (good427_onFree_of_simple_qs hy1
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc) fun K hKC hKq hKs => ?_).2
  rw [hC] at hKC hKs
  obtain ⟨hs, hcard⟩ := simple_of_psuConj hodd hn3 hB3 hB1 hKC hKq hKs
  exact ⟨hs, by rw [hcard]; exact sl2_card_ne_sixty hn3⟩

theorem good427_field (hodd : Odd n) [Finite (unitaryPSU h 3)] (hn3 : 3 ≤ n)
    {α : MulAut (unitaryPSU h 3)} (hα3 : α ^ 3 = 1) (hD : α ∉ (psuConj h).range) :
    Good427 (Sec4.autFix α) := by
  intro K hKC hKq hKs hA5
  haveI : Group.IsPerfect K := hKq.1
  have hnt : K ≠ ⊥ := ne_bot_of_isQuasisimple hKq
  have hq2 : 2 < 2 ^ n := by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨φ, hφ, H, hαH⟩ := unitary_order_three_field_descent hq2 α hα3 hD
  have hστ' : MulAut.congr ((MulEquiv.refl _).trans (psuConj h H)⁻¹) α = psuField h φ := by
    rw [congr_trans_mulAut, hαH]
    ext x
    simp
  obtain ⟨m, hnm, hm, hK₀⟩ := exists_card_fixedField_of_orderOf_eq_three h hφ
  have h₀ : UnitaryFieldData 2 m (fixedField φ) := ⟨Nat.prime_two, hm, hK₀⟩
  have hbar := bar_coe_fixedField h hnm h₀
  by_cases hm1 : 2 ^ m = 2
  · exact false_of_uniFix_two h₀ hbar ((MulEquiv.refl _).trans (psuConj h H)⁻¹) hστ' hm1
      (fun x => Sec4.mem_autFix) hKC hnt
  have hq₀ : 2 < 2 ^ m := by
    have : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
    omega
  obtain ⟨eK⟩ := nonempty_mulEquiv_uniFix h₀ hbar ((MulEquiv.refl _).trans (psuConj h H)⁻¹) hστ'
    hq₀ (fun x => Sec4.mem_autFix) hKC hnt hKs
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG₀ : Nat.card (GaloisField 2 (2 * m)) = 2 ^ (2 * m) :=
    GaloisField.card 2 (2 * m) (by omega)
  have h₁ : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) := ⟨Nat.prime_two, hm, hG₀⟩
  haveI := Fintype.ofFinite (fixedField φ)
  have ψ : fixedField φ ≃+* GaloisField 2 (2 * m) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (fixedField φ) 2 (2 * m) (by omega) hK₀
  obtain ⟨φ₁⟩ := nonempty_unitaryPSU_mulEquiv_projSU h₁
  have eK' : K ≃* projSU 3 2 m := (eK.trans
    (CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof.psuEquiv ψ h₁ h₀ hq₀)).trans φ₁
  haveI : IsSimpleGroup (projSU 3 2 m) :=
    CFSG.PGLModel.isSimpleGroup_projSU_of_admissible
      ⟨Nat.prime_two, hm, le_rfl, fun h' => by simp only [Prod.mk.injEq] at h'; omega⟩
  haveI : IsSimpleGroup K := eK'.isSimpleGroup
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : m = 1 := by omega
    exact hm1 (by rw [this]; norm_num)
  have h64 : 2 ^ (3 * m) ∣ Nat.card K := by
    rw [Nat.card_congr eK'.toEquiv]
    exact two_pow_dvd_of_mul_gcd (KFacts.KS14.card_projSU_three_mul_gcd 2 m hm)
  refine not_isA5Type_of_simple (exists_ne_comm_of_isQuasisimple hKq) (fun h60 => ?_) hA5
  rw [h60] at h64
  have : 2 ^ 6 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans h64
  norm_num at this

theorem noCfgS427_psu (hodd : Odd n) (hn3 : 3 ≤ n) [Finite (unitaryPSU h 3)] :
    NoCfgS427 (unitaryPSU h 3) := by
  intro α hα3 hα1
  by_cases hD : α ∈ (psuConj h).range
  · obtain ⟨B, rfl⟩ := hD
    exact good427_psuConj hodd hn3 hα3 hα1
  · exact good427_field hodd hn3 hα3 hD

end PSU

section Cover

open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedSU StatedScalars StatedProj)

theorem center_or_odd_su3
    {m : ℕ} (hodd : Odd m) (hm3 : 3 ≤ m) {L : Type} [Group L]
    [Finite L] (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m)))) :
    Subgroup.center L = ⊥ ∨ ∀ x : L, x ^ 3 = 1 → x ∉ Subgroup.center L →
      Odd (Nat.card (Subgroup.centralizer ({x} : Set L))) := by
  set K := GaloisField 2 (2 * m) with hKdef
  haveI : Group.IsPerfect L := hL.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddZ : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  have hK : Nat.card K = (2 ^ m) ^ 2 := by
    rw [hKdef, GaloisField.card 2 (2 * m) (by omega), ← pow_mul, mul_comm]
  obtain ⟨hsurj, hcen, hdvd⟩ := CFSG.SectionRank.EvenCover.pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := CFSG.SectionRank.EvenCover.even_unitary_three_central_odd_extension_splitting
    hK (by omega) hsurj hcen (Odd.of_dvd_nat hoddZ hdvd)
  obtain ⟨φ, hφs, hker, hDmap⟩ := CFSG.SectionRank.EvenCover.perfect_cover_map_of_section e σ hσ
  by_cases hZ : Subgroup.center L = ⊥
  · exact Or.inl hZ
  right
  set D : Subgroup (StatedSU 3 (2 ^ m) K) := (StatedScalars (Fin 3) K).subgroupOf
    (StatedSU 3 (2 ^ m) K) with hD
  have hDcard : Nat.card D = 3 := by
    rw [hD, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num)).2.2]
    exact Nat.gcd_eq_left (Res417Six.three_dvd_two_pow_add_one hodd)
  have hkerbot : φ.ker = ⊥ := by
    have hd : Nat.card φ.ker ∣ Nat.card D := Subgroup.card_dvd_of_le hker
    rw [hDcard] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hkD : φ.ker = D := Subgroup.eq_of_le_of_card_ge hker (by rw [hDcard, h3])
      apply hZ
      rw [← hDmap, ← hkD]
      exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  let eφ : StatedSU 3 (2 ^ m) K ≃* L := MulEquiv.ofBijective φ ⟨hinj, hφs⟩
  intro x hx3 hxZ
  set B := eφ.symm x with hBdef
  have hPi : PiField false 2 m K := ⟨Nat.prime_two, by omega, by rw [hK]; rfl⟩
  have hB3 : (B : GL (Fin 3) K) ^ 3 = 1 := by
    have : B ^ 3 = 1 := by rw [hBdef, ← map_pow, hx3, map_one]
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hBs : ∀ c : K, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hc
    apply hxZ
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hdet := congrArg Matrix.det hc
      rw [zero_smul, Matrix.det_zero] at hdet
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (B : GL (Fin 3) K).isUnit).ne_zero hdet
    have hBD : B ∈ D := by
      rw [hD, Subgroup.mem_subgroupOf]
      refine ⟨Units.mk0 c hc0, ?_⟩
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
      exact hc.symm
    rw [← hDmap]
    exact ⟨B, hBD, by rw [hBdef]; exact eφ.apply_symm_apply x⟩
  have hodd2 := odd_card_suCentralizer hPi (B := (B : GL (Fin 3) K))
    (CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU B.2) hB3 hBs
  have hcent : (Subgroup.centralizer ({B} : Set (StatedSU 3 (2 ^ m) K))).map eφ.toMonoidHom =
      Subgroup.centralizer ({x} : Set L) := by
    rw [centralizer_map_mulEquiv, hBdef, MulEquiv.apply_symm_apply]
  have heq : Subgroup.centralizer ({B} : Set (StatedSU 3 (2 ^ m) K)) =
      suCentralizer (2 ^ m) (B : GL (Fin 3) K) := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, mem_suCentralizer]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [← hcent, Subgroup.card_map_of_injective (f := eφ.toMonoidHom) eφ.injective, heq]
  exact hodd2

end Cover

end U3Odd

open U3Odd

section Rows


open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag in
theorem rowOf427_su3_odd
    : ∀ m : ℕ, 1 ≤ m → Odd m → RowOf427 (projSU 3 2 m) := by
  intro m hm hodd S _ _ hs hna ⟨eSX⟩
  rcases Nat.eq_or_lt_of_le hm with rfl | hm1
  ·
    exfalso
    have hsolv : Group.IsSolvable (projSU 3 2 1) :=
      CFSG.RankThree.PartTwo.Sec13.isSolvable_projSU_two
    haveI : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := eSX.symm.toMonoidHom) eSX.symm.surjective
    obtain ⟨a, b, hab⟩ := hna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr ‹_› a b)
  have hm3 : 3 ≤ m := by
    obtain ⟨j, hj⟩ := hodd
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 m (GaloisField 2 (2 * m)) :=
    ⟨Nat.prime_two, hm, GaloisField.card 2 (2 * m) (by omega)⟩
  obtain ⟨φ₀⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
  let τ : S ≃* unitaryPSU h 3 := eSX.trans φ₀.symm
  haveI : Finite (unitaryPSU h 3) := Finite.of_equiv _ τ.toEquiv
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ := by
    have hZS : Subgroup.center S = ⊥ := RonanK429.center_eq_bot_of_isSimpleGroup hs hna
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : τ.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply τ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (τ g)
    rw [hZS, Subgroup.mem_bot] at hz'
    rw [← τ.apply_symm_apply z, hz', map_one]
  refine row427_of_noCfg_on' ?_ ?_ ?_
  · intro L _ _ _ hL hZ3 ⟨e'⟩
    exact center_or_odd_su3 hodd hm3 hL hZ3
      ((e'.trans eSX).trans (CFSG.PGLModel.projSUEquivStatedProj 3 2 m))
  · intro S' _ _ ⟨e'⟩
    exact NoCfgS427.of_mulEquiv (e'.trans τ) (noCfgS427_psu hodd hm3)
  · intro S' _ _ ⟨e'⟩ y hy1 hy3
    have hx3 : (e'.trans τ) y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hx1 : (e'.trans τ) y ≠ 1 := by
      rw [Ne, map_eq_one_iff _ (e'.trans τ).injective]
      exact hy1
    have h1 := (onFree_inner hodd hm3 hZ hx1 hx3).map (e'.trans τ).symm
    rwa [MulEquiv.symm_apply_apply] at h1

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
