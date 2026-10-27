module

public import CFSG.Quasithin.Background.F6CatRecogZ2D8
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter

namespace F6

section Orders

theorem card_statedProj_sl_three {K : Type} [Field K] [Finite K] :
    Nat.card (StatedProj (StatedSL 3 K)) = Nat.card K ^ 3 *
      ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) / Nat.gcd 3 (Nat.card K - 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3),
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]

theorem card_statedProj_su_three {K : Type} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) = (p ^ f) ^ 3 *
      (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) / Nat.gcd 3 (p ^ f + 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by norm_num),
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have h2 : (((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (p ^ f) ^ 2 - 1 := by
    have : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [show ((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub this]; ring]
    exact Int.toNat_natCast _
  have h3 : (((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (p ^ f) ^ 3 + 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [h2, h3]

theorem sixtyfour_dvd_card_psl_three {q : ℕ} (hq : q % 8 = 1) :
    64 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, q = 8 * a + 1 := ⟨q / 8, by omega⟩
  have h2 : (8 * a + 1) ^ 2 - 1 = 16 * (a * (4 * a + 1)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have h3 : (8 * a + 1) ^ 3 - 1 = 8 * (a * (64 * a ^ 2 + 24 * a + 3)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h2, h3, show 8 * a + 1 - 1 = 8 * a by omega]
  apply Nat.dvd_div_of_mul_dvd
  have hg : Nat.gcd 3 (8 * a) = 1 ∨ Nat.gcd 3 (8 * a) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 _)
  rcases hg with hg | hg
  · rw [hg]
    exact ⟨2 * (8 * a + 1) ^ 3 * (a * (4 * a + 1)) * (a * (64 * a ^ 2 + 24 * a + 3)), by ring⟩
  · rw [hg]
    have h3a : 3 ∣ a := by
      have : 3 ∣ 8 * a := hg ▸ Nat.gcd_dvd_right 3 _
      exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
    obtain ⟨b, rfl⟩ := h3a
    exact ⟨2 * (8 * (3 * b) + 1) ^ 3 * (b * (4 * (3 * b) + 1)) *
      (3 * b * (64 * (3 * b) ^ 2 + 24 * (3 * b) + 3)), by ring⟩

theorem sixtyfour_dvd_card_psu_three {q : ℕ} (hq : q % 8 = 7) :
    64 ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, q = 8 * a + 7 := ⟨q / 8, by omega⟩
  have h2 : (8 * a + 7) ^ 2 - 1 = 16 * ((4 * a + 3) * (a + 1)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have h3 : (8 * a + 7) ^ 3 + 1 = 8 * ((a + 1) * (64 * a ^ 2 + 104 * a + 43)) := by ring
  rw [h2, h3, show 8 * a + 7 + 1 = 8 * (a + 1) by ring]
  apply Nat.dvd_div_of_mul_dvd
  have hg : Nat.gcd 3 (8 * (a + 1)) = 1 ∨ Nat.gcd 3 (8 * (a + 1)) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 _)
  rcases hg with hg | hg
  · rw [hg]
    exact ⟨2 * (8 * a + 7) ^ 3 * ((4 * a + 3) * (a + 1)) *
      ((a + 1) * (64 * a ^ 2 + 104 * a + 43)), by ring⟩
  · rw [hg]
    have h3a : 3 ∣ a + 1 := by
      have : 3 ∣ 8 * (a + 1) := hg ▸ Nat.gcd_dvd_right 3 _
      exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
    obtain ⟨b, hb⟩ := h3a
    rw [hb]
    exact ⟨2 * (8 * a + 7) ^ 3 * ((4 * a + 3) * b) * (3 * b * (64 * a ^ 2 + 104 * a + 43)),
      by ring⟩

end Orders

theorem f618RecogZ4wrZ2SQT_holds
    (hW : WalterModelsStatement)
    (hWr : WreathedRecognitionStatement) (hWI : WreathIndexTwoSylowFact)
    (hPG : PGammaL2InspectionFact) (hCov : SLEps3CoverFact) : F618RecogZ4wrZ2SQT := by
  intro D _ _ hS hT
  obtain ⟨S, ⟨eS⟩⟩ := hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2) with hWdef
  have hW32 : Nat.card W = 32 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hS32 : Nat.card (S : Subgroup D) = 32 := (Nat.card_congr eS.toEquiv).trans hW32
  have : IsSimpleGroup (TwoResidualQuot D) := hS.quasisimple.2.1
  have hnonab : ∃ a b : TwoResidualQuot D, a * b ≠ b * a := hS.quasisimple.2.2
  have : Group.IsPerfect ↥(twoResidual (⊤ : Subgroup D)) := hS.quasisimple.1
  have := twoResidual_top_normal (D := D)
  obtain ⟨Q, ⟨eQ⟩⟩ := exists_sylow_quotient_of_setting hS.toF618RecogSetting S
  set H : Subgroup W := (((S : Subgroup D) ⊓ twoResidual ⊤).subgroupOf S).map eS.toMonoidHom
    with hHdef
  let ιP : ↥((S : Subgroup D) ⊓ twoResidual ⊤) ≃* ↥H :=
    (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
      ((((S : Subgroup D) ⊓ twoResidual ⊤).subgroupOf S).equivMapOfInjective _ eS.injective)
  have helem : IsMulCommutative (Q : Subgroup (TwoResidualQuot D)) →
      Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) ≤ 4 := by
    intro hab
    have hsqQ := (walter_cases hW hS Q hab).1
    have hsqH : ∀ x ∈ H, x * x = 1 :=
      forall_mul_self_of_mulEquiv (eQ.symm.trans ιP).symm hsqQ
    have hcommH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
      intro x hx y hy
      have h1 := hab.is_comm.comm ((eQ.symm.trans ιP).symm ⟨x, hx⟩)
        ((eQ.symm.trans ιP).symm ⟨y, hy⟩)
      have h2 := congrArg (eQ.symm.trans ιP) h1
      simp only [map_mul, MulEquiv.apply_symm_apply] at h2
      exact congrArg Subtype.val h2
    rw [Nat.card_congr ιP.toEquiv]
    exact card_le_four_of_le_wreath H hsqH hcommH
  have h4 := (not_isCyclic_sylow_two hnonab Q).2
  rw [← Nat.card_congr eQ.toEquiv] at h4
  have hdvd : Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) ∣ 2 ^ 5 := by
    rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← hS32]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨n, hn⟩ := exists_index_twoResidual_eq (D := D)
  have hidx := card_sylow_eq_mul_index (twoResidual ⊤) hn S
  rw [hS32] at hidx
  have hcases : Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 4 ∨
      Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 8 ∨
      Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 16 ∨
      Nat.card ↥((S : Subgroup D) ⊓ twoResidual ⊤) = 32 := by
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hie] at h4 ⊢
    interval_cases i
    · norm_num at h4
    · norm_num at h4
    · left; norm_num
    · right; left; norm_num
    · right; right; left; norm_num
    · right; right; right; norm_num
  rcases hcases with hP | hP | hP | hP
  ·
    exfalso
    obtain ⟨p, K, _, _, hp, -, hp5, hK, -, -, ⟨eK⟩⟩ := psl_two_of_card_inf_eq_four hS S hP
    have : Fact p.Prime := ⟨hp⟩
    have hc : Nat.card (MulAut (TwoResidualQuot D)) = 2 * Nat.card (TwoResidualQuot D) := by
      rw [Nat.card_congr (MulAut.congr eK).toEquiv, Nat.card_congr eK.toEquiv]
      exact card_mulAut_psl_two_prime K hp5 hK
    have h2 := index_dvd_of_card_mulAut hS.toF618RecogSetting hc
    rw [hP] at hidx
    have h8 : (twoResidual (⊤ : Subgroup D)).index = 8 := by rw [hn]; omega
    rw [h8] at h2
    norm_num at h2
  ·
    exfalso
    rw [hP] at hidx
    have hindex : (twoResidual (⊤ : Subgroup D)).index = 4 := by rw [hn]; omega
    have hQ8 : Nat.card (Q : Subgroup (TwoResidualQuot D)) = 8 := by
      rw [← Nat.card_congr eQ.toEquiv, hP]
    by_cases hab : IsMulCommutative (Q : Subgroup (TwoResidualQuot D))
    · have := helem hab
      omega
    · have hnc : ∃ a b : (Q : Subgroup (TwoResidualQuot D)), a * b ≠ b * a := by
        by_contra h
        push Not at h
        exact hab ⟨⟨h⟩⟩
      rcases CFSG.ComponentClassification.WalterSchur.dihedral_or_quaternion_of_card_eq_eight hQ8
          hnc with heD | heQ8
      · obtain ⟨eD⟩ := heD
        rcases psl_two_or_alternating_seven_of_dihedral hS S ⟨eQ.trans eD⟩ with
          ⟨p, e, K, _, _, hp, hp2, he1, he2, h16, -, hK, ⟨eK⟩, -, -⟩ | ⟨⟨e7⟩, -⟩
        · have : Fact p.Prime := ⟨hp⟩
          have hodd : IsOddPrimePower (Nat.card K) :=
            ⟨p, e, hp, hp.odd_of_ne_two hp2, he1, hK⟩
          interval_cases e
          ·
            rw [pow_one] at hK h16
            have hp5 : 5 ≤ p := by
              have := hp.two_le
              omega
            have hc : Nat.card (MulAut (TwoResidualQuot D)) =
                2 * Nat.card (TwoResidualQuot D) := by
              rw [Nat.card_congr (MulAut.congr eK).toEquiv, Nat.card_congr eK.toEquiv]
              exact card_mulAut_psl_two_prime K hp5 hK
            have h2 := index_dvd_of_card_mulAut hS.toF618RecogSetting hc
            rw [hindex] at h2
            norm_num at h2
          ·
            have hp8 := mod_eight_of_sq_mod_sixteen h16
            have h3 : 3 < Nat.card K := by
              rw [hK]
              have := hp.two_le
              nlinarith
            have hc : Nat.card (MulAut (TwoResidualQuot D)) =
                Nat.card (TwoResidualQuot D) * (twoResidual (⊤ : Subgroup D)).index := by
              rw [hindex, Nat.card_congr (MulAut.congr eK).toEquiv, Nat.card_congr eK.toEquiv,
                card_mulAut_psl_two_sq K hp2 hK, mul_comm]
            obtain ⟨ψ⟩ := nonempty_quotient_mulEquiv_mulAut hS.toF618RecogSetting hc
            let Φ : PGammaL2 K ≃* MulAut (PSL2 K) := MulEquiv.ofBijective _
              ⟨pGammaL2ToMulAutPSL2_injective K hodd h3,
                pGammaL2ToMulAutPSL2_surjective K hK hodd h3⟩
            let χ : D ⧸ (conjQuotHom D).ker ≃* PGammaL2 K :=
              ψ.trans ((MulAut.congr (eK.trans
                (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)).trans Φ.symm)
            obtain ⟨Q₁, ⟨e₁⟩⟩ := exists_sylow_quotient_ker hS.toF618RecogSetting S
            have : Finite (PGammaL2 K) := finite_pGammaL2 K
            obtain ⟨Q₂, ⟨e₂⟩⟩ := exists_sylow_mulEquiv_of_mulEquiv χ Q₁
            exact (hPG p K hp hK hp8).2 Q₂ ⟨(e₂.symm.trans e₁.symm).trans eS⟩
        ·
          have hc : Nat.card (MulAut (TwoResidualQuot D)) =
              2 * Nat.card (TwoResidualQuot D) := by
            rw [Nat.card_congr (MulAut.congr e7).toEquiv, Nat.card_congr e7.toEquiv]
            exact card_mulAut_alternating_seven
          have h2 := index_dvd_of_card_mulAut hS.toF618RecogSetting hc
          rw [hindex] at h2
          norm_num at h2
      ·
        obtain ⟨eQ8⟩ := heQ8
        exact false_of_sylow_quaternion hnonab Q eQ8
  ·
    exfalso
    have hHcard : Nat.card H = 16 := by rw [← Nat.card_congr ιP.toEquiv, hP]
    have hHidx : H.index = 2 := by
      have := H.card_mul_index
      rw [hHcard, hW32] at this
      omega
    have hab := hWI (TwoResidualQuot D) hnonab Q H hHidx ⟨eQ.symm.trans ιP⟩
    have := helem hab
    omega
  ·
    rw [hP] at hidx
    have hn0 : 2 ^ n = 1 := by omega
    have hL : twoResidual (⊤ : Subgroup D) = ⊤ := by rw [← Subgroup.index_eq_one, hn, hn0]
    have hQ32 : Nat.card (Q : Subgroup (TwoResidualQuot D)) = 32 := by
      rw [← Nat.card_congr eQ.toEquiv, hP]
    have hSL : (S : Subgroup D) ⊓ twoResidual ⊤ = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hP, hS32])
    have hwr : ∃ (S' : Sylow 2 (TwoResidualQuot D)) (m : ℕ), 2 ≤ m ∧
        Nonempty ((S' : Subgroup (TwoResidualQuot D)) ≃* CFSG.Open.WreathedTwoGroup m) :=
      ⟨Q, 2, le_rfl, ⟨eQ.symm.trans ((MulEquiv.subgroupCongr hSL).trans eS)⟩⟩
    have hn64 : ¬ 64 ∣ Nat.card (TwoResidualQuot D) := fun h => by
      have h' := Sylow.pow_dvd_card_of_pow_dvd_card (P := Q) (n := 6) (by simpa using h)
      rw [hQ32] at h'
      norm_num at h'
    rcases hWr (TwoResidualQuot D) hnonab hwr with
      ⟨p, f, hp, hp2, hf, hq4, hadm₀, K, _, _, hK, ⟨eK₀⟩⟩ |
      ⟨p, f, hp, hp2, hf, hq4, hadm₀, K, _, _, hK, ⟨eK₀⟩⟩
    ·
      have : Fact p.Prime := ⟨hp⟩
      let eK : TwoResidualQuot D ≃* StatedProj (StatedSL 3 K) := eK₀
      have hadm : StatedLieAdmissible .PSL 3 p f := hadm₀
      have hq8 : p ^ f % 8 = 5 := by
        by_contra hne
        have h1 : p ^ f % 8 = 1 := by omega
        apply hn64
        rw [Nat.card_congr eK.toEquiv, card_statedProj_sl_three, hK]
        exact sixtyfour_dvd_card_psl_three h1
      have hf2 : f ≤ 2 := by
        have : Finite (StatedProj (StatedSL 3 K)) := Finite.of_equiv _ eK.toEquiv
        have h1 := CFSG.SectionRank.ClassicalOdd.le_pRank_SL (n := 3) (a := 1) (b := 1)
          le_rfl (by norm_num) hK
        have h2 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp
          (CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv eK.symm hS.sqt)) p hp hp2
        omega
      have hf1 : f = 1 := by
        interval_cases f
        · rfl
        · have := odd_sq_mod_eight (hp.odd_of_ne_two hp2)
          omega
      subst hf1
      rw [pow_one] at hq8 hK
      by_cases hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥
      · exact ⟨p, by omega, hp, K, inferInstance, inferInstance,
          Or.inl ⟨by omega, hK, Or.inr ⟨(mulEquivTwoResidualQuot hL hZ).trans eK⟩⟩⟩
      · obtain ⟨K', _, _, hK', ⟨eL⟩⟩ := (hCov ↥(twoResidual (⊤ : Subgroup D)) hS.quasisimple
          hS.center hZ p hp hp2).1 ⟨hadm, K, inferInstance, inferInstance, by rw [hK, pow_one],
            ⟨eK⟩⟩
        exact ⟨p, by omega, hp, K', inferInstance, inferInstance, Or.inl ⟨by omega, hK',
          Or.inl ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans eL⟩⟩⟩
    ·
      have : Fact p.Prime := ⟨hp⟩
      let eK : TwoResidualQuot D ≃* StatedProj (StatedSU 3 (p ^ f) K) := eK₀
      have hadm : StatedLieAdmissible .PSU 3 p f := hadm₀
      have hf1 : f = 1 := by
        have : Finite (StatedProj (StatedSU 3 (p ^ f) K)) := Finite.of_equiv _ eK.toEquiv
        have : Finite K := ‹Finite K›
        have h1 := CFSG.SectionRank.ClassicalOdd.two_mul_le_pRank_SU_three (K := K) hp2 hK
        have h2 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp
          (CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv eK.symm hS.sqt)) p hp hp2
        omega
      subst hf1
      rw [pow_one] at hq4
      have hq8 : p % 8 = 3 := by
        by_contra hne
        have h1 : p % 8 = 7 := by omega
        apply hn64
        rw [Nat.card_congr eK.toEquiv, card_statedProj_su_three hp le_rfl hK, pow_one]
        exact sixtyfour_dvd_card_psu_three h1
      have hK2 : Nat.card K = p ^ 2 := by rw [hK, pow_one]
      have eK' : TwoResidualQuot D ≃* StatedProj (StatedSU 3 p K) := by
        rw [← pow_one p]
        exact eK
      by_cases hZ : Subgroup.center ↥(twoResidual (⊤ : Subgroup D)) = ⊥
      · exact ⟨p, Or.inl hq8, hp, K, inferInstance, inferInstance,
          Or.inr ⟨hq4, hK2, Or.inr ⟨(mulEquivTwoResidualQuot hL hZ).trans eK'⟩⟩⟩
      · obtain ⟨K', _, _, hK', ⟨eL⟩⟩ := (hCov ↥(twoResidual (⊤ : Subgroup D)) hS.quasisimple
          hS.center hZ p hp hp2).2 ⟨hadm, K, inferInstance, inferInstance, hK, ⟨eK⟩⟩
        exact ⟨p, Or.inl hq8, hp, K', inferInstance, inferInstance, Or.inr ⟨hq4, hK',
          Or.inl ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hL.symm)).trans eL⟩⟩⟩

end F6

end CFSG.Quasithin
