module

public import CFSG.Milestones.ASVolI.C4
public import CFSG.Quasithin.Background.C41PfJ
public import CFSG.Quasithin.Background.C41PfU
public import CFSG.Quasithin.Background.C41PfK
public import CFSG.Quasithin.Background.Asc82Holds
public import CFSG.Quasithin.Background.SmithC27Assemble
public import CFSG.Quasithin.Background.SmithC27RCaseIIG2Iso
public import CFSG.Quasithin.Background.SmithC27RCaseIIStar
public import CFSG.Quasithin.Background.SmithC27RCaseIMain
public import CFSG.Quasithin.Background.SmithC27RTypeCases
public import CFSG.Quasithin.Vol2.KGFactLem1211G2

public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideC4h_two_pow_mul_odd_inj {a b u w : ℕ} (hu : Odd u) (hw : Odd w)
    (h : 2 ^ a * u = 2 ^ b * w) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : 2 ^ a * u = 2 ^ a * (2 ^ (k + 1) * w) := by
      rw [h, show a + k + 1 = a + (k + 1) by ring, pow_add, mul_assoc]
    have h3 : u = 2 ^ (k + 1) * w := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have : Even u := by
      rw [h3]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right _
    exact (Nat.not_even_iff_odd.mpr hu) this
  · exact hab
  · exfalso
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : 2 ^ b * (2 ^ (k + 1) * u) = 2 ^ b * w := by
      rw [← h]
      ring
    have h3 : 2 ^ (k + 1) * u = w := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have : Even w := by
      rw [← h3]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right _
    exact (Nat.not_even_iff_odd.mpr hw) this

theorem burnsideC4h_sl2_ne {n : ℕ} (hn : 2 ≤ n) {e : ℕ}
    (he : e = 360 ∨ e = 979200 ∨ e = 20160 ∨ e = 9999360 ∨ e = 2520) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ e := by
  intro h
  have hn' : n ≤ 24 := by
    by_contra hbig
    have h24 : 2 ^ 25 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ n * 3 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      apply Nat.mul_le_mul_left
      have : 4 ≤ (2 ^ n) ^ 2 := by nlinarith [Nat.one_le_two_pow (n := n)]
      omega
    rcases he with rfl | rfl | rfl | rfl | rfl <;> omega
  interval_cases n <;> rcases he with rfl | rfl | rfl | rfl | rfl <;> norm_num at h

theorem burnsideC4h_odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact ⟨2 ^ j - 1, by omega⟩

theorem burnsideC4h_sl3_ne_sl2 {m n : ℕ} (hm : 1 ≤ m) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h3 : 1 ≤ (2 ^ m) ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h4 : 4 ≤ (2 ^ m) ^ 2 := by nlinarith
    have h5 : 8 ≤ (2 ^ m) ^ 3 := by nlinarith
    have : 0 < ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hodd1 : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
    refine Odd.mul ?_ ?_
    · rw [← pow_mul]; exact burnsideC4h_odd_two_pow_sub_one (by omega)
    · rw [← pow_mul]; exact burnsideC4h_odd_two_pow_sub_one (by omega)
  have hodd2 : Odd ((2 ^ n) ^ 2 - 1) := by
    rw [← pow_mul]; exact burnsideC4h_odd_two_pow_sub_one (by omega)
  have e1 : (2 ^ m) ^ 3 = 2 ^ (3 * m) := by rw [← pow_mul, mul_comm]
  have h' : 2 ^ (3 * m) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by rw [← e1]; exact h
  have hn3 : 3 * m = n := burnsideC4h_two_pow_mul_odd_inj hodd1 hodd2 h'
  subst hn3
  set a := 2 ^ m with ha
  have ha2 : 2 ≤ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hb : (2 ^ (3 * m)) = a ^ 3 := by rw [ha, ← pow_mul]; ring_nf
  rw [hb] at h
  have hc : ((a ^ 3) ^ 2 - 1) = (a ^ 3 - 1) * (a ^ 3 + 1) := by
    have : 1 ≤ a ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [this, show 1 ≤ (a ^ 3) ^ 2 from Nat.one_le_pow _ _ this]
    ring
  rw [hc] at h
  have hpos : 0 < a ^ 3 * (a ^ 3 - 1) := by
    have : 8 ≤ a ^ 3 :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ a ^ 3 := Nat.pow_le_pow_left ha2 3
    exact Nat.mul_pos (by omega) (by omega)
  have h2 : a ^ 3 * (a ^ 3 - 1) * ((a ^ 2 - 1)) = a ^ 3 * (a ^ 3 - 1) * (a ^ 3 + 1) := by
    calc a ^ 3 * (a ^ 3 - 1) * (a ^ 2 - 1) = a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) := by ring
      _ = a ^ 3 * ((a ^ 3 - 1) * (a ^ 3 + 1)) := h
      _ = _ := by ring
  have h3 := Nat.eq_of_mul_eq_mul_left hpos h2
  have : a ^ 2 ≤ a ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem burnsideC4h_sl3_ne_small {m : ℕ} (hm : 1 ≤ m) {e : ℕ} (he : e = 60 ∨ e = 2520) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ e := by
  intro h
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    rcases he with rfl | rfl <;> norm_num at h
  · have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    have h1 : 16 ≤ (2 ^ m) ^ 2 := by nlinarith
    have h2 : 64 ≤ (2 ^ m) ^ 3 := by nlinarith
    have h3 : 64 * (15 * 63) ≤ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
      apply Nat.mul_le_mul h2
      exact Nat.mul_le_mul (by omega) (by omega)
    rcases he with rfl | rfl <;> omega

theorem burnsideC4h_sl3_ne_list {m : ℕ} (hm : 1 ≤ m) {e : ℕ}
    (he : e = 60 ∨ e = 360 ∨ e = 1080 ∨ e = 2520 ∨ e = 6048 ∨ e = 20160 ∨ e = 979200 ∨
      e = 9999360) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ e := by
  intro h
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · rcases (show m = 1 ∨ m = 2 by omega) with rfl | rfl <;>
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at h
  · have h8 : 8 ≤ 2 ^ m := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
    have h2 : 64 ≤ (2 ^ m) ^ 2 := by nlinarith
    have h3 : 512 ≤ (2 ^ m) ^ 3 := by nlinarith
    have h4 : 512 * (63 * 511) ≤ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem burnsideC4h_chi_order_clash {e : ℕ}
    (hchi : e = 60 ∨ e = 2520 ∨ ∃ n : ℕ, 2 ≤ n ∧ e = 2 ^ n * ((2 ^ n) ^ 2 - 1)) :
    e ≠ 360 ∧ e ≠ 979200 ∧ e ≠ 20160 ∧ e ≠ 9999360 ∧
      ∀ m : ℕ, 1 ≤ m → e ≠ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases hchi with rfl | rfl | ⟨n, hn, rfl⟩
    · norm_num
    · norm_num
    · exact burnsideC4h_sl2_ne hn (Or.inl rfl)
  · rcases hchi with rfl | rfl | ⟨n, hn, rfl⟩
    · norm_num
    · norm_num
    · exact burnsideC4h_sl2_ne hn (Or.inr (Or.inl rfl))
  · rcases hchi with rfl | rfl | ⟨n, hn, rfl⟩
    · norm_num
    · norm_num
    · exact burnsideC4h_sl2_ne hn (Or.inr (Or.inr (Or.inl rfl)))
  · rcases hchi with rfl | rfl | ⟨n, hn, rfl⟩
    · norm_num
    · norm_num
    · exact burnsideC4h_sl2_ne hn (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · intro m hm
    rcases hchi with rfl | rfl | ⟨n, hn, rfl⟩
    · exact fun h => burnsideC4h_sl3_ne_small hm (Or.inl rfl) h.symm
    · exact fun h => burnsideC4h_sl3_ne_small hm (Or.inr rfl) h.symm
    · exact fun h => burnsideC4h_sl3_ne_sl2 hm h.symm

theorem burnsideC4h_card_quot_eq {G X : Type} [Group G] [Group X] {K : Subgroup G}
    (α : ↥K →* X) (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card X :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

theorem burnsideC4h_card_alt {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

open CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.QuasithinUnique in
theorem burnsideC4h_card_chi {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}
    (h : Hyp27 H R M K) (hchi : IsChiBlock2 H K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60 ∨ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 ∨
      ∃ n : ℕ, 2 ≤ n ∧ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rcases hchi.2 with ⟨n, hn, hL⟩ | ⟨m, hm, htype⟩
  · right; right
    obtain ⟨F, _, _, hF, α, hα, hker, -⟩ := hL
    refine ⟨n, hn, ?_⟩
    have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
    rw [burnsideC4h_card_quot_eq α hα hker, ← StatedAPI.card_statedSL, StatedAPI.card_statedSL_two, hq]
  · rcases five_or_seven_of_isAltType h hm htype with rfl | rfl
    · left
      obtain ⟨e⟩ := nonempty_quotEquiv_of_isAltType htype
      rw [Nat.card_congr e.toEquiv, burnsideC4h_card_alt (by norm_num)]
      decide
    · right; left
      obtain ⟨e⟩ := nonempty_quotEquiv_of_isAltType htype
      rw [Nat.card_congr e.toEquiv, burnsideC4h_card_alt (by norm_num)]
      decide

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_4_4
    : C_4_4 := by
  intro G _ _ H R M L V T K hSet
  exact CFSG.Quasithin.C41Pf.le_normalizer CFSG.Quasithin.asc82Thm2_holds
    CFSG.Quasithin.H13.a3ForSQTK_holds.1 CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
    (fun _ _ hX => CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hX)
    (CFSG.Quasithin.H13.VolI.asc129Statement_holds G) (CFSG.Quasithin.asc111Statement_holds G)
    (CFSG.Quasithin.asc19Statement_holds G) CFSG.Quasithin.C41Pf.c41KGBorel_holds
    hSet.hyp.hyp hSet.hyp.comp hSet.hyp.charTwo hSet.hyp.quasi hSet.hyp.not_le

end

open CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC4h_c46_core {G : Type} [Group G] [Finite G]
    (hC27 : ∀ {H R M K : Subgroup G}, Hyp27 H R M K → IsChiBlock2 H K →
      C27Concl H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hElim : C41Elim G) (hC46 : C46Block G)
    (hnc : ∀ {H R M L V K : Subgroup G}, HypC28 H R M L V → K ∈ cComp H → ¬ K ≤ M →
      ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K)
    {H R M L V T K : Subgroup G} (hSet : SetC41 H R M L V T K)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hM0 : conjClosure L M ≤ M ⊓ K)
    (hchi : IsChiBlock2 H K) : IsAltType K 7 ∧ C41Case1 R M L V K := by
  classical
  have hhyp := hSet.hyp
  have hP : C41Post H R M L V K :=
    { hyp := hhyp.hyp, comp := hhyp.comp, charTwo := hhyp.charTwo, quasi := hhyp.quasi,
      not_le := hhyp.not_le, le_normalizer := hRN, le := hM0.trans inf_le_right,
      not_commutator_le := hnc hhyp.hyp hhyp.comp hhyp.not_le }
  have h27 : Hyp27 H R M K :=
    Hyp27.mk' (c2_10_four hhyp.hyp) hhyp.comp hhyp.quasi hhyp.charTwo hhyp.not_le hRN
  obtain ⟨h1, h2, h3⟩ := (c27Concl_iff).mp (hC27 h27 hchi)
  have hcard := burnsideC4h_card_chi h27 hchi
  have hclash := burnsideC4h_chi_order_clash hcard
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rcases hchi.2 with ⟨n, hn, hL⟩ | ⟨m, hm, htype⟩
    · exact center_eq_bot_of_lin2 hL
    · obtain ⟨α, hα, hker, -⟩ := id htype
      exact center_quot_eq_bot_of_surj (five_or_seven_of_isAltType h27 hm htype) α hα hker
  obtain ⟨eKV⟩ := h27.starHyp.quotEquiv hZ
  have hcardV : Nat.card ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) =
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := (Nat.card_congr eKV.toEquiv).symm
  have hcases : SBc17.C27Cases H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := by
    rcases h3 with ⟨hb, h1 | h2 | h3 | h4⟩ | hb | hc | hd | he | hf | hg | hh
    · exact Or.inl ⟨hb, h1⟩
    · exact Or.inr (Or.inl ⟨hb, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hb, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, h4⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hg)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr hh)))))))))
  rcases hcases with hL2 | hA5 | hA7a | hA7b | hAlt | hHat6 | hExc | hA6Sp4 | hG2 | hSL3 | hL45
  · exact (hElim H R M L V K hP h1 h2 (Or.inl hL2)).elim
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inl hA5))).elim
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inr (Or.inl hA7a)))).elim
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inr (Or.inr (Or.inl hA7b))))).elim
  ·
    have hAlt' := hAlt
    obtain ⟨⟨n, α, hn5, hn8, hshort, hαw, t, htR, htV, hRt, ht2, σ, hσ, hconj⟩, hMK⟩ := hAlt
    have h := hP.hyp
    have hM₀1 : conjClosure L M ≠ ⊥ := fun hb => ne_bot_of_mem_cComp h.comp
      (eq_bot_iff.mpr ((le_conjClosure L M).trans hb.le))
    have hn7 : 7 ≤ n := by
      by_contra hlt
      exact hM₀1 (C41Pf.eq_bot_of_alt_transposition hP.le_normalizer h1 hn5 (by omega) α hαw.1
        hαw.2.1 htR htV hσ hconj hMK hP.le (C2Nine.conjClosure_le_M h)
        (C2Nine.perfect_conjClosure_of_hyp h))
    have hcardn : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = n.factorial / 2 := by
      rw [burnsideC4h_card_quot_eq α hαw.1 hαw.2.1, burnsideC4h_card_alt (by omega)]
    have hn7' : n = 7 := by
      rcases (show n = 7 ∨ n = 8 by omega) with h7 | h8
      · exact h7
      · exfalso
        subst h8
        exact hclash.2.2.1 (by rw [hcardn]; decide)
    subst hn7'
    have hcard2520 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 := by rw [hcardn]; decide
    have hK7 : IsAltType K 7 := by
      rcases hchi.2 with ⟨n, hn, hL⟩ | ⟨m, hm, htype⟩
      · exfalso
        have := burnsideC4h_card_chi h27 hchi
        obtain ⟨F, _, _, hF, α', hα', hker', -⟩ := hL
        have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
        have hc2 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
          rw [burnsideC4h_card_quot_eq α' hα' hker', ← StatedAPI.card_statedSL,
            StatedAPI.card_statedSL_two, hq]
        exact burnsideC4h_sl2_ne hn (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (hc2.symm.trans hcard2520)
      · rcases five_or_seven_of_isAltType h27 hm htype with rfl | rfl
        · exfalso
          obtain ⟨e⟩ := nonempty_quotEquiv_of_isAltType htype
          rw [Nat.card_congr e.toEquiv, burnsideC4h_card_alt (by norm_num)] at hcard2520
          revert hcard2520
          decide
        · exact htype
    obtain ⟨hCR, hMKR⟩ := C41Pf.inf_eq_of_c27Alt hP h1 (by omega) α hαw.1 hαw.2.1 htV hRt ht2 hMK
    have hKRN : K ⊔ R ≤ Subgroup.normalizer
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ R)).trans
        (normalizer_le_normalizer_omegaOneCenterOf _)
    have hCK : K ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) ≤
        pCoreOf 2 K :=
      (C41Pf.inf_centralizer_le_oTwoZIn h1).trans
        (C41Pf.oTwoZIn_le_pCoreOf (C41Pf.center_eq_bot_of_alt (by omega) α hαw.1 hαw.2.1))
    have hIT := C41Pf.inducesTransposition_of_c27Alt hP.le_normalizer (le_sup_left.trans hKRN)
      (le_sup_right.trans hKRN) hCK α hαw htR htV hRt ht2 hσ hconj
    obtain ⟨hMb, hV⟩ := hC46 H R M L V K 7 α hP h1 h2 hAlt' hshort hαw hn7 hn8 hIT hMKR
    exact ⟨hK7, 5, Or.inl rfl, hMb, hV, ⟨hshort, α, hαw⟩, hIT, hMKR⟩
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hHat6)))))).elim
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl hExc))))))).elim
  ·
    exfalso
    rcases hA6Sp4.1 with hA6 | hSp
    · obtain ⟨-, α, hαw⟩ := hA6
      rw [burnsideC4h_card_quot_eq α hαw.1 hαw.2.1, burnsideC4h_card_alt (by norm_num)] at hclash
      exact hclash.1 (by decide)
    · obtain ⟨-, F, _, _, hF4, α, hα, hker, -⟩ := hSp
      have hq : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF4]
      rw [burnsideC4h_card_quot_eq α hα hker,
        LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two F, hq] at hclash
      exact hclash.2.1 (by norm_num)
  · exact (hElim H R M L V K hP h1 h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr hG2))))))).elim
  ·
    exfalso
    obtain ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ := hSL3
    have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
    have hc3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) =
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [← hcardV, Nat.card_congr e.toEquiv, StatedAPI.card_statedSL_three, hq]
    exact hclash.2.2.2.2 n hn1 hc3
  ·
    exfalso
    obtain ⟨he | he, -, -⟩ := hL45
    · obtain ⟨e⟩ := he
      rw [← hcardV, Nat.card_congr e.toEquiv, StatedAPI.card_statedSL_four_zmod_two] at hclash
      exact hclash.2.2.1 rfl
    · obtain ⟨e⟩ := he
      rw [← hcardV, Nat.card_congr e.toEquiv, StatedAPI.card_statedSL_five_zmod_two] at hclash
      exact hclash.2.2.2.1 rfl

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem as_C_4_6
    : C_4_6 := by
  intro G _ _ H R M L V T K hSet hRN hM0 _hK0 hchi
  have hA3 : CFSG.Quasithin.A3Orbits G :=
    CFSG.Quasithin.a3Orbits_of_a37_a38 CFSG.Quasithin.H13.a3ForSQTK_holds.1
      CFSG.Quasithin.H13.a3ForSQTK_holds.2.1
  exact burnsideC4h_c46_core
    (fun {H R M K} h hchi => SmithC27.c27Concl_of_cases (CFSG.Quasithin.H13.VolI.asc129Statement_holds G)
      (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
      asA21SQTKSection asA36NoOddCover_holds B5.asB51_holds h (Or.inl hchi))
    (C41Pf.c41Elim_of H13.KGG2.lem1211NNG2_holds) C41Pf.c46Block_holds
    (fun hH hK hKM => C41Pf.not_commutator_le_pCoreOf (H13.VolI.asc129Statement_holds G)
      (asc111Statement_holds G) (asc19Statement_holds G) hA3 hH hK hKM)
    hSet hRN hM0 hchi

end

section C45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

variable {G : Type} [Group G] [Finite G]

theorem burnsideC4h_cent_le_sup {K R S : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf S ((K ⊔ R) ⊓ C41Pf.centModO2 K)) :
    (K ⊔ R) ⊓ C41Pf.centModO2 K ≤ S ⊔ ((K ⊔ R) ⊓ C41Pf.centModO2 K ⊓ K) := by
  set D := (K ⊔ R) ⊓ C41Pf.centModO2 K with hD
  have hDN : D ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_right.trans (C41Pf.centModO2_le_normalizer K)
  set T := S ⊔ (D ⊓ K) with hT
  have hST : S ≤ T := le_sup_left
  have hTD : T ≤ D := sup_le hS.1 inf_le_left
  have hodd : ¬ 2 ∣ S.relIndex D := hS.2.2
  have h1 : T.relIndex D ∣ S.relIndex D :=
    Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex S T D hST hTD)
  have h2 : T.relIndex D ∣ (D ⊓ K).relIndex D :=
    Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex (D ⊓ K) T D le_sup_right hTD)
  have h3 : (D ⊓ K).relIndex D = K.relIndex D := by
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
  have h4 : K.relIndex D = K.relIndex (D ⊔ K) :=
    (A4.relIndex_sup_eq_of_le_normalizer' hDN).symm
  have h5 : K.relIndex (D ⊔ K) ∣ K.relIndex (K ⊔ R) :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex K (D ⊔ K) (K ⊔ R) le_sup_right
      (sup_le (inf_le_left) le_sup_left))
  have h6 : K.relIndex (K ⊔ R) = K.relIndex R := by
    rw [sup_comm]
    exact A4.relIndex_sup_eq_of_le_normalizer' hRN
  obtain ⟨n, hn⟩ := hR2.index (K.subgroupOf R)
  have h7 : T.relIndex D ∣ 2 ^ n := by
    have : K.relIndex R = 2 ^ n := hn
    rw [← this, ← h6]
    exact h2.trans (h3 ▸ h4 ▸ h5)
  have h8 : T.relIndex D = 1 := by
    have hcop : Nat.Coprime (T.relIndex D) (S.relIndex D) := by
      apply Nat.Coprime.coprime_dvd_left h7
      apply Nat.Coprime.pow_left
      exact (Nat.prime_two.coprime_iff_not_dvd).mpr hodd
    exact Nat.Coprime.eq_one_of_dvd hcop h1
  exact Subgroup.relIndex_eq_one.mp h8

theorem burnsideC4h_cs_eq {X K : Subgroup G} (hXN : X ≤ Subgroup.normalizer (K : Set G)) :
    centralizerSection X K (pCoreOf 2 K) = X ⊓ C41Pf.centModO2 K := by
  ext g
  constructor
  · rintro ⟨hgX, hgN, -, hg⟩
    refine ⟨hgX, C41Pf.mem_centModO2_iff.mpr ⟨hgN, ?_⟩⟩
    rw [C41Pf.quotConjHom_eq_one_iff]
    intro y hy
    have := (pCoreOf 2 K).inv_mem (hg y hy)
    simpa [mul_assoc] using this
  · rintro ⟨hgX, hgC⟩
    obtain ⟨hgN, hg1⟩ := C41Pf.mem_centModO2_iff.mp hgC
    refine ⟨hgX, hgN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hgN, ?_⟩
    intro x hx
    have := (pCoreOf 2 K).inv_mem ((C41Pf.quotConjHom_eq_one_iff ⟨g, hgN⟩).mp hg1 x hx)
    simpa [mul_assoc] using this

open scoped Pointwise in
theorem burnsideC4h_c45_two {H R M L V K : Subgroup G} (h : HypC28 H R M L V) (hKH : K ≤ H)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hM0K : conjClosure L M ≤ K) :
    conjClosure L M ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) ≤
        (K ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ⊓
          Subgroup.normalizer ((R ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) :
            Subgroup G) : Set G) ∧
      (K ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ⊓
          Subgroup.normalizer ((R ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) :
            Subgroup G) : Set G) ≤
        (M ⊓ K) ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) := by
  classical
  have hNK : conjClosure L M ≤ Subgroup.normalizer (K : Set G) :=
    hM0K.trans Subgroup.le_normalizer
  have hX : R ⊔ conjClosure L M ⊔ K = K ⊔ R := by
    rw [sup_assoc, sup_eq_right.mpr hM0K, sup_comm]
  have hBN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRN
  rw [hX, burnsideC4h_cs_eq hBN]
  set D := (K ⊔ R) ⊓ C41Pf.centModO2 K with hD
  have hDN : D ≤ Subgroup.normalizer (K : Set G) :=
    inf_le_right.trans (C41Pf.centModO2_le_normalizer K)
  have hBD : K ⊔ R ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf Subgroup.le_normalizer (hBN.trans (C41Pf.normalizer_le_normalizer_centModO2 K))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hDsub : D ≤ K ⊔ R := inf_le_left
  have hRD : R ≤ Subgroup.normalizer (D : Set G) := le_sup_right.trans hBD
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := le_sup_left.trans hBD
  have hDnorm : D ≤ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) := by
    intro d hd
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have hdN : d ∈ Subgroup.normalizer (D : Set G) := hBD (hDsub hd)
    have hle : R ⊔ D ≤ (R ⊔ D).comap (MulAut.conj d).toMonoidHom := by
      refine sup_le (fun r hr => ?_) (fun e he => ?_)
      · show d * r * d⁻¹ ∈ R ⊔ D
        have h1 : r * d⁻¹ * r⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.mp (hRD hr) d⁻¹).mp (D.inv_mem hd)
        have : d * r * d⁻¹ = (d * (r * d⁻¹ * r⁻¹)) * r := by group
        rw [this]
        exact (R ⊔ D).mul_mem (Subgroup.mem_sup_right (D.mul_mem hd h1)) (Subgroup.mem_sup_left hr)
      · show d * e * d⁻¹ ∈ R ⊔ D
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hdN e).mp he)
    exact hle hx
  have hM0N : conjClosure L M ≤ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) :=
    (le_inf (c2_9_two h).1 (hM0K.trans (le_sup_left.trans hBD))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup R D)
  refine ⟨sup_le (le_inf (hM0K.trans le_sup_left) hM0N) (le_inf le_sup_right hDnorm), ?_⟩
  rintro y ⟨hyKD, hyN⟩
  have hO2 : pCoreOf 2 (K ⊔ R) ≤ R := C41Pf.pCoreOf_sup_le_of_hyp h hKH hNK
  have hNM : (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) ≤ M :=
    C41Pf.sup_inf_normalizer_le_of_hyp h hKH
  have hyKD' : y ∈ ((K : Set G) * (D : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K D hKD]
    exact hyKD
  obtain ⟨k, hk, d, hd, rfl⟩ := hyKD'
  have hdN : d ∈ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) := hDnorm hd
  have hkN : k ∈ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) := by
    have := (Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G)).mul_mem hyN
      ((Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G)).inv_mem hdN)
    simpa [mul_assoc] using this
  have hRsyl : IsSylowTwoOf R (R ⊔ D) := C41Pf.isSylowTwoOf_sup_cent hRN h.pgroup hO2
  have hkmap : ∀ g ∈ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G), ∀ x ∈ R ⊔ D,
      g * x * g⁻¹ ∈ R ⊔ D := fun g hg x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hkinv : k⁻¹ ∈ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) :=
    (Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G)).inv_mem hkN
  have hkRsyl : IsSylowTwoOf (conjByElt k R) (R ⊔ D) := by
    rw [A4.isSylowTwoOf_iff_maximal]
    refine ⟨?_, h.pgroup.map _, fun P hP hP2 hRP => ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      exact hkmap k hkN r (Subgroup.mem_sup_left hr)
    · have hPc : conjByElt k⁻¹ P ≤ R ⊔ D := by
        rintro _ ⟨p, hp, rfl⟩
        have := hkmap k⁻¹ hkinv p (hP hp)
        simpa using this
      have hRc : R ≤ conjByElt k⁻¹ P := by
        intro r hr
        refine ⟨k * r * k⁻¹, hRP ⟨r, hr, rfl⟩, ?_⟩
        simp [mul_assoc]
      have hmax := ((A4.isSylowTwoOf_iff_maximal.mp hRsyl).2.2 _ hPc (hP2.map _) hRc)
      intro p hp
      have : k⁻¹ * p * k⁻¹⁻¹ ∈ R := hmax ⟨p, hp, rfl⟩
      refine ⟨k⁻¹ * p * k⁻¹⁻¹, this, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨g, hgRD, hgc⟩ := A4.exists_conj_of_isSylowTwoOf hRsyl hkRsyl
  have hn0R : g⁻¹ * k ∈ Subgroup.normalizer (R : Set G) := by
    refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
    have hky : k * y * k⁻¹ ∈ conjByElt k R := ⟨y, hy, rfl⟩
    have := (hgc _).mp hky
    have e : g⁻¹ * k * y * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * y * k⁻¹) * g := by group
    rw [e]
    exact this
  obtain ⟨S, hS, -⟩ := A4.exists_isSylowTwoOf_ge (P := ⊥) (H := D) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  obtain ⟨-, hSO⟩ := C41Pf.le_pCoreOf_of_isSylowTwoOf_cent hRN h.pgroup hS
  have hSR : S ≤ R := hSO.trans hO2
  have hDle : D ≤ S ⊔ (D ⊓ K) := burnsideC4h_cent_le_sup hRN h.pgroup hS
  have hSN : S ≤ Subgroup.normalizer ((D ⊓ K : Subgroup G) : Set G) :=
    (le_inf (hSR.trans hRD) (hSR.trans hRN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hgDR : g ∈ ((D : Set G) * (R : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left D R hRD, sup_comm]
    exact hgRD
  obtain ⟨d₁, hd₁, r₁, hr₁, rfl⟩ := hgDR
  have hd₁' : d₁ ∈ ((D ⊓ K : Subgroup G) : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (D ⊓ K) S hSN, sup_comm]
    exact hDle hd₁
  obtain ⟨z, hz, s, hs, rfl⟩ := hd₁'
  have hzk : z⁻¹ * k ∈ Subgroup.normalizer (R : Set G) := by
    have hsr : s * r₁ ∈ R := R.mul_mem (hSR hs) hr₁
    have e : z⁻¹ * k = (s * r₁) * ((z * s * r₁)⁻¹ * k) := by group
    rw [e]
    exact (Subgroup.normalizer (R : Set G)).mul_mem (Subgroup.le_normalizer hsr) hn0R
  have hzK : z ∈ K := hz.2
  have hzD : z ∈ D := hz.1
  have hzkK : z⁻¹ * k ∈ K := K.mul_mem (K.inv_mem hzK) hk
  have hzkM : z⁻¹ * k ∈ M := hNM ⟨(Subgroup.mem_sup_left hzkK), hzk⟩
  have hfin : z * (z⁻¹ * k) * d = k * d := by group
  have : z * (z⁻¹ * k) * d ∈ (M ⊓ K) ⊔ D :=
    ((M ⊓ K) ⊔ D).mul_mem (((M ⊓ K) ⊔ D).mul_mem (Subgroup.mem_sup_right hzD)
      (Subgroup.mem_sup_left ⟨hzkM, hzkK⟩)) (Subgroup.mem_sup_right hd)
  rwa [hfin] at this

theorem burnsideC4h_normal_of_kzero (hA3 : A3Orbits G)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hK0 : C41KZero G) {H R M L V K : Subgroup G} (h : HypC28 H R M L V) (hK : K ∈ cComp H)
    (hKc : CharTwo K) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ M)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hnc : ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K) :
    H ≤ Subgroup.normalizer (K : Set G) ∧ conjClosure L M ≤ K := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hNK := C41Pf.conjClosure_le_normalizer hA3 h hK
  have hOut := hSch K (h.sqtk.mono hKH) hKq
  have hO2 := C41Pf.pCoreOf_sup_le_of_hyp h hKH hNK
  have hNM := C41Pf.sup_inf_normalizer_le_of_hyp h hKH
  have hcomp : ∀ m ∈ M, conjByElt m L ∈ cComp M := fun m hm =>
    C2Nine.conjByElt_mem_cComp h.comp (Subgroup.le_normalizer hm)
  have hex : ∃ m ∈ M, conjByElt m L ≤ K := by
    by_contra hne
    push Not at hne
    refine hnc (C41Pf.commutator_le_of_le_centModO2 (conjClosure_le fun m hm l hl => ?_))
    have hLmM₀ : conjByElt m L ≤ conjClosure L M := conjByElt_le_conjClosure hm
    have hc := (C41Pf.le_or_commutator_le_of_cComp hOut hRN h.pgroup hO2 h.le_M hNM (hcomp m hm)
      (hLmM₀.trans hNK) (hLmM₀.trans (c2_9_two h).1)).resolve_left (hne m hm)
    have hmem : m * l * m⁻¹ ∈ conjByElt m L := by
      rw [mem_conjByElt]
      simpa [mul_assoc] using hl
    exact C41Pf.le_centModO2_of_commutator_le (hLmM₀.trans hNK) hc hmem
  obtain ⟨m, hm, hmK⟩ := hex
  have hHN := hK0 H R M L V K h hK hKc hKq hKM hRN ⟨conjByElt m L,
    ne_bot_of_mem_cComp (hcomp m hm), perfect_of_mem_cComp (hcomp m hm),
    le_inf (le_of_mem_cComp (hcomp m hm)) hmK,
    (conjByElt_le_conjClosure hm).trans (c2_9_two h).1⟩
  exact ⟨hHN, C41Pf.conjClosure_le_of_le_normalizer hOut h hKH hRN hNK (h.le_H.trans hHN) hnc⟩

theorem burnsideC4h_c45_core (hA3 : A3Orbits G)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hK0 : C41KZero G)
    (hnc : ∀ {H R M L V K : Subgroup G}, HypC28 H R M L V → K ∈ cComp H → ¬ K ≤ M →
      ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K)
    {H R M L V T K : Subgroup G} (hSet : SetC41 H R M L V T K)
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) :
    (conjClosure L M ≤ M ⊓ K ∧ ((conjClosure L M).subgroupOf (M ⊓ K)).Normal) ∧
      (conjClosure L M ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K) ≤
          (K ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ⊓
            Subgroup.normalizer ((R ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K
              (pCoreOf 2 K) : Subgroup G) : Set G) ∧
        (K ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ⊓
            Subgroup.normalizer ((R ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K
              (pCoreOf 2 K) : Subgroup G) : Set G) ≤
          (M ⊓ K) ⊔ centralizerSection (R ⊔ conjClosure L M ⊔ K) K (pCoreOf 2 K)) ∧
      K = conjClosure K H := by
  have hhyp := hSet.hyp
  have h := hhyp.hyp
  have hKH : K ≤ H := le_of_mem_cComp hhyp.comp
  obtain ⟨hHN, hM0K⟩ := burnsideC4h_normal_of_kzero hA3 hSch hK0 h hhyp.comp hhyp.charTwo
    hhyp.quasi hhyp.not_le hRN (hnc h hhyp.comp hhyp.not_le)
  refine ⟨⟨le_inf (C2Nine.conjClosure_le_M h) hM0K,
    Subgroup.normal_subgroupOf_of_le_normalizer
      (inf_le_left.trans (le_normalizer_conjClosure L M))⟩,
    burnsideC4h_c45_two h hKH hRN hM0K, ?_⟩
  exact le_antisymm (le_conjClosure K H)
    (conjClosure_le fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (hHN hx) k).mp hk)

end C45

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC4h_c45_of_kzero
    (hK0 : ∀ (G : Type) [Group G] [Finite G], C41KZero G) :
    C_4_5 := by
  intro G _ _ H R M L V T K hSet hRN
  have hA3 : A3Orbits G :=
    a3Orbits_of_a37_a38 H13.a3ForSQTK_holds.1 H13.a3ForSQTK_holds.2.1
  exact burnsideC4h_c45_core hA3 (fun K hK hq => C41Pf.outSolvable_of_isSQTKIn K hK hq) (hK0 G)
    (fun hH hK hKM => C41Pf.not_commutator_le_pCoreOf (H13.VolI.asc129Statement_holds G)
      (asc111Statement_holds G) (asc19Statement_holds G) hA3 hH hK hKM)
    hSet hRN

end

section C42

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

variable {G : Type} [Group G] [Finite G]

theorem burnsideC4h_c42_local_closure (hA3 : A3Orbits G) {H R M L V T : Subgroup G}
    (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M) {X : Subgroup G} (hTX : T ≤ X) :
    conjClosure L (M ⊓ X) = conjClosure L M := by
  refine le_antisymm (conjClosure_mono le_rfl inf_le_left) (conjClosure_le fun m hm l hl => ?_)
  have hmem : conjByElt m L ∈ conjSubgroupsBy M L := ⟨m, hm, rfl⟩
  rw [(c2_9_one hA3 h hT).1] at hmem
  obtain ⟨t, ht, he⟩ := hmem
  have htMX : t ∈ M ⊓ X := ⟨hT.1 ht, hTX ht⟩
  have he' : conjByElt m L = conjByElt t L := he
  have : m * l * m⁻¹ ∈ conjByElt t L := by
    rw [← he']
    exact ⟨l, hl, rfl⟩
  exact conjByElt_le_conjClosure htMX this

theorem burnsideC4h_c42_core (hA3 : A3Orbits G)
    (hKnorm : ∀ {H R M L V K : Subgroup G}, HypC41 H R M L V K → H ≤ Subgroup.normalizer (K : Set G))
    (hpres : ∀ (H R M L V T K : Subgroup G), HypC41 H R M L V K → IsSylowTwoOf T M → R ≤ T →
      conjClosure K H ⊔ conjClosure L M ⊔ T ≤ H ∧
        HypC41 (conjClosure K H ⊔ conjClosure L M ⊔ T) R
          (M ⊓ (conjClosure K H ⊔ conjClosure L M ⊔ T)) L V K)
    (H R M L V T K : Subgroup G) (hyp : HypC41 H R M L V K) (hT : IsSylowTwoOf T M)
    (hRT : R ≤ T) :
    let X := conjClosure K H ⊔ conjClosure L M ⊔ T
    (conjClosure L M ⊔ T ≤ X ∧ X ≤ H) ∧ HypC41 X R (M ⊓ X) L V K ∧
      SetC41 X R (M ⊓ X) L V T K ∧ conjClosure L (M ⊓ X) = conjClosure L M ∧
      (C41Concl X R (M ⊓ X) L V K →
        conjClosure K H = conjClosure K X ∧ C41Concl H R M L V K) := by
  intro X
  obtain ⟨hXH, hXhyp⟩ := hpres H R M L V T K hyp hT hRT
  have hHN := hKnorm hyp
  have hK0 : conjClosure K H = K :=
    le_antisymm (conjClosure_le fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (hHN hx) k).mp hk)
      (le_conjClosure K H)
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := hXH.trans hHN
  have hKX : conjClosure K X = K :=
    le_antisymm (conjClosure_le fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (hXN hx) k).mp hk)
      (le_conjClosure K X)
  have hTX : T ≤ X := le_sup_right
  have hloc : conjClosure L (M ⊓ X) = conjClosure L M :=
    burnsideC4h_c42_local_closure hA3 hyp.hyp hT hTX
  refine ⟨⟨sup_le_sup_right le_sup_right T, hXH⟩, hXhyp, ?_, hloc, fun hc => ?_⟩
  · refine ⟨hXhyp, A4.isSylowTwoOf_mono hT (le_inf hT.1 hTX) inf_le_left, hRT, ?_⟩
    rw [hKX, hloc]
    show conjClosure K H ⊔ conjClosure L M ⊔ T = K ⊔ conjClosure L M ⊔ T
    rw [hK0]
  · exact ⟨hK0.trans hKX.symm, c41Concl_of_reduction_identifications (hKX.trans hK0.symm) hloc
      (c42_local_intersection_eq H M L T K) hc⟩

theorem burnsideC4h_hypC41_normal_of_kzero (hA3 : A3Orbits G)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hK0 : C41KZero G)
    (hRN : ∀ {H R M L V K : Subgroup G}, HypC41 H R M L V K →
      R ≤ Subgroup.normalizer (K : Set G))
    (hnc : ∀ {H R M L V K : Subgroup G}, HypC28 H R M L V → K ∈ cComp H → ¬ K ≤ M →
      ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K)
    {H R M L V K : Subgroup G} (hyp : HypC41 H R M L V K) :
    H ≤ Subgroup.normalizer (K : Set G) :=
  (burnsideC4h_normal_of_kzero hA3 hSch hK0 hyp.hyp hyp.comp hyp.charTwo hyp.quasi hyp.not_le
    (hRN hyp) (hnc hyp.hyp hyp.comp hyp.not_le)).1

end C42

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC in
theorem burnsideC4h_c42_of_kzero
    (hK0 : ∀ (G : Type) [Group G] [Finite G], C41KZero G) :
    C_4_2 := by
  intro G _ _ H R M L V T K hyp hT hRT
  have hA3 : A3Orbits G :=
    a3Orbits_of_a37_a38 H13.a3ForSQTK_holds.1 H13.a3ForSQTK_holds.2.1
  have hRN : ∀ {H R M L V K : Subgroup G}, HypC41 H R M L V K →
      R ≤ Subgroup.normalizer (K : Set G) := fun hyp =>
    C41Pf.le_normalizer asc82Thm2_holds H13.a3ForSQTK_holds.1 H13.a3ForSQTK_holds.2.1
      (fun _ _ hX => Vol2Native.L122A.isSimpleGroup_of_a38Types hX)
      (H13.VolI.asc129Statement_holds G) (asc111Statement_holds G) (asc19Statement_holds G)
      C41Pf.c41KGBorel_holds hyp.hyp hyp.comp hyp.charTwo hyp.quasi hyp.not_le
  have hnc : ∀ {H R M L V K : Subgroup G}, HypC28 H R M L V → K ∈ cComp H → ¬ K ≤ M →
      ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K := fun hH hK hKM =>
    C41Pf.not_commutator_le_pCoreOf (H13.VolI.asc129Statement_holds G)
      (asc111Statement_holds G) (asc19Statement_holds G) hA3 hH hK hKM
  exact burnsideC4h_c42_core hA3
    (burnsideC4h_hypC41_normal_of_kzero hA3 (fun K hK hq => C41Pf.outSolvable_of_isSQTKIn K hK hq)
      (hK0 G) hRN hnc)
    (fun H R M L V T K hyp hT hRT =>
      as_C_4_2_hypothesis_preservation G H R M L V T K hyp hT hRT) H R M L V T K hyp hT hRT

end

section C41Bridge

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

variable {G : Type} [Group G] [Finite G]

theorem burnsideC4h_not_le_normalizer_line {K V : Subgroup G} (hK : IsShort2 K) {ι : Type}
    [Fintype ι] {F : Type} [Field F] {β : ↥(blockU K) →* Multiplicative (ι → F)}
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ K).subgroupOf (blockU K))
    (hline : IsFLineVia (blockU K) (V ⊔ blockZ K) β) (hι : Fintype.card ι ≠ 2) :
    ¬ K ≤ Subgroup.normalizer ((V ⊔ blockZ K : Subgroup G) : Set G) := by
  intro hKN
  obtain ⟨hle, W, hW, hmem⟩ := hline
  have hZle : blockZ K ≤ V ⊔ blockZ K := le_sup_right
  rcases hK.2.2.2.2.2 (V ⊔ blockZ K) hZle hle hKN with hZ | hU
  ·
    have hW0 : W ≠ ⊥ := by
      intro h0
      rw [h0, finrank_bot] at hW
      omega
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hW0
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    have huW : Multiplicative.toAdd (β u) ∈ W := by rw [hu]; exact hwW
    have huV : (u : G) ∈ V ⊔ blockZ K := (hmem u).mpr huW
    rw [hZ] at huV
    have hu1 : β u = 1 := by
      rw [← MonoidHom.mem_ker, hβk]
      exact huV
    rw [hu1] at hu
    exact hw0 (by simpa using hu.symm)
  ·
    have hWtop : W = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
      have huV : (u : G) ∈ V ⊔ blockZ K := by rw [hU]; exact u.2
      have := (hmem u).mp huV
      rw [hu] at this
      exact this
    rw [hWtop, finrank_top, Module.finrank_fintype_fun_eq_card] at hW
    exact hι hW

theorem burnsideC4h_case2_bridge {H R M L V K : Subgroup G}
    (h : CFSG.Quasithin.C41Case2 H R M L V K) : C41Case2 M L V K := by
  obtain ⟨hSp, F, iF, fF, α, β, hF, hAB, hline, hmax, hMV, hpsl⟩ := h
  refine ⟨hSp, F, iF, fF, α, β, hF, hAB, hline, hmax, ?_, hpsl⟩
  have hZc : K ≤ Subgroup.centralizer ((blockZ K : Subgroup G) : Set G) := by
    intro g hg z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 g hg).symm
  have hZK : K ≤ Subgroup.normalizer ((blockZ K : Subgroup G) : Set G) :=
    hZc.trans (Subgroup.centralizer_le_normalizer _)
  have hVN : K ⊓ Subgroup.normalizer (V : Set G) ≤
      K ⊓ Subgroup.normalizer ((V ⊔ blockZ K : Subgroup G) : Set G) :=
    fun g ⟨hgK, hgV⟩ =>
      ⟨hgK, Subgroup.inf_normalizer_le_normalizer_sup V (blockZ K) ⟨hgV, hZK hgK⟩⟩
  have hMQ : M ⊓ K ≤ K ⊓ Subgroup.normalizer ((V ⊔ blockZ K : Subgroup G) : Set G) := by
    rw [hMV]
    exact hVN
  refine le_antisymm hMQ ?_
  set Q := K ⊓ Subgroup.normalizer ((V ⊔ blockZ K : Subgroup G) : Set G) with hQ
  obtain ⟨hpar, hne, hmaxi⟩ := hmax
  obtain ⟨-, S, hS, hSle⟩ := hpar
  have hQpar : IsParabolic2 K Q := ⟨inf_le_left, S, hS, hSle.trans hMQ⟩
  have hQK : Q ≠ K := by
    intro hQK
    have hKQ : K ≤ Q := hQK ▸ le_rfl
    exact burnsideC4h_not_le_normalizer_line hSp.1 hAB.2.2.1 hAB.2.2.2.1 hline
      (by simp) (fun g hg => (hKQ hg).2)
  exact (hmaxi Q hQpar hQK hMQ).le

@[expose] def burnsideC4h_C41Case4ClauseBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R M L V K : Subgroup G), HypC41 H R M L V K →
    CFSG.Quasithin.C41Case3 H R M L V K →
    C134CorrLocal.IsC134Case4Corr (K ⊔ R) R K → IsC134Case 4 (K ⊔ R) R K

theorem burnsideC4h_case3_bridge {H R M L V K : Subgroup G}
    (hClause : C134CorrLocal.IsC134Case4Corr (K ⊔ R) R K → IsC134Case 4 (K ⊔ R) R K)
    (h : CFSG.Quasithin.C41Case3 H R M L V K) : C41Case3 R M L V K := by
  obtain ⟨n, F, iF, fF, hn, hF, he, hMS, hCases, hmax, hpsl, hline⟩ := h
  refine ⟨n, F, iF, fF, hn, hF, he, hMS, ?_, hmax, hpsl, hline⟩
  rcases hCases with c | c | c | c
  · exact Or.inl c
  · exact Or.inr (Or.inl c)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (hClause c)))

theorem burnsideC4h_c41_of_wip
    (hWIP : ∀ (G : Type) [Group G] [Finite G], ASC41Statement G)
    (hClause : burnsideC4h_C41Case4ClauseBridge) : C_4_1 := by
  intro G _ _ H R M L V K hyp
  obtain ⟨h1, h2, h3, hcase⟩ :=
    hWIP G H R M L V K hyp.hyp hyp.comp hyp.charTwo hyp.quasi hyp.not_le
  refine ⟨h1, h2, h3, ?_⟩
  rcases hcase with c1 | c2 | c3 | c4
  · exact Or.inl c1
  · exact Or.inr (Or.inl (burnsideC4h_case2_bridge c2))
  · exact Or.inr (Or.inr (Or.inl (burnsideC4h_case3_bridge (hClause G H R M L V K hyp c3) c3)))
  · exact Or.inr (Or.inr (Or.inr c4))

end C41Bridge

section C47

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

variable {G : Type} [Group G] [Finite G]

theorem burnsideC4h_c47_of_wip
    (hWIP : ∀ (G : Type) [Group G] [Finite G], ASC41Statement G)
    (hClause : burnsideC4h_C41Case4ClauseBridge) : C_4_7 := by
  intro G _ _ H R M L V T K hSet hRN hM0 hK0 hSL
  obtain ⟨n, F, iF, fF, hF, ⟨e⟩⟩ := hSL
  have hyp := hSet.hyp
  obtain ⟨-, -, -, hcase⟩ :=
    hWIP G H R M L V K hyp.hyp hyp.comp hyp.charTwo hyp.quasi hyp.not_le
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hn1 : 1 ≤ n := by
    by_contra h0
    obtain rfl : n = 0 := by omega
    have h1 : Fintype.card F = 1 := by rw [hF]; rfl
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    omega
  have hcard : Nat.card (ModO2 K) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
    rw [Nat.card_congr e.toEquiv, StatedAPI.card_statedSL_three, hq]
  have hne : ∀ x : ℕ, (x = 60 ∨ x = 360 ∨ x = 1080 ∨ x = 2520 ∨ x = 6048 ∨ x = 20160 ∨
      x = 979200 ∨ x = 9999360) → Nat.card (ModO2 K) ≠ x := fun x hx h =>
    burnsideC4h_sl3_ne_list hn1 hx (hcard.symm.trans h)
  rcases hcase with c1 | c2 | c3 | c4
  ·
    exfalso
    obtain ⟨n', hn', -, -, ⟨-, α, hαw⟩, -⟩ := c1
    have hcA : Nat.card (ModO2 K) = (n' + 2).factorial / 2 := by
      rw [burnsideC4h_card_quot_eq α hαw.1 hαw.2.1, burnsideC4h_card_alt (by omega)]
    rcases hn' with rfl | rfl
    · exact hne 2520 (by norm_num) (by rw [hcA]; decide)
    · exact hne 20160 (by norm_num) (by rw [hcA]; decide)
  ·
    exfalso
    obtain ⟨⟨-, F', _, _, hF4, α, hα, hker, -⟩, -⟩ := c2
    have hq4 : Nat.card F' = 4 := by rw [Nat.card_eq_fintype_card, hF4]
    refine hne 979200 (by norm_num) ?_
    rw [burnsideC4h_card_quot_eq α hα hker,
      LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two F', hq4]
    norm_num
  · exact burnsideC4h_case3_bridge (hClause G H R M L V K hyp c3) c3
  ·
    exfalso
    obtain ⟨hpsl | hpsl, -, -⟩ := c4
    · obtain ⟨-, F', _, _, hF', ⟨e'⟩⟩ := hpsl
      have hF2 : Nat.card F' = 2 := by simpa using hF'
      refine hne 20160 (by norm_num) ?_
      rw [Nat.card_congr e'.toEquiv,
        Nat.card_congr (Setup.Family.statedProjSL_equiv_of_card_two 4 F' hF2).toEquiv,
        ← StatedAPI.card_statedSL, StatedAPI.card_statedSL_four_zmod_two]
    · obtain ⟨-, F', _, _, hF', ⟨e'⟩⟩ := hpsl
      have hF2 : Nat.card F' = 2 := by simpa using hF'
      refine hne 9999360 (by norm_num) ?_
      rw [Nat.card_congr e'.toEquiv,
        Nat.card_congr (Setup.Family.statedProjSL_equiv_of_card_two 5 F' hF2).toEquiv,
        ← StatedAPI.card_statedSL, StatedAPI.card_statedSL_five_zmod_two]

end C47

theorem burnsideC4h_exists_elemAbelian_alt6 :
    ∃ E : Subgroup (alternatingGroup (Fin 6)), IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 2 := by
  have hc1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have hc2 : (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]; decide
  have h1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
  have h2 : (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) ^ 3 = 1 := by decide
  have h1' : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ≠ 1 := by decide
  have h2' : (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) ≠ 1 := by decide
  have h12 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) * (Equiv.swap (3 : Fin 6) 4 *
      Equiv.swap 4 5) = (Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5) *
      (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) := by decide
  have hpow : ∀ k < 3, (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ k ≠
      Equiv.swap (3 : Fin 6) 4 * Equiv.swap 4 5 := by decide
  set a : alternatingGroup (Fin 6) := ⟨_, hc1⟩ with ha_def
  set b : alternatingGroup (Fin 6) := ⟨_, hc2⟩ with hb_def
  have ha : orderOf a = 3 :=
    orderOf_eq_prime (Subtype.ext h1) (fun h => h1' (congrArg Subtype.val h))
  have hb : orderOf b = 3 :=
    orderOf_eq_prime (Subtype.ext h2) (fun h => h2' (congrArg Subtype.val h))
  have hab : Commute a b := Subtype.ext h12
  have hbn : b ∉ Subgroup.zpowers a := by
    rw [mem_zpowers_iff_mem_range_orderOf, ha]
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro k hk hkb
    exact hpow k hk (congrArg Subtype.val hkb)
  exact CFSG.Quasithin.C41Pf.exists_elemAbelian_sq Nat.prime_three ha hb hab hbn

open CFSG.Quasithin.C41Pf in
theorem burnsideC4h_exists_elemAbelian_sp4_gen {F : Type} [Field F] [Fintype F] {r : ℕ}
    (hr : r.Prime) (hrF : r ∣ Fintype.card F - 1) :
    ∃ E : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F), IsElemAbelian r E ∧
      Nat.card ↥E = r ^ 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, orderOf u = r := by
    apply exists_prime_orderOf_dvd_card
    rw [Fintype.card_units]
    exact hrF
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact hr.one_lt.ne hu
  have hur : u ^ r = 1 := hu ▸ pow_orderOf_eq_one u
  let sd : (Fin 2 → Fˣ) → (Fin 2 ⊕ Fin 2 → Fˣ) := fun w => Sum.elim w (fun i => (w i)⁻¹)
  have hsd : ∀ w w' : Fin 2 → Fˣ, sd (w * w') = sd w * sd w' := by
    intro w w'
    funext i
    rcases i with i | i <;> simp [sd, mul_comm]
  have hmem : ∀ w : Fin 2 → Fˣ,
      (diagUnits (sd w) : GL (Fin 2 ⊕ Fin 2) F) ∈ CFSG.Assembly.LowTwoRank.StatedSp 2 F := by
    intro w
    apply Subgroup.subset_closure
    show Matrix.transpose (Matrix.diagonal fun i => ((sd w i : Fˣ) : F)) *
        Matrix.fromBlocks 0 1 (-1) 0 * Matrix.diagonal (fun i => ((sd w i : Fˣ) : F)) =
      Matrix.fromBlocks 0 1 (-1) 0
    rw [Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [sd, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.one_apply] <;> split_ifs <;> simp_all
  set w₁ : Fin 2 → Fˣ := ![u, 1] with hw₁
  set w₂ : Fin 2 → Fˣ := ![1, u] with hw₂
  set a : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := ⟨_, hmem w₁⟩ with ha_def
  set b : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := ⟨_, hmem w₂⟩ with hb_def
  have hpow : ∀ (w : Fin 2 → Fˣ) (k : ℕ), sd w ^ k = sd (w ^ k) := by
    intro w k
    induction k with
    | zero =>
      funext i
      rcases i with i | i <;> simp [sd]
    | succ k ih => rw [pow_succ, ih, pow_succ, hsd]
  have hzpow : ∀ (w : Fin 2 → Fˣ) (k : ℤ), sd w ^ k = sd (w ^ k) := by
    intro w k
    funext i
    rcases i with i | i <;> simp [sd]
  have hw₁r : w₁ ^ r = 1 := by funext i; fin_cases i <;> simp [hw₁, hur]
  have hw₂r : w₂ ^ r = 1 := by funext i; fin_cases i <;> simp [hw₂, hur]
  have hsd1 : ∀ w : Fin 2 → Fˣ, sd w = 1 → w = 1 := fun w h => by
    funext i
    have := congrFun h (Sum.inl i)
    simpa [sd] using this
  have hsd1' : sd 1 = 1 := by funext i; rcases i with i | i <;> simp [sd]
  have ha : orderOf a = r := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (diagUnits (sd w₁) : GL (Fin 2 ⊕ Fin 2) F) ^ r = 1
      rw [← map_pow, hpow, hw₁r, hsd1', map_one]
    · intro h
      have h1 : sd w₁ = 1 :=
        diagUnits_injective (F := F) (by rw [map_one]; exact congrArg Subtype.val h)
      have := congrFun (hsd1 _ h1) 0
      exact hu1 (by simpa [hw₁] using this)
  have hb : orderOf b = r := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      show (diagUnits (sd w₂) : GL (Fin 2 ⊕ Fin 2) F) ^ r = 1
      rw [← map_pow, hpow, hw₂r, hsd1', map_one]
    · intro h
      have h1 : sd w₂ = 1 :=
        diagUnits_injective (F := F) (by rw [map_one]; exact congrArg Subtype.val h)
      have := congrFun (hsd1 _ h1) 1
      exact hu1 (by simpa [hw₂] using this)
  have hab : Commute a b := by
    apply Subtype.ext
    show diagUnits (sd w₁) * diagUnits (sd w₂) =
      diagUnits (sd w₂) * (diagUnits (sd w₁) : GL (Fin 2 ⊕ Fin 2) F)
    rw [← map_mul, ← map_mul, mul_comm]
  have hbn : b ∉ Subgroup.zpowers a := by
    intro hmem'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem'
    have hk' : (diagUnits (sd w₁ ^ k) : GL (Fin 2 ⊕ Fin 2) F) = diagUnits (sd w₂) := by
      rw [map_zpow]
      exact congrArg Subtype.val hk
    have h1 := diagUnits_injective hk'
    rw [hzpow] at h1
    have h0 := congrFun h1 (Sum.inl 0)
    have h1' := congrFun h1 (Sum.inl 1)
    simp [sd, hw₁, hw₂] at h0 h1'
    exact hu1 h1'.symm
  exact exists_elemAbelian_sq hr ha hb hab hbn

theorem burnsideC4h_isElemAbelian_of_le {X : Type*} [Group X] {p : ℕ} {E F : Subgroup X}
    (hE : IsElemAbelian p E) (hFE : F ≤ E) : IsElemAbelian p F := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hE.2 x (hFE hx)⟩
  have h := hE.1.is_comm.comm ⟨a, hFE a.2⟩ ⟨b, hFE b.2⟩
  have h' : (a : X) * b = b * a := congrArg Subtype.val h
  exact Subtype.ext h'

theorem burnsideC4h_exists_elemAbelian_of_two_le_pRank {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) (h : 2 ≤ CFSG.pRank p S) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup S)
  have hdvd : p ^ 2 ∣ Nat.card ↥E := by
    rw [hEc]
    exact pow_dvd_pow p h
  obtain ⟨K, hK, -, hKE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hp (H := (⊥ : Subgroup S)) (L := E)
      (by simp) hdvd bot_le
  exact ⟨K, burnsideC4h_isElemAbelian_of_le hE hKE, hK⟩

theorem burnsideC4h_oddRankLeOne_of_no_sq {S : Type} [Group S] [Finite S]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2) → False) :
    CFSG.QuasithinUnique.Setup.Family.OddRankLeOne S := by
  intro r hr hr2
  by_contra hlt
  exact h r hr hr2 (burnsideC4h_exists_elemAbelian_of_two_le_pRank hr (by omega))

theorem burnsideC4h_le_pCore_two {K : Type*} [Group K] {N : Subgroup K} (hN : N.Normal)
    (hp : IsPGroup 2 N) : N ≤ CFSG.pCore 2 K :=
  le_sSup ⟨hN, hp⟩

theorem burnsideC4h_isPGroup_center_of_ker {K X : Type*} [Group K] [Group X]
    (φ : K →* X) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) : IsPGroup 2 (Subgroup.center X) := by
  intro z
  obtain ⟨k, hk⟩ := hφ (z : X)
  have hkc : (QuotientGroup.mk k : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hcomm : φ (x * k) = φ (k * x) := by
      rw [map_mul, map_mul, hk]
      exact ((Subgroup.mem_center_iff.mp z.2) (φ x))
    have hmem : (x * k)⁻¹ * (k * x) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm, inv_mul_cancel]
    exact burnsideC4h_le_pCore_two (MonoidHom.normal_ker φ) hker hmem
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hkc
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (G := K) (p := 2)) ⟨k, hkc⟩
  refine ⟨m, Subtype.ext ?_⟩
  have h1 : k ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h2 : (z : X) ^ 2 ^ m = 1 := by rw [← hk, ← map_pow, h1, map_one]
  simpa using h2

theorem burnsideC4h_exists_odd_prime_dvd {F : Type} [Fintype F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ Fintype.card F - 1 := by
  have hq : 3 ≤ Fintype.card F - 1 := by
    rw [hF]
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := Fintype.card F - 1) (by omega)
  refine ⟨r, hr, ?_, hrd⟩
  rintro rfl
  have hodd : Odd (Fintype.card F - 1) := by
    rw [hF]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    exact Nat.odd_iff.mpr (by
      have h2 : 2 ^ n % 2 = 0 := by
        rw [Nat.pow_mod]; simp [show n ≠ 0 by omega]
      omega)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)

section CaseII

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.SmithC27

variable {G : Type} [Group G] [Finite G]

theorem burnsideC4h_exists_elemAbelian_of_caseII {R K V : Subgroup G} {n : ℕ}
    (C : CaseIICtx R K V n) (hn : n = 6 ∨ n = 8) :
    ∃ E : Subgroup ↥(autOn K V), IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ 2 := by
  let incl : ↥(autOn K V) →* ↥(autOn (K ⊔ R) V) :=
    Subgroup.inclusion (CFSG.Quasithin.C41Pf.autOn_le_autOn le_sup_left)
  let ψ : ↥(autOn K V) →* ↥(alternatingGroup (Fin n)) :=
    (C.ι.toMonoidHom.comp incl).codRestrict (alternatingGroup (Fin n))
      (fun x => (C.mem_K (incl x)).1 x.2)
  have hψi : Function.Injective ψ := by
    intro a b h
    have h1 : C.ι (incl a) = C.ι (incl b) := congrArg Subtype.val h
    exact Subgroup.inclusion_injective _ (C.ι.injective h1)
  have hψs : Function.Surjective ψ := by
    rintro ⟨σ, hσ⟩
    refine ⟨⟨((C.ι.symm σ : ↥(autOn (K ⊔ R) V)) : MulAut ↥V),
      (C.mem_K _).2 (by simpa using hσ)⟩, ?_⟩
    apply Subtype.ext
    show C.ι (C.ι.symm σ) = σ
    exact C.ι.apply_symm_apply σ
  let e : ↥(autOn K V) ≃* ↥(alternatingGroup (Fin n)) := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩
  rcases hn with rfl | rfl
  · exact CFSG.Quasithin.C41Pf.exists_elemAbelian_of_mulEquiv e
      burnsideC4h_exists_elemAbelian_alt6
  · exact CFSG.Quasithin.C41Pf.exists_elemAbelian_of_mulEquiv e
      (CFSG.Quasithin.C41Pf.exists_elemAbelian_alt8)

end CaseII

section Residue

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.SmithC27

variable (G : Type) [Group G] [Finite G] in
@[expose] def burnsideC4h_KZeroResidue : Prop :=
  ∀ (H R M K : Subgroup G), Hyp27 H R M K →
    (Group.IsSolvable ↥(autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) → False) →
    (∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ E : Subgroup ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))),
        IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2) → False) →
    IsPGroup 2 ↥(Subgroup.center ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) →
    ¬ (IsChiBlock2 H K ∨ IsExcA7Block K ∨ IsSylowTwoOf R (K ⊔ R)) → False

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin.C41Pf in
theorem burnsideC4h_kzeroResidue_core
    (hRC : ∀ {H R M K : Subgroup G}, Hyp27 H R M K → ¬ IsChiBlock2 H K → ¬ IsExcA7Block K →
      (autOn (thompsonJ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ≤
          autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ∧
        ResidueTypeI K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ∨
      ResidueTypeII R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hRank2 : ∀ {H R M K : Subgroup G}, Hyp27 H R M K →
      autOn (thompsonJ R) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ≤
        autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
      ¬ IsSylowTwoOf R (K ⊔ R) → ResidueRankTwo K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) →
      IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
        (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))))
    (hG2rk : ∀ {F : Type} [Field F] [Fintype F] {n : ℕ} {S : Type} [Group S] [Finite S],
      2 ≤ n → Fintype.card F = 2 ^ n → Nonempty (S ≃* ↥(quasithinG2 F)) →
      ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S)
    (hII : ∀ {R K V : Subgroup G}, StarHyp R K V → ResidueTypeII R K V →
      (∃ n : ℕ, (n = 6 ∨ n = 8) ∧ Nonempty (CaseIICtx R K V n)) ∨ IsPSU 3 3 1 ↥(autOn K V)) :
    burnsideC4h_KZeroResidue G := by
  intro H R M K h27 hsolv hlift hcent hc
  have hnchi : ¬ IsChiBlock2 H K := fun h => hc (Or.inl h)
  have hnexc : ¬ IsExcA7Block K := fun h => hc (Or.inr (Or.inl h))
  have hnS : ¬ IsSylowTwoOf R (K ⊔ R) := fun h => hc (Or.inr (Or.inr h))
  have hs : StarHyp R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) := h27.starHyp
  rcases hRC h27 hnchi hnexc with ⟨hJ, hI⟩ | hTII
  · rcases hI with hr1 | hr2 | hr3
    · exact false_of_residueRankOne h27 hs hJ hnS hr1
    · have ht := hr2
      rcases hr2 with ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ | ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ |
          ⟨n, F, _, _, hn, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨hhat, -⟩
      ·
        by_cases hn1 : n = 1
        · subst hn1
          exact hsolv (isSolvable_of_c27SL3_two (by rw [hF]; norm_num) e
            (hRank2 h27 hJ hnS ht))
        · obtain ⟨r, hr, hr2', hrd⟩ := burnsideC4h_exists_odd_prime_dvd (by omega) hF
          exact hlift r hr hr2' (exists_elemAbelian_of_mulEquiv e (exists_elemAbelian_sl3 hr hrd))
      ·
        obtain ⟨r, hr, hr2', hrd⟩ := burnsideC4h_exists_odd_prime_dvd hn hF
        exact hlift r hr hr2' (exists_elemAbelian_of_mulEquiv e
          (burnsideC4h_exists_elemAbelian_sp4_gen hr hrd))
      ·
        obtain ⟨r, hr, hr2', hrk⟩ := hG2rk hn hF ⟨e⟩
        exact hlift r hr hr2' (burnsideC4h_exists_elemAbelian_of_two_le_pRank hr hrk)
      ·
        exact hlift 3 Nat.prime_three (by norm_num)
          (exists_elemAbelian_of_mulEquiv e burnsideC4h_exists_elemAbelian_alt6)
      ·
        obtain ⟨k, hk⟩ := hcent.exists_card_eq
        have h3 : (3 : ℕ) = 2 ^ k := hhat.2.1.symm.trans hk
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp at h3
        · have : 2 ∣ 3 := h3 ▸ dvd_pow_self 2 hkpos.ne'
          omega
    ·
      obtain ⟨d, hd, ⟨e⟩, -⟩ := hr3
      rcases hd with rfl | rfl
      · exact hlift 3 Nat.prime_three (by norm_num)
          (exists_elemAbelian_of_mulEquiv e exists_elemAbelian_sl4_two)
      · exact hlift 3 Nat.prime_three (by norm_num)
          (exists_elemAbelian_of_mulEquiv e exists_elemAbelian_sl5_two)
  · rcases hII hs hTII with ⟨n, hn, ⟨C⟩⟩ | hpsu
    · obtain ⟨E, hE, hEc⟩ := burnsideC4h_exists_elemAbelian_of_caseII C hn
      exact hlift 3 Nat.prime_three (by norm_num) ⟨E, hE, hEc⟩
    · have hodd := burnsideC4h_oddRankLeOne_of_no_sq hlift
      have := CFSG.QuasithinUnique.Setup.Family.oddRankOneOddClassical _ hodd 3 Nat.prime_three
        (by norm_num) .PSU 3 1 hpsu
      exact absurd this.1 (by decide)

end Residue

section KZ

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin.C41Pf in
theorem burnsideC4h_kzero_of_residue
    (hC27χ : ∀ {H R M K : Subgroup G}, SmithC27.Hyp27 H R M K →
      (IsChiBlock2 H K ∨ IsExcA7Block K ∨ IsSylowTwoOf R (K ⊔ R)) →
      C27Concl H R M K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
    (hres : burnsideC4h_KZeroResidue G)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hG2 : CFSG.Quasithin.H13.Lem1211NNG2) : C41KZero G := by
  intro H R M L V K h hK hKc hKq hKM hRN ⟨P, hP1, hPp, hPMK, hPR⟩
  by_contra hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hW
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hPK : P ≤ K := hPMK.trans inf_le_right
  have hPM : P ≤ M := hPMK.trans inf_le_left
  have h23 := c2_10_four h
  have h27 : SmithC27.Hyp27 H R M K := SmithC27.Hyp27.mk' h23 hK hKq hKc hKM hRN
  have h1 : SmithC27.C27One R K W := SmithC27.c27_one h27
  have hsolv : Group.IsSolvable ↥(autOn (M ⊓ K) W) → False := fun hs =>
    false_of_isSolvable_autOn h1 hPK hPM hPp hP1 hs
  obtain ⟨t, htH, hcomm, hint⟩ :=
    exists_conj_of_not_le_normalizer (a3Orbits_of_a37_a38 hA37 hA38) h.sqtk hK hn
  have hK'H : conjByElt t K ≤ H := by
    intro x hx
    rw [mem_conjByElt] at hx
    have := H.mul_mem (H.mul_mem htH (hKH hx)) (H.inv_mem htH)
    simpa [mul_assoc] using this
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup G, E ≤ K → IsElemAbelian p E →
      Nat.card ↥E = p ^ 2 → False := by
    intro p hp hp2 E hEK hE hEc
    have : Fact p.Prime := ⟨hp⟩
    have hE1 : E ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hEc
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    obtain ⟨e, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hE1)
    have heo : orderOf (e : G) = p := orderOf_eq_prime (hE.2 _ e.2)
      (fun h => he1 (Subtype.ext h))
    have hyK' : t * (e : G) * t⁻¹ ∈ conjByElt t K := by
      rw [mem_conjByElt]
      simpa [mul_assoc] using hEK e.2
    have hyo : orderOf (t * (e : G) * t⁻¹) = p := by
      have h0 := orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective (e : G)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h0
      rw [h0, heo]
    exact false_of_elemAbelian_pair h.sqtk hKH hK'H hcomm hint hp hp2 hEK hE hEc hyK' hyo
  have hsimple := isSimpleGroup_of_not_le_normalizer hA38 h.sqtk hK hn
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))
      with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hKq.2.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, h0]
      exact Subgroup.mem_top _
  have hKN : K ≤ Subgroup.normalizer (W : Set G) := le_normalizer_omegaOneCenter K R
  let φ : ↥K →* ↥(autOn K W) :=
    ((conjAct W).comp (Subgroup.inclusion hKN)).codRestrict (autOn K W) fun k =>
      ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : IsPGroup 2 ↥φ.ker := by
    intro x
    have hxC : ((x : ↥K) : G) ∈ Subgroup.centralizer (W : Set G) := by
      have h0 : conjAct W (Subgroup.inclusion hKN (x : ↥K)) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      exact (conjAct_eq_one_iff' _).mp h0
    have hxZ : ((x : ↥K) : G) ∈ oTwoZIn K := inf_centralizer_le_oTwoZIn h1 ⟨(x : ↥K).2, hxC⟩
    obtain ⟨w, hw, hwx⟩ := hxZ
    have hw1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) w = 1 := by
      have : QuotientGroup.mk' (CFSG.pCore 2 ↥K) w ∈ Subgroup.center _ := hw
      rw [hZ] at this
      exact Subgroup.mem_bot.mp this
    have hwO : w ∈ CFSG.pCore 2 ↥K := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw1
    have hwx' : w = (x : ↥K) := Subtype.ext hwx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥K) (p := 2)) ⟨w, hwO⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
    rw [hwx'] at this
    simpa using this
  have hliftstar : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ E : Subgroup ↥(autOn K W), IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2) → False := by
    rintro p hp hp2 ⟨E, hE, hEc⟩
    obtain ⟨F, hFK, hF, hFc⟩ := exists_elemAbelian_lift φ hφ hker hp hp2 hE hEc
    exact hrank p hp hp2 F hFK hF hFc
  have hcenter : IsPGroup 2 ↥(Subgroup.center ↥(autOn K W)) :=
    burnsideC4h_isPGroup_center_of_ker φ hφ hker hZ
  have hsub : autOn (M ⊓ K) W ≤ autOn (K ⊔ R) W := autOn_le_autOn (inf_le_right.trans le_sup_left)
  by_cases hc : IsChiBlock2 H K ∨ IsExcA7Block K ∨ IsSylowTwoOf R (K ⊔ R)
  swap
  · exact hres H R M K h27 hsolv hliftstar hcenter hc
  have hcases : SBc17.C27Cases H R M K W := by
    obtain ⟨-, -, h3⟩ := (SmithC27.c27Concl_iff).mp (hC27χ h27 hc)
    rcases h3 with ⟨hb, h1 | h2 | h3 | h4⟩ | hb | hc | hd | he | hf | hg | hh
    · exact Or.inl ⟨hb, h1⟩
    · exact Or.inr (Or.inl ⟨hb, h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hb, h3⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, h4⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hf))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hg)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr hh)))))))))
  rcases hcases with ⟨-, -, -, hB⟩ | ⟨-, -, -, -, hB⟩ | ⟨-, -, -, e, Pt, hPt, he⟩ |
      ⟨-, -, -, e, Pt, hPt, he⟩ | ⟨⟨n, α, hn5, hn8, -, hαw, t', ht'R, ht'V, -, -, σ, hσ, hconj⟩,
        hMK⟩ | ⟨hHat, hidx, -⟩ | ⟨hExc, hidx⟩ | ⟨hA6 | hSp, hmax⟩ | ⟨-, hG2two, hmax⟩ |
      ⟨⟨n, F, _, _, hn1, hFc, ⟨e⟩⟩, hmax, -⟩ | ⟨he4 | he5, -, -⟩
  · exact hsolv (isSolvable_of_isBorelIn hB)
  · exact hsolv (isSolvable_of_isBorelIn hB)
  · exact hsolv (isSolvable_of_map_eq hsub e he (isSolvable_stabilizer_of_type_43 hPt))
  · exact hsolv (isSolvable_of_map_eq hsub e he (isSolvable_stabilizer_of_type_2221 hPt))
  ·
    obtain ⟨hα, hkerα, -⟩ := hαw
    by_cases hn6 : n ≤ 6
    · exact hP1 (eq_bot_of_alt_transposition hRN h1 hn5 hn6 α hα hkerα ht'R ht'V hσ hconj hMK
        hPK hPM hPp)
    · have hker2 : IsPGroup 2 ↥α.ker := hkerα ▸ CFSG.pCore_isPGroup
      have hn78 : n = 7 ∨ n = 8 := by omega
      rcases hn78 with rfl | rfl
      · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_alt7
        obtain ⟨F', hFK, hF, hFc⟩ := exists_elemAbelian_lift α hα hker2 Nat.prime_three
          (by norm_num) hE hEc
        exact hrank 3 Nat.prime_three (by norm_num) F' hFK hF hFc
      · obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_alt8
        obtain ⟨F', hFK, hF, hFc⟩ := exists_elemAbelian_lift α hα hker2 Nat.prime_three
          (by norm_num) hE hEc
        exact hrank 3 Nat.prime_three (by norm_num) F' hFK hF hFc
  · exact hsolv (isSolvable_autOn (isSolvable_inf_of_relIndex (by norm_num) hidx
      (card_of_isHatA6Block hHat)))
  · exact hsolv (isSolvable_autOn (isSolvable_inf_of_relIndex (by norm_num) hidx
      (card_of_isExcA7Block hExc)))
  · exact hsolv (isSolvable_of_c27A6 hRN h1 hA6 hmax)
  ·
    obtain ⟨-, F, _, _, hF4, α, hα, hkerα, -⟩ := hSp
    have hker2 : IsPGroup 2 ↥α.ker := hkerα ▸ CFSG.pCore_isPGroup
    obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_sp4 hF4
    obtain ⟨F', hFK, hF, hFc⟩ := exists_elemAbelian_lift α hα hker2 Nat.prime_three
      (by norm_num) hE hEc
    exact hrank 3 Nat.prime_three (by norm_num) F' hFK hF hFc
  · have := isSolvable_of_isMaxParabolic2_g2 hG2 hG2two hmax
    have hle : autOn (M ⊓ K) W ≤ autOn (M ⊓ K) W ⊔ autOn R W := le_sup_left
    exact hsolv (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))
  ·
    by_cases hn1' : n = 1
    · subst hn1'
      exact hsolv (isSolvable_of_c27SL3_two (by rw [hFc]; norm_num) e hmax)
    · have hq : 3 ≤ Fintype.card F - 1 := by
        rw [hFc]
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := Fintype.card F - 1) (by omega)
      have hr2 : r ≠ 2 := by
        rintro rfl
        have hodd : Odd (Fintype.card F - 1) := by
          rw [hFc]
          have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          exact Nat.odd_iff.mpr (by
            have h2 : 2 ^ n % 2 = 0 := by
              rw [Nat.pow_mod]; simp [show n ≠ 0 by omega]
            omega)
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)
      exact hliftstar r hr hr2 (exists_elemAbelian_of_mulEquiv e (exists_elemAbelian_sl3 hr hrd))
  · obtain ⟨e⟩ := he4
    exact hliftstar 3 Nat.prime_three (by norm_num)
      (exists_elemAbelian_of_mulEquiv e exists_elemAbelian_sl4_two)
  · obtain ⟨e⟩ := he5
    exact hliftstar 3 Nat.prime_three (by norm_num)
      (exists_elemAbelian_of_mulEquiv e exists_elemAbelian_sl5_two)

end KZ

section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank in
theorem burnsideC4h_kzero_holds
    (G : Type) [Group G] [Finite G] : C41KZero G := by
  refine burnsideC4h_kzero_of_residue ?_ ?_ H13.a3ForSQTK_holds.1 H13.a3ForSQTK_holds.2.1
    H13.KGG2.lem1211NNG2_holds
  · intro H R M K h hc
    exact SmithC27.c27Concl_of_cases (H13.VolI.asc129Statement_holds G)
      (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
      asA21SQTKSection asA36NoOddCover_holds B5.asB51_holds h hc
  · refine burnsideC4h_kzeroResidue_core ?_ ?_ ?_ ?_
    · intro H R M K h hnchi hnexc
      exact SmithC27.residue_cases asA21SQTKSection B5.asB51_holds
        (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)
        (C124.c124StatementSQTK_of_e22 e22StatementNoN_proved G) h h.starHyp hnchi hnexc
    · intro H R M K h hJ hnS ht
      exact (SmithC27.maxParabolic_msPair h h.starHyp ht.isRadicalParabolic
        ht.maxParabolicMaximal hJ hnS (SmithC27.ResidueRankTwo.isRankTwoLie2Derived h.starHyp ht)).1
    · intro F _ _ n S _ _ hn hF he
      obtain ⟨e⟩ := he
      have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
      have : CharP F 2 := B42G2Id.charP_two_of_card hF'
      obtain ⟨e'⟩ := B42G2Id.nonempty_quasithinG2_mulEquiv_adjointQuotient hF' hn
      exact CFSG.RankThree.Chevalley.exists_two_le_pRank_of_G2_even hn
        ⟨F, inferInstance, inferInstance, hF', ⟨e.trans e'⟩⟩
    · intro R K V hs hII
      obtain ⟨hV, -, hKT, ⟨n, hn, π, hπ, hπK⟩ | hG⟩ := hII
      · exact Or.inl ⟨n, hn, SmithC27.nonempty_caseIICtx hs hV hn
          (SmithC27.autI_le_jPStar hV hKT) π hπ hπK⟩
      · exact Or.inr (SmithC27.g2StarData_of hs hV hKT hG).2.psu

end

section

theorem as_C_4_5
    : C_4_5 := by
  exact burnsideC4h_c45_of_kzero fun G _ _ => burnsideC4h_kzero_holds G

end

section

theorem as_C_4_2
    : C_4_2 := by
  exact burnsideC4h_c42_of_kzero fun G _ _ => burnsideC4h_kzero_holds G

end

end CFSG.ASVolI
