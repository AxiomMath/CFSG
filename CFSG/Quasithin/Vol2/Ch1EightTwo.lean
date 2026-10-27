module

public import CFSG.Quasithin.Vol2.Ch1EightTwoOrd
public import CFSG.Quasithin.Vol2.Ch1EightFourMain
public import CFSG.Quasithin.H13.VolIRankTwoA38
public import CFSG.Quasithin.H13.VolIA38SLThree

public section

namespace CFSG.Quasithin.Ch1Two

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.VolI
open CFSG.Quasithin.Ch1Four CFSG.Assembly.LowTwoRank

section Types

variable {X : Type} [Group X]

theorem sixty_le_card_of_a38Types
    (hA : A38Types X) : 60 ≤ Nat.card X :=
  sixty_le_of_a38Order (a38Order_card hA)

theorem false_of_isHat
    {S : Type} [Group S] (hA : A38Types X) (h : IsHat X S) : False := by
  have hS := isSimpleGroup_of_a38Types hA
  have h60 := sixty_le_card_of_a38Types hA
  have h3 := h.2.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht
  · rw [hb, Subgroup.card_bot] at h3
    omega
  · rw [ht, Subgroup.card_top] at h3
    omega

theorem oddCore_eq_bot_of_a38Types
    [Finite X] (hA : A38Types X) : CFSG.oddCore X = ⊥ := by
  have hS := isSimpleGroup_of_a38Types hA
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore X) with hb | ht
  · exact hb
  · exfalso
    have hodd := A312.odd_card_oddCore X
    rw [ht, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_of_a38Order (a38Order_card hA))

theorem false_of_rankTwoOrder
    (hA : A38Types X) (h : RankTwoOrder (Nat.card X)) : False :=
  a38Order_not_rankTwoOrder (a38Order_card hA) h

theorem card_eq_168_of_rank2
    (hA : A38Types X) (hR : IsRank2LieChar2 X) :
    Nat.card X = 168 := by
  have hD : IsRankTwoLie2Derived X → Nat.card X = 168 := fun hD => by
    rcases rankTwo_cases hD with ⟨-, h⟩ | hb
    · exact h
    · exact (false_of_rankTwoOrder hA hb).elim
  rcases hR with ⟨f, ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩⟩ | h
  · exact hD (Or.inl ⟨f, h⟩)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
    have hf := a38TypesSLThree_holds X K f hK ⟨e⟩ hA
    subst hf
    rw [pow_one] at hK
    exact hD (Or.inl ⟨1, isPSL_three_two_of_isSL3 ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩⟩)
  · exact hD (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h⟩))))
  · exact hD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h⟩))))))
  · exact hD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h⟩))))))))
  · exact hD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨f, h⟩)))))))))
  · exact hD (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))

theorem card_of_isSporadic {s : TauCeti.SporadicName} {m : ℕ} (h : IsSporadic s X)
    (hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) = m) : Nat.card X = m := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.toEquiv).trans hc

theorem oddL3Shape_of_psl3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSL 3 p 1 X) :
    OddL3Shape (Nat.card X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hc := card_psl3_mul (K := K)
  rw [hK, pow_one, ← Nat.card_congr e.toEquiv] at hc
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact ⟨p, _, _, hp, h3, hc, Or.inl ⟨rfl, gcd_three_eq _⟩⟩

theorem oddL3Shape_of_psu3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSU 3 p 1 X) :
    OddL3Shape (Nat.card X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hc := card_psu3_mul hp le_rfl hK
  rw [← Nat.card_congr e.toEquiv, pow_one] at hc
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact ⟨p, _, _, hp, h3, hc, Or.inr ⟨rfl, gcd_three_eq _⟩⟩

theorem oddL3Shape_of_sl3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSL3 p X) :
    OddL3Shape (Nat.card X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hc : Nat.card X * 1 = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 - 1)) := by
    rw [mul_one, Nat.card_congr e.toEquiv, card_sl3, hK]
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact ⟨p, 1, _, hp, h3, hc, Or.inl ⟨rfl, Or.inl rfl⟩⟩

theorem oddL3Shape_of_su3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSU3 p X) :
    OddL3Shape (Nat.card X) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK1 : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have hc := card_su3 hp hK1
  rw [pow_one] at hc
  have hc' : Nat.card X * 1 = p ^ 3 * ((p ^ 2 - 1) * (p ^ 3 + 1)) := by
    rw [mul_one, Nat.card_congr e.toEquiv, hc]
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  exact ⟨p, 1, _, hp, h3, hc', Or.inr ⟨rfl, Or.inl rfl⟩⟩

theorem oddL3Shape_of_eps {s : Bool} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsPSLEps3 s p 1 X ∨ IsSLEps3 s p X) : OddL3Shape (Nat.card X) := by
  cases s
  · rcases h with h | h
    · exact oddL3Shape_of_psu3 hp hp2 h
    · exact oddL3Shape_of_su3 hp hp2 h
  · rcases h with h | h
    · exact oddL3Shape_of_psl3 hp hp2 h
    · exact oddL3Shape_of_sl3 hp hp2 h

theorem two_mul_card_of_l2sq {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) (h : IsPSL 2 r 2 X) :
    2 * Nat.card X = r ^ 2 * (r ^ 4 - 1) := by
  have hodd := hr.odd_of_ne_two (by omega)
  have hev : 2 ∣ r ^ 2 - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)
  rw [card_of_isPSL' (by norm_num) h, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one,
    Finset.Icc_self, Finset.prod_singleton, ← pow_mul, Nat.gcd_eq_left hev]
  have h4 : 2 ∣ r ^ 4 - 1 := by
    rw [show r ^ 4 - 1 = (r ^ 2 - 1) * (r ^ 2 + 1) from four_sub_one_eq' r hr.one_lt.le]
    exact hev.mul_right _
  exact Nat.mul_div_cancel' (h4.mul_left _)

end Types

section Cases

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

theorem false_of_rank2
    (hBL : B ≤ L) (hA : A38Types ↥L) {n : ℕ}
    (hn : IsPSL 2 2 n (ModO2 B)) (hR : IsRank2LieChar2 ↥L) : False := by
  have hcard := card_eq_168_of_rank2 hA hR
  obtain ⟨h2, hc⟩ := card_of_isPSL_two_two hn
  obtain ⟨j, hj⟩ := card_modO2_mul (H := ↥B)
  have hdvd : Nat.card ↥B ∣ 168 := hcard ▸ Subgroup.card_dvd_of_le hBL
  rw [← hj, hc] at hdvd
  have h4 : 4 ^ n - 1 ∣ 168 := (Dvd.intro (2 ^ n * 2 ^ j) (by ring)).trans hdvd
  have hle : 4 ^ n - 1 ≤ 168 := Nat.le_of_dvd (by norm_num) h4
  have hn3 : n ≤ 3 := by
    by_contra hgt
    have : 4 ^ 4 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n <;> norm_num at h4

theorem case_of_a312Case
    (hBL : B ≤ L) (hA : A38Types ↥L) (h : A312Case B L) :
    IsAlt 5 ↥B ∧ (IsSporadic .J1 ↥L ∨ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
      (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 ↥L) := by
  have hO := a38Order_card hA
  have hfix : ∀ {m : ℕ}, Nat.card ↥L = m → FixShape m → m ≠ 175560 → False :=
    fun hm hF hJ => not_a38Order_of_fixShape hF hJ (hm ▸ hO)
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨n, hn⟩, hR, -⟩ := h
    exact (false_of_rank2 hBL hA hn hR).elim
  ·
    obtain ⟨f, -, hF, -⟩ := h
    obtain ⟨k, hk, hc⟩ := H13.card_eq_ordTwistedF4_of_reeTitsModel hF
    have hR : RankTwoOrder (Nat.card ↥L) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨k, hk, hc⟩))))))))
    exact (false_of_rankTwoOrder hA hR).elim
  ·
    obtain ⟨-, hL | hL, -⟩ := h
    · exact (not_a38Order_20160 (card_of_isPSL_four_two hL ▸ hO)).elim
    · exact (not_a38Order_9999360
        ((show Nat.card ↥L = 9999360 by rw [card_of_isPSL' (by norm_num) hL]; decide) ▸ hO)).elim
  ·
    obtain ⟨-, hL, -⟩ := h
    exact (not_a38Order_9999360
      ((show Nat.card ↥L = 9999360 by rw [card_of_isPSL' (by norm_num) hL]; decide) ▸ hO)).elim
  ·
    obtain ⟨-, hL | hL⟩ := h
    · exact (not_a38Order_2520 (card_alt7 hL ▸ hO)).elim
    · exact (false_of_isHat hA hL).elim
  ·
    rcases h with ⟨-, hL⟩ | ⟨-, hL⟩
    · exact (not_a38Order_2520 (card_alt7 hL ▸ hO)).elim
    · exact (false_of_isHat hA hL).elim
  ·
    rcases h with ⟨p, hp, hp3, -, hL⟩ | ⟨hB, p, hp, hL, h5, h8⟩
    · exact (not_a38Order_of_r2 hp (five_le_of_three_lt hp hp3)
        (two_mul_card_of_l2sq hp hp3 hL) hO).elim
    · exact ⟨hB, Or.inr ⟨p, hp, h5, h8, hL⟩⟩
  ·
    rcases h with ⟨s, p, hp, hp3, -, hL⟩ | ⟨-, hL⟩ | ⟨-, hL⟩
    · exact (not_a38Order_of_oddL3Shape (oddL3Shape_of_eps hp (by omega) hL) hO).elim
    · exact (not_a38Order_of_oddL3Shape (oddL3Shape_of_psu3 (by norm_num) (by norm_num) hL)
        hO).elim
    · exact (not_a38Order_of_oddL3Shape (oddL3Shape_of_su3 (by norm_num) (by norm_num) hL)
        hO).elim
  ·
    obtain ⟨p, hp, hp3, -, hL | hL⟩ := h
    · exact (not_a38Order_of_oddL3Shape (oddL3Shape_of_psl3 hp (by omega) hL) hO).elim
    · exact (not_a38Order_of_oddL3Shape (oddL3Shape_of_sl3 hp (by omega) hL) hO).elim
  ·
    exact (hfix (card_of_isSporadic h.2 CFSG.Sporadic.Mathieu.card_M11) fixShape_m11
      (by norm_num)).elim
  ·
    rcases h with ⟨-, hL⟩ | ⟨-, hL⟩
    · exact (not_a38Order_443520 (card_of_isSporadic_M22' hL ▸ hO)).elim
    · exact (false_of_isHat hA hL).elim
  ·
    exact (hfix (card_of_isSporadic h.2 CFSG.Sporadic.Schreier.m23_card) fixShape_m23
      (by norm_num)).elim
  ·
    exact (not_a38Order_244823040 (card_of_isSporadic_M24' h.2 ▸ hO)).elim
  ·
    exact ⟨h.1, Or.inl h.2⟩
  ·
    exact (hfix (card_of_isSporadic h.2 CFSG.Sporadic.J2.card_J2) fixShape_j2 (by norm_num)).elim
  ·
    exact (hfix (card_of_isSporadic h.1 CFSG.Sporadic.J4.card_J4) fixShape_j4 (by norm_num)).elim
  ·
    exact (hfix (card_of_isSporadic h.2 CFSG.Sporadic.HS.card_HS) fixShape_hs (by norm_num)).elim
  ·
    exact (hfix (card_of_isSporadic h.2 CFSG.Sporadic.He.card_He) fixShape_he (by norm_num)).elim
  ·
    exact (hfix (card_of_isSporadic h.2.2 CFSG.Sporadic.Ru.card_Ru) fixShape_ru
      (by norm_num)).elim

theorem false_of_a312Nonquasi
    (hA : A38Types ↥L) (h : A312Nonquasi B L) : False := by
  have hO := oddCore_eq_bot_of_a38Types hA
  have hOL : (CFSG.oddCore ↥L).map L.subtype = ⊥ := by rw [hO, Subgroup.map_bot]
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨hne, -⟩ | ⟨hne, -⟩ <;> exact hne (by rw [hOL, Subgroup.commutator_bot_left])

theorem isAlt5_modO2 {B : Subgroup Q} (h : IsAlt 5 ↥B) : IsAlt 5 (ModO2 B) := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup ↥B := e.isSimpleGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card ↥B = 60 := card_alt5 ⟨e⟩
  have hbot : CFSG.pCore 2 ↥B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥B) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
      rw [ht, Subgroup.card_top, hc] at hk
      have hk6 : k < 6 := by
        by_contra hge
        have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> omega
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans (QuotientGroup.quotientBot.trans e)⟩

end Cases

theorem lemma128TwoAS_form_of_inputs
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h312 : A312ForSQTK) (h128 : Lemma128One) :
    ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → ∀ S L K : Subgroup G, quasithinIsLocal S L →
        quasithinIsLocal S K → L ≤ K → L < conjClosure L S →
          L = K ∨ (IsAlt 5 (ModO2 L) ∧ (IsSporadic .J1 (ModO2 K) ∨
            ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
              IsPSL 2 p 1 (ModO2 K))) := by
  intro G _ _ hQ hs hnab S L K hL hK hLK hlt
  by_cases hLK' : L = K
  · exact Or.inl hLK'
  right
  have hS : IsSylowTwoOf S (K ⊔ S) := ⟨le_sup_right, hK.1, hK.2.2.1⟩
  have hKc : K ∈ cComp (K ⊔ S) := cComp_of_isLocal hK
  obtain ⟨s, hsS, hsL⟩ : ∃ s ∈ S, s ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hcon
    refine hlt.ne (le_antisymm (le_conjClosure L S) (conjClosure_le fun h hh z hz => ?_))
    have hN : h ∈ Subgroup.normalizer (L : Set G) := by
      by_contra hn
      exact hcon ⟨h, hh, hn⟩
    exact (Subgroup.mem_normalizer_iff.mp hN z).mp hz
  have hsK : s ∉ Subgroup.normalizer (K : Set G) := fun h =>
    hsL (h128 G hQ hs hnab S L K hL hK hLK ⟨hsS, h⟩)
  have hKA : A38Types (ModO2 K) := by
    rcases lemma_1_2_1_three hQ hs hnab h37 h38 hK.2.2.2 hKc with hn | ⟨-, hA⟩
    · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn
        (Subgroup.mem_sup_right hsS)) hsK
    · exact hA
  obtain ⟨eK⟩ := modO2_mulEquiv hKc
  have hKbA : A38Types ↥(modO2Image (K ⊔ S) K) := A38Types.of_mulEquiv eK hKA
  have hBH : L ≤ K ⊔ S := hLK.trans le_sup_left
  have hBL : modO2Image (K ⊔ S) L ≤ modO2Image (K ⊔ S) K :=
    Subgroup.map_mono (fun x hx => hLK hx)
  rcases lemma_1_2_4_list hQ hs hnab h312 hK.2.2.2 hS hBH (mem_lFamily_of_isLocal hL) hKc hLK with
    heq | hcase | hnq
  · exact absurd (eq_of_modO2Image_eq hL hK hLK heq) hLK'
  · obtain ⟨hA5, hJ⟩ := case_of_a312Case hBL hKbA hcase
    obtain ⟨eL⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hBH
    refine ⟨IsAlt.of_mulEquiv eL.symm (isAlt5_modO2 hA5), ?_⟩
    rcases hJ with hJ | ⟨p, hp, h5, h8, hp1⟩
    · exact Or.inl (IsSporadic.of_mulEquiv eK.symm hJ)
    · exact Or.inr ⟨p, hp, h5, h8, isPSL_of_mulEquiv hp1 eK.symm⟩
  · exact (false_of_a312Nonquasi hKbA hnq).elim

end CFSG.Quasithin.Ch1Two
