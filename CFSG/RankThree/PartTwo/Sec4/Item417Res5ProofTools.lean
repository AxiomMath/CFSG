module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofTools
import CFSG.RankThree.PartTwo.Sec4.Item413Back
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Five

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem card_le_27_of_le_normalizer (hG : SectionFourHyp G) {X S : Subgroup G}
    (hX : CFSG.Assembly.IsElemAbelian 3 X) (hS2 : IsPGroup 2 S) (hS : S ≠ ⊥)
    (hXS : X ≤ Subgroup.normalizer (S : Set G)) : Nat.card X ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hX)
  have h1 := CFSG.RankThree.PartOne.Sec9Excl.le_localRank_of_normalizes (by norm_num : 1 < 3) hS
    hS2 hX.1 hX.2 hk hXS
  have h2 := (CFSG.RankThree.OddKernel.localRank_le_evenRank Nat.prime_three
    (by norm_num)).trans hG.evenRank_le
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (h1.trans h2)
    _ = 27 := by norm_num

theorem mem_of_commute_of_isE27 (hG : SectionFourHyp G) {D S : Subgroup G} (hD : Late.IsE27 D)
    (hS2 : IsPGroup 2 S) (hS : S ≠ ⊥) (hDS : D ≤ Subgroup.normalizer (S : Set G)) {w : G}
    (hw3 : w ^ 3 = 1) (hwD : ∀ d ∈ D, d * w = w * d)
    (hwS : w ∈ Subgroup.normalizer (S : Set G)) : w ∈ D := by
  obtain ⟨B, hDB, hwB, hB⟩ := exists_isElemAbelian_le_mem hD.1 hw3 hwD
  have hle : D ⊔ Subgroup.zpowers w ≤ B := sup_le hDB (Subgroup.zpowers_le.mpr hwB)
  have hX := isElemAbelian_of_le hB hle
  have hN : D ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer (S : Set G) :=
    sup_le hDS (Subgroup.zpowers_le.mpr hwS)
  have h27 := card_le_27_of_le_normalizer hG hX hS2 hS hN
  have heq : D = D ⊔ Subgroup.zpowers w :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hD.2]; exact h27)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)

omit [Finite G] in
theorem isElemAbelian_sup_zpowers_cube {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) {x : G} (hx : x ^ 3 = 1)
    (hxE : ∀ a ∈ E, a * x = x * a) :
    CFSG.Assembly.IsElemAbelian 3 (E ⊔ Subgroup.zpowers x) := by
  obtain ⟨B, hEB, hxB, hB⟩ := exists_isElemAbelian_le_mem hE hx hxE
  exact isElemAbelian_of_le hB (sup_le hEB (Subgroup.zpowers_le.mpr hxB))

theorem card_sup_zpowers_eq_three_mul {E₀ : Subgroup G} {c : G} (hc3 : orderOf c = 3)
    (hcE : c ∉ E₀)
    (hcomm : ∀ a ∈ E₀, ∀ b ∈ Subgroup.zpowers c, a * b = b * a) :
    Nat.card (E₀ ⊔ Subgroup.zpowers c : Subgroup G) = 3 * Nat.card E₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hinf : E₀ ⊓ Subgroup.zpowers c = ⊥ := by
    have hz : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
    have hdvd : Nat.card (E₀ ⊓ Subgroup.zpowers c : Subgroup G) ∣ 3 :=
      hz ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : E₀ ⊓ Subgroup.zpowers c = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hz, h3])
      have hc : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
      rw [← heq] at hc
      exact hcE hc.1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3] at hcard
  rw [hcard, mul_comm]

theorem exists_isQuad417 (hG : SectionFourHyp G) {L : Subgroup G} {c : G}
    (hcC : c ∈ Subgroup.centralizer (L : Set G)) (hc3 : orderOf c = 3)
    {P E₀ T₀ : Subgroup G} (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hcP : ∀ a ∈ P, a * c = c * a) (hE₀P : E₀ ≤ P) (hE₀9 : Nat.card E₀ = 9)
    (hE₀C : E₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hT₀L : T₀ ≤ L) (hT₀ : IsPGroup 2 T₀)
    (hE₀T₀ : E₀ ≤ Subgroup.normalizer (T₀ : Set G))
    (hT₀E₀ : ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set G)) :
    ∃ (A' : Subgroup G) (m' : ℕ), IsQuad417 L A' (E₀ ⊔ Subgroup.zpowers c) c m' ∧ P ≤ A' ∧
      c ∈ A' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  obtain ⟨B, hPB, hcB, hB⟩ := exists_isElemAbelian_le_mem hP hc3' hcP
  obtain ⟨A', hBA', hA'max⟩ := exists_le_maximal_isElemAbelian hB
  have hA' := hA'max.prop
  obtain ⟨m', hm'⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hA')
  have hcA' : c ∈ A' := hBA' hcB
  have hPA' : P ≤ A' := hPB.trans hBA'
  have hE₀A' : E₀ ≤ A' := hE₀P.trans hPA'
  have hT₀ne : T₀ ≠ ⊥ := by
    rintro rfl
    exact hT₀E₀ bot_le
  have hCT : Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (T₀ : Set G) :=
    (Subgroup.centralizer_le hT₀L).trans (Subgroup.centralizer_le_normalizer _)
  have hcomm : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA'.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hAC : A' ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hcA', hcC⟩)
    set W := A' ⊓ Subgroup.centralizer (L : Set G) with hW
    by_contra hWc
    have hcW : Subgroup.zpowers c ≤ W := Subgroup.zpowers_le.mpr ⟨hcA', hcC⟩
    have hlt : Subgroup.zpowers c < W := lt_of_le_of_ne hcW fun h => hWc (h ▸ le_rfl)
    have hW3 : 3 < Nat.card W := by
      have := Subgroup.card_lt_of_lt hlt
      rwa [Nat.card_zpowers, hc3] at this
    have hWe : CFSG.Assembly.IsElemAbelian 3 W := isElemAbelian_of_le hA' inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hWe)
    have hW9 : 9 ≤ Nat.card W := by
      rw [hk] at hW3 ⊢
      have hk2 : 2 ≤ k := by
        by_contra hk2
        interval_cases k <;> norm_num at hW3
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have hX : CFSG.Assembly.IsElemAbelian 3 (E₀ ⊔ W) :=
      isElemAbelian_of_le hA' (sup_le hE₀A' inf_le_left)
    have hXN : E₀ ⊔ W ≤ Subgroup.normalizer (T₀ : Set G) :=
      sup_le hE₀T₀ (inf_le_right.trans hCT)
    have h27 := card_le_27_of_le_normalizer hG hX hT₀ hT₀ne hXN
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E₀ W
      fun a ha b hb => hcomm a (hE₀A' ha) b hb.1
    have hinf : E₀ ⊓ W = ⊥ := le_bot_iff.mp (hE₀C ▸ inf_le_inf_left E₀ inf_le_right)
    rw [hinf, Subgroup.card_bot, mul_one, hE₀9] at hcard
    have : 81 ≤ Nat.card (E₀ ⊔ W : Subgroup G) := by rw [hcard]; omega
    omega
  have hcE₀ : c ∉ E₀ := fun h => by
    have : c ∈ E₀ ⊓ Subgroup.centralizer (L : Set G) := ⟨h, hcC⟩
    rw [hE₀C, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hc3
    norm_num at hc3
  have hE'A' : E₀ ⊔ Subgroup.zpowers c ≤ A' := sup_le hE₀A' (Subgroup.zpowers_le.mpr hcA')
  have hE' : Late.IsE27 (E₀ ⊔ Subgroup.zpowers c) := by
    refine ⟨isElemAbelian_of_le hA' hE'A', ?_⟩
    rw [card_sup_zpowers_eq_three_mul hc3 hcE₀ fun a ha b hb =>
      hcomm a (hE₀A' ha) b ((Subgroup.zpowers_le.mpr hcA') hb), hE₀9]
  refine ⟨A', m', ⟨hA'max, hm', hAC, hc3, hE', hE'A', T₀, ?_, ?_⟩, hPA', hcA'⟩
  · exact (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr
      ⟨hT₀L, hT₀, sup_le hE₀T₀ (Subgroup.zpowers_le.mpr (hCT hcC))⟩
  · exact fun h => hT₀E₀ (h.trans (Subgroup.centralizer_le fun x hx => Subgroup.mem_sup_left hx))

theorem false_of_star417 (hG : SectionFourHyp G) {L : Subgroup G}
    (hstar : ∀ (A E : Subgroup G) (c : G) (m : ℕ), IsQuad417 L A E c m → m ≤ 4) {c : G}
    (hcC : c ∈ Subgroup.centralizer (L : Set G)) (hc3 : orderOf c = 3)
    {P E₀ T₀ : Subgroup G} (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hcP : ∀ a ∈ P, a * c = c * a) (hE₀P : E₀ ≤ P) (hE₀9 : Nat.card E₀ = 9)
    (hE₀C : E₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hT₀L : T₀ ≤ L) (hT₀ : IsPGroup 2 T₀)
    (hE₀T₀ : E₀ ≤ Subgroup.normalizer (T₀ : Set G))
    (hT₀E₀ : ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set G))
    (h243 : 3 ^ 5 ≤ Nat.card (P ⊔ Subgroup.zpowers c : Subgroup G)) : False := by
  obtain ⟨A', m', hq, hPA', hcA'⟩ :=
    exists_isQuad417 hG hcC hc3 hP hcP hE₀P hE₀9 hE₀C hT₀L hT₀ hE₀T₀ hT₀E₀
  have hm' := hstar _ _ _ _ hq
  have h1 := Subgroup.card_le_of_le (sup_le hPA' (Subgroup.zpowers_le.mpr hcA'))
  rw [hq.2.1] at h1
  have : 3 ^ m' ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hm'
  omega

theorem card_sup_zpowers_of_le_of_not_mem {L P : Subgroup G} (hPL : P ≤ L) {c : G}
    (hcC : c ∈ Subgroup.centralizer (L : Set G)) (hc3 : orderOf c = 3) (hcL : c ∉ L) :
    Nat.card (P ⊔ Subgroup.zpowers c : Subgroup G) = 3 * Nat.card P := by
  refine card_sup_zpowers_eq_three_mul hc3 (fun h => hcL (hPL h)) fun a ha b hb => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hcC a (hPL ha)) k).eq

omit [Finite G] in
theorem isElemAbelian_closure_of_commute {S : Set G}
    (hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (h3 : ∀ x ∈ S, x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure S) := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h3 x hx
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

omit [Finite G] in
theorem isElemAbelian_sup_of_le_centralizer {R S : Subgroup G}
    (hR : CFSG.Assembly.IsElemAbelian 3 R) (hS : CFSG.Assembly.IsElemAbelian 3 S)
    (hRS : S ≤ Subgroup.centralizer (R : Set G)) :
    CFSG.Assembly.IsElemAbelian 3 (R ⊔ S) := by
  rw [Subgroup.sup_eq_closure]
  refine isElemAbelian_closure_of_commute ?_ ?_
  · rintro x (hx | hx) y (hy | hy)
    · exact congrArg Subtype.val (hR.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · exact (Subgroup.mem_centralizer_iff.mp (hRS hy) x hx)
    · exact (Subgroup.mem_centralizer_iff.mp (hRS hx) y hy).symm
    · exact congrArg Subtype.val (hS.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro x (hx | hx)
    · exact hR.2 x hx
    · exact hS.2 x hx

theorem exists_nine_of_isQuad417 {L A E : Subgroup G} {c : G} {m : ℕ}
    (hq : IsQuad417 L A E c m) :
    ∃ F T₁ : Subgroup G, F ≤ A ∧ Nat.card F = 9 ∧
      F ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ T₁ ≤ L ∧ IsPGroup 2 T₁ ∧
      F ≤ Subgroup.normalizer (T₁ : Set G) ∧ ¬ T₁ ≤ Subgroup.centralizer (F : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAmax, -, hAc, hc3, hE, hEA, T, hT, hTE⟩ := hq
  have hA := hAmax.prop
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hTL, hT2, hTN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hT
  have hcC : c ∈ Subgroup.centralizer (L : Set G) :=
    (hAc ▸ Subgroup.mem_zpowers c : c ∈ A ⊓ Subgroup.centralizer (L : Set G)).2
  have : IsElementaryAbelian 3 E := isElementaryAbelian_of_isElemAbelian hE.1
  have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE.2]; norm_num)
  have h3T : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hgen := Res417Three.le_iSup_hyperplane_centralizers hTN h3T
  obtain ⟨B, hB, hTB⟩ : ∃ B : Subgroup E, B.index = 3 ∧
      ¬ T ⊓ Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G) ≤
        Subgroup.centralizer (E : Set G) := by
    by_contra hall
    push Not at hall
    exact hTE (hgen.trans (iSup₂_le fun B hB => hall B hB))
  set BG : Subgroup G := B.map E.subtype with hBG
  set TB : Subgroup G := T ⊓ Subgroup.centralizer (BG : Set G) with hTBdef
  have hBG9 : Nat.card BG = 9 := by
    rw [hBG, Subgroup.card_map_of_injective E.subtype_injective]
    have h1 := Subgroup.card_mul_index B
    rw [hB, hE.2] at h1
    omega
  have hBGE : BG ≤ E := Subgroup.map_subtype_le B
  have hECB : E ≤ Subgroup.centralizer (BG : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b (hEA (hBGE hb)) e (hEA he)
  have hETB : E ≤ Subgroup.normalizer (TB : Set G) :=
    le_trans (le_inf hTN (hECB.trans (Subgroup.le_normalizer)))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hBGC : BG ≤ Subgroup.centralizer (TB : Set G) :=
    Subgroup.le_centralizer_iff.mp inf_le_right
  obtain ⟨t, htTB, htE⟩ := Set.not_subset.mp hTB
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at htE
  push Not at htE
  obtain ⟨e, he, hte⟩ := htE
  have heC : e ∉ Subgroup.centralizer (TB : Set G) := fun h =>
    hte (Subgroup.mem_centralizer_iff.mp h t htTB).symm
  have hz3 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
  obtain ⟨b, hbB, hbc⟩ : ∃ b ∈ BG, b ∉ Subgroup.zpowers c := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show BG ≤ Subgroup.zpowers c from hall)
    omega
  have hcTB : c ∈ Subgroup.centralizer (TB : Set G) :=
    Subgroup.centralizer_le (fun x hx => hTL hx.1) hcC
  have hb3 : orderOf b = 3 :=
    orderOf_eq_prime (hA.2 b (hEA (hBGE hbB))) fun h => hbc (h ▸ Subgroup.one_mem _)
  have he3 : orderOf e = 3 :=
    orderOf_eq_prime (hA.2 e (hEA he)) fun h => heC (h ▸ Subgroup.one_mem _)
  have heb : e ∉ Subgroup.zpowers b := fun h =>
    heC (hBGC ((Subgroup.zpowers_le.mpr hbB) h))
  have hbe : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers e, x * y = y * x := by
    intro x hx y hy
    exact hcomm x ((Subgroup.zpowers_le.mpr (hEA (hBGE hbB))) hx) y
      ((Subgroup.zpowers_le.mpr (hEA he)) hy)
  set F := Subgroup.zpowers b ⊔ Subgroup.zpowers e with hF
  have hF9 : Nat.card F = 9 := by
    rw [hF, card_sup_zpowers_eq_three_mul he3 heb hbe, Nat.card_zpowers, hb3]
  have hFA : F ≤ A := sup_le (Subgroup.zpowers_le.mpr (hEA (hBGE hbB)))
    (Subgroup.zpowers_le.mpr (hEA he))
  have hFE : F ≤ E := sup_le (Subgroup.zpowers_le.mpr (hBGE hbB)) (Subgroup.zpowers_le.mpr he)
  have hcA : c ∈ A := (hAc ▸ Subgroup.mem_zpowers c : c ∈ A ⊓ Subgroup.centralizer (L : Set G)).1
  have hbA : b ∈ A := hEA (hBGE hbB)
  have hFc : F ⊓ Subgroup.zpowers c = ⊥ := by
    have hdvd : Nat.card (F ⊓ Subgroup.zpowers c : Subgroup G) ∣ 3 :=
      hz3 ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : F ⊓ Subgroup.zpowers c = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hz3, h3])
      have hcF : c ∈ F := by
        have hc : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
        rw [← heq] at hc
        exact hc.1
      have hcb : c ∉ Subgroup.zpowers b := by
        intro h
        apply hbc
        have hle : Subgroup.zpowers c ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr h
        have heq' : Subgroup.zpowers c = Subgroup.zpowers b :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hz3, hb3])
        rw [heq']
        exact Subgroup.mem_zpowers b
      have h9 : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) = 9 := by
        rw [card_sup_zpowers_eq_three_mul hc3 hcb fun x hx y hy =>
          hcomm x ((Subgroup.zpowers_le.mpr hbA) hx) y ((Subgroup.zpowers_le.mpr hcA) hy),
          Nat.card_zpowers, hb3]
      have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ F :=
        sup_le le_sup_left (Subgroup.zpowers_le.mpr hcF)
      have heqF : Subgroup.zpowers b ⊔ Subgroup.zpowers c = F :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hF9, h9])
      have heF : e ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c :=
        heqF ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
      exact heC ((sup_le (Subgroup.zpowers_le.mpr (hBGC hbB))
        (Subgroup.zpowers_le.mpr hcTB)) heF)
  have hFC : F ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hFc]
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [← hAc]
    exact ⟨hFA hx.1, hx.2⟩
  refine ⟨F, TB, hFA, hF9, hFC, fun x hx => hTL hx.1, hT2.to_le inf_le_left, hFE.trans hETB,
    fun h => heC (Subgroup.le_centralizer_iff.mp h (Subgroup.mem_sup_right
      (Subgroup.mem_zpowers e)))⟩

end CFSG.RankThree.PartTwo.Sec4.Res417Five
