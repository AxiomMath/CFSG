module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFourteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.LayerSeventeenFiftyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.UniqueConjugacy
public import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEight
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProductComponents
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def R136a (D : Data G) : Prop :=
  D.sig = D.sig1 → F13.Hyp131 D → ∀ p ∈ D.sig, F13.Case136a D →
    Hinf D.M = F13.Lp D.M p ∧ ∃ n : ℕ, F13.Concl136 D p n

theorem hyp125_to_f12 {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    F12.Hyp125 D V₀ V := by
  obtain ⟨h123, H₀, hH, h124⟩ := h
  exact ⟨h123, H₀, TwelveEight.f12Hyp124_of_mem_hSet D hH h124⟩

theorem card_of_isL2 {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2 X n) :
    Nat.card X = 2 ^ n * (2 ^ (2 * n) - 1) := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h), ← pow_mul, mul_comm n 2]

theorem card_mul_gcd_of_isU3 {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsU3 X n) :
    Nat.card X * Nat.gcd 3 (2 ^ n + 1) =
      2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by
  have hSC : StatedClassicalModel X .PSU 3 2 n :=
    LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hcard := CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three
    (X := X) (p := 2) (e := n) hSC
  have h3 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by
    rw [← pow_mul]
    ring_nf
  have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
    rw [← pow_mul]
    ring_nf
  calc Nat.card X * Nat.gcd 3 (2 ^ n + 1)
      = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) := hcard
    _ = 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by rw [h3, h2]

theorem card_of_isL2Square_eq {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Square X n) :
    Nat.card X = 2 ^ (2 * n) * (2 ^ (2 * n) - 1) ^ 2 := by
  obtain ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ := h
  haveI : Finite (A × B) := Finite.of_equiv X e.toEquiv
  haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B)))
    (fun a b hab => by simpa using hab)
  haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b))
    (fun a b hab => by simpa using hab)
  have hp : 2 ^ n * 2 ^ n = 2 ^ (2 * n) := by
    rw [← pow_add]
    ring_nf
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_of_isL2 hA, card_of_isL2 hB]
  calc 2 ^ n * (2 ^ (2 * n) - 1) * (2 ^ n * (2 ^ (2 * n) - 1))
      = (2 ^ n * 2 ^ n) * ((2 ^ (2 * n) - 1) * (2 ^ (2 * n) - 1)) := by ring
    _ = 2 ^ (2 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (2 * n) - 1)) := by rw [hp]
    _ = 2 ^ (2 * n) * (2 ^ (2 * n) - 1) ^ 2 := by ring

theorem card_mul_gcd_of_isL2U3Product_eq {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsL2U3Product X n) :
    Nat.card X * Nat.gcd 3 (2 ^ n + 1) =
      2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) := by
  obtain ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ := h
  haveI : Finite (A × B) := Finite.of_equiv X e.toEquiv
  haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : B)))
    (fun a b hab => by simpa using hab)
  haveI : Finite B := Finite.of_injective (fun b : B => ((1 : A), b))
    (fun a b hab => by simpa using hab)
  have hB' := card_mul_gcd_of_isU3 hB
  have hA' := card_of_isL2 hA
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  calc Nat.card A * Nat.card B * Nat.gcd 3 (2 ^ n + 1)
      = Nat.card A * (Nat.card B * Nat.gcd 3 (2 ^ n + 1)) := by ring
    _ = (2 ^ n * (2 ^ (2 * n) - 1)) *
          (2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) := by
        rw [hA', hB']
    _ = 2 ^ (4 * n) *
          ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) := by
        have hp : 2 ^ n * 2 ^ (3 * n) = 2 ^ (4 * n) := by
          rw [← pow_add]
          ring_nf
        calc (2 ^ n * (2 ^ (2 * n) - 1)) *
              (2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)))
            = (2 ^ n * 2 ^ (3 * n)) *
                ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) := by ring
          _ = 2 ^ (4 * n) *
                ((2 ^ (2 * n) - 1) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1))) := by rw [hp]

theorem card_of_isL2Square {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2Square X n) :
    ∃ r : ℕ, Odd r ∧ Nat.card X = 2 ^ (2 * n) * r := by
  have hn : 1 ≤ n := by obtain ⟨A, B, _, _, -, hA, -⟩ := h; exact hA.admissible.2.1
  exact ⟨_, (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)).pow, card_of_isL2Square_eq h⟩

theorem card_mul_gcd_of_isL2U3Product {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsL2U3Product X n) :
    ∃ r : ℕ, Odd r ∧ Nat.card X * Nat.gcd 3 (2 ^ n + 1) = 2 ^ (4 * n) * r := by
  have hn : 1 ≤ n := by obtain ⟨A, B, _, _, -, hA, -⟩ := h; exact hA.admissible.2.1
  exact ⟨_, (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)).mul
    ((CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)).mul
      ((Nat.even_pow' (by omega)).mpr even_two).add_one),
    card_mul_gcd_of_isL2U3Product_eq h⟩

theorem isL2Square_field_unique {X : Type} [Group X] [Finite X] {n m : ℕ}
    (h1 : IsL2Square X n) (h2 : IsL2Square X m) : n = m := by
  obtain ⟨r, hr, h1'⟩ := card_of_isL2Square h1
  obtain ⟨s, hs, h2'⟩ := card_of_isL2Square h2
  have h := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (h1'.symm.trans h2')
  omega

theorem isL2U3Product_field_unique {X : Type} [Group X] [Finite X] {n m : ℕ}
    (h1 : IsL2U3Product X n) (h2 : IsL2U3Product X m) : n = m := by
  obtain ⟨r, hr, h1'⟩ := card_mul_gcd_of_isL2U3Product h1
  obtain ⟨s, hs, h2'⟩ := card_mul_gcd_of_isL2U3Product h2
  have hodd : ∀ k : ℕ, Odd (Nat.gcd 3 (2 ^ k + 1)) := fun k =>
    Odd.of_dvd_nat ⟨1, rfl⟩ (Nat.gcd_dvd_left 3 _)
  have h := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd (hr.mul (hodd m)) (hs.mul (hodd n))
    (show 2 ^ (4 * n) * (r * Nat.gcd 3 (2 ^ m + 1)) =
        2 ^ (4 * m) * (s * Nat.gcd 3 (2 ^ n + 1)) by
      rw [← mul_assoc, ← h1', ← mul_assoc, ← h2']; ring)
  omega

theorem P17_64_2_unique {D : Data G} {p n m : ℕ} (h1 : P17_64_2 D p n)
    (h2 : P17_64_2 D p m) : n = m := by
  rcases h1 with ⟨hs1, hsp1⟩ | ⟨hu1, hsp1⟩ <;> rcases h2 with ⟨hs2, hsp2⟩ | ⟨hu2, hsp2⟩
  · exact isL2Square_field_unique hs1 hs2
  · exact absurd hsp2 hsp1
  · exact absurd hsp1 hsp2
  · exact isL2U3Product_field_unique hu1 hu2

theorem not_isMulCommutative_of_isU3 {X : Type} [Group X] {n : ℕ}
    (h : IsU3 X n) : ¬ IsMulCommutative X := by
  intro hc
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 h
  exact hab (hc.is_comm.comm a b)

theorem exists_two_calC_of_p1642 {D : Data G} {n p : ℕ}
    (hn : P17_64_2 D p n) (hH : Hinf D.M = Lp D p) :
    ∃ KA KB : Subgroup G, KA ∈ calC D.M ∧ KB ∈ calC D.M ∧
      IsL2 (Bar2 KA) n ∧ (IsL2 (Bar2 KB) n ∨ IsU3 (Bar2 KB) n) ∧
      barImage D.M KA ≠ barImage D.M KB := by
  have hAab_of : ∀ {A : Type} [Group A] {n : ℕ},
      IsL2 A n → ¬ ∀ x y : A, x * y = y * x := by
    intro A _ n hA
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.HarrisLit.nonabelian_of_lieModel_psl2
        (p := 2) (f := n) hA
    exact fun h => hab (h a b)
  rcases hn with ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩ |
    ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩
  · letI := gA
    letI := gB
    haveI : IsSimpleGroup A :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
    haveI : IsSimpleGroup B :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
    obtain ⟨KA, KB, hKA, hKB, ⟨eA⟩, ⟨eB⟩, hne⟩ :=
      exists_two_calC_of_bar2_hinf_prod (hAab_of hA) (hAab_of hB)
        ((MulEquiv.cast (M := fun x : Subgroup G => Bar2 x) (by rw [hH])).trans e)
    exact ⟨KA, KB, hKA, hKB, LieModel.of_mulEquiv eA.symm hA,
      Or.inl (LieModel.of_mulEquiv eB.symm hB), hne⟩
  · letI := gA
    letI := gB
    haveI : IsSimpleGroup A :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
    haveI : IsSimpleGroup B :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
    obtain ⟨KA, KB, hKA, hKB, ⟨eA⟩, ⟨eB⟩, hne⟩ :=
      exists_two_calC_of_bar2_hinf_prod (hAab_of hA)
        (fun h => not_isMulCommutative_of_isU3 hB (isMulCommutative_iff.mpr h))
        ((MulEquiv.cast (M := fun x : Subgroup G => Bar2 x) (by rw [hH])).trans e)
    exact ⟨KA, KB, hKA, hKB, LieModel.of_mulEquiv eA.symm hA,
      Or.inr (LieModel.of_mulEquiv eB.symm hB), hne⟩

theorem zmod_of_dvd_two_pow_add_one {p n : ℕ} (h : p ∣ 2 ^ n + 1) :
    (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] :=
  (Int.modEq_iff_dvd.mpr (by simpa using Int.natCast_dvd_natCast.mpr h)).symm

theorem thin8_of_isL2 {L : Subgroup G} {n : ℕ} (h : IsL2 (Bar2 L) n) : Thin8 L := by
  intro p hp hp2
  rw [← pRank_bar2_eq_of_odd (Y := L) hp hp2]
  exact pRank_le_one_of_isL2_or_isSz (Or.inl h) hp hp2

theorem thin8_of_isSz {L : Subgroup G} {n : ℕ} (h : IsSz (Bar2 L) n) : Thin8 L := by
  intro p hp hp2
  rw [← pRank_bar2_eq_of_odd (Y := L) hp hp2]
  exact pRank_le_one_of_isL2_or_isSz (Or.inr h) hp hp2

theorem three_dvd_card_of_isL2Even {X : Type} [Group X] {m : ℕ} (h : IsL2 X m) :
    3 ∣ Nat.card X :=
  CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)

theorem three_dvd_card_of_bar_isL2Even {L : Subgroup G} {m : ℕ}
    (h : IsL2 (Bar2 L) m) : 3 ∣ Nat.card L :=
  (three_dvd_card_of_isL2Even h).trans (Subgroup.card_quotient_dvd_card _)

theorem three_dvd_card_of_bar_isL2Odd {L : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (h : IsL2Odd (Bar2 L) p) : 3 ∣ Nat.card L := by
  have h3 : 3 ∣ Nat.card (Bar2 L) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.three_dvd_card_of_isL2Odd (by have := hp.two_le; omega) h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)]
  exact h3.mul_right _

theorem thin8_of_isL2Odd {L : Subgroup G} {p : ℕ} (h : IsL2Odd (Bar2 L) p) : Thin8 L := by
  obtain ⟨hp, hp2, hp5⟩ := s13_five_le_of_isL2Odd h
  intro q hq hq2
  rw [← s13_pRank_bar_top hq hq2 L]
  exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_prime hp (by omega)
    (LieModel.statedClassicalModel_of_ne_zero (by norm_num) h) hq hq2

theorem thin8_of_isJ1 {L : Subgroup G} (h : IsJ1 (Bar2 L)) :
    Thin8 L := by
  intro p hp hp2
  rw [← s13_pRank_bar_top hp hp2 L]
  exact CFSG.QuasithinUnique.Id2519.pRank_le_one_J1 h hp hp2

theorem pRank_three_eq_one_of_isL2 {L : Subgroup G} {m : ℕ} (h : IsL2 (Bar2 L) m) :
    CFSG.Open.pRank 3 L = 1 :=
  pRank_three_eq_one_of_thin_of_dvd (thin8_of_isL2 h) (three_dvd_card_of_bar_isL2Even h)

theorem pRank_three_eq_one_of_isL2Odd {L : Subgroup G} {p : ℕ}
    (h : IsL2Odd (Bar2 L) p) : CFSG.Open.pRank 3 L = 1 := by
  obtain ⟨hp, hp2, hp5⟩ := s13_five_le_of_isL2Odd h
  exact pRank_three_eq_one_of_thin_of_dvd (thin8_of_isL2Odd h)
    (three_dvd_card_of_bar_isL2Odd hp hp2 (by omega) h)

theorem pRank_three_eq_one_of_isJ1 {L : Subgroup G}
    (h : IsJ1 (Bar2 L)) : CFSG.Open.pRank 3 L = 1 := by
  refine pRank_three_eq_one_of_thin_of_dvd (thin8_of_isJ1 h) ?_
  obtain ⟨e⟩ := h
  have h3 : 3 ∣ Nat.card (Bar2 L) := by
    rw [Nat.card_congr e.toEquiv]
    change 3 ∣ Nat.card (CFSG.Blueprint.NativeSporadic.J1)
    rw [CFSG.Sporadic.J1.card_J1]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)]
  exact h3.mul_right _

theorem isSpor_barInf_of_isJ1 {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (h : IsJ1 (Bar2 L)) : ∃ s, IsSpor (BarInf L) s := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup_congr.mpr CFSG.Sporadic.J1.isSimpleGroup_J1
  obtain ⟨f⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 (uc22p21k_center_eq_bot hL.2.2)
  exact ⟨.J1, ⟨f.trans e⟩⟩

theorem hyp131_normal {D : Data G} {p : ℕ} (hp : Hyp1754 D p) :
    ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal := fun L hL => (hp.2 L hL).1

theorem hyp131_thinOrU3 {D : Data G} {p : ℕ} (hp : Hyp1754 D p) {V₀ V : Subgroup G}
    (h33 : R17_33_2At D V₀ V) (h58 : R17_58At D V₀ V) :
    ∀ L ∈ calC D.M, Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n := by
  intro L hL
  obtain ⟨-, hthin | ⟨f, hU⟩ | hL3⟩ := hp.2 L hL
  · exact Or.inl hthin
  · exact Or.inr ⟨f, h33 L f hL (uc22p22d_isSU3_of_isU3 hL.2.2 hU), hU⟩
  · exact absurd hL3 (h58 p hp L hL)

theorem hyp131_uniq {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    (hp : Hyp1754 D p) (h3 : R17_3At D V₀ V) (h55 : R17_55At D V₀ V) :
    ∀ L ∈ calC D.M, ∀ n : ℕ, (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) →
      ∀ s : ℕ, Odd s → s ∣ n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
        ∀ X : Subgroup G, X ≤ L → Nat.card X = r →
          normalizer (X : Set G) ≤ D.M ∧
            X ∉ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  intro L hL n hn s hs hsn r hr hrdvd X hXL hXr
  have hr2 : r ≠ 2 := by have := s13_seven_le_of_dvd hs hr hrdvd; omega
  exact ⟨h3 L hL (hn.elim thin8_of_isL2 thin8_of_isSz) X ⟨r, hr, hr2, hXr, hXL⟩,
    fun hXU => h55 L hL.1.le (hp.2 L hL).1 n hn s hs hsn r hr hrdvd X hXL hXr
      (conjSetOf_eq_of_mem_uniqueSet D hXU)⟩

theorem centSection_eq_cMStar {M L : Subgroup G} (hLM : L ≤ M)
    (hNM : M ≤ normalizer (L : Set G)) :
    centSection M L (pCoreOf 2 L) = F13.cMStar M L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNO : M ≤ normalizer (pCoreOf 2 L : Set G) :=
    hNM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hO2 : pCoreOf 2 L ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM) hNO
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  ext m
  constructor
  · rintro ⟨hmM, -, -, hcomm⟩
    refine Subgroup.mem_map.mpr ⟨⟨m, hmM⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxL : (x : G) ∈ L := hx
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hO2 (hcomm x hxL))
    have hyx : y = ⟨m, hmM⟩ * x * (⟨m, hmM⟩ : ↥M)⁻¹ * x⁻¹ := Subtype.ext (by simpa using hyeq)
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
        (⟨m, hmM⟩ * x * (⟨m, hmM⟩ : ↥M)⁻¹ * x⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hyx ▸ hy)
    simp only [map_mul, map_inv] at h1
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  · intro hm
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hm
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at ha
    refine ⟨a.2, hNM a.2, hNO a.2, fun x hxL => ?_⟩
    have hcm := ha (QuotientGroup.mk' _ ⟨x, hLM hxL⟩) ⟨⟨x, hLM hxL⟩, hxL, rfl⟩
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
        (a * ⟨x, hLM hxL⟩ * a⁻¹ * (⟨x, hLM hxL⟩ : ↥M)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
      exact hcm.symm
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ pCoreOf 2 M := Subgroup.mem_map.mpr ⟨_, h2, rfl⟩
    have h4 : (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNM a.2) x).mp hxL) (L.inv_mem hxL)
    exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hLM ⟨h4, h3⟩

theorem sp_eq_f13Sp (D : Data G) (q : ℕ) : S17.Sp D q = F13.Sp D.M q := by
  have hLM : S17.Lp D q ≤ D.M := s13_Lp_le D.M q
  have hNM : D.M ≤ normalizer (S17.Lp D q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp (s13_Lp_normal D.M q)
  show Opp q (centSection D.M (S17.Lp D q) (pCoreOf 2 (S17.Lp D q))) =
    Opp q (F13.cMStar D.M (F13.Lp D.M q))
  rw [centSection_eq_cMStar hLM hNM]
  rfl

theorem hyp131_smallS {D : Data G} {p : ℕ} (hp : Hyp1754 D p) {V₀ V : Subgroup G}
    (h57 : R17_57At D V₀ V) : ∀ q ∈ D.sig, CFSG.Open.pRank q (F13.Sp D.M q) ≤ 1 := by
  intro q hq
  rw [← sp_eq_f13Sp D q]
  exact h57 q ⟨hq, hp.2⟩

theorem hyp131_notAmong {D : Data G} {V₀ V : Subgroup G}
    (h61 : R17_6_1At D V₀ V) (h63 : R17_6_3At D V₀ V)
    (h17 : R17_17At D V₀ V) (h33 : R17_33_2At D V₀ V) :
    ∀ L ∈ calC D.M,
      (IsJ1 (Bar2 L) ∨ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ f ∧
        LieModel (Bar2 L) .PSL 2 p f) →
      ∀ K ∈ calC D.M, K ≠ L →
        ¬ ((∃ n : ℕ, IsL2 (Bar2 K) (2 ^ n)) ∨ (∃ n : ℕ, IsU3 (Bar2 K) n) ∨
          (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd (Bar2 K) p) ∨ IsJ1 (Bar2 K)) := by
  intro L hL hLshape K hK hKL hKshape
  have hKey : (∀ K' ∈ calC D.M, Thin8 K' → CFSG.Open.pRank 3 K' = 1 → K' = L) ∧
      (∀ K' ∈ calC D.M, ∀ n : ℕ, ¬ IsU3 (Bar2 K') (2 * n)) := by
    rcases hLshape with hJ1 | ⟨p, f, hp, hp2, hpf, hmodel⟩
    · obtain ⟨s, hs⟩ := isSpor_barInf_of_isJ1 hL hJ1
      obtain ⟨-, ⟨-, -, huniq⟩, hnoU3, -⟩ := h17 L hL ⟨s, hs⟩
      refine ⟨fun K' hK' hthin hp3 => huniq K' hK' hthin ?_, hnoU3⟩
      have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K') = 1 := by
        rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K']
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥K']
      exact h1
    · have hf : 1 ≤ f := hmodel.admissible.2.1
      have hLover : IsL2Over17 (Bar2 L) (p ^ f) := ⟨p, f, hp, hp2, rfl, hf, hmodel⟩
      obtain ⟨e⟩ := SeventeenFourteen.barInf_equiv_bar2 hL hLover
      have hchev : IsChev (BarInf L) p :=
        ⟨.PSL, 2, f, hmodel.admissible, LieModel.of_mulEquiv e.symm hmodel⟩
      have hLoverP : IsL2Over17 (Bar2 L) p := h61 L hL p hp2 hchev
      have hLodd : IsL2Odd (Bar2 L) p := isL2Odd_of_isL2Over17_prime hp hLoverP
      have hpow : p ^ f = p ^ 1 :=
        CFSG.GH74.GLS.EvenSelP.pow_eq_of_lieModel hp hp2 hp hp2 hmodel hLodd
      have hf1 : f = 1 := Nat.pow_right_injective hp.two_le hpow
      have hp5 : 5 < p := by
        have h := hpf
        rwa [hf1, pow_one] at h
      obtain ⟨⟨K₀, ⟨-, hK₀thin, hK₀p3⟩, huniq₀⟩, hnoU3₀⟩ :=
        h63 L hL p hp2 hchev hp5
      have hLthin : Thin8 L := thin8_of_isL2Odd hLodd
      have hLp3 : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isL2Odd hLodd
      have hLeq : L = K₀ := huniq₀ L ⟨hL, hLthin, hLp3⟩
      refine ⟨fun K' hK' hthin hp3 => ?_, fun K' hK' n hU => hnoU3₀ K' hK' n hU⟩
      exact (huniq₀ K' ⟨hK', hthin, hp3⟩).trans hLeq.symm
  obtain ⟨huniq, hnoU3⟩ := hKey
  rcases hKshape with ⟨n, hK2⟩ | ⟨n, hKU3⟩ | ⟨p, hp, hp2, hKodd⟩ | hKJ1
  · exact hKL (huniq K hK (thin8_of_isL2 hK2) (pRank_three_eq_one_of_isL2 hK2))
  · have hSU : IsSU3 (Bar2 K) n := uc22p22d_isSU3_of_isU3 hK.2.2 hKU3
    obtain ⟨k, hk⟩ := h33 K n hK hSU
    have hk0 : k ≠ 0 := by
      intro h0
      have h2n : 2 ≤ n := s13_two_le_of_isU3 hKU3
      rw [hk, h0, pow_zero] at h2n
      omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjk : k = j + 1 := by simpa using hj
    refine hnoU3 K hK (2 ^ j) ?_
    have hn : 2 * 2 ^ j = 2 ^ (j + 1) := by rw [pow_succ]; ring
    rw [hn, ← hjk, ← hk]
    exact hKU3
  · exact hKL (huniq K hK (thin8_of_isL2Odd hKodd) (pRank_three_eq_one_of_isL2Odd hKodd))
  · exact hKL (huniq K hK (thin8_of_isJ1 hKJ1) (pRank_three_eq_one_of_isJ1 hKJ1))

theorem hyp131_of {D : Data G} {V₀ V : Subgroup G}
    {p : ℕ} (hp : Hyp1754 D p) (hV : Hyp125 D V₀ V)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    (h3 : R17_3At D V₀ V) (h33 : R17_33_2At D V₀ V) (h55 : R17_55At D V₀ V)
    (h57 : R17_57At D V₀ V) (h58 : R17_58At D V₀ V) (h61 : R17_6_1At D V₀ V)
    (h63 : R17_6_3At D V₀ V) (h17 : R17_17At D V₀ V)
    (hcyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) :
    F13.Hyp131 D where
  thinOrU3 := hyp131_thinOrU3 hp h33 h58
  normal := hyp131_normal hp
  layer := layer_seventeen_fiftyfour D hp hV h22 h23 hcyc
  uniq := hyp131_uniq hp h3 h55
  smallS := hyp131_smallS hp h57
  notAmong := hyp131_notAmong h61 h63 h17 h33

private theorem concl136_at {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1219 : D.sig = D.sig1) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h136 : R136a D) (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    (h3 : R17_3At D V₀ V) (h33 : R17_33_2At D V₀ V)
    (h55 : R17_55At D V₀ V) (h57 : R17_57At D V₀ V) (h58 : R17_58At D V₀ V)
    (h61 : R17_6_1At D V₀ V) (h63 : R17_6_3At D V₀ V) (h17 : R17_17At D V₀ V)
    (hcyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    {p : ℕ} (hp : Hyp1754 D p) :
    Hinf D.M = Lp D p ∧ ∃ n : ℕ, F13.Concl136 D p n := by
  have h131 : F13.Hyp131 D :=
    hyp131_of hp hV h22 h23 h3 h33 h55 h57 h58 h61 h63 h17 hcyc
  exact h136 h1219 h131 p hp.1 ⟨V₀, V, hyp125_to_f12 hV, h1669⟩

private theorem p17_64_2_of_concl136 {D : Data G} {p n : ℕ} (h : F13.Concl136 D p n) :
    P17_64_2 D p n := by
  rcases h.1 with ⟨⟨A, B, gA, gB, hA, hB, he⟩, hsp⟩ | ⟨⟨A, B, gA, gB, hA, hB, he⟩, hsp⟩
  · exact Or.inl ⟨⟨A, B, gA, gB, he, hA, hB⟩, by rw [sp_eq_f13Sp D p]; exact hsp⟩
  · exact Or.inr ⟨⟨A, B, gA, gB, he, hA, hB⟩, by rw [sp_eq_f13Sp D p]; exact hsp⟩

theorem seventeen_sixtyfour_one (D : Data G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h1219 : D.sig = D.sig1)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h136 : R136a D)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    (h3 : R17_3At D V₀ V) (h6_1 : R17_6_1At D V₀ V) (h6_3 : R17_6_3At D V₀ V)
    (h17 : R17_17At D V₀ V) (h33 : R17_33_2At D V₀ V) (h55 : R17_55At D V₀ V)
    (h57 : R17_57At D V₀ V) (h58 : R17_58At D V₀ V)
    (hcyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) :
    R17_64_1At D V₀ V := by
  intro p hp
  exact (concl136_at hV h1219 h1669 h136 h22 h23 h3 h33 h55 h57 h58 h6_1 h6_3 h17 hcyc hp).1

theorem seventeen_sixtyfour_two (D : Data G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h1219 : D.sig = D.sig1)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h136 : R136a D)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    (h3 : R17_3At D V₀ V) (h6_1 : R17_6_1At D V₀ V) (h6_3 : R17_6_3At D V₀ V)
    (h17 : R17_17At D V₀ V) (h33 : R17_33_2At D V₀ V) (h55 : R17_55At D V₀ V)
    (h57 : R17_57At D V₀ V) (h58 : R17_58At D V₀ V)
    (hcyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) :
    R17_64_2At D V₀ V := by
  intro p hp
  obtain ⟨-, n, hconcl⟩ :=
    concl136_at hV h1219 h1669 h136 h22 h23 h3 h33 h55 h57 h58 h6_1 h6_3 h17 hcyc hp
  exact ⟨n, p17_64_2_of_concl136 hconcl⟩

theorem seventeen_sixtyfour_three (D : Data G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h1219 : D.sig = D.sig1)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) (h136 : R136a D)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    (h3 : R17_3At D V₀ V) (h6_1 : R17_6_1At D V₀ V) (h6_3 : R17_6_3At D V₀ V)
    (h17 : R17_17At D V₀ V) (h33 : R17_33_2At D V₀ V) (h55 : R17_55At D V₀ V)
    (h57 : R17_57At D V₀ V) (h58 : R17_58At D V₀ V)
    (hcyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) :
    R17_64_3At D V₀ V := by
  intro p hp n hn
  obtain ⟨-, n₀, hconcl⟩ :=
    concl136_at hV h1219 h1669 h136 h22 h23 h3 h33 h55 h57 h58 h6_1 h6_3 h17 hcyc hp
  rw [P17_64_2_unique hn (p17_64_2_of_concl136 hconcl)]
  exact ⟨hconcl.2.1, zmod_of_dvd_two_pow_add_one hconcl.2.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
