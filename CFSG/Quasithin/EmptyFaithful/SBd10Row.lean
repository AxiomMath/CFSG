module

public import CFSG.Quasithin.Background.A3Structure312Defs
import CFSG.Quasithin.Vol2.Ch11SecA11Cases1
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure37Comm

public section

namespace CFSG.Quasithin.SBd10

open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)

section Orders

variable {X : Type} [Group X]

private theorem card_of_isAlt {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k X) :
    Nat.card X = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

private theorem card_of_isHat {S : Type} [Group S] (h : IsHat X S) :
    Nat.card X = Nat.card S * 3 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  rw [(Subgroup.center X).card_eq_card_quotient_mul_card_subgroup, h3, Nat.card_congr e.toEquiv]

private theorem card_of_isPSL {k p e : ℕ} (hk : 0 < k) (h : IsPSL k p e X) :
    Nat.card X = ((p ^ e) ^ (k * (k - 1) / 2) * ∏ i ∈ Finset.Icc 2 k, ((p ^ e) ^ i - 1)) /
      k.gcd (p ^ e - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl hk h

private theorem card_of_isSL2 {p : ℕ} (hp : p.Prime) (h : IsSL2 p X) :
    Nat.card X = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.OrderReductions.LinearOrders.card_specialLinear (ZMod p) 2 (by norm_num),
    Nat.card_zmod]
  simp

private theorem odd_two_pow_sub_one {e : ℕ} (he : 1 ≤ e) : Odd (2 ^ e - 1) := by
  have h2 : Even (2 ^ e) := (Nat.even_pow' (by omega)).mpr even_two
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) h2 odd_one

private theorem eleven_dvd_card_M22 : 11 ∣ Nat.card ↥NativeSporadic.M22 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg, hg11, hg1⟩ : ∃ g ∈ NativeSporadic.M22, g ^ 11 = 1 ∧ g ≠ 1 := by
    refine ⟨_, Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))), ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  have ho : orderOf (⟨g, hg⟩ : ↥NativeSporadic.M22) = 11 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hg11 hg1
  rw [← ho]
  exact orderOf_dvd_natCard _

private theorem card_isE2 {k : ℕ} (h : IsE2 k X) : Nat.card X = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin k → ZMod 2) = 2 ^ k
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

private theorem card_isZ4Cubed (h : IsZ4Cubed X) : Nat.card X = 2 ^ 6 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 3 → ZMod 4) = 2 ^ 6
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

private theorem card_isZ4StarExtra2 [Finite X] (h : IsZ4StarExtra2 X) :
    ∃ k, Nat.card X = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, E, hZ, -, hE, hZc, hZE, -⟩ := h
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZc hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hp : IsPGroup 2 ↥(Z ⊔ E) :=
    IsPGroup.to_sup_of_normal_left (IsPGroup.of_card (n := 2) (by rw [hZ]; norm_num))
      (IsPGroup.of_card hE.2)
  rw [hZE] at hp
  exact IsPGroup.iff_card.mp (hp.of_equiv Subgroup.topEquiv)

private theorem four_le_card_isZ4StarExtra2 [Finite X] (h : IsZ4StarExtra2 X) : 4 ≤ Nat.card X := by
  obtain ⟨Z, -, hZ, -⟩ := h
  rw [← hZ]
  exact Subgroup.card_le_card_group Z

private theorem card_alt5 (h : IsAlt 5 X) : Nat.card X = 60 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

private theorem card_alt6 (h : IsAlt 6 X) : Nat.card X = 360 := by
  rw [card_of_isAlt (by norm_num) h]
  decide

private theorem card_hat6 (h : IsHat X (alternatingGroup (Fin 6))) : Nat.card X = 1080 := by
  rw [card_of_isHat h, nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem card_L32 (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

private theorem card_L42 (h : IsPSL 4 2 1 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

private theorem card_L34 (h : IsPSL 3 2 2 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

private theorem two_mul_card_of_isPSL_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSL 2 p 1 X) :
    2 * Nat.card X = p * (p ^ 2 - 1) :=
  CFSG.Quasithin.Vol2.Ch11.SecA.two_mul_card_of_isPSL_two hp hp2 h

private theorem false_of_isPSL_two_two {m : ℕ} (h : IsPSL 2 2 m X) (hc : Nat.card X = 62400) :
    False := by
  have hm : 1 ≤ m := h.1.2.1
  have hform := card_of_isPSL (by norm_num) h
  have hg : Nat.gcd 2 (2 ^ m - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hm)
  rw [hg, Nat.div_one] at hform
  simp only [pow_one, show 2 * (2 - 1) / 2 = 1 by norm_num, Finset.Icc_self,
    Finset.prod_singleton] at hform
  rw [hc] at hform
  rcases Nat.lt_or_ge m 6 with hlt | hge
  · interval_cases m <;> omega
  · have h6 : 2 ^ 6 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hge
    have h1 : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have : 64 * 4095 ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      refine Nat.mul_le_mul (by simpa using h6) ?_
      have : 64 ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left (by simpa using h6) 2
      omega
    omega

private theorem false_of_isSz {f : ℕ} (h : IsSz f X)
    (hc : Nat.card X = 62400) : False := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [hf] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK] at hc
  rcases Nat.lt_or_ge a 2 with hlt | hge
  · obtain rfl : a = 1 := by omega
    norm_num at hc
  · have h5 : 2 ^ 5 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 2 ^ (2 * a + 1) = q at h5 hc
    have hq : 32 ≤ q := by simpa using h5
    have h1 : 32 * 32 ≤ q ^ 2 := by nlinarith
    have h2 : 31 ≤ q - 1 := by omega
    have h3 : 1025 ≤ q ^ 2 + 1 := by omega
    have h4 : 1024 * 31 * 1025 ≤ q ^ 2 * (q - 1) * (q ^ 2 + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

private theorem no_sl2_card {p : ℕ} (h : p * (p ^ 2 - 1) = 62400) : False := by
  rcases Nat.lt_or_ge p 41 with hlt | hge
  · interval_cases p <;> omega
  · have h1 : 41 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hge 2
    have : 41 * 1680 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hge (by omega)
    omega

private theorem no_psl2_card {p : ℕ} (h : p * (p ^ 2 - 1) = 124800) : False := by
  rcases Nat.lt_or_ge p 51 with hlt | hge
  · interval_cases p <;> omega
  · have h1 : 51 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hge 2
    have : 51 * 2600 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hge (by omega)
    omega

end Orders

section Simple

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
structure U34Row (B : Subgroup Q) : Prop where
  simple : IsSimpleGroup ↥B
  card : Nat.card ↥B = 62400
  modCard : Nat.card (ModO2 B) = 62400

variable {B : Subgroup Q}

omit [Finite Q] in
theorem U34Row.odd_normal (hD : U34Row B) {N : Subgroup ↥B} (hN : N.Normal)
    (hodd : Odd (Nat.card ↥N)) : N = ⊥ := by
  have := hN
  rcases hD.simple.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h, Subgroup.card_top, hD.card] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨31200, by norm_num⟩

omit [Finite Q] in
theorem U34Row.not_two_pow (hD : U34Row B) : ¬ ∃ k : ℕ, Nat.card ↥B = 2 ^ k := by
  rintro ⟨k, hk⟩
  rw [hD.card] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 62400)
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem U34Row.false_of_ext (hD : U34Row B) {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, 1 ≤ k ∧ Nat.card V = 2 ^ k) : False := by
  obtain ⟨V, hVn, hPV', -⟩ := h
  obtain ⟨k, hk1, hk⟩ := hPV _ hPV'
  have := hVn
  rcases hD.simple.eq_bot_or_eq_top_of_normal V with hV | hV
  · rw [hV, Subgroup.card_bot] at hk
    have h2 : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
  · rw [hV, Subgroup.card_top] at hk
    exact hD.not_two_pow ⟨k, hk⟩

end Simple

section Rows

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

omit [Finite Q] in
theorem U34Row.false_C2_C11 (hD : U34Row B)
    (h : A312C2 B L ∨ A312C3 B L ∨ A312C4 B L ∨ A312C6 B L ∨ A312C7 B L ∨ A312C8 B L ∨
      A312C9 B L ∨ A312C10 B L ∨ A312C11 B L) : False := by
  have h3 : Nat.card (ModO2 B) = 62400 := hD.modCard
  have hc : Nat.card ↥B = 62400 := hD.card
  rcases h with ⟨⟨m, hm⟩, -⟩ | ⟨f, hf, -⟩ | ⟨hB, -⟩ | ⟨hB | hB, -⟩ |
      (⟨hB, -⟩ | ⟨hB, -⟩) | (⟨p, hp, hp3, hB, -⟩ | ⟨hB, -⟩) |
      (⟨s, p, hp, hp3, hB, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩) | ⟨p, hp, hp3, ⟨V, hV, ⟨e⟩, -⟩, -⟩ | ⟨hB, -⟩
  · exact false_of_isPSL_two_two hm h3
  · exact false_of_isSz hf h3
  · rw [card_L32 hB] at h3
    norm_num at h3
  · rw [card_alt5 hB] at hc
    norm_num at hc
  · rw [card_L32 hB] at hc
    norm_num at hc
  · rw [card_alt6 hB] at hc
    norm_num at hc
  · rw [card_hat6 hB] at hc
    norm_num at hc
  · have h2 := two_mul_card_of_isPSL_two hp (by omega) hB
    rw [hc] at h2
    exact no_psl2_card h2.symm
  · rw [card_alt5 hB] at hc
    norm_num at hc
  · have h2 := card_of_isSL2 hp hB
    rw [hc] at h2
    exact no_sl2_card h2.symm
  · rw [card_alt6 hB] at hc
    norm_num at hc
  · rw [card_hat6 hB] at hc
    norm_num at hc
  · have : NeZero p := ⟨hp.ne_zero⟩
    have hcard : Nat.card ↥V = p ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Fin 2 → ZMod p) = p ^ 2
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    have hodd : Odd (Nat.card ↥V) := by
      rw [hcard]
      exact (hp.odd_of_ne_two (by omega)).pow
    have hbot := hD.odd_normal hV hodd
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  · rw [card_alt6 hB] at hc
    norm_num at hc

omit [Finite Q] in
theorem U34Row.false_C5 (hD : U34Row B) (h : A312C5 B L) : False := by
  have h3 : Nat.card (ModO2 B) = 62400 := hD.modCard
  rw [card_L42 h.1] at h3
  norm_num at h3

theorem U34Row.false_C12_C20 (hD : U34Row B)
    (h : A312C12 B L ∨ A312C13 B L ∨ A312C14 B L ∨ A312C15 B L ∨ A312C16 B L ∨ A312C17 B L ∨
      A312C18 B L ∨ A312C19 B L ∨ A312C20 B L) : False := by
  have hE : ∀ m, 1 ≤ m → ∀ (V : Type) [Group V] [Finite V], IsE2 m V →
      ∃ k, 1 ≤ k ∧ Nat.card V = 2 ^ k := fun m hm V _ _ hV => ⟨m, hm, card_isE2 hV⟩
  have hX : ∀ (V : Type) [Group V] [Finite V], ∀ {m : ℕ}, IsExtraspecial2 m V →
      ∃ k, 1 ≤ k ∧ Nat.card V = 2 ^ k := fun V _ _ m hV => ⟨1 + 2 * m, by omega, hV.2⟩
  have hZ : ∀ (V : Type) [Group V] [Finite V], IsZ4StarExtra2 V →
      ∃ k, 1 ≤ k ∧ Nat.card V = 2 ^ k := by
    intro V _ _ hV
    obtain ⟨k, hk⟩ := card_isZ4StarExtra2 hV
    have h4 := four_le_card_isZ4StarExtra2 hV
    refine ⟨k, ?_, hk⟩
    by_contra hk0
    obtain rfl : k = 0 := by omega
    rw [hk] at h4
    norm_num at h4
  have h3 : Nat.card (ModO2 B) = 62400 := hD.modCard
  have hc : Nat.card ↥B = 62400 := hD.card
  rcases h with (⟨hB | hB, -⟩ | ⟨hB | hB, -⟩) | h | h | ⟨hB, -⟩ | ⟨hB, -⟩ | h | ⟨hB | hB, -⟩ |
      ⟨hB | hB, -⟩ | ⟨hB | hB, -, -⟩
  · exact hD.false_of_ext hB (hE 4 (by norm_num))
  · exact hD.false_of_ext hB (hE 4 (by norm_num))
  · exact hD.false_of_ext hB (hE 4 (by norm_num))
  · exact hD.false_of_ext hB (hE 4 (by norm_num))
  · obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩ := h
    · obtain ⟨e⟩ := hB
      have h11 : 11 ∣ Nat.card ↥B := by
        rw [Nat.card_congr e.toEquiv]
        exact eleven_dvd_card_M22
      rw [hc] at h11
      omega
    · rw [card_L34 hB] at hc
      norm_num at hc
    · exact hD.false_of_ext hB (hE 4 (by norm_num))
    · exact hD.false_of_ext hB (hE 4 (by norm_num))
    · exact hD.false_of_ext hB (hE 3 (by norm_num))
    · exact hD.false_of_ext hB (hE 4 (by norm_num))
    · exact hD.false_of_ext hB (hE 4 (by norm_num))
  · obtain ⟨hB | hB | hB | hB, hL⟩ := h
    · exact hD.false_of_ext hB (hE 4 (by norm_num))
    · exact hD.false_of_ext hB (hE 6 (by norm_num))
    · exact hD.false_of_ext hB (fun V _ _ hV => hX V hV)
    · exact hD.false_of_ext hB (hE 6 (by norm_num))
  · rw [card_alt5 hB] at hc
    norm_num at hc
  · exact hD.false_of_ext hB (fun V _ _ hV => hX V hV)
  · obtain ⟨-, hB | hB | hB | hB | hB | hB⟩ := h
    · exact hD.false_of_ext hB (fun V _ _ hV => hX V hV)
    · exact hD.false_of_ext hB (hE 11 (by norm_num))
    · rw [card_alt5 hB] at h3
      norm_num at h3
    · rw [card_hat6 hB] at h3
      norm_num at h3
    · rw [card_L42 hB] at h3
      norm_num at h3
    · rw [card_L32 hB] at h3
      norm_num at h3
  · exact hD.false_of_ext hB hZ
  · exact hD.false_of_ext hB (fun V _ _ hV => ⟨6, by norm_num, card_isZ4Cubed hV⟩)
  · exact hD.false_of_ext hB (fun V _ _ hV => hX V hV)
  · exact hD.false_of_ext hB (hE 6 (by norm_num))
  · rw [card_alt5 hB] at h3
    norm_num at h3
  · rw [card_L32 hB] at h3
    norm_num at h3

omit [Finite Q] in
private theorem relIndex_sup_eq_of_le_normalizer {A D : Subgroup Q}
    (h : A ≤ Subgroup.normalizer (D : Set Q)) : D.relIndex (A ⊔ D) = D.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A D h).toEquiv.symm

omit [Finite Q] in
theorem U34Row.card_sup_eq (hD : U34Row B) {O : Subgroup Q}
    (hBO : B ≤ Subgroup.normalizer (O : Set Q)) (hO : Odd (Nat.card ↥O)) :
    Nat.card ↥(B ⊔ O) = Nat.card ↥B * Nat.card ↥O := by
  have hN : (O.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
    exact fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hBO hb, Subgroup.le_normalizer hb⟩
  have hc : Nat.card ↥(O.subgroupOf B) = Nat.card ↥(O ⊓ B) := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hodd : Odd (Nat.card ↥(O.subgroupOf B)) := by
    rw [hc]
    exact hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hbot := hD.odd_normal hN hodd
  have hOB : O ⊓ B = ⊥ := by
    rw [← Subgroup.subgroupOf_map_subtype, hbot, Subgroup.map_bot]
  have h2 := Subgroup.relIndex_mul_card O B
  rw [hOB, Subgroup.card_bot, mul_one] at h2
  have h3 := Subgroup.relIndex_mul_card O (B ⊔ O)
  rw [relIndex_sup_eq_of_le_normalizer hBO, h2, inf_eq_left.mpr le_sup_right] at h3
  exact h3.symm

theorem U34Row.false_of_nonquasi (hD : U34Row B) (hBL : B ≤ L) (h : A312Nonquasi B L) :
    False := by
  have hOLL : (CFSG.oddCore ↥L).map L.subtype ≤ L := Subgroup.map_subtype_le _
  have hLO :
      L ≤ Subgroup.normalizer (((CFSG.oddCore ↥L).map L.subtype : Subgroup Q) : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOLL).mp ?_
    have he : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [he]
    infer_instance
  have hOcard : Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) = Nat.card ↥(CFSG.oddCore ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hOodd : Odd (Nat.card ↥((CFSG.oddCore ↥L).map L.subtype)) := by
    rw [hOcard]
    exact A37.odd_card_oddCore _
  have h1 := hD.card_sup_eq (hBL.trans hLO) hOodd
  have hpos : 0 < Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := Nat.card_pos
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, hNeq, hN5⟩
  · rw [← hLB] at h1
    have h2 := (CFSG.oddCore ↥L).card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 hp hSL, ← hOcard] at h2
    have hB : Nat.card ↥B = p * (p ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    exact no_sl2_card (hB.symm.trans hD.card)
  · have h2 := N.card_eq_card_quotient_mul_card_subgroup
    rw [card_of_isSL2 (by norm_num) hN5] at h2
    have h3 : Nat.card ↥N = Nat.card ↥((CFSG.oddCore ↥L).map L.subtype) := by
      rw [hNeq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h3] at h2
    have hB : Nat.card ↥B = 5 * (5 ^ 2 - 1) := Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2)
    have := hD.card
    omega

theorem row_u34 {B N : Subgroup Q} (hD : U34Row B) (hBN : B ≤ N)
    (h : A312Case B N ∨ A312Nonquasi B N) : False := by
  rcases h with h | h
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact hD.false_C2_C11 (Or.inl h)
    · exact hD.false_C2_C11 (Or.inr (Or.inl h))
    · exact hD.false_C2_C11 (Or.inr (Or.inr (Or.inl h)))
    · exact hD.false_C5 h
    · exact hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact hD.false_C2_C11 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
    · exact hD.false_C12_C20 (Or.inl h)
    · exact hD.false_C12_C20 (Or.inr (Or.inl h))
    · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inl h)))
    · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact hD.false_C12_C20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
  · exact hD.false_of_nonquasi hBN h

end Rows

end CFSG.Quasithin.SBd10
