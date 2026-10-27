module

public import CFSG.Quasithin.EmptyFaithful.S151U4
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Cocycle
public import CFSG.Quasithin.EmptyFaithful.A38cBasic
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.H13.VolIA38Orders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.Timmesfeld.Orders CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA
open scoped commutatorElement

variable {G : Type} [Group G]

theorem s151u_exists_third {α : Type*} [Finite α] (h : 4 ≤ Nat.card α) (a b : α) :
    ∃ c, c ≠ a ∧ c ≠ b := by
  classical
  by_contra hcon
  push Not at hcon
  have hle : Nat.card α ≤ Nat.card Bool := by
    refine Nat.card_le_card_of_injective (fun x => decide (x = a)) (fun x y hxy => ?_)
    by_cases hx : x = a <;> by_cases hy : y = a
    · rw [hx, hy]
    · simp [hx, hy] at hxy
    · simp [hx, hy] at hxy
    · rw [hcon x hx, hcon y hy]
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hle
  omega

theorem s151u_hrank [Finite G] {L : Subgroup G} (hbig : 4 ≤ Nat.card (BlockN L)) :
    ∃ u₁ ∈ blockU L, ∃ u₂ ∈ blockU L, u₁ ∉ blockZ L ∧ u₂ ∉ blockZ L ∧
      u₁⁻¹ * u₂ ∉ blockZ L := by
  have hmk : ∀ ω : BlockN L, ∃ u : ↥(blockU L), (u : BlockN L) = ω := fun ω =>
    QuotientGroup.mk_surjective ω
  obtain ⟨ω₁, hω₁, -⟩ := s151u_exists_third hbig ((1 : ↥(blockU L)) : BlockN L) ((1 : ↥(blockU L)) : BlockN L)
  obtain ⟨ω₂, hω₂o, hω₂ω₁⟩ := s151u_exists_third hbig ((1 : ↥(blockU L)) : BlockN L) ω₁
  obtain ⟨u₁, rfl⟩ := hmk ω₁
  obtain ⟨u₂, rfl⟩ := hmk ω₂
  refine ⟨u₁, u₁.2, u₂, u₂.2, ?_, ?_, ?_⟩
  · intro hz
    apply hω₁
    rw [s151u_mk_eq_iff]
    simpa using (blockZ L).inv_mem hz
  · intro hz
    apply hω₂o
    rw [s151u_mk_eq_iff]
    simpa using (blockZ L).inv_mem hz
  · intro hz
    apply hω₂ω₁
    rw [s151u_mk_eq_iff]
    simpa using (blockZ L).inv_mem hz

theorem s151u_odd_part {b c m o : ℕ} (hm : m % 2 = 1) (ho : o % 2 = 1)
    (h : 2 ^ b * m = 2 ^ c * o) : m = o := by
  have hcm : Nat.Coprime m (2 ^ c) := Nat.Coprime.pow_right c (by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega)
  have hco : Nat.Coprime o (2 ^ b) := Nat.Coprime.pow_right b (by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega)
  have h1 : m ∣ o := by
    have : m ∣ 2 ^ c * o := ⟨2 ^ b, by rw [← h]; ring⟩
    exact hcm.dvd_of_dvd_mul_left this
  have h2 : o ∣ m := by
    have : o ∣ 2 ^ b * m := ⟨2 ^ c, by rw [h]; ring⟩
    exact hco.dvd_of_dvd_mul_left this
  exact Nat.dvd_antisymm h1 h2

theorem s151u_hmax3_of_lat {L B : Subgroup G}
    (hlat : ∀ M' : Subgroup G, IsMaxSubgroupIn L M' → B ≤ M' → ∃ P : Subgroup G, OtherPar L B M' P) :
    ∀ H : Subgroup G, IsMaxSubgroupIn L H → B ≤ H → Nat.card H = 3 * Nat.card B := by
  intro H hH hBH
  obtain ⟨P, hP⟩ := hlat H hH hBH
  obtain ⟨Q, hQ⟩ := hlat P hP.max hP.ge
  rcases hQ.only H hH hBH with h | h
  · rw [h]
    exact hP.card3
  · rw [h]
    exact hQ.card3

theorem s151u_zl2_of_numerics [Finite G] {S L : Subgroup G} (hsh : IsShort2 L) (hperf : ⁅L, L⁆ = L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hB : IsSylowTwoOf (S ⊓ L) L)
    (hN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L)
    (hmax3 : ∀ H : Subgroup G, IsMaxSubgroupIn L H → S ⊓ L ≤ H →
      Nat.card H = 3 * Nat.card (S ⊓ L : Subgroup G))
    {e q o : ℕ} (ho : o % 2 = 1) (hLcard : Nat.card ↥L = 2 ^ q * (2 ^ e * o))
    (hN3 : o = 3 * (Nat.card (BlockN L) - 1)) (hbig : 4 ≤ Nat.card (BlockN L)) : ZL2 S L := by
  have hBL : S ⊓ L ≤ L := inf_le_right
  have hcard : Nat.card ↥L = 3 * Nat.card (S ⊓ L : Subgroup G) * (Nat.card (BlockN L) - 1) := by
    have h1 : Nat.card ((S ⊓ L).subgroupOf L) * ((S ⊓ L).subgroupOf L).index = Nat.card ↥L :=
      Subgroup.card_mul_index _
    have h2 : Nat.card ((S ⊓ L).subgroupOf L) = Nat.card (S ⊓ L : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hB.2.1
    have hmodd : ((S ⊓ L).subgroupOf L).index % 2 = 1 := Nat.two_dvd_ne_zero.mp hB.2.2
    have hm : ((S ⊓ L).subgroupOf L).index = o := by
      apply s151u_odd_part (b := b) (c := q + e) hmodd ho
      rw [← hb, ← h2, h1, hLcard]
      ring
    rw [← h1, h2, hm, hN3]
    ring
  intro a b ha hb haL hasq hacomm hbL hbsq hbcomm
  have hnt := s151u_nontrivial_action hsh (s151u_hrank (L := L) hbig)
  obtain ⟨ua, hua, hconja, hfixa⟩ := s151u_block_inner hsh hperf hq hnt hB (hSN ha)
    (fun s hs => hacomm s hs.1)
  obtain ⟨ub, hub, hconjb, hfixb⟩ := s151u_block_inner hsh hperf hq hnt hB (hSN hb)
    (fun s hs => hbcomm s hs.1)
  have hZcomm : ∀ z ∈ blockZ L, ∀ l ∈ L, z * l = l * z := fun z hz l hl => by
    have := s151v_blockZ_comm hz hl
    calc z * l = (l * z * l⁻¹) * l := by rw [this]
      _ = l * z := by group
  have hnotZ : ∀ c u : G, c ∉ Subgroup.centralizer (L : Set G) → (∀ l ∈ L, c * l * c⁻¹ = u * l * u⁻¹) →
      u ∉ blockZ L := by
    intro c u hc hconj hz
    apply hc
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hconj l hl
    have h2 : u * l * u⁻¹ = l := by rw [hZcomm u hz l hl]; group
    rw [h2] at h1
    calc l * c = (c * l * c⁻¹) * c := by rw [h1]
      _ = c * l := by group
  have huaZ := hnotZ a ua haL hconja
  have hubZ := hnotZ b ub hbL hconjb
  have hz := s151u_fix_le_two hsh hB hN hmax3 hcard hbig ua hua ub hub huaZ hubZ hfixa hfixb
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hUL : blockU L ≤ L := s151v_blockU_le_L hsh
  have key : ∀ m ∈ L, a⁻¹ * m * a = ua⁻¹ * m * ua := by
    intro m hm
    have hl' : ua⁻¹ * m * ua ∈ L := L.mul_mem (L.mul_mem (L.inv_mem (hUL hua)) hm) (hUL hua)
    have h3 : a * (ua⁻¹ * m * ua) * a⁻¹ = m := by rw [hconja _ hl']; group
    calc a⁻¹ * m * a = a⁻¹ * (a * (ua⁻¹ * m * ua) * a⁻¹) * a := by rw [h3]
      _ = ua⁻¹ * m * ua := by group
  have hbl : b * l * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hSN hb) l).mp hl
  have hzL : ua⁻¹ * ub ∈ blockZ L := hz
  have hconj_eq : (a⁻¹ * b) * l * (a⁻¹ * b)⁻¹ = l := by
    calc (a⁻¹ * b) * l * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * l * b⁻¹) * a := by group
      _ = ua⁻¹ * (b * l * b⁻¹) * ua := key _ hbl
      _ = ua⁻¹ * (ub * l * ub⁻¹) * ua := by rw [hconjb l hl]
      _ = (ua⁻¹ * ub) * l * (ua⁻¹ * ub)⁻¹ := by group
      _ = l := by rw [hZcomm _ hzL l hl]; group
  calc l * (a⁻¹ * b) = ((a⁻¹ * b) * l * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by rw [hconj_eq]
    _ = (a⁻¹ * b) * l := by group

theorem s151u_card_L [Finite G] {L : Subgroup G} {c : ℕ} (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = c) :
    ∃ q : ℕ, Nat.card ↥L = 2 ^ q * c := by
  obtain ⟨q, hq⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  have h1 := Subgroup.card_mul_index (CFSG.pCore 2 ↥L)
  refine ⟨q, ?_⟩
  rw [← h1, hq]
  show 2 ^ q * Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ q * c
  rw [hc]

theorem s151u_quasisimple_of_card {L : Subgroup G} (hsh : IsShort2 L) {c : ℕ} (hc3 : c ≠ 3)
    (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = c) : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  rcases hsh.2.2.2.1 with h | h
  · exact h
  · exact absurd (hc ▸ h) hc3

theorem s151u_card_BlockN_L3 {L : Subgroup G} {e : ↥L →* SLt 3}
    {β : ↥(blockU L) →* Multiplicative (Vt 3)} (hs : LnStr L e β) : Nat.card (BlockN L) = 8 := by
  have h := Subgroup.index_ker β
  rw [hs.βker] at h
  have h2 : Nat.card β.range = Nat.card (Multiplicative (Vt 3)) := by
    rw [MonoidHom.range_eq_top.mpr hs.βsurj]
    exact Subgroup.card_top
  show ((blockZ L).subgroupOf (blockU L)).index = 8
  rw [h, h2]
  rw [Nat.card_eq_fintype_card]
  decide

theorem s151u_zl2_L3 [Finite G] {S L : Subgroup G} (h3 : IsLnBlock L 3) (hperf : ⁅L, L⁆ = L)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hB : IsSylowTwoOf (S ⊓ L) L)
    (hN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L)
    (hmax3 : ∀ H : Subgroup G, IsMaxSubgroupIn L H → S ⊓ L ≤ H →
      Nat.card H = 3 * Nat.card (S ⊓ L : Subgroup G)) : ZL2 S L := by
  obtain ⟨e, β, hs⟩ := exists_lnStr h3
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
    rw [card_quot_pCore_of_surjective e hs.surj hs.ker, card_SLt_three]
  obtain ⟨q, hq⟩ := s151u_card_L hc
  have hn := s151u_card_BlockN_L3 hs
  exact s151u_zl2_of_numerics (e := 3) (q := q) (o := 21) h3.1 hperf
    (s151u_quasisimple_of_card h3.1 (by norm_num) hc) hSN hB hN hmax3 (by norm_num)
    (by rw [hq]; norm_num) (by rw [hn]) (by rw [hn]; norm_num)

theorem s151u_zl2_A6 [Finite G] {S L : Subgroup G} (h6 : IsAltBlockType L 6) (hperf : ⁅L, L⁆ = L)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hB : IsSylowTwoOf (S ⊓ L) L)
    (hN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L)
    (hmax3 : ∀ H : Subgroup G, IsMaxSubgroupIn L H → S ⊓ L ≤ H →
      Nat.card H = 3 * Nat.card (S ⊓ L : Subgroup G)) : ZL2 S L := by
  obtain ⟨hsh, α, hα, hker, β, hβs, hβk, -⟩ := h6
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
    rw [card_quot_pCore_of_surjective α hα hker, card_alt 6 (by norm_num)]
    decide
  obtain ⟨q, hq⟩ := s151u_card_L hc
  have hn : Nat.card (BlockN L) = 16 := by
    have h := Subgroup.index_ker β
    rw [hβk] at h
    have h2 : Nat.card β.range = Nat.card (Multiplicative (AltHeart 6)) := by
      rw [MonoidHom.range_eq_top.mpr hβs]
      exact Subgroup.card_top
    show ((blockZ L).subgroupOf (blockU L)).index = 16
    rw [h, h2, Nat.card_congr (Multiplicative.toAdd : Multiplicative (AltHeart 6) ≃ AltHeart 6)]
    exact CFSG.Quasithin.H13.A6Coc.card_altHeart
  exact s151u_zl2_of_numerics (e := 3) (q := q) (o := 45) hsh hperf
    (s151u_quasisimple_of_card hsh (by norm_num) hc) hSN hB hN hmax3 (by norm_num)
    (by rw [hq]; norm_num) (by rw [hn]) (by rw [hn]; norm_num)

theorem s151u_zl2_G2 [Finite G] {S L : Subgroup G} (hg : IsG2Block L) (hperf : ⁅L, L⁆ = L)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hB : IsSylowTwoOf (S ⊓ L) L)
    (hN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L)
    (hmax3 : ∀ H : Subgroup G, IsMaxSubgroupIn L H → S ⊓ L ≤ H →
      Nat.card H = 3 * Nat.card (S ⊓ L : Subgroup G)) : ZL2 S L := by
  obtain ⟨hsh, hpsu, hidx, hnatural⟩ := hg
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 :=
    CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three hpsu
  obtain ⟨q, hq⟩ := s151u_card_L hc
  have hn : Nat.card (BlockN L) = 64 := hidx
  exact s151u_zl2_of_numerics (e := 5) (q := q) (o := 189) hsh hperf
    (s151u_quasisimple_of_card hsh (by norm_num) hc) hSN hB hN hmax3 (by norm_num)
    (by rw [hq]; norm_num) (by rw [hn]) (by rw [hn]; norm_num)

end CFSG.Quasithin
