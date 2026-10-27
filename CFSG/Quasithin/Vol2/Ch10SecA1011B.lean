module

public import CFSG.Quasithin.Vol2.Ch10SecAModels
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch10SecABasicCent
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inf_centralizer_le_pCoreOf (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) {W : Subgroup G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hne : ⁅W, L⁆ ≠ ⊥) :
    L ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 L := by
  intro y hy
  by_contra hyO
  have hs := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.faithful hyp.not_normal
  set D := L ⊓ Subgroup.centralizer (W : Set G)
  have hDL : D ≤ L := inf_le_left
  have hn : L ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx
    have hx' : x ∈ Subgroup.normalizer (L : Set G) ⊓
        Subgroup.normalizer (Subgroup.centralizer (W : Set G) : Set G) :=
      ⟨Subgroup.le_normalizer hx, le_normalizer_centralizer hLW hx⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf hx'
  have : (D.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr hn
  have hnorm := this.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  have htop : (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    refine (hs.eq_bot_or_eq_top_of_normal _).resolve_left fun hbot => hyO ?_
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨y, hy.1⟩) ∈
        (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      ⟨⟨y, hy.1⟩, hy, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, mk_eq_one_iff] at hmem
    exact hmem
  have hDeq : D = L := eq_of_forall_mul_mem_pCoreOf hyp.fsu.faithful hDL hn fun x hx => by
    have hx' : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx⟩) ∈
        (D.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨d, hd, hdx⟩ := hx'
    refine ⟨d, hd, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← subgroupOf_pCoreOf,
      Subgroup.mem_subgroupOf] at hdx
    simpa using hdx
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  intro x hx
  rw [← hDeq] at hx
  exact hx.2

omit [Finite G] in
theorem card_autOn_eq_index {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card ↥(autOn L W) = ((L ⊓ Subgroup.centralizer (W : Set G)).subgroupOf L).index :=
  CFSG.Quasithin.AutOn.card_autOn_eq_relIndex hLW

omit [Finite G] in
theorem card_quot_dvd_card_autOn {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hC : L ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ Nat.card ↥(autOn L W) := by
  rw [card_autOn_eq_index hLW, ← Subgroup.index, ← subgroupOf_pCoreOf]
  exact Subgroup.index_dvd_of_le (Subgroup.subgroupOf_mono L hC)

omit [Finite G] in
theorem card_SL_two (K : Type) [Field K] [Fintype K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Fintype.card K * (Fintype.card K ^ 2 - 1) :=
  (Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv).trans
    (card_statedSL_two K)

omit [Finite G] in
theorem lBarL32_of_shape_dvd {L : Subgroup G} (hsh : Shape701 L)
    (hdvd : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ 168) : LBarL32 L := by
  rcases hsh with ⟨n, hn, K, _, _, hK, ⟨e⟩⟩ | ⟨f, -, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ | h
  · exfalso
    have := Fintype.ofFinite K
    have hK' : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hK]
    rw [Nat.card_congr e.toEquiv, card_SL_two, hK'] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      norm_num at hdvd
    · have h8 : 8 ≤ 2 ^ n := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
      have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by omega
      nlinarith
  · exfalso
    rw [hf] at hK
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h7 : 7 ≤ 2 ^ (2 * a + 1) - 1 := by omega
    have h64 : 64 ≤ (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
    have h65 : 65 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h64 h7) h65
    omega
  · exact h

end CFSG.Quasithin.Vol2.Ch10.SecA
