module

public import CFSG.Quasithin.Vol2.Ch11SecFCase2
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp StatedSU)
open scoped Pointwise

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h
  have h6 : Nat.factorial 6 = 720 := by decide
  omega

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem lt_card_quot (hset : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n) :
    6048 < Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hk
  obtain ⟨e₀⟩ := hset.quot
  have hn : 2 ≤ n := hset.one_lt
  rw [Nat.card_congr (e₀.trans e).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h1 : 256 ≤ (2 ^ n) ^ (2 ^ 2) := by
    calc 256 = 4 ^ (2 ^ 2) := by norm_num
      _ ≤ (2 ^ n) ^ (2 ^ 2) := Nat.pow_le_pow_left h4 _
  have h2 : 16 ≤ (2 ^ n) ^ (2 * 1) := by
    calc 16 = 4 ^ (2 * 1) := by norm_num
      _ ≤ (2 ^ n) ^ (2 * 1) := Nat.pow_le_pow_left h4 _
  have h3 : 256 ≤ (2 ^ n) ^ (2 * 2) := by
    calc 256 = 4 ^ (2 * 2) := by norm_num
      _ ≤ (2 ^ n) ^ (2 * 2) := Nat.pow_le_pow_left h4 _
  have h2' : 15 ≤ (2 ^ n) ^ (2 * 1) - 1 := by omega
  have h3' : 255 ≤ (2 ^ n) ^ (2 * 2) - 1 := by omega
  calc 6048 < 256 * (15 * 255) := by norm_num
    _ ≤ (2 ^ n) ^ (2 ^ 2) * (((2 ^ n) ^ (2 * 1) - 1) * ((2 ^ n) ^ (2 * 2) - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2' h3')

theorem false_of_quot_SL3 (hset : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n)
    {m : ℕ} {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ m)
    (e₁ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 F)) : False := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hk
  obtain ⟨e₀⟩ := hset.quot
  have hn : 1 ≤ n := by have := hset.one_lt; omega
  have hc := (Nat.card_congr e₁.toEquiv).symm.trans (Nat.card_congr (e₀.trans e).toEquiv)
  rw [card_statedSL_three, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    Nat.card_eq_fintype_card (α := F), hF, hK] at hc
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at hc
  apply false_of_card_eq (m := m) hn
  rw [← pow_mul, ← pow_mul, ← pow_mul] at hc
  convert hc using 2 <;> ring_nf

theorem isSp4Block_of_isMSPair (h132 : ASInputs.AS_C_1_32) (hset : SecD.NatSetting11 G T L I n)
    (hk : KindSp4 L (fsuV T I) n) {G₀ R : Subgroup G} (hMS : IsMSPair G₀ R)
    (hL : L ∈ cComp G₀) (hcoe : (G₀ : Set G) = (L : Set G) * (R : Set G)) : IsSp4Block L := by
  have hlt := lt_card_quot hset hk
  rcases h132 G G₀ R L hMS hL hcoe with hb | hb | hb | hb | hb
  ·
    exfalso
    obtain ⟨-, ⟨-, K, _, _, hK, ⟨e⟩⟩, -⟩ := hb
    have h9 : Nat.card K = 9 := by simpa using hK
    have hc : Nat.card ↥(StatedSU 3 (3 ^ 1) K) = 6048 := by
      rw [pow_one]
      exact CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU h9
    have hd := Subgroup.card_quotient_dvd_card
      ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (3 ^ 1) K))
    rw [hc] at hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    rw [← Nat.card_congr e.toEquiv] at hle
    omega
  ·
    exfalso
    obtain ⟨-, α, hα, hker, -⟩ := hb
    have e₁ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e₁.toEquiv, card_alt_six] at hlt
    omega
  · exact hb
  ·
    exfalso
    obtain ⟨-, ⟨-, hZ, ⟨e⟩⟩, -⟩ := hb
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [Nat.card_congr e.toEquiv, card_alt_six, hZ] at hc
    omega
  ·
    obtain ⟨m, F, _, _, α, hF, hα, hker⟩ := hb
    exact (false_of_quot_SL3 hset hk hF ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα))).elim

end CFSG.Quasithin.Vol2.Ch11.SecF
