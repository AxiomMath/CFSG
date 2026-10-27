module

public import CFSG.Quasithin.Vol2.Ch8Sec2InspDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Direct
import CFSG.Quasithin.Vol2.Ch4Sec3L4314Row
import CFSG.Quasithin.EmptyFaithful.S146zXGOrder
import CFSG.Quasithin.Background.GoldschmidtS146RArith
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main

public section

namespace CFSG.Quasithin.H13.Insp82

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.A5.G3

theorem false_of_sl2_mul {p k n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : Odd k)
    (hn : n = 960 ∨ n = 11520 ∨ n = 17280 ∨ n = 23040 ∨ n = 34560)
    (h : p * (p ^ 2 - 1) * k = n) : False := by
  obtain ⟨j, rfl⟩ := hk
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hle : p * (p ^ 2 - 1) ≤ 34560 := by
    have : p * (p ^ 2 - 1) ≤ p * (p ^ 2 - 1) * (2 * j + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hp27 : p < 34 := by
    by_contra hlt
    have h1 : 34 ≤ p := by omega
    have h2 : 1155 ≤ p ^ 2 - 1 := by
      have : 1156 ≤ p ^ 2 := by nlinarith
      omega
    have : 34 * 1155 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul h1 h2
    omega
  interval_cases p <;> norm_num at h <;> omega

theorem false_of_psl2_two {n m : ℕ} (hn : 1 ≤ n) (hm : m = 360 ∨ m = 1080)
    (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) = m) : False := by
  have hn4 : n < 4 := by
    by_contra hlt
    have h1 : 16 ≤ 2 ^ n := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 255 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 256 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    have : 16 * 255 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h1 h2
    omega
  interval_cases n <;> norm_num at h <;> omega

section Orders

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_card_of_isExt {X : Type} [Group X] {PV PY : ∀ (V : Type) [Group V], Prop}
    (h : IsExt X PV PY) : ∃ (V : Subgroup X) (_ : V.Normal), PV ↥V ∧ PY (X ⧸ V) ∧
      Nat.card X = Nat.card (X ⧸ V) * Nat.card ↥V := by
  obtain ⟨V, hV, hPV, hPY⟩ := h
  exact ⟨V, hV, hPV, hPY, V.card_eq_card_quotient_mul_card_subgroup⟩

omit [Finite Q] in
theorem card_eq_modO2_mul (B : Subgroup Q) :
    Nat.card ↥B = Nat.card (ModO2 B) * Nat.card ↥(CFSG.pCore 2 ↥B) :=
  (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup

theorem pCore_two_eq_bot_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : CFSG.pCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have hp : IsPGroup 2 X := by
      have h2 := (CFSG.pCore_isPGroup (p := 2) (G := X))
      rw [h] at h2
      exact h2.of_equiv Subgroup.topEquiv
    have hnil : Group.IsNilpotent X := hp.isNilpotent
    have hsolv : Group.IsSolvable X := inferInstance
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem pCore_two_eq_bot_of_mem_cComp {Y : Type} [Group Y] (hY : SQTKHypCat Y)
    {L : Subgroup Y} (hL : L ∈ cComp (⊤ : Subgroup Y)) : CFSG.pCore 2 ↥L = ⊥ :=
  have := hY.finite
  hY.pCore_two_of_subnormal (subnormal_of_mem_cComp hL)

theorem card_of_a312Nonquasi {B L : Subgroup Q} (hBL : B ≤ L) (h : A312Nonquasi B L) :
    (∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd k ∧ Nat.card ↥B = p * (p ^ 2 - 1) * k) ∨
      ∃ k : ℕ, Odd k ∧ Nat.card ↥B = 120 * k := by
  set OL : Subgroup Q := (CFSG.oddCore ↥L).map L.subtype with hOL
  have hsub : OL.subgroupOf L = CFSG.oddCore ↥L :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hLO : L ≤ Subgroup.normalizer (OL : Set Q) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
    rw [hsub]
    infer_instance
  have hBO : B ≤ Subgroup.normalizer (OL : Set Q) := hBL.trans hLO
  have : (OL.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBO
  set V := OL.subgroupOf B with hV
  have hVodd : Odd (Nat.card V) := by
    have h1 : Nat.card V = Nat.card ↥(OL ⊓ B) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective B.subtype_injective]
    have h2 : Nat.card ↥(OL ⊓ B) ∣ Nat.card OL := Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card OL = Nat.card (CFSG.oddCore ↥L) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [h1]
    exact (h3 ▸ A312.odd_card_oddCore ↥L).of_dvd_nat h2
  have : (OL.subgroupOf (B ⊔ OL)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBO
  have hφ : Nat.card (↥B ⧸ V) = (OL.subgroupOf (B ⊔ OL)).index :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient B OL hBO).toEquiv
  have hB : Nat.card ↥B = Nat.card (↥B ⧸ V) * Nat.card V :=
    V.card_eq_card_quotient_mul_card_subgroup
  unfold A312Nonquasi at h
  dsimp only at h
  rcases h with ⟨-, hLB, p, hp, hp2, hSL⟩ | ⟨-, -, N, hN, rfl, hSL⟩
  · left
    refine ⟨p, Nat.card V, hp, hp2, hVodd, ?_⟩
    rw [hB, hφ, ← hLB, hsub, Subgroup.index, A313.IsSL2.card_eq hp hSL]
  · right
    refine ⟨Nat.card V, hVodd, ?_⟩
    rw [hB, hφ, Subgroup.index, A313.IsSL2.card_eq (by norm_num) hSL]
    norm_num

theorem false_of_a312Nonquasi {B L : Subgroup Q} (hBL : B ≤ L) (h : A312Nonquasi B L)
    (hc : Nat.card ↥B = 960 ∨ Nat.card ↥B = 11520 ∨ Nat.card ↥B = 17280) : False := by
  rcases card_of_a312Nonquasi hBL h with ⟨p, k, hp, hp2, hk, hcard⟩ | ⟨k, ⟨j, rfl⟩, hcard⟩
  · rw [hcard] at hc
    exact false_of_sl2_mul hp hp2 hk (by omega) rfl
  · omega

end Orders

theorem inspL34_of (h312 : A312ForSQTKCat) (hM : A314ModelFacts) (hR : Delta5Rows) :
    InspL34 := by
  intro Y _ hY T hT B hB hTB hD
  have := hY.finite
  obtain ⟨L, hL, hBL, -, hcase⟩ := h312 Y hY T hT B hB
  rcases hcase with rfl | hc | hc
  · have h1 := hD.card_pCore
    rw [pCore_two_eq_bot_of_mem_cComp hY hL, Subgroup.card_bot] at h1
    omega
  · have hTL' : IsSylowTwoOf (T ⊓ L) L :=
      L246C127.isSylowTwoOf_inf_of_isSubnormal' (subnormal_of_mem_cComp hL) hT
    exact not_a312Case_of_delta5 hM hR hD hTL' hBL (inf_le_left.trans hTB) hc
  · exact false_of_a312Nonquasi hBL hc (Or.inl hD.card)

section Code22

variable {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q}

theorem not_a312Case_of_code22 (hM : A314ModelFacts) (hmod : Nat.card (ModO2 B) = 360)
    (hO : Nat.card ↥(CFSG.pCore 2 ↥B) = 2 ^ 5) (hcase : A312Case B L) : False := by
  have hcard : Nat.card ↥B = 11520 := by
    rw [card_eq_modO2_mul, hmod, hO]
    norm_num
  have hnotS : IsSimpleGroup ↥B → (∃ a b : ↥B, a * b ≠ b * a) → False := by
    intro _ hnc
    have h1 := pCore_two_eq_bot_of_simple hnc
    rw [h1, Subgroup.card_bot] at hO
    norm_num at hO
  unfold A312Case at hcase
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨⟨n, hn⟩, -⟩ := h
    have h1 := GoldS146R.card_isPSL_two_two hn
    exact false_of_psl2_two hn.1.2.1 (Or.inl rfl) (h1.symm.trans hmod)
  ·
    obtain ⟨f, hf, -⟩ := h
    have h1 := S146zX.not_three_dvd_card_isSz hf
    rw [hmod] at h1
    exact h1 (by norm_num)
  ·
    have h1 := Ch4.L4314Row.card_L32 h.1
    omega
  ·
    have h1 := Ch4.L4314Row.card_L42 h.1
    omega
  ·
    rcases h.1 with h1 | h1
    · have := Ch4.L4314Row.card_alt5 h1
      omega
    · have := Ch4.L4314Row.card_L32 h1
      omega
  ·
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := Ch4.L4314Row.card_alt6 h1
      omega
    · have := Ch4.L4314Row.card_hat6 h1
      omega
  ·
    rcases h with ⟨p, hp, hp3, h1, -⟩ | ⟨h1, -⟩
    · have h2 := Ch4.L4314Row.two_mul_card_of_isPSL_two hp (by omega) h1
      rw [hcard] at h2
      exact false_of_sl2_mul hp (by omega) odd_one (n := 23040) (by omega) (by omega)
    · have := Ch4.L4314Row.card_alt5 h1
      omega
  ·
    rcases h with ⟨s, p, hp, hp3, h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · have h2 := A313.IsSL2.card_eq hp h1
      exact false_of_sl2_mul hp (by omega) odd_one (n := 11520) (by omega)
        (by rw [mul_one, ← h2, hcard])
    · have := Ch4.L4314Row.card_alt6 h1
      omega
    · have := Ch4.L4314Row.card_hat6 h1
      omega
  ·
    obtain ⟨p, hp, hp3, hext, -⟩ := h
    obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt hext
    rw [card_of_isElemAbelianOfRank hV, A313.IsSL2.card_eq hp hYq, hcard] at hc
    have hp5 : 5 ≤ p := by
      rcases (by omega : p = 4 ∨ 5 ≤ p) with rfl | h5
      · norm_num at hp
      · exact h5
    have h6 : p < 7 := by
      by_contra h7
      have h7' : 7 ≤ p := by omega
      have : 48 ≤ p ^ 2 - 1 := by
        have : 49 ≤ p ^ 2 := by nlinarith
        omega
      have : 7 * 48 * 49 ≤ p * (p ^ 2 - 1) * p ^ 2 := by
        have h1 : 7 * 48 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul h7' this
        have h2 : 49 ≤ p ^ 2 := by nlinarith
        exact Nat.mul_le_mul h1 h2
      omega
    interval_cases p <;> norm_num at hc
  ·
    have := Ch4.L4314Row.card_alt6 h.1
    omega
  ·
    rcases h with ⟨h1 | h1, -⟩ | ⟨h1 | h1, -⟩
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt5 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt6 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt5 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_hat6 hYq] at hc
      omega
  ·
    obtain ⟨h1 | h1 | h1 | h1 | h1 | h1 | h1, -⟩ := h
    · obtain ⟨hs, hnc, -⟩ := hM.1 ↥B (Or.inr (Or.inr (Or.inr (Or.inl h1))))
      exact hnotS hs hnc
    · obtain ⟨hs, hnc, -⟩ := hM.1 ↥B (Or.inr (Or.inr (Or.inl h1)))
      exact hnotS hs hnc
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt7 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt6 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_alt5 hYq] at hc
      omega
  ·
    obtain ⟨h1 | h1 | h1 | h1, -⟩ := h
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_L42 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [hV.2, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_hat6 hYq] at hc
      omega
  ·
    have := Ch4.L4314Row.card_alt5 h.1
    omega
  ·
    obtain ⟨h1, -⟩ := h
    obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
    rw [hV.2, Ch4.L4314Row.card_alt5 hYq] at hc
    omega
  ·
    obtain ⟨-, h1 | h1 | h1 | h1 | h1 | h1⟩ := h
    · obtain ⟨V, _, hV, -, -⟩ := exists_card_of_isExt h1
      have h2 : Nat.card ↥V ∣ Nat.card ↥B := Subgroup.card_subgroup_dvd_card V
      rw [hV.2, hcard] at h2
      norm_num at h2
    · obtain ⟨V, _, hV, -, -⟩ := exists_card_of_isExt h1
      have h2 : Nat.card ↥V ∣ Nat.card ↥B := Subgroup.card_subgroup_dvd_card V
      rw [Ch4.L4314Row.card_isE2 hV, hcard] at h2
      norm_num at h2
    · have := Ch4.L4314Row.card_alt5 h1
      omega
    · have := Ch4.L4314Row.card_hat6 h1
      omega
    · have := Ch4.L4314Row.card_L42 h1
      omega
    · have := Ch4.L4314Row.card_L32 h1
      omega
  ·
    obtain ⟨h1 | h1, -⟩ := h
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      obtain ⟨k, hk⟩ := Ch4.L4314Row.card_isZ4StarExtra2 hV
      rw [hk, Ch4.L4314Row.card_alt5 hYq, hcard] at hc
      have h2 : 2 ^ 2 * 15 * 2 ^ k = 2 ^ (k + 2) * 15 := by ring
      have h3 : (11520 : ℕ) = 2 ^ 8 * 45 := by norm_num
      rw [h2, h3] at hc
      have := Ch4.L4314Row.eq_of_two_pow_mul_eq (by decide) (by decide) hc.symm
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isZ4Cubed hV, Ch4.L4314Row.card_L32 hYq] at hc
      omega
  ·
    obtain ⟨h1 | h1, -⟩ := h
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [hV.2, Ch4.L4314Row.card_L32 hYq] at hc
      omega
    · obtain ⟨V, _, hV, hYq, hc⟩ := exists_card_of_isExt h1
      rw [Ch4.L4314Row.card_isE2 hV, Ch4.L4314Row.card_hat6 hYq] at hc
      omega
  ·
    obtain ⟨-, h1, -⟩ := h
    omega

theorem inspCode22_of (h312 : A312ForSQTKCat) (hM : A314ModelFacts) : InspCode22 := by
  intro Y _ hY T hT B hB hmod hO
  have := hY.finite
  obtain ⟨L, hL, hBL, -, hcase⟩ := h312 Y hY T hT B hB
  rcases hcase with rfl | hc | hc
  · rw [pCore_two_eq_bot_of_mem_cComp hY hL, Subgroup.card_bot] at hO
    norm_num at hO
  · exact not_a312Case_of_code22 hM hmod hO hc
  · refine false_of_a312Nonquasi hBL hc (Or.inr (Or.inl ?_))
    rw [card_eq_modO2_mul, hmod, hO]
    norm_num

end Code22

end CFSG.Quasithin.H13.Insp82
