module

import CFSG.LocalAnalysis.ComponentClassification.FooteLitSmallCentGrp
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Iso
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Levi
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Max

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
open CFSG.Blueprint (LieModel)

theorem r95_u3_eq_centralizer_of_le {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    [IsSimpleGroup (SU (unitaryInvolution F p f) 3)] (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hCW : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) ≤ W)
    (hU : rootU hF ≤ W → W = ⊤) (hW : W ≠ ⊤) :
    W = Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) := by
  have hq2 := two_le_prime_pow_of_card hF
  have hC := centralizer_zSU hF hp2
  have hCW' : (embSU (unitaryInvolution F p f)).range ⊔ (tSU hF).range ≤ W := hC ▸ hCW
  have hLW : (embSU (unitaryInvolution F p f)).range ≤ W := le_sup_left.trans hCW'
  have hTW : (tSU hF).range ≤ W := le_sup_right.trans hCW'
  have hZW : zU hF ≤ W := (zU_le_range_embSU hF).trans hLW
  have hZB : zU hF ≤ bSU (unitaryInvolution F p f) := (zU_le_rootU hF).trans (rootU_le_bSU hF)
  have hSt : ∀ μ ∈ rootsOfUnity (p ^ f + 1) F, ∀ x ∈ W ⊓ rootU hF,
      tSU hF μ * x * (tSU hF μ)⁻¹ ∈ W ⊓ rootU hF := by
    intro μ _ x hx
    have ht : tSU hF μ ∈ W := hTW ⟨μ, rfl⟩
    exact ⟨W.mul_mem (W.mul_mem ht hx.1) (W.inv_mem ht), tSU_conj_mem_rootU hF μ hx.2⟩
  rcases eq_top_or_ca_eq_zero hF hq3 (inf_le_right : W ⊓ rootU hF ≤ rootU hF) hSt with h | h
  · exact absurd (hU (by rw [← h]; exact inf_le_left)) hW
  have hmod : (bSU (unitaryInvolution F p f)).relIndex W ≡ 1 [MOD Nat.card (zU hF)] :=
    relIndex_modEq_one hZW hZB fun ζ hζ hζ1 w _ hw => fix_B hF (zU_le_rootU hF hζ) hζ1 hw
  rw [card_zU hF hq3] at hmod
  have hn1 : (bSU (unitaryInvolution F p f)).relIndex W % p ^ f = 1 := by
    have := hmod
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt (by omega : 1 < p ^ f)] at this
  have hBc : Nat.card (W ⊓ bSU (unitaryInvolution F p f) : Subgroup _) =
      p ^ f * ((p ^ f) ^ 2 - 1) := by
    have hZT : zU hF ⊓ (tSU hF).range = ⊥ :=
      eq_bot_iff.2 ((inf_le_inf_right _ (zU_le_rootU hF)).trans (inf_rootU_range_tSU hF).le)
    have := card_mul_inf_eq (zU hF) (tSU hF).range (W ⊓ bSU (unitaryInvolution F p f))
      (le_inf hZW hZB) (le_inf hTW (range_tSU_le_bSU hF)) (fun b hb => by
        obtain ⟨μ, hμ⟩ := exists_mul_tSU hF hb.2
        have hbW : b * (tSU hF μ)⁻¹ ∈ W := W.mul_mem hb.1 (W.inv_mem (hTW ⟨μ, rfl⟩))
        exact ⟨b * (tSU hF μ)⁻¹, ⟨hμ, h _ ⟨hbW, hμ⟩⟩, tSU hF μ, ⟨μ, rfl⟩,
          (inv_mul_cancel_right b _).symm⟩)
    rwa [hZT, Subgroup.card_bot, mul_one, card_zU hF hq3, card_range_tSU hF] at this
  have hcard : (bSU (unitaryInvolution F p f)).relIndex W * (p ^ f * ((p ^ f) ^ 2 - 1)) =
      Nat.card W := by
    rw [← hBc, inf_comm]
    exact Subgroup.relIndex_mul_card _ _
  have hpos : 0 < p ^ f * ((p ^ f) ^ 2 - 1) := by
    have : 1 < (p ^ f) ^ 2 := by nlinarith
    exact Nat.mul_pos (by omega) (by omega)
  have hdvd2 : p ^ f + 1 ∣ (bSU (unitaryInvolution F p f)).relIndex W := by
    have h1 := Subgroup.card_dvd_of_le hCW
    rw [card_centralizer_zSU hF hp2, ← hcard] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hpos h1
  have hdvd3 : (bSU (unitaryInvolution F p f)).relIndex W ∣ (p ^ f) ^ 2 * ((p ^ f) ^ 3 + 1) := by
    have h1 := Subgroup.card_subgroup_dvd_card W
    rw [card_SU3 hF, ← hcard] at h1
    refine Nat.dvd_of_mul_dvd_mul_right hpos ?_
    have e : (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) =
        (p ^ f) ^ 2 * ((p ^ f) ^ 3 + 1) * (p ^ f * ((p ^ f) ^ 2 - 1)) := by ring
    rwa [e] at h1
  rcases eq_or_eq_of_modEq_one hq2 hn1 hdvd2 hdvd3 with hn | hn
  ·
    have hEq : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) = W := by
      refine Subgroup.eq_of_le_of_card_ge hCW ?_
      rw [card_centralizer_zSU hF hp2, ← hcard, hn]
    exact hEq.symm
  ·
    have hBpos : 0 < (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) := by
      have : 1 < (p ^ f) ^ 2 := by nlinarith
      exact Nat.mul_pos (pow_pos (by omega) 3) (by omega)
    have hidx : (bSU (unitaryInvolution F p f)).index = (p ^ f) ^ 3 + 1 := by
      have h1 := (bSU (unitaryInvolution F p f)).card_mul_index
      rw [card_SU3 hF, card_bSU hF] at h1
      exact Nat.eq_of_mul_eq_mul_left hBpos h1
    have hGWB := exists_mul_of_relIndex_eq (W := W) (hn.trans hidx.symm)
    have hcore : zU hF ≤ W.normalCore := by
      intro x hx g
      obtain ⟨w, hw, b, hb, rfl⟩ := hGWB g
      have e : w * b * x * (w * b)⁻¹ = w * (b * x * b⁻¹) * w⁻¹ := by group
      rw [e]
      exact W.mul_mem (W.mul_mem hw (hZW (conj_mem_zU hF hb hx))) (W.inv_mem hw)
    have hZbot : zU hF ≠ ⊥ := fun hbot => by
      have := card_zU hF hq3
      rw [hbot, Subgroup.card_bot] at this
      omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W.normalCore with hb | ht
    · exact absurd (eq_bot_iff.2 (hb ▸ hcore)) hZbot
    · exact absurd (eq_top_iff.2 (ht ▸ W.normalCore_le)) hW

theorem r95_u3_centralizer_le_of_not_isSolvable {F : Type} [Field F]
    [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1) (hq13 : 13 ≤ p ^ f) {ω : Fˣ}
    (hω : orderOf ω = 3)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hNW : normA0 hF ω ≤ W)
    (hns : ¬ Group.IsSolvable W) :
    Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) ≤ W := by
  have hTW : (tSU hF).range ≤ W := (range_tSU_le_normA0 hF hω hq3).trans hNW
  by_cases hbad : ∀ x ∈ W, x * zSU hF = zSU hF * x → x ∈ normA0 hF ω
  · exact absurd (isSolvable_of_centralizer_le hF hp2 hω hq3 hNW hbad) hns
  · push Not at hbad
    obtain ⟨x, hxW, hxz, hxN⟩ := hbad
    have hLW := range_embSU_le_of_not_bad hF hp2 hq3 hq13 hω hNW hxW hxz hxN
    rw [centralizer_zSU hF hp2]
    exact sup_le hLW hTW

theorem r95_psl2_seven_eq_top {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7)
    {H : Subgroup (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K)} (h6 : 6 ∣ Nat.card H)
    (h7 : 7 ∣ Nat.card H) : H = ⊤ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : IsSimpleGroup (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega : 4 ≤ Nat.card K)
  have hcard : Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K) = 168 := by
    rw [CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd (p := 7) (f := 1)
      (by simpa using hK) (by norm_num)]
    norm_num
  by_contra hne
  have hidx : 7 ≤ H.index :=
    CFSG.ComponentClassification.FooteLit.seven_le_index_of_card_eq_168 hcard hne
  have h42 : 42 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 6 7) h6 h7
  have hne0 : Nat.card H ≠ 0 := by
    intro h0
    have hmi := H.card_mul_index
    rw [h0, zero_mul, hcard] at hmi
    exact absurd hmi (by norm_num)
  have hle : 42 ≤ Nat.card H := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) h42
  have h1 : 42 * 7 ≤ Nat.card H * H.index := Nat.mul_le_mul hle hidx
  rw [H.card_mul_index, hcard] at h1
  norm_num at h1

theorem r95_u3_levi_le_of_psl_top {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {ζ : F} (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution F p f ζ = -ζ)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hTW : (tSU hF).range ≤ W)
    (htop : (W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) = ⊤) :
    (embSU (unitaryInvolution F p f)).range ≤ W := by
  have hF0 : Nat.card (fixedSubfield F p f) = p ^ f := card_fixedSubfield hF
  have hcount := card_inf_range_embSU_eq hζ0 hζ hF hp2 W hTW
  rw [htop, Subgroup.card_top, CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF0 hp2] at hcount
  have h2 : 2 ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
    obtain ⟨a, ha⟩ := odd_prime_pow (p := p) (f := f) hp2
    refine Dvd.dvd.mul_left ?_ _
    have h : (p ^ f) ^ 2 = 4 * a * (a + 1) + 1 := by rw [ha]; ring
    have : (p ^ f) ^ 2 - 1 = 4 * a * (a + 1) := by omega
    rw [this]
    exact ⟨2 * a * (a + 1), by ring⟩
  have hge : Nat.card (embSU (unitaryInvolution F p f)).range ≤
      Nat.card (W ⊓ (embSU (unitaryInvolution F p f)).range : Subgroup _) := by
    rw [hcount, card_range_embSU hF, Nat.mul_div_cancel' h2]
  have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right :
    W ⊓ (embSU (unitaryInvolution F p f)).range ≤ (embSU (unitaryInvolution F p f)).range) hge
  rw [← heq]
  exact inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
