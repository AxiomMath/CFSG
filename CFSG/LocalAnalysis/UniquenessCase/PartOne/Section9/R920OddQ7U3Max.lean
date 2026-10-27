module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Block
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Count
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3

theorem card_centralizer_aux {q C : ℕ} (hq : 2 ≤ q)
    (h : C * (q - 1) = q * (q ^ 2 - 1) * (q ^ 2 - 1)) : C = (q + 1) * (q * (q ^ 2 - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hr : 0 < r := by omega
  have e : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    have : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
    omega
  rw [e, Nat.add_sub_cancel] at h
  rw [e]
  refine Nat.eq_of_mul_eq_mul_right hr ?_
  rw [h]
  ring

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)
include hF

theorem card_centralizer_zSU (hp2 : p ≠ 2) :
    Nat.card (Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))) =
      (p ^ f + 1) * (p ^ f * ((p ^ f) ^ 2 - 1)) := by
  have h := card_inf_centralizer_zSU hF hp2 ⊤ le_top
  rw [top_inf_eq, top_inf_eq, card_inf_range_embSU_range_tSU hF, card_range_embSU hF,
    card_range_tSU hF] at h
  exact card_centralizer_aux (two_le_prime_pow_of_card hF) h

theorem eq_top_of_centralizer_le [IsSimpleGroup (SU (unitaryInvolution F p f) 3)] (hp2 : p ≠ 2)
    (hq3 : p ^ f % 3 = 1) (h7 : (7 : F) ≠ 0) {W : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hCW : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) ≤ W)
    (hU : rootU hF ≤ W → W = ⊤) {a d : SU (unitaryInvolution F p f) 3} (haW : a ∈ W)
    (hdW : d ∈ W) (ha7 : a ^ 7 = 1) (ha1 : a ≠ 1) (hda : d * a * d⁻¹ = a ^ 2) : W = ⊤ := by
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
  · exact hU (by rw [← h]; exact inf_le_left)
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
    exfalso
    have hEq : Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) = W := by
      refine Subgroup.eq_of_le_of_card_ge hCW ?_
      rw [card_centralizer_zSU hF hp2, ← hcard, hn]
    rw [← hEq] at haW hdW
    exact false_of_commute_zSU hF hp2 h7 (Subgroup.mem_centralizer_singleton_iff.1 haW)
      (Subgroup.mem_centralizer_singleton_iff.1 hdW) ha7 ha1 hda
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
    · exact eq_top_iff.2 (ht ▸ W.normalCore_le)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
