module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKInputs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcSchur
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotMap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKQuotFix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_u43 (h : S16gRowCtx D V₀ V L hV) (hU43 : S16kU43Noncyclic3)
    (hirr : commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L))
    (hS : ∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧
      IsHat ↥(lBar V₀ V hV L) S)
    (hm : E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) = 12) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 : 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := h.three_le_pRank hpσ
  obtain ⟨S, hGrp, hLie, hHat⟩ := hS
  letI := hGrp
  by_cases hp3 : p = 3
  ·
    obtain ⟨Q, hQc, hQf, q, ρ, hqs, hqk, hρ, heq, hexp, hcard, hirrMap⟩ :=
      s16k_exists_quot_map (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) h
    have hcard12 : Nat.card Q = 2 ^ 12 := by rw [hcard, hm]
    haveI : Nontrivial Q := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcard12]
      norm_num
    have hrk12 : rk ↥(⊤ : Subgroup Q) = 12 := by
      rw [CFSG.Quasithin.rk_top]
      unfold CFSG.Quasithin.rk
      rw [hcard12, padicValNat.prime_pow]
    have hSrange : ∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧
        IsHat ↥(ρ.range) S :=
      ⟨S, hGrp, hLie, IsHat.of_mulEquiv (MonoidHom.ofInjective hρ) hHat⟩
    have hIrrRange : IsIrrOn (ρ.range) ⊤ ⊥ := by
      refine ⟨bot_lt_top, ?_, ?_, ?_⟩
      · intro x hx u hu
        exact Subgroup.mem_top u
      · intro x hx u hu
        rw [Subgroup.mem_bot] at hu ⊢
        rw [hu, map_one]
      · intro J hJ _ _
        exact hirrMap hirr J (fun l b hb => hJ (ρ l) ⟨l, rfl⟩ b hb)
    have hfix3 : ∀ w : Q, w ≠ 1 → ∃ B : Subgroup (MulAut Q), B ≤ ρ.range ∧ IsPGroup 3 B ∧
        ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b w = w :=
      s16k_u43_noncyclic3 hU43 hexp hSrange hrk12 hIrrRange
    have hfixp : ∀ w : Q, w ≠ 1 → ∃ B : Subgroup (MulAut Q), B ≤ ρ.range ∧ IsPGroup p B ∧
        ¬ IsCyclic ↥B ∧ ∀ b ∈ B, b w = w := by
      intro w hw
      obtain ⟨B, hB, hBp, hBc, hBfix⟩ := hfix3 w hw
      refine ⟨B, hB, ?_, hBc, hBfix⟩
      rw [hp3]
      exact hBp
    have hne : ∃ w : Q, w ≠ 1 := exists_ne (1 : Q)
    have hfixV := s16k_transport_fix_nc_quot (Q := Q) hp hp2
      (barSub_mono V₀ V hV h.setting.hyp151.le) hqs hqk hρ heq hne hfixp
    exact s16g_false_of_fix D h.std h.setting hp hpσ hfixV
  ·
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    obtain ⟨Q, hQc, hQf, L', N, hexp, hcard, ⟨eL⟩, hirrImp, hnorm, hrank, -⟩ :=
      s16k_exists_quot_data (D := D) (V₀ := V₀) (V := V) (L := L) (hV := hV) h
    have hcard12 : Nat.card Q = 2 ^ 12 := by rw [hcard, hm]
    have hirrQ : ∀ B : Subgroup Q, (∀ l ∈ L', ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤ :=
      hirrImp hirr
    have hcentC : CFSG.Open.pRank p (Subgroup.centralizer (L' : Set (MulAut Q))) ≤ 1 := by
      have hc := s16k_pRank_centralizer_le (Q := Q) hexp hirrQ hcard12 hp hp2
      by_cases hd : orderOf (2 : ZMod p) ∣ 12
      · rw [if_pos hd] at hc
        exact hc
      · rw [if_neg hd] at hc
        omega
    have hcent : CFSG.Open.pRank p
        (N ⊓ Subgroup.centralizer (L' : Set (MulAut Q))) ≤ 1 :=
      (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right).trans hcentC
    have haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥L')) ≤ 1 :=
      s16k_pRank_aut_u43 hLie (IsHat.of_mulEquiv eL hHat) hp hp5
    have hN : CFSG.Open.pRank p N ≤ 2 := by
      have h1 := s16k_pRank_le_of_normalizer (Q := Q) hnorm hp
      omega
    have hM : CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ 2 := (hrank p hp).trans hN
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
