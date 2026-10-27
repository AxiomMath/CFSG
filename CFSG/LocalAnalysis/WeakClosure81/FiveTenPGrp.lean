module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenWeak
public import CFSG.LocalAnalysis.WeakClosure81.FiveNorm

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem b5_FiveTenPGrp_aux (n : ℕ) :
    ∀ {H W U : Subgroup G} {Ω : Set (Subgroup G)}, Nat.card W = n → E1.IsInvColl H Ω →
      W ≤ H → IsPGroup 2 W → E1.weakClosure W Ω = W → U < W → E1.weakClosure U Ω = U →
      ∃ B ∈ Ω, B ≤ W ∧ B ≤ normalizer (U : Set G) ∧ ¬ B ≤ U := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H W U Ω hcard hΩ hWH hW hWΩ hUW hU
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set R : Subgroup G := ⨆ w ∈ W, A1b.conjSub w U with hR
    have hconjW : ∀ w ∈ W, A1b.conjSub w U ≤ W := by
      intro w hw x hx
      rw [A1b.mem_conjSub_iff] at hx
      have h1 : w⁻¹ * x * w ∈ W := hUW.le (hx)
      have h2 : w * (w⁻¹ * x * w) * w⁻¹ ∈ W := W.mul_mem (W.mul_mem hw h1) (W.inv_mem hw)
      simpa [mul_assoc] using h2
    have hUR : U ≤ R := le_iSup₂_of_le (1 : G) W.one_mem (by rw [A1b.conjSub_one])
    have hRW : R ≤ W := iSup₂_le fun w hw => hconjW w hw
    have hRcl : E1.weakClosure R Ω = R := by
      refine le_antisymm E1.weakClosure_le ?_
      refine iSup₂_le fun w hw => ?_
      have h1 : A1b.conjSub w U = E1.weakClosure (A1b.conjSub w U) Ω := by
        rw [← conjSub_weakClosure hΩ (hWH hw) U, hU]
      rw [h1]
      exact weakClosure_mono Ω (le_iSup₂_of_le w hw le_rfl)
    have hRlt : R < W := by
      obtain ⟨Mx, hMx, hUMx⟩ := exists_isMaxSubgroupIn hUW
      have hne : Mx ≠ W := hMx.1.ne
      have hlt := lt_inf_normalizer_of_isPGroup hW hMx.1.le hne
      have hWn : W ≤ normalizer (Mx : Set G) := by
        have := hMx.2 (W ⊓ normalizer (Mx : Set G)) hlt inf_le_left
        rw [← this]
        exact inf_le_right
      have hRMx : R ≤ Mx := by
        refine iSup₂_le fun w hw x hx => ?_
        have h1 : A1b.conjSub w Mx = Mx := B6.conjSub_eq_self (hWn hw)
        rw [← h1]
        exact A1b.conjSub_mono w hUMx hx
      exact lt_of_le_of_lt hRMx hMx.1
    rcases eq_or_lt_of_le hUR with hRU | hUR'
    ·
      have hWU : ∀ w ∈ W, w ∈ normalizer (U : Set G) := by
        intro w hw
        apply E1.mem_normalizer_of_conj_mem
        intro x hx
        have : w * x * w⁻¹ ∈ A1b.conjSub w U := A1b.mem_conjSub_of_mem hx
        rw [hRU]
        exact (le_iSup₂_of_le w hw le_rfl : A1b.conjSub w U ≤ R) this
      have hex : ∃ B ∈ Ω, B ≤ W ∧ ¬ B ≤ U := by
        by_contra hcon
        have hall : ∀ B ∈ Ω, B ≤ W → B ≤ U := fun B hB hBW => by
          by_contra hBU
          exact hcon ⟨B, hB, hBW, hBU⟩
        have hle : E1.weakClosure W Ω ≤ U :=
          iSup₂_le fun B hB => iSup_le fun hBW => hall B hB hBW
        rw [hWΩ] at hle
        exact lt_irrefl W (lt_of_le_of_lt hle hUW)
      obtain ⟨B, hBΩ, hBW, hBU⟩ := hex
      exact ⟨B, hBΩ, hBW, fun b hb => hWU b (hBW hb), hBU⟩
    · have hcardlt : Nat.card R < n := by
        rw [← hcard]
        exact Subgroup.card_lt_of_lt hRlt
      obtain ⟨B, hBΩ, hBR, hBN, hBU⟩ := ih (Nat.card R) hcardlt (H := H) (W := R) (U := U)
        (Ω := Ω) rfl hΩ (hRW.trans hWH) (hW.to_le hRW) hRcl hUR' hU
      exact ⟨B, hBΩ, hBR.trans hRW, hBN, hBU⟩

theorem exists_mem_le_normalizer_of_lt {H W U : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hWH : W ≤ H) (hW : IsPGroup 2 W)
    (hWΩ : E1.weakClosure W Ω = W) (hUW : U < W) (hU : E1.weakClosure U Ω = U) :
    ∃ B ∈ Ω, B ≤ W ∧ B ≤ normalizer (U : Set G) ∧ ¬ B ≤ U :=
  b5_FiveTenPGrp_aux (Nat.card W) rfl hΩ hWH hW hWΩ hUW hU

end CFSG.LocalAnalysis.WeakClosure81
