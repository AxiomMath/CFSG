module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem GT_eq_pCoreOf_sup_K {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.GT = pCoreOf 2 t.GT ⊔ t.K := by
  have hKG : t.K ≤ t.GT := by
    refine le_iInf fun i => ?_
    have h := t.K_le_Gw i i
    rwa [show t.Gw i i = t.Gv i from win_self i] at h
  have hGTle : t.GT ≤ t.Gw 0 1 := by
    refine le_iInf fun i => le_iInf fun _ => ?_
    exact iInf_le (fun j => t.Gv j) i
  have hGw : t.Gw 0 1 = pCoreOf 2 (t.Gw 0 1) ⊔ t.K :=
    t.Gw_eq_sup hfr (u := 0) (w := 1) (by norm_num)
  have hKN : t.K ≤ normalizer (pCoreOf 2 (t.Gw 0 1) : Set G) :=
    (t.K_le_Gw 0 1).trans (le_normalizer_pCoreOf 2 (t.Gw 0 1))
  have hGT_eq : t.GT = (t.GT ⊓ pCoreOf 2 (t.Gw 0 1)) ⊔ t.K := by
    refine le_antisymm (fun x hx => ?_) (sup_le inf_le_left hKG)
    have hxGw : x ∈ t.Gw 0 1 := hGTle hx
    rw [hGw] at hxGw
    obtain ⟨s, hs, k, hk, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hKN).mp hxGw
    have hsGT : s ∈ t.GT := by
      have h := t.GT.mul_mem hx (t.GT.inv_mem (hKG hk))
      simpa only [mul_inv_cancel_right] using h
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hsGT, hs⟩) hk
  refine le_antisymm ?_ (sup_le (pCoreOf_le 2 t.GT) hKG)
  calc t.GT = (t.GT ⊓ pCoreOf 2 (t.Gw 0 1)) ⊔ t.K := hGT_eq
    _ ≤ pCoreOf 2 t.GT ⊔ t.K :=
      sup_le_sup_right ((le_of_eq (inf_comm _ _)).trans (F7.pCoreOf_inf_le hGTle)) t.K

theorem pCoreOf_GT_inf_K : pCoreOf 2 t.GT ⊓ t.K = ⊥ := by
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 t.GT).exists_card_eq
  refine (Subgroup.disjoint_of_coprime_natCard (H := pCoreOf 2 t.GT) (K := t.K) ?_).eq_bot
  rw [hn]
  exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr t.hHall.2.1)

theorem GT_eq_K_of_pCoreOf_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h : pCoreOf 2 t.GT = ⊥) : t.GT = t.K := by
  rw [t.GT_eq_pCoreOf_sup_K hfr, h, bot_sup_eq]

end Track

theorem str83RqO4_of_pCoreOf_eq_bot
    (h : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a f : ℕ),
      Frame L1 L2 S a f → f ≠ 2 * a + 1 → ∀ t : Track L1 L2 S, pCoreOf 2 t.GT = ⊥) :
    Str83RqO4 := by
  intro G _ _ L1 L2 S a f hfr hf t
  exact t.GT_eq_K_of_pCoreOf_eq_bot hfr (h G L1 L2 S a f hfr hf t)

end CFSG.Quasithin.Stroth.Rq

end
