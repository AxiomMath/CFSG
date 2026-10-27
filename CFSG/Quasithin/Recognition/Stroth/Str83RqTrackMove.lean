module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

def edgeElt (v : ℤ) : G :=
  if Even v then (t.x₂ * t.x₁) ^ (v / 2) else (t.x₂ * t.x₁) ^ (v / 2) * t.x₂

theorem edgeElt_mem_normalizer (v : ℤ) : t.edgeElt v ∈ normalizer (t.K : Set G) := by
  unfold edgeElt
  split_ifs
  · exact zpow_mem t.track.tau_mem_normalizer _
  · exact mul_mem (zpow_mem t.track.tau_mem_normalizer _) t.track.x₂_norm

theorem map_qv_edgeElt {F₁ F₂ : Subgroup G} (h₁ : P1 L1 L2 S ≤ normalizer (F₁ : Set G))
    (h₂ : P2 L1 L2 S ≤ normalizer (F₂ : Set G)) (v i : ℤ) :
    (qv F₁ F₂ t.x₁ t.x₂ i).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
      qv F₁ F₂ t.x₁ t.x₂ (if Even v then v + i else v + 1 - i) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · have hm : t.edgeElt (2 * k) = (t.x₂ * t.x₁) ^ k := by
      unfold edgeElt
      rw [if_pos (even_two_mul k), show 2 * k / 2 = k by omega]
    rw [hm, if_pos (even_two_mul k), map_qv_tau_pow (Q₁ := F₁) (Q₂ := F₂) i k]
    congr 1
    ring
  · have hm : t.edgeElt (2 * k + 1) = (t.x₂ * t.x₁) ^ k * t.x₂ := by
      unfold edgeElt
      rw [if_neg (Int.not_even_two_mul_add_one k), show (2 * k + 1) / 2 = k by omega]
    rw [hm, if_neg (Int.not_even_two_mul_add_one k),
      ← Subgroup.map_conj_map_conj (qv F₁ F₂ t.x₁ t.x₂ i) t.x₂ ((t.x₂ * t.x₁) ^ k),
      t.track.map_qv_x₂ (Q₁ := F₁) (Q₂ := F₂) h₁ h₂ i,
      map_qv_tau_pow (Q₁ := F₁) (Q₂ := F₂) (2 - i) k]
    congr 1
    ring

theorem map_win_edgeElt {F₁ F₂ : Subgroup G} (h₁ : P1 L1 L2 S ≤ normalizer (F₁ : Set G))
    (h₂ : P2 L1 L2 S ≤ normalizer (F₂ : Set G)) (v a b : ℤ) :
    (win F₁ F₂ t.x₁ t.x₂ a b).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
      if Even v then win F₁ F₂ t.x₁ t.x₂ (v + a) (v + b)
      else win F₁ F₂ t.x₁ t.x₂ (v + 1 - b) (v + 1 - a) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · have hm : t.edgeElt (2 * k) = (t.x₂ * t.x₁) ^ k := by
      unfold edgeElt
      rw [if_pos (even_two_mul k), show 2 * k / 2 = k by omega]
    rw [hm, if_pos (even_two_mul k), map_win_tau_pow (Q₁ := F₁) (Q₂ := F₂) a b k]
    rw [show a + 2 * k = 2 * k + a by ring, show b + 2 * k = 2 * k + b by ring]
  · have hm : t.edgeElt (2 * k + 1) = (t.x₂ * t.x₁) ^ k * t.x₂ := by
      unfold edgeElt
      rw [if_neg (Int.not_even_two_mul_add_one k), show (2 * k + 1) / 2 = k by omega]
    rw [hm, if_neg (Int.not_even_two_mul_add_one k),
      ← Subgroup.map_conj_map_conj (win F₁ F₂ t.x₁ t.x₂ a b) t.x₂ ((t.x₂ * t.x₁) ^ k),
      t.track.map_win_x₂ (Q₁ := F₁) (Q₂ := F₂) h₁ h₂ a b,
      map_win_tau_pow (Q₁ := F₁) (Q₂ := F₂) (2 - b) (2 - a) k]
    rw [show (2 - b) + 2 * k = 2 * k + 1 + 1 - b by ring,
      show (2 - a) + 2 * k = 2 * k + 1 + 1 - a by ring]

theorem map_Gv_edgeElt (v i : ℤ) :
    (t.Gv i).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
      t.Gv (if Even v then v + i else v + 1 - i) := by
  change (qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ i).map
      (MulAut.conj (t.edgeElt v)).toMonoidHom =
    qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (if Even v then v + i else v + 1 - i)
  exact t.map_qv_edgeElt (F₁ := P1 L1 L2 S) (F₂ := P2 L1 L2 S)
    Subgroup.le_normalizer Subgroup.le_normalizer v i

theorem map_Qv_edgeElt (v i : ℤ) :
    (t.Qv i).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
      t.Qv (if Even v then v + i else v + 1 - i) := by
  change (qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ i).map
      (MulAut.conj (t.edgeElt v)).toMonoidHom =
    qv (Q1 L1 L2 S) (Q2 L1 L2 S) t.x₁ t.x₂ (if Even v then v + i else v + 1 - i)
  exact t.map_qv_edgeElt (F₁ := Q1 L1 L2 S) (F₂ := Q2 L1 L2 S)
    (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)) v i

theorem map_Zv_edgeElt (v i : ℤ) :
    (t.Zv i).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
      t.Zv (if Even v then v + i else v + 1 - i) := by
  change (qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ i).map
      (MulAut.conj (t.edgeElt v)).toMonoidHom =
    qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ (if Even v then v + i else v + 1 - i)
  exact t.map_qv_edgeElt (F₁ := Z1 L1 L2 S) (F₂ := Z2 L1 L2 S)
    ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
    ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))) v i

theorem map_Gw_edgeElt (v a b : ℤ) :
    (t.Gw a b).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
      if Even v then t.Gw (v + a) (v + b) else t.Gw (v + 1 - b) (v + 1 - a) := by
  change (win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ a b).map
      (MulAut.conj (t.edgeElt v)).toMonoidHom =
    if Even v then win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (v + a) (v + b)
    else win (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ (v + 1 - b) (v + 1 - a)
  exact t.map_win_edgeElt (F₁ := P1 L1 L2 S) (F₂ := P2 L1 L2 S)
    Subgroup.le_normalizer Subgroup.le_normalizer v a b

theorem map_Gw_zero_one_edgeElt (v : ℤ) :
    (t.Gw 0 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Gw v (v + 1) := by
  rw [t.map_Gw_edgeElt v 0 1]
  split_ifs <;>
    simp only [add_zero, add_sub_cancel_left, add_sub_cancel_right, sub_zero]

end Track

end CFSG.Quasithin.Stroth.Rq

end
