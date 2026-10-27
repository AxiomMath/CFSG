module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8NoAC
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab8Reach
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab9Crit
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Ord
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RCoinc
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Dbl
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7MvMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7 CFSG.Quasithin.F6.GoldAmL3

namespace F6

namespace GoldAmLab9

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V : Subgroup D} {z : D}

theorem aMovedEmpty_of_pushUp (h3 : GoldHyp3 A B z V) (hb : 5 ≤ critDist (A ⊔ B) A B V)
    (hPU : ∀ x y : CosetGeom (A ⊔ B) A B, vtype x = true → (graph (A ⊔ B) A B).Adj x y →
      ¬ stab x ≤ Subgroup.normalizer ((ballStab 1 x ⊓ ballStab 1 y : Subgroup D) : Set D)) :
    GoldAmLab8.AMovedEmpty A B z V := by
  classical
  intro c V₂ hn₂ hmv
  have h64 := h3.sixty_four_le_card_inf
  have h : TwoSys A B z V c V₂ := TwoSys.of_goldHyp3 h3 (by omega) hn₂
  have hreach := GoldAmLab8.reach_of_pushUp h h3 (b := critDist (A ⊔ B) A B V) rfl hb hPU
  obtain ⟨m, hm⟩ : ∃ m, critDist (A ⊔ B) A B V = m + 1 :=
    ⟨critDist (A ⊔ B) A B V - 1, by omega⟩
  rw [hm] at hreach
  obtain ⟨p, hp0, hp, hcrit⟩ := h3.exists_crit_geodesic hm
  have hd : CosetGeom.dist (p 0) (p (m + 1)) = m + 1 := by
    have := hp 0 (m + 1) (Nat.zero_le _) le_rfl
    omega
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hnot : ¬ Nm A B V V₂ (p 0) ≤ ballStab 1 (p (m + 1)) := by
    rw [hp0, Nm_γ₀ hA]
    exact hcrit
  have hv0 : vtype (p 0) = false := by rw [hp0]; exact vtype_γ₀
  have hd' : CosetGeom.dist (p (m + 1)) (p 0) = m + 1 := by
    rw [CosetGeom.dist_comm]
    exact hd
  exact false_of_moved_crit h hmv hreach hv0 hd' (not_nm_le_flip h hreach hd hnot)

end GoldAmLab9

end F6

end CFSG.Quasithin
