module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab4Comm
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Geom
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab3Ker

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab4

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem four_le_critDist_of_le_coreIn_left (h : OneSide A B z V)
    (hU : conjClosure V B ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) A) :
    4 ≤ critDist (A ⊔ B) A B V := by
  rw [le_critDist_iff (h.gold.amalgamHypV h.nat) h.nat.natural.ne_bot (by norm_num),
    le_ballStab_four_iff rfl h.nat.reduced.2.1]
  have hVA : V ≤ A := h.nat.le_pCoreOf.trans (pCoreOf_le 2 A)
  have hVB : V ≤ B := h.hVQ.trans (pCoreOf_le 2 B)
  have hUA : conjClosure V B ≤ A := h.U_le_Q_A.trans (pCoreOf_le 2 A)
  have hN : conjClosure (conjClosure V B) A ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) A :=
    conjClosure_le fun k hk u hu =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ hk) u).mp (hU hu)
  have hNQB : conjClosure (conjClosure V B) A ≤ pCoreOf 2 B :=
    hN.trans ((coreIn_le_right _ _).trans inf_le_right)
  have hNB : conjClosure (conjClosure V B) A ≤ B := hNQB.trans (pCoreOf_le 2 B)
  have hN2 : conjClosure (conjClosure (conjClosure V B) A) B ≤ A := by
    have : conjClosure (conjClosure (conjClosure V B) A) B ≤ pCoreOf 2 B :=
      conjClosure_le fun k hk w hw =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 B hk) w).mp (hNQB hw)
    exact this.trans (h.gold.pCoreOf_right_le.trans inf_le_left)
  exact ⟨hVA, hVB, hUA, hNB, hN2⟩

theorem le_coreIn_left_of_swap (h : OneSide A B z V) {x c : D} {V₂ : Subgroup D}
    (h2 : OneSide B A c V₂) (hxB : x ∈ B) (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) :
    conjClosure V B ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) A := fun u hu => by
  have hu' : u ∈ pCoreOf 2 A ⊓ Subgroup.centralizer (conjClosure V₂ A : Set D) :=
    ⟨h.U_le_Q_A hu, Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (U_comm_U₂ h h2 hxB hx3 hxz hc u hu w hw).symm⟩
  rw [GoldAmLab3.pCoreOf_inf_centralizer_eq_coreIn h2, inf_comm] at hu'
  exact hu'

theorem four_le_critDist_of_moves (h : OneSide A B z V) (h32 : 32 ≤ Nat.card ↥(A ⊓ B))
    (hmove : ∃ y ∈ B, y * z * y⁻¹ ≠ z) : 4 ≤ critDist (A ⊔ B) A B V := by
  obtain ⟨x, c, V₂, hxB, hx3, hxz, hc, h2⟩ := exists_swap h.gold h32 h.nat hmove
  exact four_le_critDist_of_le_coreIn_left h (le_coreIn_left_of_swap h h2 hxB hx3 hxz hc)

theorem four_le_critDist_swap (h : OneSide A B z V) {x c : D} {V₂ : Subgroup D}
    (h2 : OneSide B A c V₂) (hxB : x ∈ B) (hx3 : x * x * x = 1) (hxz : x * z * x⁻¹ ≠ z)
    (hc : c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹)) : 4 ≤ critDist (B ⊔ A) B A V₂ := by
  refine four_le_critDist_of_le_coreIn_left h2 fun w hw => ?_
  have hw' : w ∈ pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) :=
    ⟨h2.U_le_Q_A hw, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      U_comm_U₂ h h2 hxB hx3 hxz hc u hu w hw⟩
  rw [GoldAmLab3.pCoreOf_inf_centralizer_eq_coreIn h, inf_comm] at hw'
  exact hw'

end GoldAmLab4

end F6

end CFSG.Quasithin
