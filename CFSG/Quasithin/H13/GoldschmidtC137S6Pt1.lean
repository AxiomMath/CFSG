module

public import CFSG.Quasithin.H13.GoldschmidtC137CPt1
public import CFSG.Quasithin.H13.GoldschmidtC137S6Rst
public import CFSG.Quasithin.EmptyFaithful.A38c5Aut
public import CFSG.Quasithin.H13.GoldschmidtC137S6Pst

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace S6Ctx

variable [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M)
include h

theorem R_le_N : pCoreOf 2 P ≤ normalizer (V : Set G) :=
  h.toBase.R_le_N

theorem R_le_X : pCoreOf 2 P ≤ X :=
  h.toBase.R_le_X

theorem isPGroup_P_inf_C : IsPGroup 2 ↥(P ⊓ centralizer (V : Set G)) := by
  have h1 : IsPGroup 2 ↥(pCoreOf 2 X) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  refine h1.to_le ?_
  rw [← h.CXV]
  exact inf_le_inf_right _ h.hPX.le

end S6Ctx

namespace S6Frame

variable [Finite G] {X T V L P M : Subgroup G} {h : S6Ctx X T V L P M} (F : S6Frame h)

theorem pstar_cases :
    (autI h.hVe P = H1.map F.ρ ∧ autI h.hVe (pCoreOf 2 P) = R1.map F.ρ) ∨
      (autI h.hVe P = H2.map F.ρ ∧ autI h.hVe (pCoreOf 2 P) = R2.map F.ρ) := by
  have hR : autI h.hVe (pCoreOf 2 P) = pCoreOf 2 (autI h.hVe P) :=
    A38c5.autI_pCoreOf h.hVe (h.hPX.le.trans h.hXN) h.isPGroup_P_inf_C
  rw [hR]
  rcases F.autI_P_cases with hP | hP
  · left
    refine ⟨hP, ?_⟩
    rw [hP, A38c5.pCoreOf_map_of_injective 2 F.ρ F.inj, pCoreOf_H1]
  · right
    refine ⟨hP, ?_⟩
    rw [hP, A38c5.pCoreOf_map_of_injective 2 F.ρ F.inj, pCoreOf_H2]

theorem point_J_cases (hP : autI h.hVe P = H1.map F.ρ)
    (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    autI h.hVe (thompsonJ (pCoreOf 2 P)) = Z1.map F.ρ ∨
      autI h.hVe (thompsonJ (pCoreOf 2 P)) = R1.map F.ρ :=
  F.toC137B.point_J_cases hP hR hJ

theorem point_no_strong (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ) :
    ∀ B, ¬ IsStrongFFStarOffender (autI h.hVe (pCoreOf 2 P)) B :=
  F.toC137B.point_no_strong hR

end S6Frame

end CFSG.Quasithin.H13.U3.GC137
