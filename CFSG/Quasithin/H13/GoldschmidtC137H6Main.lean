module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Ln3
public import CFSG.Quasithin.H13.GoldschmidtC137H6Pt3
public import CFSG.Quasithin.H13.GoldschmidtC137S6Pt3

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

theorem h6_concl [Finite G] (hC124 : C124StatementSQTK (G := G))
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32) {X T V L P : Subgroup G}
    (h : H6Ctx X T V L P) (hPpg : IsPGroup 2 ↥(P ⊓ centralizer (V : Set G)))
    (hPmax : ∀ K : Subgroup (MulAut (IntMod V h.hVe)), autI h.hVe P ≤ K → K ≤ autI h.hVe X →
      K = autI h.hVe P ∨ K = autI h.hVe X)
    (hPne : autI h.hVe P ≠ autI h.hVe X) (hZ : ¬ oTwoUpper (A6.o2Z L) ≤ P) :
    Concl X T V L P := by
  obtain ⟨F⟩ := h.nonempty_frame
  by_cases hCN : CharNormal (baum (pCoreOf 2 P)) X
  · exact Or.inl hCN
  obtain ⟨-, -, -, hdich⟩ := C124.B2_10_2 h.hVe h.hred h.hQR h.hRT h.hT h.hLX h.hn h.hprod
    h.hVL (Or.inl h.hLq)
  rcases hdich with hbq | ⟨hst, -⟩
  · have hV1 : V ≠ ⊥ := fun hb => h.hVL (by rw [hb, Subgroup.commutator_bot_left])
    exact absurd (charNormal_of_baum_eq_gc (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      ⟨V, C124.le_pCoreOf_of_reduced h.hred, h.hVe, hV1⟩ hbq) hCN
  have hJ := not_J_le_of_conjIn_nonempty h.hVe h.hXN hst.1
  rcases F.pstar_cases hPpg hPmax hPne with ⟨hP, hR⟩ | ⟨hP, hR⟩
  · rcases F.point_J_cases hP hR hJ with hJ1 | hJ1
    · exact Or.inr (Or.inl (F.point_a_concl hC124 hCN hR hJ1))
    · exact Or.inr (Or.inl (F.point_b_concl hC132 hCN hR hJ hJ1))
  · by_cases h5 : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A V)
    · exact F.line_five hR hZ h5
    · push Not at h5
      exact Or.inr (Or.inl (F.line_block hC132 hCN hP hR h5 hJ))

end CFSG.Quasithin.H13.U3.GC137
