module

public import CFSG.Quasithin.H13.GoldschmidtC137H6ToBase
public import CFSG.Quasithin.H13.GoldschmidtC137CLn2

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

theorem line_J_eq (hP : autI h.hVe P = H2.map F.ρ) (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    autI h.hVe (thompsonJ (pCoreOf 2 P)) = R2.map F.ρ :=
  F.toC137B.line_J_eq hP hR h5 hJ

theorem line_no_strong (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2) :
    ∀ A : Subgroup G, ¬ IsStrongFFOffender h.hVe (pCoreOf 2 P) A :=
  F.toC137B.line_no_strong hR h5

theorem line_hDE (hP : autI h.hVe P = H2.map F.ρ) (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) :
    ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V h.hVe))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI h.hVe L, B1.conjAut g (Y i) ≤ autI h.hVe (pCoreOf 2 P)) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (starPreIn h.hVe (L ⊔ pCoreOf 2 P) (Y i))) ∧
      (∀ i, Y i = autI h.hVe (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 (pCoreOf 2 P)) ∧
      autI h.hVe L ≤ ⨆ i, Y i ∧
      ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI h.hVe L)) ∧
      ∀ A, IsFFStarOffender (autI h.hVe (pCoreOf 2 P)) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V h.hVe))),
          A = ⨆ k, Ai k ∧ ∀ k, IsFFStarOffender (autI h.hVe (pCoreOf 2 P)) (Ai k) ∧
            ∃ j : Fin n, ∃ g ∈ autI h.hVe L, Ai k ≤ B1.conjAut g (Y j) ∧
              B1.conjAut g (Y j) ≤ autI h.hVe (pCoreOf 2 P) :=
  F.toC137B.line_hDE hP hR h5 hJ

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
