module

public import CFSG.Quasithin.H13.GoldschmidtC137Tail
public import CFSG.Quasithin.H13.GoldschmidtC137WeakRel

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

namespace BaumCtx

variable [Finite G] {X T V L P : Subgroup G} (h : BaumCtx X T V L P)
include h

theorem ms_tail' (hSQ : SQTKGroup ↥X)
    (hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G))
    (hRS : autI h.hVe (pCoreOf 2 P) ≤ autI h.hVe (baum (pCoreOf 2 P)))
    (hC : ∀ A, ¬ IsStrongFFOffender h.hVe (pCoreOf 2 P) A)
    (hDE : ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V h.hVe))) (Rs : Fin n → Subgroup G),
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
              B1.conjAut g (Y j) ≤ autI h.hVe (pCoreOf 2 P)) :
    IsMSPair (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) ∧
      L ∈ cComp (L ⊔ baum (pCoreOf 2 P)) ∧
      ((L ⊔ baum (pCoreOf 2 P) : Subgroup G) : Set G) = (L : Set G) * (baum (pCoreOf 2 P) : Set G) ∧
      P ⊓ (L ⊔ baum (pCoreOf 2 P)) < L ⊔ baum (pCoreOf 2 P) ∧
      ¬ 2 ∣ (P ⊓ (L ⊔ baum (pCoreOf 2 P))).relIndex (L ⊔ baum (pCoreOf 2 P)) ∧
      baum (pCoreOf 2 P) = pCoreOf 2 (P ⊓ (L ⊔ baum (pCoreOf 2 P))) := by
  have hRX : pCoreOf 2 P ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans h.hPX.le
  obtain ⟨hCV, -⟩ := b2_19_rel' h.hVe h.hred.1 h.hXN h.hLeq.symm
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) hRX h.hVR h.hA1 h.hA2 h.hA3 h.hB hC hDE
  obtain ⟨hMS, hLcomp, hset⟩ := isMSPair_of_baumann hSQ h.hT h.hprod h.hL h.hL2 h.hn h.hTP h.hPX
    h.hXN h.hLie hn1 hCV hRS
  obtain ⟨hHlt, hHodd, hSeq⟩ := msA_of_baumann h.hT h.hprod h.hL h.hn h.hTP h.hPX h.hXN hCV hRS
  exact ⟨hMS, hLcomp, hset, hHlt, hHodd, hSeq⟩

end BaumCtx

end CFSG.Quasithin.H13.U3.GC137
