module

public import CFSG.Quasithin.H13.GoldschmidtC137L32Baum
public import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
public import CFSG.Quasithin.H13.GoldschmidtC137MSd

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

structure BaumCtx [Finite G] (X T V L P : Subgroup G) : Prop where
  hT : IsSylowTwoOf T X
  hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t
  hL : L ∈ cComp X
  hL2 : CharTwo L
  hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3
  hLie : IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  hTP : T ≤ P
  hPX : P < X
  hred : IsTwoReducedIn X V
  hVL : ⁅V, L⁆ ≠ ⊥
  hB : (L ⊓ centralizer (V : Set G)).subgroupOf X ≤ oTwoPhi (L.subgroupOf X)

namespace BaumCtx

variable [Finite G] {X T V L P : Subgroup G} (h : BaumCtx X T V L P)
include h

theorem hLX : L ≤ X := le_of_mem_cComp h.hL

theorem hn : X ≤ normalizer (L : Set G) := C124.le_normalizer_of_prod h.hT h.hprod h.hL

theorem hXN : X ≤ normalizer (V : Set G) := h.hred.2.1

theorem hVe : IsElemAbelian 2 V := h.hred.2.2.1

theorem hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
  have h3 := Subgroup.relIndex_mul_relIndex T P X h.hTP h.hPX.le
  have h4 : 2 ∣ T.relIndex X := by
    rw [← h3]
    exact Dvd.dvd.mul_right h2 _
  exact h.hT.2.2 h4

theorem hRT : pCoreOf 2 P ≤ T := pCoreOf_two_le_of_sylowIn h.hTP h.hT.2.1 h.hTodd

theorem hQR : pCoreOf 2 X ≤ pCoreOf 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn h.hT.1 h.hT.2.1 h.hT.2.2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans h.hTP)
    (h.hPX.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem hLeq : CFSG.QuasithinUnique.Setup.oddOrderSubgroup X = L := by
  have hperf : Group.IsPerfect ↥L := isPerfect_of_commutator_eq_gc (perfect_of_mem_cComp h.hL)
  apply le_antisymm
  · exact CFSG.QuasithinUnique.Setup.oddOrderSubgroup_le_of_pow_mem fun x hx =>
      C124.exists_pow_mem_of_prod h.hLX h.hn h.hT.1 h.hT.2.1 hx (h.hprod x hx)
  · calc L = CFSG.QuasithinUnique.Setup.oddOrderSubgroup L :=
        (CFSG.QuasithinUnique.Setup.Lift.oddOrderSubgroup_eq_of_perfect hperf).symm
      _ ≤ CFSG.QuasithinUnique.Setup.oddOrderSubgroup X :=
        CFSG.QuasithinUnique.Setup.Lift.oddOrderSubgroup_mono h.hLX

theorem hVR : V ≤ pCoreOf 2 P := (C124.le_pCoreOf_of_reduced h.hred).trans h.hQR

theorem hOL_le_Q : pCoreOf 2 L ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.hLX)
    (h.hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem hXC : X ≤ normalizer ((X ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => ⟨X.mul_mem (X.mul_mem hx hc.1) (X.inv_mem hx),
    C124.conj_mem_centralizer_of_le h.hXN hx hc.2⟩, fun hc => ?_⟩
  have h1 := C124.conj_mem_centralizer_of_le h.hXN (X.inv_mem hx) hc.2
  refine ⟨?_, ?_⟩
  · have := X.mul_mem (X.mul_mem (X.inv_mem hx) hc.1) hx
    simpa [mul_assoc] using this
  · simpa [mul_assoc] using h1

theorem hQ_eq : pCoreOf 2 X = pCoreOf 2 (X ⊓ centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X) (C124.pCoreOf_le_centralizer h.hred))
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
      (h.hXC.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem hb2102 :
    IsSylowTwoOf (pCoreOf 2 X) (X ⊓ centralizer (V : Set G)) ∧
      pCoreOf 2 X = pCoreOf 2 P ⊓ centralizer (V : Set G) := by
  obtain ⟨⟨hsyl, hQ⟩, -⟩ := C124.B2_10_2 h.hVe h.hred h.hQR h.hRT h.hT h.hLX h.hn h.hprod h.hVL
    h.hLq
  exact ⟨h.hQ_eq ▸ hsyl, hQ⟩

theorem hA1 : pCoreOf 2 L ≤ pCoreOf 2 P ⊓ centralizer (V : Set G) := by
  rw [← h.hb2102.2]
  exact h.hOL_le_Q

theorem hA2 :
    IsSylowTwoOf (pCoreOf 2 P ⊓ centralizer (V : Set G))
      ((L ⊔ pCoreOf 2 P) ⊓ centralizer (V : Set G)) := by
  rw [← h.hb2102.2]
  refine isSylowTwoOf_of_le_of_le ?_ ?_ h.hb2102.1
  · exact le_inf (h.hQR.trans le_sup_right) (C124.pCoreOf_le_centralizer h.hred)
  · exact inf_le_inf_right _ (sup_le h.hLX (h.hRT.trans h.hT.1))

theorem hA3 : L ≤ normalizer ((pCoreOf 2 P ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  rw [← h.hb2102.2]
  exact h.hLX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)

theorem ms_tail (hSQ : SQTKGroup ↥X)
    (hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G))
    (hRS : autI h.hVe (pCoreOf 2 P) ≤ autI h.hVe (baum (pCoreOf 2 P)))
    (hC : ∀ B, ¬ IsStrongFFStarOffender (autI h.hVe (pCoreOf 2 P)) B)
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
  obtain ⟨hCV, -⟩ := b2_19_rel h.hVe h.hred.1 h.hXN h.hLeq.symm
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) hRX h.hVR h.hA1 h.hA2 h.hA3 h.hB hC hDE
  obtain ⟨hMS, hLcomp, hset⟩ := isMSPair_of_baumann hSQ h.hT h.hprod h.hL h.hL2 h.hn h.hTP h.hPX
    h.hXN h.hLie hn1 hCV hRS
  obtain ⟨hHlt, hHodd, hSeq⟩ := msA_of_baumann h.hT h.hprod h.hL h.hn h.hTP h.hPX h.hXN hCV hRS
  exact ⟨hMS, hLcomp, hset, hHlt, hHodd, hSeq⟩

end BaumCtx

end CFSG.Quasithin.H13.U3.GC137
