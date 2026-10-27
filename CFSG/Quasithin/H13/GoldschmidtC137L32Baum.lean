module

public import CFSG.Quasithin.H13.GoldschmidtC137L32Off
public import CFSG.Quasithin.H13.GoldschmidtC137Baum

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isSylowTwoOf_of_le_of_le {Q D D' : Subgroup G} (hQD : Q ≤ D) (hDD' : D ≤ D')
    (h : IsSylowTwoOf Q D') : IsSylowTwoOf Q D := by
  refine ⟨hQD, h.2.1, fun h2 => h.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex Q D D' hQD hDD'
  show 2 ∣ Q.relIndex D'
  rw [← h1]
  exact Dvd.dvd.mul_right h2 _

theorem pCoreOf_le_oTwoPhi (M : Subgroup G) : pCoreOf 2 M ≤ oTwoPhi M := by
  unfold pCoreOf oTwoPhi
  refine Subgroup.map_mono fun y hy => ?_
  rw [Subgroup.mem_comap]
  have : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥M) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  rw [this]
  exact Subgroup.one_mem _

namespace L32Ctx

variable [Finite G] {X T L P W : Subgroup G} {u : G} (h : L32Ctx X T L P W u)
include h

theorem hLeq : CFSG.QuasithinUnique.Setup.oddOrderSubgroup X = L := by
  have hLX := h.hLX
  have hperf : Group.IsPerfect ↥L := isPerfect_of_commutator_eq_gc (perfect_of_mem_cComp h.hL)
  apply le_antisymm
  · exact CFSG.QuasithinUnique.Setup.oddOrderSubgroup_le_of_pow_mem fun x hx =>
      C124.exists_pow_mem_of_prod hLX h.hn h.hT.1 h.hT.2.1 hx (h.hprod x hx)
  · calc L = CFSG.QuasithinUnique.Setup.oddOrderSubgroup L :=
        (CFSG.QuasithinUnique.Setup.Lift.oddOrderSubgroup_eq_of_perfect hperf).symm
      _ ≤ CFSG.QuasithinUnique.Setup.oddOrderSubgroup X :=
        CFSG.QuasithinUnique.Setup.Lift.oddOrderSubgroup_mono hLX

theorem hWR : W ≤ pCoreOf 2 P := (C124.le_pCoreOf_of_reduced h.hred).trans h.hQR

theorem hL_inf_C : L ⊓ centralizer (W : Set G) = pCoreOf 2 L :=
  (autI_L_eq_top h.hL h.lie h.hXN h.hWe h.hWL h.hW8).2

theorem hOL_le_Q : pCoreOf 2 L ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans h.hLX)
    (h.hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

omit [Finite G] in
theorem hXC : X ≤ normalizer ((X ⊓ centralizer (W : Set G) : Subgroup G) : Set G) := by
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

theorem hQ_eq : pCoreOf 2 X = pCoreOf 2 (X ⊓ centralizer (W : Set G)) := by
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
    IsSylowTwoOf (pCoreOf 2 X) (X ⊓ centralizer (W : Set G)) ∧
      pCoreOf 2 X = pCoreOf 2 P ⊓ centralizer (W : Set G) := by
  have hVL : ⁅W, L⁆ ≠ ⊥ := by
    rw [h.hWL]
    intro hb
    have h8 := h.hW8
    have h1 : Nat.card W = 1 := by rw [hb]; exact Subgroup.card_bot
    omega
  obtain ⟨⟨hsyl, hQ⟩, -⟩ := C124.B2_10_2 h.hWe h.hred h.hQR h.hRT h.hT h.hLX h.hn h.hprod hVL
    (Or.inl (isQuasisimple_L32 h.lie))
  exact ⟨h.hQ_eq ▸ hsyl, hQ⟩

theorem hA1 : pCoreOf 2 L ≤ pCoreOf 2 P ⊓ centralizer (W : Set G) := by
  rw [← h.hb2102.2]
  exact h.hOL_le_Q

theorem hA2 :
    IsSylowTwoOf (pCoreOf 2 P ⊓ centralizer (W : Set G))
      ((L ⊔ pCoreOf 2 P) ⊓ centralizer (W : Set G)) := by
  rw [← h.hb2102.2]
  refine isSylowTwoOf_of_le_of_le ?_ ?_ h.hb2102.1
  · exact le_inf (h.hQR.trans le_sup_right) (C124.pCoreOf_le_centralizer h.hred)
  · exact inf_le_inf_right _ (sup_le h.hLX (h.hRT.trans h.hT.1))

theorem hA3 : L ≤ normalizer ((pCoreOf 2 P ⊓ centralizer (W : Set G) : Subgroup G) : Set G) := by
  rw [← h.hb2102.2]
  exact h.hLX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)

theorem hB : (L ⊓ centralizer (W : Set G)).subgroupOf X ≤ oTwoPhi (L.subgroupOf X) := by
  rw [h.hL_inf_C, ← pCoreOf_subgroupOf_eq h.hLX]
  exact pCoreOf_le_oTwoPhi _

end L32Ctx

end CFSG.Quasithin.H13.U3.GC137
