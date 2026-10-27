module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclNB
public import CFSG.Quasithin.EmptyFaithful.S151ZH
public import CFSG.Quasithin.EmptyFaithful.S153H33

public section

namespace CFSG.Quasithin.N204

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_centralizer_of_quasisimple {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) :
    pCoreOf 2 L ≤ Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ CFSG.pCore 2 ↥L := by assumption
  have hc := zb_pCore_le_center (CFSG.Quasithin.B1Red.isQuasisimple_to_open hq) hy'
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have := Subgroup.mem_center_iff.mp hc ⟨g, hg⟩
  exact congrArg Subtype.val this

theorem commutator_eq_bot_of_quasisimple {X L Q : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hLX : L ≤ X) (hXL : X ≤ Subgroup.normalizer (L : Set G)) (hQX : Q ≤ X)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 ↥Q) : ⁅L, Q⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
  have h1 : ⁅L, Q⁆ ≤ L := Rk2.commutator_le_of_le_normalizer (hQX.trans hXL)
  have h2 : ⁅L, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_comm]
    exact Rk2.commutator_le_of_le_normalizer (hLX.trans hXQ)
  have hnorm : L ≤ Subgroup.normalizer ((L ⊓ Q : Subgroup G) : Set G) :=
    Rk2.le_normalizer_inf Subgroup.le_normalizer (hLX.trans hXQ)
  have h3 : L ⊓ Q ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm (hQ2.to_le inf_le_right)
  have h5 : ⁅⁅L, Q⁆, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((le_inf h1 h2).trans (h3.trans (pCoreOf_le_centralizer_of_quasisimple hq)))
  have h6 : ⁅⁅Q, L⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm Q L]; exact h5
  have h7 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L) (H₂ := L) (H₃ := Q)
    (by rw [Subgroup.commutator_comm L Q]; exact h6) h6
  rwa [hperf] at h7

theorem isComponentIn_of_not_charTwo {X L : Subgroup G} (hL : L ∈ cComp X)
    (hO : oddCoreIn X = ⊥) (hnc : ¬ CharTwo L) : IsComponentIn L X := by
  by_contra h
  exact hnc (S153H.charTwo_of_mem_cComp_not_isComponentIn hO hL h)

theorem isQuasisimple_of_not_charTwo_of_oddCore {X L : Subgroup G} (hL : L ∈ cComp X)
    (hO : oddCoreIn X = ⊥) (hnc : ¬ CharTwo L) : CFSG.IsQuasisimple ↥L :=
  BenderBranch.isQuasisimple_of_isComponentIn (isComponentIn_of_not_charTwo hL hO hnc)

end CFSG.Quasithin.N204
