module

public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.RankThree.PartOne.FOCD.Bridge
public import CFSG.RankThree.PartOne.K1214.SylowShape

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOCD

@[expose] def SylowAbelian (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow p G, ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x

section Generic

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem commute_of_isCyclic {S : Subgroup G} (hS : IsCyclic S) :
    ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  intro x hx y hy
  have h := (IsCyclic.commGroup (α := S)).mul_comm ⟨x, hx⟩ ⟨y, hy⟩
  simpa using congrArg Subtype.val h

theorem sylowAbelian_of_shape (hp : p.Prime) {r e : ℕ} (h : K1214.SylowShape p r e G) :
    SylowAbelian p G := by
  intro P x hx y hy
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ⟩ := h P P.isPGroup' (Sylow.not_dvd_index P)
  have h1 : φ (⟨x, hx⟩ * ⟨y, hy⟩) = φ (⟨y, hy⟩ * ⟨x, hx⟩) := by
    rw [map_mul, map_mul, mul_comm (φ ⟨x, hx⟩)]
  have := φ.injective h1
  simpa using congrArg Subtype.val this

theorem sylowAbelian_of_pRank_le_one (hp : p.Prime) (hp2 : p ≠ 2) (h : CFSG.pRank p G ≤ 1) :
    SylowAbelian p G := by
  intro P
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : IsCyclic (P : Subgroup G) := isCyclic_of_pRank_le_one hp hp2
    (le_top : (P : Subgroup G) ≤ ⊤) P.isPGroup' (by
      rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)]
      exact h)
  exact commute_of_isCyclic hcyc

theorem sylowAbelian_of_not_dvd (hp : p.Prime) (h : ¬ p ∣ Nat.card G) : SylowAbelian p G := by
  intro P x hx y hy
  have : Fact p.Prime := ⟨hp⟩
  have hcard := Sylow.card_eq_multiplicity P
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero] at hcard
  have hbot : (P : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard
  rw [hbot, Subgroup.mem_bot] at hx hy
  rw [hx, hy]

end Generic

end CFSG.RankThree.PartOne.FOC
