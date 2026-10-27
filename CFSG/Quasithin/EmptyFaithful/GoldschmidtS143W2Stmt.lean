module

public import CFSG.Quasithin.EmptyFaithful.Insp7RedB
public import CFSG.Quasithin.EmptyFaithful.S143UE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint

namespace S143

namespace InspW2

@[expose] def ListCasesCD (L : Type) [Group L] : Prop :=
  ∃ n : ℕ, (n = 6 ∨ n = 7) ∧ Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin n)) ∧
    (Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3)

structure InspInput {L : Type} [Group L] {Gc : Type} [Group Gc] (ρ : Gc →* MulAut L) (ž : Gc)
    (Ŝ Kh : Subgroup Gc) : Prop where
  inj : Function.Injective ρ
  inn : ∀ l : L, MulAut.conj l ∈ ρ.range
  sq : ž * ž = 1
  ne : ž ≠ 1
  sylow : IsPGroup 2 Ŝ ∧ ¬ 2 ∣ Ŝ.index
  cent : Ŝ ≤ Subgroup.centralizer ({ž} : Set Gc)
  K_le : Kh ≤ Subgroup.centralizer ({ž} : Set Gc)
  K_norm : (Kh.subgroupOf (Subgroup.centralizer ({ž} : Set Gc))).Normal
  K_shape : IsZ4StarSL23 ↥Kh
  ž_mem : ž ∈ Kh
  ž_cent : ∀ k ∈ Kh, k * ž = ž * k
  card_C : Nat.card ↥(Subgroup.centralizer ({ž} : Set Gc)) = 3 * Nat.card Ŝ
  card_S : Nat.card Ŝ = 2 ^ 5 ∨ Nat.card Ŝ = 2 ^ 6
  E : ∃ (E : Subgroup Gc) (y : Gc), E ≤ Ŝ ∧
    Nonempty (↥E ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ∧ orderOf y = 3 ∧
      y ∈ Subgroup.normalizer (E : Set Gc) ∧ ∀ e ∈ E, y * e * y⁻¹ = e → e = 1

@[expose] def InspWi : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → Insp7.ListCases L →
    ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L) (ž : Gc) (Ŝ Kh : Subgroup Gc),
      InspInput ρ ž Ŝ Kh → (∃ z : L, z * z = 1 ∧ ρ ž = MulAut.conj z) →
        CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSU 3 3 1

@[expose] def InspWo : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → ListCasesCD L →
    ∀ (Gc : Type) [Group Gc] [Finite Gc] (ρ : Gc →* MulAut L) (ž : Gc) (Ŝ Kh : Subgroup Gc),
      InspInput ρ ž Ŝ Kh → False

@[expose] def InspW : Prop := InspWi ∧ InspWo

end InspW2

end S143

end CFSG.Quasithin
