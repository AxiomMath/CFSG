module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPerm
import CFSG.LocalAnalysis.StandardType.GGNSJoinToralAAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNSDiag_toral_bound {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) :
    Nat.card ↥Bs ≤ p ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
  let a : Fin n := ⟨0, by have h4 := h.four_le; omega⟩
  have hcard : Nat.card ↥Bs = Nat.card (nsTor_ratioPi h hd a).ker *
      Nat.card (nsTor_ratioPi h hd a).range :=
    (Subgroup.card_ker_mul_card_range (nsTor_ratioPi h hd a)).symm
  have hker : Nat.card (nsTor_ratioPi h hd a).ker ≤
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥(nsTor_ratioPi h hd a).ker =>
        (⟨((x.1 : ↥Bs) : G), nsTor_ratioPi_ker_le h hd a x.1 x.2⟩ :
          ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)))) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) => (z : G)) hxy
  have hrange : Nat.card (nsTor_ratioPi h hd a).range ≤ p ^ (n - 1) :=
    nsTor_ratioPi_range_card_le h hd a
  calc Nat.card ↥Bs
      = Nat.card (nsTor_ratioPi h hd a).ker * Nat.card (nsTor_ratioPi h hd a).range := hcard
    _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) * p ^ (n - 1) :=
        Nat.mul_le_mul hker hrange
    _ = p ^ (n - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) :=
        Nat.mul_comm _ _

end CFSG.StandardType

end
