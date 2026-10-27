module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux9

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix
  CFSG.LocalAnalysis.ComponentInitial

open scoped MatrixGroups

theorem ggNSPosPA7_card_fixed {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs)
    {a b : Fin n} (hab : a ≠ b) :
    Nat.card {s : ↥Bs // (((ggNSPosPA_permAutEquiv h hd (Equiv.swap a b) :
        ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) s = s)} * p = Nat.card ↥Bs := by
  classical
  let ρ : ↥Bs →* Kˣ := ggNSPosPA7_ratioHom h hd a b
  have hrange : Nat.card ρ.range = p := ggNSPosPA7_ratioHom_range_card h hd a b hab
  have hfix : ∀ s : ↥Bs, (((ggNSPosPA_permAutEquiv h hd (Equiv.swap a b) :
      ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) s = s) ↔ ρ s = 1 :=
    fun s => ggNSPosPA7_fixed_iff h hd hab s
  have hcardfix : Nat.card {s : ↥Bs // (((ggNSPosPA_permAutEquiv h hd (Equiv.swap a b) :
      ↥(ggAutomizer ψ.range Bs)) : MulAut ↥Bs) s = s)} = Nat.card ρ.ker := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hfix)]
    rfl
  rw [hcardfix, ← Subgroup.card_ker_mul_card_range ρ, hrange]

end CFSG.StandardType

end
