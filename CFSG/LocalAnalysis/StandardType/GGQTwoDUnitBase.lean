module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartTwoThreeCent
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLang
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

variable {G : Type} [Group G] [Finite G]

structure QTwoUnitBase (p : ℕ) (B Bs : Subgroup G) (x : G) (L : Subgroup G) {F0 : Type}
    [Field F0] [Finite F0] [CharP F0 2] {m : ℕ} (ψ : Su F0 2 1 m →* G)
    (ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)) : Prop where
  p_eq : p = 3
  card_field : Nat.card F0 = 4
  hyp : GGNSLocalHyp p B Bs F0 1 m ψ
  range : ψ.range = L
  diag : GGActsDiagonally (p := 2) (f := 1) ψ Bs
  perm : ∀ (σ : Equiv.Perm (Fin m)) (s : ↥Bs),
    ((((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s : ↥Bs) : G) =
      ψ (ggPermSU σ⁻¹) * (s : G) * (ψ (ggPermSU σ⁻¹))⁻¹
  refl : ∀ a b : Fin m, a ≠ b →
    GGIsReflection p ((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  rankOne : ∀ a b : Fin m, a ≠ b →
    ggRankOneIn L Bs ((ε (Equiv.swap a b) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
      (ggSuPairBlock F0 2 1 m a b).map ψ
  card_bs : Nat.card ↥Bs = 3 ^ m
  x_mem : x ∈ Bs
  x_order : orderOf x = 3
  cent : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x
  full : ∀ c : Fin m → F0ˣ, ∃ b ∈ Bs, qTwoChartTwoThree_induces ψ b c

theorem QTwoUnitBase.card_bs_eq {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} {F0 : Type}
    [Field F0] [Finite F0] [CharP F0 2] {m : ℕ} {ψ : Su F0 2 1 m →* G}
    {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} (h : QTwoUnitBase p B Bs x L ψ ε)
    (hm : 1 ≤ m) :
    Nat.card ↥Bs = 3 ^ (m - 1) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := by
  rw [h.cent, Nat.card_zpowers, h.x_order, h.card_bs, ← pow_succ, Nat.sub_add_cancel hm]

end CFSG.StandardType.QTwo

end
