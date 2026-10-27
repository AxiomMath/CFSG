module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.RankThree.Classical.OrthogonalOrderThree

public section

namespace CFSG.StandardType

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.RankThree.Classical Matrix

open scoped MatrixGroups

noncomputable def ggNSPosPC_subgroupOfEquiv {G : Type*} [Group G] (H K : Subgroup G) :
    ↥(H.subgroupOf K) ≃ ↥(H ⊓ K) where
  toFun x := ⟨x.1.1, Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_subgroupOf.mp x.2, x.1.2⟩⟩
  invFun y := ⟨⟨y.1, y.2.2⟩, Subgroup.mem_subgroupOf.mpr y.2.1⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; rfl

theorem ggNSPosPC_card_map_mul_card_inf_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) (H0 : Subgroup G) :
    Nat.card ↥H0 = Nat.card ↥(H0.map f) * Nat.card ↥(H0 ⊓ f.ker) := by
  let φ : ↥H0 →* H := f.comp H0.subtype
  have hker : φ.ker = (H0 ⊓ f.ker).subgroupOf H0 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : φ.range = H0.map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  calc Nat.card ↥H0 = Nat.card (↥H0 ⧸ φ.ker) * Nat.card ↥(φ.ker) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    _ = Nat.card ↥φ.range * Nat.card ↥(φ.ker) := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    _ = Nat.card ↥(H0.map f) * Nat.card ↥(H0 ⊓ f.ker) := by
        rw [hrange, hker, Nat.card_congr (ggNSPosPC_subgroupOfEquiv (H0 ⊓ f.ker) H0),
          show (H0 ⊓ f.ker) ⊓ H0 = H0 ⊓ f.ker from inf_eq_left.mpr inf_le_left]

theorem ggNSPosPC_pow_pi_zmod {p n : ℕ} [NeZero p] (x : Fin n → Multiplicative (ZMod p)) :
    x ^ p = 1 := by
  funext l
  rw [Pi.pow_apply, Pi.one_apply]
  have hcard : Fintype.card (Multiplicative (ZMod p)) = p := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (ZMod p) = p
    exact Nat.card_zmod p
  have h := pow_card_eq_one (x := x l)
  rwa [hcard] at h

theorem ggNSPosPC_coe_ggPermSU_swap {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (i j : Fin n) :
    ((ggPermSU (K := K) (f := f) (Equiv.swap i j) : Su K 2 f n) : GL (Fin n) K) =
      CFSG.RankThree.Classical.permGL (Equiv.swap i j) := by
  apply Units.ext
  ext a b
  unfold CFSG.RankThree.Classical.permGL
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.swap_inv]
  rfl

end CFSG.StandardType

end
