module

public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYE6
public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYCore
import CFSG.LocalAnalysis.StandardType.FF81.FrameAut

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT (blockSL2 blockSL)
open Blocks
open scoped MatrixGroups

theorem coe_rhoE : ((rhoE : SL(2, ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1] := by
  decide

@[expose] def SevenTwoAt (n : ℕ) [NeZero n] : Prop :=
  ∀ (G : Type) [Group G] (L' : Subgroup G) (φ : ↥L' ≃* SL(n + 1, ZMod 2)) (w : ↥L'),
    φ w = blockSL2 (ZMod 2) n 0 rhoE → ∀ x : G, x ∈ Subgroup.normalizer (L' : Set G) →
      Nat.Coprime (orderOf x) 3 → x * (w : G) = w * x →
      (∀ B : SL(n - 1, ZMod 2), x * (φ.symm (blockSL (ZMod 2) (n + 1) (n - 1) 2
        (by have := NeZero.pos n; omega) B) : G) =
          (φ.symm (blockSL (ZMod 2) (n + 1) (n - 1) 2 (by have := NeZero.pos n; omega) B) :
            G) * x) →
      ∀ y ∈ L', x * y = y * x

@[expose] def TOneCentAt (n : ℕ) : Prop :=
  ∀ g : SL(n + 2 + 1, ZMod 2),
    g * blockSL2 (ZMod 2) (n + 2) 0 rhoE = blockSL2 (ZMod 2) (n + 2) 0 rhoE * g →
      ∃ a : ℕ, ∃ B : SL(n + 2 - 1, ZMod 2),
        g = blockSL2 (ZMod 2) (n + 2) 0 rhoE ^ a *
          blockSL (ZMod 2) (n + 2 + 1) (n + 2 - 1) 2 (by omega) B

theorem constructY_of_72
    (h5 : SevenTwoAt 5) (h6 : SevenTwoAt 6) (hm5 : TOneCentAt 5) (hm6 : TOneCentAt 6) :
    ConstructY := by
  intro hC G _ _ _ _ _ n b L hA K t hU
  obtain ⟨-, -, hF⟩ := hU
  rcases hA.n_cases with rfl | rfl
  · have hcore := hF.core_of_72 hA coe_rhoE (h5 G)
    rcases hF.commute_one_five_or hA with h1n | ⟨ψg, hinj, hrange, hblk, hcomm⟩
    · exact ⟨hF.yLab_of_commute hC (Or.inl rfl) h1n, hF.L_le_join,
        hF.cen_b_of_commute_of_tOne (by norm_num) hA.ord h1n coe_rhoE hm5, hcore,
        hF.syl_of_commute (by norm_num) h1n⟩
    · obtain ⟨hlab, hcen, hsyl⟩ := hF.yData_e6 hC hA hinj hrange hblk hcomm
      exact ⟨Or.inr ⟨rfl, hlab⟩, hF.L_le_join, hcen, hcore, hsyl⟩
  · have hcore := hF.core_of_72 hA coe_rhoE (h6 G)
    have h1n := hF.commute_one_six hA
    exact ⟨hF.yLab_six hC hA, hF.L_le_join,
      hF.cen_b_of_commute_of_tOne (by norm_num) hA.ord h1n coe_rhoE hm6, hcore,
      hF.syl_of_commute (by norm_num) h1n⟩

private theorem rhoE_eq_rhoTwo : rhoE = rhoTwo :=
  Subtype.ext coe_rhoE

theorem sevenTwoAt_of_four_le {n : ℕ} [NeZero n] (hn : 4 ≤ n) : SevenTwoAt n := by
  intro G _ L' φ w hw x hxN hx3 hxw hxJ
  exact commute_of_commute_centralizer hn φ (by rw [hw, rhoE_eq_rhoTwo]; rfl) hxN hx3 hxw hxJ

theorem tOneCentAt_holds (n : ℕ) : TOneCentAt n := by
  intro g hg
  rw [rhoE_eq_rhoTwo] at hg
  obtain ⟨a, B, h⟩ := (mem_centralizer_tOne_iff (n := n + 2)).mp hg
  exact ⟨a, B, by rw [rhoE_eq_rhoTwo]; exact h⟩

theorem constructY_holds :
    ConstructY :=
  constructY_of_72 (sevenTwoAt_of_four_le (by norm_num)) (sevenTwoAt_of_four_le (by norm_num))
    (tOneCentAt_holds 5) (tOneCentAt_holds 6)

end CFSG.StandardType.FF81
