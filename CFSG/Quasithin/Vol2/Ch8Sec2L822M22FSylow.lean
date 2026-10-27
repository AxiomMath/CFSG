module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.M22F

open CFSG.Quasithin

theorem padic_mul_m22f {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat 2 (a * b) = padicValNat 2 a + padicValNat 2 b :=
  padicValNat.mul ha hb

theorem rk_map_eq_range_m22f {H N : Type} [Group H] [Group N] [Finite H] [Finite N]
    (φ : H →* N) (P : Subgroup H) (hP : rk P = rk H) :
    rk ↥(P.map φ) = rk ↥φ.range := by
  have hA : Nat.card φ.ker * Nat.card φ.range = Nat.card H := Subgroup.card_ker_mul_card_range φ
  have hArk : rk H = rk ↥φ.ker + rk ↥φ.range := by
    unfold rk
    rw [← hA, padic_mul_m22f (Nat.card_pos.ne') (Nat.card_pos.ne')]
  set ψ : P →* N := φ.comp P.subtype with hψdef
  have hB : Nat.card ψ.ker * Nat.card ψ.range = Nat.card P := Subgroup.card_ker_mul_card_range ψ
  have hBr : ψ.range = P.map φ := by
    rw [hψdef, MonoidHom.range_comp, Subgroup.range_subtype]
  have hBk : Nat.card ψ.ker = Nat.card ↥(P ⊓ φ.ker) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.mpr ⟨x.1.2, ?_⟩⟩
        invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.mp y.2).1⟩, ?_⟩
        left_inv := fun x => Subtype.ext (Subtype.ext rfl)
        right_inv := fun y => Subtype.ext rfl }
    · have hx := MonoidHom.mem_ker.mp x.2
      exact MonoidHom.mem_ker.mpr hx
    · have hy := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp y.2).2
      exact MonoidHom.mem_ker.mpr hy
  have hPrk : rk P = rk ↥(P ⊓ φ.ker) + rk ↥(P.map φ) := by
    have h := hB
    rw [hBr, hBk] at h
    unfold rk
    rw [← h, padic_mul_m22f (Nat.card_pos.ne') (Nat.card_pos.ne')]
  have hKle : rk ↥(P ⊓ φ.ker) ≤ rk ↥φ.ker := rk_mono inf_le_right
  have hPle : rk ↥(P.map φ) ≤ rk ↥φ.range := rk_mono (Subgroup.map_le_range φ P)
  omega

end CFSG.Quasithin.H13.M22F
