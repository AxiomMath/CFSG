module

public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.GroupTheory.WeirSylow

theorem f4_card_orthogonal {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hdim : Module.finrank (ZMod 2) W = 6) (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hS : ∃ S : Submodule (ZMod 2) W, Module.finrank (ZMod 2) S = 3 ∧ ∀ s ∈ S, q s = 0) :
    Nat.card (orthogonalSubgroupOf q) = 40320 := by
  have hB00 : B 0 0 = 0 := by simp
  have hq0 : q 0 = 0 := by
    have h := hq 0 0
    rw [add_zero, hB00] at h
    simpa using h
  have hpolar : ∀ x y, q (x + y) - q x - q y = B x y := fun x y => by
    linear_combination hq x y
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    have h1 := hpolar x y
    have h2 := hpolar y x
    rw [add_comm y x] at h2
    linear_combination h2 - h1
  let Q : QuadraticForm (ZMod 2) W :=
    { toFun := q
      toFun_smul := fun a v => by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a with rfl | rfl
        · simp [hq0]
        · simp
      exists_companion' := ⟨B, fun x y => hq x y⟩ }
  have hPlus : IsPlusType Q := by
    obtain ⟨S, hS3, hSs⟩ := hS
    exact ⟨S, by omega, fun x hx => hSs x hx⟩
  have hord := natCard_orthogonalGroup_of_type (K := ZMod 2) (V := W) (Q := Q)
    (by
      unfold LinearMap.Nondegenerate
      refine ⟨fun m hm => hB m (fun w => ?_), fun n hn => hB n (fun w => ?_)⟩
      · have h2 := hm w
        rw [QuadraticMap.polarBilin_apply_apply] at h2
        have h1 : q (m + w) - q m - q w = 0 := h2
        linear_combination h1 - hpolar m w
      · have h2 := hn w
        rw [QuadraticMap.polarBilin_apply_apply] at h2
        have h1 : q (w + n) - q w - q n = 0 := h2
        rw [hsymm n w]
        linear_combination h1 - hpolar w n)
    (m := 2) (by omega) (ε := 1) (Or.inl ⟨rfl, hPlus⟩)
  have hK : Nat.card (ZMod 2) = 2 := by simp
  rw [hK] at hord
  simp only [Nat.cast_ofNat] at hord
  have hprod : ∏ i ∈ Finset.Icc 1 2, (((2 : ℤ) ^ 2) ^ i - 1) = 45 := by decide
  have hnum : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 40320 := by
    rw [hord, hprod]
    norm_num
  have hO : orthogonalSubgroupOf q = TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.ext fun γ => by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      exact Iff.rfl
  rw [hO]
  exact_mod_cast hnum

end CFSG.Quasithin.H13.C1294
