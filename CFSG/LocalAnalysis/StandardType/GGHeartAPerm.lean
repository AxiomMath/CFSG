module

public import CFSG.LocalAnalysis.StandardType.GGWAutCommon
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112AModel
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLinPerm
public import CFSG.Permutation.SymmetricCoxeter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin
open CFSG.Permutation.SymmetricCoxeter

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggHAP_coeff_adj {r : ℕ} {i j : Fin r} (hne : i ≠ j)
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : CartanMatrix.A r i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne, if_pos h]

private lemma ggHAP_coeff_other {r : ℕ} {i j : Fin r} (hne : i ≠ j)
    (h1 : i.val + 1 ≠ j.val) (h2 : j.val + 1 ≠ i.val) : CartanMatrix.A r i j = 0 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hne,
    if_neg (show ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) from fun h => h.elim h1 h2)]

private noncomputable def ggHAP_refl {H : Type} [AddCommGroup H] [Module (ZMod 3) H] {r : ℕ}
    (h : Fin r → H) (α : Fin r → Module.Dual (ZMod 3) H) (hpair : ∀ i, α i (h i) = 2)
    (i : Fin r) : H ≃ₗ[ZMod 3] H :=
  Module.reflection (hpair i)

private lemma ggHAP_refl_sq {H : Type} [AddCommGroup H] [Module (ZMod 3) H]
    {x : H} {f : Module.Dual (ZMod 3) H} (hfx : f x = 2) :
    Module.reflection hfx * Module.reflection hfx = 1 := by
  ext v
  simp [Module.involutive_reflection hfx v]

private lemma ggHAP_refl_braid {H : Type} [AddCommGroup H] [Module (ZMod 3) H]
    {x y : H} {f g : Module.Dual (ZMod 3) H}
    (hfx : f x = 2) (hgy : g y = 2) (hfy : f y = -1) (hgx : g x = -1) :
    Module.reflection hfx * Module.reflection hgy * Module.reflection hfx =
      Module.reflection hgy * Module.reflection hfx * Module.reflection hgy := by
  ext v
  simp only [LinearEquiv.mul_apply, Module.reflection_apply, map_sub, map_smul,
    hfx, hgy, hfy, hgx]
  module

private lemma ggHAP_refl_braid_apply {H : Type} [AddCommGroup H] [Module (ZMod 3) H]
    {x y : H} {f g : Module.Dual (ZMod 3) H}
    (hfx : f x = 2) (hgy : g y = 2) (hfy : f y = -1) (hgx : g x = -1) :
    (Module.reflection hfx * Module.reflection hgy) x = y := by
  simp only [LinearEquiv.mul_apply, Module.reflection_apply, map_sub, map_smul,
    hfx, hfy, hgx]
  module

private lemma ggHAP_refl_comm {H : Type} [AddCommGroup H] [Module (ZMod 3) H]
    {x y : H} {f g : Module.Dual (ZMod 3) H}
    (hfx : f x = 2) (hgy : g y = 2) (hfy : f y = 0) (hgx : g x = 0) :
    Module.reflection hfx * Module.reflection hgy =
      Module.reflection hgy * Module.reflection hfx := by
  ext v
  simp only [LinearEquiv.mul_apply, Module.reflection_apply, map_sub, map_smul,
    hfy, hgx]
  module

private lemma ggHAP_isLinRefl_of_isReflLin {H : Type} [AddCommGroup H] [Module (ZMod 3) H]
    {t : H ≃ₗ[ZMod 3] H} (h : IsReflLin t) : IsLinRefl t := by
  obtain ⟨c, φ, hφ, rfl⟩ := h
  exact ⟨c, φ, hφ, fun v => by rw [Module.reflection_apply]⟩

theorem ggHA_perm {H : Type} [AddCommGroup H] [Module (ZMod 3) H] {r : ℕ} (hr : 4 ≤ r)
    (h : Fin r → H) (α : Fin r → Module.Dual (ZMod 3) H)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A r i j : ℤ) : ZMod 3)) :
    ∃ Ψ : Equiv.Perm (Fin (r + 1)) →* (H ≃ₗ[ZMod 3] H), Function.Injective Ψ ∧
      (∀ (i : Fin r) (v : H), Ψ (Equiv.swap i.castSucc i.succ) v = v - α i v • h i) ∧
      ∀ σ : Equiv.Perm (Fin (r + 1)), GGLinRefl (Ψ σ) → σ ∈ ggTransp (r + 1) := by
  have hpair : ∀ i : Fin r, α i (h i) = 2 := by
    intro i
    rw [hα i i, ggQ2xKDa_coeff_self r i]
    norm_num
  let x : ℕ → H ≃ₗ[ZMod 3] H := fun k =>
    if hk : k < r then ggHAP_refl h α hpair ⟨k, hk⟩ else 1
  have hx : IsCoxeterA r x := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      rw [show x i = ggHAP_refl h α hpair ⟨i, hi⟩ by simp [x, hi]]
      exact ggHAP_refl_sq (hpair ⟨i, hi⟩)
    · intro i hi
      have hi' : i < r := by omega
      rw [show x i = ggHAP_refl h α hpair ⟨i, hi'⟩ by simp [x, hi'],
        show x (i + 1) = ggHAP_refl h α hpair ⟨i + 1, hi⟩ by simp [x, hi]]
      refine ggHAP_refl_braid (hpair ⟨i, hi'⟩) (hpair ⟨i + 1, hi⟩) ?_ ?_
      · rw [hα ⟨i, hi'⟩ ⟨i + 1, hi⟩,
          ggHAP_coeff_adj (by simp [Fin.ext_iff]) (Or.inl rfl)]
        norm_num
      · rw [hα ⟨i + 1, hi⟩ ⟨i, hi'⟩,
          ggHAP_coeff_adj (by simp [Fin.ext_iff]) (Or.inr rfl)]
        norm_num
    · intro i j hij hj
      have hi : i < r := by omega
      rw [show x i = ggHAP_refl h α hpair ⟨i, hi⟩ by simp [x, hi],
        show x j = ggHAP_refl h α hpair ⟨j, hj⟩ by simp [x, hj]]
      refine ggHAP_refl_comm (hpair ⟨i, hi⟩) (hpair ⟨j, hj⟩) ?_ ?_
      · rw [hα ⟨i, hi⟩ ⟨j, hj⟩,
          ggHAP_coeff_other (by simp [Fin.ext_iff]; omega)
            (by
              intro hh
              have h' : i + 1 = j := by simpa using hh
              omega)
            (by
              intro hh
              have h' : j + 1 = i := by simpa using hh
              omega)]
        norm_num
      · rw [hα ⟨j, hj⟩ ⟨i, hi⟩,
          ggHAP_coeff_other (by simp [Fin.ext_iff]; omega)
            (by
              intro hh
              have h' : j + 1 = i := by simpa using hh
              omega)
            (by
              intro hh
              have h' : i + 1 = j := by simpa using hh
              omega)]
        norm_num
  obtain ⟨Ψ, hΨ⟩ := exists_hom_perm r x hx
  have hΨ_swap : ∀ i : Fin r, Ψ (Equiv.swap i.castSucc i.succ) = ggHAP_refl h α hpair i := by
    intro i
    have h1 := hΨ i i.isLt
    rw [adjSwap_of_lt i.isLt] at h1
    rw [show x i = ggHAP_refl h α hpair i by simp [x, i.isLt]] at h1
    rw [show Equiv.swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩ = Equiv.swap i.castSucc i.succ by
      rfl] at h1
    exact h1
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    by_contra hne
    have hNt : Nontrivial Ψ.ker := by
      rw [Subgroup.nontrivial_iff_exists_ne_one]
      exact ⟨σ, by rwa [MonoidHom.mem_ker], hne⟩
    have hcard : 5 ≤ Nat.card (Fin (r + 1)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    have hA := Equiv.Perm.alternatingGroup_le_of_normal (N := Ψ.ker) hcard hNt
    let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨1, by omega⟩
    let i2 : Fin r := ⟨2, by omega⟩
    let a : Fin (r + 1) := ⟨0, by omega⟩
    let b : Fin (r + 1) := ⟨1, by omega⟩
    let c : Fin (r + 1) := ⟨2, by omega⟩
    have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
    have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
    have hcyc : Equiv.swap a b * Equiv.swap b c ∈ alternatingGroup (Fin (r + 1)) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
        Equiv.Perm.sign_swap hbc]
      decide
    have hmem : Ψ (Equiv.swap a b * Equiv.swap b c) = 1 :=
      MonoidHom.mem_ker.mp (hA hcyc)
    have ha : a = i0.castSucc := by ext; simp [a, i0]
    have hb : b = i0.succ := by ext; simp [b, i0]
    have hb' : b = i1.castSucc := by ext; simp [b, i1]
    have hc : c = i1.succ := by ext; simp [c, i1]
    have hs : ggHAP_refl h α hpair i0 * ggHAP_refl h α hpair i1 = 1 := by
      rw [map_mul] at hmem
      rw [show Equiv.swap a b = Equiv.swap i0.castSucc i0.succ by rw [ha, hb],
        show Equiv.swap b c = Equiv.swap i1.castSucc i1.succ by rw [hb', hc]] at hmem
      rwa [hΨ_swap i0, hΨ_swap i1] at hmem
    have hfy : α i0 (h i1) = -1 := by
      rw [hα i0 i1, ggHAP_coeff_adj (by simp [i0, i1, Fin.ext_iff]) (Or.inl rfl)]
      norm_num
    have hgx : α i1 (h i0) = -1 := by
      rw [hα i1 i0, ggHAP_coeff_adj (by simp [i0, i1, Fin.ext_iff]) (Or.inr rfl)]
      norm_num
    have hcomp : (ggHAP_refl h α hpair i0 * ggHAP_refl h α hpair i1) (h i0) = h i1 :=
      ggHAP_refl_braid_apply (hpair i0) (hpair i1) hfy hgx
    have hfix : (ggHAP_refl h α hpair i0 * ggHAP_refl h α hpair i1) (h i0) = h i0 := by
      rw [hs]; rfl
    have hnei : h i1 ≠ h i0 := by
      intro hh
      have h2 : α i2 (h i1) = -1 := by
        rw [hα i2 i1, ggHAP_coeff_adj (by simp [i2, i1, Fin.ext_iff]) (Or.inr rfl)]
        norm_num
      have h0 : α i2 (h i0) = 0 := by
        rw [hα i2 i0,
          ggHAP_coeff_other (by simp [i2, i0, Fin.ext_iff]) (by simp [i2, i0])
            (by simp [i2, i0])]
        norm_num
      rw [hh] at h2
      rw [h2] at h0
      norm_num at h0
    exact hnei (by rw [← hcomp, hfix])
  have hsw : ∀ u v : Fin (r + 1), u ≠ v → IsLinRefl (Ψ (Equiv.swap u v)) := by
    intro u v huv
    let i0 : Fin r := ⟨0, by omega⟩
    have hrefl0 : IsReflLin (Ψ (Equiv.swap i0.castSucc i0.succ)) := by
      rw [hΨ_swap i0]
      exact ⟨h i0, α i0, hpair i0, rfl⟩
    have hconj : IsConj (Equiv.swap i0.castSucc i0.succ) (Equiv.swap u v) :=
      Equiv.Perm.isConj_swap (by simp [i0, Fin.ext_iff]) huv
    obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
    have heq : Ψ τ * Ψ (Equiv.swap i0.castSucc i0.succ) * (Ψ τ)⁻¹ = Ψ (Equiv.swap u v) := by
      rw [← map_mul, ← map_inv, ← map_mul, hτ]
    rw [← heq]
    exact ggHAP_isLinRefl_of_isReflLin
      (ggQ2_isReflLin_conj (Ψ τ) (Ψ (Equiv.swap i0.castSucc i0.succ)) hrefl0)
  refine ⟨Ψ, hinj, ?_, ?_⟩
  · intro i v
    rw [hΨ_swap i]
    exact Module.reflection_apply v (hpair i)
  · intro σ hσ
    have hlin : IsLinRefl (Ψ σ) :=
      ggHAP_isLinRefl_of_isReflLin ((ggLinRefl_iff_isReflLin (Ψ σ)).mp hσ)
    have hswap : σ.IsSwap :=
      isSwap_of_isLinRefl (p := 3) (by decide : (3 : ℕ) ≠ 2) Ψ hinj hsw hlin
    rw [ggTransp]
    exact hswap

end CFSG.StandardType

end
