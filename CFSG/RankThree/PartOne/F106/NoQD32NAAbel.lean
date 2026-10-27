module

public import CFSG.RankThree.PartOne.F106.NoQD32NAOrb

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.GroupTheory

theorem false_of_invariant_abelian {T : Type} [Group T] {E R : Subgroup T}
    (hE : IsElementaryAbelian 3 E) (h : InducesQD32 E R) (hE81 : Nat.card E = 81)
    (pr : T → Prop) (hconj : ∀ n x : T, pr (n * x * n⁻¹) ↔ pr x) {N : ℕ} (hN : ¬ 16 ∣ N)
    (hcount : Nat.card {x : ↥E // (x : T) ≠ 1 ∧ pr (x : T)} = N) : False := by
  classical
  obtain ⟨ψ, hψs, hψc⟩ := h.hom
  have : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE81]; norm_num)
  have hEcube : ∀ a ∈ E, a ^ 3 = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := 3) a ha
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have : Fintype ↥E := Fintype.ofFinite _
  let A : Finset ↥E := Finset.univ.filter fun x => (x : T) ≠ 1 ∧ pr (x : T)
  have hAcard : A.card = N := by
    have h1 : A.card = Nat.card {x : ↥E // (x : T) ≠ 1 ∧ pr (x : T)} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h1]
    exact hcount
  obtain ⟨f, hf⟩ := exists_qd32_embedding_normalizerRange h.normalizes ψ hψs hψc
  let f' : QD32 →* MulAut ↥E := E.normalizerMonoidHom.range.subtype.comp f
  have hf' : Function.Injective f' := Subtype.val_injective.comp hf
  have hinv : ∀ q : QD32, ∀ x ∈ A, f' q x ∈ A := by
    intro q x hx
    obtain ⟨n, hn⟩ := (f q).2
    have hcoe : ((f' q x : ↥E) : T) = (n : T) * (x : T) * (n : T)⁻¹ := by
      have : f' q = E.normalizerMonoidHom n := hn.symm
      rw [this]
      exact Subgroup.normalizerMonoidHom_apply_apply_coe E n x
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hcoe]
    refine ⟨fun h1 => hx.1 ?_, (hconj _ _).mpr hx.2⟩
    have : (x : T) = (n : T)⁻¹ * 1 * (n : T) := by
      rw [← h1]
      group
    simpa using this
  have h16 := qd32_dvd_card_of_invariant_nonzero Nat.prime_three (by norm_num)
    (fun x y => Subtype.ext (hEcomm x x.2 y y.2)) (fun x => Subtype.ext (hEcube x x.2)) f' hf'
    (by rw [hE81]; norm_num) A (by simp [A]) hinv
  rw [hAcard] at h16
  exact hN h16

end CFSG.RankThree.PartOne.F106
