module

public import CFSG.RankThree.CentralExtension.InvariantComplement

public section

namespace CFSG.RankThree.CentralExtension

open Subgroup
open scoped commutatorElement

variable {U Q : Type*} [Group U] [Group Q]

theorem extraspecial_scalar_central_extension_unique_complement {p : ℕ} [hp : Fact p.Prime]
    [Finite U] (π : U →* Q) (hπ : Function.Surjective π) (hC : π.ker ≤ center U)
    (hCp : IsPGroup p π.ker) (hQexp : ∀ q : Q, q ^ p = 1) (hZQ : center Q = commutator Q)
    (hZcard : Nat.card (center Q) = p) (α : MulAut U) (hα : (orderOf α).Coprime p)
    (hαC : ∀ c ∈ π.ker, α c = c) (r : ZMod p) (hr2 : r ^ 2 ≠ 1) (hr3 : r ^ 3 ≠ 1)
    (hαV : ∀ u : U, (QuotientGroup.mk (π (α u)) : Q ⧸ center Q) =
      (QuotientGroup.mk (π u)) ^ r.val) :
    π.ker ⊓ commutator U = ⊥ ∧
      ∃ D : Subgroup U, ((∀ d ∈ D, α d ∈ D) ∧ π.ker ⊔ D = ⊤ ∧ π.ker ⊓ D = ⊥) ∧
        (∀ D' : Subgroup U, (∀ d ∈ D', α d ∈ D') → π.ker ⊔ D' = ⊤ → π.ker ⊓ D' = ⊥ →
          D' = D) ∧
        commutator U ≤ D ∧ D.Normal ∧ Function.Bijective (π.domRestrict D) ∧
        ∃ e : π.ker × D ≃* U, ∀ c d, e (c, d) = (c : U) * d := by
  have hαfin : IsOfFinOrder α := isOfFinOrder_of_finite α
  set A := zpowers α with hA
  have hAfix : ∀ a ∈ A, ∀ c ∈ π.ker, a c = c := zpowers_fix_of_fix hαfin hαC
  have hAcard : (Nat.card A).Coprime p := by rw [hA, Nat.card_zpowers]; exact hα
  set k := r.val with hk
  have hkr : (k : ZMod p) = r := ZMod.natCast_zmod_val r
  have hr : ∀ u : U, (π u ^ k)⁻¹ * π (α u) ∈ center Q := fun u =>
    (mk_eq_pow_iff_mem_center _ _ _).1 (hαV u)
  have hW := comap_center_le_center_of_scalar π hπ hC hQexp hZQ hZcard α hαC k hr
    (by rw [hkr]; exact hr3)
  have hUW : ∀ x y : U, ⁅x, y⁆ ∈ center U := fun x y =>
    hW (by rw [mem_comap, map_commutatorElement]; exact commutatorElement_mem_center_of_eq hZQ _ _)
  have hαcomm : ∀ x y : U, α ⁅x, y⁆ = ⁅x, y⁆ ^ (k * k) := by
    intro x y
    have hx : (x ^ k)⁻¹ * α x ∈ center U :=
      hW (by rw [mem_comap, map_mul, map_inv, map_pow]; exact hr x)
    have hy : (y ^ k)⁻¹ * α y ∈ center U :=
      hW (by rw [mem_comap, map_mul, map_inv, map_pow]; exact hr y)
    rw [map_commutatorElement, ← mul_inv_cancel_left (x ^ k) (α x),
      ← mul_inv_cancel_left (y ^ k) (α y), commutatorElement_mul_center_left hx,
      commutatorElement_mul_center_right hy, commutatorElement_pow_pow_of_mem_center (hUW x y)]
  have hU' : ∀ g ∈ commutator U, g ∈ center U ∧ g ^ p = 1 ∧ α g = g ^ (k * k) := by
    intro g hg
    simp only [_root_.commutator_def, commutator_def] at hg
    induction hg using closure_induction with
    | mem g hg =>
      obtain ⟨x, -, y, -, rfl⟩ := hg
      refine ⟨hUW x y, ?_, hαcomm x y⟩
      have hxp : x ^ p ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hQexp]
      rw [Commute.commutatorElement_pow_left
          (show Commute x ⁅x, y⁆ from mem_center_iff.1 (hUW x y) x) p,
        commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.1 (hC hxp) y).symm
    | one => exact ⟨one_mem _, one_pow _, by rw [map_one, one_pow]⟩
    | mul g h _ _ hg hh =>
      have hgh : Commute g h := (mem_center_iff.1 hg.1 h).symm
      exact ⟨mul_mem hg.1 hh.1, by rw [hgh.mul_pow, hg.2.1, hh.2.1, one_mul],
        by rw [map_mul, hg.2.2, hh.2.2, hgh.mul_pow]⟩
    | inv g _ hg =>
      exact ⟨inv_mem hg.1, by rw [inv_pow, hg.2.1, inv_one], by rw [map_inv, hg.2.2, inv_pow]⟩
  have hCU : π.ker ⊓ commutator U = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    obtain ⟨hcC, hcU⟩ := mem_inf.1 hc
    obtain ⟨-, hcp, hαc⟩ := hU' c hcU
    rw [hαC c hcC] at hαc
    rw [mem_bot]
    by_contra hne
    have hord : orderOf c = p := orderOf_eq_prime hcp hne
    nth_rewrite 1 [← pow_one c] at hαc
    rw [pow_eq_pow_iff_modEq, hord] at hαc
    apply hr2
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 hαc.symm
    push_cast at h
    rw [← hkr, sq, h]
  have hr1 : (k : ZMod p) ≠ 1 := by
    rw [hkr]
    intro h
    exact hr2 (by rw [h, one_pow])
  have hDmap : (autCommutator A).map π = ⊤ :=
    map_eq_top_of_scalar π hπ hQexp hZQ α
      (fun u => inv_mul_apply_mem_autCommutator u (mem_zpowers α)) k hr hr1
  obtain ⟨hinv, hsup, hinf, hcommD, hnormal, hbij, huniq⟩ :=
    invariant_complement_of_map_eq_top π hC hCp A hAcard hAfix hCU hDmap
  refine ⟨hCU, autCommutator A, ⟨fun d hd => hinv α (mem_zpowers α) d hd, hsup, hinf⟩, ?_,
    hcommD, hnormal, hbij, exists_mulEquiv_prod_of_central hC hsup hinf⟩
  intro D' hD' hsup' hinf'
  exact huniq D' (zpowers_invariant_of_invariant hαfin hD') hsup' hinf'

end CFSG.RankThree.CentralExtension
