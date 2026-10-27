module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L62b
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Step1
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64.Quot

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem inf_centralizer_sSup_eq_bot (h : Counterexample p A θ) :
    A ⊓ Subgroup.centralizer ((sSup (Msig p A θ) : Subgroup G) : Set G) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ ha =>
    h.eq_one_of_mem_centralizer_sSup_msig (Subgroup.mem_inf.mp ha).1 (Subgroup.mem_inf.mp ha).2

theorem inf_eq_bot_of_normal (h : Counterexample p A θ) {M : Subgroup G}
    (hMW : M ≤ sSup (Msig p A θ)) (hMn : (M.subgroupOf (sSup (Msig p A θ))).Normal)
    (hMA : A ≤ Subgroup.normalizer (M : Set G)) (hMne : M ≠ sSup (Msig p A θ)) :
    ∀ a ∈ A, a ≠ 1 → θ a ⊓ M = ⊥ := by
  obtain ⟨U, hU, hUn, hle⟩ := h.exists_normal_member_of_normal hMW hMn hMA hMne
  have hU1 : U = ⊥ := h.noNormalMember hU
  exact fun a ha ha1 => eq_bot_iff.mpr ((hle a ha ha1).trans hU1.le)

theorem exists_card_quotient (h : Counterexample p A θ) {Z : Subgroup G}
    (hZ : Z ≤ zOf (sSup (Msig p A θ))) (hZA : A ≤ Subgroup.normalizer (Z : Set G))
    (hZ1 : Z ≠ ⊥) :
    ∃ m : ℕ, Nat.card (sSup (Msig p A θ) : Subgroup G) = Nat.card Z * m ∧ Nat.Coprime p m := by
  have := h.normal_of_le_zOf hZ hZA
  obtain ⟨N, hN, hWN, -⟩ := h.exists_quotient_member hZ hZ1
  refine ⟨Nat.card ((sSup (Msig p A θ)).map (QuotientGroup.mk' Z)), ?_, ?_⟩
  · rw [mul_comm, card_map_mk'_mul_card (hZ.trans (Subgroup.map_subtype_le _))]
  · exact hN.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hWN)

theorem exists_mul_of_mem_centralizer (h : Counterexample p A θ) {Z : Subgroup G}
    (hZ : Z ≤ zOf (sSup (Msig p A θ))) (hZA : A ≤ Subgroup.normalizer (Z : Set G))
    (hZ1 : Z ≠ ⊥) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) {w : G}
    (hw : w ∈ sSup (Msig p A θ)) (hwb : w ∈ Subgroup.centralizer {b}) :
    ∃ z ∈ Z, ∃ t ∈ θ b, w = z * t := by
  have := h.normal_of_le_zOf hZ hZA
  obtain ⟨N, -, hWN, hfix⟩ := h.exists_quotient_member hZ hZ1
  have hmem : QuotientGroup.mk' Z w ∈ N ⊓ Subgroup.centralizer {QuotientGroup.mk' Z b} := by
    refine Subgroup.mem_inf.mpr ⟨hWN (Subgroup.mem_map_of_mem _ hw), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul] using
      congrArg (QuotientGroup.mk' Z) (Subgroup.mem_centralizer_singleton_iff.mp hwb)
  obtain ⟨t, ht, hwt⟩ := hfix b hb hb1 hmem
  refine ⟨w * t⁻¹, ?_, t, ht, by group⟩
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hwt, mul_inv_cancel]

theorem hypB_map_sSup (h : Counterexample p A θ) {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ zOf (sSup (Msig p A θ))) (_hZA : A ≤ Subgroup.normalizer (Z : Set G))
    (hZ1 : Z ≠ ⊥) :
    signalizerMcBrideHypothesisB p ((sSup (Msig p A θ)).map (QuotientGroup.mk' Z)) := by
  obtain ⟨N, hN, hWN, -⟩ := h.exists_quotient_member hZ hZ1
  exact hypB_mono hWN hN

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
