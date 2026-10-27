module

public import CFSG.Quasithin.Background.B5Inputs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem outAbelian_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : OutAbelian L) : OutAbelian L' := by
  intro φ ψ
  have hmem : ⁅(MulAut.congr e).symm φ, (MulAut.congr e).symm ψ⁆ ∈ inner L := h _ _
  have himg : MulAut.congr e ⁅(MulAut.congr e).symm φ, (MulAut.congr e).symm ψ⁆ ∈ inner L' := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
    exact ⟨_, hmem, rfl⟩
  rwa [map_commutatorElement, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at himg

theorem outAbelian_of_isMulCommutative_outer {L : Type} [Group L]
    (h : IsMulCommutative (Outer L)) : OutAbelian L := by
  intro φ ψ
  have h1 : (QuotientGroup.mk' (inner L)) ⁅φ, ψ⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h.is_comm.comm _ _
  exact (QuotientGroup.eq_one_iff (N := inner L) _).mp h1

theorem outAbelian_of_card_outer_le_four {L : Type} [Group L] [Finite (Outer L)]
    (h : Nat.card (Outer L) ≤ 4) : OutAbelian L :=
  outAbelian_of_isMulCommutative_outer
    (CFSG.ComponentClassification.CatalogueSchreierAlternating.commutative_of_card_le_four h)

theorem outAbelian_alternatingGroup {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    OutAbelian ↥(alternatingGroup (Fin n)) := by
  by_cases h6 : n = 6
  · subst h6
    exact outAbelian_of_isMulCommutative_outer
      CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_commutative
  · have hdvd := CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_card_dvd_two_of_equiv_outside_six
      (n := n) (by omega) (MulEquiv.refl ↥(alternatingGroup (Fin n)))
    have hne : Nat.card (Outer ↥(alternatingGroup (Fin n))) ≠ 0 :=
      fun h0 => by rw [h0] at hdvd; exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by norm_num)
    have : Finite (Outer ↥(alternatingGroup (Fin n))) := Nat.finite_of_card_ne_zero hne
    exact outAbelian_of_card_outer_le_four (Nat.le_of_dvd (by norm_num) hdvd |>.trans (by norm_num))

theorem nonempty_commutator_equiv_alternating {Ω : Type*} [Group Ω] {M : Subgroup Ω} {n : ℕ}
    (hn : 5 ≤ n) (e : ↥M ≃* Equiv.Perm (Fin n)) :
    Nonempty (↥⁅M, M⁆ ≃* ↥(alternatingGroup (Fin n))) := by
  have hA : commutator (Equiv.Perm (Fin n)) = alternatingGroup (Fin n) :=
    alternatingGroup.commutator_perm_eq (by simpa using hn)
  have hmap : (commutator ↥M).map e.toMonoidHom = alternatingGroup (Fin n) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 e.surjective, ← commutator_def, hA]
  have h1 : (commutator ↥M).map M.subtype = ⁅M, M⁆ := Subgroup.map_subtype_commutator M
  exact ⟨((MulEquiv.subgroupCongr h1.symm).trans
    (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm).trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap))⟩

theorem outAbelian_commutator_of_perm {Ω : Type} [Group Ω] {M : Subgroup Ω} {n : ℕ}
    (h5 : 5 ≤ n) (h8 : n ≤ 8) (e : ↥M ≃* Equiv.Perm (Fin n)) : OutAbelian ↥⁅M, M⁆ := by
  obtain ⟨f⟩ := nonempty_commutator_equiv_alternating h5 e
  exact outAbelian_of_mulEquiv f.symm (outAbelian_alternatingGroup h5 h8)

theorem outAbelian_of_card_mulAut_le {G : Type} [Group G] [Finite G]
    (hc : Subgroup.center G = ⊥) (h : Nat.card (MulAut G) ≤ 2 * Nat.card G) : OutAbelian G := by
  have hker : (MulAut.conj : G →* MulAut G).ker = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
    have hcen : g ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have h1 := congrArg (fun φ : MulAut G => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    rwa [hc, Subgroup.mem_bot] at hcen
  have hinn : Nat.card (inner G) = Nat.card G := by
    have e : G ≃* (MulAut.conj : G →* MulAut G).range :=
      MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff _).mp hker)
    exact (Nat.card_congr e.toEquiv).symm
  have : Finite (MulAut G) :=
    Finite.of_injective (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective
  have hq := (inner G).card_eq_card_quotient_mul_card_subgroup
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hle : Nat.card (Outer G) ≤ 2 := by
    have h1 : Nat.card (Outer G) * Nat.card G ≤ 2 * Nat.card G := by
      calc Nat.card (Outer G) * Nat.card G = Nat.card (MulAut G) := by rw [hq, hinn]
        _ ≤ 2 * Nat.card G := h
    exact Nat.le_of_mul_le_mul_right h1 hpos
  exact outAbelian_of_card_outer_le_four (hle.trans (by norm_num))

theorem nonempty_commutator_equiv {Ω Ω' : Type*} [Group Ω] [Group Ω'] {M : Subgroup Ω}
    {M' : Subgroup Ω'} (e : ↥M ≃* ↥M') : Nonempty (↥⁅M, M⁆ ≃* ↥⁅M', M'⁆) := by
  have hmap : (commutator ↥M).map e.toMonoidHom = commutator ↥M' := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 e.surjective, ← commutator_def]
  have h1 : (commutator ↥M).map M.subtype = ⁅M, M⁆ := Subgroup.map_subtype_commutator M
  have h2 : (commutator ↥M').map M'.subtype = ⁅M', M'⁆ := Subgroup.map_subtype_commutator M'
  exact ⟨((MulEquiv.subgroupCongr h1.symm).trans
    (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm).trans
      ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        ((MulEquiv.subgroupCongr hmap).trans
          ((Subgroup.equivMapOfInjective _ M'.subtype M'.subtype_injective).trans
            (MulEquiv.subgroupCongr h2))))⟩

end CFSG.Quasithin
