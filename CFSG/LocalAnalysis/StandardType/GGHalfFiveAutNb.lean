module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbrBasic
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveAutL
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveAutK
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveAutCount

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

theorem card_automizer_nb_le (hAut : GGHalfAutWithin Bs L K) {N : Subgroup G}
    (hN : GGNbr p B x (dPrime x φ₁ φ₂) (sl3four.map φ₁) (bElt φ₁ φ₂) N) :
    Nat.card (ggAutomizer N Bs) ≤ 24 := by
  obtain ⟨e, he0, he1, he2, he3, hcomm, hpow, hgen, hindep⟩ := exists_bsBasis h
  let bt : ↥Bs := e 0 * e 1 * e 2 * e 3
  have hbt : (bt : G) = bElt φ₁ φ₂ := by
    show ((e 0 * e 1 * e 2 * e 3 : ↥Bs) : G) = bElt φ₁ φ₂
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, he0, he1, he2, he3, bElt_eq h]
  let P : MulAut ↥Bs → Prop := fun ψ => ∀ i : Fin 4, ∃ j : Fin 4,
    ψ (e i) = e j ∨ ψ (e i) = (e j)⁻¹
  have hone : P 1 := by
    intro i
    exact ⟨i, Or.inl rfl⟩
  have hmul : ∀ u v : MulAut ↥Bs, P u → P v → P (u * v) := by
    intro u v hu hv i
    obtain ⟨j, hj⟩ := hv i
    obtain ⟨k, hk⟩ := hu j
    refine ⟨k, ?_⟩
    rw [MulAut.mul_apply]
    rcases hj with hj | hj
    · rw [hj]
      rcases hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr hk
    · rw [hj, map_inv]
      rcases hk with hk | hk
      · exact Or.inr (by rw [hk])
      · exact Or.inl (by rw [hk, inv_inv])
  have hpowS : ∀ (u : MulAut ↥Bs) (n : ℕ), P u → P (u ^ n) := by
    intro u n hu
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hu
  have hinv : ∀ u : MulAut ↥Bs, P u → P u⁻¹ := by
    intro u hu
    have huinv : u⁻¹ = u ^ (orderOf u - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (orderOf_pos u),
        pow_orderOf_eq_one]
    rw [huinv]
    exact hpowS u (orderOf u - 1) hu
  let S : Subgroup (MulAut ↥Bs) :=
    { carrier := P
      mul_mem' := fun hu hv => hmul _ _ hu hv
      one_mem' := hone
      inv_mem' := fun hu => hinv _ hu }
  have hL : ggAutomizer L Bs ≤ S := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro φ hφ
    obtain ⟨h3, hrest⟩ := autL_pres h he0 he1 he2 he3 (Subgroup.subset_closure hφ)
    intro i
    by_cases hi : i = 3
    · subst hi
      exact ⟨3, Or.inl h3⟩
    · obtain ⟨j, _, hj⟩ := hrest i hi
      exact ⟨j, hj⟩
  have hK : ggAutomizer K Bs ≤ S := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro φ hφ
    obtain ⟨h0, hrest⟩ := autK_pres h he0 he1 he2 he3 (Subgroup.subset_closure hφ)
    intro i
    by_cases hi : i = 0
    · subst hi
      exact ⟨0, Or.inl h0⟩
    · obtain ⟨j, _, hj⟩ := hrest i hi
      exact ⟨j, hj⟩
  have hsup : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ S := sup_le hL hK
  have hA_le : ggAutomizer N Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro φ hφ
    obtain ⟨g, hgN, hgnorm, hconj⟩ := hφ
    exact hAut φ ⟨g, Subgroup.mem_top g, hgnorm, hconj⟩
  have hAS : ggAutomizer N Bs ≤ S := le_trans hA_le hsup
  have hA : ∀ φ ∈ ggAutomizer N Bs, ∀ i : Fin 4, ∃ j : Fin 4,
      φ (e i) = e j ∨ φ (e i) = (e j)⁻¹ := by
    intro φ hφ
    have h : P φ := hAS hφ
    exact h
  let T : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | φ bt = bt}
      mul_mem' := by
        intro u v hu hv
        show (u * v) bt = bt
        rw [MulAut.mul_apply, hv, hu]
      one_mem' := rfl
      inv_mem' := by
        intro u hu
        show u⁻¹ bt = bt
        have h : (u⁻¹ * u) bt = bt := by rw [inv_mul_cancel]; rfl
        rw [MulAut.mul_apply, hu] at h
        exact h }
  have hAT : ggAutomizer N Bs ≤ T := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro φ hφ
    obtain ⟨g, hgN, hgnorm, hconj⟩ := hφ
    show φ bt = bt
    apply Subtype.ext
    rw [hconj bt, hbt]
    have hgC : g ∈ Subgroup.centralizer ({bElt φ₁ φ₂} : Set G) := le_centralizer_of_nbr hN hgN
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC
    rw [hgC]
    group
  have hfix : ∀ φ ∈ ggAutomizer N Bs, φ (e 0 * e 1 * e 2 * e 3) = e 0 * e 1 * e 2 * e 3 := by
    intro φ hφ
    have h := hAT hφ
    change φ bt = bt at h
    exact h
  exact card_le_24_of_signed e hcomm hpow hgen hindep (ggAutomizer N Bs) hA hfix

end GGHalfCtx

end CFSG.StandardType

end
