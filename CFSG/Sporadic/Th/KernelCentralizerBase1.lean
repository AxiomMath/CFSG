
module

public import CFSG.Sporadic.Th.KernelCentralizerBase

public import CFSG.Sporadic.Th.KernelOrder

@[expose] public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.Th.Max3 TauCeti Pointwise MulAction

variable (h : KernelFacts)
include h

theorem card_fix_le : Nat.card {p : Om // gen 0 • p = p} ≤ 10200 := by
  classical
  have := h.finite
  have hP := card_P_eq h
  obtain ⟨v, hv0, hcov, hstab, hfix, hK, hcl, -⟩ := h.dce hP
  obtain ⟨-, hKc, hc, -, hlab⟩ := orbitData hP hv0 hcov hstab hK
  have : Fintype Om := Fintype.ofFinite Om
  have hcent : Nat.card (Subgroup.centralizer ({aK} : Set K)) ≤ 774144 := by
    have h1 := card_centralizer_mul_ncard aK
    have hmemK : ∀ k : {k : P // ∃ g ∈ K, g * gen 0 * g⁻¹ = k}, k.1 ∈ K := by
      intro k
      obtain ⟨g, hg, hk⟩ := k.2
      rw [← hk]
      exact K.mul_mem (K.mul_mem hg aK.2) (K.inv_mem hg)
    have hmemC : ∀ k : {k : P // ∃ g ∈ K, g * gen 0 * g⁻¹ = k},
        (⟨k.1, hmemK k⟩ : K) ∈ conjugatesOf aK := by
      intro k
      obtain ⟨g, hg, hk⟩ := k.2
      exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hk⟩
    have h2 : 819 ≤ (conjugatesOf aK).ncard := by
      refine hcl.trans ?_
      rw [← Nat.card_coe_set_eq]
      refine Nat.card_le_card_of_injective (fun k => ⟨⟨k.1, hmemK k⟩, hmemC k⟩) ?_
      intro x y hxy
      have e : x.1 = y.1 := congrArg (fun z : conjugatesOf aK => ((z : K) : P)) hxy
      exact Subtype.ext e
    have h3 := Nat.mul_le_mul_left (Nat.card (Subgroup.centralizer ({aK} : Set K))) h2
    rw [h1, hKc] at h3
    have h4 : Nat.card (Subgroup.centralizer ({aK} : Set K)) * 819 ≤ 774144 * 819 :=
      h3.trans (by norm_num)
    exact Nat.le_of_mul_le_mul_right h4 (by norm_num)
  have hD : ∀ D, Nat.card {p : Om // lab v hc p = D ∧ gen 0 • p = p} ≤ fD D := by
    intro D
    have e : Nat.card {p : Om // lab v hc p = D ∧ gen 0 • p = p} =
        Nat.card {p : orb (v D) // aK • p = p} := by
      refine Nat.card_congr ⟨fun p => ⟨⟨p.1, (hlab _ _).2 p.2.1⟩, Subtype.ext p.2.2⟩,
        fun p => ⟨p.1.1, (hlab _ _).1 p.1.2, congrArg Subtype.val p.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [e]
    by_cases hD0 : D = 0
    · subst hD0
      have : Subsingleton (orb (v 0)) := by
        rw [hv0, orb_one]
        infer_instance
      exact (Finite.card_le_one_iff_subsingleton.2 inferInstance).trans (by rfl)
    · have h1 := fix_orb_le (v D) aK (hstab D) (hfix D hD0) hcent
      rw [fD_spec D hD0]
      exact (Nat.le_div_iff_mul_le (mD_pos D)).2 h1
  calc Nat.card {p : Om // gen 0 • p = p}
      = ∑ D, Nat.card {p : Om // lab v hc p = D ∧ gen 0 • p = p} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
        rw [Finset.card_eq_sum_card_fiberwise (f := lab v hc) (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun D _ => ?_
        congr 1
        ext p
        simp [and_comm]
    _ ≤ ∑ D, fD D := Finset.sum_le_sum fun D _ => hD D
    _ = 10200 := sum_fD

theorem exists_equiv : ∃ e : P ≃* J,
    (∀ i < 7, e (gen i) ∈ H ∧ e (gen i) • Wset = Wset) ∧ e (gen 0) ^ 2 = 1 := by
  obtain ⟨ψ, hb, hK, h2⟩ := exists_psi h
  exact ⟨MulEquiv.ofBijective ψ hb, hK, h2⟩

theorem gen_zero_ne_one : gen 0 ≠ (1 : P) := by
  intro h1
  have := h.finite
  obtain ⟨v, -, -, -, -, -, hcl, -⟩ := h.dce (card_P_eq h)
  have : Nat.card {k : P // ∃ g ∈ K, g * gen 0 * g⁻¹ = k} ≤ 1 := by
    refine Finite.card_le_one_iff_subsingleton.2 ⟨fun x y => Subtype.ext ?_⟩
    obtain ⟨g, -, hx⟩ := x.2
    obtain ⟨g', -, hy⟩ := y.2
    rw [← hx, ← hy, h1]
    group
  omega

end CFSG.Sporadic.Th.Kernel
