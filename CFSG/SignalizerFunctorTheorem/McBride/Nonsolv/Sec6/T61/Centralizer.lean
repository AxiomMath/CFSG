module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Types
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61.Maximal
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T61.Wreath

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem card_lcal_thetaOf_special
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) : Nat.card (lcal (thetaOf θ E)) = p ^ 2 := by
  have hc := h.card_lcal_mul_card_bN_line core.mem
  rw [core.bN_eq E core.mem, sup_idem, core.mem.2] at hc
  exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 1) (hc.trans (by ring))

theorem card_lcal_thetaOf_ne
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk p 1 A)
    (hFE : F ≠ E) : Nat.card (lcal (thetaOf θ F)) = p := by
  have hc := h.card_lcal_mul_card_bN_line hF
  rw [core.bN_eq F hF, (h.sup_mem_E2_of_ne hF core.mem hFE).2] at hc
  exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 2) (hc.trans (by ring))

theorem wreath_F'_of_core
    (h : Counterexample p A θ) {E K : Subgroup G}
    (core : TypeBCore p A θ E K) : ∀ F ∈ signalizerFunctorEk p 1 A, F ≠ E → ∃ L : Subgroup G,
      IsWreath (thetaOf θ F ⊔ A) L A (E ⊔ F) F ∧ Nonempty (↥L ≃* ↥K) := by
  intro F hF hFE
  obtain ⟨L, C, hW, ⟨e⟩⟩ := core.wreath_F F hF hFE
  refine ⟨L, ?_, ⟨e⟩⟩
  suffices hCF : C = F from hCF ▸ hW
  have hFA : F ≤ A := hF.1
  have hF0 : F ≠ ⊥ := h.ne_bot_of_mem_E1 hF
  have hLs : IsSimpleGroup L := e.isSimpleGroup_congr.mpr core.simple_K.1
  have hnc : ¬ IsMulCommutative L := fun hc => core.simple_K.2 ((isMulCommutative_congr e).mp hc)
  have hLmem : L ∈ lcal (thetaOf θ F) :=
    T61.mem_lcal_of_isWreath (h.isFunctor.normalizes_thetaOf hFA) hW hLs hnc
  obtain ⟨hC1, hC2⟩ := h.lemma_6_9_a hFA hF0
  have hCbC : C = bC A θ F := by rw [hW.C_eq, hC2 L hLmem]
  have hNbN : bN A θ F = A ⊓ Subgroup.normalizer (L : Set G) := h.lemma_6_9_b hFA hF0 L hLmem
  have hbN : bN A θ F = F ⊔ E := core.bN_eq F hF
  have hFC : F ≤ C := by
    rw [hCbC, hC1]
    exact le_inf hFA (Subgroup.le_centralizer_iff.mpr (h.isFunctor.thetaOf_le_centralizer hFA))
  have hCN : C ≤ F ⊔ E := by
    intro c hc
    have hc' : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hW.C_eq ▸ hc
    rw [← hbN, hNbN]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hc').1,
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hc').2⟩
  have hsupcard : Nat.card ↥(F ⊔ E) = p ^ 2 := (h.sup_mem_E2_of_ne hF core.mem hFE).2
  have hEC : ¬ E ≤ C := by
    intro hEC
    obtain ⟨f, hfF, hf1⟩ := h.exists_ne_one_of_mem_E1 hF
    have hHF : thetaOf θ F = θ f := h.thetaOf_line hF hfF hf1
    have hFeq : F = Subgroup.zpowers f := h.line_eq_zpowers hF hfF hf1
    have hEcen : E ≤ Subgroup.centralizer (thetaOf θ F : Set G) := by
      intro x hx
      have hx' : x ∈ bC A θ F := hCbC ▸ hEC hx
      rw [hC1] at hx'
      exact (Subgroup.mem_inf.mp hx').2
    have hcen : θ f ≤ Subgroup.centralizer (E : Set G) :=
      hHF ▸ Subgroup.le_centralizer_iff.mp hEcen
    have hle : θ f ≤ thetaOf θ E :=
      calc θ f = θ f ⊓ Subgroup.centralizer (E : Set G) := (inf_eq_left.mpr hcen).symm
        _ = thetaOf θ (Subgroup.zpowers f ⊔ E) :=
          h.isFunctor.inf_centralizer_eq_thetaOf (hFA hfF) hf1 core.mem.1
        _ ≤ thetaOf θ E := thetaOf_anti le_sup_right
    have hfE : f ∉ E := by
      intro hfE
      refine hFE ?_
      rw [hFeq]
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfE)
        (by rw [core.mem.2, h.card_zpowers (hFA hfF) hf1, pow_one])
    have hmax := h.maximal_of_core core f (hFA hfF) hfE
    rw [h.isFunctor.thetaOf_zpowers (hFA hfF) hf1] at hmax
    have hEF : thetaOf θ E = θ f :=
      le_antisymm (hmax.2 (h.thetaOf_mem_msig core.mem.1 (h.ne_bot_of_mem_E1 core.mem)) hle) hle
    have hcE := h.card_lcal_thetaOf_special core
    rw [hEF, ← hHF, h.card_lcal_thetaOf_ne core hF hFE] at hcE
    have h1 := h.prime.one_lt
    nlinarith
  obtain ⟨j, hj, hjC⟩ := (Nat.dvd_prime_pow h.prime).1
    (hsupcard ▸ Subgroup.card_dvd_of_le hCN)
  interval_cases j
  · exfalso
    have := Subgroup.card_le_of_le hFC
    rw [hF.2, hjC] at this
    simp at this
    exact absurd this (not_le.mpr h.prime.one_lt)
  · exact (Subgroup.eq_of_le_of_card_ge hFC (by rw [hjC, hF.2])).symm
  · exact (hEC ((Subgroup.eq_of_le_of_card_ge hCN (by rw [hjC, hsupcard])) ▸ le_sup_right)).elim

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
