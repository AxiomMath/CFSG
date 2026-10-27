module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NotConclBig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

theorem s16c1610_a3_of_isSym_three {A : Type} [Group A] {K : Subgroup A} (h : IsSym ↥K 3) :
    ∃ X : Subgroup A, X ≤ K ∧ Nat.card X = 3 ∧ ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ X := by
  obtain ⟨e⟩ := h
  refine ⟨(alternatingGroup (Fin 3)).map (K.subtype.comp e.symm.toMonoidHom), ?_, ?_, ?_⟩
  · rintro _ ⟨σ, -, rfl⟩
    exact (e.symm σ).2
  · have hinj : Function.Injective (K.subtype.comp e.symm.toMonoidHom) := fun a b hab =>
      e.symm.injective (Subtype.ext hab)
    rw [Subgroup.card_map_of_injective hinj]
    have h2 : 2 * Nat.card (alternatingGroup (Fin 3)) = Nat.card (Equiv.Perm (Fin 3)) :=
      two_mul_nat_card_alternatingGroup
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)), Fintype.card_perm,
      Fintype.card_fin] at h2
    have h6 : Nat.factorial 3 = 6 := rfl
    omega
  · rintro k hk _ ⟨σ, hσ, rfl⟩
    refine ⟨e ⟨k, hk⟩ * σ * (e ⟨k, hk⟩)⁻¹,
      (inferInstance : (alternatingGroup (Fin 3)).Normal).conj_mem σ hσ _, ?_⟩
    simp

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s16c1610_out10_of_case2_core (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hK : IsSym ↥(kBar D.M V₀ V hV L) 3) (hσ : D.sig = {3})
    {L₀ : Subgroup (MulAut (Vtil V₀ V hV))}
    (hdir : IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV))
    {m₀ r₀ : ℕ} (hm₀ : 4 ≤ m₀) (hr₀ : 2 * m₀ ≤ r₀ + 1) (hrk : r₀ ≤ rk (Vtil V₀ V hV))
    (h9 : 9 < Nat.card L₀) (hN : Nat.card L₀ < 2 ^ (m₀ * m₀ - 2)) :
    Out10 D V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨hcomm, -, hsup⟩ := hdir
  have hKc : kBar D.M V₀ V hV L ≤ centralizer (L₀ : Set (MulAut (Vtil V₀ V hV))) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  obtain ⟨X, hXK, hXcard, hXnK⟩ := s16c1610_a3_of_isSym_three hK
  have hKM : kBar D.M V₀ V hV L ≤ Mbar D.M V₀ V hV := hsup ▸ le_sup_left
  have hLM : L₀ ≤ Mbar D.M V₀ V hV := hsup ▸ le_sup_right
  have hkn : ∀ k ∈ kBar D.M V₀ V hV L, ∀ n ∈ L₀, k * n * k⁻¹ = n := fun k hk n hn => by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((Subgroup.mem_centralizer_iff.1 (hKc hk)) n hn).symm
  have hLX : L₀ ≤ centralizer (X : Set (MulAut (Vtil V₀ V hV))) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((Subgroup.mem_centralizer_iff.1 (hKc (hXK hx))) l hl).symm
  have hXnorm : ∀ m ∈ Mbar D.M V₀ V hV, ∀ x ∈ X, m * x * m⁻¹ ∈ X := by
    have hle : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (X : Set (MulAut (Vtil V₀ V hV))) := by
      rw [← hsup]
      refine sup_le (Subgroup.le_normalizer_iff.2 hXnK) (Subgroup.le_normalizer_iff.2 ?_)
      intro l hl x hx
      have hlx : l * x * l⁻¹ = x := by
        rw [mul_inv_eq_iff_eq_mul]
        exact ((Subgroup.mem_centralizer_iff.1 (hKc (hXK hx))) l hl)
      rw [hlx]
      exact hx
    exact Subgroup.le_normalizer_iff.1 hle
  have hNn : ∀ g ∈ Mbar D.M V₀ V hV, ∀ n ∈ L₀, g * n * g⁻¹ ∈ L₀ := by
    have hle : Mbar D.M V₀ V hV ≤ Subgroup.normalizer (L₀ : Set (MulAut (Vtil V₀ V hV))) := by
      rw [← hsup]
      refine sup_le (Subgroup.le_normalizer_iff.2 ?_) Subgroup.le_normalizer
      intro k hk n hn
      rw [hkn k hk n hn]
      exact hn
    exact Subgroup.le_normalizer_iff.1 hle
  have hnot : ¬ Concl614 (Vtil V₀ V hV) (Mbar D.M V₀ V hV) X :=
    s16c1610_not_concl614_of_normal_big (m₀ := m₀) hm₀ (by omega) hLM hLX hNn h9 hN
  exact s16c1610_out10_of_normal_prime D hin.hx hin.h61 hin.h127 hin.h1114 hin.h1214 hin.h162
    hin.h139 h125 (Or.inl rfl)
    (s16c1610_k_lt_dParam_three D hin.hSg hin.h1219 (by rw [hσ]; simp)) (hXK.trans hKM) hXcard
    hXnorm (by rw [s16c1610_dParam_three]; omega) hnot

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
