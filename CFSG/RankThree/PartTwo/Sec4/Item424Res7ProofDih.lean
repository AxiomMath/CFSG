module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofPairing

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res424Seven

open CFSG CFSG.RankThree.Asc83Table

variable {X : Type} [Group X] [Finite X] {D : Subgroup X} {c d : X} {J : Subgroup X}

theorem c_not_mem_zpowers_of_config (h : InnerConfig424 X D c d J) :
    c ∉ Subgroup.zpowers d := by
  intro hc
  apply h.d_not_mem
  have hDe := h.maximal.prop
  have hc3 : c ^ 3 = 1 := hDe.2 c h.c_mem
  have hd3 : d ^ 3 = 1 := hDe.2 d h.d_mem
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact h.c_ne_one (by simpa using hc)
  have hle : Subgroup.zpowers c ≤ Subgroup.zpowers d := (Subgroup.zpowers_le).mpr hc
  have hcard : Nat.card (Subgroup.zpowers d) ≤ Nat.card (Subgroup.zpowers c) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hc3 h.c_ne_one,
      orderOf_eq_prime hd3 hd1]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  exact Subgroup.mem_zpowers d

theorem nonempty_autIn_dihedral_of_elements (h : InnerConfig424 X D c d J) {n₁ n₂ g : X}
    (h₁c : n₁ * c * n₁⁻¹ = c⁻¹) (h₁d : n₁ * d * n₁⁻¹ = d)
    (h₂c : n₂ * c * n₂⁻¹ = c) (h₂d : n₂ * d * n₂⁻¹ = d⁻¹)
    (hgd : g * d * g⁻¹ = d) (hgc : g * c * g⁻¹ = d * c ∨ g * c * g⁻¹ = d ^ 2 * c) :
    Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6) := by
  have hDe := h.maximal.prop
  have hc3 : c ^ 3 = 1 := hDe.2 c h.c_mem
  have hd3 : d ^ 3 = 1 := hDe.2 d h.d_mem
  have hdc : Commute d c := by
    have := congrArg Subtype.val (hDe.1.is_comm.comm ⟨d, h.d_mem⟩ ⟨c, h.c_mem⟩)
    exact this
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact h.d_not_mem (Subgroup.one_mem _)
  have hdinv : d⁻¹ = d ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hd3]
  have hcinv : c⁻¹ = c ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hc3]
  set E : E9Basis X := ⟨d, c, hd3, hc3, hdc,
    card_closure_pair_eq_nine hd3 hc3 hdc hd1 (c_not_mem_zpowers_of_config h)⟩ with hE
  have hsub : E.sub = D := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact h.d_mem
      · exact h.c_mem
    · rw [h.card_eq, E.card]
  obtain ⟨g', hg'd, hg'c⟩ : ∃ g' : X, g' * d * g'⁻¹ = d ∧ g' * c * g'⁻¹ = d * c := by
    rcases hgc with hgc | hgc
    · exact ⟨g, hgd, hgc⟩
    · refine ⟨g * g, ?_, ?_⟩
      · calc g * g * d * (g * g)⁻¹ = g * (g * d * g⁻¹) * g⁻¹ := by group
          _ = d := by rw [hgd, hgd]
      · calc g * g * c * (g * g)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := by group
          _ = g * (d ^ 2 * c) * g⁻¹ := by rw [hgc]
          _ = (g * d ^ 2 * g⁻¹) * (g * c * g⁻¹) := by group
          _ = (g * d * g⁻¹) ^ 2 * (g * c * g⁻¹) := by rw [conj_pow]
          _ = d ^ 2 * (d ^ 2 * c) := by rw [hgd, hgc]
          _ = d ^ 3 * d * c := by group
          _ = d * c := by rw [hd3, one_mul]
  have hS : bS ∈ E.rhoE.range := by
    refine E.mem_range_of_conj (g := n₂) 2 0 0 1 ?_ ?_ ?_
    · change n₂ * d * n₂⁻¹ = d ^ 2 * c ^ 0
      rw [h₂d, hdinv, pow_zero, mul_one]
    · change n₂ * c * n₂⁻¹ = d ^ 0 * c ^ 1
      rw [h₂c, pow_zero, pow_one, one_mul]
    · decide
  have hR : bR ∈ E.rhoE.range := by
    refine E.mem_range_of_conj (g := n₂ * n₁ * g') 2 2 0 2 ?_ ?_ ?_
    · change n₂ * n₁ * g' * d * (n₂ * n₁ * g')⁻¹ = d ^ 2 * c ^ 0
      calc n₂ * n₁ * g' * d * (n₂ * n₁ * g')⁻¹ = n₂ * (n₁ * (g' * d * g'⁻¹) * n₁⁻¹) * n₂⁻¹ := by
            group
        _ = d ^ 2 * c ^ 0 := by rw [hg'd, h₁d, h₂d, hdinv, pow_zero, mul_one]
    · change n₂ * n₁ * g' * c * (n₂ * n₁ * g')⁻¹ = d ^ 2 * c ^ 2
      calc n₂ * n₁ * g' * c * (n₂ * n₁ * g')⁻¹ = n₂ * (n₁ * (g' * c * g'⁻¹) * n₁⁻¹) * n₂⁻¹ := by
            group
        _ = n₂ * ((n₁ * d * n₁⁻¹) * (n₁ * c * n₁⁻¹)) * n₂⁻¹ := by rw [hg'c]; group
        _ = (n₂ * d * n₂⁻¹) * (n₂ * c⁻¹ * n₂⁻¹) := by rw [h₁d, h₁c]; group
        _ = d⁻¹ * c⁻¹ := by
            rw [h₂d, show n₂ * c⁻¹ * n₂⁻¹ = (n₂ * c * n₂⁻¹)⁻¹ by group, h₂c]
        _ = d ^ 2 * c ^ 2 := by rw [hdinv, hcinv]
    · decide
  rcases E.dihedral_or_gl hR hS with hq | hgl
  · rw [hsub] at hq
    obtain ⟨q⟩ := hq
    exact ⟨(Sporadic.automizerEquivAutIn D).symm.trans q⟩
  · rw [hsub] at hgl
    exact absurd hgl (Res424Two.not_nonempty_gl_of_config h)

end CFSG.RankThree.PartTwo.Sec4.Res424Seven
