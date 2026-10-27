module

public import CFSG.Quasithin.Vol2.Ch3E213MG41D5
public import CFSG.Quasithin.Vol2.Ch3E213MG41R

public section

namespace CFSG.Quasithin.Ch3E213M.G41

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)}

omit [CharP k 2] in
theorem irr_closure_of_dInv (hG : ∀ W, DInv G₀ W → W = ⊥ ∨ W = ⊤) :
    IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)) := by
  intro W hW
  apply hG W
  intro d hd w hw
  exact hW d (Subgroup.subset_closure hd) w hw

theorem dInv_of_irr_closure (h : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀))) :
    ∀ W, DInv G₀ W → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  apply h W
  intro g hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx => exact hW x hx
  | inv_mem x hx =>
    obtain ⟨v, c, -, -, -, rfl⟩ := exists_of_mem_transvSet hx
    rw [trv_inv]
    exact hW _ hx
  | one => intro w hw; rw [natAct_one]; exact hw
  | mul x y _ _ hx hy => intro w hw; rw [natAct_mul]; exact hx _ (hy w hw)

theorem card_lam_eq_two_or_le [Finite k] {v : Fin 4 → k} (hv : v ∈ centres G₀) :
    Nat.card (Lam G₀ v) = 2 ∨ 4 ≤ Nat.card (Lam G₀ v) := by
  obtain ⟨hv0, c, hc, hcL⟩ := hv
  obtain ⟨a, ha⟩ := (isPGroup_rootGrp (G₀ := G₀) v).exists_card_eq
  rw [card_rootGrp hv0] at ha
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · interval_cases a
    · exfalso
      rw [pow_zero, Nat.card_eq_one_iff_unique] at ha
      have := ha.1.elim (⟨c, hcL⟩ : Lam G₀ v) ⟨0, (Lam G₀ v).zero_mem⟩
      exact hc (congrArg Subtype.val this)
    · left
      rw [ha, pow_one]
  · right
    rw [ha]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right two_pos ha2

theorem refl_of_card_two (h2 : ∀ v ∈ centres G₀, Nat.card (Lam G₀ v) = 2) :
    ∀ d ∈ transvSet G₀, ∀ d' ∈ transvSet G₀, commSpace d = commSpace d' → d = d' := by
  intro d hd d' hd' hcomm
  obtain ⟨v, c, hv, hc, hcL, rfl⟩ := exists_of_mem_transvSet hd
  obtain ⟨v', c', hv', hc', hc'L, rfl⟩ := exists_of_mem_transvSet hd'
  rw [commSpace_trv hv hc, commSpace_trv hv' hc'] at hcomm
  have hmem : v' ∈ Submodule.span k {v} := by
    rw [hcomm]
    exact Submodule.mem_span_singleton_self v'
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  have hμ : μ ≠ 0 := by
    rintro rfl
    exact hv' (zero_smul k v)
  rw [trv_smul]
  rw [mem_Lam_smul] at hc'L
  have hcard := h2 v ⟨hv, c, hc, hcL⟩
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (⟨0, (Lam G₀ v).zero_mem⟩ : Lam G₀ v)).mp hcard
  have e1 := hy ⟨c, hcL⟩ (fun h => hc (congrArg Subtype.val h))
  have e2 := hy ⟨μ ^ 2 * c', hc'L⟩ (fun h => mul_ne_zero (pow_ne_zero 2 hμ) hc'
    (congrArg Subtype.val h))
  have := congrArg Subtype.val (e1.trans e2.symm)
  simp only at this
  rw [this]

theorem factSp4TransvW_of_refl
    (hR : FactSp4TransvRefl) : FactSp4TransvW := by
  intro k _ _ _ n hk G₀ hirr hD
  by_cases hG : ∀ W, DInv G₀ W → W = ⊥ ∨ W = ⊤
  · by_cases h4 : ∃ x ∈ centres G₀, 4 ≤ Nat.card (Lam G₀ x)
    · obtain ⟨x₀, hx₀, h4⟩ := h4
      exact Or.inl (spW_of_large hk hirr hD hG hx₀ h4)
    · simp only [not_exists, not_and, not_le] at h4
      have h2 : ∀ x ∈ centres G₀, Nat.card (Lam G₀ x) = 2 := fun x hx =>
        (card_lam_eq_two_or_le hx).resolve_right (by have := h4 x hx; omega)
      rcases hR k G₀ (irr_closure_of_dInv hG) hD (refl_of_card_two h2) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · simp only [not_forall, not_or] at hG
    obtain ⟨W, hW, hW0, hWt⟩ := hG
    exact Or.inr (Or.inr (decW_of_reducible hirr hD hW hW0 hWt))

end CFSG.Quasithin.Ch3E213M.G41
