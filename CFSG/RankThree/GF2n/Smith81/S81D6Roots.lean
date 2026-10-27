module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

theorem card_pr_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    (idx0.filter fun a => pr a β = 1).card = 8 ∧ (idx0.filter fun a => pr a β = -1).card = 8 ∧
      (idx0.filter fun a => pr a β = 0).card = 16 := by
  refine (forall_isRoot_iff fun γ => MinData.toWeight γ ⬝ᵥ theta = 0 →
    (idx0.filter fun a => pr a γ = 1).card = 8 ∧ (idx0.filter fun a => pr a γ = -1).card = 8 ∧
      (idx0.filter fun a => pr a γ = 0).card = 16).2 ?_ β hβ.1 hβ.2
  unfold pr idx0
  decide +kernel

theorem range_EW [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) :
    LinearMap.range (EW K β) = Finsupp.supported K K {b : Idx0 | pr (b : Fin e7Data.d) β = 1} := by
  have hnβ : -β ∈ Perp := neg_mem_Perp hβ
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    rw [Finsupp.mem_supported']
    intro b hb
    have hb' : ¬ pr (b : Fin e7Data.d) β = 1 := fun h => hb h
    rw [EW_apply, if_neg hb']
  · intro w hw
    rw [Finsupp.mem_supported'] at hw
    refine ⟨Finsupp.equivFunOnFinite.symm
      (fun a : Idx0 => if pr (a : Fin e7Data.d) β = -1 then w (shiftW β a) else 0), ?_⟩
    ext b
    rw [EW_apply]
    by_cases hb : pr (b : Fin e7Data.d) β = 1
    · rw [if_pos hb]
      have h2 : pr (b : Fin e7Data.d) (-β) = -1 := by rw [pr_neg, hb]
      have h3 : pr ((shiftW (-β) b : Idx0) : Fin e7Data.d) β = -1 := by
        rw [shiftW_val hnβ h2]
        exact pr_shift_neg hβ.1 hb
      have h4 : shiftW β (shiftW (-β) b) = b := by
        apply Subtype.ext
        rw [shiftW_val hβ h3, shiftW_val hnβ h2, shift_shift_neg hβ.1 hb]
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      rw [if_pos h3, h4]
    · rw [if_neg hb]
      have hb'' : b ∉ {b : Idx0 | pr (b : Fin e7Data.d) β = 1} := hb
      exact (hw b hb'').symm

private theorem xuWUnit_mul_self [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp)
    (c : K) : xuWUnit hβ c * xuWUnit hβ c = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  rw [Units.val_mul, Units.val_one, Module.End.mul_apply, Module.End.one_apply]
  simp only [xuWUnit_apply, map_add, map_smul, EW_mul_self_apply hβ, smul_zero, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem IsRootEltW.mul_self [CharP K 2] {x : (Module.End K (W K))ˣ} (hx : IsRootEltW x) :
    x * x = 1 := by
  obtain ⟨g, -, β, hβ, c, -, rfl⟩ := isRootEltW_iff.1 hx
  calc g * xuWUnit hβ c * g⁻¹ * (g * xuWUnit hβ c * g⁻¹)
      = g * (xuWUnit hβ c * xuWUnit hβ c) * g⁻¹ := by group
    _ = 1 := by rw [xuWUnit_mul_self hβ c]; group

end CFSG.RankThree.GF2n.Smith81.D6Spin
