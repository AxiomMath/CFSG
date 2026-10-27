module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Pointwise

theorem s16t_a_exists_conj_stable_set {Γ : Type} [Group Γ] {B : Subgroup Γ}
    (hB : IsPGroup 2 ↥B) {Ω : Set (Subgroup Γ)}
    (hΩ : ∀ b ∈ B, ∀ H ∈ Ω, H.map (MulAut.conj b).toMonoidHom ∈ Ω)
    (hodd : Odd (Nat.card ↥Ω)) :
    ∃ H ∈ Ω, ∀ b ∈ B, H.map (MulAut.conj b).toMonoidHom = H := by
  classical
  letI : MulAction ↥B (Subgroup Γ) :=
    MulAction.compHom (Subgroup Γ) ((MulAut.conj : Γ →* MulAut Γ).comp B.subtype)
  have hsmul : ∀ (b : ↥B) (H : Subgroup Γ), b • H = H.map (MulAut.conj (b : Γ)).toMonoidHom := by
    intro b H
    have hf : MulDistribMulAction.toMonoidEnd _ _ (MulAut.conj (b : Γ)) =
        (MulAut.conj (b : Γ)).toMonoidHom := by
      ext y
      rfl
    show (MulAut.conj (b : Γ)) • H = _
    rw [Subgroup.pointwise_smul_def, hf]
  let S : SubMulAction ↥B (Subgroup Γ) :=
    { carrier := Ω
      smul_mem' := by
        intro b H hH
        rw [hsmul]
        exact hΩ b b.2 H hH }
  have hndvd : ¬ 2 ∣ Nat.card ↥S := by
    obtain ⟨k, hk⟩ := hodd
    show ¬ 2 ∣ Nat.card ↥Ω
    omega
  obtain ⟨s, hs⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card ↥S hndvd
  refine ⟨s.1, s.2, fun b hb => ?_⟩
  have h1 : (⟨b, hb⟩ : ↥B) • s = s := hs ⟨b, hb⟩
  have h2 := congrArg Subtype.val h1
  rw [← hsmul ⟨b, hb⟩ s.1]
  exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
