module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

theorem qTwoChartTwoThree_mem_fixI_iff
    (ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (I : Finset (Fin (n + 1))) (b : ↥Bs) :
    (b : G) ∈ qTwoFixI ρA I ↔ ∀ s : qTwoSymI ρA I, (s : MulAut ↥Bs) b = b := by
  unfold qTwoFixI
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxb⟩
    have hxeq : x = b := Subtype.ext hxb
    rw [hxeq] at hx
    intro s
    have hs : b ∈ MonoidHom.eqLocus ((s : MulAut ↥Bs).toMonoidHom) (MonoidHom.id ↥Bs) :=
      (Subgroup.mem_iInf.mp hx) s
    show (s : MulAut ↥Bs) b = b
    exact hs
  · intro h
    refine ⟨b, ?_, rfl⟩
    rw [Subgroup.mem_iInf]
    intro s
    show (s : MulAut ↥Bs) b = b
    exact h s

theorem qTwoChartTwoThree_closure_supported_iff {I : Finset (Fin (n + 1))}
    {σ : Equiv.Perm (Fin (n + 1))} :
    σ ∈ Subgroup.closure {τ : Equiv.Perm (Fin (n + 1)) | ∀ y, y ∉ I → τ y = y} ↔
      ∀ y, y ∉ I → σ y = y := by
  constructor
  · intro hσ
    let H : Subgroup (Equiv.Perm (Fin (n + 1))) :=
      { carrier := {τ | ∀ y, y ∉ I → τ y = y}
        one_mem' := by intro y _; rfl
        mul_mem' := by
          intro a b ha hb y hy
          rw [Equiv.Perm.mul_apply, hb y hy, ha y hy]
        inv_mem' := by
          intro a ha y hy
          calc a⁻¹ y = a⁻¹ (a y) := by rw [ha y hy]
          _ = y := Equiv.symm_apply_apply a y }
    have hle : Subgroup.closure {τ : Equiv.Perm (Fin (n + 1)) | ∀ y, y ∉ I → τ y = y} ≤ H :=
      (Subgroup.closure_le H).mpr fun _ hτ => hτ
    show ∀ y, y ∉ I → σ y = y
    exact hle hσ
  · intro hσ
    exact Subgroup.subset_closure hσ

theorem qTwoChartTwoThree_mem_closure_swaps_of_supported {I : Finset (Fin (n + 1))}
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : ∀ y, y ∉ I → σ y = y) :
    σ ∈ Subgroup.closure {τ : Equiv.Perm (Fin (n + 1)) | τ.IsSwap ∧ ∀ y, y ∉ I → τ y = y} := by
  classical
  refine (mem_closure_isSwap
    (S := {τ : Equiv.Perm (Fin (n + 1)) | τ.IsSwap ∧ ∀ y, y ∉ I → τ y = y})
    (fun τ hτ => hτ.1)).mpr ⟨Set.toFinite _, ?_⟩
  intro x
  by_cases hx : x ∈ I
  · have hσx : σ x ∈ I := by
      by_contra h
      have hfix : σ (σ x) = σ x := hσ (σ x) h
      have hcontra : σ x = x := σ.injective hfix
      exact h (hcontra.symm ▸ hx)
    by_cases hxx : σ x = x
    · rw [hxx]
      exact MulAction.mem_orbit_self x
    · refine MulAction.mem_orbit_iff.mpr
        ⟨⟨Equiv.swap x (σ x), Subgroup.subset_closure ⟨⟨x, σ x, fun h => hxx h.symm, rfl⟩, ?_⟩⟩, ?_⟩
      · intro y hy
        exact Equiv.swap_apply_of_ne_of_ne (fun hyx => hy (hyx.symm ▸ hx))
          (fun hyx => hy (hyx.symm ▸ hσx))
      · show (Equiv.swap x (σ x) : Equiv.Perm (Fin (n + 1))) x = σ x
        rw [Equiv.swap_apply_left]
  · rw [hσ x hx]
    exact MulAction.mem_orbit_self x

theorem qTwoChartTwoThree_mem_symI
    {ρA : Equiv.Perm (Fin (n + 1)) ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {I : Finset (Fin (n + 1))}
    {s : MulAut ↥Bs} :
    s ∈ qTwoSymI ρA I ↔ ∃ σ : Equiv.Perm (Fin (n + 1)), (∀ y, y ∉ I → σ y = y) ∧
      ((ρA σ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = s := by
  constructor
  · intro hs
    rw [qTwoSymI, Subgroup.mem_map] at hs
    obtain ⟨σ, hσ, hσs⟩ := hs
    exact ⟨σ, qTwoChartTwoThree_closure_supported_iff.mp hσ, hσs⟩
  · rintro ⟨σ, hσ, rfl⟩
    rw [qTwoSymI, Subgroup.mem_map]
    exact ⟨σ, Subgroup.subset_closure hσ, rfl⟩

end CFSG.StandardType.QTwo

end
