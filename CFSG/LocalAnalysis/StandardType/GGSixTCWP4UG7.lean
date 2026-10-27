module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UG3
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuter

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Orbit

theorem exists_iterate_rho_eq_id
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) :
    ∃ N : ℕ, 0 < N ∧ ∀ γ, IsRoot τ γ → (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[N] γ = γ := by
  classical
  let RT := {γ : Fin τ.rank → ℤ // IsRoot τ γ}
  have hfin : Finite RT := by
    have : Set.Finite {γ : Fin τ.rank → ℤ | IsRoot τ γ} :=
      (rootFinset τ).finite_toSet.subset fun γ hγ => mem_rootFinset.2 hγ
    exact this.to_subtype
  let σ : Equiv.Perm RT :=
    S.ρ.subtypePerm (p := fun γ => IsRoot τ γ) fun γ => S.frob.isRoot_iff γ
  refine ⟨orderOf σ, orderOf_pos σ, fun γ hγ => ?_⟩
  have hσ : σ ^ orderOf σ = 1 := pow_orderOf_eq_one σ
  have hiter : ∀ (n : ℕ) (γ : RT), ((σ ^ n) γ).1 = (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ.1 := by
    intro n
    induction n with
    | zero => intro γ; rfl
    | succ n ih =>
      intro γ
      rw [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ_apply, ih (σ γ)]
      rfl
  have h1 := hiter (orderOf σ) ⟨γ, hγ⟩
  rw [hσ] at h1
  exact h1.symm

theorem componentOrbitLength_pos
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ) :
    0 < componentOrbitLength S.ρ Ψ := by
  obtain ⟨N, hN, hid⟩ := exists_iterate_rho_eq_id S
  have hne : {s : ℕ | 0 < s ∧
      (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[s] '' Ψ = Ψ}.Nonempty :=
    ⟨N, hN, by
      ext γ
      constructor
      · rintro ⟨δ, hδ, rfl⟩
        rw [hid δ (hΨ δ hδ)]
        exact hδ
      · intro hγ
        exact ⟨γ, hγ, hid γ (hΨ γ hγ)⟩⟩
  exact (Nat.sInf_mem hne).1

end Orbit

section G7

theorem eq_one_of_commute_Γ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hτ : τ ≠ .G2) (hq : 4 ≤ S.D.q) {z : ModGL τ L}
    (hz : z ∈ adjointGroup τ L) (hcomm : ∀ x ∈ S.Γ, Commute z x) : z = 1 := by
  have hT : rootDiagUnit τ (1 : Fin τ.rank → Lˣ) ∈ S.D.torus := by
    rw [rootDiagUnit_one]
    exact one_mem _
  have hone : ∀ α : Fin τ.rank → ℤ, rootChar (1 : Fin τ.rank → Lˣ) α = 1 := fun α => by
    simp [rootChar]
  have hle : adjointGroup τ L ≤ Subgroup.centralizer {z} := by
    rw [adjointGroup_eq_rootSpan]
    refine iSup₂_le fun γ hγ => ?_
    have hγk : γ ∈ kernelRoots (rootCharHom (1 : Fin τ.rank → Lˣ)) := ⟨hγ, hone γ⟩
    let i : KernelComponent (rootCharHom (1 : Fin τ.rank → Lˣ)) := ⟦⟨γ, hγk⟩⟧
    have hγi : γ ∈ componentRoots (rootCharHom (1 : Fin τ.rank → Lˣ)) i := ⟨hγk, rfl⟩
    have hQ4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ
        (componentRoots (rootCharHom (1 : Fin τ.rank → Lˣ)) i) := by
      have hpos := componentOrbitLength_pos S
        (Ψ := componentRoots (rootCharHom (1 : Fin τ.rank → Lˣ)) i) (fun δ hδ => hδ.1.1)
      exact hq.trans (Nat.le_self_pow hpos.ne' _)
    have hrat : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom (1 : Fin τ.rank → Lˣ)) i,
        Commute z x := by
      intro x hx
      exact hcomm x
        ((inf_le_right : rationalSpan S.ρ S.Γ (rootCharHom (1 : Fin τ.rank → Lˣ)) i ≤ S.Γ)
          (commutator_self_le_self _ hx))
    have hz' := commute_rootSpan_of_commute_component_anyT S hτ hT i (by omega) hQ4 z hrat
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hz' _ (pinnedX_mem_rootSpan hγi c)).symm.eq
  have hcent : (⟨z, hz⟩ : adjointGroup τ L) ∈ Subgroup.center (adjointGroup τ L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
  exact congrArg Subtype.val hcent

end G7

end CFSG.StandardType.TableCRes
