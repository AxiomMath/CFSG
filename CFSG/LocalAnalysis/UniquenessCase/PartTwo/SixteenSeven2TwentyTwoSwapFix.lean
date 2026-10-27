module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentySwap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_two_core {M V A : Subgroup G} (hAM : A ≤ M) (hAel : IsElemAbelian 2 A)
    {I : Fin 3 → Subgroup G} {ρ : ↥M →* Equiv.Perm (Fin 3)} {P : Subgroup G}
    {Δ : Set (Subgroup G)} (hle : ∀ i, I i ≤ V) (hne : ∀ i, I i ≠ ⊥)
    (hpair : ∀ i j : Fin 3, i ≠ j → I i ⊓ I j = ⊥ ∧ I i ⊔ I j = V)
    (hconj : ∀ (m : ↥M) (i : Fin 3), conjSubgroup (I i) (m : G)⁻¹ = I (ρ m i))
    (hP : ∀ m : ↥M, m ^ 2 = 1 → ((m : G) ∈ P ↔ ρ m = 1))
    (hρ : ∃ m : ↥M, (m : G) ∈ A ∧ ρ m ≠ 1) (hΔ : ∀ J ∈ Δ, ∃ i, J = I i) :
    ∃ (I₀ I₁ : Subgroup G) (a : G) (i₀ : Fin 3), I₀ = I i₀ ∧ Swap20 A V I₀ I₁ a ∧
      (∀ x ∈ A, conjSubgroup I₀ x = I₀ ↔ x ∈ P) ∧
      (∀ b : ↥M, (b : G) ∈ A → conjSubgroup I₀ (b : G) = I₀ → ρ b = 1) ∧
      (∀ b ∈ A, conjSubgroup I₀ b = I₀ → ∀ J ∈ Δ, conjSubgroup J b = J) := by
  have hperm : ∀ σ τ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 → τ * σ = σ * τ →
      τ = 1 ∨ τ = σ := by decide
  obtain ⟨m, hmA, hm1⟩ := hρ
  have hsq : ∀ x : ↥M, (x : G) ∈ A → x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using hAel.2 _ hx)
  have hσ2 : ρ m * ρ m = 1 := by rw [← map_mul, ← sq, hsq m hmA, map_one]
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ρ m i₀ ≠ i₀ := by
    by_contra h
    push Not at h
    exact hm1 (Equiv.ext h)
  have hinj : ∀ i j, I i = I j → i = j := by
    intro i j h
    by_contra hij
    have := (hpair i j hij).1
    rw [h, inf_idem] at this
    exact hne j this
  have hact : ∀ (x : ↥M), x ^ 2 = 1 → ∀ i, conjSubgroup (I i) (x : G) = I (ρ x i) := by
    intro x hx i
    have hxx : (x : G) * (x : G) = 1 := by
      have := congrArg Subtype.val hx
      simpa [sq] using this
    have hxinv : (x : G)⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    have := hconj x i
    rwa [hxinv] at this
  have hcent : ∀ x : ↥M, (x : G) ∈ A → ρ x = 1 ∨ ρ x = ρ m := by
    intro x hx
    refine hperm (ρ m) (ρ x) hσ2 hm1 ?_
    rw [← map_mul, ← map_mul]
    have hxm : (x : G) * (m : G) = (m : G) * (x : G) :=
      congrArg Subtype.val (hAel.1.is_comm.comm ⟨(x : G), hx⟩ ⟨(m : G), hmA⟩)
    exact congrArg ρ (Subtype.ext hxm)
  have hi1 : i₀ ≠ ρ m i₀ := fun h => hi₀ h.symm
  obtain ⟨hinf, hsup⟩ := hpair i₀ (ρ m i₀) hi1
  have hb1 : ∀ b : ↥M, (b : G) ∈ A → conjSubgroup (I i₀) (b : G) = I i₀ → ρ b = 1 := by
    intro b hb hbI
    rw [hact b (hsq b hb) i₀] at hbI
    have := hinj _ _ hbI
    rcases hcent b hb with h' | h'
    · exact h'
    · exfalso
      rw [h'] at this
      exact hi₀ this
  refine ⟨I i₀, I (ρ m i₀), (m : G), i₀, rfl,
    ⟨hle i₀, hle _, hne i₀, hinf, hsup, hmA, hact m (hsq m hmA) i₀, ?_⟩, ?_, hb1, ?_⟩
  · intro x hx
    let xM : ↥M := ⟨x, hAM hx⟩
    rcases hcent xM hx with h | h
    · left
      refine ⟨?_, ?_⟩
      · rw [hact xM (hsq xM hx) i₀, h]
        rfl
      · rw [hact xM (hsq xM hx) _, h]
        rfl
    · right
      refine ⟨?_, ?_⟩
      · rw [hact xM (hsq xM hx) i₀, h]
      · rw [hact xM (hsq xM hx) _, h]
        congr 1
        simpa using congrArg (fun τ : Equiv.Perm (Fin 3) => τ i₀) hσ2
  · intro x hx
    let xM : ↥M := ⟨x, hAM hx⟩
    rw [hact xM (hsq xM hx) i₀]
    refine Iff.trans ⟨hinj _ _, fun h => by rw [h]⟩ ?_
    refine Iff.trans ?_ (hP xM (hsq xM hx)).symm
    constructor
    · intro h
      rcases hcent xM hx with h' | h'
      · exact h'
      · exfalso
        rw [h'] at h
        exact hi₀ h
    · intro h
      rw [h]
      rfl
  · intro b hb hbI J hJ
    let bM : ↥M := ⟨b, hAM hb⟩
    have hρb : ρ bM = 1 := hb1 bM hb hbI
    obtain ⟨i, rfl⟩ := hΔ J hJ
    rw [hact bM (hsq bM hb) i, hρb]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
