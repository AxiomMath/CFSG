module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8Nat
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SBd7Case3

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Mod

variable {G : Type} [Group G] {L U : Subgroup G}

theorem s8_beta_injective {F : Type} [Field F] {β : ↥U →* Multiplicative (Fin 1 → Fin 3 → F)}
    (hβk : β.ker = (⊥ : Subgroup G).subgroupOf U) : Function.Injective β := by
  rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]

variable {F : Type} [Field F] [Fintype F] {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}

theorem s8_sq_eq_one_of_mem {β : ↥U →* Multiplicative (Fin 1 → Fin 3 → F)}
    (hF2 : Fintype.card F = 2) (hβk : β.ker = (⊥ : Subgroup G).subgroupOf U) {a : G} (ha : a ∈ U) :
    a * a = 1 := by
  have hβi := s8_beta_injective hβk
  have : (⟨a * a, U.mul_mem ha ha⟩ : ↥U) = 1 := by
    apply hβi
    rw [show (⟨a * a, U.mul_mem ha ha⟩ : ↥U) = ⟨a, ha⟩ * ⟨a, ha⟩ from rfl, map_mul, map_one]
    apply Multiplicative.toAdd.injective
    funext i j
    simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
    exact SBd7.add_self_eq_zero_of_card_two hF2 _
  exact congrArg Subtype.val this

omit [Fintype F] in
theorem s8_alpha_eq_one (hU : IsSumOfNaturalModulesVia L U ⊥ α false 1) {l : ↥L}
    (hl : ∀ u ∈ U, (l : G) * u * (l : G)⁻¹ = u) : α l = 1 := by
  obtain ⟨-, -, β, hβs, -, hβe⟩ := hU
  have hmv : ∀ x : Fin 3 → F,
      ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (fun _ => x))
    have hux : Multiplicative.toAdd (β u) 0 = x := by rw [hu]; rfl
    have hc : (u : G) = (l : G) * (u : G) * (l : G)⁻¹ := (hl u u.2).symm
    have h := hβe l u u hc 0
    have h' : moduleAct false (α l : Matrix.GeneralLinearGroup (Fin 3) F) =
        ((α l : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      simp [moduleAct]
    rw [h', hux] at h
    exact h.symm
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have := congrFun (hmv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem s8_no_two_fixed (hF2 : Fintype.card F = 2) (hα : Function.Surjective α)
    (hU : IsSumOfNaturalModulesVia L U ⊥ α false 1) (B : Subgroup ↥L) (hB : ¬ 2 ∣ B.index)
    {u₁ u₂ : G} (h₁ : u₁ ∈ U) (h₂ : u₂ ∈ U) (n₁ : u₁ ≠ 1) (n₂ : u₂ ≠ 1) (n₁₂ : u₁ ≠ u₂)
    (f₁ : ∀ b ∈ B, (b : G) * u₁ * (b : G)⁻¹ = u₁)
    (f₂ : ∀ b ∈ B, (b : G) * u₂ * (b : G)⁻¹ = u₂) : False := by
  obtain ⟨-, -, β, -, hβk, hβe⟩ := hU
  have hβi := s8_beta_injective hβk
  have hx0 : ∀ u : ↥U, (u : G) ≠ 1 → Multiplicative.toAdd (β u) 0 ≠ 0 := by
    intro u hu h0
    apply hu
    have : β u = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simpa using h0
    have h1 : u = 1 := hβi (this.trans (map_one β).symm)
    exact congrArg Subtype.val h1
  have hfix : ∀ (u : ↥U), (∀ b ∈ B, (b : G) * (u : G) * (b : G)⁻¹ = u) → ∀ b ∈ B,
      ((α b : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (Multiplicative.toAdd (β u) 0) = Multiplicative.toAdd (β u) 0 := by
    intro u hu b hb
    have h := hβe b u u (hu b hb).symm 0
    have h' : moduleAct false (α b : Matrix.GeneralLinearGroup (Fin 3) F) =
        ((α b : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      simp [moduleAct]
    rw [h'] at h
    exact h.symm
  refine SzC4S8.no_two_fixed_vectors hF2 α hα B hB (Multiplicative.toAdd (β ⟨u₁, h₁⟩) 0)
    (Multiplicative.toAdd (β ⟨u₂, h₂⟩) 0) (hx0 ⟨u₁, h₁⟩ n₁) (hx0 ⟨u₂, h₂⟩ n₂) ?_
    (hfix ⟨u₁, h₁⟩ f₁) (hfix ⟨u₂, h₂⟩ f₂)
  intro h
  apply n₁₂
  have : β ⟨u₁, h₁⟩ = β ⟨u₂, h₂⟩ := by
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact h
  exact congrArg Subtype.val (hβi this)

end Mod

end CFSG.Quasithin.SzC4
