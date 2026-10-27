module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def BlockType (p : ℕ) (J : Type) [Group J] : Prop :=
  ∃ g : ℕ, 1 ≤ g ∧ p ∣ 2 ^ g - 1 ∧
    (StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 2 2 g ∨
      StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 3 2 g ∨
      StatedClassicalModel (J ⧸ Subgroup.center J) .PSp 2 2 g ∨
      StatedClassicalModel (J ⧸ Subgroup.center J) .PSU 4 2 g)

section Constructors

variable {p : ℕ} {J : Type} [Group J]

theorem BlockType.of_psl_two {g : ℕ} (hg : 1 ≤ g) (hpg : p ∣ 2 ^ g - 1)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 2 2 g) : BlockType p J :=
  ⟨g, hg, hpg, Or.inl h⟩

theorem BlockType.of_psl_three {g : ℕ} (hg : 1 ≤ g) (hpg : p ∣ 2 ^ g - 1)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 3 2 g) : BlockType p J :=
  ⟨g, hg, hpg, Or.inr (Or.inl h)⟩

theorem BlockType.of_psp {g : ℕ} (hg : 1 ≤ g) (hpg : p ∣ 2 ^ g - 1)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSp 2 2 g) : BlockType p J :=
  ⟨g, hg, hpg, Or.inr (Or.inr (Or.inl h))⟩

theorem BlockType.of_psu {g : ℕ} (hg : 1 ≤ g) (hpg : p ∣ 2 ^ g - 1)
    (h : StatedClassicalModel (J ⧸ Subgroup.center J) .PSU 4 2 g) : BlockType p J :=
  ⟨g, hg, hpg, Or.inr (Or.inr (Or.inr h))⟩

end Constructors

noncomputable def centerQuotientCongr {J J' : Type} [Group J] [Group J'] (e : J ≃* J') :
    J ⧸ Subgroup.center J ≃* J' ⧸ Subgroup.center J' :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem statedClassicalModel_psl_of_sl {J : Type} [Group J] {E : Type} [Field E] [Finite E]
    {g m : ℕ} (hE : Nat.card E = 2 ^ g) (hg : 2 ≤ g) (hm : 2 ≤ m)
    (e : J ≃* Matrix.SpecialLinearGroup (Fin m) E) :
    StatedClassicalModel (J ⧸ Subgroup.center J) .PSL m 2 g := by
  have h4 : 4 ≤ 2 ^ g := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  refine ⟨⟨Nat.prime_two, by omega, hm, fun hc => ?_, fun hc => ?_⟩, E, inferInstance, inferInstance,
    hE, ⟨(centerQuotientCongr e).trans (projectiveSpecialLinearGroupEquivStatedProj m E)⟩⟩
  · have := (Prod.mk.inj hc).2
    omega
  · have := (Prod.mk.inj hc).2
    omega

theorem statedClassicalModel_psp_of_sp {J : Type} [Group J] {E : Type} [Field E] [Finite E]
    {g n : ℕ} (hE : Nat.card E = 2 ^ g) (hg : 2 ≤ g) (hn : 2 ≤ n) (e : J ≃* StatedSp n E) :
    StatedClassicalModel (J ⧸ Subgroup.center J) .PSp n 2 g := by
  have h4 : 4 ≤ 2 ^ g := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hadm : StatedLieAdmissible .PSp n 2 g :=
    ⟨Nat.prime_two, by omega, hn, fun hc => by have := (Prod.mk.inj hc).2; omega⟩
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv (centerQuotientCongr e).symm
    (CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient n E hadm hE)

section Transport

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ]

theorem nonempty_mulEquiv_of_transport {I : Subgroup G} (ψ : ↥I →* Γ) (hψ : Function.Injective ψ)
    {U : Type*} [Group U] (ρ : U →* Γ) {F : Subgroup U} {Q : Subgroup G}
    (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ F.map ρ) (hFB : F.map ρ ≤ ψ.range)
    (hρ : ∀ u ∈ F, ρ u = 1 → u = 1) : Nonempty (↥F ≃* ↥Q) := by
  let ρF : ↥F →* Γ := ρ.comp F.subtype
  have hρF : ∀ u : ↥F, ρF u ∈ ψ.range := fun u => hFB ⟨u, u.2, rfl⟩
  let θ : ↥F →* ↥ψ.range := ρF.codRestrict ψ.range hρF
  let ψe : ↥I ≃* ↥ψ.range := MonoidHom.ofInjective hψ
  let Θ : ↥F →* G := I.subtype.comp (ψe.symm.toMonoidHom.comp θ)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : ρ (u : U) = 1 := congrArg Subtype.val hu
    exact Subtype.ext (hρ _ u.2 h1)
  have hΘ : Function.Injective Θ := Subtype.val_injective.comp (ψe.symm.injective.comp hθ)
  have hrange : Θ.range = Q := by
    ext x
    rw [hQ x]
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨(ψe.symm (θ u)).2, ?_⟩
      have h1 : ψ (ψe.symm (θ u)) = ρ (u : U) := by
        have := congrArg Subtype.val (ψe.apply_symm_apply (θ u))
        exact this
      show ψ (ψe.symm (θ u)) ∈ F.map ρ
      rw [h1]
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨hx, u, hu, hux⟩
      refine ⟨⟨u, hu⟩, ?_⟩
      have h1 : θ ⟨u, hu⟩ = ψe ⟨x, hx⟩ := Subtype.ext hux
      show ((ψe.symm (θ ⟨u, hu⟩) : ↥I) : G) = x
      rw [h1, ψe.symm_apply_apply]
  exact ⟨(MonoidHom.ofInjective hΘ).trans (MulEquiv.subgroupCongr hrange)⟩

end Transport

end CFSG.RankThree.PartOne.S15K
