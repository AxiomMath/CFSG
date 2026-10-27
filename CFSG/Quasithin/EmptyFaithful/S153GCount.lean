module

public import CFSG.Quasithin.EmptyFaithful.S153D25

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Vocabulary

variable {G : Type} [Group G]

abbrev P153 (T M V₁ : Subgroup G) : Subgroup G :=
  pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁)

abbrev S0153 (T V₁ L : Subgroup G) : Subgroup G :=
  Sgp153 T V₁ ⊓ (L ⊔ pCoreOf 2 (L ⊔ Sgp153 T V₁))

@[expose] def IsOffenderB (T V₁ U A : Subgroup G) : Prop :=
  IsMaxElemAbelian (Sgp153 T V₁) A ∧ ¬ A ≤ Subgroup.centralizer (U : Set G) ∧
    ∀ B : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) B → ¬ B ≤ Subgroup.centralizer (U : Set G) →
      autOn B U ≤ autOn A U → autOn B U = autOn A U

noncomputable abbrev cm0 (P A : Subgroup G) : ℕ := rk ↥A - rk ↥(A ⊓ P)

noncomputable abbrev cm1 (P U A : Subgroup G) : ℕ :=
  rk ↥(A ⊓ P) - rk ↥(A ⊓ P ⊓ Subgroup.centralizer (U : Set G))

noncomputable abbrev cm3 (U A : Subgroup G) : ℕ :=
  rk ↥U - rk ↥(U ⊓ Subgroup.centralizer (A : Set G))

end Vocabulary

@[expose] def CountExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∃ A : Subgroup G, IsOffenderB T V₁ (UL153 T I L) A

@[expose] def CountSideU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∀ A : Subgroup G, IsOffenderB T V₁ (UL153 T I L) A →
        ¬ A ≤ P153 T M V₁ ∧
        cm1 (P153 T M V₁) (UL153 T I L) A + 1 = cm3 (UL153 T I L) A ∧
        (cm0 (P153 T M V₁) A = 1 ∨
          (cm0 (P153 T M V₁) A = 2 ∧ ¬ A ≤ S0153 T V₁ L))

@[expose] def CountSideUt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → ∀ A : Subgroup G, IsOffenderB T V₁ (UL153 T I L) A →
        cm1 (P153 T M V₁) (conjBy153 t' (UL153 T I L)) A + 1 =
          cm3 (conjBy153 t' (UL153 T I L)) A

@[expose] def CountIneq : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → ∀ A : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) A →
        cm3 (UL153 T I L) A + cm3 (conjBy153 t' (UL153 T I L)) A ≤
          cm0 (P153 T M V₁) A + cm1 (P153 T M V₁) (UL153 T I L) A +
            cm1 (P153 T M V₁) (conjBy153 t' (UL153 T I L)) A

@[expose] def CountTHat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → conjBy153 t' (S0153 T V₁ L) ≠ S0153 T V₁ L →
        ∀ A : Subgroup G, IsOffenderB T V₁ (UL153 T I L) A → cm0 (P153 T M V₁) A = 2 → False

@[expose] def CountFinal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
      ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → conjBy153 t' (S0153 T V₁ L) = S0153 T V₁ L →
        (∀ A : Subgroup G, IsOffenderB T V₁ (UL153 T I L) A → ¬ A ≤ S0153 T V₁ L) → False

section Derivation

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem exists_mem_T_not_mem_S (c : Ctx15332 T Mc M V₁ V₂ Yp I L t) :
    ∃ t' ∈ T, t' ∉ Sgp153 T V₁ := by
  have h : Hyp15310 G T Mc M V₁ V₂ Yp t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L.ctx.hyp
  have hidx : (Sgp153 T V₁).relIndex T = 2 := h.decomp.relIndex_nS h.hyp
  by_contra hcon
  push Not at hcon
  have hle : T ≤ Sgp153 T V₁ := fun x hx => hcon x hx
  have h1 : (Sgp153 T V₁).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hle
  omega

end Derivation

theorem input15325Count_of_narrow (hE : CountExists) (hU : CountSideU) (hUt : CountSideUt)
    (hI : CountIneq) (hT : CountTHat) (hF : CountFinal) : Input15325Count := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc
  obtain ⟨t', ht'T, ht'S⟩ := exists_mem_T_not_mem_S c
  have key : ∀ A : Subgroup G, IsOffenderB T V₁ (UL153 T I L) A →
      cm0 (P153 T M V₁) A = 2 ∧ ¬ A ≤ S0153 T V₁ L := by
    intro A hA
    have h1 := hU G T Mc M V₁ V₂ Yp I L t c cc A hA
    have h2 := hUt G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA
    have h3 := hI G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA.1
    obtain ⟨-, h1b, h1c⟩ := h1
    rcases h1c with h | ⟨h, hn⟩
    · omega
    · exact ⟨h, hn⟩
  by_cases hS0 : conjBy153 t' (S0153 T V₁ L) = S0153 T V₁ L
  · exact hF G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S hS0 (fun A hA => (key A hA).2)
  · obtain ⟨A, hA⟩ := hE G T Mc M V₁ V₂ Yp I L t c cc
    exact hT G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S hS0 A hA (key A hA).1

end CFSG.Quasithin
