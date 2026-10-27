module

public import CFSG.Quasithin.EmptyFaithful.S153D31
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Outcome31 {G : Type} [Group G] [Finite G] (T V₁ I L : Subgroup G) : Prop :=
  (IsAltBlockType L 6 ∨ IsG2Block L ∨
      (IsPSL 3 2 1 ↥(Star153 T I L) ∧
        (IsC134Case 1 I (Sgp153 T V₁) L ∨ IsC134Case 2 I (Sgp153 T V₁) L ∨
          IsC134Case 3 I (Sgp153 T V₁) L))) ∧
    L ⊓ Subgroup.centralizer (UI153 T I : Set G) = pCoreOf 2 L

@[expose] def Input31MSOutcome : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t →
    (IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L)) →
    IsMinParabolicOf (Star153 T I L) (Star153 T I (M ⊓ L)) →
      Outcome31 T V₁ I L

@[expose] def Input31CentQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L →
    I ⊓ Subgroup.centralizer (Yp : Set G) ≤ Subgroup.centralizer (blockU L : Set G) →
      I ⊓ Subgroup.centralizer (Yp : Set G) ≤ Subgroup.centralizer (L : Set G)

@[expose] def Input31NotCentQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Outcome31 T V₁ I L →
    ¬ (I ⊓ Subgroup.centralizer (Yp : Set G) ≤ Subgroup.centralizer (blockU L : Set G)) → False

namespace S153H

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem le_I_of_ctx31 (c : Ctx15331 T Mc M V₁ V₂ Yp I L t) : L ≤ I :=
  le_of_mem_cComp (S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1)

theorem one_lt_of_isPSL_two_two {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) : 1 < n := by
  obtain ⟨⟨-, hf, -, hne, -⟩, -⟩ := h
  by_contra hn
  have h1 : n = 1 := by omega
  subst h1
  exact hne (by simp)

theorem case_two_of_not_S8 (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hne : ¬ Nonempty (↥(Star153 T I I) ≃* Equiv.Perm (Fin 8))) :
    (IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨ IsPSU 3 3 1 ↥(Star153 T I L)) ∧
      IsMinParabolicOf (Star153 T I L) (Star153 T I (M ⊓ L)) := by
  rcases c.c28 with ⟨⟨n, -, hn⟩, -⟩ | ⟨h1, h2, -⟩ | ⟨hS8, -⟩
  · exact absurd ⟨n, one_lt_of_isPSL_two_two hn, hn⟩ c.c30
  · exact ⟨h1, h2⟩
  · exact absurd hS8 hne

theorem input15331_of_named_inputs (hMS : Input31MSOutcome) (hCQ : Input31CentQ)
    (hNQ : Input31NotCentQ) : Input15331 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  by_contra hne
  obtain ⟨hlist, hmin⟩ := case_two_of_not_S8 c hne
  have hout := hMS G T Mc M V₁ V₂ Yp I L t c hlist hmin
  have hD : I ⊓ Subgroup.centralizer (Yp : Set G) ≤ Subgroup.centralizer (L : Set G) := by
    by_cases hQ : I ⊓ Subgroup.centralizer (Yp : Set G) ≤ Subgroup.centralizer (blockU L : Set G)
    · exact hCQ G T Mc M V₁ V₂ Yp I L t c hout hQ
    · exact (hNQ G T Mc M V₁ V₂ Yp I L t c hout hQ).elim
  have hV₁S : V₁ ≤ Sgp153 T V₁ :=
    le_inf (c.ctx.hyp.decomp.le₁.trans c.ctx.hyp.hyp.VZ_le_T) Subgroup.le_normalizer
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.ctx.inH.1.1
  have hLC : L ≤ Subgroup.centralizer (V₁ : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvD : v ∈ I ⊓ Subgroup.centralizer (Yp : Set G) := by
      refine ⟨hSI (hV₁S hv), ?_⟩
      show v ∈ Subgroup.centralizer (Yp : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (c.c29.cent hy) v hv).symm
    exact (Subgroup.mem_centralizer_iff.mp (hD hvD) l hl).symm
  have hLM : L ≤ M := hLC.trans ((Subgroup.centralizer_le_normalizer _).trans c.c29.norm_le)
  exact c.conc.2.1 (le_inf hLM (le_I_of_ctx31 c))

end S153H

end CFSG.Quasithin
