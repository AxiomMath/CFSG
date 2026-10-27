module

public import CFSG.Quasithin.EmptyFaithful.S153D26

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

structure Ctx15327 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends Ctx15325L T Mc M V₁ V₂ Yp I L t where
  solv : ∀ X : Subgroup G, X ≤ I → Group.IsSolvable ↥X →
    Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (X : Set G) → X ≤ M ⊓ I

structure Concl15327 {G : Type} [Group G] [Finite G] (T Yp I L : Subgroup G) : Prop where
  normal : I ≤ Subgroup.normalizer (L : Set G)
  Yp_le : Yp ≤ L
  not_SL3 : ¬ ∃ n : ℕ, Even n ∧ IsSL3 (2 ^ n) ↥(Star153 T I L)
  not_hatA6 : ¬ IsHat ↥(Star153 T I L) (alternatingGroup (Fin 6))

@[expose] def Input15327 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15327 T Mc M V₁ V₂ Yp I L t → Concl15327 T Yp I L

namespace S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem exists_minimal_counterexample (c : Ctx15325 T Mc M V₁ V₂ Yp I t)
    (hF : Facts153 T M V₁ Yp I) :
    ∃ J : Subgroup G, J ≤ I ∧ Ctx15325 T Mc M V₁ V₂ Yp J t ∧
      ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ J → K = J := by
  obtain ⟨J, ⟨hJ, hJI⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {K : Subgroup G | IsHPlus Yp (Sgp153 T V₁) M K ∧ K ≤ I} ⟨I, c.inH, le_rfl⟩
  refine ⟨J, hJI, ctx25_of_le c hF hJI hJ.1.1 hJ.2, fun K hK hKJ => ?_⟩
  by_contra hne
  exact hmin K ⟨hK, hKJ.trans hJI⟩ (lt_of_le_of_ne hKJ hne)

theorem lemma_15_3_27_four (c : Ctx15325L T Mc M V₁ V₂ Yp I L t) (c27 : Concl15327 T Yp I L)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) :
    I = L ⊔ Sgp153 T V₁ ∧
      ∀ K : Subgroup G, Yp ⊔ Sgp153 T V₁ ≤ K → K < I → K ≤ M ⊓ I := by
  have hLI : L ≤ I := (le_of_mem_cComp c.conc.1).trans (thompsonJ_le_self I)
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.ctx.inH.1.1
  have hLM : ¬ L ≤ M := fun h => c.conc.2.1 (le_inf h hLI)
  have hF3 : Facts153 T M V₁ Yp I := c.facts.toFacts153
  constructor
  · have hK : L ⊔ Sgp153 T V₁ = I := by
      refine hmin (L ⊔ Sgp153 T V₁) ?_ (sup_le hLI hSI)
      have := (ctx25_of_le c.ctx hF3 (sup_le hLI hSI) (sup_le (c27.Yp_le.trans le_sup_left) le_sup_right)
        (fun hle => hLM (le_sup_left.trans hle))).inH
      exact this
    exact hK.symm
  · intro K hYSK hKI
    by_contra hKM
    have hKM' : ¬ K ≤ M := fun hle => hKM (le_inf hle hKI.le)
    have hH : IsHPlus Yp (Sgp153 T V₁) M K :=
      (ctx25_of_le c.ctx hF3 hKI.le hYSK hKM').inH
    exact hKI.ne (hmin K hH hKI.le)

end S153D

end CFSG.Quasithin
