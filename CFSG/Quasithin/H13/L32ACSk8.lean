module

public import CFSG.Quasithin.H13.L32ACSk7

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

structure L2Red (G : Type) [Group G] [Finite G] (T L V K : Subgroup G) : Prop where
  S : Setting147 G T L V (A6.g1 T V)
  hK : K ∈ cComp (A6.g1 T V)
  hT : ¬ T ≤ Subgroup.normalizer (K : Set G)
  hA5 : IsAlt 5 (cStar K)
  hG1 : A6.g1 T V = conjClosure K T ⊔ T
  hl1 : l1 T L V ≤ conjClosure K T

@[expose] def L2CaseOne (G : Type) [Group G] [Finite G] (T L V : Subgroup G) : Prop :=
  (∀ (γ γ' : F8.Geom T L (A6.g1 T V)) (g : ↥((L ⊔ T) ⊔ A6.g1 T V)),
    F8Setup T V L (A6.g1 T V) γ γ' g →
      F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G) < F8.Uγ V (A6.g1 T V) (g : G)) ∧
  ∃ (γ γ' : F8.Geom T L (A6.g1 T V)) (g : ↥((L ⊔ T) ⊔ A6.g1 T V)),
    F8Setup T V L (A6.g1 T V) γ γ' g ∧
    Nat.card ↥(modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G))) = 2 ∧
    (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex (conjClosure V (A6.g1 T V)) = 2 ∧
    fsuV1 T V ≤ F8.Uγ V (A6.g1 T V) (g : G) ∧
    F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure V (A6.g1 T V)

@[expose] def Lemma14_7_32_L2_red : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H : Subgroup G), Setting147 G T L V H →
    ∀ K ∈ cComp H, ¬ T ≤ Subgroup.normalizer (K : Set G) →
      ((∃ n : ℕ, IsPSL 2 2 n (cStar K)) ∨ IsAlt 5 (cStar K)) → L2Red G T L V K

@[expose] def Lemma14_7_32_L2_mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V K : Subgroup G), L2Red G T L V K → L2CaseOne G T L V

@[expose] def Lemma14_7_32_L2_loc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V K : Subgroup G), L2Red G T L V K →
    L2CaseOne G T L V → False

theorem lemma14_7_32_L2_of (h1 : Lemma14_7_32_L2_red) (h2 : Lemma14_7_32_L2_mod)
    (h3 : Lemma14_7_32_L2_loc) : Lemma14_7_32_L2 := by
  intro G _ _ T L V H S K hK hT
  have key : ((∃ n : ℕ, IsPSL 2 2 n (cStar K)) ∨ IsAlt 5 (cStar K)) → False := fun h => by
    have hred := h1 G T L V H S K hK hT h
    exact h3 G T L V K hred (h2 G T L V K hred)
  exact ⟨fun n hn => key (Or.inl ⟨n, hn⟩), fun h => key (Or.inr h)⟩

end CFSG.Quasithin.H13.L32A.C
