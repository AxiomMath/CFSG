module

public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def HatA6Quot {G : Type} [Group G] (L V : Subgroup G) : Prop :=
  ∃ _ : ((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal,
    CFSG.IsQuasisimple (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ∧
    Nat.card (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L)) = 3 ∧
    Nonempty ((↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ⧸
        Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ≃*
      alternatingGroup (Fin 6))

structure Hyp1271 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) : Prop where
  hyp : Hyp1223 G T L V
  hatA6 : HatA6Quot L V

@[expose] def Lemma12_7_4_one : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∃ z ∈ V, ∃ t ∈ V,
      (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 ∧
      (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 ∧
      ∀ v ∈ V, v ≠ 1 → (∃ l ∈ L, l * v * l⁻¹ = z) ∨ (∃ l ∈ L, l * v * l⁻¹ = t)

@[expose] def Theorem12_7_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
      ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
        Nonempty (G ≃* NativeSporadic.He)

@[expose] def Theorem12_7_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
    ∀ z ∈ V, (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 →
      Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      ¬ V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) →
        Nonempty (G ≃* NativeSporadic.M24)

@[expose] def Final1271 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V →
    ¬ Nonempty (G ≃* NativeSporadic.M24) → ¬ Nonempty (G ≃* NativeSporadic.He) →
    ∀ t ∈ V, (Subgroup.centralizer ({t} : Set G)).relIndex L = 18 →
    ∀ z ∈ V, (Subgroup.centralizer ({z} : Set G)).relIndex L = 45 →
      Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) → False

theorem stmt12_7_1_of_lemmas (h1274 : Lemma12_7_4_one) (h1277 : Theorem12_7_7)
    (h12714 : Theorem12_7_14) (hfin : Final1271) : Stmt12_7_1 := by
  rw [stmt12_7_1_iff]
  intro G _ _ T L V hH hA6
  have hH' : Hyp1271 G T L V := ⟨hH, hA6⟩
  obtain ⟨z, hz, t, ht, hz45, ht18, -⟩ := h1274 G T L V hH'
  by_cases hGt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)
  · by_cases hVz : V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))
    · by_contra hne
      exact hfin G T L V hH' (fun h => hne (Or.inl h)) (fun h => hne (Or.inr h)) t ht ht18 z hz
        hz45 hGt hVz
    · exact Or.inl (h12714 G T L V hH' t ht ht18 z hz hz45 hGt hVz)
  · exact Or.inr (h1277 G T L V hH' t ht ht18 hGt)

end CFSG.Quasithin.H13
