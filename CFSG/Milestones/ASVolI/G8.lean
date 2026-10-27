module

public import CFSG.Quasithin.Background.G8Dihedral
public import CFSG.Quasithin.Background.G8Nine

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin

@[expose] def G_8_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P A : Subgroup G), G81 X P A →
    ∀ B : Subgroup G, B ≤ A → B ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      ∃ D : Subgroup G, IsSubgroupComplementIn A B D ∧
        B ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) =
          ⊥ ∧
        D = A ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) :
          Set G)

theorem as_G_8_2 : G_8_2 := by
  intro G _ _ X P A h B hBA hfaith
  exact g8_2 h hBA hfaith

@[expose] def G_8_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P A : Subgroup G), G81 X P A →
    ∀ U : Subgroup G, U ≤ X →
      pCoreOf 2 (Subgroup.centralizer (U : Set G) ⊓ (X ⊔ P)) = pCoreOf 2 (X ⊔ P)

theorem as_G_8_3 : G_8_3 := by
  intro G _ _ X P A h U hUX
  exact g8_3 h hUX

@[expose] def G_8_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P A : Subgroup G), G81 X P A →
    ∀ Y : Subgroup G, Y ≤ X → P ≤ Subgroup.centralizer (Y : Set G) →
      P ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
        P ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) = ⊥

theorem as_G_8_4 : G_8_4 := by
  intro G _ _ X P A h Y hYX hPY hfaith
  exact g8_4 h hYX hPY hfaith

@[expose] def G_8_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P A : Subgroup G), G81 X P A →
    ∀ B Y : Subgroup G, B ≤ A → Y ≤ X → A ≤ Subgroup.normalizer (Y : Set G) →
      B ≤ Subgroup.centralizer (Y : Set G) → B ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
        ∃ D : Subgroup G, IsSubgroupComplementIn A B D ∧
          B ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G) :
            Subgroup G) : Set G) = ⊥

theorem as_G_8_5 : G_8_5 := by
  intro G _ _ X P A h B Y hBA hYX hYA hBY hfaith
  exact g8_5 h hBA hYX hYA hBY hfaith

@[expose] def G_8_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P A : Subgroup G), G81 X P A →
    ∀ n : ℕ, 0 < n → Nat.card A = 2 ^ n → A ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      ∃ (Hs : Fin n → Subgroup G) (p : Fin n → ℕ), IsDihedralFamily Hs p ∧ A ≤ ⨆ i, Hs i ∧
        (⨆ i, Hs i) ≤ X ⊔ P

theorem as_G_8_6 : G_8_6 := by
  intro G _ _ X P A h n hn hcard hfaith
  obtain ⟨Hs, p, hD, hA, hle, -⟩ := g8_6 h hn hcard hfaith
  exact ⟨Hs, p, hD, hA, hle.trans (sup_le_sup_left h.le_pGroup X)⟩

@[expose] def G_8_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P A Y : Subgroup G), G81 X P A →
    ∀ m k : ℕ, 0 < m → 0 < k → A ⊓ Subgroup.centralizer (X : Set G) = ⊥ → Y ≤ X →
      A ≤ Subgroup.normalizer (Y : Set G) → Nat.card A = 2 ^ (m + k) →
      Nat.card (A ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) = 2 ^ m →
        ∃ D : Subgroup G, IsSubgroupComplementIn A (A ⊓ Subgroup.centralizer (Y : Set G)) D ∧
          ∃ (Hs : Fin (m + k) → Subgroup G) (p : Fin (m + k) → ℕ),
            (∀ i, (p i).Prime ∧ Odd (p i) ∧ Nonempty (↥(Hs i) ≃* DihedralGroup (p i))) ∧
            IsDihedralFamily (fun i : Fin m => Hs (Fin.castAdd k i))
              (fun i : Fin m => p (Fin.castAdd k i)) ∧
            IsDihedralFamily (fun j : Fin k => Hs (Fin.natAdd m j))
              (fun j : Fin k => p (Fin.natAdd m j)) ∧
            (A ⊓ Subgroup.centralizer (Y : Set G) ≤ ⨆ i : Fin m, Hs (Fin.castAdd k i)) ∧
            ((⨆ i : Fin m, Hs (Fin.castAdd k i)) ≤ (A ⊓ Subgroup.centralizer (Y : Set G)) ⊔
              (X ⊓ Subgroup.centralizer ((D ⊔ Y : Subgroup G) : Set G))) ∧
            (D ≤ ⨆ j : Fin k, Hs (Fin.natAdd m j)) ∧
            ((⨆ j : Fin k, Hs (Fin.natAdd m j)) ≤ Y ⊔ D)

theorem as_G_8_7 : G_8_7 := by
  intro G _ _ X P A Y h m k hm hk hfaith hYX hYA hcA hcB
  obtain ⟨D, hD, Hs, p, hDF, h1, h2, h3, h4, -, -⟩ := g8_7 h hm hk hfaith hYX hYA hcA hcB
  refine ⟨D, hD, Hs, p, fun i => ⟨hDF.prime i, hDF.odd i, hDF.iso i⟩, ?_, ?_, h1, h2, h3, h4⟩
  · exact ⟨fun i => hDF.prime _, fun i => hDF.odd _, fun i => hDF.iso _,
      fun i j hij => hDF.commute _ _ (fun h => hij (Fin.castAdd_injective _ _ h)),
      hDF.independent.comp (Fin.castAdd_injective _ _)⟩
  · exact ⟨fun i => hDF.prime _, fun i => hDF.odd _, fun i => hDF.iso _,
      fun i j hij => hDF.commute _ _ (fun h => hij (Fin.natAdd_injective k m h)),
      hDF.independent.comp (Fin.natAdd_injective k m)⟩

@[expose] def G_8_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X P A : Subgroup G), G81 X P A →
    ∀ (p n : ℕ), p.Prime → Nat.card A = 2 ^ n → A ⊓ Subgroup.centralizer (X : Set G) = ⊥ →
      ¬ A ≤ Subgroup.centralizer (pCoreOf p X : Set G) →
        ∃ (Hs : Fin n → Subgroup G) (q : Fin n → ℕ), IsDihedralFamily Hs q ∧ A ≤ ⨆ i, Hs i ∧
          (⨆ i, Hs i) ≤ X ⊔ P ∧ ∀ i : Fin n, i.val = 0 → q i = p

theorem as_G_8_8 : G_8_8 := by
  intro G _ _ X P A h p n hp hcard hfaith hnt
  obtain ⟨Hs, q, hD, hA, hle, hq⟩ := g8_8 h hp hcard hfaith hnt
  exact ⟨Hs, q, hD, hA, hle.trans (sup_le_sup_left h.le_pGroup X), hq⟩

@[expose] def G_8_9 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.pCore 2 H = ⊥ →
    (∀ X : Subgroup H,
      lambdaSubgroup (Subgroup.centralizer (X : Set H) ⊓ CFSG.generalizedFitting H) ≤ X →
      IsSubnormal X (CFSG.generalizedFitting H) →
      ∀ U : Subgroup H, IsPGroup 2 U → U ≤ Subgroup.normalizer (X : Set H) →
        U ⊓ Subgroup.centralizer (X : Set H) = ⊥) ∧
    (∀ θ : Subgroup H, IsTheta H θ → ∀ U : Subgroup H, IsPGroup 2 U →
      U ⊓ Subgroup.centralizer (θ : Set H) = ⊥)

theorem as_G_8_9 : G_8_9 := by
  intro H _ _ hO2
  exact ⟨fun X hΛ hX U hU hUX => g8_9_one hO2 hΛ hX hU hUX, fun θ hθ U hU => g8_9_two hO2 hθ hU⟩

end CFSG.ASVolI
