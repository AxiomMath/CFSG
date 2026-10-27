module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22P
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22M

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lem12223ExtraL32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G),
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V 3 →
    Pre12_2_21 T L V H P U I h 3 → U ≤ pCoreOf 2 H →
    Nat.card P = 27 → (∀ x ∈ P, x ^ 3 = 1) → Nat.card ((frattini ↥P).map P.subtype) = 3 →
    (∀ f ∈ (frattini ↥P).map P.subtype, ∀ x ∈ P, f * x = x * f) →
    (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G) →
    (∀ x ∈ V, ∀ f ∈ (frattini ↥P).map P.subtype, x * f * x⁻¹ * f⁻¹ ∈ pCoreOf 2 H) →
    pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ⊓
        Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) ≤
      Subgroup.centralizer (P : Set G) →
    V ⊓ pCoreOf 2 H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) →
    (V ⊓ pCoreOf 2 H) ⊓
        Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥ →
    conjClosure (V ⊓ pCoreOf 2 H) P ≤
      pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) →
    Nat.card (conjClosure (V ⊓ pCoreOf 2 H) P) = 64 →
    H ≤ Subgroup.normalizer ((conjClosure (V ⊓ pCoreOf 2 H) P : Subgroup G) : Set G) →
    conjClosure (V ⊓ pCoreOf 2 H) P ⊓
        Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥ →
    (∀ x ∈ P, ∀ r ∈ pCoreOf 2 H, x * r * x⁻¹ * r⁻¹ ∈ conjClosure (V ⊓ pCoreOf 2 H) P) →
    pCoreOf 2 H ⊓ Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) ≤
      Subgroup.centralizer (P : Set G) ⊓ Subgroup.centralizer (V : Set G) →
    H ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ Subgroup.centralizer
      (((frattini ↥P).map P.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) →
    False

@[expose] def Lem12223ExtraN45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V H P U I : Subgroup G) (h : G) (n : ℕ),
    (n = 4 ∨ n = 5) →
    Hyp1223 G T L V → NoEscape12_2_13 L V → Concl12_2_20 T L V n →
    Pre12_2_21 T L V H P U I h 3 → U ≤ pCoreOf 2 H →
    Nat.card P = 27 → (∀ x ∈ P, x ^ 3 = 1) → Nat.card ((frattini ↥P).map P.subtype) = 3 →
    (∀ f ∈ (frattini ↥P).map P.subtype, ∀ x ∈ P, f * x = x * f) →
    (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (V : Set G) →
    (∀ x ∈ V, ∀ f ∈ (frattini ↥P).map P.subtype, x * f * x⁻¹ * f⁻¹ ∈ pCoreOf 2 H) →
    pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ⊓
        Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) ≤
      Subgroup.centralizer (P : Set G) →
    (∃ X : Subgroup G, X ≠ ⊥ ∧
      X ≤ V ⊓ (pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) ∧
      (frattini ↥P).map P.subtype ≤ Subgroup.normalizer (X : Set G) ∧
      X ⊓ Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) = ⊥) →
    False

theorem lem12223Extra_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hL32 : Lem12223ExtraL32)
    (hN45 : Lem12223ExtraN45) : Lem12223Extra := by
  intro G _ _ T L V H P U I h n hyp hNE hC hpre hUO hcard hexp hΦ3 hZ hΦV hVΦ hcent hX
  rcases hC.1 with rfl | rfl | rfl
  · have e : Lem22.Extra3 T L V H P U I h :=
      ⟨hyp, hNE, hC, hpre, hUO, hcard, hexp, hΦ3, hZ, hΦV, hVΦ, hcent, hX⟩
    obtain ⟨h1, -, h2⟩ := e.eq_inf
    exact hL32 G T L V H P U I h hyp hNE hC hpre hUO hcard hexp hΦ3 hZ hΦV hVΦ hcent h1 h2
      e.W_le_center (e.card_W h331 h1222) (e.le_normalizer_W h331 h1222)
      (e.W_inf_centralizer h331 h1222) (e.comm_mem_W h331 h1222)
      (e.inf_centralizer_le h331 h1222) (e.le_normalizer_inf_centralizer h331 h1222)
  · exact hN45 G T L V H P U I h 4 (Or.inl rfl) hyp hNE hC hpre hUO hcard hexp hΦ3 hZ hΦV hVΦ
      hcent hX
  · exact hN45 G T L V H P U I h 5 (Or.inr rfl) hyp hNE hC hpre hUO hcard hexp hΦ3 hZ hΦV hVΦ
      hcent hX

end CFSG.Quasithin.H13
