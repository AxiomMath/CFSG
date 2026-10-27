module

public import CFSG.Quasithin.H13.U3Local
public import CFSG.Quasithin.H13.U3Assembly

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def IsUniqueMaxOvergroup (T M H : Subgroup G) : Prop :=
  H ⊓ M < H ∧ T ≤ H ⊓ M ∧ ∀ A : Subgroup G, T ≤ A → A < H → A ≤ H ⊓ M

@[expose] def U3ConfinedCentralizerOvergroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G),
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
    SteinbergCB.QTU3InternalFrame T L V z →
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) →
    (∀ v ∈ V, v ≠ 1 → centralizer ({v} : Set G) ≤ normalizer (V : Set G)) ∧
      normalizer (V : Set G) ≤ normalizer (L : Set G) ∧
      (∀ x : G, V ⊓ CFSG.conjugate V x = ⊥ ∨ CFSG.conjugate V x = V) ∧
      (∀ g : G, (CFSG.conjugate V g ⊓ normalizer (V : Set G) ≠ ⊥ ∨
          V ⊓ normalizer (CFSG.conjugate V g : Set G) ≠ ⊥) → ⁅V, CFSG.conjugate V g⁆ = ⊥) ∧
      (V ≠ ⊥ ∧ V ≤ ⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g ∧
        (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) ≤ pCoreOf 2 (L ⊔ T) ∧
        normalizer ((⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g :
          Subgroup G) : Set G) ≤ normalizer (L : Set G)) ∧
      normalizer (T : Set G) ≤ normalizer (L : Set G) ∧
      centralizer (quasithinOmegaOneCenter T : Set G) ≤ normalizer (L : Set G) ∧
      (∀ A : Subgroup G, T ≤ A → Group.IsSolvable A → A ≤ normalizer (L : Set G)) ∧
      (∃ H : Subgroup G, (T ≤ H ∧ pCoreOf 2 H ≠ ⊥ ∧ ¬ H ≤ normalizer (L : Set G)) ∧
        ∀ A : Subgroup G, T ≤ A → pCoreOf 2 A ≠ ⊥ → ¬ A ≤ normalizer (L : Set G) →
          Nat.card H ≤ Nat.card A) ∧
      ∀ H : Subgroup G, T ≤ H → pCoreOf 2 H ≠ ⊥ → ¬ H ≤ normalizer (L : Set G) →
        (∀ A : Subgroup G, T ≤ A → pCoreOf 2 A ≠ ⊥ → ¬ A ≤ normalizer (L : Set G) →
          Nat.card H ≤ Nat.card A) →
        H < ⊤ ∧ ¬ Group.IsSolvable H ∧ CharTwo H ∧ SectionRank.IsSQTKCat H ∧
          ¬ (T.subgroupOf H).Normal ∧ IsUniqueMaxOvergroup T (normalizer (L : Set G)) H ∧
          6 ≤ CFSG.pRank 2 (↥H ⧸ CFSG.pCore 2 ↥H)

@[expose] def ExcludedMinimalOvergroupTwoRankBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ¬ QT13Excluded G → centralizer (quasithinOmegaOneCenter T : Set G) ≤ M → T ≤ H →
    ¬ Group.IsSolvable H → pCoreOf 2 H ≠ ⊥ → ¬ (T.subgroupOf H).Normal → ¬ H ≤ M →
    IsUniqueMaxOvergroup T M H → CFSG.pRank 2 (↥H ⧸ CFSG.pCore 2 ↥H) ≤ 4

theorem u3_local_uniqueness_and_escape_producer (hD : LocalDoubleEmbeddingExclusion)
    (h137 : Stmt13_1_7) (h1323 : Stmt13_1_2_three) (hord : FiveQuotientExactOrders)
    (hgrow : LocalTwoCoreQuotientStrictGrowth)
    (hA7 : SylowNormalizedMaximalLocalUniqueNormalizer)
    (hconf : U3ConfinedCentralizerOvergroup) (hexcl : ExcludedMinimalOvergroupTwoRankBound) :
    U3LocalUniquenessEscapeProducer := by
  intro G _ _ T L V z hH hU3 hF
  obtain ⟨hMtop, hVM, hTI, -, -⟩ :=
    u3_selected_local_normalizer_and_TI hD h137 h1323 hord hgrow hA7 hH hU3 hF
  refine ⟨hMtop, hVM, fun m hm => hTI m hm, fun hz => ?_⟩
  obtain ⟨-, -, -, -, -, -, hZM, -, ⟨H, ⟨hTH, hR, hHM⟩, hleast⟩, hmin⟩ :=
    hconf G T L V z hH hU3 hF hz
  obtain ⟨-, hns, -, -, hTn, huniq, h6⟩ := hmin H hTH hR hHM hleast
  have h4 := hexcl G T _ H hH.simple hH.nonabelian hH.qtke hH.sylow hH.not_excluded hZM hTH hns
    hR hTn hHM huniq
  omega

end CFSG.Quasithin.H13.U3
