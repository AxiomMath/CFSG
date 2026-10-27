module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11B
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

@[expose] def Res627QL24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
    ∀ (t : G) (A D : Subgroup G) (g : G), t ∈ T → IsInvolutoryFieldAut L t →
    let U := V ⊓ Subgroup.centralizer ({t} : Set G)
    let H := Subgroup.centralizer (U : Set G)
    let UH := conjClosure V H
    let R := ch6Q T V ⊔ Subgroup.zpowers t
    let LU := oTwoUpper (L ⊓ Subgroup.normalizer (U : Set G))
    let B := ⁅V, A⁆
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (M ⊓ Subgroup.normalizer (U : Set G)) →
    QuasithinUnique.CharTwo H → IsSylowIn 2 R H →
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (thompsonJ R : Set G) →
    Subgroup.normalizer (thompsonJ R : Set G) ≤ M →
    IsSylowIn 2 (T ⊓ Subgroup.normalizer (U : Set G)) (Subgroup.normalizer (U : Set G)) →
    (T ⊓ Subgroup.normalizer (U : Set G)).relIndex T = 2 → wClos V 0 R ≤ ch6Q T V →
    IsElemAbelian 2 UH → UH ≤ pCoreOf 2 H → ⁅UH, pCoreOf 2 H⁆ ≤ U →
    centralizerMod U H UH = pCoreOf 2 H → ∀ h13 : IsReducedMod H UH U,
    Nat.card LU = 3 * Nat.card (pCoreOf 2 LU) → pCoreOf 2 LU = LU ⊓ H →
    A = conjSubgroup V g → V ≤ Subgroup.normalizer (A : Set G) →
    ¬ A ≤ Subgroup.normalizer (V : Set G) → V ⊓ Subgroup.centralizer (A : Set G) = U → A ≤ H →
    UH ≤ conjSubgroup T g → B = conjSubgroup (ch6ZS T L V) g → Nat.card B = 4 →
    A ⊓ Subgroup.normalizer (V : Set G) = B →
    UH ≤ Subgroup.normalizer (A : Set G) → UH = V ⊔ (UH ⊓ Subgroup.centralizer (A : Set G)) →
    ⁅UH, A⁆ = B → mQuot UH (UH ⊓ Subgroup.centralizer (A : Set G)) = 2 →
    (∀ U₀ : Subgroup G, UH ⊓ Subgroup.centralizer (A : Set G) < U₀ → U₀ ≤ UH →
      A ⊓ Subgroup.centralizer (U₀ : Set G) = B) →
    A ⊓ centralizerMod U H UH = B →
    D ≤ LU → Nat.card D = 3 → ⁅V, D⁆ = V →
    (∀ K : Subgroup G, K ≤ H → A ≤ K →
      (∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈
        centralizerMod U (Subgroup.normalizer (U : Set G)) UH) →
      ¬ ⁅⁅UH, K⁆, D⁆ ≤ U) →
    B ⊓ U = ⊥ →
    (∀ A₁ : Subgroup G, B < A₁ → A₁ ≤ A →
      centralizerMod U UH A₁ ≤ Subgroup.centralizer (A : Set G)) →
    mQuot UH (centralizerMod U UH A) = 2 →
    ∀ [(U.subgroupOf UH).Normal] [CommModCh611 UH U],
    ∃ K : Subgroup G, pCoreOf 2 H ≤ K ∧ K ≤ H ∧ A ≤ K ∧
      H ≤ Subgroup.normalizer (K : Set G) ∧ D ≤ Subgroup.normalizer (K : Set G) ∧
      let Ks := (K.subgroupOf H).map (actQuot UH U H h13.2.2.1 h13.2.2.2.1)
      BinaryNaturalSL Ks (commV Ks) ⊥ 2 2 ∧ IsIntDirect (commV Ks) (fixV Ks) ⊤

end CFSG.Quasithin.H13
