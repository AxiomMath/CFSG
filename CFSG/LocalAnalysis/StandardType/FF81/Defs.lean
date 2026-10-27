module

public import CFSG.LocalAnalysis.StandardType.GGF4SmallFFDefs
public import CFSG.LocalAnalysis.StandardType.GGFFLocal
public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.StandardType.FF81

open CFSG CFSG.Assembly CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.StandardType.FrameRoute.FS81 (IsConjLine IsSylow2In)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

structure HypA (G : Type) [Group G] [Finite G] (n : ℕ) (b : G) (L : Subgroup G) : Prop where
  n_cases : n = 5 ∨ n = 6
  ord : orderOf b = 3
  le : L ≤ Subgroup.centralizer ({b} : Set G)
  nor : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)
  model : StatedClassicalModel L .PSL (n + 1) 2 1
  cyc : ∀ P : Sylow 3 ↥(Subgroup.centralizer (L : Set G)), IsCyclic P
  rank : twoLocalPrimeRank 3 G = twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({b} : Set G))
  notWC : CFSG.RankThree.PartTwo.Sec21.FFNotWeaklyClosed b

structure LocalFacts {G : Type} [Group G] (b : G) (L : Subgroup G) (z : Fin 3 → ↥L) : Prop where
  syl : ∀ P : Subgroup G, P ≤ Subgroup.centralizer (L : Set G) →
    P ≤ Subgroup.centralizer ({b} : Set G) → IsPGroup 3 P → Subgroup.zpowers b ≤ P →
      P = Subgroup.zpowers b
  not_nor : ¬ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G) ≤
    Subgroup.normalizer (Subgroup.zpowers b : Set G)
  fus : ∀ g : G, g * b * g⁻¹ ∈ GGFF.Bt b z →
    ∃ n ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G), n * b * n⁻¹ = g * b * g⁻¹
  fusC : ∀ g : G, g * b * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) →
    ∃ n ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G),
      ∃ c ∈ Subgroup.centralizer ({b} : Set G), g * b * g⁻¹ = c * (n * b * n⁻¹) * c⁻¹
  stab : ∀ n ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G),
    n * b * n⁻¹ ∈ Subgroup.zpowers b →
      ∀ i : Fin 3, ∃ j : Fin 3, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ n * GGFF.zs z i * n⁻¹ = GGFF.zs z j ^ e

abbrev xs {G : Type} [Group G] {L : Subgroup G} (b : G) (z : Fin 3 → ↥L) : Fin 4 → G :=
  ![b, GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2]

@[expose] def ContainsMonomial {G : Type} [Group G] {L : Subgroup G} (b : G) (z : Fin 3 → ↥L) :
    Prop :=
  ∀ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ZMod 3), (∀ i, ε i ≠ 0) →
    ∃ n ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G),
      ∀ i, n * xs b z i * n⁻¹ = xs b z (σ i) ^ (ε i).val

@[expose] def IsMonomial {G : Type} [Group G] {L : Subgroup G} (b : G) (z : Fin 3 → ↥L) : Prop :=
  ContainsMonomial b z ∧
    ∀ n ∈ Subgroup.normalizer ((GGFF.Bt b z : Subgroup G) : Set G),
      ∃ (σ : Equiv.Perm (Fin 4)) (ε : Fin 4 → ZMod 3), (∀ i, ε i ≠ 0) ∧
        ∀ i, n * xs b z i * n⁻¹ = xs b z (σ i) ^ (ε i).val

@[expose] def coordLines {G : Type} [Group G] {L : Subgroup G} (b : G) (z : Fin 3 → ↥L) :
    Set (Subgroup G) :=
  {Z | ∃ i : Fin 4, Z = Subgroup.zpowers (xs b z i)}

@[expose] def weightFourLines {G : Type} [Group G] {L : Subgroup G} (b : G) (z : Fin 3 → ↥L) :
    Set (Subgroup G) :=
  {Z | ∃ (ε : ZMod 3) (v : Fin 3 → ZMod 3), ε ≠ 0 ∧ (∀ i, v i ≠ 0) ∧
    Z = Subgroup.zpowers (b ^ ε.val * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v)}

@[expose] def ConjLinesOfB {G : Type} [Group G] {L : Subgroup G} (b : G) (z : Fin 3 → ↥L)
    (S : Set (Subgroup G)) : Prop :=
  ∀ Z : Subgroup G, Z ≤ GGFF.Bt b z → Nat.card Z = 3 → (IsConjLine b Z ↔ Z ∈ S)

@[expose] def PropTwoOut {G : Type} [Group G] (b : G) (L : Subgroup G) (z : Fin 3 → ↥L) : Prop :=
  (IsMonomial b z ∧ ConjLinesOfB b z (coordLines b z)) ∨
  (ContainsMonomial b z ∧ Nat.card (ggAutomizer ⊤ (GGFF.Bt b z)) = 1152 ∧
    ConjLinesOfB b z (coordLines b z ∪ weightFourLines b z) ∧
    Odd (Nat.card (Subgroup.centralizer ((GGFF.Bt b z : Subgroup G) : Set G))))

structure AfterProp2 {G : Type} [Group G] (b : G) (L : Subgroup G) (z : Fin 3 → ↥L) : Prop where
  model : GGFF.Model ↥L z
  loc : LocalFacts b L z
  meet : ∃ g : G, g * b * g⁻¹ ∈ L
  out : PropTwoOut b L z

@[expose] def adjA {m : ℕ} (i j : Fin m) : Prop := (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i

@[expose] def adjE6 (i j : Fin 6) : Prop :=
  CFSG.Timmesfeld.edgeE 6 i j ∨ CFSG.Timmesfeld.edgeE 6 j i

@[expose] def A2System {G : Type} [Group G] {m : ℕ} (adj : Fin m → Fin m → Prop)
    (U : Fin m → Subgroup G) (X : Subgroup G) : Prop :=
  (∀ i, Nonempty (SL(2, ZMod 2) ≃* ↥(U i))) ∧ ⨆ i, U i = X ∧
  (∀ i j, i ≠ j → ¬ adj i j → ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a) ∧
  (∀ i j, adj i j → ∃ W : Subgroup G, LinearBlockStandardPair (ZMod 2) W (U i) (U j))

@[expose] def CurtisA2 : Prop :=
  (∀ (m : ℕ), 3 ≤ m → ∀ (X : Type) [Group X] (U : Fin m → Subgroup X), A2System adjA U ⊤ →
      CFSG.IsQuasisimple X ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (m + 1) 2 1) ∧
  (∀ (X : Type) [Group X] (U : Fin 6 → Subgroup X), A2System adjE6 U ⊤ →
      CFSG.IsQuasisimple X ∧ CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X)
        CFSG.Assembly.LowTwoRank.StatedLieTag.E6 0 2 1)

structure FrameSystem {G : Type} [Group G] [Finite G] (n : ℕ) (b : G) (L : Subgroup G)
    (K : ℕ → Subgroup G) (t : G) : Prop where
  sysL : A2System adjA (fun i : Fin n => K ((i : ℕ) + 2)) L
  sysL' : A2System adjA (fun i : Fin n => K (i : ℕ)) (⨆ i : Fin n, K (i : ℕ))
  K0 : K 0 = Subgroup.zpowers b ⊔ Subgroup.zpowers t
  ord_t : orderOf t = 2
  inv_b : t * b * t⁻¹ = b⁻¹
  comm_L : ∀ x ∈ K 0, ∀ y ∈ L, x * y = y * x
  conj_b : ∀ i : ℕ, i < n + 2 →
    ∃ x ∈ K i, orderOf x = 3 ∧ IsConjLine b (Subgroup.zpowers x)
  odd_core : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
      Odd (Nat.card R)
  tau : ∃ g : G, g * b * g⁻¹ ∈ K (n + 1) ∧
    ⨆ i : Fin n, K (i : ℕ) = L.map (MulAut.conj g).toMonoidHom ∧
    ∀ x ∈ K (n + 1), ∀ y ∈ L.map (MulAut.conj g).toMonoidHom, x * y = y * x

@[expose] def Upstream {G : Type} [Group G] [Finite G] (n : ℕ) (b : G) (L : Subgroup G)
    (K : ℕ → Subgroup G) (t : G) : Prop :=
  ∃ z : Fin 3 → ↥L, AfterProp2 b L z ∧ FrameSystem n b L K t

@[expose] def YLab (n : ℕ) {G : Type} [Group G] (Y : Subgroup G) : Prop :=
  StatedClassicalModel ↥Y .PSL (n + 3) 2 1 ∨ (n = 5 ∧ GGHasLabel ⟨.E6, 0, 1⟩ ↥Y)

structure YData {G : Type} [Group G] [Finite G] (n : ℕ) (b : G) (L Y : Subgroup G) (t : G) :
    Prop where
  lab : YLab n Y
  le : L ≤ Y
  cen_b : Subgroup.centralizer ({b} : Set G) ⊓ Y = Subgroup.zpowers b ⊔ L
  core : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({b} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({b} : Set G))).Normal → ¬ 3 ∣ Nat.card R →
      R ≤ Subgroup.centralizer (Y : Set G)
  syl : ∃ S : Subgroup G, IsSylow2In S Y ∧ t ∈ S ∧ orderOf t = 2 ∧ ∀ s ∈ S, s * t = t * s

@[expose] def LocalSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → ∀ (n : ℕ) (b : G) (L : Subgroup G), HypA G n b L →
      ∀ z : Fin 3 → ↥L, GGFF.Model ↥L z → LocalFacts b L z

@[expose] def PropOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → KProper InCatalog G → ∀ (n : ℕ) (b : G) (L : Subgroup G), HypA G n b L →
      ∀ z : Fin 3 → ↥L, GGFF.Model ↥L z → LocalFacts b L z → ∃ g : G, g * b * g⁻¹ ∈ L

@[expose] def PropTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → ∀ (n : ℕ) (b : G) (L : Subgroup G), HypA G n b L →
      ∀ z : Fin 3 → ↥L, GGFF.Model ↥L z → LocalFacts b L z → (∃ g : G, g * b * g⁻¹ ∈ L) →
        PropTwoOut b L z

@[expose] def FrameStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → ∀ (n : ℕ) (b : G) (L : Subgroup G), HypA G n b L →
      ∀ z : Fin 3 → ↥L, AfterProp2 b L z → ∃ (K : ℕ → Subgroup G) (t : G), FrameSystem n b L K t

@[expose] def ConstructY : Prop :=
  CurtisA2 →
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → ∀ (n : ℕ) (b : G) (L : Subgroup G), HypA G n b L →
      ∀ (K : ℕ → Subgroup G) (t : G), Upstream n b L K t →
        YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t

@[expose] def CentralizerA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → ∀ (n : ℕ) (b : G) (L : Subgroup G), HypA G n b L →
      ∀ (K : ℕ → Subgroup G) (t : G), Upstream n b L K t →
        YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t →
        StatedClassicalModel ↥(⨆ i : Fin (n + 2), K (i : ℕ)) .PSL (n + 3) 2 1 →
          Subgroup.centralizer ({t} : Set G) ≤ ⨆ i : Fin (n + 2), K (i : ℕ)

@[expose] def CentralizerE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → ∀ (n : ℕ) (b : G) (L : Subgroup G), HypA G n b L →
      ∀ (K : ℕ → Subgroup G) (t : G), Upstream n b L K t →
        YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t → n = 5 →
        GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ)) →
          Subgroup.centralizer ({t} : Set G) ≤ ⨆ i : Fin (n + 2), K (i : ℕ)

@[expose] def RootFusionE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → ∀ (n : ℕ) (b : G) (L : Subgroup G), HypA G n b L →
      ∀ (K : ℕ → Subgroup G) (t : G), Upstream n b L K t →
        YData n b L (⨆ i : Fin (n + 2), K (i : ℕ)) t → n = 5 →
        GGHasLabel ⟨.E6, 0, 1⟩ ↥(⨆ i : Fin (n + 2), K (i : ℕ)) →
        Subgroup.centralizer ({t} : Set G) ≤ ⨆ i : Fin (n + 2), K (i : ℕ) →
          ∀ g : G, g * t * g⁻¹ ∈ (⨆ i : Fin (n + 2), K (i : ℕ)) →
            ∃ y ∈ (⨆ i : Fin (n + 2), K (i : ℕ)), g * t * g⁻¹ = y * t * y⁻¹

@[expose] def HoltEnd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsCharTwoType G →
    ∀ (n : ℕ), (n = 5 ∨ n = 6) → ∀ (Y S : Subgroup G) (t : G), YLab n Y → Y ≠ ⊤ →
      IsSylow2In S Y → t ∈ S → orderOf t = 2 → (∀ s ∈ S, s * t = t * s) →
        (∀ g : G, g * t * g⁻¹ ∈ Y → g ∈ Y) → False

end CFSG.StandardType.FF81

end
