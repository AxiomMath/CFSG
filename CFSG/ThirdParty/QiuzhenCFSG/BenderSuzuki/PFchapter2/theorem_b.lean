module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_11
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_9
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_10
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_14
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_15
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_16
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_17
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Projectivization.Action

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII MatrixGroups
open scoped LinearAlgebra.Projectivization
open PFchapter1section3

universe u v

private abbrev theorem_b_context
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ) : Prop :=
  (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)

private abbrev theorem_b_claim14_data
    {G : Type u} [Group G] [Finite G] (P Sigma Z1 R R1 R2 : Subgroup G) (s : G) : Prop :=
  Sigma ≤ Subgroup.normalizer (R : Set G) ∧
    s ∈ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
        Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
          (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
            Z1 ⊔ P ∧
            R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
              R ⊔ Sigma ≤ R1 ∧
                R2 = Subgroup.centralizer (Z1 : Set G) ∧
                  R1 ≤ R2

private abbrev theorem_b_claim14_source_data
    {G : Type u} [Group G] [Finite G] (P Sigma Z1 R R1 R2 : Subgroup G) (s : G) : Prop :=
  IsPGroup 3 R1 ∧
    (∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2) ∧
      (∃ phi : (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G)) →*
            Equiv.Perm (Fin 3),
        Function.Surjective phi ∧
          MonoidHom.ker phi =
            (R ⊔ Sigma).subgroupOf
              (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G))) ∧
        Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) =
          R1 ⊔ Subgroup.closure ({s} : Set G) ∧
          Disjoint R1 (Subgroup.closure ({s} : Set G)) ∧
            Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ≤
              Subgroup.normalizer (R1 : Set G) ∧
              ((R1.subgroupOf R2).index = 1 ∨ (R1.subgroupOf R2).index = 3) ∧
                R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1 ∧
                  R2 ⊓ Subgroup.centralizer (R2 : Set G) = Z1 ∧
                    ⁅(R ⊔ Sigma : Subgroup G), (R ⊔ Sigma : Subgroup G)⁆ = Z1 ∧
                      R2 ⊓ Subgroup.centralizer (P : Set G) = R ⊔ Sigma

private abbrev theorem_b_claim15_data
    {G : Type u} [Group G] [Finite G] (V W P Sigma Z1 R1 R2 L : Subgroup G) (s : G) : Prop :=
  L ≤ R1 ∧
    (Nat.card L = 9 ∧ IsCyclic L) ∧
      (∀ x : G, x ∈ L → rightConjugateElem x s = x⁻¹) ∧
        V ≤ Subgroup.normalizer (L : Set G) ∧
          W ≤ Subgroup.centralizer (L : Set G) ∧
            ¬ P ≤ Subgroup.centralizer (L : Set G) ∧
              L ⊔ V ≤ R2 ∧
                Nat.card R2 = 3 * Nat.card ((L ⊔ V : Subgroup G)) ∧
                  (L ⊔ V) ⊓ Subgroup.centralizer ((L ⊔ V : Subgroup G) : Set G) =
                    Z1 ⊔ Sigma ∧
                    ∀ x : G, x ∈ L ⊔ V →
                      (x ^ 3 = 1 ↔ x ∈ Z1 ⊔ Sigma ⊔ P)

set_option backward.isDefEq.respectTransparency false in
private theorem theorem_b_B2_contradiction_after_claim15
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 L : Subgroup G)
    (t s : G) (p : ℕ)
    (hch : theorem_b_context (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P t s p)
    (h14 : theorem_b_claim14_data P Sigma Z1 R R1 R2 s)
    (h15 : theorem_b_claim15_data V W P Sigma Z1 R1 R2 L s)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hp3 : p = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (hR2p : IsPGroup 3 R2)
    (hcenterR2 : R2 ⊓ Subgroup.centralizer (R2 : Set G) = Z1)
    (hR2s : ∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2)
    (hRT : R = T ⊔ P) (hTdisjP : Disjoint T P)
    (hTleCP : T ≤ Subgroup.centralizer (P : Set G))
    (hSigmaNormT : Sigma ≤ Subgroup.normalizer (T : Set G))
    (hTinverted : ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹)
    (hRdisjSigma : Disjoint R Sigma)
    (hRScard : Nat.card (R ⊔ Sigma : Subgroup G) = 81)
    (hWdisjP : Disjoint W P)
    (hWcases : Nat.card W = 3 ∨ Nat.card W = 9)
    (hfactor : ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
      Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u)
    (hR1p : IsPGroup 3 R1)
    (h14Source : theorem_b_claim14_source_data P Sigma Z1 R R1 R2 s) : False := by
  rcases h14Source with
    ⟨_hR1p, _hR2sData, hphi, hNormalizerSplit, hR1DisjointS,
      hNormalizerNormR1, hIndex, hCenterR1, _hCenterR2, _hDerived, _hR2InfCP⟩
  have h16 :=
    claim_16 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P Sigma Z1 R R1 R2 L
      t s p hch h14 h15 hSigma hp3 hSigmaCard hZ1 hst3 hR1p hR2p hCenterR1
  exact
    claim_17 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 L
      t s p hch h14 h15 h16 hSigma hp3 hSigmaCard hZ1 hst3
      hR2p hcenterR2 hR2s
      hRT hTdisjP hTleCP hSigmaNormT hTinverted hRdisjSigma hRScard
      hWdisjP hWcases hfactor hR1p hphi hNormalizerSplit hR1DisjointS
      hNormalizerNormR1 hCenterR1 hIndex

set_option backward.isDefEq.respectTransparency false in
private theorem theorem_b_B2_contradiction_after_claim14
    {G : Type u} {Ω F : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [PFAppendixII.RightNearField F] [Finite F]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 : Subgroup G)
    (t s : G) (p : ℕ)
    (hch : theorem_b_context (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P t s p)
    (hind :
      ∀ (A : Type u) [Group A] [Finite A],
        ∀ (ΩA : Type v) [MulAction A ΩA] [Finite ΩA]
          (HA DA QA : Subgroup A) (tA : A),
          Nat.card A < Nat.card G →
            HypothesisA A ΩA HA DA QA tA →
              suzukiConclusion A ΩA)
    (addEquiv : Multiplicative F ≃* T)
    (hchar3 : addOrderOf (1 : F) = 3)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hp3 : p = 3) (hSigmaCard : Nat.card Sigma = 3)
    (hWcyclic : IsCyclic W)
    (hWcases : Nat.card W = 3 ∨ Nat.card W = 9)
    (hfactor : ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
      Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u)
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hst3 : orderOf (s * t) = 3)
    (hRT : R = T ⊔ P) (hTdisjP : Disjoint T P)
    (hTleCP : T ≤ Subgroup.centralizer (P : Set G))
    (hTinverted : ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹)
    (hRdisjSigma : Disjoint R Sigma)
    (hRScard : Nat.card (R ⊔ Sigma : Subgroup G) = 81)
    (hSigmaNormT : Sigma ≤ Subgroup.normalizer (T : Set G))
    (h14 : theorem_b_claim14_data P Sigma Z1 R R1 R2 s)
    (h14Source : theorem_b_claim14_source_data P Sigma Z1 R R1 R2 s) : False := by
  have h14SourceForTail := h14Source
  rcases h14Source with
    ⟨hR1p, hR2sData, _hphi, hNormalizerSplit, hR1DisjointS,
      hNormalizerNormR1, _hIndex, _hCenterR1, hCenterR2, hDerived, hR2InfCP⟩
  have h1 := claim_1 H D Q K V W Q0 S Q1 P t s p hch
  have hQ0card : Nat.card Q0 = 8 := by
    calc
      Nat.card Q0 = 2 ^ p := h1.2.1
      _ = 8 := by rw [hp3]; norm_num
  have hWP : W ⊔ P = V := h1.1.2.2.2.2
  rcases
    claim_15 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 t s p
      hch hind hst3 hQ0card hWP hSigma hZ1 addEquiv hchar3 hRT hTleCP
      hp3 hSigmaCard hWcyclic hWcases hfactor h14 hR1p hR2sData
      hNormalizerSplit hR1DisjointS hNormalizerNormR1 hCenterR2 hDerived hR2InfCP with
    ⟨L, h15⟩
  have hR2sForP := hR2sData
  have hR2p : IsPGroup 3 R2 := by
    rcases hR2sForP with ⟨R2s, hR2s⟩
    rw [← hR2s]
    exact R2s.isPGroup'
  exact
    theorem_b_B2_contradiction_after_claim15
      H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 L t s p hch h14 h15
      hSigma hp3 hSigmaCard hZ1 hst3 hR2p hCenterR2 hR2sData
      hRT hTdisjP hTleCP hSigmaNormT hTinverted hRdisjSigma hRScard
      h1.1.2.2.2.1 hWcases hfactor hR1p h14SourceForTail

/-!
# Peterfalvi, Part II, Chapter II, Theorem B
-/


set_option backward.isDefEq.respectTransparency false in
public theorem theorem_b_B2_contradiction
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL) :
    False := by
  let Sigma : Subgroup G := W ⊓ Subgroup.centralizer (P : Set G)
  let Z1 : Subgroup G := Subgroup.zpowers (s * t)
  have hp_eq_order : p = orderOf (s * t) :=
    claim_9 H D Q K V W Q0 S Q1 P t s p (orderOf (s * t)) hch rfl
  rcases claim_11 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P t s p hch hind with
    ⟨R, T, hR, hModel⟩
  rcases hModel with
    ⟨_N, F, hFnear, hFfinite, hFnontrivial, addEquiv, unitEquiv,
      _hN, _hRcentral, _hinverse, hTinverted, _hst_mem_T, _hconjugation,
      hchar_order, h11ExceptionalLocal, _h11CaseOneLocal,
        _h11CaseOneMOne⟩

  have hchar : addOrderOf (1 : F) = p :=
    hchar_order.trans hp_eq_order.symm
  letI : PFAppendixII.RightNearField F := hFnear
  letI : Finite F := hFfinite
  letI : Nontrivial F := hFnontrivial
  obtain ⟨m, hFcard⟩ :=
    PFAppendixII.rightNearField_natCard_eq_addOrderOf_one_pow (F := F)
  have hUnitsCard : Nat.card (nearFieldStar Q P) = Nat.card Fˣ := by
    simpa [nearFieldStar] using (Nat.card_congr unitEquiv.toEquiv).symm
  have hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m := by
    calc
      Nat.card (nearFieldStar Q P) + 1 = Nat.card Fˣ + 1 := by rw [hUnitsCard]
      _ = Nat.card F := (Nat.card_eq_card_units_add_one F).symm
      _ = addOrderOf (1 : F) ^ m := hFcard
      _ = p ^ m := by rw [hchar]
  have hcase10_2 :=
    claim_12 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P Sigma t s p m hch
      hind rfl hStarComm_order
  have hchar_three : addOrderOf (1 : F) = 3 :=
    hchar.trans hcase10_2.1
  have h13 :=
    claim_13 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P Z1 t s p hch
      (by simpa [Sigma] using hcase10_2) rfl
  rcases
    claim_14 (G := G) (Ω := Ω) H D Q K V W Q0 S Q1 P Sigma Z1 R T t s p hch
      rfl hcase10_2 rfl h13 hR
        (by
          refine ⟨_N, F, hFnear, hFfinite, hFnontrivial, addEquiv, unitEquiv, ?_⟩
          exact ⟨_hN, _hRcentral, _hinverse, hTinverted, _hst_mem_T,
            _hconjugation, hchar_order, h11ExceptionalLocal, _h11CaseOneLocal⟩) with
    ⟨R1, R2, h14, h14Source⟩
  have hst_order : orderOf (s * t) = 3 :=
    hp_eq_order.symm.trans hcase10_2.1
  have hExceptional := h11ExceptionalLocal
    hcase10_2.1 hcase10_2.2.1 hcase10_2.2.2.1
  have hRdisjSigma : Disjoint R Sigma := by
    simpa [Sigma] using hExceptional.1
  have hRScard : Nat.card (R ⊔ Sigma : Subgroup G) = 81 := by
    norm_num [Sigma] at hExceptional ⊢
    exact hExceptional.2.1
  have hSigmaNormT : Sigma ≤ Subgroup.normalizer (T : Set G) := by
    dsimp [Sigma]
    exact le_sup_right.trans hR.2.2.2.1
  have hWcyclic : IsCyclic W := hcase10_2.2.2.2.1
  have hWcases : Nat.card W = 3 ∨ Nat.card W = 9 :=
    hcase10_2.2.2.2.2.1
  have hfactor : ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
      Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u :=
    hcase10_2.2.2.2.2.2.1
  exact
    theorem_b_B2_contradiction_after_claim14
      H D Q K V W Q0 S Q1 P Sigma Z1 R T R1 R2 t s p hch hind
      addEquiv hchar_three rfl hcase10_2.1 hcase10_2.2.1
      hWcyclic hWcases hfactor rfl hst_order hR.1 hR.2.1 hR.2.2.1 hTinverted
      hRdisjSigma hRScard hSigmaNormT h14 h14Source

private theorem theorem_b_opening_reduction_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hB1 : HypothesisB1 G V P p)
    (hN : ∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p) :
    ∃ L : Subgroup G, L.Normal ∧ L ≠ ⊥ ∧ L ≠ ⊤ := by
  classical
  rcases hN with ⟨N, hNnormal, hNcard⟩
  refine ⟨N, hNnormal, ?_, ?_⟩
  · intro hNbot
    have hV_le_D : V ≤ D := by
      intro x hx
      have hx' : x ∈ D ⊓ Subgroup.centralizer ({t} : Set G) := by
        simpa [PFchapter1section1.peterfalviV, hsec.section2.V_eq] using hx
      exact hx'.1
    have hP_le_D : P ≤ D := hB1.P_le_V.trans hV_le_D
    have hP_nat : Nat.card P = p := by
      simpa [Nat.card, Nat.card_coe_set_eq] using hB1.P_card
    have hp_dvd_D : p ∣ Nat.card D := by
      rw [← hP_nat]
      exact Subgroup.card_dvd_of_le hP_le_D
    have hp_ne_two : p ≠ 2 :=
      hsec.section2.hA.A1.D_odd.ne_two_of_dvd_nat hp_dvd_D
    have ht_order : orderOf t = 2 := by
      refine (orderOf_eq_prime_iff (x := t) (p := 2)).2 ⟨?_, ?_⟩
      · exact hsec.section2.hA.A1.involution_t.sq_eq_one
      · exact hsec.section2.hA.A1.involution_t.ne_one
    have htwo_dvd_G : 2 ∣ Nat.card G := by
      simpa [ht_order] using orderOf_dvd_natCard t
    let e : G ⧸ N ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hNbot).trans QuotientGroup.quotientBot
    have hquot_card : Nat.card (G ⧸ N) = Nat.card G := Nat.card_congr e.toEquiv
    have hGcard : Nat.card G = p := hquot_card.symm.trans hNcard
    have htwo_dvd_p : 2 ∣ p := by
      simpa [hGcard] using htwo_dvd_G
    have htwo_eq_p : 2 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two hB1.p_prime).mp htwo_dvd_p
    exact hp_ne_two htwo_eq_p.symm
  · intro hNtop
    have hquot_card_one : Nat.card (G ⧸ N) = 1 := by
      subst hNtop
      haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
        QuotientGroup.subsingleton_quotient_top (G := G)
      exact Nat.card_of_subsingleton (1 : G ⧸ (⊤ : Subgroup G))
    have hp_eq_one : p = 1 := hNcard.symm.trans hquot_card_one
    exact hB1.p_prime.ne_one hp_eq_one

private theorem theorem_b_normal_index_or_B2
    {G : Type*} [Group G] [Finite G] (p : ℕ) :
    (∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p) ∨ HypothesisB2 G p := by
  classical
  by_cases hN : ∃ N : Subgroup G, N.Normal ∧ Nat.card (G ⧸ N) = p
  · exact Or.inl hN
  · refine Or.inr ?_
    intro N hNnormal hNcard
    exact hN ⟨N, hNnormal, hNcard⟩

public theorem theorem_b
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              ∃ (M : Subgroup L) (_ : M.Normal) (q : ℕ),
  Odd (Nat.card (L ⧸ M)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
    ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : M ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : ΩL ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : M, ∀ ω : ΩL,
      eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : M ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : ΩL ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : M ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : ΩL ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : M, ∀ ω : ΩL,
        eΩ ((l : L) • ω) = rho (eL l) (eΩ ω))))
    (hB1 : HypothesisB1 G V P p) :
    ∃ (L : Subgroup G) (_ : L.Normal) (q : ℕ),
  Odd (Nat.card (G ⧸ L)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
    ((∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : L ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eΩ : Ω ≃ ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : L, ∀ ω : Ω,
      eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : L ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eΩ : Ω ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : L, ∀ ω : Ω,
        eΩ ((l : G) • ω) = rho (eL l) (eΩ ω)) ∨
  (∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eΩ : Ω ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : L, ∀ ω : Ω,
        eΩ ((l : G) • ω) = rho (eL l) (eΩ ω))) := by
  rcases theorem_b_normal_index_or_B2 (G := G) p with hN | hB2
  · exact
      PFchapter1section3.proposition_2 H D Q K V W Q0 S Q1 t s hsec hind
        (theorem_b_opening_reduction_obligation H D Q K V W Q0 S Q1 P
          t s p hsec hB1 hN)
  · exact False.elim
      (theorem_b_B2_contradiction H D Q K V W Q0 S Q1 P t s p
        ⟨hsec, hB1, hB2⟩ hind)

end PFchapter2
end CFSG.BenderSuzuki
