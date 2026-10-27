module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.SplitBNPair
public import CFSG.Open.QuasithinDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Milestones.ASVolI.I1
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.G2OddCover
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J3LocalDet
public import CFSG.LocalAnalysis.SectionRank.LocalDet
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.Alternating.Multipliers.Small
public import CFSG.RankThree.PerfectCover.HopfCover
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.GroupTheory.TitsSystem.Parabolic
public import CFSG.GH74.GLS.SP.DatumBN
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.Universal.SymplecticExtras.Torus
public import CFSG.LieType.Universal.SymplecticExtras.Unipotent
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSL
public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.Universal.Unitary
public import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.LieType.Universal.Unitary.Extras.Torus
public import CFSG.LieType.Steinberg.CentralExt.SUBruhatExtras
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.OppositeBorel
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LieType.Ree.FixedTwoCellParabolics
public import CFSG.LieType.Ree.FixedSubgroupData
public import CFSG.LieType.Ree.ReeGenericPerfect
public import CFSG.LieType.Steinberg.CentralExt.TorusLift
public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.GraphFixedSimpleBruhat
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.CurtisTits.Spin
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRestSpinPlus
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusPosLift
import all CFSG.LieType.Universal.Spin.Structure.TypeB
import CFSG.LieType.Universal.Spin.Structure.Levels
import CFSG.LieType.Universal.Spin.Structure.Entries

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Basic

variable {G : Type} [Group G]

@[expose] def twoResidual (H : Subgroup G) : Subgroup G :=
  (sInf {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}).map H.subtype

@[expose] def IsTwoCentralInvolution (t : G) : Prop :=
  t ^ 2 = 1 ∧ t ≠ 1 ∧
    ∃ T : Sylow 2 G, t ∈ (T : Subgroup G) ∧ ∀ x ∈ (T : Subgroup G), x * t = t * x

@[expose] def IsMaxParabolicTwo (P : Subgroup G) : Prop :=
  P ≠ ⊤ ∧ ∃ S : Sylow 2 G, Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ P ∧
    ∀ Q : Subgroup G, Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Q → Q ≠ ⊤ → P ≤ Q → Q = P

@[expose] def IsZ4StarQ8Sq (X : Type) [Group X] : Prop :=
  ∃ A B C : Subgroup X, Nonempty (A ≃* Multiplicative (ZMod 4)) ∧
    Nonempty (B ≃* QuaternionGroup 2) ∧ Nonempty (C ≃* QuaternionGroup 2) ∧
    A ⊔ B ⊔ C = ⊤ ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ (∀ a ∈ A, ∀ c ∈ C, a * c = c * a) ∧
    (∀ b ∈ B, ∀ c ∈ C, b * c = c * b) ∧ Nat.card ↥(A ⊓ B) = 2 ∧ A ⊓ B = A ⊓ C ∧ A ⊓ B = B ⊓ C

@[expose] def IsS5OverE16 (J : Subgroup G) : Prop :=
  ∃ (V : Subgroup G) (_ : (V.subgroupOf J).Normal), V ≤ J ∧ IsElemAbelian 2 V ∧
    Nat.card ↥V = 16 ∧ Nonempty (↥J ⧸ V.subgroupOf J ≃* Equiv.Perm (Fin 5))

@[expose] def frattiniOf (R : Subgroup G) : Subgroup G := (frattini ↥R).map R.subtype

@[expose] def centerOf (W : Subgroup G) : Subgroup G := (Subgroup.center ↥W).map W.subtype

@[expose] def omegaOne (P : Subgroup G) : Subgroup G := Subgroup.closure {x | x ∈ P ∧ x ^ 2 = 1}

end Basic

section Quasisimple

variable (K : Type) [Group K]

@[expose] def preimageStar (Js : Subgroup (K ⧸ Subgroup.center K)) : Subgroup K :=
  Subgroup.comap (QuotientGroup.mk' (Subgroup.center K)) Js

@[expose] def InvolutionsLift : Prop :=
  ∀ t : K ⧸ Subgroup.center K, t ^ 2 = 1 → t ≠ 1 →
    ∃ k : K, k ^ 2 = 1 ∧ (k : K ⧸ Subgroup.center K) = t

@[expose] def TwoCentralInvolutionsLift : Prop :=
  ∀ t : K ⧸ Subgroup.center K, IsTwoCentralInvolution t →
    ∃ k : K, k ^ 2 = 1 ∧ (k : K ⧸ Subgroup.center K) = t

@[expose] def NonTwoCentralInvolutionsLiftToOrderFour : Prop :=
  ∀ t : K ⧸ Subgroup.center K, t ^ 2 = 1 → t ≠ 1 → ¬ IsTwoCentralInvolution t →
    ∃ k : K, orderOf k = 4 ∧ (k : K ⧸ Subgroup.center K) = t

@[expose] def OuterInvolutionsInvertOrderFour : Prop :=
  ∀ α : K ≃* K, (∀ k, α (α k) = k) → (∀ g : K, α ≠ MulAut.conj g) →
    ∃ k : K, orderOf k = 4 ∧ (k : K ⧸ Subgroup.center K) ^ 2 = 1 ∧
      (k : K ⧸ Subgroup.center K) ≠ 1 ∧
      ¬ IsTwoCentralInvolution (k : K ⧸ Subgroup.center K) ∧ α k = k⁻¹

@[expose] def UniqueSquareInCoset (u : K) : Prop :=
  ∃! v : K, (∃ z ∈ Subgroup.center K, v = u * z) ∧
    ∃ x ∈ pCoreOf 2 (twoResidual (Subgroup.centralizer ({u} : Set K))), x ^ 2 = v

@[expose] def centralizerOfFrattiniOfCore (u : K) : Subgroup K :=
  pCoreOf 2 (twoResidual (Subgroup.centralizer ({u} : Set K))) ⊓
    Subgroup.centralizer
      (frattiniOf (pCoreOf 2 (twoResidual (Subgroup.centralizer ({u} : Set K)))) : Set K)

@[expose] def preimageLayerCentralizer (i : K ⧸ Subgroup.center K) : Subgroup K :=
  preimageStar K
    ((CFSG.layer ↥(Subgroup.centralizer ({i} : Set (K ⧸ Subgroup.center K)))).map
      (Subgroup.centralizer ({i} : Set (K ⧸ Subgroup.center K))).subtype)

end Quasisimple

section GraphField

@[expose] def invTransposeSL (n : Type) [Fintype n] [DecidableEq n] (R : Type) [CommRing R] :
    Matrix.SpecialLinearGroup n R →* Matrix.SpecialLinearGroup n R where
  toFun g := Matrix.SpecialLinearGroup.transpose g⁻¹
  map_one' := by
    apply Subtype.ext
    simp [Matrix.SpecialLinearGroup.coe_transpose]
  map_mul' g h := by
    apply Subtype.ext
    simp [Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_mul]

theorem invTransposeSL_invTransposeSL (n : Type) [Fintype n] [DecidableEq n] (R : Type)
    [CommRing R] (hn : Fintype.card n ≠ 1) (g : Matrix.SpecialLinearGroup n R) :
    invTransposeSL n R (invTransposeSL n R g) = g := by
  apply Subtype.ext
  simp only [invTransposeSL, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_transpose]
  rw [Matrix.transpose_transpose, Matrix.adjugate_adjugate _ hn,
    Matrix.SpecialLinearGroup.det_coe]
  simp

abbrev F4 : Type := GaloisField 2 2

theorem frobenius_frobenius_F4 (x : F4) : frobenius F4 2 (frobenius F4 2 x) = x := by
  let _ : Fintype F4 := Fintype.ofFinite F4
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)] at h
  simp only [frobenius_def]
  rw [← pow_mul]
  simpa using h

@[expose] noncomputable def fieldSL3 : SL(3, F4) →* SL(3, F4) :=
  Matrix.SpecialLinearGroup.map (frobenius F4 2)

theorem fieldSL3_fieldSL3 (g : SL(3, F4)) : fieldSL3 (fieldSL3 g) = g := by
  apply Subtype.ext
  ext i j
  simp [fieldSL3, frobenius_frobenius_F4]

theorem fieldSL3_invTranspose (g : SL(3, F4)) :
    fieldSL3 (invTransposeSL (Fin 3) F4 g) = invTransposeSL (Fin 3) F4 (fieldSL3 g) := by
  apply Subtype.ext
  simp [fieldSL3, invTransposeSL, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_map]
  have := RingHom.map_adjugate (frobenius F4 2) (g : Matrix (Fin 3) (Fin 3) F4)
  simpa [RingHom.mapMatrix_apply] using this

@[expose] noncomputable def graphFieldSL3 : SL(3, F4) ≃* SL(3, F4) where
  toFun g := invTransposeSL (Fin 3) F4 (fieldSL3 g)
  invFun g := invTransposeSL (Fin 3) F4 (fieldSL3 g)
  left_inv g := by
    show invTransposeSL (Fin 3) F4 (fieldSL3 (invTransposeSL (Fin 3) F4 (fieldSL3 g))) = g
    rw [fieldSL3_invTranspose, fieldSL3_fieldSL3, invTransposeSL_invTransposeSL _ _ (by simp)]
  right_inv g := by
    show invTransposeSL (Fin 3) F4 (fieldSL3 (invTransposeSL (Fin 3) F4 (fieldSL3 g))) = g
    rw [fieldSL3_invTranspose, fieldSL3_fieldSL3, invTransposeSL_invTransposeSL _ _ (by simp)]
  map_mul' g h := by
    simp [map_mul]

@[expose] noncomputable def graphFieldPSL3 : PSL(3, F4) ≃* PSL(3, F4) :=
  QuotientGroup.congr _ _ graphFieldSL3 (Subgroup.map_center_eq graphFieldSL3)

@[expose] def IsGraphFieldAut {K : Type} [Group K] (β : K ≃* K) : Prop :=
  ∃ (e : K ⧸ Subgroup.center K ≃* PSL(3, F4)) (c : PSL(3, F4)), ∀ k : K,
    e ((β k : K) : K ⧸ Subgroup.center K) =
      c * graphFieldPSL3 (e (k : K ⧸ Subgroup.center K)) * c⁻¹

end GraphField

section Fusion

variable {G : Type} [Group G]

@[expose] def IsNormalIn (K H : Subgroup G) : Prop := K ≤ H ∧ (K.subgroupOf H).Normal

@[expose] def IsWeaklyClosedIn (A B : Subgroup G) : Prop :=
  ∀ g : G, CFSG.conjugate A g ≤ B → CFSG.conjugate A g = A

@[expose] def FusionStep (𝒟 : Set (Subgroup G)) (Q R : Subgroup G) : Prop :=
  ∃ D ∈ 𝒟, ∃ x ∈ Subgroup.normalizer (D : Set G), Q ⊔ R ≤ D ∧ CFSG.conjugate Q x = R

@[expose] def IsConjugationFamily (P : Subgroup G) (𝒟 : Set (Subgroup G)) : Prop :=
  (∀ D ∈ 𝒟, D ≤ P) ∧ ∀ Q R : Subgroup G, Q ≤ P → R ≤ P → ∀ g : G,
    CFSG.conjugate Q g = R → Relation.ReflTransGen (FusionStep 𝒟) Q R

theorem conj_mem_of_normalIn {Q N : Subgroup G} (h : IsNormalIn Q N)
    {q x : G} (hq : q ∈ Q) (hx : x ∈ N) : x * q * x⁻¹ ∈ Q := by
  have := h.2.conj_mem ⟨q, h.1 hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem conj_eq_of_normalIn {Q N : Subgroup G} (h : IsNormalIn Q N)
    {x : G} (hx : x ∈ N) : CFSG.conjugate Q x = Q := by
  ext y
  simp only [CFSG.conjugate, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have := conj_mem_of_normalIn h hq (N.inv_mem hx)
    simpa using this
  · intro hy
    refine ⟨x * y * x⁻¹, conj_mem_of_normalIn h hy hx, by group⟩

theorem weaklyClosed_of_fusion {P : Subgroup G} {𝒟 : Set (Subgroup G)}
    (hfam : IsConjugationFamily P 𝒟) {Q : Subgroup G} (hQP : Q ≤ P)
    (hn : ∀ D ∈ 𝒟, Q ≤ D → IsNormalIn Q (Subgroup.normalizer (D : Set G))) :
    IsWeaklyClosedIn Q P := by
  intro g hg
  have hchain := hfam.2 Q (CFSG.conjugate Q g) hQP hg g rfl
  have key : ∀ R, Relation.ReflTransGen (FusionStep 𝒟) Q R → R = Q := by
    intro R hR
    induction hR with
    | refl => rfl
    | tail _ hstep ih =>
      subst ih
      obtain ⟨D, hD, x, hx, hle, hconj⟩ := hstep
      rw [← hconj]
      exact conj_eq_of_normalIn (hn D hD (le_sup_left.trans hle)) hx
  exact key _ hchain

end Fusion

section BNPair

open CFSG.Open CFSG.Blueprint

section Bridge

open scoped Pointwise

variable {G : Type} [Group G]

structure burnsideI2BN_Pre (p : ℕ) (B N : Subgroup G) : Prop where
  gen : B ⊔ N = ⊤
  normal_inter : ((B ⊓ N).subgroupOf N).Normal
  coxeter : ∃ S : Set G, (∀ s ∈ S, s ∈ N ∧ s ∉ B ∧ s ^ 2 ∈ B) ∧
    Subgroup.closure S ⊔ (B ⊓ N) = N ∧
    (∀ s ∈ S, ∀ w ∈ N, ∀ b ∈ B, ∃ b₁ ∈ B, ∃ b₂ ∈ B,
      s * b * w = b₁ * w * b₂ ∨ s * b * w = b₁ * (s * w) * b₂) ∧
    (∀ s ∈ S, ∃ b ∈ B, s * b * s ∉ B)
  split : ∃ U : Subgroup G, U ≤ B ∧ (U.subgroupOf B).Normal ∧ IsPGroup p U ∧
    U ⊓ N = ⊥ ∧ U ⊔ (B ⊓ N) = B ∧ (⨅ n ∈ N, CFSG.conjugate B n) = B ⊓ N

theorem burnsideI2BN_toPre {p : ℕ} {B N : Subgroup G} (hBN : IsSplitBNPair p B N) :
    burnsideI2BN_Pre p B N := by
  obtain ⟨U, hUB, hUn, hUp, -, hUN, hUH, hsat⟩ := hBN.split
  exact ⟨hBN.gen, hBN.normal_inter, hBN.coxeter, U, hUB, hUn, hUp, hUN, hUH, hsat⟩

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem in
theorem burnsideI2BN_exists_isBNPair {p : ℕ} {B N : Subgroup G} [(cartan B N).Normal]
    (hBN : burnsideI2BN_Pre p B N) : ∃ S : Set (WeylGroup B N), IsBNPair B N S := by
  obtain ⟨S₀, hS₁, hS₂, hS₃, hS₄⟩ := hBN.coxeter
  refine ⟨{w | ∃ n : N, (n : G) ∈ S₀ ∧ (n : WeylGroup B N) = w}, hBN.gen, ?_, ?_, ?_, ?_⟩
  · rintro w ⟨n, hn, rfl⟩
    obtain ⟨-, hnB, hn2⟩ := hS₁ _ hn
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, mk_eq_one_iff]
      simpa using hn2
    · rw [Ne, mk_eq_one_iff]
      exact hnB
  · rw [eq_top_iff]
    intro w _
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    let K : Subgroup N := (Subgroup.closure
      {w | ∃ n : N, (n : G) ∈ S₀ ∧ (n : WeylGroup B N) = w}).comap
        (QuotientGroup.mk' (cartan B N))
    have hle : Subgroup.closure S₀ ⊔ (B ⊓ N) ≤ K.map N.subtype := by
      refine sup_le ((Subgroup.closure_le _).2 fun s hs => ?_) fun h hh => ?_
      · refine ⟨⟨s, (hS₁ s hs).1⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        exact Subgroup.subset_closure ⟨⟨s, (hS₁ s hs).1⟩, hs, rfl⟩
      · obtain ⟨hhB, hhN⟩ := Subgroup.mem_inf.1 hh
        refine ⟨⟨h, hhN⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        have : (QuotientGroup.mk' (cartan B N)) ⟨h, hhN⟩ = 1 :=
          (mk_eq_one_iff (B := B) (N := N)).2 hhB
        rw [this]
        exact Subgroup.one_mem _
    have hn : (n : G) ∈ K.map N.subtype := hle (by rw [hS₂]; exact n.2)
    obtain ⟨k, hk, hkn⟩ := hn
    have : k = n := Subtype.ext hkn
    subst this
    exact hk
  · intro n m hn x hx
    obtain ⟨n', hn'S, hn'⟩ := hn
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hx
    rw [Set.mem_singleton_iff] at ha hc
    subst ha hc
    have h₀ : ((n' : G))⁻¹ * (n : G) ∈ B := mk_eq_mk_iff.1 hn'
    have hmem := hS₃ (n' : G) hn'S (m : G) m.2 (((n' : G))⁻¹ * (n : G) * b) (B.mul_mem h₀ hb)
    obtain ⟨b₁, hb₁, b₂, hb₂, h | h⟩ := hmem
    · left
      refine mem_dc_mk_iff.2 ⟨b₁, hb₁, b₂, hb₂, ?_⟩
      calc (n : G) * b * (m : G) = (n' : G) * (((n' : G))⁻¹ * (n : G) * b) * (m : G) := by group
        _ = _ := h
    · right
      have hnm : (n : WeylGroup B N) * (m : WeylGroup B N) = ((n' * m : N) : WeylGroup B N) := by
        rw [QuotientGroup.mk_mul, hn']
      rw [hnm]
      refine mem_dc_mk_iff.2 ⟨b₁, hb₁, b₂, hb₂, ?_⟩
      calc (n : G) * b * (m : G) = (n' : G) * (((n' : G))⁻¹ * (n : G) * b) * (m : G) := by group
        _ = _ := h
  · intro n hn hEq
    obtain ⟨n', hn'S, hn'⟩ := hn
    have h₀ : ((n' : G))⁻¹ * (n : G) ∈ B := mk_eq_mk_iff.1 hn'
    obtain ⟨b, hb, hnb⟩ := hS₄ (n' : G) hn'S
    have hmem : (n : G) * (((n : G))⁻¹ * (n' : G) * b) * (n : G) ∈
        ({(n : G)} : Set G) * (B : Set G) * {(n : G)} :=
      ⟨_, ⟨(n : G), rfl, _, B.mul_mem (by simpa using B.inv_mem h₀) hb, rfl⟩, (n : G), rfl, rfl⟩
    rw [hEq] at hmem
    apply hnb
    have h1 : (n' : G) * b * (n' : G) =
        ((n : G) * (((n : G))⁻¹ * (n' : G) * b) * (n : G)) * (((n' : G))⁻¹ * (n : G))⁻¹ := by
      group
    rw [h1]
    exact B.mul_mem hmem (B.inv_mem h₀)

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem in
theorem burnsideI2BN_normalizer_borel {p : ℕ} {B N : Subgroup G} (hBN : burnsideI2BN_Pre p B N) :
    Subgroup.normalizer (B : Set G) = B := by
  haveI : (cartan B N).Normal := hBN.normal_inter
  obtain ⟨S, hS⟩ := burnsideI2BN_exists_isBNPair hBN
  have := hS.normalizer_parabolic (J := ∅) (Set.empty_subset _)
  rwa [parabolic_empty] at this

theorem burnsideI2BN_conj_mem_of_normalizer {p : ℕ} {B N U : Subgroup G}
    (hBN : burnsideI2BN_Pre p B N) (hUH : U ⊔ (B ⊓ N) = B)
    {n : G} (hnN : n ∈ N)
    (hnU : n ∈ Subgroup.normalizer (U : Set G)) {x : G} (hx : x ∈ B) : n * x * n⁻¹ ∈ B := by
  have hUB : U ≤ B := hUH ▸ le_sup_left
  have hnor := hBN.normal_inter
  have hle : U ⊔ (B ⊓ N) ≤ B.comap (MulAut.conj n).toMonoidHom := by
    refine sup_le (fun u hu => ?_) (fun h hh => ?_)
    · have := (Subgroup.mem_normalizer_iff.1 hnU u).1 hu
      exact hUB this
    · obtain ⟨hhB, hhN⟩ := Subgroup.mem_inf.1 hh
      have hmem : (⟨h, hhN⟩ : N) ∈ (B ⊓ N).subgroupOf N := hh
      have := hnor.conj_mem _ hmem ⟨n, hnN⟩
      exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).1
  have := hle (hUH ▸ hx)
  exact this

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem in
theorem IsSplitBNPair.exists_sylow_normalizer [Finite G] {p : ℕ} (hp : p.Prime)
    {B N : Subgroup G} (hBN : IsSplitBNPair p B N) :
    ∃ U : Sylow p G, Subgroup.normalizer ((U : Subgroup G) : Set G) = B := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (cartan B N).Normal := hBN.normal_inter
  obtain ⟨S, hS⟩ := burnsideI2BN_exists_isBNPair (burnsideI2BN_toPre hBN)
  obtain ⟨U, hUB, hUn, hUp, hUi, hUN, hUH, -⟩ := hBN.split
  have hBU : B ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1 hUn
  have hcoe : ((hUp.toSylow hUi : Sylow p G) : Subgroup G) = U := rfl
  refine ⟨hUp.toSylow hUi, ?_⟩
  rw [hcoe]
  refine le_antisymm (fun g hg => ?_) hBU
  obtain ⟨w, hw⟩ := hS.exists_mem_dc g
  obtain ⟨n, hn, b, hb, b', hb', rfl⟩ := mem_dc_iff.1 hw
  have hnU : (n : G) ∈ Subgroup.normalizer (U : Set G) := by
    have e : (n : G) = b⁻¹ * (b * n * b') * b'⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hBU hb)) hg)
      (Subgroup.inv_mem _ (hBU hb'))
  have hnorm : (n : G) ∈ Subgroup.normalizer (B : Set G) := by
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact burnsideI2BN_conj_mem_of_normalizer (burnsideI2BN_toPre hBN) hUH n.2 hnU hx
    · have := burnsideI2BN_conj_mem_of_normalizer (burnsideI2BN_toPre hBN) hUH
        (N.inv_mem n.2) (Subgroup.inv_mem _ hnU) hx
      simpa [mul_assoc] using this
  rw [burnsideI2BN_normalizer_borel (burnsideI2BN_toPre hBN)] at hnorm
  exact B.mul_mem (B.mul_mem hb hnorm) hb'

theorem burnsideI2BN_mem_conjugate {B : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate B g ↔ g * x * g⁻¹ ∈ B := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem burnsideI2BN_mem_iInf_conjugate {B N : Subgroup G} {x : G} :
    x ∈ (⨅ n ∈ N, CFSG.conjugate B n) ↔ ∀ n ∈ N, n * x * n⁻¹ ∈ B := by
  simp only [Subgroup.mem_iInf, burnsideI2BN_mem_conjugate]

theorem burnsideI2BN_center_le {p : ℕ} {B N : Subgroup G} (hBN : IsSplitBNPair p B N) :
    Subgroup.center G ≤ B ⊓ N := by
  obtain ⟨U, hUB, hUn, hUp, hUi, hUN, hUH, hsat⟩ := hBN.split
  intro z hz
  rw [← hsat, burnsideI2BN_mem_iInf_conjugate]
  intro n _
  have hcomm : n * z * n⁻¹ = z := by
    have := Subgroup.mem_center_iff.1 hz n
    rw [this]; group
  rw [hcomm]
  have hzB : z ∈ Subgroup.normalizer (B : Set G) := Subgroup.center_le_normalizer (B : Set G) hz
  rw [burnsideI2BN_normalizer_borel (burnsideI2BN_toPre hBN)] at hzB
  exact hzB

theorem burnsideI2BN_mem_map_iff {X : Type} [Group X] (q : G →* X) {C : Subgroup G}
    (hC : q.ker ≤ C) (x : G) : q x ∈ C.map q ↔ x ∈ C := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hk : y⁻¹ * x ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx]; group
    have := C.mul_mem hy (hC hk)
    simpa using this
  · intro h
    exact ⟨x, h, rfl⟩

theorem burnsideI2BN_map {X : Type} [Group X] {p : ℕ} {B N : Subgroup G}
    (hBN : IsSplitBNPair p B N) (q : G →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G) : IsSplitBNPair p (B.map q) (N.map q) := by
  have hK : q.ker ≤ B ⊓ N := hker.trans (burnsideI2BN_center_le hBN)
  have hKB : q.ker ≤ B := hK.trans inf_le_left
  have hKN : q.ker ≤ N := hK.trans inf_le_right
  have hinf : B.map q ⊓ N.map q = (B ⊓ N).map q := by
    ext x
    obtain ⟨g, rfl⟩ := hq x
    rw [Subgroup.mem_inf, burnsideI2BN_mem_map_iff q hKB, burnsideI2BN_mem_map_iff q hKN,
      burnsideI2BN_mem_map_iff q hK, Subgroup.mem_inf]
  obtain ⟨S₀, hS₁, hS₂, hS₃, hS₄⟩ := hBN.coxeter
  obtain ⟨U, hUB, hUn, hUp, hUi, hUN, hUH, hsat⟩ := hBN.split
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, hBN.gen, Subgroup.map_top_of_surjective q hq]
  · rw [hinf]
    refine (Subgroup.normal_subgroupOf_iff
      (Subgroup.map_mono inf_le_right : (B ⊓ N).map q ≤ N.map q)).2 ?_
    rintro _ _ ⟨h, hh, rfl⟩ ⟨k, hk, rfl⟩
    refine ⟨k * h * k⁻¹, ?_, by simp⟩
    exact (Subgroup.normal_subgroupOf_iff inf_le_right).1 hBN.normal_inter h k hh hk
  · refine ⟨q '' S₀, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨hsN, hsB, hs2⟩ := hS₁ s hs
      refine ⟨⟨s, hsN, rfl⟩, ?_, ?_⟩
      · rw [burnsideI2BN_mem_map_iff q hKB]; exact hsB
      · rw [← map_pow]; exact ⟨_, hs2, rfl⟩
    · rw [hinf, ← MonoidHom.map_closure, ← Subgroup.map_sup, hS₂]
    · rintro _ ⟨s, hs, rfl⟩ _ ⟨w, hw, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := hS₃ s hs w hw b hb
      refine ⟨q b₁, ⟨b₁, hb₁, rfl⟩, q b₂, ⟨b₂, hb₂, rfl⟩, ?_⟩
      rcases h with h | h
      · left; simpa only [map_mul] using congrArg q h
      · right; simpa only [map_mul] using congrArg q h
    · rintro _ ⟨s, hs, rfl⟩
      obtain ⟨b, hb, hsb⟩ := hS₄ s hs
      refine ⟨q b, ⟨b, hb, rfl⟩, ?_⟩
      rw [← map_mul, ← map_mul, burnsideI2BN_mem_map_iff q hKB]
      exact hsb
  · refine ⟨U.map q, Subgroup.map_mono hUB, ?_, hUp.map q, ?_, ?_, ?_, ?_⟩
    · refine (Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hUB)).2 ?_
      rintro _ _ ⟨u, hu, rfl⟩ ⟨b, hb, rfl⟩
      refine ⟨b * u * b⁻¹, ?_, by simp⟩
      exact (Subgroup.normal_subgroupOf_iff hUB).1 hUn u b hu hb
    · exact fun hdvd => hUi (hdvd.trans (Subgroup.index_map_dvd U hq))
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
      obtain ⟨u, hu, rfl⟩ := hxU
      have hu' : u ∈ N := (burnsideI2BN_mem_map_iff q hKN u).1 hxN
      have : u ∈ U ⊓ N := Subgroup.mem_inf.2 ⟨hu, hu'⟩
      rw [hUN, Subgroup.mem_bot] at this
      simp [this]
    · rw [hinf, ← Subgroup.map_sup, hUH]
    · ext x
      obtain ⟨g, rfl⟩ := hq x
      rw [burnsideI2BN_mem_iInf_conjugate, hinf, burnsideI2BN_mem_map_iff q hK]
      constructor
      · intro h
        have hg : g ∈ ⨅ n ∈ N, CFSG.conjugate B n := by
          rw [burnsideI2BN_mem_iInf_conjugate]
          intro n hn
          have := h (q n) ⟨n, hn, rfl⟩
          rw [← map_mul, ← map_inv, ← map_mul, burnsideI2BN_mem_map_iff q hKB] at this
          exact this
        rwa [hsat] at hg
      · intro hg n' hn'
        obtain ⟨n, hn, rfl⟩ := hn'
        rw [← hsat, burnsideI2BN_mem_iInf_conjugate] at hg
        have := hg n hn
        rw [← map_mul, ← map_inv, ← map_mul]
        exact ⟨_, this, rfl⟩

theorem burnsideI2BN_exists_lift {X : Type} [Group X] [Finite G] {p : ℕ} (hp : p.Prime)
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center G)
    (hcop : ¬ p ∣ Nat.card q.ker) {U' : Subgroup X} (hU' : IsPGroup p U') :
    ∃ U : Subgroup G, U ≤ U'.comap q ∧ IsPGroup p U ∧ U ⊓ q.ker = ⊥ ∧ U ⊔ q.ker = U'.comap q ∧
      (∀ v ∈ U'.comap q, (∃ n : ℕ, v ^ (p ^ n) = 1) → v ∈ U) ∧
      U.index = U'.index * Nat.card q.ker := by
  haveI : Finite X := Finite.of_surjective q hq
  set V : Subgroup G := U'.comap q with hV
  have hKV : q.ker ≤ V := fun k hk => by
    rw [hV, Subgroup.mem_comap, (MonoidHom.mem_ker).1 hk]; exact U'.one_mem
  set KV : Subgroup V := q.ker.subgroupOf V with hKVdef
  haveI : KV.Normal := ⟨fun k hk v => by
    rw [hKVdef, Subgroup.mem_subgroupOf] at hk ⊢
    have hc : (v : G) * (k : G) = (k : G) * (v : G) :=
      Subgroup.mem_center_iff.1 (hker hk) (v : G)
    have : (v : G) * (k : G) * (v : G)⁻¹ = (k : G) := by rw [hc]; group
    simpa [this] using hk⟩
  have hcardKV : Nat.card KV = Nat.card q.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKV).toEquiv
  have hKVker : KV = (q.comp V.subtype).ker := by
    ext v
    simp [hKVdef, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hrange : (q.comp V.subtype).range = U' := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact v.2
    · intro hx
      obtain ⟨g, rfl⟩ := hq x
      exact ⟨⟨g, hx⟩, rfl⟩
  have hindexKV : KV.index = Nat.card U' := by
    rw [hKVker, Subgroup.index_ker, hrange]
  obtain ⟨n₀, hn₀⟩ := (isPGroup_iff_card_dvd_pow (p := p) (G := U')).1 hU'
  have hcopr : Nat.Coprime (Nat.card KV) KV.index := by
    rw [hcardKV, hindexKV]
    refine Nat.Coprime.coprime_dvd_right hn₀ ?_
    exact Nat.Coprime.pow_right n₀ ((Nat.Prime.coprime_iff_not_dvd hp).2 hcop).symm
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcopr
  have hdec : ∀ v : V, ∃ k ∈ KV, ∃ h ∈ H, k * h = v := by
    intro v
    obtain ⟨⟨⟨k, hk⟩, ⟨h, hh⟩⟩, hkh, -⟩ := hH.existsUnique v
    exact ⟨k, hk, h, hh, hkh⟩
  set U : Subgroup G := H.map V.subtype with hU
  have hUV : U ≤ V := by
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hF1 : ∀ v ∈ V, ∃ k ∈ q.ker, ∃ u ∈ U, v = k * u := by
    intro v hv
    obtain ⟨k, hk, h, hh, hkh⟩ := hdec ⟨v, hv⟩
    refine ⟨(k : G), (Subgroup.mem_subgroupOf.1 hk), (h : G), ⟨h, hh, rfl⟩, ?_⟩
    exact (congrArg Subtype.val hkh).symm
  have hF2 : U ⊓ q.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨h, hh, rfl⟩, hx⟩
    have hmem : h ∈ KV := Subgroup.mem_subgroupOf.2 hx
    have := Subgroup.disjoint_def.1 hH.disjoint hmem hh
    simp [this]
  have hpel : ∀ x ∈ U, ∃ n : ℕ, x ^ (p ^ n) = 1 := by
    intro x hx
    obtain ⟨n, hn⟩ := hU' ⟨q x, hUV hx⟩
    refine ⟨n, ?_⟩
    have h1 : x ^ (p ^ n) ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact congrArg Subtype.val hn
    have h2 : x ^ (p ^ n) ∈ U ⊓ q.ker := Subgroup.mem_inf.2 ⟨U.pow_mem hx _, h1⟩
    rw [hF2, Subgroup.mem_bot] at h2
    exact h2
  have hF5 : ∀ v ∈ V, (∃ n : ℕ, v ^ (p ^ n) = 1) → v ∈ U := by
    rintro v hv ⟨n, hn⟩
    obtain ⟨k, hk, u, hu, rfl⟩ := hF1 v hv
    have hcomm : Commute k u := (Subgroup.mem_center_iff.1 (hker hk) u).symm
    rw [hcomm.mul_pow] at hn
    have hkpow : k ^ (p ^ n) = 1 := by
      have h1 : k ^ (p ^ n) ∈ q.ker := q.ker.pow_mem hk _
      have h2 : k ^ (p ^ n) ∈ U := by
        have : k ^ (p ^ n) = (u ^ (p ^ n))⁻¹ := eq_inv_of_mul_eq_one_left hn
        rw [this]
        exact U.inv_mem (U.pow_mem hu _)
      have h3 : k ^ (p ^ n) ∈ U ⊓ q.ker := Subgroup.mem_inf.2 ⟨h2, h1⟩
      rw [hF2, Subgroup.mem_bot] at h3
      exact h3
    have hk1 : k = 1 := by
      have hd1 : orderOf k ∣ p ^ n := orderOf_dvd_of_pow_eq_one hkpow
      have hd2 : orderOf k ∣ Nat.card q.ker := by
        have := Subgroup.orderOf_dvd_natCard q.ker hk
        exact this
      have hcp : Nat.Coprime (p ^ n) (Nat.card q.ker) :=
        Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hcop)
      have : orderOf k ∣ Nat.gcd (p ^ n) (Nat.card q.ker) := Nat.dvd_gcd hd1 hd2
      rw [hcp] at this
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
    rw [hk1, one_mul]
    exact hu
  have hcardU : Nat.card U = Nat.card U' := by
    have h1 : KV.index = Nat.card H := hH.symm.index_eq_card
    have h2 : Nat.card U = Nat.card H :=
      Subgroup.card_map_of_injective V.subtype_injective
    rw [h2, ← h1, hindexKV]
  refine ⟨U, hUV, ?_, hF2, ?_, hF5, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hpel x hx
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  · refine le_antisymm (sup_le hUV hKV) fun v hv => ?_
    obtain ⟨k, hk, u, hu, rfl⟩ := hF1 v hv
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hu)
  · have hGcard : Nat.card G = Nat.card X * Nat.card q.ker := by
      have h1 := Subgroup.card_mul_index q.ker
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hq, Subgroup.card_top] at h1
      rw [← h1, mul_comm]
    have h2 := Subgroup.card_mul_index U
    have h3 := Subgroup.card_mul_index U'
    have hpos : 0 < Nat.card U' := Nat.card_pos
    rw [hcardU, hGcard, ← h3] at h2
    exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans (by ring))

theorem burnsideI2BN_comap {X : Type} [Group X] [Finite G] {p : ℕ} (hp : p.Prime)
    {B' N' : Subgroup X} (hBN : IsSplitBNPair p B' N') (q : G →* X)
    (hq : Function.Surjective q) (hker : q.ker ≤ Subgroup.center G)
    (hcop : ¬ p ∣ Nat.card q.ker) : IsSplitBNPair p (B'.comap q) (N'.comap q) := by
  haveI : Finite X := Finite.of_surjective q hq
  have hKcomap : ∀ H : Subgroup X, q.ker ≤ H.comap q := fun H k hk => by
    rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hk]; exact H.one_mem
  have hKB : q.ker ≤ B'.comap q := hKcomap B'
  have hKN : q.ker ≤ N'.comap q := hKcomap N'
  have hKBN : q.ker ≤ B'.comap q ⊓ N'.comap q := le_inf hKB hKN
  have hz : ∀ g g' : G, q g = q g' → g = g' * (g'⁻¹ * g) ∧ g'⁻¹ * g ∈ q.ker := by
    intro g g' h
    refine ⟨by group, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, h]; group
  obtain ⟨S', hS₁, hS₂, hS₃, hS₄⟩ := hBN.coxeter
  obtain ⟨U', hU'B, hU'n, hU'p, hU'i, hU'N, hU'H, hsat'⟩ := hBN.split
  have hinfmap : (B'.comap q ⊓ N'.comap q).map q = B' ⊓ N' := by
    rw [← Subgroup.comap_inf, Subgroup.map_comap_eq_self_of_surjective hq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (B'.comap q ⊔ N'.comap q).map q = ⊤ := by
      rw [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hq,
        Subgroup.map_comap_eq_self_of_surjective hq, hBN.gen]
    have h2 := Subgroup.comap_map_eq_self (f := q) (H := B'.comap q ⊔ N'.comap q)
      (le_sup_of_le_left hKB)
    rw [h1, Subgroup.comap_top] at h2
    exact h2.symm
  · refine (Subgroup.normal_subgroupOf_iff inf_le_right).2 fun h k hh hk => ?_
    obtain ⟨hhB, hhN⟩ := Subgroup.mem_inf.1 hh
    have h1 : q h ∈ B' ⊓ N' := Subgroup.mem_inf.2 ⟨hhB, hhN⟩
    have h2 : q k ∈ N' := hk
    have h3 := (Subgroup.normal_subgroupOf_iff inf_le_right).1 hBN.normal_inter (q h) (q k) h1 h2
    obtain ⟨h3B, h3N⟩ := Subgroup.mem_inf.1 h3
    exact Subgroup.mem_inf.2 ⟨by simpa using h3B, by simpa using h3N⟩
  · refine ⟨q ⁻¹' S', ?_, ?_, ?_, ?_⟩
    · intro s hs
      obtain ⟨h1, h2, h3⟩ := hS₁ (q s) hs
      exact ⟨h1, h2, by simpa using h3⟩
    · have hle : q.ker ≤ Subgroup.closure (q ⁻¹' S') ⊔ (B'.comap q ⊓ N'.comap q) :=
        hKBN.trans le_sup_right
      have h1 : (Subgroup.closure (q ⁻¹' S') ⊔ (B'.comap q ⊓ N'.comap q)).map q = N' := by
        rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_preimage_eq _ hq, hinfmap, hS₂]
      have h2 := Subgroup.comap_map_eq_self (f := q) hle
      rw [h1] at h2
      exact h2.symm
    · intro s hs w hw b hb
      obtain ⟨b₁', hb₁', b₂', hb₂', h⟩ := hS₃ (q s) hs (q w) hw (q b) hb
      obtain ⟨b₁, rfl⟩ := hq b₁'
      obtain ⟨b₂, rfl⟩ := hq b₂'
      rcases h with h | h
      · obtain ⟨he, hzk⟩ := hz (s * b * w) (b₁ * w * b₂) (by simpa only [map_mul] using h)
        refine ⟨b₁, hb₁', b₂ * ((b₁ * w * b₂)⁻¹ * (s * b * w)),
          (B'.comap q).mul_mem hb₂' (hKB hzk), Or.inl ?_⟩
        calc s * b * w = (b₁ * w * b₂) * ((b₁ * w * b₂)⁻¹ * (s * b * w)) := he
          _ = _ := by group
      · obtain ⟨he, hzk⟩ := hz (s * b * w) (b₁ * (s * w) * b₂) (by simpa only [map_mul] using h)
        refine ⟨b₁, hb₁', b₂ * ((b₁ * (s * w) * b₂)⁻¹ * (s * b * w)),
          (B'.comap q).mul_mem hb₂' (hKB hzk), Or.inr ?_⟩
        calc s * b * w = (b₁ * (s * w) * b₂) * ((b₁ * (s * w) * b₂)⁻¹ * (s * b * w)) := he
          _ = _ := by group
    · intro s hs
      obtain ⟨b', hb', hnot⟩ := hS₄ (q s) hs
      obtain ⟨b, rfl⟩ := hq b'
      exact ⟨b, hb', by simpa using hnot⟩
  · obtain ⟨U, hUV, hUp, hUker, hUsup, hUel, hUidx⟩ :=
      burnsideI2BN_exists_lift hp q hq hker hcop hU'p
    have hUB : U ≤ B'.comap q := hUV.trans (Subgroup.comap_mono hU'B)
    refine ⟨U, hUB, ?_, hUp, ?_, ?_, ?_, ?_⟩
    · refine (Subgroup.normal_subgroupOf_iff hUB).2 fun u b hu hb => ?_
      obtain ⟨n, hn⟩ := hUp ⟨u, hu⟩
      have hun : u ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
      refine hUel _ ?_ ⟨n, ?_⟩
      · have := (Subgroup.normal_subgroupOf_iff hU'B).1 hU'n (q u) (q b) (hUV hu) hb
        simpa using this
      · rw [conj_pow, hun]; group
    · intro hd
      rw [hUidx] at hd
      rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
      · exact hU'i h
      · exact hcop h
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
      have h1 : q x ∈ U' ⊓ N' := Subgroup.mem_inf.2 ⟨hUV hxU, hxN⟩
      rw [hU'N, Subgroup.mem_bot] at h1
      have h2 : x ∈ U ⊓ q.ker := Subgroup.mem_inf.2 ⟨hxU, h1⟩
      rwa [hUker] at h2
    · refine le_antisymm (sup_le hUB inf_le_left) ?_
      have h1 : B'.comap q = U'.comap q ⊔ (B'.comap q ⊓ N'.comap q) := by
        rw [← Subgroup.comap_inf, Subgroup.comap_sup_eq q U' (B' ⊓ N') hq, hU'H]
      refine h1.le.trans ?_
      rw [← hUsup]
      exact sup_le (sup_le le_sup_left (hKBN.trans le_sup_right)) le_sup_right
    · ext x
      rw [burnsideI2BN_mem_iInf_conjugate]
      constructor
      · intro h
        have hx : q x ∈ ⨅ n ∈ N', CFSG.conjugate B' n := by
          rw [burnsideI2BN_mem_iInf_conjugate]
          intro n' hn'
          obtain ⟨n, rfl⟩ := hq n'
          have := h n hn'
          simpa using this
        rw [hsat'] at hx
        exact hx
      · intro hx n hn
        have hx' : q x ∈ ⨅ n ∈ N', CFSG.conjugate B' n := by rw [hsat']; exact hx
        rw [burnsideI2BN_mem_iInf_conjugate] at hx'
        have := hx' (q n) hn
        simpa using this

theorem splitBNPair_iff_of_central_primeToP_surjection [Finite G]
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (q : G →* X) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center G) (hcoprime : ¬ p ∣ Nat.card q.ker) :
    (∃ B N : Subgroup G, IsSplitBNPair p B N) ↔
      ∃ B N : Subgroup X, IsSplitBNPair p B N := by
  constructor
  · rintro ⟨B, N, h⟩
    exact ⟨B.map q, N.map q, burnsideI2BN_map h q hq hcentral⟩
  · rintro ⟨B, N, h⟩
    exact ⟨B.comap q, N.comap q, burnsideI2BN_comap hp h q hq hcentral hcoprime⟩

theorem burnsideI2BN_index_eq {B U H : Subgroup G} (hUB : U ≤ B)
    (hUn : (U.subgroupOf B).Normal) (hHB : H ≤ B) (hUH : U ⊔ H = B) (hinf : U ⊓ H = ⊥) :
    U.index = Nat.card H * B.index := by
  have h1 : U.relIndex B = Nat.card H := by
    haveI : (U.subgroupOf B).Normal := hUn
    have hsup : H.subgroupOf B ⊔ U.subgroupOf B = ⊤ := by
      have := Subgroup.comap_sup_eq_of_le_range (f := B.subtype) (H := H) (K := U)
        (by rw [Subgroup.range_subtype]; exact hHB) (by rw [Subgroup.range_subtype]; exact hUB)
      change (H.comap B.subtype) ⊔ (U.comap B.subtype) = ⊤
      rw [this, sup_comm, hUH]
      exact Subgroup.subgroupOf_self B
    have h2 := Subgroup.relIndex_sup_right (H.subgroupOf B) (U.subgroupOf B)
    rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hHB] at h2
    have h3 : U.subgroupOf H = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (x : G) ∈ U ⊓ H := Subgroup.mem_inf.2 ⟨hx, x.2⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have h4 : U.relIndex H = Nat.card H := by
      rw [Subgroup.relIndex, h3, Subgroup.index_bot]
    exact h2.trans h4
  rw [← Subgroup.relIndex_mul_index hUB, h1]

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem in
theorem burnsideI2BN_index_borel [Finite G] {p : ℕ} (hp : p.Prime) {B N : Subgroup G}
    (hBN : burnsideI2BN_Pre p B N) : ¬ p ∣ B.index := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (cartan B N).Normal := hBN.normal_inter
  obtain ⟨S, hS⟩ := burnsideI2BN_exists_isBNPair hBN
  obtain ⟨U, hUB, hUn, hUp, hUN, hUH, hsat⟩ := hBN.split
  have hfix : MulAction.fixedPoints U (G ⧸ B) = {(QuotientGroup.mk (1 : G) : G ⧸ B)} := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [Set.mem_singleton_iff, MulAction.mem_fixedPoints]
    constructor
    · intro hfx
      have hgU : ∀ u ∈ U, g⁻¹ * u * g ∈ B := by
        intro u hu
        have h1 : (QuotientGroup.mk (((⟨u⁻¹, U.inv_mem hu⟩ : U) : G) * g) : G ⧸ B) =
            QuotientGroup.mk g := hfx ⟨u⁻¹, U.inv_mem hu⟩
        have h2 := QuotientGroup.eq.1 h1
        simpa [mul_assoc] using h2
      obtain ⟨w, hw⟩ := hS.exists_mem_dc g
      obtain ⟨n, hn, b, hb, b', hb', rfl⟩ := mem_dc_iff.1 hw
      have hclaim1 : ∀ u₀ ∈ U, (n : G)⁻¹ * u₀ * n ∈ B := by
        intro u₀ hu₀
        have hu : b * u₀ * b⁻¹ ∈ U := (Subgroup.normal_subgroupOf_iff hUB).1 hUn u₀ b hu₀ hb
        have h1 := hgU _ hu
        have e : (n : G)⁻¹ * u₀ * n =
            b' * ((b * (n : G) * b')⁻¹ * (b * u₀ * b⁻¹) * (b * (n : G) * b')) * b'⁻¹ := by group
        rw [e]
        exact B.mul_mem (B.mul_mem hb' h1) (B.inv_mem hb')
      have hclaim2 : ∀ x ∈ B, (n : G)⁻¹ * x * ((n : G)⁻¹)⁻¹ ∈ B := by
        have hle : U ⊔ (B ⊓ N) ≤ B.comap (MulAut.conj (n : G)⁻¹).toMonoidHom := by
          refine sup_le (fun u hu => ?_) (fun h hh => ?_)
          · have := hclaim1 u hu
            simpa [MulAut.conj_apply] using this
          · obtain ⟨hhB, hhN⟩ := Subgroup.mem_inf.1 hh
            have hmem : (⟨h, hhN⟩ : N) ∈ (B ⊓ N).subgroupOf N := hh
            have := hBN.normal_inter.conj_mem _ hmem ⟨(n : G)⁻¹, N.inv_mem n.2⟩
            exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).1
        intro x hx
        exact hle (by rw [hUH]; exact hx)
      have hnB := (hS.mem_and_subset_of_conj_le (J := ∅) (K := ∅) (Set.empty_subset _)
        (Set.empty_subset _) (g := (n : G)⁻¹) (by
          rw [parabolic_empty]
          intro x hx
          exact hclaim2 x hx)).1
      rw [parabolic_empty] at hnB
      have hnB' : (n : G) ∈ B := by simpa using B.inv_mem hnB
      have hgB : b * (n : G) * b' ∈ B := B.mul_mem (B.mul_mem hb hnB') hb'
      exact QuotientGroup.eq.2 (by simpa using B.inv_mem hgB)
    · intro hx u
      have hgB : g ∈ B := by
        have := QuotientGroup.eq.1 hx
        simpa using B.inv_mem this
      show (QuotientGroup.mk ((u : G) * g) : G ⧸ B) = QuotientGroup.mk g
      refine QuotientGroup.eq.2 ?_
      have : ((u : G) * g)⁻¹ * g = g⁻¹ * ((u : G))⁻¹ * g := by group
      rw [this]
      exact B.mul_mem (B.mul_mem (B.inv_mem hgB) (B.inv_mem (hUB u.2))) hgB
  have hmod := hUp.card_modEq_card_fixedPoints (G ⧸ B)
  have hone : Nat.card (↥({(QuotientGroup.mk (1 : G) : G ⧸ B)} : Set (G ⧸ B))) = 1 :=
    Nat.card_unique
  rw [hfix, hone] at hmod
  intro hdvd
  have h1 : Nat.card (G ⧸ B) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hdvd
  have h2 : 1 ≡ 0 [MOD p] := hmod.symm.trans h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd).1 h2))

theorem burnsideI2BN_toIsSplit [Finite G] {p : ℕ} (hp : p.Prime) {B N : Subgroup G}
    (hBN : burnsideI2BN_Pre p B N) (hH : ¬ p ∣ Nat.card (B ⊓ N : Subgroup G)) :
    IsSplitBNPair p B N := by
  obtain ⟨U, hUB, hUn, hUp, hUN, hUH, hsat⟩ := hBN.split
  refine ⟨hBN.gen, hBN.normal_inter, hBN.coxeter, U, hUB, hUn, hUp, ?_, hUN, hUH, hsat⟩
  have hinf : U ⊓ (B ⊓ N) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxBN⟩ := Subgroup.mem_inf.1 hx
    have : x ∈ U ⊓ N := Subgroup.mem_inf.2 ⟨hxU, (Subgroup.mem_inf.1 hxBN).2⟩
    rw [hUN] at this
    exact this
  rw [burnsideI2BN_index_eq hUB hUn (inf_le_left : B ⊓ N ≤ B) hUH hinf]
  intro hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · exact hH h
  · exact burnsideI2BN_index_borel hp hBN h

open CFSG.GH74.BNPair in
theorem burnsideI2BN_sat_of_isSaturated {B N : Subgroup G} (hsat : IsSaturated B N) :
    (⨅ n ∈ N, CFSG.conjugate B n) = B ⊓ N := by
  ext x
  rw [burnsideI2BN_mem_iInf_conjugate]
  have hx := Subgroup.ext_iff.1 hsat x
  have key : ∀ m : G, x ∈ B.map (MulAut.conj m⁻¹).toMonoidHom ↔ m * x * m⁻¹ ∈ B :=
    fun m => burnsideI2BN_mem_conjugate
  simp only [Subgroup.mem_iInf, key] at hx
  constructor
  · intro h'
    exact hx.2 fun m => h' m m.2
  · intro h' m hm
    exact hx.1 h' ⟨m, hm⟩

theorem burnsideI2BN_sat_of_opposite {B N : Subgroup G}
    (hnorm : ((B ⊓ N).subgroupOf N).Normal) {c : G} (hc : c ∈ N)
    (hopp : ∀ z ∈ B, c⁻¹ * z * c ∈ B → z ∈ N) :
    (⨅ n ∈ N, CFSG.conjugate B n) = B ⊓ N := by
  ext x
  rw [burnsideI2BN_mem_iInf_conjugate]
  constructor
  · intro h
    have h1 : x ∈ B := by simpa using h 1 N.one_mem
    have h2 : c⁻¹ * x * c ∈ B := by simpa using h c⁻¹ (N.inv_mem hc)
    exact Subgroup.mem_inf.2 ⟨h1, hopp x h1 h2⟩
  · intro hx n hn
    have := (Subgroup.normal_subgroupOf_iff inf_le_right).1 hnorm x n hx hn
    exact (Subgroup.mem_inf.1 this).1

open CFSG.GH74.BNPair CFSG.GroupActions in
theorem burnsideI2BN_pre_of_splitBN {p : ℕ} {B N U : Subgroup G} {I : Type*} {n : I → N}
    (h : SplitBN B N U n) (hUp : IsPGroup p U)
    (hsat : (⨅ n ∈ N, CFSG.conjugate B n) = B ⊓ N) :
    burnsideI2BN_Pre p B N := by
  obtain ⟨hnorm, hgen, hinj, hord, hclos, hmul, hne, hUB, hUn, hnil, hcomm, hBU, hUH⟩ := h
  have hmk1 : ∀ i, ((n i : N) : WeylGroup B N) ≠ 1 := fun i h1 => by
    have := hord i
    rw [h1] at this
    simp at this
  have hsq : ∀ i, ((n i : N) : G) ^ 2 ∈ B := by
    intro i
    have h1 : ((n i : N) : WeylGroup B N) ^ 2 = 1 := by
      have := pow_orderOf_eq_one ((n i : N) : WeylGroup B N)
      rwa [hord i] at this
    rw [← QuotientGroup.mk_pow, mk_eq_one_iff] at h1
    simpa using h1
  have hnotB : ∀ i, ((n i : N) : G) ∉ B := fun i hi => hmk1 i (mk_eq_one_iff.2 hi)
  have hUN : U ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
    have : x ∈ U ⊓ (B ⊓ N) := Subgroup.mem_inf.2 ⟨hxU, Subgroup.mem_inf.2 ⟨hUB hxU, hxN⟩⟩
    rw [hUH] at this
    exact this
  refine ⟨hgen, hnorm, ⟨Set.range fun i => ((n i : N) : G), ?_, ?_, ?_, ?_⟩,
    ⟨U, hUB, hUn, hUp, hUN, ?_, ?_⟩⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨(n i).2, hnotB i, hsq i⟩
  · refine le_antisymm (sup_le ((Subgroup.closure_le N).2 (by rintro _ ⟨i, rfl⟩; exact (n i).2))
      inf_le_right) fun g hg => ?_
    set L : Subgroup N := (Subgroup.closure (Set.range fun i => ((n i : N) : G)) ⊔
      (B ⊓ N)).comap N.subtype with hL
    have hLclos : (⊤ : Subgroup (WeylGroup B N)) ≤ L.map (QuotientGroup.mk' (cartan B N)) := by
      rw [← hclos, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine ⟨n i, ?_, rfl⟩
      rw [SetLike.mem_coe, hL, Subgroup.mem_comap]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, rfl⟩)
    obtain ⟨l, hl, hlg⟩ := hLclos (Subgroup.mem_top (QuotientGroup.mk (⟨g, hg⟩ : N)))
    have hcart : l⁻¹ * (⟨g, hg⟩ : N) ∈ cartan B N := QuotientGroup.eq.1 hlg
    have hcL : l⁻¹ * (⟨g, hg⟩ : N) ∈ L := by
      rw [hL, Subgroup.mem_comap]
      exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hcart)
    have := L.mul_mem hl hcL
    rw [mul_inv_cancel_left] at this
    exact this
  · rintro _ ⟨i, rfl⟩ w hw b hb
    have hmem : ((n i : N) : G) * b * w ∈ ({((n i : N) : G)} : Set G) * (B : Set G) * {w} :=
      ⟨_, ⟨_, rfl, b, hb, rfl⟩, w, rfl, rfl⟩
    rcases hmul i w hw hmem with ⟨_, ⟨b₁, hb₁, c, hc, rfl⟩, b₂, hb₂, he⟩ |
        ⟨_, ⟨b₁, hb₁, c, hc, rfl⟩, b₂, hb₂, he⟩
    · rw [Set.mem_singleton_iff] at hc
      subst hc
      exact ⟨b₁, hb₁, b₂, hb₂, Or.inr he.symm⟩
    · rw [Set.mem_singleton_iff] at hc
      subst hc
      exact ⟨b₁, hb₁, b₂, hb₂, Or.inl he.symm⟩
  · rintro _ ⟨i, rfl⟩
    by_contra hcon
    push Not at hcon
    apply hne i
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    rw [Set.mem_singleton_iff] at ha hc
    subst ha hc
    have h1 := hcon b hb
    have e : ((n i : N) : G) * b * ((n i : N) : G)⁻¹ =
        (((n i : N) : G) * b * ((n i : N) : G)) * (((n i : N) : G) ^ 2)⁻¹ := by group
    have e2 : (((n i : N) : G) * b * (((n i : N) : G)⁻¹)) =
        ((n i : N) : G) * b * (((n i : N) : G)⁻¹) := rfl
    show ((n i : N) : G) * b * (((n i : N) : G))⁻¹ ∈ B
    rw [e]
    exact B.mul_mem h1 (B.inv_mem (hsq i))
  · refine le_antisymm (sup_le hUB inf_le_left) fun x hx => ?_
    have hx' : x ∈ (U : Set G) * ((B ⊓ N : Subgroup G) : Set G) := hBU ▸ hx
    obtain ⟨u, hu, h, hh, rfl⟩ := hx'
    exact Subgroup.mul_mem_sup hu hh
  · exact hsat

open CFSG.GH74.BNPair CFSG.GroupActions in
theorem burnsideI2BN_of_splitBN [Finite G] {p : ℕ} (hp : p.Prime) {B N U : Subgroup G}
    {I : Type*} {n : I → N} (h : SplitBN B N U n) (hUp : IsPGroup p U)
    (hsat : (⨅ n ∈ N, CFSG.conjugate B n) = B ⊓ N)
    (hH : ¬ p ∣ Nat.card (B ⊓ N : Subgroup G)) :
    IsSplitBNPair p B N :=
  burnsideI2BN_toIsSplit hp (burnsideI2BN_pre_of_splitBN h hUp hsat) hH

end Bridge

section Helpers

variable {G : Type} [Group G]

theorem burnsideI2BN_charP_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : CharP K p := by
  have : Fintype K := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hp', hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, hK] at hn
  have hdvd : p ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn]
    exact dvd_pow_self p (by omega)
  have : p = ringChar K := (Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow hdvd)
  rw [this]
  infer_instance

theorem burnsideI2BN_pow_eq_one_of_triangular {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] (s : κ → ℤ)
    {M : Matrix κ κ F} (hM : ∀ a b, s b - s a < 1 → M a b = (1 : Matrix κ κ F) a b) :
    ∃ k : ℕ, M ^ (p ^ k) = 1 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · exact ⟨0, Subsingleton.elim _ _⟩
  set N : Matrix κ κ F := M - 1 with hN
  have hNzero : ∀ a b, s b - s a < 1 → N a b = 0 := by
    intro a b h
    simp [hN, Matrix.sub_apply, hM a b h]
  have hpow : ∀ k : ℕ, ∀ a b, (N ^ k) a b ≠ 0 → (k : ℤ) ≤ s b - s a := by
    intro k
    induction k with
    | zero =>
      intro a b h
      have hab : a = b := by
        by_contra hne
        exact h (by simp [Matrix.one_apply_ne hne])
      subst hab
      simp
    | succ k ih =>
      intro a b h
      rw [pow_succ', Matrix.mul_apply] at h
      obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have h1 : N a c ≠ 0 := left_ne_zero_of_mul hc
      have h2 : (N ^ k) c b ≠ 0 := right_ne_zero_of_mul hc
      have h1' : 1 ≤ s c - s a := by
        by_contra hlt
        exact h1 (hNzero a c (by omega))
      have := ih c b h2
      push_cast
      omega
  set B : ℕ := 2 * ∑ a, (s a).natAbs + 1 with hB
  have hNB : N ^ B = 0 := by
    ext a b
    by_contra h
    have h0 := hpow B a b h
    have h1 : (s b).natAbs ≤ ∑ a, (s a).natAbs :=
      Finset.single_le_sum (f := fun a => (s a).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    have h2 : (s a).natAbs ≤ ∑ a, (s a).natAbs :=
      Finset.single_le_sum (f := fun a => (s a).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ a)
    omega
  refine ⟨B, ?_⟩
  have hMN : M = 1 + N := by rw [hN]; abel
  have hle : B ≤ p ^ B := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have hcomm : Commute (1 : Matrix κ κ F) N := Commute.one_left N
  rw [hMN, add_pow_char_pow_of_commute p B hcomm, one_pow]
  have : N ^ (p ^ B) = 0 := by
    rw [← Nat.add_sub_cancel' hle, pow_add, hNB, zero_mul]
  rw [this, add_zero]

theorem burnsideI2BN_not_dvd_card_of_pow_eq_one {K : Type*} [Group K] {p m : ℕ} [Fact p.Prime]
    {T : Subgroup K} [Finite T] (hT : ∀ x ∈ T, x ^ m = 1) (hpm : ¬ p ∣ m) :
    ¬ p ∣ Nat.card T := by
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  apply hpm
  rw [← hx]
  exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hT x x.2))

theorem burnsideI2BN_not_dvd_card_sub_one {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card F) : ¬ p ∣ Nat.card F - 1 := by
  intro h
  have h1 : 1 ≤ Nat.card F := Nat.card_pos
  have h2 := Nat.dvd_sub hdvd h
  rw [Nat.sub_sub_self h1] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem burnsideI2BN_units_pow_card_sub_one {F : Type} [Field F] [Finite F] (u : Fˣ) :
    u ^ (Nat.card F - 1) = 1 := by
  have : Fintype F := Fintype.ofFinite F
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ u.ne_zero

theorem burnsideI2BN_rankOne_conj_inv {H : Subgroup G} {w : G}
    (hwH : ∀ h ∈ H, w * h * w⁻¹ ∈ H) (hw2 : w * w ∈ H) {h : G} (hh : h ∈ H) :
    w⁻¹ * h * w ∈ H := by
  have e : w⁻¹ * h * w = (w * w)⁻¹ * (w * h * w⁻¹) * (w * w) := by group
  rw [e]
  exact H.mul_mem (H.mul_mem (H.inv_mem hw2) (hwH h hh)) hw2

def burnsideI2BN_rankOneN (H : Subgroup G) (w : G) (hwH : ∀ h ∈ H, w * h * w⁻¹ ∈ H)
    (hw2 : w * w ∈ H) : Subgroup G where
  carrier := {g | g ∈ H ∨ ∃ h ∈ H, g = h * w}
  mul_mem' := by
    rintro x y (hx | ⟨h₁, hh₁, rfl⟩) (hy | ⟨h₂, hh₂, rfl⟩)
    · exact Or.inl (H.mul_mem hx hy)
    · exact Or.inr ⟨x * h₂, H.mul_mem hx hh₂, by group⟩
    · exact Or.inr ⟨h₁ * (w * y * w⁻¹), H.mul_mem hh₁ (hwH y hy), by group⟩
    · refine Or.inl ?_
      have e : h₁ * w * (h₂ * w) = h₁ * (w * h₂ * w⁻¹) * (w * w) := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hh₁ (hwH h₂ hh₂)) hw2
  one_mem' := Or.inl H.one_mem
  inv_mem' := by
    rintro x (hx | ⟨h, hh, rfl⟩)
    · exact Or.inl (H.inv_mem hx)
    · refine Or.inr ⟨w⁻¹ * h⁻¹ * w⁻¹, ?_, by group⟩
      have e : w⁻¹ * h⁻¹ * w⁻¹ = (w⁻¹ * h⁻¹ * w) * (w * w)⁻¹ := by group
      rw [e]
      exact H.mul_mem (burnsideI2BN_rankOne_conj_inv hwH hw2 (H.inv_mem hh)) (H.inv_mem hw2)

theorem burnsideI2BN_rankOne [Finite G] {p : ℕ} (hp : p.Prime) {B H U : Subgroup G} {w : G}
    (hcell : ∀ g : G, g ∈ B ∨ ∃ b ∈ B, ∃ b' ∈ B, g = b * w * b')
    (hwB : w ∉ B) (hHB : H ≤ B) (hwH : ∀ h ∈ H, w * h * w⁻¹ ∈ H) (hw2 : w * w ∈ H)
    (hbn3 : ∃ b ∈ B, w * b * w ∉ B)
    (hUB : U ≤ B) (hUn : (U.subgroupOf B).Normal) (hUp : IsPGroup p U)
    (hUH : U ⊓ H = ⊥) (hUHB : U ⊔ H = B)
    (hopp : ∀ z ∈ B, w⁻¹ * z * w ∈ B → z ∈ H)
    (hHp : ¬ p ∣ Nat.card H) :
    ∃ N : Subgroup G, IsSplitBNPair p B N := by
  set N := burnsideI2BN_rankOneN H w hwH hw2 with hN
  have hmemN : ∀ g, g ∈ N ↔ g ∈ H ∨ ∃ h ∈ H, g = h * w := fun g => Iff.rfl
  have hwN : w ∈ N := (hmemN w).2 (Or.inr ⟨1, H.one_mem, by group⟩)
  have hHN : H ≤ N := fun h hh => (hmemN h).2 (Or.inl hh)
  have hBN : B ⊓ N = H := by
    refine le_antisymm (fun g hg => ?_) (le_inf hHB hHN)
    obtain ⟨hgB, hgN⟩ := Subgroup.mem_inf.1 hg
    rcases (hmemN g).1 hgN with h | ⟨h, hh, rfl⟩
    · exact h
    · exfalso
      apply hwB
      have := B.mul_mem (B.inv_mem (hHB hh)) hgB
      simpa using this
  have hnorm : ((B ⊓ N).subgroupOf N).Normal := by
    rw [hBN]
    refine (Subgroup.normal_subgroupOf_iff hHN).2 fun h n hh hn => ?_
    rcases (hmemN n).1 hn with h₀ | ⟨h₀, hh₀, rfl⟩
    · exact H.mul_mem (H.mul_mem h₀ hh) (H.inv_mem h₀)
    · have e : h₀ * w * h * (h₀ * w)⁻¹ = h₀ * (w * h * w⁻¹) * h₀⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hh₀ (hwH h hh)) (H.inv_mem hh₀)
  have hsat : (⨅ n ∈ N, CFSG.conjugate B n) = B ⊓ N :=
    burnsideI2BN_sat_of_opposite hnorm hwN fun z hz hz' => hHN (hopp z hz hz')
  have hpre : burnsideI2BN_Pre p B N := by
    refine ⟨?_, hnorm, ⟨{w}, ?_, ?_, ?_, ?_⟩, U, hUB, hUn, hUp, ?_, ?_, hsat⟩
    · refine eq_top_iff.2 fun g _ => ?_
      rcases hcell g with hg | ⟨b, hb, b', hb', rfl⟩
      · exact Subgroup.mem_sup_left hg
      · exact mul_mem (mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hwN))
          (Subgroup.mem_sup_left hb')
    · intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact ⟨hwN, hwB, by rw [pow_two]; exact hHB hw2⟩
    · rw [hBN]
      refine le_antisymm (sup_le ((Subgroup.closure_le N).2 (by simpa using hwN)) hHN)
        fun g hg => ?_
      rcases (hmemN g).1 hg with hgH | ⟨h, hh, rfl⟩
      · exact Subgroup.mem_sup_right hgH
      · exact mul_mem (Subgroup.mem_sup_right hh)
          (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))
    · intro s hs x hx b hb
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      rcases (hmemN x).1 hx with hxH | ⟨h, hh, rfl⟩
      · refine ⟨1, B.one_mem, x⁻¹ * b * x,
          B.mul_mem (B.mul_mem (B.inv_mem (hHB hxH)) hb) (hHB hxH), Or.inr ?_⟩
        group
      · rcases hcell (w * b * (h * w)) with hB' | ⟨b₁', hb₁', b₂', hb₂', he⟩
        · have hwx : w * (h * w) ∈ B := by
            have e : w * (h * w) = (w * h * w⁻¹) * (w * w) := by group
            rw [e]
            exact hHB (H.mul_mem (hwH h hh) hw2)
          refine ⟨w * b * (h * w) * (w * (h * w))⁻¹, B.mul_mem hB' (B.inv_mem hwx), 1,
            B.one_mem, Or.inr ?_⟩
          group
        · refine ⟨b₁' * h⁻¹, B.mul_mem hb₁' (B.inv_mem (hHB hh)), b₂', hb₂', Or.inl ?_⟩
          rw [he]
          group
    · intro s hs
      rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hbn3
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
      rcases (hmemN x).1 hxN with hxH | ⟨h, hh, rfl⟩
      · have : x ∈ U ⊓ H := Subgroup.mem_inf.2 ⟨hxU, hxH⟩
        rw [hUH] at this
        exact this
      · exfalso
        apply hwB
        have := B.mul_mem (B.inv_mem (hHB hh)) (hUB hxU)
        simpa using this
    · rw [hBN]
      exact hUHB
  exact ⟨N, burnsideI2BN_toIsSplit hp hpre (by rw [hBN]; exact hHp)⟩

theorem burnsideI2BN_isSplit_sub {X : Type} [Group X] {Γ B N U : Subgroup X} [Finite Γ]
    {p : ℕ} (hp : p.Prime) (hBΓ : B ≤ Γ) (hNΓ : N ≤ Γ) (hgen : B ⊔ N = Γ)
    (hnorm : ((B ⊓ N).subgroupOf N).Normal) {S : Set X}
    (hS1 : ∀ s ∈ S, s ∈ N ∧ s ∉ B ∧ s ^ 2 ∈ B)
    (hS2 : Subgroup.closure S ⊔ (B ⊓ N) = N)
    (hS3 : ∀ s ∈ S, ∀ w ∈ N, ∀ b ∈ B, ∃ b₁ ∈ B, ∃ b₂ ∈ B,
      s * b * w = b₁ * w * b₂ ∨ s * b * w = b₁ * (s * w) * b₂)
    (hS4 : ∀ s ∈ S, ∃ b ∈ B, s * b * s ∉ B)
    (hUB : U ≤ B) (hUn : (U.subgroupOf B).Normal) (hUp : IsPGroup p U)
    (hUN : U ⊓ N = ⊥) (hUH : U ⊔ (B ⊓ N) = B)
    (hsat : (⨅ n ∈ N, CFSG.conjugate B n) = B ⊓ N)
    (hHp : ¬ p ∣ Nat.card (B ⊓ N : Subgroup X)) :
    IsSplitBNPair p (B.subgroupOf Γ) (N.subgroupOf Γ) := by
  have hUΓ : U ≤ Γ := hUB.trans hBΓ
  have hBNΓ : B ⊓ N ≤ Γ := inf_le_left.trans hBΓ
  have hmem : ∀ {C : Subgroup X} (x : Γ), x ∈ C.subgroupOf Γ ↔ (x : X) ∈ C :=
    fun x => Subgroup.mem_subgroupOf
  have hinf : B.subgroupOf Γ ⊓ N.subgroupOf Γ = (B ⊓ N).subgroupOf Γ := by
    ext x
    rw [Subgroup.mem_inf, hmem, hmem, hmem, Subgroup.mem_inf]
  have hpre : burnsideI2BN_Pre p (B.subgroupOf Γ) (N.subgroupOf Γ) := by
    refine ⟨?_, ?_, ⟨{s' : Γ | (s' : X) ∈ S}, ?_, ?_, ?_, ?_⟩, U.subgroupOf Γ,
      Subgroup.subgroupOf_mono Γ hUB, ?_, ?_, ?_, ?_, ?_⟩
    · have h := Subgroup.comap_sup_eq_of_le_range (f := Γ.subtype) (H := B) (K := N)
        (by rw [Subgroup.range_subtype]; exact hBΓ) (by rw [Subgroup.range_subtype]; exact hNΓ)
      change B.comap Γ.subtype ⊔ N.comap Γ.subtype = ⊤
      rw [h, hgen]
      exact Subgroup.subgroupOf_self Γ
    · rw [hinf]
      refine (Subgroup.normal_subgroupOf_iff
        (Subgroup.subgroupOf_mono Γ (inf_le_right : B ⊓ N ≤ N))).2 ?_
      intro h n hh hn
      have := (Subgroup.normal_subgroupOf_iff inf_le_right).1 hnorm (h : X) (n : X)
        ((hmem _).1 hh) ((hmem _).1 hn)
      exact (hmem _).2 (by simpa using this)
    · intro s hs
      obtain ⟨h1, h2, h3⟩ := hS1 (s : X) hs
      refine ⟨(hmem s).2 h1, fun h => h2 ((hmem s).1 h), (hmem _).2 ?_⟩
      simpa using h3
    · rw [hinf]
      refine le_antisymm (sup_le ((Subgroup.closure_le _).2 fun s hs => (hmem s).2 (hS1 _ hs).1)
        (Subgroup.subgroupOf_mono Γ (inf_le_right : B ⊓ N ≤ N))) fun g hg => ?_
      have hle : Subgroup.closure S ⊔ (B ⊓ N) ≤
          (Subgroup.closure {s' : Γ | (s' : X) ∈ S} ⊔ (B ⊓ N).subgroupOf Γ).map Γ.subtype := by
        refine sup_le ((Subgroup.closure_le _).2 fun s hs => ?_) fun h hh => ?_
        · exact ⟨⟨s, hNΓ (hS1 s hs).1⟩, Subgroup.mem_sup_left (Subgroup.subset_closure hs), rfl⟩
        · exact ⟨⟨h, hBNΓ hh⟩, Subgroup.mem_sup_right ((hmem _).2 hh), rfl⟩
      have h1 : (g : X) ∈ (Subgroup.closure {s' : Γ | (s' : X) ∈ S} ⊔
          (B ⊓ N).subgroupOf Γ).map Γ.subtype := hle (by rw [hS2]; exact (hmem g).1 hg)
      obtain ⟨y, hy, hyg⟩ := h1
      have : y = g := Subtype.ext hyg
      subst this
      exact hy
    · intro s hs w hw b hb
      obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := hS3 (s : X) hs (w : X) ((hmem w).1 hw) (b : X)
        ((hmem b).1 hb)
      exact ⟨⟨b₁, hBΓ hb₁⟩, (hmem _).2 hb₁, ⟨b₂, hBΓ hb₂⟩, (hmem _).2 hb₂,
        h.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)⟩
    · intro s hs
      obtain ⟨b, hb, hnot⟩ := hS4 (s : X) hs
      exact ⟨⟨b, hBΓ hb⟩, (hmem _).2 hb, fun h => hnot ((hmem _).1 h)⟩
    · refine (Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono Γ hUB)).2 ?_
      intro u b hu hb
      exact (hmem _).2 ((Subgroup.normal_subgroupOf_iff hUB).1 hUn (u : X) (b : X)
        ((hmem _).1 hu) ((hmem _).1 hb))
    · exact hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUΓ).symm
    · rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
      have : (x : X) ∈ U ⊓ N := Subgroup.mem_inf.2 ⟨(hmem _).1 hxU, (hmem _).1 hxN⟩
      rw [hUN, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    · rw [hinf]
      have h := Subgroup.comap_sup_eq_of_le_range (f := Γ.subtype) (H := U) (K := B ⊓ N)
        (by rw [Subgroup.range_subtype]; exact hUΓ) (by rw [Subgroup.range_subtype]; exact hBNΓ)
      change U.comap Γ.subtype ⊔ (B ⊓ N).comap Γ.subtype = B.comap Γ.subtype
      rw [h, hUH]
    · rw [hinf]
      ext x
      rw [burnsideI2BN_mem_iInf_conjugate, hmem]
      have hx := Subgroup.ext_iff.1 hsat (x : X)
      rw [burnsideI2BN_mem_iInf_conjugate] at hx
      constructor
      · intro h
        refine hx.1 fun n hn => ?_
        have := (hmem _).1 (h ⟨n, hNΓ hn⟩ ((hmem _).2 hn))
        simpa using this
      · intro h n hn
        refine (hmem _).2 ?_
        have := hx.2 h (n : X) ((hmem _).1 hn)
        simpa using this
  refine burnsideI2BN_toIsSplit hp hpre ?_
  rw [hinf]
  have : Nat.card ((B ⊓ N).subgroupOf Γ) = Nat.card (B ⊓ N : Subgroup X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBNΓ).toEquiv
  rw [this]
  exact hHp

end Helpers

section Datum

open CFSG.GH74.BNPair CFSG.GroupActions CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.GH74.GLS.SP

theorem burnsideI2BN_of_datum {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBE : BruhatExtras D H)
    (hU : IsPGroup p (posUnipotent D)) (hT : ¬ p ∣ Nat.card (⨆ i, H i : Subgroup K)) :
    IsSplitBNPair p (borel D H) (weylN n H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent (posUnipotent D) := hU.isNilpotent
  refine burnsideI2BN_of_splitBN hp (splitBN_of_datum hct hext hnil) hU
    (burnsideI2BN_sat_of_isSaturated (isSaturated_of_datum hct hext hBE)) ?_
  rw [borel_inf_weylN hct hext]
  exact hT

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras in
theorem statedSp_has_splitBNPair {p f d : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hd : 1 ≤ d) (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f) :
    ∃ B N : Subgroup ↥(StatedSp d F), IsSplitBNPair p B N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := burnsideI2BN_charP_of_card hp hf hF
  refine ⟨_, _, burnsideI2BN_of_datum hp (D := Symplectic.rootDatum d F)
    (n := Symplectic.weylRep d F) (H := Symplectic.torus d F) (Symplectic.isCTGroupDatum d F)
    (Symplectic.steinbergExtras d F) CFSG.StandardType.GGRootSp.bruhatExtras ?_ ?_⟩
  · rintro ⟨x, hx⟩
    have hidb := idBelow_of_mem_iSup (F := F) 1
      {γ | γ ∈ roots (isFiniteType_cartanC d) ∅ ∧ 0 < ht γ}
      (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hx
    obtain ⟨k, hk⟩ := burnsideI2BN_pow_eq_one_of_triangular (p := p)
      (fun a => (1 : ℤ) * lvl a) (M := mat d F x) hidb
    refine ⟨k, Subtype.ext (mat_injective (n := d) (F := F) ?_)⟩
    simpa [map_pow] using hk
  · have hT : ∀ x ∈ (⨆ i, Symplectic.torus d F i : Subgroup (StatedSp d F)),
        x ^ (Nat.card F - 1) = 1 := by
      intro x hx
      obtain ⟨t, rfl⟩ := exists_diagonal_of_mem_iSup_torus hx
      have ht : t ^ (Nat.card F - 1) = 1 := by
        funext i
        rw [Pi.pow_apply, Pi.one_apply]
        exact burnsideI2BN_units_pow_card_sub_one (t i)
      rw [← map_pow, ← map_pow, ht, map_one, map_one]
    exact burnsideI2BN_not_dvd_card_of_pow_eq_one hT
      (burnsideI2BN_not_dvd_card_sub_one hp (hF ▸ dvd_pow_self p hf.ne'))

section SL

open CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix

theorem burnsideI2BN_SL_isPGroup {p m : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p] :
    IsPGroup p (posUnipotent (SpecialLinear.rootDatum m F)) := by
  rintro ⟨x, hx⟩
  obtain ⟨hup, hdiag⟩ := CFSG.StandardType.GGRootSL.upperUni_of_mem_posUnipotent hx
  obtain ⟨k, hk⟩ := burnsideI2BN_pow_eq_one_of_triangular (p := p)
    (fun a : Fin (m + 1) => (a : ℤ)) (M := (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (by
      intro a b hab
      rcases lt_trichotomy b a with h | rfl | h
      · rw [hup a b h, Matrix.one_apply_ne h.ne']
      · rw [hdiag b, Matrix.one_apply_eq]
      · exfalso
        have : (a : ℤ) < b := by exact_mod_cast h
        omega)
  have hx1 : x ^ p ^ k = 1 := Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_pow] using hk)
  exact ⟨k, Subtype.ext (by simpa using hx1)⟩

theorem burnsideI2BN_SL_torus {p m : ℕ} (hp : p.Prime) {F : Type} [Field F] [Finite F]
    (hdvd : p ∣ Nat.card F) :
    ¬ p ∣ Nat.card (⨆ i, SpecialLinear.torus m F i :
      Subgroup (SpecialLinearGroup (Fin (m + 1)) F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine burnsideI2BN_not_dvd_card_of_pow_eq_one (m := Nat.card F - 1) (fun g hg => ?_)
    (burnsideI2BN_not_dvd_card_sub_one hp hdvd)
  have hdiag : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag :=
    SpecialLinearGroup.mem_diagonalTorus_iff.mp
      (CFSG.StandardType.GGRootSL.iSup_torus_le_diagonalTorus hg)
  obtain ⟨d, hd⟩ : ∃ d : Fin (m + 1) → F,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal d :=
    ⟨fun a => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a,
      (Matrix.IsDiag.diagonal_diag hdiag).symm⟩
  have hdet : ∏ a, d a = 1 := by
    have := g.2
    rwa [hd, Matrix.det_diagonal] at this
  have hne : ∀ a, d a ≠ 0 := fun a h0 => by
    have := Finset.prod_eq_zero (Finset.mem_univ a) h0
    rw [hdet] at this
    exact one_ne_zero this
  have : Fintype F := Fintype.ofFinite F
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, hd, Matrix.diagonal_pow]
  have hd1 : d ^ (Nat.card F - 1) = 1 := by
    funext a
    rw [Pi.pow_apply, Pi.one_apply, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (hne a)
  rw [hd1]
  simp

theorem statedSL_has_splitBNPair {p f d : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hd : 2 ≤ d) (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f) :
    ∃ B N : Subgroup ↥(StatedSL d F), IsSplitBNPair p B N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := burnsideI2BN_charP_of_card hp hf hF
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hSL := burnsideI2BN_of_datum hp (D := SpecialLinear.rootDatum m F)
    (n := SpecialLinear.weylRep m F) (H := SpecialLinear.torus m F)
    (SpecialLinear.isCTGroupDatum m F) (SpecialLinear.steinbergExtras m F)
    CFSG.StandardType.GGRootSL.bruhatExtras burnsideI2BN_SL_isPGroup
    (burnsideI2BN_SL_torus hp (hF ▸ dvd_pow_self p hf.ne'))
  let e : SpecialLinearGroup (Fin (m + 1)) F ≃* ↥(StatedSL (m + 1) F) :=
    (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL (m + 1) F).symm)
  have hker : (e.toMonoidHom).ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  exact ⟨_, _, burnsideI2BN_map hSL e.toMonoidHom e.surjective hker⟩

end SL

section SU

open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg.CentralExt.SUBruhat

theorem statedSU_has_splitBNPair {p f d : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hd : 3 ≤ d) (F : Type) [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) :
    ∃ B N : Subgroup ↥(StatedSU d (p ^ f) F), IsSplitBNPair p B N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := burnsideI2BN_charP_of_card hp (f := f * 2) (by omega) (by rw [hF, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hd2 : 2 ≤ d := by omega
  have hσ := unitaryInvolution_involutive hF
  have hSU := burnsideI2BN_of_datum hp (D := rootDatum hF d)
    (n := levelWeyl hσ ζ) (H := levelTorus (unitaryInvolution F p f))
    (isCTGroupDatum hF d hd2 ζ hζ) (steinbergExtras hF d hd2 ζ hζ) (bruhatExtras hF hd2 ζ hζ)
    ?_ ?_
  · have hker : ((equivStatedSU hF d).toMonoidHom).ker ≤
        Subgroup.center (SU (unitaryInvolution F p f) d) := by
      rw [(MonoidHom.ker_eq_bot_iff _).2 (equivStatedSU hF d).injective]
      exact bot_le
    exact ⟨_, _, burnsideI2BN_map hSU (equivStatedSU hF d).toMonoidHom
      (equivStatedSU hF d).surjective hker⟩
  · rintro ⟨x, hx⟩
    have hidb := idBelow_of_mem_iSup hσ 1
      {γ | γ ∈ roots (isFiniteType_cartan d) (divisible d) ∧ 0 < ht γ}
      (fun γ hγ => by have := hγ.2; omega) hx
    obtain ⟨k, hk⟩ := burnsideI2BN_pow_eq_one_of_triangular (p := p) (lvl 1)
      (M := mat (unitaryInvolution F p f) d x) hidb
    refine ⟨k, Subtype.ext (mat_injective (σ := unitaryInvolution F p f) (n := d) ?_)⟩
    simpa [map_pow] using hk
  · have hT : ∀ y ∈ (⨆ i, levelTorus (unitaryInvolution F p f) i :
        Subgroup (SU (unitaryInvolution F p f) d)), y ^ (Nat.card F - 1) = 1 := by
      intro y hy
      obtain ⟨t, ht⟩ : ∃ t : Fin d → F, mat (unitaryInvolution F p f) d y = Matrix.diagonal t :=
        Subgroup.iSup_induction _ hy
          (C := fun y => ∃ t : Fin d → F,
            mat (unitaryInvolution F p f) d y = Matrix.diagonal t)
          (fun k y hy => exists_diagonal_of_mem_levelTorus hy)
          ⟨1, by rw [map_one]; exact Matrix.diagonal_one.symm⟩
          (fun y z ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ =>
            ⟨d₁ * d₂, by rw [map_mul, h₁, h₂, Matrix.diagonal_mul_diagonal]; rfl⟩)
      have hdet : ∏ a, t a = 1 := by
        have := y.2.1
        rwa [← mat_apply (σ := unitaryInvolution F p f) (n := d), ht, Matrix.det_diagonal] at this
      have hne : ∀ a, t a ≠ 0 := fun a h0 => by
        have := Finset.prod_eq_zero (Finset.mem_univ a) h0
        rw [hdet] at this
        exact one_ne_zero this
      have : Fintype F := Fintype.ofFinite F
      refine mat_injective (σ := unitaryInvolution F p f) (n := d) ?_
      rw [map_pow, ht, Matrix.diagonal_pow, map_one]
      have hd1 : t ^ (Nat.card F - 1) = 1 := by
        funext a
        rw [Pi.pow_apply, Pi.one_apply, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one _ (hne a)
      rw [hd1]
      simp
    exact burnsideI2BN_not_dvd_card_of_pow_eq_one hT
      (burnsideI2BN_not_dvd_card_sub_one hp
        (hF ▸ dvd_pow (dvd_pow_self p hf.ne') two_ne_zero))

end SU

end Datum

section AdjointGroup

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem adjointGroup_has_splitBNPair {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (t : CFSG.Blueprint.Chevalley.Tag) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) :
    ∃ B N : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup t F),
      IsSplitBNPair p B N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP F p := burnsideI2BN_charP_of_card hp hf hF
  obtain ⟨hsb, hBN, -, -, -, -, -, hpg⟩ := chevalley_split_bn_pair t F
  have hfinG : Finite (adjointGroup t F) := inferInstance
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t
  let c : ↥(adjointGroup t F) :=
    ⟨canonicalRep (coxeterSystem t) F w₀, canonicalRep_mem_adjointGroup _ F w₀⟩
  have hcN : c ∈ monomialSub t F := canonicalRep_mem_monomialSubgroup F w₀
  have hsat : (⨅ n ∈ monomialSub t F, CFSG.conjugate (borelSub t F) n) =
      borelSub t F ⊓ monomialSub t F := by
    refine burnsideI2BN_sat_of_opposite normal_borelSub_inf_monomialSub hcN ?_
    intro z hz hz'
    have hmap := (opposite_Borel_intersection t F w₀ hw₀).2.1
    have hinter := (opposite_Borel_intersection t F w₀ hw₀).2.2.1
    have hzT : (z : ModGL t F) ∈ torusGroup t F := by
      rw [← hinter]
      refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
      rw [← hmap]
      refine ⟨_, hz', ?_⟩
      simp [MulAut.conj_apply, c, mul_assoc]
    have hzT' : z ∈ torusSub t F := hzT
    rw [← borelSub_inf_monomialSub] at hzT'
    exact (Subgroup.mem_inf.1 hzT').2
  have hT : ¬ p ∣ Nat.card (borelSub t F ⊓ monomialSub t F : Subgroup (adjointGroup t F)) := by
    rw [borelSub_inf_monomialSub]
    have h1 := not_dvd_card_torusGroup (τ := t) (K := F) p
    have h2 : torusGroup t F ≤ adjointGroup t F :=
      torusGroup_le_borelGroup.trans borelGroup_le_adjointGroup'
    rwa [torusSub, card_subgroupOf_of_le h2]
  exact ⟨_, _, burnsideI2BN_of_splitBN hp hsb (hpg p).2 hsat hT⟩

end AdjointGroup

section Suzuki

open CFSG.LieType.Ree

theorem suzukiGroup_has_splitBNPair (a : ℕ) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ (2 * a + 1)) :
    ∃ B N : Subgroup ↥(suzukiGroup a F), IsSplitBNPair 2 B N := by
  have hK := hF
  have hWnot : suzukiWElt a F ∉ suzukiB a F := by
    intro h
    obtain ⟨u, v, l, hW⟩ := (mem_suzukiB_iff hK).1 h
    exact (suzuki_bruhat_normal_form hK (suzukiWElt a F)).2.1
      ⟨⟨u, v, l, hW⟩, ⟨0, 0, 1, 0, 0, by simp [suzukiSElt_zero_zero hK, suzukiDElt_one]⟩⟩
  have hcell : ∀ g : suzukiGroup a F, g ∈ suzukiB a F ∨
      ∃ b ∈ suzukiB a F, ∃ b' ∈ suzukiB a F, g = b * suzukiWElt a F * b' := by
    intro g
    rcases suzukiGroup_mem_cells hK g with hg | ⟨b, hb, x, hx, rfl⟩
    · exact Or.inl hg
    · exact Or.inr ⟨b, hb, x, suzukiU_le_suzukiB a F hx, rfl⟩
  have hwH : ∀ h ∈ suzukiT a F, suzukiWElt a F * h * (suzukiWElt a F)⁻¹ ∈ suzukiT a F := by
    intro h hh
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hh
    rw [suzukiWElt_inv, suzukiWElt_D_W hK]
    exact suzukiDElt_mem_suzukiT a F _
  have hw2 : suzukiWElt a F * suzukiWElt a F ∈ suzukiT a F := by
    rw [suzukiWElt_mul_self]
    exact one_mem _
  have hbn3 : ∃ b ∈ suzukiB a F, suzukiWElt a F * b * suzukiWElt a F ∉ suzukiB a F := by
    refine ⟨suzukiSElt a F 1 0, suzukiU_le_suzukiB a F (suzukiSElt_mem_suzukiU a F 1 0),
      fun hB => ?_⟩
    obtain ⟨u₁, v₁, l, c, d, h⟩ := exists_W_S_W hK (show ((1 : F), (0 : F)) ≠ (0, 0) by simp)
    obtain ⟨u, v, l', hB'⟩ := (mem_suzukiB_iff hK).1 hB
    exact (suzuki_bruhat_normal_form hK
      (suzukiWElt a F * suzukiSElt a F 1 0 * suzukiWElt a F)).2.1
      ⟨⟨u, v, l', hB'⟩, ⟨u₁, v₁, l, c, d, h⟩⟩
  have hUn : ((suzukiU a F).subgroupOf (suzukiB a F)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (suzukiU_le_suzukiB a F)]
    exact sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)
  have hUp : IsPGroup 2 (suzukiU a F) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := (2 * a + 1) * 2) (by
      rw [(suzuki_unipotent_structure hK).2.1, pow_mul])
  have hopp : ∀ z ∈ suzukiB a F, (suzukiWElt a F)⁻¹ * z * suzukiWElt a F ∈ suzukiB a F →
      z ∈ suzukiT a F := by
    intro z hz hz'
    obtain ⟨u, v, l, rfl⟩ := (mem_suzukiB_iff hK).1 hz
    by_cases huv : (u, v) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj huv
      rw [suzukiSElt_zero_zero hK, one_mul]
      exact suzukiDElt_mem_suzukiT a F l
    · exfalso
      obtain ⟨u₁, v₁, l₁, c, d, h⟩ := exists_W_S_W hK huv
      have hW := suzukiWElt_mul_self (a := a) (K := F)
      have e : (suzukiWElt a F)⁻¹ * (suzukiSElt a F u v * suzukiDElt a F l) * suzukiWElt a F =
          (suzukiWElt a F * suzukiSElt a F u v * suzukiWElt a F) * suzukiDElt a F l⁻¹ := by
        rw [suzukiWElt_inv, ← suzukiWElt_D_W hK l]
        calc suzukiWElt a F * (suzukiSElt a F u v * suzukiDElt a F l) * suzukiWElt a F
            = suzukiWElt a F * suzukiSElt a F u v * 1 * suzukiDElt a F l * suzukiWElt a F := by
              group
          _ = suzukiWElt a F * suzukiSElt a F u v * (suzukiWElt a F * suzukiWElt a F) *
              suzukiDElt a F l * suzukiWElt a F := by rw [hW]
          _ = _ := by group
      rw [e] at hz'
      have hBW : suzukiWElt a F * suzukiSElt a F u v * suzukiWElt a F ∈ suzukiB a F := by
        have := (suzukiB a F).mul_mem hz' ((suzukiB a F).inv_mem
          (suzukiT_le_suzukiB a F (suzukiDElt_mem_suzukiT a F l⁻¹)))
        simpa using this
      obtain ⟨u', v', l', hB'⟩ := (mem_suzukiB_iff hK).1 hBW
      exact (suzuki_bruhat_normal_form hK
        (suzukiWElt a F * suzukiSElt a F u v * suzukiWElt a F)).2.1
        ⟨⟨u', v', l', hB'⟩, ⟨u₁, v₁, l₁, c, d, h⟩⟩
  have hHp : ¬ 2 ∣ Nat.card (suzukiT a F) := by
    rw [(suzuki_borel_structure hK).2.2.1]
    have h2 : 2 ^ (2 * a + 1) = 2 * 2 ^ (2 * a) := by ring
    have h3 : 0 < 2 ^ (2 * a) := Nat.two_pow_pos (2 * a)
    omega
  obtain ⟨N, hN⟩ := burnsideI2BN_rankOne Nat.prime_two (B := suzukiB a F) (H := suzukiT a F)
    (U := suzukiU a F) (w := suzukiWElt a F) hcell hWnot (suzukiT_le_suzukiB a F) hwH hw2 hbn3
    (suzukiU_le_suzukiB a F) hUn hUp (suzukiU_inf_suzukiT hK) rfl hopp hHp
  exact ⟨_, N, hN⟩

end Suzuki

section ReeHelpers

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open scoped Pointwise

theorem burnsideI2BN_parabolic_mul_cell
    {τ : Tag} {K : Type} [Field K] (J : Set (Fin τ.rank))
    (w : WeylGroup τ) {p y : ModGL τ K} (hp : p ∈ parabolicSubgroup τ K J)
    (hy : y ∈ bruhatCell τ K w) :
    ∃ x ∈ parabolicWeylGroup τ J, p * y ∈ bruhatCell τ K (x * w) := by
  set X : Set (ModGL τ K) := ⋃ x ∈ parabolicWeylGroup τ J, bruhatCell τ K (x * w) with hX
  have hB : ∀ b ∈ borelGroup τ K, ∀ y ∈ X, b * y ∈ X := by
    intro b hb y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hyx
    exact Set.mem_iUnion₂.2 ⟨x, hx, mem_bruhatCell.2 ⟨b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩⟩
  have hn : ∀ i ∈ J, ∀ y ∈ X, weylElt τ K i 1 * y ∈ X := by
    intro i hi y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
    have hmem : weylElt τ K i 1 * y ∈ bruhatCell τ K (simple τ i) * bruhatCell τ K (x * w) :=
      Set.mul_mem_mul (weylElt_mem_bruhatCell_simple i) hyx
    rcases bruhatCell_simple_mul_subset i (x * w) hmem with h | h
    · exact Set.mem_iUnion₂.2 ⟨simple τ i * x,
        mul_mem (simple_mem_parabolicWeylGroup_iff.2 hi) hx, by rwa [mul_assoc]⟩
    · exact Set.mem_iUnion₂.2 ⟨x, hx, h⟩
  have hS : parabolicSubgroup τ K J ≤ MulAction.stabilizer (ModGL τ K) X := by
    refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
    · exact smul_set_eq_of_forall (hB b hb) (hB b⁻¹ (inv_mem hb))
    · rintro _ ⟨i, hi, rfl⟩
      refine smul_set_eq_of_forall (hn i hi) fun x hx => ?_
      have e : (weylElt τ K i 1)⁻¹ = (torusElt τ K i (-1))⁻¹ * weylElt τ K i 1 := by
        rw [← weylElt_one_mul_self, mul_inv_rev, inv_mul_cancel_right]
      rw [e, mul_assoc]
      exact hB _ (inv_mem (torusGroup_le_borelGroup (torusElt_mem_torusGroup i (-1)))) _
        (hn i hi x hx)
  have hyX : y ∈ X := Set.mem_iUnion₂.2 ⟨1, one_mem _, by rwa [one_mul]⟩
  have hp' : p • X = X := hS hp
  have : p * y ∈ X := by
    rw [← hp']
    exact ⟨y, hyX, rfl⟩
  obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.1 this
  exact ⟨x, hx, hxy⟩

theorem burnsideI2BN_ree_hasSplit
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (hp : t.prime.Prime) :
    ∃ B N : Subgroup ↥(t.reeGamma K a), IsSplitBNPair t.prime B N := by
  haveI : Fact t.prime.Prime := ⟨hp⟩
  haveI : Finite (ModGL t.tag K) := finite_modGL
  haveI : Finite ↥(t.reeGamma K a) := inferInstance
  obtain ⟨-, hord, -, -, -, -, hW7, -, -, -, -, -, -, -, -, -, -, -, -, hlong, hmax⟩ :=
    ree_fixed_Weyl_structure
  obtain ⟨w₀, hw₀⟩ := hlong t
  obtain ⟨-, hw₀W⟩ := hmax t w₀ hw₀
  obtain ⟨hnN₀, -, -, hBinter, -, -, hNB⟩ := ree_Borel_self_normalizers t a K w₀ hw₀
  obtain ⟨-, hker, hHnorm, -, hNeq, -⟩ := ree_fixed_monomial_quotient t a K
  have hHB : t.reeFixedTorus K a ≤ t.reeFixedBorel K a := reeFixedTorus_le_reeFixedBorel
  have hHN : t.reeFixedTorus K a ≤ t.reeFixedMonomial K a :=
    reeFixedTorus_le_reeFixedMonomial t K a
  have hBΓ : t.reeFixedBorel K a ≤ t.reeGamma K a := reeFixedBorel_le_reeGamma
  have hNΓ : t.reeFixedMonomial K a ≤ t.reeGamma K a :=
    (inf_le_right : monomialSubgroup t.tag K ⊓ t.reeGamma K a ≤ t.reeGamma K a)
  have hBN : t.reeFixedBorel K a ⊓ t.reeFixedMonomial K a = t.reeFixedTorus K a := by
    refine le_antisymm (fun g hg => ?_) (le_inf hHB hHN)
    obtain ⟨hgB, hgN⟩ := Subgroup.mem_inf.1 hg
    have hg1 : g ∈ borelGroup t.tag K ⊓ monomialSubgroup t.tag K :=
      Subgroup.mem_inf.2 ⟨(hgB : g ∈ borelGroup t.tag K ⊓ t.reeGamma K a).1,
        (hgN : g ∈ monomialSubgroup t.tag K ⊓ t.reeGamma K a).1⟩
    rw [(borel_weyl_intersection t.tag K).1] at hg1
    exact Subgroup.mem_inf.2 ⟨hg1, hBΓ hgB⟩
  have hzne : ∀ j, t.fixedOrbitElement j ≠ 1 := fun j h => by
    have := hord t j
    rw [h] at this
    simp at this
  have hz2 : ∀ j, t.fixedOrbitElement j * t.fixedOrbitElement j = 1 := fun j => by
    have := pow_orderOf_eq_one (t.fixedOrbitElement j)
    rwa [hord t j, pow_two] at this
  have hs2H : ∀ j, canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) *
      canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeFixedTorus K a := by
    intro j
    have hzW := fixedOrbitElement_mem (t := t) j
    have hsN := canonicalRep_mem_reeFixedMonomial t K a hzW
    have hmem : (⟨_, hsN⟩ : t.reeFixedMonomial K a) * ⟨_, hsN⟩ ∈
        (t.reeFixedWeylHom K a).ker := by
      rw [MonoidHom.mem_ker, map_mul, reeFixedWeylHom_canonicalRep t K a hzW]
      exact hz2 j
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  have hsB : ∀ j, canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∉
      t.reeFixedBorel K a := by
    intro j hB
    have hzW := fixedOrbitElement_mem (t := t) j
    have h1 : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
        t.reeFixedBruhatCell K a (t.fixedOrbitElement j) :=
      (mem_reeFixedBruhatCell).2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
    have h2 : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
        t.reeFixedBruhatCell K a 1 := by
      rw [reeFixedBruhatCell_one]
      exact hB
    exact Set.disjoint_left.1 (disjoint_reeFixedBruhatCell (t := t) (K := K) (a := a)
      (Ne.symm (hzne j))) h2 h1
  refine ⟨_, _, burnsideI2BN_isSplit_sub (Γ := t.reeGamma K a) (B := t.reeFixedBorel K a)
    (N := t.reeFixedMonomial K a) (U := t.reeFixedPosUnipotent K a)
    (S := Set.range fun j : Fin t.fixedOrbitCount =>
      canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) hp hBΓ hNΓ
    (reeGamma_eq_sup_reeFixedMonomial (t := t) (K := K) (a := a)).symm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_⟩
  · rw [hBN]
    exact hHnorm
  · rintro _ ⟨j, rfl⟩
    exact ⟨canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j), hsB j,
      by rw [pow_two]; exact hHB (hs2H j)⟩
  · rw [hBN, sup_comm]
    exact hNeq.symm
  · rintro _ ⟨j, rfl⟩ w hw b hb
    beta_reduce
    have hW7j := hW7 t j
    have hzW : t.fixedOrbitElement j ∈ t.relWeylRee := fixedOrbitElement_mem j
    have hsN := canonicalRep_mem_reeFixedMonomial t K a hzW
    have hsP : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
        parabolicSubgroup t.tag K (t.fixedOrbitSet j) :=
      (canonicalRep_fixedOrbitElement_mem_reeGamma_inf (t := t) (K := K) (a := a) j).2
    have hsW : t.reeFixedWeylHom K a ⟨_, hsN⟩ = t.fixedOrbitElement j :=
      reeFixedWeylHom_canonicalRep t K a hzW
    generalize canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) = s at hsN hsP hsW ⊢
    generalize t.fixedOrbitElement j = z at hzW hsW hW7j ⊢
    obtain ⟨wb, hwb⟩ : ∃ wb, t.reeFixedWeylHom K a ⟨w, hw⟩ = wb := ⟨_, rfl⟩
    have hwbW : wb ∈ t.relWeylRee := hwb ▸ reeFixedWeylHom_mem t K a ⟨w, hw⟩
    have hnN := canonicalRep_mem_reeFixedMonomial t K a hwbW
    have hh' : (canonicalRep (coxeterSystem t.tag) K wb)⁻¹ * w ∈ t.reeFixedTorus K a := by
      have hmem : (⟨canonicalRep (coxeterSystem t.tag) K wb, hnN⟩ : t.reeFixedMonomial K a)⁻¹ *
          ⟨w, hw⟩ ∈ (t.reeFixedWeylHom K a).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, reeFixedWeylHom_canonicalRep t K a hwbW, hwb]
        simp
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.1 hmem
    have hbw : b * w ∈ bruhatCell t.tag K wb := by
      refine mem_bruhatCell.2 ⟨b, (hb : b ∈ borelGroup t.tag K ⊓ t.reeGamma K a).1,
        (canonicalRep (coxeterSystem t.tag) K wb)⁻¹ * w,
        (torusGroup_le_borelGroup
          (hh' : (canonicalRep (coxeterSystem t.tag) K wb)⁻¹ * w ∈
            torusGroup t.tag K ⊓ t.reeGamma K a).1), ?_⟩
      group
    have hgΓ : s * b * w ∈ t.reeGamma K a :=
      mul_mem (mul_mem (hNΓ hsN) (hBΓ hb)) (hNΓ hw)
    obtain ⟨x, hx, hgx⟩ := burnsideI2BN_parabolic_mul_cell (t.fixedOrbitSet j) wb hsP hbw
    have hgΓ' : (s * b * w) ∈ (t.reeGamma K a : Set (ModGL t.tag K)) := hgΓ
    rw [reeGamma_eq_iUnion_reeFixedBruhatCell (t := t) (K := K) (a := a)] at hgΓ'
    obtain ⟨⟨v, hv⟩, hgv⟩ := Set.mem_iUnion.1 hgΓ'
    have hgv' : s * b * w ∈ bruhatCell t.tag K v :=
      reeFixedBruhatCell_subset_bruhatCell (t := t) (K := K) (a := a) v hgv
    have hvx : v = x * wb := by
      by_contra hne
      exact Set.disjoint_left.1 (disjoint_bruhatCell (K := K) hne) hgv'
        (by simpa [mul_assoc] using hgx)
    have hxW : x ∈ t.relWeylRee := by
      have := mul_mem hv (inv_mem hwbW)
      rwa [hvx, mul_inv_cancel_right] at this
    have hxz : x ∈ ({1, z} : Set (WeylGroup t.tag)) := by
      rw [← hW7j]
      exact ⟨hx, hxW⟩
    rcases hxz with hx1 | hxz'
    · have hv1 : v = wb := by rw [hvx, hx1, one_mul]
      subst hv1
      obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := mem_reeFixedBruhatCell.1 hgv
      generalize canonicalRep (coxeterSystem t.tag) K v = n at hh' he
      refine ⟨b₁, hb₁, (n⁻¹ * w)⁻¹ * b₂, (t.reeFixedBorel K a).mul_mem
        ((t.reeFixedBorel K a).inv_mem (hHB hh')) hb₂, Or.inl ?_⟩
      rw [← he]
      group
    · rw [Set.mem_singleton_iff] at hxz'
      have hvz : v = z * wb := by rw [hvx, hxz']
      subst hvz
      obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := mem_reeFixedBruhatCell.1 hgv
      have hzwbW : z * wb ∈ t.relWeylRee := mul_mem hzW hwbW
      have hmN := canonicalRep_mem_reeFixedMonomial t K a hzwbW
      have hh'' : (canonicalRep (coxeterSystem t.tag) K (z * wb))⁻¹ * (s * w) ∈
          t.reeFixedTorus K a := by
        have hmem : (⟨canonicalRep (coxeterSystem t.tag) K (z * wb), hmN⟩ :
            t.reeFixedMonomial K a)⁻¹ * (⟨s, hsN⟩ * ⟨w, hw⟩) ∈
              (t.reeFixedWeylHom K a).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
            reeFixedWeylHom_canonicalRep t K a hzwbW, hsW, hwb]
          simp
        rw [hker] at hmem
        exact Subgroup.mem_subgroupOf.1 hmem
      generalize canonicalRep (coxeterSystem t.tag) K (z * wb) = m at hh'' he
      refine ⟨b₁, hb₁, (m⁻¹ * (s * w))⁻¹ * b₂,
        (t.reeFixedBorel K a).mul_mem ((t.reeFixedBorel K a).inv_mem (hHB hh'')) hb₂, Or.inr ?_⟩
      rw [← he]
      group
  · rintro _ ⟨j, rfl⟩
    by_contra hcon
    push Not at hcon
    apply hsB j
    have hs2 := hs2H j
    have hnorm : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
        Subgroup.normalizer (t.reeFixedBorel K a : Set (ModGL t.tag K)) := by
      set n := canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)
      refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · have e : n * x * n⁻¹ = (n * x * n) * (n * n)⁻¹ := by group
        rw [e]
        exact (t.reeFixedBorel K a).mul_mem (hcon x hx)
          ((t.reeFixedBorel K a).inv_mem (hHB hs2))
      · have e : x = (n * n)⁻¹ * (n * (n * x * n⁻¹) * n) := by group
        rw [e]
        exact (t.reeFixedBorel K a).mul_mem ((t.reeFixedBorel K a).inv_mem (hHB hs2))
          (hcon _ hx)
    have hnΓ : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeGamma K a :=
      hNΓ (canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j))
    have : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeGamma K a ⊓
        Subgroup.normalizer (t.reeFixedBorel K a : Set (ModGL t.tag K)) :=
      Subgroup.mem_inf.2 ⟨hnΓ, hnorm⟩
    rw [hNB] at this
    exact this
  · exact reeFixedPosUnipotent_le_reeFixedBorel
  · exact reeFixedPosUnipotent_subgroupOf_normal
  · exact IsPGroup.to_le (((positive_root_triangularity.{0, 0} t.tag).2 K t.prime).2.1) inf_le_left
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
    have hxB : x ∈ t.reeFixedBorel K a := reeFixedPosUnipotent_le_reeFixedBorel hxU
    have hxH : x ∈ t.reeFixedTorus K a := by
      rw [← hBN]
      exact Subgroup.mem_inf.2 ⟨hxB, hxN⟩
    have := reeFixed_mul_unique (t := t) (K := K) (a := a) (h₁ := x) (h₂ := 1) (u₁ := 1)
      (u₂ := x) hxH (one_mem _) (one_mem _) hxU (by simp)
    exact Subgroup.mem_bot.2 this.1
  · rw [hBN]
    refine le_antisymm (sup_le reeFixedPosUnipotent_le_reeFixedBorel hHB) fun b hb => ?_
    have hb' : b ∈ (t.reeFixedTorus K a : Set (ModGL t.tag K)) *
        (t.reeFixedPosUnipotent K a : Set (ModGL t.tag K)) := by
      rw [← reeFixedBorel_eq_mul]
      exact hb
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    exact mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hu)
  · refine burnsideI2BN_sat_of_opposite ?_ hnN₀ ?_
    · rw [hBN]
      exact hHnorm
    · intro z hz hz'
      have hzT : z ∈ t.reeFixedTorus K a := by
        rw [← hBinter]
        refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
        refine ⟨_, hz', ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      exact hHN hzT
  · rw [hBN]
    intro hd
    exact not_dvd_card_torusGroup (τ := t.tag) (K := K) t.prime
      (hd.trans (Subgroup.card_dvd_of_le inf_le_left))

end ReeHelpers

section LieModelHelpers

theorem burnsideI2BN_exists_of_mulEquiv {G X : Type} [Group G] [Group X] {p : ℕ} (e : G ≃* X)
    (h : ∃ B N : Subgroup G, IsSplitBNPair p B N) : ∃ B N : Subgroup X, IsSplitBNPair p B N := by
  obtain ⟨B, N, h⟩ := h
  have hker : e.toMonoidHom.ker ≤ Subgroup.center G := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  exact ⟨_, _, burnsideI2BN_map h e.toMonoidHom e.surjective hker⟩

theorem burnsideI2BN_exists_quotient_center {G : Type} [Group G] {p : ℕ}
    (h : ∃ B N : Subgroup G, IsSplitBNPair p B N) :
    ∃ B N : Subgroup (G ⧸ Subgroup.center G), IsSplitBNPair p B N := by
  obtain ⟨B, N, h⟩ := h
  refine ⟨_, _, burnsideI2BN_map h (QuotientGroup.mk' (Subgroup.center G))
    (QuotientGroup.mk'_surjective _) ?_⟩
  rw [QuotientGroup.ker_mk']

theorem burnsideI2BN_exists_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {p : ℕ} {H : Subgroup (GL ι K)}
    (h : ∃ B N : Subgroup ↥H, IsSplitBNPair p B N) :
    ∃ B N : Subgroup (StatedProj H), IsSplitBNPair p B N := by
  obtain ⟨B, N, h⟩ := h
  refine ⟨_, _, burnsideI2BN_map h (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H))
    (QuotientGroup.mk'_surjective _) ?_⟩
  rw [QuotientGroup.ker_mk']
  intro x hx
  have hx' : (x : GL ι K) ∈ StatedScalars ι K := hx
  rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.1 hx' (y : GL ι K))

theorem burnsideI2BN_derivedCentralQuotient {M : Type} [Group M] {H C : Subgroup M} {p : ℕ}
    (hD : ⁅H, H⁆ = C) (h : ∃ B N : Subgroup ↥C, IsSplitBNPair p B N) :
    ∃ B N : Subgroup (DerivedCentralQuotient H), IsSplitBNPair p B N :=
  burnsideI2BN_exists_quotient_center
    (burnsideI2BN_exists_of_mulEquiv (MulEquiv.subgroupCongr hD).symm h)

end LieModelHelpers

section ClassicalCases

theorem burnsideI2BN_PSL {G : Type} [Group G] {p n f : ℕ} (hp : p.Prime)
    (hadm : StatedLieAdmissible .PSL n p f) (h : StatedClassicalModel G .PSL n p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hf, hn, -⟩ := hadm
  exact burnsideI2BN_exists_of_mulEquiv e.symm (burnsideI2BN_exists_statedProj
    (statedSL_has_splitBNPair hp hf hn K hcard))

theorem burnsideI2BN_PSU {G : Type} [Group G] {p n f : ℕ} (hp : p.Prime)
    (hadm : StatedLieAdmissible .PSU n p f) (h : StatedClassicalModel G .PSU n p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hf, hn, -⟩ := hadm
  exact burnsideI2BN_exists_of_mulEquiv e.symm (burnsideI2BN_exists_statedProj
    (statedSU_has_splitBNPair hp hf hn K hcard))

theorem burnsideI2BN_PSp {G : Type} [Group G] {p n f : ℕ} (hp : p.Prime)
    (hadm : StatedLieAdmissible .PSp n p f) (h : StatedClassicalModel G .PSp n p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hf, hn, -⟩ := hadm
  exact burnsideI2BN_exists_of_mulEquiv e.symm (burnsideI2BN_exists_statedProj
    (statedSp_has_splitBNPair hp hf (by omega) K hcard))

end ClassicalCases

section SpinCases

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank

theorem burnsideI2BN_not_dvd_card_iSup_range_units {U : Type} [Group U] [Finite U] {p : ℕ}
    [Fact p.Prime] {F : Type} [Field F] [Finite F] (hdvd : p ∣ Nat.card F) {ι : Type*}
    (φ : ι → Fˣ →* U) (hc : ∀ i j, ∀ h ∈ (φ i).range, ∀ h' ∈ (φ j).range, Commute h h') :
    ¬ p ∣ Nat.card (⨆ i, (φ i).range : Subgroup U) := by
  refine burnsideI2BN_not_dvd_card_of_pow_eq_one (m := Nat.card F - 1) (fun x hx => ?_)
    (burnsideI2BN_not_dvd_card_sub_one (Fact.out) hdvd)
  exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pow_eq_one_of_mem_iSup
    (fun i h hh => by
      obtain ⟨t, rfl⟩ := hh
      rw [← map_pow, burnsideI2BN_units_pow_card_sub_one, map_one]) hc hx

theorem burnsideI2BN_spinPlus {p n : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hdvd : p ∣ Nat.card K) [CharP K p] (hn : 3 ≤ n) :
    ∃ B N : Subgroup ↥(spinGroup (quadPlus n K)), IsSplitBNPair p B N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Finite (spinGroup (quadPlus n K)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := K))
  have hext := plusDatum_steinbergExtras (K := K) hn
  refine ⟨_, _, burnsideI2BN_of_datum hp (D := plusDatum n K hn) (n := weylD K hn)
    (H := fun k => (torusD K hn k).range)
    (plusDatum_isCTGroupDatum hn (plusDatum_iSup_eq_top n K hn)) hext
    (CFSG.StandardType.GGRootSpinPlus.bruhatExtras hn)
    (isPGroup_iSup_pos hext fun γ hγ =>
      isPGroup_of_isParametrization (SpinPlus.isParametrization hn) hγ) ?_⟩
  exact burnsideI2BN_not_dvd_card_iSup_range_units hdvd (fun i => torusD K hn i)
    fun i j h hh h' hh' => hext.torus_commute i j h hh h' hh'

theorem burnsideI2BN_not_dvd_sub_one {p M : ℕ} (hp : p.Prime) (hM : 1 ≤ M) (hdvd : p ∣ M) :
    ¬ p ∣ M - 1 := by
  intro h
  have h2 := Nat.dvd_sub hdvd h
  rw [Nat.sub_sub_self hM] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

open CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Universal.Spin.Twisted in
theorem burnsideI2BN_spinMinus {p n : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hdvd : p ∣ Nat.card K) [CharP K p] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hn : 4 ≤ n) :
    ∃ B N : Subgroup ↥(spinGroup (quadMinus n K b c)), IsSplitBNPair p B N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (spinGroup (quadMinus n K b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hext := minusDatum_steinbergExtras n hirr
  refine ⟨_, _, burnsideI2BN_of_datum hp (D := minusDatum n hirr) (n := minusWeyl n hirr)
    (H := minusTorus n hirr) (minusDatum_isCTGroupDatum n hirr hn) hext
    (SpinMinusClosed.bruhatExtras hirr hn)
    (isPGroup_iSup_pos hext fun γ hγ => isPGroup_minusRootGroup hirr hγ) ?_⟩
  refine burnsideI2BN_not_dvd_card_of_pow_eq_one (m := Nat.card K ^ 2 - 1) (fun x hx => ?_)
    (burnsideI2BN_not_dvd_sub_one hp (Nat.one_le_pow _ _ Nat.card_pos) (dvd_pow hdvd two_ne_zero))
  exact SpinMinusClosed.pow_eq_one_of_mem_iSup
    (fun i h hh => by
      have := SpinMinusClosed.pow_eq_one_of_mem_minusTorus hirr i hh
      rwa [SpinMinusClosed.card_shortField] at this)
    (fun i j h hh h' hh' => hext.torus_commute i j h hh h' hh') hx

theorem burnsideI2BN_POmegaPlus {G : Type} [Group G] {p n f : ℕ} (hp : p.Prime)
    (hadm : StatedLieAdmissible .POmegaPlus n p f) (h : StatedClassicalModel G .POmegaPlus n p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hf, hn⟩ := hadm
  haveI : CharP K p := burnsideI2BN_charP_of_card hp hf hcard
  have hn3 : 3 ≤ n := by omega
  exact burnsideI2BN_exists_of_mulEquiv ((spinQuotientCenterEquivQuadPlus hn3).trans e.symm)
    (burnsideI2BN_exists_quotient_center
      (burnsideI2BN_spinPlus hp (hcard ▸ dvd_pow_self p (by omega)) hn3))

theorem burnsideI2BN_POmegaMinus {G : Type} [Group G] {p n f : ℕ} (hp : p.Prime)
    (hadm : StatedLieAdmissible .POmegaMinus n p f)
    (h : StatedClassicalModel G .POmegaMinus n p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨-, K, hK, hKf, hcard, b, c, hirr, ⟨e⟩⟩ := h
  obtain ⟨-, hf, hn⟩ := hadm
  haveI : CharP K p := burnsideI2BN_charP_of_card hp hf hcard
  exact burnsideI2BN_exists_of_mulEquiv ((spinQuotientCenterEquivQuadMinus hn hirr).trans e.symm)
    (burnsideI2BN_exists_quotient_center
      (burnsideI2BN_spinMinus hp (hcard ▸ dvd_pow_self p (by omega)) hirr hn))

end SpinCases

section OddSpin

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.ClassicalInvolution.ModelFacts

variable {n : ℕ} {K : Type} [Field K]

theorem burnsideI2BN_oddBruhatExtras [Finite K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    BruhatExtras (oddDatum n K) (fun k => (torusB K k).range) := by
  have hct := oddDatum_isCTGroupDatum n K (oddDatum_iSup_eq_top n K h2 hn)
  have hext := oddDatum_steinbergExtras (n := n) h2
  obtain ⟨p, _, _⟩ := CFSG.LieType.Steinberg.CentralExt.TorusLift.exists_prime_charP (k := K)
  refine ⟨eq_bot_iff.2 fun x hx => ?_⟩
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.1 hx
  rw [Subgroup.mem_bot]
  have hneg := idBelow_of_mem_iSup (n := n) (K := K) (-1) _ (fun γ hγ => ⟨hγ.1, by
      have : ht (ι := Fin n) γ < 0 := hγ.2
      omega⟩) hxN
  obtain ⟨t, htT, u, hu, htu⟩ := (Set.ext_iff.1 (coe_borel hct) x).1 hxB
  have htu' : t * u = x := htu
  subst htu'
  have hD : (spinMat (quadOdd n K) t).IsDiag := isDiag_of_mem_iSup (n := n) (K := K) htT
  have hpos := idBelow_of_mem_iSup (n := n) (K := K) 1 _ (fun γ hγ => ⟨hγ.1, by
      have : 0 < ht (ι := Fin n) γ := hγ.2
      omega⟩) hu
  have hdiag : ∀ a, spinMat (quadOdd n K) (t * u) a a = spinMat (quadOdd n K) t a a := by
    intro a
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hpos a a (by simp), Matrix.one_apply_eq, mul_one]
    · intro c _ hca
      rw [hD (Ne.symm hca), zero_mul]
    · simp
  have ht1 : spinMat (quadOdd n K) t = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [← hdiag a]
      exact hneg a a (by simp)
    · rw [hD hab, Matrix.one_apply_ne hab]
  have hxu : spinMat (quadOdd n K) (t * u) = spinMat (quadOdd n K) u := by
    rw [map_mul, ht1, one_mul]
  have hu1 : spinMat (quadOdd n K) u = 1 :=
    eq_one_of_idBelow_one_of_idBelow_neg_one _ hpos (hxu ▸ hneg)
  have hu' : u = 1 := eq_one_of_mem_posPart h2 hu hu1
  subst hu'
  rw [mul_one] at hxN ⊢
  rcases eq_one_or_eq_neg_one_of_spinAction_eq_one_odd n K h2 t
    (spinAction_eq_one_of_spinMat_eq_one ht1) with h | h
  · exact Subtype.ext h
  · have hsq : t ^ 2 = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, h, OneMemClass.coe_one]
      simp)
    have hU : IsPGroup p ↥(negUnipotent (oddDatum n K)) := by
      refine (isPGroup_iSup_posSet hext
        (fun γ hγ => isPGroup_of_isParametrization SpinOdd.isParametrization hγ)
        (-htHom)).to_le (iSup₂_le fun γ hγ => le_iSup₂_of_le γ ⟨hγ.1, ?_⟩ le_rfl)
      exact neg_pos.2 hγ.2
    obtain ⟨k, hk⟩ := hU ⟨t, hxN⟩
    have htp : t ^ p ^ k = 1 := congrArg Subtype.val hk
    by_cases hp2 : p = 2
    · subst hp2
      have h20 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      exact absurd h20 h2
    · have hcop : Nat.Coprime (p ^ k) 2 :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp2)
      have h1 : orderOf t ∣ Nat.gcd (p ^ k) 2 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one htp) (orderOf_dvd_of_pow_eq_one hsq)
      rw [hcop] at h1
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

end OddSpin

section OddSpinBN

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank

theorem burnsideI2BN_spinOdd {p n : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hdvd : p ∣ Nat.card K) [CharP K p] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    ∃ B N : Subgroup ↥(spinGroup (quadOdd n K)), IsSplitBNPair p B N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (spinGroup (quadOdd n K)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have hext := oddDatum_steinbergExtras (n := n) h2
  refine ⟨_, _, burnsideI2BN_of_datum hp (D := oddDatum n K) (n := weylB K)
    (H := fun k => (torusB K k).range)
    (oddDatum_isCTGroupDatum n K (oddDatum_iSup_eq_top n K h2 hn)) hext
    (burnsideI2BN_oddBruhatExtras h2 hn)
    (isPGroup_iSup_pos hext fun γ hγ =>
      isPGroup_of_isParametrization SpinOdd.isParametrization hγ) ?_⟩
  exact burnsideI2BN_not_dvd_card_iSup_range_units hdvd (fun i => torusB K i)
    fun i j h hh h' hh' => hext.torus_commute i j h hh h' hh'

theorem burnsideI2BN_POmegaOdd {G : Type} [Group G] {p n f : ℕ} (hp : p.Prime)
    (hadm : StatedLieAdmissible .POmegaOdd n p f) (h : StatedClassicalModel G .POmegaOdd n p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  obtain ⟨-, hf, hn, hp2⟩ := hadm
  haveI : CharP K p := burnsideI2BN_charP_of_card hp hf hcard
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  exact burnsideI2BN_exists_of_mulEquiv ((spinQuotientCenterEquivQuadOdd h2 hn).trans e.symm)
    (burnsideI2BN_exists_quotient_center
      (burnsideI2BN_spinOdd hp (hcard ▸ dvd_pow_self p (by omega)) h2 hn))

end OddSpinBN

section ReeTwisted

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem burnsideI2BN_ree_derived
    (t : ReeTag) (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K t.prime] (hp : t.prime.Prime) (hK : Nat.card K = t.prime ^ (2 * a + 1)) :
    ∃ B N : Subgroup (DerivedCentralQuotient (reeFixedGroup t.tag K t.perm
      (fun i => if i ∈ t.longSet then t.prime ^ a else t.prime ^ (a + 1)))),
      IsSplitBNPair t.prime B N := by
  have hH := reeGamma_eq_reeFixedGroup (t := t) (K := K) (a := a)
  have hcomm := (ree_generic_fixed_group_perfect t a ha K hK).2.1
  have hD : ⁅t.reeGamma K a, t.reeGamma K a⁆ = t.reeGamma K a := by
    rw [← Subgroup.map_subtype_commutator, hcomm, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨B, N, h⟩ := burnsideI2BN_ree_hasSplit t a K hp
  have hD' := hD
  rw [hH] at hD'
  exact burnsideI2BN_derivedCentralQuotient hD'
    (burnsideI2BN_exists_of_mulEquiv (MulEquiv.subgroupCongr hH) ⟨B, N, h⟩)

theorem burnsideI2BN_twistedG2
    {G : Type} [Group G] {p f : ℕ}
    (hadm : StatedLieAdmissible .twistedG2 0 p f) (h : ReeTitsModel G .twistedG2 p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨-, a, hfa, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  obtain ⟨hp, -, -, hp3, -, h3f⟩ := hadm
  subst hp3 hfa
  haveI : CharP K 3 := burnsideI2BN_charP_of_card Nat.prime_three (by omega) hcard
  haveI : CharP K ReeTag.G2.prime := ‹CharP K 3›
  exact burnsideI2BN_exists_of_mulEquiv e.symm
    (burnsideI2BN_ree_derived ReeTag.G2 a (by omega) K Nat.prime_three hcard)

theorem burnsideI2BN_twistedF4
    {G : Type} [Group G] {p f : ℕ}
    (hadm : StatedLieAdmissible .twistedF4 0 p f) (h : ReeTitsModel G .twistedF4 p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨-, a, hfa, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  obtain ⟨hp, -, -, hp2, -, h3f⟩ := hadm
  subst hp2 hfa
  haveI : CharP K 2 := burnsideI2BN_charP_of_card Nat.prime_two (by omega) hcard
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  exact burnsideI2BN_exists_of_mulEquiv e.symm
    (burnsideI2BN_ree_derived ReeTag.F4 a (by omega) K Nat.prime_two hcard)

end ReeTwisted

section GraphFixed

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open scoped Pointwise

theorem burnsideI2BN_graphFixed_hasSplit
    (t : TwistTag) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) [CharP K p] (σ : K ≃+* K) :
    ∃ B N : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom), IsSplitBNPair p B N := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL t.tag K) := finite_modGL
  haveI : Finite ↥(graphFixedRootGroup t K σ.toRingHom) := inferInstance
  obtain ⟨hBeq, -, huniq, -, hUB, hUn, -, -, -, -, -, -, hΓgen, -⟩ :=
    fixed_root_Bruhat_decomposition t K σ
  obtain ⟨hmonN, -, hker, hHnorm, -, -, hNeq⟩ := fixed_root_monomial_quotient t K σ.toRingHom
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  obtain ⟨hw₀rel, hn₀N, -, -, hBinter, -, -, hNB⟩ := fixed_Borel_self_normalizers t K σ w₀ hw₀
  have hBΓ : graphFixedRootBorel t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedRootBorel_le t K σ.toRingHom
  have hNΓ : graphFixedRootMonomial t K σ.toRingHom ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedRootMonomial_le t K σ.toRingHom
  have hHB : graphFixedRootTorus t K σ.toRingHom ≤ graphFixedRootBorel t K σ.toRingHom :=
    graphFixedRootTorus_le_graphFixedRootBorel
  have hHN : graphFixedRootTorus t K σ.toRingHom ≤ graphFixedRootMonomial t K σ.toRingHom :=
    le_inf (inf_le_left.trans (graphFixedTorus_le_graphFixedMonomial t K σ.toRingHom)) inf_le_right
  have hBN : graphFixedRootBorel t K σ.toRingHom ⊓ graphFixedRootMonomial t K σ.toRingHom =
      graphFixedRootTorus t K σ.toRingHom := by
    refine le_antisymm (fun g hg => ?_) (le_inf hHB hHN)
    obtain ⟨hgB, hgN⟩ := Subgroup.mem_inf.1 hg
    have hg1 : g ∈ borelGroup t.tag K ⊓ monomialSubgroup t.tag K :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hgB).1).1,
        (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hgN).1).1⟩
    rw [(borel_weyl_intersection t.tag K).1] at hg1
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hg1, (Subgroup.mem_inf.1
      (Subgroup.mem_inf.1 hgB).1).2⟩, (Subgroup.mem_inf.1 hgB).2⟩
  have hHp : ¬ p ∣ Nat.card (graphFixedRootTorus t K σ.toRingHom) := by
    intro hd
    refine not_dvd_card_torusGroup (τ := t.tag) (K := K) p
      (hd.trans (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)))
  have hcell1 : ∀ x ∈ graphFixedRootBorel t K σ.toRingHom,
      x ∈ graphFixedRootBruhatCell t K σ.toRingHom 1 := fun x hx =>
    mem_graphFixedRootBruhatCell.2 ⟨x, hx, 1, one_mem _, by simp [canonicalRep_one]⟩
  have hsB : ∀ a, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∉
      graphFixedRootBorel t K σ.toRingHom := by
    intro a hB
    have h1 : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) :=
      mem_graphFixedRootBruhatCell.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
    exact Set.disjoint_left.1 (disjoint_graphFixedRootBruhatCell
      (t := t) (K := K) (σ := σ.toRingHom) (Ne.symm (t.orbitReflection_ne_one a)))
      (hcell1 _ hB) h1
  have hs2H : ∀ a, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        graphFixedRootTorus t K σ.toRingHom := by
    intro a
    have hsN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom
      (t.orbitReflection_mem a)
    have hmem : (⟨_, hsN⟩ : graphFixedRootMonomial t K σ.toRingHom) * ⟨_, hsN⟩ ∈
        (graphFixedRootWeylHom t K σ.toRingHom).ker := by
      rw [MonoidHom.mem_ker, map_mul, graphFixedRootWeylHom_canonicalRep t K σ.toRingHom
        (t.orbitReflection_mem a)]
      exact t.orbitReflection_mul_self a
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  have hS3 : ∀ s ∈ Set.range (fun a => canonicalRep (coxeterSystem t.tag) K
      (t.orbitReflection a)), ∀ w ∈ graphFixedRootMonomial t K σ.toRingHom,
      ∀ b ∈ graphFixedRootBorel t K σ.toRingHom,
      ∃ b₁ ∈ graphFixedRootBorel t K σ.toRingHom, ∃ b₂ ∈ graphFixedRootBorel t K σ.toRingHom,
        s * b * w = b₁ * w * b₂ ∨ s * b * w = b₁ * (s * w) * b₂ := by
    rintro _ ⟨a, rfl⟩ w hw b hb
    beta_reduce
    have hraW : t.orbitReflection a ∈ relWeylTwist t := t.orbitReflection_mem a
    have hsN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom hraW
    obtain ⟨wb, hwb⟩ : ∃ wb, graphFixedRootWeylHom t K σ.toRingHom ⟨w, hw⟩ = wb := ⟨_, rfl⟩
    have hwbW : wb ∈ relWeylTwist t := by
      rw [← graphFixedRootWeylHom_range t K σ.toRingHom]
      exact ⟨⟨w, hw⟩, hwb⟩
    have hnN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom hwbW
    have hh' : (canonicalRep (coxeterSystem t.tag) K wb)⁻¹ * w ∈
        graphFixedRootTorus t K σ.toRingHom := by
      have hmem : (⟨canonicalRep (coxeterSystem t.tag) K wb, hnN⟩ :
          graphFixedRootMonomial t K σ.toRingHom)⁻¹ * ⟨w, hw⟩ ∈
            (graphFixedRootWeylHom t K σ.toRingHom).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, graphFixedRootWeylHom_canonicalRep t K
          σ.toRingHom hwbW, hwb]
        simp
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.1 hmem
    have hrwW : t.orbitReflection a * wb ∈ relWeylTwist t := mul_mem hraW hwbW
    have hmN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom hrwW
    have hh'' : (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * wb))⁻¹ *
        (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * w) ∈
          graphFixedRootTorus t K σ.toRingHom := by
      have hmem : (⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * wb), hmN⟩ :
          graphFixedRootMonomial t K σ.toRingHom)⁻¹ *
            (⟨canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a), hsN⟩ * ⟨w, hw⟩) ∈
              (graphFixedRootWeylHom t K σ.toRingHom).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, graphFixedRootWeylHom_canonicalRep t K
          σ.toRingHom hrwW, graphFixedRootWeylHom_canonicalRep t K σ.toRingHom hraW, hwb]
        simp
      rw [hker] at hmem
      exact Subgroup.mem_subgroupOf.1 hmem
    have hmemprod : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w ∈
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) *
          graphFixedRootBruhatCell t K σ.toRingHom wb :=
      Set.mul_mem_mul (mem_graphFixedRootBruhatCell.2 ⟨1, one_mem _, b, hb, by simp⟩)
        (mem_graphFixedRootBruhatCell.2 ⟨1, one_mem _, _, hHB hh', by simp⟩)
    obtain ⟨hmul1, hmul2, hmul3, -⟩ := fixed_simple_Bruhat_multiplication t K σ
    have hcase1 : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w ∈
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a * wb) →
        ∃ b₁ ∈ graphFixedRootBorel t K σ.toRingHom, ∃ b₂ ∈ graphFixedRootBorel t K σ.toRingHom,
          canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w =
            b₁ * (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * w) * b₂ := by
      intro hx
      obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := mem_graphFixedRootBruhatCell.1 hx
      generalize canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * wb) = m at hh'' he
      refine ⟨b₁, hb₁, (m⁻¹ * (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * w))⁻¹
        * b₂, mul_mem (inv_mem (hHB hh'')) hb₂, ?_⟩
      rw [← he]
      group
    have hcase2 : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w ∈
        graphFixedRootBruhatCell t K σ.toRingHom wb →
        ∃ b₁ ∈ graphFixedRootBorel t K σ.toRingHom, ∃ b₂ ∈ graphFixedRootBorel t K σ.toRingHom,
          canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b * w = b₁ * w * b₂ := by
      intro hx
      obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ := mem_graphFixedRootBruhatCell.1 hx
      generalize canonicalRep (coxeterSystem t.tag) K wb = n at hh' he
      refine ⟨b₁, hb₁, (n⁻¹ * w)⁻¹ * b₂, mul_mem (inv_mem (hHB hh')) hb₂, ?_⟩
      rw [← he]
      group
    rcases forall_height_pos_or_forall_height_neg (inv_mem hwbW) a with hp | hn
    · have hlen := (length_orbitReflection_mul_of_pos t hwbW hp).1
      rw [hmul2 wb hwbW a hlen] at hmemprod
      obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := hcase1 hmemprod
      exact ⟨b₁, hb₁, b₂, hb₂, Or.inr h⟩
    · have hlen := (length_orbitReflection_mul_of_neg t hwbW hn).1
      rw [hmul3 wb hwbW a hlen] at hmemprod
      rcases hmemprod with hx | hx
      · obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := hcase1 hx
        exact ⟨b₁, hb₁, b₂, hb₂, Or.inr h⟩
      · obtain ⟨b₁, hb₁, b₂, hb₂, h⟩ := hcase2 hx
        exact ⟨b₁, hb₁, b₂, hb₂, Or.inl h⟩
  have hS4 : ∀ s ∈ Set.range (fun a => canonicalRep (coxeterSystem t.tag) K
      (t.orbitReflection a)), ∃ b ∈ graphFixedRootBorel t K σ.toRingHom,
        s * b * s ∉ graphFixedRootBorel t K σ.toRingHom := by
    rintro _ ⟨a, rfl⟩
    beta_reduce
    by_contra hcon
    push Not at hcon
    apply hsB a
    have hs2 := hs2H a
    have hsN := canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom
      (t.orbitReflection_mem a)
    have hnorm : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        Subgroup.normalizer (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) := by
      generalize canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) = n at hs2 hcon
      refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
      · have e : n * x * n⁻¹ = (n * x * n) * (n * n)⁻¹ := by group
        rw [e]
        exact (graphFixedRootBorel t K σ.toRingHom).mul_mem (hcon x hx)
          ((graphFixedRootBorel t K σ.toRingHom).inv_mem (hHB hs2))
      · have e : x = (n * n)⁻¹ * (n * (n * x * n⁻¹) * n) := by group
        rw [e]
        exact (graphFixedRootBorel t K σ.toRingHom).mul_mem
          ((graphFixedRootBorel t K σ.toRingHom).inv_mem (hHB hs2)) (hcon _ hx)
    have : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈
        graphFixedRootGroup t K σ.toRingHom ⊓
          Subgroup.normalizer (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) :=
      Subgroup.mem_inf.2 ⟨hNΓ hsN, hnorm⟩
    rw [hNB] at this
    exact this
  have hUp : IsPGroup p (graphFixedPosUnipotent t K σ.toRingHom) :=
    IsPGroup.to_le (((positive_root_triangularity.{0, 0} t.tag).2 K p).2.1) inf_le_left
  have hUH0 : graphFixedPosUnipotent t K σ.toRingHom ⊓ graphFixedRootTorus t K σ.toRingHom =
      ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxH⟩ := Subgroup.mem_inf.1 hx
    have := huniq x hxH 1 (one_mem _) 1 (one_mem _) x hxU (by simp)
    exact Subgroup.mem_bot.2 this.1
  have hUN : graphFixedPosUnipotent t K σ.toRingHom ⊓ graphFixedRootMonomial t K σ.toRingHom =
      ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
    have hxH : x ∈ graphFixedRootTorus t K σ.toRingHom := by
      rw [← hBN]
      exact Subgroup.mem_inf.2 ⟨graphFixedPosUnipotent_le_graphFixedRootBorel hxU, hxN⟩
    rw [← hUH0]
    exact Subgroup.mem_inf.2 ⟨hxU, hxH⟩
  have hUHB : graphFixedPosUnipotent t K σ.toRingHom ⊔ graphFixedRootTorus t K σ.toRingHom =
      graphFixedRootBorel t K σ.toRingHom := by
    refine le_antisymm (sup_le graphFixedPosUnipotent_le_graphFixedRootBorel hHB) fun b hb => ?_
    have hb' : b ∈ (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) := by
      rw [← hBeq]
      exact hb
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    exact mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hu)
  have hsat : (⨅ n ∈ graphFixedRootMonomial t K σ.toRingHom, CFSG.conjugate
      (graphFixedRootBorel t K σ.toRingHom) n) = graphFixedRootBorel t K σ.toRingHom ⊓
        graphFixedRootMonomial t K σ.toRingHom := by
    refine burnsideI2BN_sat_of_opposite ?_ hn₀N ?_
    · rw [hBN]
      exact hHnorm
    · intro z hz hz'
      have hzT : z ∈ graphFixedRootTorus t K σ.toRingHom := by
        rw [← hBinter]
        refine Subgroup.mem_inf.2 ⟨hz, ?_⟩
        refine ⟨_, hz', ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      exact hHN hzT
  refine ⟨_, _, burnsideI2BN_isSplit_sub (Γ := graphFixedRootGroup t K σ.toRingHom)
    (B := graphFixedRootBorel t K σ.toRingHom) (N := graphFixedRootMonomial t K σ.toRingHom)
    (U := graphFixedPosUnipotent t K σ.toRingHom)
    (S := Set.range fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)) hp
    hBΓ hNΓ hΓgen.symm (by rw [hBN]; exact hHnorm) ?_ ?_ hS3 hS4
    graphFixedPosUnipotent_le_graphFixedRootBorel hUn hUp hUN ?_ hsat (by rw [hBN]; exact hHp)⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom (t.orbitReflection_mem a),
      hsB a, by rw [pow_two]; exact hHB (hs2H a)⟩
  · rw [hBN, sup_comm]
    exact hNeq.symm
  · rw [hBN]
    exact hUHB

theorem burnsideI2BN_twisted_model
    {G : Type} [Group G] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {t : TwistTag} (h : TwistedChevalleyModel G t (p ^ f)) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨K, hK, hKf, hcard, σ, hσ, ⟨e⟩⟩ := h
  have hord := two_le_order_twistTag t
  haveI : CharP K p := burnsideI2BN_charP_of_card hp (f := f * t.order)
    (Nat.mul_pos hf (by omega)) (by rw [hcard, pow_mul])
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩, RingHom.ext fun _ => rfl⟩
  have h3 := (finite_fixed_root_group_perfect t hp hf K hcard σ'.toRingHom hσ).2.2.1
  exact burnsideI2BN_exists_of_mulEquiv e.symm
    (burnsideI2BN_derivedCentralQuotient h3 (burnsideI2BN_graphFixed_hasSplit t K hp σ'))

end GraphFixed

section ExceptionalCases

theorem burnsideI2BN_untwisted
    {G : Type} [Group G] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    {τ : CFSG.Blueprint.Chevalley.Tag} (h : UntwistedChevalleyModel G τ (p ^ f)) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := h
  exact burnsideI2BN_exists_of_mulEquiv e.symm (burnsideI2BN_exists_quotient_center
    (adjointGroup_has_splitBNPair hp hf τ K hcard))

end ExceptionalCases

section SuzukiModelCase

theorem burnsideI2BN_suzuki_model
    {G : Type} [Group G] {p f : ℕ} (h : SuzukiModel G p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  obtain ⟨rfl, a, -, K, hK, hKf, hfa, hcard, ⟨e⟩⟩ := h
  exact burnsideI2BN_exists_of_mulEquiv e.symm
    (suzukiGroup_has_splitBNPair a K (hfa ▸ hcard))

end SuzukiModelCase

section LieModelMain

theorem lieModel_has_splitBNPair {G : Type} [Group G] [Finite G] {p n f : ℕ}
    {t : StatedLieTag} (hp : p.Prime) (ht : t ≠ .Tits) (hG : LieModel G t n p f) :
    ∃ B N : Subgroup G, IsSplitBNPair p B N := by
  rcases hG with ⟨htc, hcl⟩ | ⟨-, htc, hce⟩ | ⟨-, htc, hrt⟩ | ⟨-, rfl, hsz⟩
  · have hcl' := hcl
    obtain ⟨hadm, -⟩ := hcl
    simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at htc
    rcases htc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact burnsideI2BN_PSL hp hadm hcl'
    · exact burnsideI2BN_PSU hp hadm hcl'
    · exact burnsideI2BN_PSp hp hadm hcl'
    · exact burnsideI2BN_POmegaOdd hp hadm hcl'
    · exact burnsideI2BN_POmegaPlus hp hadm hcl'
    · exact burnsideI2BN_POmegaMinus hp hadm hcl'
  · obtain ⟨hadm, hmod⟩ := hce
    obtain ⟨-, hf, -⟩ := hadm
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at htc
    rcases htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact burnsideI2BN_untwisted hp hf hmod
    · exact burnsideI2BN_untwisted hp hf hmod
    · exact burnsideI2BN_untwisted hp hf hmod
    · exact burnsideI2BN_untwisted hp hf hmod
    · exact burnsideI2BN_untwisted hp hf hmod
    · exact burnsideI2BN_twisted_model hp hf hmod
    · exact burnsideI2BN_twisted_model hp hf hmod
  · obtain ⟨hadm, hmod⟩ := hrt
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at htc
    rcases htc with rfl | rfl | rfl
    · exact burnsideI2BN_twistedG2 hadm ⟨hadm, hmod⟩
    · exact burnsideI2BN_twistedF4 hadm ⟨hadm, hmod⟩
    · exact absurd rfl ht
  · exact burnsideI2BN_suzuki_model hsz

end LieModelMain

end BNPair

section I2bVocab

open CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped MatrixGroups

section I2b

variable {V : Type} [CommGroup V]

@[expose] def SpDerivedNatural (H : Subgroup (MulAut V)) (U Z : Subgroup V) (a : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
    (FFModel.nat ⁅StatedSp 2 K, StatedSp 2 K⁆).Realizes H U Z

@[expose] def zornO0F (F : Type) [Field F] : Submodule F (quasithinZorn F) where
  carrier := {x | x.1 + x.2.2.2 = 0}
  add_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add] at hx hy ⊢
    rw [add_add_add_comm, hx, hy, add_zero]
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hx ⊢
    rw [← mul_add, hx, mul_zero]

@[expose] def IsEndStableMod (L : Subgroup (MulAut V)) (W0 U : Subgroup V) : Prop :=
  ∀ φ : (V ⧸ W0) →* (V ⧸ W0),
    (∀ g ∈ L, ∀ v w : V, φ (QuotientGroup.mk v) = QuotientGroup.mk w →
      φ (QuotientGroup.mk (g v)) = QuotientGroup.mk (g w)) →
    ∀ u ∈ U, ∃ w ∈ U, φ (QuotientGroup.mk u) = QuotientGroup.mk w

@[expose] def IsTInvFSub (L T : Subgroup (MulAut V)) (W0 : Subgroup V) (n i : ℕ) (U : Subgroup V) : Prop :=
  W0 ≤ U ∧ (∀ t ∈ T, ∀ u ∈ U, t u ∈ U) ∧ IsEndStableMod L W0 U ∧
    Nat.card ↥U = Nat.card ↥W0 * (2 ^ n) ^ i

abbrev I23Holomorph (V : Type) [CommGroup V] :=
  SemidirectProduct V (MulAut V) (MonoidHom.id (MulAut V))

@[expose] def i23ModuleSubgroup (U : Subgroup V) : Subgroup (I23Holomorph V) :=
  U.map (SemidirectProduct.inl : V →* I23Holomorph V)

@[expose] def i23Extension (G : Subgroup (MulAut V)) : Subgroup (I23Holomorph V) :=
  G.comap (SemidirectProduct.rightHom : I23Holomorph V →* MulAut V)

@[expose] def I23LiteralCentralCore (G : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  i23ModuleSubgroup U ≤
    centerOf (pCoreOf 2
      (i23Extension G ⊓ Subgroup.normalizer (i23ModuleSubgroup U : Set (I23Holomorph V))))

@[expose] def I23CentralCoreCompatibility : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (U : Subgroup V),
      I23LiteralCentralCore G U ↔ pCoreOf 2 (G ⊓ stabSub U) ≤ centSub U

@[expose] def i23NaturalModel (m : ℕ) (F : Type) [Field F] : FFModel :=
  match m with
  | 0 => FFModel.zornQ ⁅quasithinG2 F, quasithinG2 F⁆
  | 1 => FFModel.nat (StatedSL 2 F)
  | 2 => FFModel.nat ⁅StatedSp 2 F, StatedSp 2 F⁆
  | _ + 3 => FFModel.zornQ ⁅quasithinG2 F, quasithinG2 F⁆

@[expose] def i23NaturalScalar (m : ℕ) (F : Type) [Field F] :
    F → (i23NaturalModel m F).Amb → (i23NaturalModel m F).Amb := by
  match m with
  | 0 =>
      change F → Multiplicative (quasithinZorn F) → Multiplicative (quasithinZorn F)
      exact fun scalar vector => Multiplicative.ofAdd (scalar • Multiplicative.toAdd vector)
  | 1 =>
      change F → Multiplicative (Fin 2 → F) → Multiplicative (Fin 2 → F)
      exact fun scalar vector => Multiplicative.ofAdd (scalar • Multiplicative.toAdd vector)
  | 2 =>
      change F → Multiplicative ((Fin 2 ⊕ Fin 2) → F) →
        Multiplicative ((Fin 2 ⊕ Fin 2) → F)
      exact fun scalar vector => Multiplicative.ofAdd (scalar • Multiplicative.toAdd vector)
  | _ + 3 =>
      change F → Multiplicative (quasithinZorn F) → Multiplicative (quasithinZorn F)
      exact fun scalar vector => Multiplicative.ofAdd (scalar • Multiplicative.toAdd vector)

@[expose] def I23SectionMap (D : FFModel) (L : Subgroup (MulAut V)) (W0 : Subgroup V)
    (π : D.Gam →* ↥L) (β : V →* ↥D.sec ⧸ D.ker.subgroupOf D.sec) : Prop :=
  Function.Surjective π ∧ Function.Surjective β ∧ β.ker = W0 ∧ D.ker ≤ D.sec ∧
    (∀ γ : D.Gam, ∀ vector ∈ D.sec, D.act γ vector ∈ D.sec) ∧
    (∀ γ : D.Gam, ∀ vector ∈ D.ker, D.act γ vector ∈ D.ker) ∧
    ∀ (γ : D.Gam) (vector : V) (native : ↥D.sec)
      (hNative : D.act γ (native : D.Amb) ∈ D.sec),
      β vector = QuotientGroup.mk native →
        β ((π γ : MulAut V) vector) =
          QuotientGroup.mk ⟨D.act γ (native : D.Amb), hNative⟩

@[expose] def IsI23MarkedSubspace (m n i : ℕ) (F : Type) [Field F]
    (T : Subgroup (MulAut V)) (W0 U : Subgroup V)
    (β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec) : Prop :=
  W0 ≤ U ∧ (∀ t ∈ T, ∀ vector ∈ U, t vector ∈ U) ∧
    Nat.card ↥U = Nat.card ↥W0 * (2 ^ n) ^ i ∧
    ∀ (scalar : F) (vector : V), vector ∈ U →
      ∀ native : ↥(i23NaturalModel m F).sec,
        β vector = QuotientGroup.mk native →
          ∃ image : V, image ∈ U ∧
            ∃ hNative : i23NaturalScalar m F scalar native ∈ (i23NaturalModel m F).sec,
              β image = QuotientGroup.mk ⟨i23NaturalScalar m F scalar native, hNative⟩

@[expose] def i23TransvectionRoot (L : Subgroup (MulAut V)) (W0 U : Subgroup V) :
    Subgroup (MulAut V) :=
  Subgroup.closure {root | root ∈ L ∧
    (∀ vector : V, root vector * vector⁻¹ ∈ U) ∧
    (∀ vector ∈ U, root vector * vector⁻¹ ∈ W0) ∧
    ∃ vector : V, root vector * vector⁻¹ ∉ W0}

@[expose] def I23ScalarCompatibility (m : ℕ) (F : Type) [Field F]
    {W : Type} [AddCommGroup W] [Module F W] (ψ : V ≃* Multiplicative W)
    (β : V →* ↥(i23NaturalModel m F).sec ⧸
      (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec) : Prop :=
  ∀ (scalar : F) (vector : V) (native : ↥(i23NaturalModel m F).sec),
    β vector = QuotientGroup.mk native →
      ∃ hNative : i23NaturalScalar m F scalar native ∈ (i23NaturalModel m F).sec,
        β (ψ.symm (Multiplicative.ofAdd (scalar • Multiplicative.toAdd (ψ vector)))) =
          QuotientGroup.mk ⟨i23NaturalScalar m F scalar native, hNative⟩

@[expose] def i23G2HighestLongRoot (F : Type) [Field F] :
    Subgroup ↥⁅quasithinG2 F, quasithinG2 F⁆ :=
  Subgroup.closure {γ | ∃ c : F, ∀ x : quasithinZorn F,
    (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F) x =
      (x.1,
        (fun i => x.2.1 i + if i = 1 then c * x.2.1 2 else 0),
        (fun i => x.2.2.1 i - if i = 2 then c * x.2.2.1 1 else 0),
        x.2.2.2)}

@[expose] def i23NativeHighestLongRoot (m : ℕ) (F : Type) [Field F] :
    Subgroup (i23NaturalModel m F).Gam :=
  match m with
  | 0 => i23G2HighestLongRoot F
  | 1 => ⊥
  | 2 => ⊥
  | _ + 3 => i23G2HighestLongRoot F

@[expose] def IsI23MarkedLongRoot (m : ℕ) (F : Type) [Field F]
    (L : Subgroup (MulAut V))
    (marking : (i23NaturalModel m F).Gam →* ↥L)
    (S : Subgroup (MulAut V)) : Prop :=
  ∃ γ : (i23NaturalModel m F).Gam,
    S = (CFSG.conjugate (i23NativeHighestLongRoot m F) γ).map
      (L.subtype.comp marking)

@[expose] def IsUniversalCovering (G : Subgroup (MulAut V)) (W0 : Subgroup V) : Prop :=
  W0 ≤ fixV G ∧ commV G = ⊤ ∧
  ∀ (V' : Type) [CommGroup V'] [Finite V'] (ρ' : ↥G →* MulAut V') (W0' : Subgroup V')
    (ψ' : V' →* V ⧸ W0),
    (∀ v : V', v ^ 2 = 1) → (∀ w ∈ W0', ∀ g : ↥G, ρ' g w = w) →
    Subgroup.closure {w : V' | ∃ (g : ↥G) (v : V'), w = ρ' g v * v⁻¹} = ⊤ →
    Function.Surjective ψ' → ψ'.ker = W0' →
    (∀ (g : ↥G) (v' : V') (v : V), ψ' v' = QuotientGroup.mk v →
      ψ' (ρ' g v') = QuotientGroup.mk ((g : MulAut V) v)) →
    ∃ θ : V →* V', Function.Surjective θ ∧ (∀ (g : ↥G) (v : V), θ ((g : MulAut V) v) = ρ' g (θ v)) ∧
      ∀ v : V, ψ' (θ v) = QuotientGroup.mk v

@[expose] def I23RelativeUniversalLift (G L : Subgroup (MulAut V))
    (W0 : Subgroup V) : Prop :=
  ∃ (hLG : L ≤ G) (U : Type) (_ : CommGroup U) (_ : Finite U)
    (ρ : ↥G →* MulAut U) (K : Subgroup U) (θ : U →* V),
    (∀ u : U, u ^ 2 = 1) ∧
    IsUniversalCovering (ρ.comp (Subgroup.inclusion hLG)).range K ∧
    Function.Surjective θ ∧ K = W0.comap θ ∧
    ∀ (g : ↥G) (u : U), θ (ρ g u) = (g : MulAut V) (θ u)

@[expose] def I23Case (m n : ℕ) (L : Subgroup (MulAut V)) (W0 : Subgroup V) : Prop :=
  (m = 1 ∧ 1 < n ∧ BinaryNaturalSL L ⊤ W0 2 n) ∨ (m = 2 ∧ SpDerivedNatural L ⊤ W0 n) ∨
    (m = 3 ∧ G2NaturalDerived L ⊤ W0 n)

@[expose] def IsFSubspaceVia {F : Type} [Field F] {W : Type} [AddCommGroup W] [Module F W]
    (ψ : V ≃* Multiplicative W) (U : Subgroup V) (k : ℕ) : Prop :=
  ∃ S : Submodule F W, Module.finrank F ↥S = k ∧ ∀ v : V, v ∈ U ↔ Multiplicative.toAdd (ψ v) ∈ S

@[expose] def polarOf {F : Type} [Field F] {W : Type} [AddCommGroup W] (Q : W → F) (x y : W) : F :=
  Q (x + y) - Q x - Q y

@[expose] def I23SmallSymplecticConcl {F : Type} [Field F]
    {W : Type} [AddCommGroup W] [Module F W] (Q : W → F)
    (ψ : V ≃* Multiplicative W) (L T : Subgroup (MulAut V))
    (V1 V2 : Subgroup V) : Prop :=
  Nat.card ↥(omegaOne (centerOf (T ⊓ L))) = 2 ∧
  ∀ z ∈ omegaOne (centerOf (T ⊓ L)), z ≠ 1 →
    let D := commV (Subgroup.zpowers z)
    IsFSubspaceVia (F := F) ψ D 2 ∧
    D ≤ fixV (Subgroup.zpowers z) ∧ D ⊓ fixV L = ⊥ ∧ D ⊔ fixV L = V2 ∧
    (∀ x ∈ D, ∀ y ∈ D,
      polarOf Q (Multiplicative.toAdd (ψ x)) (Multiplicative.toAdd (ψ y)) = 0) ∧
    (∃ x ∈ D, Q (Multiplicative.toAdd (ψ x)) ≠ 0) ∧
    IsFSubspaceVia (F := F) ψ (D ⊓ V1) 1 ∧
    (∀ x ∈ D ⊓ V1, Q (Multiplicative.toAdd (ψ x)) = 0) ∧
    V1 = (D ⊓ V1) ⊔ fixV L

@[expose] def OrthConcl {F : Type} [Field F] {W : Type} [AddCommGroup W] [Module F W] (Q : W → F)
    (m n : ℕ) (ψ : V ≃* Multiplicative W) (L T R : Subgroup (MulAut V)) (V1 V2 : Subgroup V) : Prop :=
  ((∀ v : V, v ∈ fixV L ↔ ∀ w : W, polarOf Q (Multiplicative.toAdd (ψ v)) w = 0) ∧
      Nat.card ↥(fixV L) = 2 ^ n) ∧
  (V1 = fixV (T ⊓ L) ∧
    ∃! P : Subgroup V, IsFSubspaceVia (F := F) ψ P 1 ∧
      (∀ v ∈ P, Q (Multiplicative.toAdd (ψ v)) = 0) ∧ V1 = P ⊔ fixV L ∧ P ⊓ fixV L = ⊥) ∧
  (m ≠ 3 ∧ (m ≠ 2 ∨ n ≠ 1) →
    (∀ r ∈ R, r ≠ 1 →
      (IsFSubspaceVia (F := F) ψ (commV (Subgroup.zpowers r)) 1 ∧
        (∃ v ∈ commV (Subgroup.zpowers r), Q (Multiplicative.toAdd (ψ v)) ≠ 0) ∧
        commV (Subgroup.zpowers r) ≤ V1 ∧ commV (Subgroup.zpowers r) ≠ fixV L) ∧
      (1 < n → ∀ s ∈ R, s ∉ Subgroup.zpowers r →
        commV (Subgroup.zpowers r) ⊓ commV (Subgroup.zpowers s) = ⊥)) ∧
    (1 < n → V1 = commV R ∧ commV R ≤ fixV R)) ∧
  (m = 2 ∧ n = 1 → R = ⊥ ∧ I23SmallSymplecticConcl Q ψ L T V1 V2) ∧
  (m = 3 →
    (IsFSubspaceVia (F := F) ψ (commV (omegaOne (centerOf (T ⊓ L)))) 2 ∧
      (∀ v ∈ commV (omegaOne (centerOf (T ⊓ L))), Q (Multiplicative.toAdd (ψ v)) = 0) ∧
      commV (omegaOne (centerOf (T ⊓ L))) ⊓ fixV L = ⊥ ∧
      commV (omegaOne (centerOf (T ⊓ L))) ⊔ fixV L = V2))

@[expose] def OrthConclMarked {F : Type} [Field F] {W : Type} [AddCommGroup W] [Module F W] (Q : W → F)
    (m n : ℕ) (ψ : V ≃* Multiplicative W) (L T R S : Subgroup (MulAut V)) (V1 V2 : Subgroup V) : Prop :=
  ((∀ v : V, v ∈ fixV L ↔ ∀ w : W, polarOf Q (Multiplicative.toAdd (ψ v)) w = 0) ∧
      Nat.card ↥(fixV L) = 2 ^ n) ∧
  (V1 = fixV (T ⊓ L) ∧
    ∃! P : Subgroup V, IsFSubspaceVia (F := F) ψ P 1 ∧
      (∀ v ∈ P, Q (Multiplicative.toAdd (ψ v)) = 0) ∧ V1 = P ⊔ fixV L ∧ P ⊓ fixV L = ⊥) ∧
  (m ≠ 3 ∧ (m ≠ 2 ∨ n ≠ 1) →
    (∀ r ∈ R, r ≠ 1 →
      (IsFSubspaceVia (F := F) ψ (commV (Subgroup.zpowers r)) 1 ∧
        (∃ v ∈ commV (Subgroup.zpowers r), Q (Multiplicative.toAdd (ψ v)) ≠ 0) ∧
        commV (Subgroup.zpowers r) ≤ V1 ∧ commV (Subgroup.zpowers r) ≠ fixV L) ∧
      (1 < n → ∀ s ∈ R, s ∉ Subgroup.zpowers r →
        commV (Subgroup.zpowers r) ⊓ commV (Subgroup.zpowers s) = ⊥)) ∧
    (1 < n → V1 = commV R ∧ commV R ≤ fixV R)) ∧
  (m = 2 ∧ n = 1 → R = ⊥ ∧ I23SmallSymplecticConcl Q ψ L T V1 V2) ∧
  (m = 3 →
    (IsFSubspaceVia (F := F) ψ (commV (S)) 2 ∧
      (∀ v ∈ commV (S), Q (Multiplicative.toAdd (ψ v)) = 0) ∧
      commV (S) ⊓ fixV L = ⊥ ∧
      commV (S) ⊔ fixV L = V2))

end I2b

end I2bVocab

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (φ : G →* Gs),
    Function.Surjective φ → Group.IsPerfect G → φ.ker ≤ Subgroup.center G →
    IsPGroup 3 (Subgroup.center G) →
    (StatedClassicalModel Gs .PSU 4 3 1 ∨ ChevalleyExceptionalModel Gs .G2 3 1 ∨
      StatedClassicalModel Gs .POmegaOdd 3 3 1 ∨ NativeSporadic.IsSporadic Gs .ONan ∨
      NativeSporadic.IsSporadic Gs .J3 ∨ NativeSporadic.IsSporadic Gs .McL) →
    2 < CFSG.pRank 3 G

section BurnsideI2b

private theorem burnsideI2a_two_lt_pRank_of_central_quotient {G Gs : Type} [Group G] [Finite G]
    [Group Gs] [Finite Gs] (φ : G →* Gs) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Gs)) : 2 < CFSG.pRank 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  have hG : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  have h3 := CFSG.SectionRank.pRank_quotient_le_three (by norm_num) hG φ.ker hker
  have h5 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  omega

private theorem burnsideI2a_four_le_pRank_of_elem {Gs T : Type} [Group Gs] [Finite Gs] [Group T]
    (e : Gs ≃* T) (hT : ∃ E : Subgroup T, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Gs) := by
  haveI : Finite T := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, hE, hcard⟩ := hT
  have h := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (le_top : E ≤ ⊤) hE hcard
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h
  exact h

private theorem burnsideI2a_chevalleyG2_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {p f : ℕ} (h : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 p f) :
    CFSG.Blueprint.ChevalleyExceptionalModel X .G2 p f := by
  obtain ⟨hadm, K, hK, hKfin, hcard, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK, hKfin, hcard, ⟨e.trans e'⟩⟩

end BurnsideI2b

section

theorem as_I_2_1 : I_2_1 := by
  intro G _ _ Gs _ φ hφ _ hker hcen hmod
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite Gs := Finite.of_surjective φ hφ
  rcases hmod with hU | hG2 | hO | hON | hJ3 | hMcL
  ·
    obtain ⟨-, -, hrk⟩ := CFSG.SectionRank.classical_model_rank (by norm_num) hU
    refine burnsideI2a_two_lt_pRank_of_central_quotient φ hφ hker ?_
    rcases hrk with ⟨h, -⟩ | ⟨-, ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | h
    · exact absurd h (by decide)
    · exact absurd h (by norm_num)
    · exact h
    · exact absurd h (by decide)
    · exact h
  ·
    exact (CFSG.SectionRank.g2_odd_central_cover_rank_three φ.ker hker Nat.prime_three
      (by norm_num) (burnsideI2a_chevalleyG2_of_mulEquiv
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ) hG2)).1
  ·
    obtain ⟨-, -, hrk⟩ := CFSG.SectionRank.classical_model_rank (by norm_num) hO
    refine burnsideI2a_two_lt_pRank_of_central_quotient φ hφ hker ?_
    rcases hrk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  ·
    obtain ⟨e⟩ := hON
    exact burnsideI2a_two_lt_pRank_of_central_quotient φ hφ hker
      (burnsideI2a_four_le_pRank_of_elem e CFSG.SectionRank.ON_elementary_three_rank_four)
  ·
    obtain ⟨e⟩ := hJ3
    obtain ⟨K, hKp, Q, x, y, h, cc, a, b, c, d, -, hQ, hQcard, hcyc, hhK, hgen, hx, hy, hdet, hcK,
      hcc, hcK1⟩ := CFSG.SectionRank.J3_perfect_local_det_witness
    haveI : Finite CFSG.Blueprint.NativeSporadic.J3 := Finite.of_equiv _ e.toEquiv
    let π : G →* CFSG.Blueprint.NativeSporadic.J3 := e.toMonoidHom.comp φ
    have hπ : Function.Surjective π := e.surjective.comp hφ
    have hπker : π.ker ≤ Subgroup.center G := fun g hg => hker (by
      have h1 : e (φ g) = 1 := hg
      rw [MonoidHom.mem_ker]
      exact e.injective (by rw [h1, map_one]))
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hcen.to_le hπker)
    have hodd : Odd (Nat.card π.ker) := by
      rw [hn]
      exact Odd.pow (by decide)
    obtain ⟨E3, hE3, hcard⟩ := CFSG.SectionRank.perfect_local_det_cover_rank K Q hQ hQcard hcyc h
      hhK hgen hx hy hdet cc hcK hcc hcK1 π hπ hπker hodd
    have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hE3 hcard
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  ·
    obtain ⟨e⟩ := hMcL
    exact burnsideI2a_two_lt_pRank_of_central_quotient φ hφ hker
      (burnsideI2a_four_le_pRank_of_elem e CFSG.SectionRank.McL_elementary_three_rank_four)

end

@[expose] def I_2_2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    (IsPGroup 2 (Subgroup.center K) →
      (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 5)) →
        Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ∧
      (Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) →
        Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 3 2)))) ∧
    ((Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7))) →
      CFSG.pRank 3 K = 2) ∧
    ((StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 3 2 2 ∧ IsPGroup 2 (Subgroup.center K)) →
      ∀ Ps : Subgroup (K ⧸ Subgroup.center K), IsMaxParabolicTwo Ps →
        (frattini ↥(Subgroup.center K) ≠ ⊥ →
          (∀ S : Sylow 2 K,
            (Subgroup.center ↥(S : Subgroup K)).map (S : Subgroup K).subtype =
              Subgroup.center K) ∧
          ∃ a ∈ pCoreOf 2 (preimageStar K Ps), ∃ b ∈ pCoreOf 2 (preimageStar K Ps),
            a * b ≠ b * a) ∧
        (frattini ↥(Subgroup.center K) = ⊥ →
          InvolutionsLift K ∧ frattiniOf (pCoreOf 2 (preimageStar K Ps)) = ⊥ ∧
          ⁅pCoreOf 2 (preimageStar K Ps), preimageStar K Ps⁆ = pCoreOf 2 (preimageStar K Ps) ∧
          ∃ β : K ≃* K, IsGraphFieldAut β ∧ ∀ z ∈ Subgroup.center K, β z = z)) ∧
    (SuzukiModel (K ⧸ Subgroup.center K) 2 3 →
      InvolutionsLift K ∧ ∀ S : Sylow 2 K,
        Subgroup.center K = (Subgroup.center ↥(S : Subgroup K)).map (S : Subgroup K).subtype) ∧
    ((ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .J2 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M12 ∨
        NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .HS) →
      TwoCentralInvolutionsLift K ∧
      (NonTwoCentralInvolutionsLiftToOrderFour K ∧ OuterInvolutionsInvertOrderFour K) ∧
      (¬ ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 2 2 →
        ∀ u : K, u ∉ Subgroup.center K → u ^ 2 = 1 → UniqueSquareInCoset K u)) ∧
    ((NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .M22 ∧ IsPGroup 2 (Subgroup.center K)) →
      (∀ Js : Subgroup (K ⧸ Subgroup.center K), IsS5OverE16 Js →
        Subgroup.center K ≤ twoResidual (preimageStar K Js) ∧
        (Nat.card (Subgroup.center K) = 2 → frattiniOf (pCoreOf 2 (preimageStar K Js)) = ⊥) ∧
        (Nat.card (Subgroup.center K) = 4 → IsZ4StarQ8Sq ↥(pCoreOf 2 (preimageStar K Js)))) ∧
      (Nat.card (Subgroup.center K) = 2 →
        ∀ u : K, u ∉ Subgroup.center K → u ^ 2 = 1 → UniqueSquareInCoset K u)) ∧
    (NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) .Ru →
      ∀ i : K ⧸ Subgroup.center K, i ^ 2 = 1 → i ≠ 1 → ¬ IsTwoCentralInvolution i →
        (∃ L : Subgroup K, L ≤ preimageLayerCentralizer K i ∧ L ⊓ Subgroup.center K = ⊥ ∧
          L ⊔ Subgroup.center K = preimageLayerCentralizer K i) ∧
        ((∃ k : K, orderOf k = 4 ∧ (k : K ⧸ Subgroup.center K) = i) ∧
          TwoCentralInvolutionsLift K ∧ 6 ≤ CFSG.pRank 2 K) ∧
        ∀ u : K, u ∉ Subgroup.center K → u ^ 2 = 1 →
          Nat.card ↥⁅centralizerOfFrattiniOfCore K u, centralizerOfFrattiniOfCore K u⁆ = 2 ∧
          (⁅centralizerOfFrattiniOfCore K u, centralizerOfFrattiniOfCore K u⁆).map
              (QuotientGroup.mk' (Subgroup.center K)) =
            Subgroup.zpowers (u : K ⧸ Subgroup.center K))

@[expose] def I_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → ∀ P : Sylow p G,
    ∀ 𝒟 : Set (Subgroup G), IsConjugationFamily (P : Subgroup G) 𝒟 →
      ∀ Q : Subgroup G, Q ≤ (P : Subgroup G) →
        ((∀ D ∈ 𝒟, Q ≤ D → IsNormalIn Q (Subgroup.normalizer (D : Set G))) →
          IsWeaklyClosedIn Q (P : Subgroup G)) ∧
        ((∀ D ∈ 𝒟, ∀ E ∈ 𝒟, D ≤ E →
            Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (D : Set G)) →
          ∀ D ∈ 𝒟, IsWeaklyClosedIn D (P : Subgroup G))

theorem as_I_2_4 : I_2_4 := by
  intro G _ _ p hp P 𝒟 hfam Q hQP
  refine ⟨fun hn => weaklyClosed_of_fusion hfam hQP hn, fun hE D hD => ?_⟩
  refine weaklyClosed_of_fusion hfam (hfam.1 D hD) (fun D' hD' hDD' => ?_)
  refine ⟨hDD'.trans Subgroup.le_normalizer, ?_⟩
  refine ⟨fun n hn g => ?_⟩
  have hgD : (g : G) ∈ Subgroup.normalizer (D : Set G) := hE D hD D' hD' hDD' g.2
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have := (Subgroup.mem_normalizer_iff.1 hgD (n : G)).1 hn
  simpa using this

@[expose] def IsRankOneNormal {G : Type} [Group G] (p : ℕ) (B N : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ B → (U.subgroupOf B).Normal → IsPGroup p U → ¬ p ∣ U.index →
  ∀ s ∈ N, s ∉ B → (∀ b ∈ B, s * b * s ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, s * b * s = b₁ * s * b₂) →
    ∀ u ∈ U, ∀ c ∈ U, s⁻¹ * c * s ∈ B → s⁻¹ * (u * c * u⁻¹) * s ∈ B

@[expose] def I_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime →
    (∃ B N : Subgroup G, IsSplitBNPair p B N ∧ IsRankOneNormal p B N) →
    ∀ P : Subgroup G, (∃ U : Sylow p G, Subgroup.normalizer ((U : Subgroup G) : Set G) ≤ P) →
      ∀ S : Subgroup G, IsPGroup p S → pCoreOf p P ≤ S → IsWeaklyClosedIn (pCoreOf p P) S

section I2bProps

open CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.ASVolI.ChIJK CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped MatrixGroups

@[expose] def I_2_3_legacyUnmarked : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (G L T : Subgroup (MulAut V)) (W0 : Subgroup V) (m n : ℕ),
    L = quasithinGenFitting G → G = L ⊔ T → IsSylowTwoOf T G →
    (∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) → W0 ≤ fixV L → commV L = ⊤ →
    I23Case m n L W0 →
    ∀ V1 V2 : Subgroup V, IsTInvFSub L T W0 n 1 V1 → IsTInvFSub L T W0 n 2 V2 →
    (∀ U : Subgroup V, IsTInvFSub L T W0 n 1 U → U = V1) →
    (∀ U : Subgroup V, IsTInvFSub L T W0 n 2 U → U = V2) →
    ∀ R : Subgroup (MulAut V), R = i23TransvectionRoot L W0 V1 →
      (IsUniversalCovering L W0 →
        ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
          ((m = 1 ∨ m = 2) →
            ∃ (ψ : V ≃* Multiplicative (Fin m ⊕ Fin m ⊕ Unit → F))
              (π : ↥(StatedOmega (StatedQuadOdd m F)) →* ↥L),
              Function.Surjective π ∧
              (∀ (γ : ↥(StatedOmega (StatedQuadOdd m F))) (v : V),
                ψ ((π γ : MulAut V) v) = Multiplicative.ofAdd
                  (((γ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m ⊕ Unit) F) :
                    Matrix (Fin m ⊕ Fin m ⊕ Unit) (Fin m ⊕ Fin m ⊕ Unit) F).mulVec
                    (Multiplicative.toAdd (ψ v)))) ∧
              OrthConcl (StatedQuadOdd m F) m n ψ L T R V1 V2) ∧
          (m = 3 →
            ∃ (ψ : V ≃* Multiplicative ↥(zornO0F F))
              (π : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L),
              Function.Surjective π ∧
              (∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (v : V),
                ((Multiplicative.toAdd (ψ ((π γ : MulAut V) v)) : ↥(zornO0F F)) : quasithinZorn F) =
                  (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
                    ((Multiplicative.toAdd (ψ v) : ↥(zornO0F F)) : quasithinZorn F)) ∧
              OrthConcl (fun x : ↥(zornO0F F) => zornNorm F (x : quasithinZorn F)) m n ψ L T R V1 V2)) ∧
      (¬ (fixV T ⊓ V1 ≤ fixV L) ∧
        pCoreOf 2 (G ⊓ stabSub V1) ≤ centSub V1 ∧ pCoreOf 2 (G ⊓ stabSub V2) ≤ centSub V2) ∧
      (1 < n → fixV L ≤ V1 ∧ (m ≠ 3 → V1 = commV R ∧ commV R ≤ fixV R))

@[expose] def I_2_3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
  ∀ (G L T : Subgroup (MulAut V)) (W0 : Subgroup V) (m n : ℕ),
    L = quasithinGenFitting G → G = L ⊔ T → IsSylowTwoOf T G →
    (∀ g ∈ G, ∀ w ∈ W0, g w ∈ W0) → W0 ≤ fixV L → commV L = ⊤ →
    ((m = 1 ∧ 1 < n) ∨ (m = 2 ∧ 0 < n) ∨ (m = 3 ∧ 0 < n)) →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
    ∀ (marking : (i23NaturalModel m F).Gam →* ↥L)
      (β : V →* ↥(i23NaturalModel m F).sec ⧸
        (i23NaturalModel m F).ker.subgroupOf (i23NaturalModel m F).sec),
      I23SectionMap (i23NaturalModel m F) L W0 marking β →
      ∃ V1 V2 : Subgroup V,
        IsI23MarkedSubspace m n 1 F T W0 V1 β ∧
        IsI23MarkedSubspace m n 2 F T W0 V2 β ∧
        (∀ U : Subgroup V, IsI23MarkedSubspace m n 1 F T W0 U β → U = V1) ∧
        (∀ U : Subgroup V, IsI23MarkedSubspace m n 2 F T W0 U β → U = V2) ∧
        let R := i23TransvectionRoot L W0 V1
        ∃ S : Subgroup (MulAut V),
          (m = 3 → IsI23MarkedLongRoot m F L marking S ∧
            S = ChIJK.omegaOne (ChIJK.centerOf (T ⊓ L)) ∧
            (1 < n → S = ChIJK.centerOf (T ⊓ L))) ∧
          (m = 2 ∧ n = 1 → R = ⊥) ∧
      (IsUniversalCovering L W0 →
          ((m = 1 ∨ m = 2) →
            ∃ (ψ : V ≃* Multiplicative (Fin m ⊕ Fin m ⊕ Unit → F))
              (π : ↥(StatedOmega (StatedQuadOdd m F)) →* ↥L),
              Function.Surjective π ∧
              (∀ (γ : ↥(StatedOmega (StatedQuadOdd m F))) (v : V),
                ψ ((π γ : MulAut V) v) = Multiplicative.ofAdd
                  (((γ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m ⊕ Unit) F) :
                    Matrix (Fin m ⊕ Fin m ⊕ Unit) (Fin m ⊕ Fin m ⊕ Unit) F).mulVec
                    (Multiplicative.toAdd (ψ v)))) ∧
              I23ScalarCompatibility m F ψ β ∧
              OrthConclMarked (StatedQuadOdd m F) m n ψ L T R S V1 V2) ∧
          (m = 3 →
            ∃ (ψ : V ≃* Multiplicative ↥(zornO0F F))
              (π : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥L),
              Function.Surjective π ∧
              (∀ (γ : ↥⁅quasithinG2 F, quasithinG2 F⁆) (v : V),
                ((Multiplicative.toAdd (ψ ((π γ : MulAut V) v)) : ↥(zornO0F F)) : quasithinZorn F) =
                  (γ : quasithinZorn F ≃ₗ[F] quasithinZorn F)
                    ((Multiplicative.toAdd (ψ v) : ↥(zornO0F F)) : quasithinZorn F)) ∧
              I23ScalarCompatibility m F ψ β ∧
              OrthConclMarked (fun x : ↥(zornO0F F) => zornNorm F (x : quasithinZorn F)) m n ψ L T R S V1 V2)) ∧
      (¬ (fixV T ⊓ V1 ≤ fixV L) ∧
        I23LiteralCentralCore G V1 ∧ I23LiteralCentralCore G V2) ∧
      (1 < n → fixV L ≤ V1 ∧ (m ≠ 3 → V1 = commV R ∧ commV R ≤ fixV R))

@[expose] def I_1_7b : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut W)) (V : Subgroup W) (n : ℕ),
      L = quasithinGenFitting G → (∀ g ∈ G, ∀ v ∈ V, g v ∈ V) → G2NaturalDerived L V ⊥ n →
      commV G ≤ V → fixV G = ⊥ → IsFFModule G → V = ⊤

end I2bProps

end CFSG.ASVolI
