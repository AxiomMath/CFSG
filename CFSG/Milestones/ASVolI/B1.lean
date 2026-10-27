module

public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B1NaturalL2
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Open.QuasithinDefs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.Quasithin.Background.B1MoreTen
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B1MoreSeven
public import CFSG.Quasithin.Background.B1MoreChief
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.Background.B1More8
public import CFSG.Quasithin.Background.F918Z8g
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Solvable
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Background.B1MoreTwelve
public import CFSG.Quasithin.Background.G2
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Vocabulary

variable {V : Type*} [CommGroup V]

@[expose] def ActsTrivOnSection (g : MulAut V) (W U : Subgroup V) : Prop :=
  ∀ w ∈ W, g w * w⁻¹ ∈ U

@[expose] def autSec (X : Subgroup (MulAut V)) (W U : Subgroup V) :
    Subgroup (MulAut (↥W ⧸ U.subgroupOf W)) where
  carrier := {φ | ∃ g ∈ X, g ∈ stabSub W ∧ g ∈ stabSub U ∧
    ∀ w w' : ↥W, (w' : V) = g (w : V) →
      φ (QuotientGroup.mk w) = QuotientGroup.mk w'}
  one_mem' := by
    refine ⟨1, X.one_mem, (stabSub W).one_mem, (stabSub U).one_mem, ?_⟩
    intro w w' h
    have hw : w' = w := Subtype.ext h
    subst hw
    rfl
  mul_mem' := by
    rintro φ₁ φ₂ ⟨g₁, hg₁, hW₁, hU₁, h₁⟩ ⟨g₂, hg₂, hW₂, hU₂, h₂⟩
    refine ⟨g₁ * g₂, X.mul_mem hg₁ hg₂, (stabSub W).mul_mem hW₁ hW₂,
      (stabSub U).mul_mem hU₁ hU₂, ?_⟩
    intro w w' hw
    have hmem : g₂ (w : V) ∈ W := (mem_stabSub.1 hW₂ (w : V)).2 w.2
    have e₂ := h₂ w ⟨g₂ (w : V), hmem⟩ rfl
    have e₁ := h₁ ⟨g₂ (w : V), hmem⟩ w' (by simpa [MulAut.mul_apply] using hw)
    show φ₁ (φ₂ (QuotientGroup.mk w)) = _
    rw [e₂, e₁]
  inv_mem' := by
    rintro φ ⟨g, hg, hW, hU, h⟩
    refine ⟨g⁻¹, X.inv_mem hg, (stabSub W).inv_mem hW, (stabSub U).inv_mem hU, ?_⟩
    intro w w' hw
    have hw' : (w : V) = g (w' : V) := by
      rw [hw]; simp
    have e := h w' w hw'
    show φ.symm (QuotientGroup.mk w) = _
    rw [MulEquiv.symm_apply_eq]
    exact e.symm

end Vocabulary

section Groups

variable {M : Type*} [Group M]

@[expose] def IsIntDirProd {ι : Type*} (X : Subgroup M) (Gs : ι → Subgroup M) : Prop :=
  (∀ i j, i ≠ j → ∀ a ∈ Gs i, ∀ b ∈ Gs j, a * b = b * a) ∧ iSupIndep Gs ∧ (⨆ i, Gs i) = X

@[expose] def IsIntDirSum {ι : Type*} (X : Subgroup M) (Us : ι → Subgroup M) : Prop :=
  iSupIndep Us ∧ (⨆ i, Us i) = X

@[expose] def TwoChiefFactorsCentral (X : Subgroup M) : Prop :=
  ∀ N K : Subgroup M, N < K → K ≤ X → (N.subgroupOf X).Normal → (K.subgroupOf X).Normal →
    (∀ J : Subgroup M, N ≤ J → J ≤ K → (J.subgroupOf X).Normal → J = N ∨ J = K) →
    (∃ k : ℕ, N.relIndex K = 2 ^ k) → ⁅K, X⁆ ≤ N

@[expose] def fitOf (X : Subgroup M) : Subgroup M := CFSG.fittingSubgroupOf X

@[expose] def layerOf (X : Subgroup M) : Subgroup M := sSup {L | IsComponentOf L X}

@[expose] def oddCoreOf (X : Subgroup M) : Subgroup M := oddCoreIn X

@[expose] def conjSet (T K : Subgroup M) : Set (Subgroup M) :=
  {K' | ∃ t ∈ T, K' = K.map (MulAut.conj t).toMonoidHom}

@[expose] def conjClosureUnder (T K : Subgroup M) : Subgroup M := ⨆ K' ∈ conjSet T K, K'

end Groups

section FFNotation

variable {V : Type*} [CommGroup V]

@[expose] def offenderSet (G : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | IsFFStarOffender G A}

@[expose] def offenderStarSet (G : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | IsFFStarMin G A}

@[expose] def jStar (G : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ffJP (offenderStarSet G) G

@[expose] def fitJStar (G : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⁅fitOf G, jStar G⁆

end FFNotation

@[expose] def IsLieTypeQuasisimple (K : Type) [Group K] : Prop :=
  CFSG.Open.IsQuasisimple K ∧
    (CFSG.Blueprint.OddLieType (K ⧸ Subgroup.center K) ∨
      CFSG.Blueprint.EvenLieType (K ⧸ Subgroup.center K))

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement

@[expose] def B_1_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V),
      ((¬ ∃ A, IsA2 G A) ↔ Odd (Nat.card ↥G)) ∧ ((¬ ∃ A, IsA2 G A) → qOf G = ⊤)

section BurnsideB1a

open CFSG.Quasithin in
private theorem burnsideB1a_rk_iff {V : Type} [CommGroup V] [Finite V] (A : Subgroup (MulAut V)) :
    rk (⊥ : Subgroup (MulAut V)) + rk (fixV (⊥ : Subgroup (MulAut V))) ≤ rk A + rk (fixV A) ↔
      rkIdx (fixV A) ≤ rk A := by
  have h1 : rk (⊥ : Subgroup (MulAut V)) = 0 := rk_bot
  have h2 : rk (fixV (⊥ : Subgroup (MulAut V))) = rk V := by
    rw [CFSG.Quasithin.B1.fixV_bot, rk_top]
  have h3 : rk (fixV A) + rkIdx (fixV A) = rk V := rk_add_rkIdx (fixV A)
  rw [h1, h2]
  constructor <;> intro h <;> omega

open CFSG.Quasithin in
private theorem burnsideB1a_rkIdx_iff_rAV {V : Type} [CommGroup V] [Finite V]
    {X A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    rkIdx (fixV A) ≤ rk A ↔ rAV A ≤ 1 := by
  have hr : (0 : ℚ) < (rk A : ℚ) := by exact_mod_cast hA.rk_pos
  unfold rAV
  rw [div_le_one hr, Nat.cast_le]

open CFSG.Quasithin in
private theorem burnsideB1a_isA2_zpowers_involution {V : Type} [CommGroup V] {G : Subgroup
    (MulAut V)}
    {s : MulAut V} (hsG : s ∈ G) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    IsA2 G (Subgroup.zpowers s) :=
  ⟨Subgroup.zpowers_le.2 hsG, fun hbot => hs1 (by
    have hmem := Subgroup.mem_zpowers s
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem), CFSG.Quasithin.StabLat.isElemAbelian2_zpowers hs2⟩

end BurnsideB1a

open CFSG.Quasithin in
theorem as_B_1_1 : B_1_1 := by
  unfold B_1_1
  intro V _ _ _ G
  refine ⟨⟨fun h => ?_, fun hodd => ?_⟩, fun h => ?_⟩
  · by_contra hev
    have h2 : 2 ∣ Nat.card ↥G := by
      by_contra h2
      exact hev (Nat.odd_iff.2 (by omega))
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥G) 2 h2
    have hg2 : g ^ 2 = 1 := by
      rw [← hg]
      exact pow_orderOf_eq_one g
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hg
      norm_num at hg
    have hs2 : ((g : ↥G) : MulAut V) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, hg2, Subgroup.coe_one]
    have hs1 : ((g : ↥G) : MulAut V) ≠ 1 := fun h1 => hg1 (Subtype.ext h1)
    exact h ⟨Subgroup.zpowers ((g : ↥G) : MulAut V),
      burnsideB1a_isA2_zpowers_involution g.2 hs2 hs1⟩
  · rintro ⟨A, hA⟩
    have hdvd : Nat.card A ∣ Nat.card ↥G := Subgroup.card_dvd_of_le hA.1
    have hodd' : Odd (Nat.card A) := Odd.of_dvd_nat hodd hdvd
    have heven : Even (Nat.card A) := by
      rw [CFSG.Quasithin.B1.card_elemAbelian hA.2.2]
      exact Nat.even_pow.2 ⟨even_two, hA.rk_pos.ne'⟩
    exact (Nat.not_even_iff_odd.2 hodd') heven
  · unfold qOf
    exact kq_eq_top_iff.2 (fun ⟨A, hA, _⟩ => h ⟨A, hA⟩)

@[expose] def B_1_2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V),
      (∀ A, IsA2 G A →
        ((rk (⊥ : Subgroup (MulAut V)) + rk (fixV (⊥ : Subgroup (MulAut V))) ≤
            rk A + rk (fixV A)) ↔ rkIdx (fixV A) ≤ rk A) ∧
        (rkIdx (fixV A) ≤ rk A ↔ rAV A ≤ 1)) ∧
      (∀ A, IsA2 G A → FFLe G A A) ∧
      (∀ A B, FFLe G B A → FFLe G A B → A = B) ∧
      (∀ A B C, FFLe G C B → FFLe G B A → FFLe G C A)

open CFSG.Quasithin in
theorem as_B_1_2 : B_1_2 := by
  unfold B_1_2
  intro V _ _ _ G
  refine ⟨fun A hA => ⟨burnsideB1a_rk_iff A, burnsideB1a_rkIdx_iff_rAV hA⟩,
    fun A hA => ⟨hA, hA, le_rfl, rfl⟩,
    fun A B h1 h2 => (le_antisymm h1.2.2.1 h2.2.2.1).symm,
    fun A B C h1 h2 => ⟨h1.1, h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩⟩

@[expose] def B_1_4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V),
      (∀ A, IsFFStarOffender G A → rAV A ≤ 1) ∧
      (∀ A B, IsFFStarOffender G A → FFLe G B A → IsFFStarOffender G B) ∧
      ((∀ A, IsFFStarMin G A → IsQuadratic A) ∧
        (∀ A, IsFFStarOffender G A →
          (∀ B, IsFFStarOffender G B → B ≤ A → B = A) → IsQuadratic A)) ∧
      ((∀ A, IsA2 G A → rAV A ≤ 1 → ∃ B, B ≤ A ∧ IsFFStarOffender G B ∧ rAV B ≤ 1) ∧
        (∀ A, IsA2 G A → rAV A < 1 → ∃ B, B ≤ A ∧ IsFFStarOffender G B ∧ rAV B < 1)) ∧
      ((IsFFModule G ↔ ∃ A, IsFFStarOffender G A) ∧
        ((∃ A, IsFFStarOffender G A) ↔ qOf G ≤ 1)) ∧
      (¬ IsStrongFFModule G →
        {A | IsFFStarOffender G A} = {A | IsA2 G A ∧ rAV A = 1})

open CFSG.Quasithin in
theorem as_B_1_4 : B_1_4 := by
  unfold B_1_4
  intro V _ _ hV G
  exact ⟨fun A hA => B1_4_1 hV hA,
    fun A B hA hB => B1_4_2 hA hB,
    ⟨fun A hA => B1_4_3 hV hA, fun A hA hmin => B1_4_3_of_minimal hV hA hmin⟩,
    ⟨fun A hA hr => B1_4_4_le hV hA hr, fun A hA hr => B1_4_4_lt hV hA hr⟩,
    ⟨(B1_4_5 hV G).out 1 2, (B1_4_5 hV G).out 2 3⟩,
    fun hX => B1_4_6 hV hX⟩

@[expose] def B_1_5 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
      (∀ W : Subgroup V, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → commSub W A ≠ ⊥ →
        IsFFStarOffender (autSub G W) (autSub A W) ∧
        (IsFFStarMin G A →
          IsFFStarMin (autSub G W) (autSub A W) ∧
            (¬ IsStrongFFStarOffender (autSub G W) (autSub A W) →
              W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥)) ∧
        (IsFFStarMin G A → qOf (autSub G W) = 1 →
          IsFFStarMin (autSub G W) (autSub A W) ∧ W ⊔ fixV A = ⊤ ∧ A ⊓ centSub W = ⊥) ∧
        (rk (autSub A W) = rkIdx (fixV (autSub A W)) →
          A ⊓ centSub W = ⊥ ∨ IsFFStarOffender G (A ⊓ centSub W)) ∧
        (A ⊓ centSub W = ⊥ → qOf (autSub G W) = 1 → W ⊔ fixV A = ⊤ ∧ commV A ≤ W)) ∧
      (IsFFStarMin G A → ∀ X : Subgroup (MulAut V), X ≤ G → twoResidual X = X → ⁅X, A⁆ = X →
        TwoChiefFactorsCentral X →
        ∀ I ∈ IrrPlus X ⊤, ∀ a ∈ A, I.map a.toMonoidHom = I) ∧
      (∀ L : Subgroup (MulAut V), IsComponentOf L G → A ≤ Subgroup.normalizer (L : Set (MulAut V))) ∧
      (CFSG.Open.IsQuasisimple ↥(quasithinGenFitting G) → pCoreOf 2 G = ⊥ →
        ∀ W U : Subgroup V, U ≤ W → (∀ g ∈ G, g ∈ stabSub W ∧ g ∈ stabSub U) →
          (∃ l ∈ quasithinGenFitting G, ¬ ActsTrivOnSection l W U) →
          ((∀ a ∈ A, ActsTrivOnSection a W U → a = 1) ∧ Nonempty (↥A ≃* ↥(ChB.autSec A W U)) ∧
              ∃ B, IsFFStarOffender (ChB.autSec G W U) B ∧ B ≤ ChB.autSec A W U) ∧
          (qOf (ChB.autSec G W U) = 1 →
            IsFFStarOffender (ChB.autSec G W U) (ChB.autSec A W U) ∧
              commSub U (A ⊔ quasithinGenFitting G) = ⊥ ∧ commV (A ⊔ quasithinGenFitting G) ≤ W ∧
              W ⊔ fixV A = ⊤))

section BurnsideB1b

private theorem burnsideB1b_autSec_eq {V : Type*} [CommGroup V] (X : Subgroup (MulAut V))
    {W U : Subgroup V} (hUW : U ≤ W) :
    CFSG.ASVolI.ChB.autSec X W U = CFSG.Quasithin.autSec X W U := by
  ext φ
  constructor
  · rintro ⟨g, hgX, hgW, hgU, h⟩
    rw [CFSG.Quasithin.autSec, CFSG.Quasithin.mem_autQuot]
    have hK : CFSG.Quasithin.resHom W ⟨g, hgW⟩ ∈ CFSG.Quasithin.stabSub (U.subgroupOf W) := by
      rw [CFSG.Quasithin.mem_stabSub]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, CFSG.Quasithin.resHom_apply]
      exact CFSG.Quasithin.mem_stabSub.1 hgU x
    refine ⟨⟨CFSG.Quasithin.resHom W ⟨g, hgW⟩, hK⟩,
      CFSG.Quasithin.mem_autSub.2 ⟨⟨g, hgW⟩, hgX, rfl⟩, ?_⟩
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [CFSG.Quasithin.quotHom_mk]
      exact (h w ⟨g w, (CFSG.Quasithin.mem_stabSub.1 hgW w).2 w.2⟩ rfl).symm
  · intro hφ
    obtain ⟨g', hg', rfl⟩ := CFSG.Quasithin.mem_autQuot.1 hφ
    obtain ⟨g₁, hgX, hg₁⟩ := CFSG.Quasithin.mem_autSub.1 hg'
    have hK : ∀ x : W, CFSG.Quasithin.resHom W g₁ x ∈ U.subgroupOf W ↔ x ∈ U.subgroupOf W := by
      intro x
      have := CFSG.Quasithin.mem_stabSub.1 g'.2 x
      rw [← hg₁] at this
      exact this
    have hgU : (g₁ : MulAut V) ∈ CFSG.Quasithin.stabSub U := by
      rw [CFSG.Quasithin.mem_stabSub]
      intro v
      constructor
      · intro hv
        have hvW : v ∈ W := (CFSG.Quasithin.mem_stabSub.1 g₁.2 v).1 (hUW hv)
        have hmem := (hK ⟨v, hvW⟩).1
          (by rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.resHom_apply]; exact hv)
        exact Subgroup.mem_subgroupOf.1 hmem
      · intro hv
        have hvW : v ∈ W := hUW hv
        have hmem := (hK ⟨v, hvW⟩).2 (Subgroup.mem_subgroupOf.2 hv)
        rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.resHom_apply] at hmem
        exact hmem
    refine ⟨g₁, hgX, g₁.2, hgU, ?_⟩
    intro w w' hw
    rw [CFSG.Quasithin.quotHom_mk]
    congr 1
    apply Subtype.ext
    rw [← hg₁, CFSG.Quasithin.resHom_apply]
    exact hw.symm

private theorem burnsideB1b_commSub_eq_bot_iff {V : Type*} [CommGroup V] (U : Subgroup V)
    (Y : Subgroup (MulAut V)) :
    CFSG.Quasithin.commSub U Y = ⊥ ↔ Y ≤ CFSG.Quasithin.centSub U := by
  constructor
  · intro h g hg
    rw [CFSG.Quasithin.mem_centSub]
    intro u hu
    have hmem : g u * u⁻¹ ∈ CFSG.Quasithin.commSub U Y :=
      Subgroup.subset_closure ⟨g, hg, u, hu, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.1 hmem
  · intro h
    rw [eq_bot_iff]
    unfold CFSG.Quasithin.commSub
    refine (Subgroup.closure_le _).2 ?_
    rintro c ⟨g, hg, u, hu, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    exact mul_inv_eq_one.2 ((CFSG.Quasithin.mem_centSub.1 (h hg)) u hu)

private theorem burnsideB1b_commV_le_iff {V : Type*} [CommGroup V] (W : Subgroup V)
    (Y : Subgroup (MulAut V)) :
    CFSG.Quasithin.commV Y ≤ W ↔ Y ≤ CFSG.Quasithin.centQuot W := by
  constructor
  · intro h g hg
    rw [CFSG.Quasithin.mem_centQuot]
    intro v
    exact h (Subgroup.subset_closure ⟨g, hg, v, rfl⟩)
  · intro h
    unfold CFSG.Quasithin.commV
    refine (Subgroup.closure_le W).2 ?_
    rintro c ⟨x, hx, v, rfl⟩
    exact (CFSG.Quasithin.mem_centQuot.1 (h hx)) v

private theorem burnsideB1b_allTCF {M : Type*} [Group M] [Finite M] {X : Subgroup M}
    (h : CFSG.ASVolI.ChB.TwoChiefFactorsCentral X) :
    CFSG.Quasithin.AllTwoChiefFactorsCentral X := by
  intro A B hAB
  obtain ⟨hBA, hAX, hXA, hXB, hmin, hpow⟩ := hAB
  have hBX : B ≤ X := hBA.le.trans hAX
  obtain ⟨n, hn⟩ := CFSG.Quasithin.B6.exists_relIndex_eq_two_pow (hAX.trans hXB) hpow
  have hBn : (B.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBX).2 hXB
  have hAn : (A.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).2 hXA
  have hmin' : ∀ J : Subgroup M, B ≤ J → J ≤ A → (J.subgroupOf X).Normal → J = B ∨ J = A := by
    intro J hBJ hJA hJn
    by_contra hne
    push_neg at hne
    have hJX : J ≤ X := hJA.trans hAX
    exact hmin J (lt_of_le_of_ne hBJ (Ne.symm hne.1)) (lt_of_le_of_ne hJA hne.2)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hJX).1 hJn)
  exact h B A hBA hAX hBn hAn hmin' ⟨n, hn⟩

private theorem burnsideB1b_twoResidual_eq {M : Type*} [Group M] [Finite M] (X : Subgroup M) :
    CFSG.Quasithin.twoResidual X = CFSG.Quasithin.oTwoUpper X :=
  le_antisymm
    (CFSG.Quasithin.twoResidual_le_of_isTwoQuotient (CFSG.Quasithin.oTwoUpper_le X)
      (CFSG.Quasithin.le_normalizer_oTwoUpper X)
      (fun y hy => CFSG.Quasithin.exists_pow_mem_oTwoUpper X hy))
    (CFSG.Quasithin.oTwoUpper_le_of_pow_mem (CFSG.Quasithin.twoResidual_isTwoQuotient X))

end BurnsideB1b

theorem as_B_1_5 : B_1_5 := by
  intro V _ _ hV G A hA
  refine ⟨fun W hW hWA => ?_, ?_, ?_, ?_⟩
  · exact ⟨CFSG.Quasithin.B1_5_1 hA hW hWA,
      fun hmin => CFSG.Quasithin.B1_5_2 hV hmin hW hWA,
      fun hmin hq => CFSG.Quasithin.B1_5_5 hV hmin hW hWA hq,
      fun hm => CFSG.Quasithin.B1_5_6 hV hA hW hWA hm,
      fun hf hq => CFSG.Quasithin.B1_5_7 hV hA hW hWA hf hq⟩
  · intro hmin X _ htr hXA hcf I hI a ha
    exact CFSG.Quasithin.B1_5_3 hV hmin ((burnsideB1b_twoResidual_eq X).symm.trans htr) hXA
      (burnsideB1b_allTCF hcf) a ha I hI
  · intro L hL
    exact CFSG.Quasithin.B15P4.asB15Part4 V hV G A hA L hL
  · intro hQ hO2 W U hUW hGWU hact
    have hGW : G ≤ CFSG.Quasithin.stabSub W := fun g hg => (hGWU g hg).1
    have hGU : G ≤ CFSG.Quasithin.stabSub U := fun g hg => (hGWU g hg).2
    have hS : ¬ CFSG.Quasithin.commSub W (CFSG.Open.quasithinGenFitting G) ≤ U := by
      intro hle
      obtain ⟨l, hl, hnot⟩ := hact
      exact hnot fun w hw => hle (Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩)
    obtain ⟨hfaith, hex, hq⟩ :=
      CFSG.Quasithin.B1_5_8 hV hA hUW hGW hGU (CFSG.Quasithin.B1Red.isQuasisimple_of_open hQ)
        hO2 hS
    have eG := burnsideB1b_autSec_eq (V := V) G hUW
    have eA := burnsideB1b_autSec_eq (V := V) A hUW
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro a ha hact_a
      have hmem : a ∈ A ⊓ CFSG.Quasithin.centSec W U := by
        refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
        rw [CFSG.Quasithin.mem_centSec]
        exact ⟨hGW (hA.1 ha), hact_a⟩
      rw [hfaith] at hmem
      exact Subgroup.mem_bot.1 hmem
    · rw [eA]
      exact ⟨CFSG.Quasithin.d321f_autSecEquiv (fun a ha => hGW (hA.1 ha))
        (fun a ha => hGU (hA.1 ha)) hfaith⟩
    · obtain ⟨B, hBA, hB⟩ := hex
      rw [eA, eG]
      exact ⟨B, hB, hBA⟩
    · intro hq1
      rw [eG] at hq1
      obtain ⟨hPA, hsub, htop⟩ := hq hq1
      rw [eG, eA]
      refine ⟨hPA, ?_, ?_, htop⟩
      · exact (burnsideB1b_commSub_eq_bot_iff U _).2 (le_inf_iff.1 hsub).1
      · exact (burnsideB1b_commV_le_iff W _).2 (le_inf_iff.1 hsub).2

@[expose] def B_1_7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), IsFFModule G → IsStableFF G {A | IsFFStarMin G A}

open CFSG.Quasithin in
theorem as_B_1_7 : B_1_7 := by
  unfold B_1_7
  intro V _ _ hV G hG
  exact B1_7 hV hG

@[expose] def B_1_8 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), pCoreOf 2 G = ⊥ → IsFFModule G → Group.IsSolvable ↥G →
      ∃ (s : ℕ) (Gs : Fin s → Subgroup (MulAut V)),
        IsIntDirProd (ffJ G) Gs ∧
        IsIntDirSum (commV (ffJ G)) (fun i => commV (Gs i)) ∧
        (∀ i, Nonempty (↥(Gs i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
          ActsAsNaturalL2 (Gs i) (commV (Gs i))) ∧
        (qOf G = 1 ∧ ∀ A, ¬ IsStrongFFStarOffender G A) ∧
        (∀ A, IsFFStarOffender G A ↔ ∃ As : Fin s → Subgroup (MulAut V),
          (∀ i, As i = ⊥ ∨ IsSylowTwoOf (As i) (Gs i)) ∧ (∃ j, As j ≠ ⊥) ∧ A = ⨆ i, As i) ∧
        (∀ P : Set (Subgroup (MulAut V)), IsStableFF G P →
          (∃ I : Finset (Fin s), ffJP P G = ⨆ i ∈ I, Gs i) ∧
          (P ∩ offenderStarSet G = {A | A ∈ offenderStarSet G ∧ A ≤ ffJP P G}))

section BurnsideB1c

private theorem burnsideB1c_biSup_fin {α ι : Type*} [CompleteLattice α] {n : ℕ} (𝓗 : Finset ι)
    (e : {x // x ∈ 𝓗} ≃ Fin n) (F : ι → α) :
    (⨆ H ∈ 𝓗, F H) = ⨆ i : Fin n, F (e.symm i).1 := by
  calc (⨆ H ∈ 𝓗, F H) = ⨆ x : {x // x ∈ 𝓗}, F x.1 := iSup_subtype'
    _ = ⨆ i : Fin n, F (e.symm i).1 :=
      (Equiv.iSup_comp (g := fun x : {x // x ∈ 𝓗} => F x.1) e.symm).symm

private theorem burnsideB1c_biSup_subset {α ι : Type*} [CompleteLattice α] {n : ℕ} (𝓗 I : Finset ι)
    (hI : I ⊆ 𝓗) (e : {x // x ∈ 𝓗} ≃ Fin n) (J : Finset (Fin n))
    (hJ : ∀ i, i ∈ J ↔ (e.symm i).1 ∈ I) (F : ι → α) :
    (⨆ H ∈ I, F H) = ⨆ i ∈ J, F (e.symm i).1 := by
  apply le_antisymm
  · refine iSup₂_le fun H hH => ?_
    have hH𝓗 : H ∈ 𝓗 := hI hH
    have hmem : e ⟨H, hH𝓗⟩ ∈ J := by
      rw [hJ]
      simpa using hH
    refine le_iSup₂_of_le (f := fun i (_ : i ∈ J) => F (e.symm i).1) (e ⟨H, hH𝓗⟩) hmem ?_
    simp
  · refine iSup₂_le fun i hi => ?_
    have hi' := (hJ i).1 hi
    exact le_iSup₂_of_le (f := fun H (_ : H ∈ I) => F H) (e.symm i).1 hi' le_rfl

private theorem burnsideB1c_iSupIndep_finset {α ι : Type*} [CompleteLattice α] (𝓗 : Finset ι)
    (f : ι → α) (h : ∀ H ∈ 𝓗, f H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), f H' = ⊥) :
    iSupIndep (fun x : {x // x ∈ 𝓗} => f x.1) := by
  intro x
  have hle : (⨆ j : {x // x ∈ 𝓗}, ⨆ (_ : j ≠ x), f j.1) ≤
      ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ x.1), f H' := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_iSup₂_of_le (f := fun H' (_ : H' ∈ 𝓗) => ⨆ (_ : H' ≠ x.1), f H') j.1 j.2
      (le_iSup (fun _ : j.1 ≠ x.1 => f j.1) (fun e => hj (Subtype.ext e)))
  exact Disjoint.mono_right hle (disjoint_iff.mpr (h x.1 x.2))



private theorem burnsideB1c_conjClosure_eq {V : Type*} [CommGroup V] (T K : Subgroup (MulAut V)) :
    CFSG.ASVolI.ChB.conjClosureUnder T K = CFSG.Quasithin.conjClosure K T := by
  unfold CFSG.ASVolI.ChB.conjClosureUnder CFSG.Quasithin.conjClosure
  apply le_antisymm
  · refine iSup₂_le fun K' hK' => ?_
    obtain ⟨t, ht, rfl⟩ := hK'
    rw [Subgroup.map_le_iff_le_comap]
    intro z hz
    rw [Subgroup.mem_comap]
    exact Subgroup.subset_closure ⟨t, ht, z, hz, rfl⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨h, hh, z, hz, rfl⟩
    have hle : K.map (MulAut.conj h).toMonoidHom ≤ ⨆ K' ∈ CFSG.ASVolI.ChB.conjSet T K, K' :=
      le_iSup₂ (f := fun (K' : Subgroup (MulAut V)) (_ : K' ∈ CFSG.ASVolI.ChB.conjSet T K) => K')
        _ ⟨h, hh, rfl⟩
    exact hle (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)

private theorem burnsideB1c_idp_comp {ι ι' Γ : Type*} [Group Γ] (F : ι → Subgroup Γ) (K :
    Subgroup Γ)
    (e : ι' ≃ ι) (h : CFSG.Quasithin.EmptyFaithfulMultiple.IsInnerDirectProduct F K) :
    CFSG.Quasithin.EmptyFaithfulMultiple.IsInnerDirectProduct (fun j => F (e j)) K :=
  ⟨fun i j hij a ha b hb => h.1 (e i) (e j) (fun h' => hij (e.injective h')) a ha b hb,
    h.2.1.comp e.injective, (Equiv.iSup_comp e).trans h.2.2⟩

private theorem burnsideB1c_idp_map {ι A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (F : ι → Subgroup A) (K : Subgroup A)
    (h : CFSG.Quasithin.EmptyFaithfulMultiple.IsInnerDirectProduct F K) :
    CFSG.Quasithin.EmptyFaithfulMultiple.IsInnerDirectProduct
      (fun i => (F i).map φ.toMonoidHom) (K.map φ.toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, h.1 i j hij a' ha' b' hb']
  · intro i
    dsimp only
    have hS : (⨆ j, ⨆ (_ : j ≠ i), (F j).map φ.toMonoidHom) =
        (⨆ j, ⨆ (_ : j ≠ i), F j).map φ.toMonoidHom := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun j => ?_
      rw [Subgroup.map_iSup]
    rw [hS, disjoint_iff, ← Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective,
      disjoint_iff.mp (h.2.1 i), Subgroup.map_bot]
  · dsimp only
    rw [← Subgroup.map_iSup, h.2.2]

private theorem burnsideB1c_relPPrime_eq_oddCoreOfSub {Γ : Type*} [Group Γ] (H : Subgroup Γ) :
    CFSG.Open.relPPrimeCore 2 H = CFSG.Quasithin.EmptyFaithfulMultiple.oddCoreOfSub H := by
  unfold CFSG.Quasithin.EmptyFaithfulMultiple.oddCoreOfSub
  apply le_antisymm
  · apply sSup_le
    rintro N ⟨hNH, hN, hcop⟩
    have hcard : Nat.card ↥(N.subgroupOf H) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
    have hodd : Odd (Nat.card ↥(N.subgroupOf H)) := by
      rw [hcard]
      exact Nat.coprime_two_left.mp hcop
    have hle : N.subgroupOf H ≤ CFSG.oddCore ↥H := le_sSup ⟨hN, hodd⟩
    calc N = (N.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH).symm
      _ ≤ (CFSG.oddCore ↥H).map H.subtype := Subgroup.map_mono hle
  · rw [Subgroup.map_le_iff_le_comap]
    apply sSup_le
    rintro N ⟨hN, hodd⟩
    rw [← Subgroup.map_le_iff_le_comap]
    apply le_sSup
    refine ⟨Subgroup.map_subtype_le N, ?_, ?_⟩
    · rw [CFSG.Quasithin.map_subtype_subgroupOf']
      exact hN
    · have hc : Nat.card ↥(N.map H.subtype) = Nat.card ↥N :=
        Nat.card_congr
          (Subgroup.equivMapOfInjective N H.subtype (Subgroup.subtype_injective H)).symm.toEquiv
      rw [hc]
      exact Nat.coprime_two_left.mpr hodd

private theorem burnsideB1c_relPPrime_map_le {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (H : Subgroup A) (p : ℕ) :
    (CFSG.Open.relPPrimeCore p H).map f ≤ CFSG.Open.relPPrimeCore p (H.map f) := by
  rw [Subgroup.map_le_iff_le_comap]
  apply sSup_le
  rintro N ⟨hNH, hN, hcop⟩
  rw [← Subgroup.map_le_iff_le_comap]
  apply le_sSup
  refine ⟨Subgroup.map_mono hNH, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hNH)]
    rintro _ _ ⟨n, hn, rfl⟩ ⟨k, hk, rfl⟩
    have hnorm := (Subgroup.normal_subgroupOf_iff hNH).mp hN n k hn hk
    exact ⟨k * n * k⁻¹, hnorm, by simp⟩
  · have hc : Nat.card ↥(N.map f) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.equivMapOfInjective N f hf).symm.toEquiv
    rw [hc]
    exact hcop

private theorem burnsideB1c_map_symm_map {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (H : Subgroup A) : (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have hc : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id A := by
    ext x
    simp
  rw [hc, Subgroup.map_id]

private theorem burnsideB1c_map_map_symm {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (X : Subgroup B) : (X.map φ.symm.toMonoidHom).map φ.toMonoidHom = X := by
  rw [Subgroup.map_map]
  have hc : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id B := by
    ext x
    simp
  rw [hc, Subgroup.map_id]

private theorem burnsideB1c_relPPrime_map_eq {A B : Type*} [Group A] [Group B] (φ : A ≃* B)
    (H : Subgroup A) (p : ℕ) :
    CFSG.Open.relPPrimeCore p (H.map φ.toMonoidHom) =
      (CFSG.Open.relPPrimeCore p H).map φ.toMonoidHom := by
  apply le_antisymm
  · have h := burnsideB1c_relPPrime_map_le φ.symm.toMonoidHom φ.symm.injective
      (H.map φ.toMonoidHom) p
    rw [burnsideB1c_map_symm_map φ H] at h
    calc CFSG.Open.relPPrimeCore p (H.map φ.toMonoidHom)
        = ((CFSG.Open.relPPrimeCore p (H.map φ.toMonoidHom)).map φ.symm.toMonoidHom).map
            φ.toMonoidHom := (burnsideB1c_map_map_symm φ _).symm
      _ ≤ (CFSG.Open.relPPrimeCore p H).map φ.toMonoidHom := Subgroup.map_mono h
  · exact burnsideB1c_relPPrime_map_le φ.toMonoidHom φ.injective H p

end BurnsideB1c

theorem as_B_1_8 : B_1_8 := by
  classical
  intro V _ _ hV G hO2 hFF hsolv
  obtain ⟨𝓗, -, hJ, hcomm, hind, hcV, hcVind, hNat, hqs, hoff, hstab⟩ :=
    CFSG.Quasithin.B1_8 hV hsolv (CFSG.Quasithin.normal_two_subgroups_trivial_of_pCoreOf_eq_bot hO2)
      hFF
  have e : {x // x ∈ 𝓗} ≃ Fin 𝓗.card := 𝓗.equivFin
  have hmemG : ∀ i, (e.symm i).1 ∈ 𝓗 := fun i => (e.symm i).2
  have hinjG : ∀ i j, (e.symm i).1 = (e.symm j).1 → i = j := fun i j h =>
    e.symm.injective (Subtype.ext h)
  refine ⟨𝓗.card, fun i => (e.symm i).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun i j hij a ha b hb =>
      hcomm _ (hmemG i) _ (hmemG j) (fun h => hij (hinjG i j h)) a ha b hb, ?_, ?_⟩
    · exact (burnsideB1c_iSupIndep_finset 𝓗 (fun H => H) hind).comp e.symm.injective
    · rw [hJ]
      exact (burnsideB1c_biSup_fin 𝓗 e (fun H => H)).symm
  · refine ⟨?_, ?_⟩
    · exact (burnsideB1c_iSupIndep_finset 𝓗 (fun H => CFSG.Quasithin.commV H) hcVind).comp
        e.symm.injective
    · rw [hcV]
      exact (burnsideB1c_biSup_fin 𝓗 e (fun H => CFSG.Quasithin.commV H)).symm
  · intro i
    obtain ⟨φ, -⟩ := hNat _ (hmemG i)
    exact ⟨⟨φ⟩, hNat _ (hmemG i)⟩
  · exact hqs
  · intro A
    rw [hoff A]
    constructor
    · rintro ⟨a, ha1, ⟨H, hH, haH⟩, hA⟩
      refine ⟨fun i => a (e.symm i).1, fun i => ha1 _ (hmemG i), ?_, ?_⟩
      · refine ⟨e ⟨H, hH⟩, ?_⟩
        simpa using haH
      · rw [hA, burnsideB1c_biSup_fin 𝓗 e a]
    · rintro ⟨As, hAs1, ⟨j, hj⟩, hA⟩
      let a : Subgroup (MulAut V) → Subgroup (MulAut V) :=
        fun H => if h : H ∈ 𝓗 then As (e ⟨H, h⟩) else ⊥
      have ha_gs : ∀ i, a (e.symm i).1 = As i := by
        intro i
        simp only [a, dif_pos (e.symm i).2, Subtype.coe_eta, Equiv.apply_symm_apply]
      refine ⟨a, ?_, ⟨(e.symm j).1, (e.symm j).2, ?_⟩, ?_⟩
      · intro H hH
        have hdef : a H = As (e ⟨H, hH⟩) := dif_pos hH
        rw [hdef]
        have h2 := hAs1 (e ⟨H, hH⟩)
        simpa using h2
      · rw [ha_gs]
        exact hj
      · rw [burnsideB1c_biSup_fin 𝓗 e a]
        simp only [ha_gs]
        exact hA
  · intro P hP
    obtain ⟨I, hIsub, hIJ, -, hmin⟩ := hstab P hP
    let J : Finset (Fin 𝓗.card) := Finset.univ.filter (fun i => (e.symm i).1 ∈ I)
    have hJI : ∀ i, i ∈ J ↔ (e.symm i).1 ∈ I := fun i => by simp [J]
    refine ⟨⟨J, ?_⟩, ?_⟩
    · rw [hIJ]
      exact burnsideB1c_biSup_subset 𝓗 I hIsub e J hJI (fun H => H)
    · ext A
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hAP, hAmin⟩
        exact ⟨hAmin, (hmin A hAmin).1 hAP⟩
      · rintro ⟨hAmin, hAle⟩
        exact ⟨(hmin A hAmin).2 hAle, hAmin⟩

@[expose] def B_1_9 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), pCoreOf 2 G = ⊥ → fitJStar G ≠ ⊥ →
      ∃ (s : ℕ) (Gs : Fin s → Subgroup (MulAut V)),
        IsIntDirProd (ffJ G)
          (fun o : Option (Fin s) => o.elim
            (ffJP (offenderSet G) (G ⊓ Subgroup.centralizer (fitJStar G : Set (MulAut V)))) Gs) ∧
        (∀ i, Nonempty (↥(Gs i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) ∧
        IsIntDirProd (fitJStar G) (fun i => oddCoreOf (Gs i)) ∧
        (∀ i, Nonempty (↥(oddCoreOf (Gs i)) ≃* Multiplicative (ZMod 3))) ∧
        IsIntDirProd (fitOf G)
          ![fitJStar G, fitOf G ⊓ Subgroup.centralizer (jStar G : Set (MulAut V))] ∧
        IsIntDirSum (commV (fitJStar G)) (fun i => commV (oddCoreOf (Gs i))) ∧
        (∀ i, commV (oddCoreOf (Gs i)) = commV (Gs i) ∧ Nat.card ↥(commV (Gs i)) = 2 ^ 2) ∧
        {A | A ∈ offenderStarSet G ∧ ⁅fitOf G, A⁆ ≠ ⊥} = {A | ∃ i, IsSylowTwoOf A (Gs i)} ∧
        (∀ A ∈ offenderStarSet G, ∀ K : Subgroup (MulAut V), K ≤ G → ⁅K, A⁆ = K →
          K ≤ jStar G ⊓ Subgroup.centralizer (fitOf G : Set (MulAut V)))

theorem as_B_1_9 : B_1_9 := by
  intro V _ _ hV G hO2 hfit
  obtain ⟨s, H, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    CFSG.Quasithin.EmptyFaithfulMultiple.inputB19_holds V hV G hO2 hfit
  have hZ : Nat.card (Multiplicative (ZMod 3)) = 3 :=
    (Nat.card_congr Multiplicative.ofAdd).symm.trans
      (Nat.card_eq_fintype_card.trans (ZMod.card 3))
  refine ⟨s, H, h2, fun i => (h1 i).2, h3, fun i => ⟨mulEquivOfPrimeCardEq (h4 i) hZ⟩, h5,
    ⟨h7, h8⟩, fun i => ⟨(h6 i).1, (h6 i).2.trans (by norm_num)⟩, ?_, ?_⟩
  · ext A
    exact h9 A
  · exact fun A hA K hK hKA => h10 A K hA hK hKA

@[expose] def B_1_10 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), pCoreOf 2 G = ⊥ →
      ∀ K : Subgroup (MulAut V), K ≤ G → (∃ A, IsFFStarOffender G A ∧ ⁅K, A⁆ = K) →
        (CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) →
          K ≤ ffJ G ⊓ Subgroup.centralizer (fitOf G : Set (MulAut V))

open CFSG.Quasithin in
theorem as_B_1_10 : B_1_10 := by
  unfold B_1_10
  intro V _ _ hV G hO2 K hKG hAK hK
  obtain ⟨A, hA, hKA⟩ := hAK
  exact B1_10 hV hO2 hKG hA hKA (hK.imp B1Red.isQuasisimple_of_open id)

@[expose] def B_1_11 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), IsFFStarOffender G A → L ≤ G →
      CFSG.Open.IsQuasisimple ↥L → ⁅L, A⁆ = L →
        ∃ (H : Subgroup (MulAut V)) (I : Subgroup V), L ≤ H ∧ H ≤ G ∧ I ∈ IrrPlus L ⊤ ∧
          (∀ h ∈ H, h ∈ stabSub I) ∧
          (∀ h ∈ H, h ∈ stabSub (fixV L ⊓ I)) ∧
          IsFFModule (ChB.autSec H I (fixV L ⊓ I)) ∧
          (∀ h ∈ H, ActsTrivOnSection h I (fixV L ⊓ I) → ∀ l ∈ L, h * l = l * h) ∧
          XMod.IsIrrSec ↥L (fixV L ⊓ I) I

theorem as_B_1_11 : B_1_11 := by
  intro V _ _ hV G L A hA hLG hLq hLA
  obtain ⟨H, I, hLH, hHG, hI, hHst, hFF, hcent, -⟩ :=
    CFSG.Quasithin.B1_11 hV hA hLG (CFSG.Quasithin.B1Red.isQuasisimple_of_open hLq) hLA
  obtain ⟨hinv, hcomm, hlt, hmin⟩ := CFSG.Quasithin.mem_irrPlus_top_iff.1 hI
  have hc : CFSG.Quasithin.fixV L ⊓ I = I ⊓ CFSG.Quasithin.fixV L := inf_comm _ _
  have hLU : L ≤ CFSG.Quasithin.stabSub (CFSG.Quasithin.fixV L ⊓ I) := by
    intro l hl
    rw [CFSG.Quasithin.mem_stabSub]
    intro u
    have hlinv : l⁻¹ ∈ L := L.inv_mem hl
    have hfix : l u ∈ CFSG.Quasithin.fixV L ↔ u ∈ CFSG.Quasithin.fixV L := by
      constructor
      · intro hu
        have := CFSG.Quasithin.isInv_fixV L l⁻¹ hlinv (l u) hu
        simpa using this
      · intro hu
        exact CFSG.Quasithin.isInv_fixV L l hl u hu
    have hIi : l u ∈ I ↔ u ∈ I := by
      constructor
      · intro hu
        have := hinv l⁻¹ hlinv (l u) hu
        simpa using this
      · intro hu
        exact hinv l hl u hu
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hfix, hIi]
  refine ⟨H ⊓ CFSG.Quasithin.stabSub (CFSG.Quasithin.fixV L ⊓ I), I, le_inf hLH hLU,
    inf_le_left.trans hHG, hI, fun h hh => hHst (Subgroup.mem_inf.1 hh).1,
    fun h hh => (Subgroup.mem_inf.1 hh).2, ?_, ?_, ?_⟩
  ·
    have e1 : CFSG.ASVolI.ChB.autSec (H ⊓ CFSG.Quasithin.stabSub (CFSG.Quasithin.fixV L ⊓ I)) I
        (CFSG.Quasithin.fixV L ⊓ I) = CFSG.ASVolI.ChB.autSec H I (CFSG.Quasithin.fixV L ⊓ I) := by
      ext φ
      constructor
      · rintro ⟨g, hg, hgI, hgU, h⟩
        exact ⟨g, (Subgroup.mem_inf.1 hg).1, hgI, hgU, h⟩
      · rintro ⟨g, hg, hgI, hgU, h⟩
        exact ⟨g, Subgroup.mem_inf.2 ⟨hg, hgU⟩, hgI, hgU, h⟩
    rw [e1, burnsideB1b_autSec_eq (W := I) (U := CFSG.Quasithin.fixV L ⊓ I) H inf_le_right, hc]
    exact hFF
  ·
    intro h hh hact l hl
    have hmem : h ∈ H ⊓ CFSG.Quasithin.centSec I (I ⊓ CFSG.Quasithin.fixV L) := by
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hh).1, ?_⟩
      rw [CFSG.Quasithin.mem_centSec]
      refine ⟨hHst (Subgroup.mem_inf.1 hh).1, fun w hw => ?_⟩
      have := hact w hw
      rw [hc] at this
      exact this
    exact (Subgroup.mem_centralizer_iff.1 (hcent hmem) l hl).symm
  ·
    unfold CFSG.Quasithin.XMod.IsIrrSec
    refine ⟨?_, fun J hJ hCJ hJI => ?_⟩
    · rw [hc]; exact hlt
    · rw [CFSG.Quasithin.isInv_iff] at hJ
      rw [hc] at hCJ
      rcases hmin J hJ hCJ hJI with h | h
      · exact Or.inl (h.trans hc.symm)
      · exact Or.inr h

@[expose] def B_1_12 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T K : Subgroup (MulAut V), IsSylowTwoOf T G → K ≤ G →
      Nonempty (↥K ≃* Multiplicative (ZMod 3)) → ⁅K, ffJ T⁆ = K → IsSubnormal K (T ⊔ K) →
      ∃ (n : ℕ) (Ks : Fin n → Subgroup (MulAut V)),
        Set.range Ks = conjSet T K ∧ IsIntDirProd (conjClosureUnder T K) Ks ∧
        ∃ Ms : Fin n → Subgroup (↥(ffJ T ⊔ conjClosureUnder T K) ⧸
            pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)),
          IsIntDirProd ⊤ Ms ∧
          (∀ i, ((Ks i).subgroupOf (ffJ T ⊔ conjClosureUnder T K)).map
              (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K))) =
            relPPrimeCore 2 (Ms i)) ∧
          (∀ i, Nonempty (↥(Ms i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) ∧
          (∀ t ∈ T, ∀ i, ∃ j,
            (((Ms i).comap (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)))).map
              (ffJ T ⊔ conjClosureUnder T K).subtype).map (MulAut.conj t).toMonoidHom =
            ((Ms j).comap (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)))).map
              (ffJ T ⊔ conjClosureUnder T K).subtype) ∧
          (∀ i j, ∃ t ∈ T,
            (((Ms i).comap (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)))).map
              (ffJ T ⊔ conjClosureUnder T K).subtype).map (MulAut.conj t).toMonoidHom =
            ((Ms j).comap (QuotientGroup.mk' (pCore 2 ↥(ffJ T ⊔ conjClosureUnder T K)))).map
              (ffJ T ⊔ conjClosureUnder T K).subtype)

theorem as_B_1_12 : B_1_12 := by
  classical
  intro V _ _ hV G T K hT _hKG hKiso hKJ hsub
  haveI : Finite (MulAut V) := inferInstance
  obtain ⟨ψ⟩ := hKiso
  have hZ : Nat.card (Multiplicative (ZMod 3)) = 3 :=
    (Nat.card_congr Multiplicative.ofAdd).symm.trans
      (Nat.card_eq_fintype_card.trans (ZMod.card 3))
  have hK3 : Nat.card ↥K = 3 := (Nat.card_congr ψ.toEquiv).trans hZ
  obtain ⟨h1, h2, h3, h4, Mb, h5, h6, h7, h8⟩ :=
    CFSG.Quasithin.B1_12 hV hT hK3 hKJ hsub
  have key : ∀ X : Subgroup (MulAut V), X = CFSG.Quasithin.conjClosure K T →
      ∃ (n : ℕ) (Ks : Fin n → Subgroup (MulAut V)),
        Set.range Ks = CFSG.ASVolI.ChB.conjSet T K ∧
        CFSG.ASVolI.ChB.IsIntDirProd X Ks ∧
        ∃ Ms : Fin n → Subgroup (↥(CFSG.Quasithin.ffJ T ⊔ X) ⧸
            CFSG.pCore 2 ↥(CFSG.Quasithin.ffJ T ⊔ X)),
          CFSG.ASVolI.ChB.IsIntDirProd ⊤ Ms ∧
          (∀ i, ((Ks i).subgroupOf (CFSG.Quasithin.ffJ T ⊔ X)).map
              (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.ffJ T ⊔ X))) =
                CFSG.Open.relPPrimeCore 2 (Ms i)) ∧
          (∀ i, Nonempty (↥(Ms i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) ∧
          (∀ t ∈ T, ∀ i, ∃ j,
            (((Ms i).comap (QuotientGroup.mk'
                (CFSG.pCore 2 ↥(CFSG.Quasithin.ffJ T ⊔ X)))).map
                  (CFSG.Quasithin.ffJ T ⊔ X).subtype).map (MulAut.conj t).toMonoidHom =
              ((Ms j).comap (QuotientGroup.mk'
                (CFSG.pCore 2 ↥(CFSG.Quasithin.ffJ T ⊔ X)))).map
                  (CFSG.Quasithin.ffJ T ⊔ X).subtype) ∧
          (∀ i j, ∃ t ∈ T,
            (((Ms i).comap (QuotientGroup.mk'
                (CFSG.pCore 2 ↥(CFSG.Quasithin.ffJ T ⊔ X)))).map
                  (CFSG.Quasithin.ffJ T ⊔ X).subtype).map (MulAut.conj t).toMonoidHom =
              ((Ms j).comap (QuotientGroup.mk'
                (CFSG.pCore 2 ↥(CFSG.Quasithin.ffJ T ⊔ X)))).map
                  (CFSG.Quasithin.ffJ T ⊔ X).subtype) := by
    intro X hX
    subst hX
    rw [show CFSG.Quasithin.ffJ T ⊔ CFSG.Quasithin.conjClosure K T =
      CFSG.Quasithin.twelveM T K from rfl]
    have hpc : (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.twelveM T K)).subgroupOf
        (CFSG.Quasithin.twelveM T K) = CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K) := by
      unfold CFSG.Open.pCoreOf
      exact CFSG.Quasithin.map_subtype_subgroupOf' _
    let φ := QuotientGroup.quotientMulEquivOfEq hpc
    have hφ : ∀ x : ↥(CFSG.Quasithin.twelveM T K),
        φ (CFSG.Quasithin.secMk (CFSG.Quasithin.twelveM T K)
            (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.twelveM T K)) x) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K)) x :=
      fun x => rfl
    have hcomp : φ.toMonoidHom.comp (CFSG.Quasithin.secMk (CFSG.Quasithin.twelveM T K)
        (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.twelveM T K))) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K)) :=
      MonoidHom.ext hφ
    have hcomap : ∀ B : Subgroup (CFSG.Quasithin.SecQuot (CFSG.Quasithin.twelveM T K)
          (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.twelveM T K))),
        (B.map φ.toMonoidHom).comap
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K))) =
          B.comap (CFSG.Quasithin.secMk (CFSG.Quasithin.twelveM T K)
            (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.twelveM T K))) := by
      intro B
      ext x
      rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_map_equiv, ← hφ x,
        MulEquiv.symm_apply_apply]
    have perm : ∀ t ∈ T, ∀ i j : CFSG.Quasithin.conjSetUnder T K,
        j.1 = i.1.map (MulAut.conj t).toMonoidHom →
        ((((Mb i).comap (CFSG.Quasithin.secMk (CFSG.Quasithin.twelveM T K)
            (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.twelveM T K)))).map
              (CFSG.Quasithin.twelveM T K).subtype).map (MulAut.conj t).toMonoidHom) =
          ((Mb j).comap (CFSG.Quasithin.secMk (CFSG.Quasithin.twelveM T K)
            (CFSG.Open.pCoreOf 2 (CFSG.Quasithin.twelveM T K)))).map
              (CFSG.Quasithin.twelveM T K).subtype := by
      intro t ht i j hij
      ext m
      constructor
      · rintro ⟨m', ⟨x, hx, rfl⟩, rfl⟩
        have hxt : t * (x : MulAut V) * t⁻¹ ∈ CFSG.Quasithin.twelveM T K :=
          h2 t ht (x : MulAut V) x.2
        refine ⟨⟨t * (x : MulAut V) * t⁻¹, hxt⟩, ?_, rfl⟩
        exact (h8 t ht i j hij x ⟨t * (x : MulAut V) * t⁻¹, hxt⟩ rfl).mp hx
      · rintro ⟨y, hy, rfl⟩
        have hyM : t⁻¹ * (y : MulAut V) * t ∈ CFSG.Quasithin.twelveM T K := by
          simpa using h2 t⁻¹ (T.inv_mem ht) (y : MulAut V) y.2
        have hyx : (y : MulAut V) = t * (t⁻¹ * (y : MulAut V) * t) * t⁻¹ := by group
        have hx := (h8 t ht i j hij ⟨t⁻¹ * (y : MulAut V) * t, hyM⟩ y hyx).mpr hy
        exact ⟨(CFSG.Quasithin.twelveM T K).subtype ⟨t⁻¹ * (y : MulAut V) * t, hyM⟩,
          ⟨⟨t⁻¹ * (y : MulAut V) * t, hyM⟩, hx, rfl⟩, hyx.symm⟩
    have hfin : Finite ↥(CFSG.Quasithin.conjSetUnder T K) := by
      have hr : CFSG.Quasithin.conjSetUnder T K =
          Set.range (fun t : ↥T => K.map (MulAut.conj (t : MulAut V)).toMonoidHom) := by
        ext K'
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, rfl⟩
        · rintro ⟨t, rfl⟩
          exact ⟨t, t.2, rfl⟩
      rw [hr]
      exact (Set.finite_range _).to_subtype
    let e : Fin (Nat.card ↥(CFSG.Quasithin.conjSetUnder T K)) ≃
        ↥(CFSG.Quasithin.conjSetUnder T K) := (Finite.equivFin _).symm
    have hrange : Set.range (fun i => (e i).1) = CFSG.ASVolI.ChB.conjSet T K := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).2
      · intro hx
        exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
    have hIDP1 : CFSG.Quasithin.EmptyFaithfulMultiple.IsInnerDirectProduct
        (fun i => (e i).1) (CFSG.Quasithin.conjClosure K T) :=
      burnsideB1c_idp_comp (fun K' : ↥(CFSG.Quasithin.conjSetUnder T K) =>
        (K' : Subgroup (MulAut V))) _ e h1
    have hIDP2 : CFSG.Quasithin.EmptyFaithfulMultiple.IsInnerDirectProduct
        (fun i => (Mb (e i)).map φ.toMonoidHom) ⊤ := by
      have h' := burnsideB1c_idp_map φ Mb ⊤ h5
      rw [Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective] at h'
      exact burnsideB1c_idp_comp (fun i => (Mb i).map φ.toMonoidHom) ⊤ e h'
    have hrel : ∀ i, ((((e i).1).subgroupOf (CFSG.Quasithin.twelveM T K)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K)))) =
          CFSG.Open.relPPrimeCore 2 ((Mb (e i)).map φ.toMonoidHom) := by
      intro i
      rw [burnsideB1c_relPPrime_map_eq φ (Mb (e i)) 2,
        burnsideB1c_relPPrime_eq_oddCoreOfSub, ← h7 (e i)]
      unfold CFSG.Quasithin.secImg
      rw [Subgroup.map_map, hcomp]
    have hnon : ∀ i, Nonempty (↥((Mb (e i)).map φ.toMonoidHom) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
      intro i
      obtain ⟨ψ'⟩ := h6 (e i)
      exact ⟨(Subgroup.equivMapOfInjective (Mb (e i)) φ.toMonoidHom φ.injective).symm.trans ψ'⟩
    have hperm1 : ∀ t ∈ T, ∀ i, ∃ j,
        (((((Mb (e i)).map φ.toMonoidHom).comap
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K)))).map
              (CFSG.Quasithin.twelveM T K).subtype).map (MulAut.conj t).toMonoidHom) =
          ((((Mb (e j)).map φ.toMonoidHom).comap
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K)))).map
              (CFSG.Quasithin.twelveM T K).subtype) := by
      intro t ht i
      obtain ⟨j, hj⟩ := h3 t ht (e i)
      refine ⟨e.symm j, ?_⟩
      rw [Equiv.apply_symm_apply, hcomap, hcomap]
      exact perm t ht (e i) j hj
    have hperm2 : ∀ i j, ∃ t ∈ T,
        (((((Mb (e i)).map φ.toMonoidHom).comap
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K)))).map
              (CFSG.Quasithin.twelveM T K).subtype).map (MulAut.conj t).toMonoidHom) =
          ((((Mb (e j)).map φ.toMonoidHom).comap
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(CFSG.Quasithin.twelveM T K)))).map
              (CFSG.Quasithin.twelveM T K).subtype) := by
      intro i j
      obtain ⟨t, ht, hj⟩ := h4 (e i) (e j)
      refine ⟨t, ht, ?_⟩
      rw [hcomap, hcomap]
      exact perm t ht (e i) (e j) hj
    exact ⟨_, fun i => (e i).1, hrange, hIDP1, fun i => (Mb (e i)).map φ.toMonoidHom, hIDP2,
      hrel, hnon, hperm1, hperm2⟩
  exact key _ (burnsideB1c_conjClosure_eq T K)

@[expose] def B_1_13 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), CFSG.SectionRank.IsKGroupCat ↥G → pCoreOf 2 G = ⊥ →
      ∀ T K : Subgroup (MulAut V), IsSylowTwoOf T G → K ≤ G →
        (CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) → IsSubnormal K (K ⊔ T) →
        ⁅K, ffJP (offenderSet G) T⁆ = K →
          (Nonempty (↥K ≃* Multiplicative (ZMod 3)) ∧ K ≤ fitOf G ∧
              K ≤ Subgroup.centralizer (fitOf G : Set (MulAut V))) ∨
          (IsComponentOf K G ∧ (IsLieTypeQuasisimple ↥K ∨ (∃ n, IsAlt n ↥K) ∨
              IsHat ↥K ↥(alternatingGroup (Fin 6)))) ∨
          ∃ L : Subgroup (MulAut V), IsComponentOf L G ∧ K ≤ L ∧
            ∃ m, IsAlt m ↥L ∧ ((∃ n, n ≤ m ∧ IsAlt n ↥K) ∨ (IsPSL 3 2 1 ↥K ∧ m = 7))

end CFSG.ASVolI
