module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def InPStar (D : Data G) (V₀ X : Subgroup G) : Prop :=
  F11.InP11 D X ∧
    (V₀ = ⊥ → ∃ p : ℕ, p.Prime ∧ IsPGroup p X ∧
      (p ^ 2 < Nat.card X ∨
        (∃ a ∈ F11.Omega1p 2 D.T, F11.Omega1p 2 D.T =
          Subgroup.zpowers a ⊔ (F11.Omega1p 2 D.T ⊓ pCoreOf 2 (X ⊔ D.T))) ∨
        IrrOn (normalizer (X : Set G) ⊓ normalizer (D.T : Set G)) X))

theorem InPStar.inP11 {D : Data G} {V₀ X : Subgroup G} (h : InPStar D V₀ X) : F11.InP11 D X :=
  h.1

theorem inPStar_iff_of_ne_bot {D : Data G} {V₀ : Subgroup G} (h : V₀ ≠ ⊥) (X : Subgroup G) :
    InPStar D V₀ X ↔ F11.InP11 D X :=
  ⟨fun hX => hX.1, fun hX => ⟨hX, fun h0 => absurd h0 h⟩⟩

@[expose] def Hyp124Min (D : Data G) (H₀ : Subgroup G) : Prop :=
  H₀ ∈ RankThreeUC.hSet D.T D.M ∧ RankThreeUC.Hyp124 D.M H₀ ∧
    ∀ H ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H → H ≤ H₀ → H = H₀

theorem exists_hyp124Min (D : Data G)
    (h : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) : ∃ H₀, Hyp124Min D H₀ := by
  obtain ⟨H₁, hH₁, hH₁'⟩ := h
  obtain ⟨H₀, ⟨hH₀, hH₀'⟩, hmin⟩ :=
    Set.exists_min_image {H : Subgroup G | H ∈ RankThreeUC.hSet D.T D.M ∧ RankThreeUC.Hyp124 D.M H}
      (fun H => Nat.card H) (Set.toFinite _) ⟨H₁, hH₁, hH₁'⟩
  exact ⟨H₀, hH₀, hH₀', fun H hH hH' hle => Subgroup.eq_of_le_of_card_ge hle (hmin H ⟨hH, hH'⟩)⟩

theorem Hyp125.exists_hyp124Min {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    ∃ H₀, Hyp124Min D H₀ :=
  PartTwo.exists_hyp124Min D h.2

structure Hyp141 (D : Data G) (L₁ L₂ X : Subgroup G) : Prop where
  sig : D.sig = {7}
  rank : evenRank G = 3
  mem₁ : L₁ ∈ calC D.M
  mem₂ : L₂ ∈ calC D.M
  ne : L₁ ≠ L₂
  shape₁ : IsL3 (Bar2 L₁) 1
  shape₂ : IsL3 (Bar2 L₂) 1
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 X (L₁ ⊔ L₂)
  permutes : Permutes X D.T

section Sec15

variable (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G)

@[expose] noncomputable def wTil : Subgroup (Vtil V₀ V hV) :=
  commSub ⊤ (barSub V₀ V hV L)

@[expose] noncomputable def wSub : Subgroup G :=
  preTil V₀ V hV (wTil V₀ V hV L)

open Classical in
@[expose] noncomputable def v1Sub : Subgroup G :=
  if V₀ = ⊥ then ⨆ m : M, conjSubgroup (wSub V₀ V hV L ⊓ centralizer (L : Set G)) (m : G) else V₀

theorem v1Sub_of_ne_bot (h : V₀ ≠ ⊥) : v1Sub M V₀ V hV L = V₀ := by
  unfold v1Sub
  rw [if_neg h]

theorem v1Sub_of_eq_bot (h : V₀ = ⊥) :
    v1Sub M V₀ V hV L =
      ⨆ m : M, conjSubgroup (wSub V₀ V hV L ⊓ centralizer (L : Set G)) (m : G) := by
  unfold v1Sub
  rw [if_pos h]

@[expose] noncomputable def wConj : Set (Subgroup G) :=
  {X | ∃ m ∈ M, X = conjSubgroup (wSub V₀ V hV L) m}

abbrev vStar : Type :=
  Vtil (v1Sub M V₀ V hV L) V hV

@[expose] noncomputable def wStar : Subgroup (vStar M V₀ V hV L) :=
  imgTil (v1Sub M V₀ V hV L) V hV (wSub V₀ V hV L)

@[expose] noncomputable def gamma15 : ℕ :=
  rk ↥(wStar M V₀ V hV L)

@[expose] noncomputable def delta15 : ℕ :=
  mSub (v1Sub M V₀ V hV L ⊓ wSub V₀ V hV L)

@[expose] noncomputable def s15 : ℕ :=
  Set.ncard {X : Subgroup (MulAut (Vtil V₀ V hV)) |
    ∃ φ ∈ Mbar M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}

@[expose] noncomputable def nBar : Subgroup G :=
  preBarSub M V₀ V hV (normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))))

end Sec15

structure Hyp151 (D : Data G) (V₀ V L : Subgroup G) : Prop where
  hyp125 : Hyp125 D V₀ V
  le : L ≤ D.M
  twoResidual_eq : twoResidual L = L
  fstar_eq : Fstar (barSub V₀ V hyp125.isElemAbelian L) = barSub V₀ V hyp125.isElemAbelian L
  commute : ∀ g ∈ D.M, g ∉ nBar D.M V₀ V hyp125.isElemAbelian L →
    ⁅barSub V₀ V hyp125.isElemAbelian L, barSub V₀ V hyp125.isElemAbelian (conjSubgroup L g)⁆ = ⊥ ∧
      commSub (wTil V₀ V hyp125.isElemAbelian L)
        (barSub V₀ V hyp125.isElemAbelian (conjSubgroup L g)) = ⊥

theorem Hyp151.isElemAbelian {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    IsElemAbelian 2 V :=
  h.hyp125.isElemAbelian

structure Hyp154 (D : Data G) (V₀ V L : Subgroup G) : Prop where
  hyp151 : Hyp151 D V₀ V L
  unique₁ : ∀ w ∈ wSub V₀ V hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V hyp151.isElemAbelian L, w ≠ 1 →
    UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))
  unique₂ : ∀ x ∈ D.M, ∀ y ∈ D.M,
    conjSubgroup (wSub V₀ V hyp151.isElemAbelian L) x ≠
      conjSubgroup (wSub V₀ V hyp151.isElemAbelian L) y →
    ∀ w ∈ v1Sub D.M V₀ V hyp151.isElemAbelian L ⊔
      ⨆ X ∈ {X | X ∈ wConj D.M V₀ V hyp151.isElemAbelian L ∧
        X ≠ conjSubgroup (wSub V₀ V hyp151.isElemAbelian L) x ∧
        X ≠ conjSubgroup (wSub V₀ V hyp151.isElemAbelian L) y}, X,
    w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))
  third : ∀ g : G, g ∉ D.M → ∀ X ∈ wConj D.M V₀ V hyp151.isElemAbelian L,
    ∀ Y ∈ wConj D.M V₀ V hyp151.isElemAbelian L, X ≠ Y →
    (X ⊔ Y ⊔ v1Sub D.M V₀ V hyp151.isElemAbelian L) ⊓
      conjSubgroup (wSub V₀ V hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V hyp151.isElemAbelian L) g ≠ ⊥ →
    s15 D.M V₀ V hyp151.isElemAbelian L = 2 ∧
      delta15 D.M V₀ V hyp151.isElemAbelian L < gamma15 D.M V₀ V hyp151.isElemAbelian L - 1

structure Hyp16 (D : Data G) (V₀ V : Subgroup G) : Prop where
  hyp125 : Hyp125 D V₀ V
  small : mSub V₀ ≤ 2
  not_gt : ¬ MBarGT D.M V₀ V 3

structure Setting16 (D : Data G) (V₀ V L : Subgroup G) : Prop where
  hyp16 : Hyp16 D V₀ V
  hyp151 : Hyp151 D V₀ V L

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
