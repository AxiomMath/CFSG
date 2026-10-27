module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F11

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def CElt (M V₀ : Subgroup G) (v : G) : Subgroup G where
  carrier := {m | m ∈ M ∧ m ∈ normalizer (V₀ : Set G) ∧ m * v * m⁻¹ * v⁻¹ ∈ V₀}
  one_mem' := ⟨M.one_mem, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨haM, haN, ha⟩ ⟨hbM, hbN, hb⟩
    refine ⟨M.mul_mem haM hbM, Subgroup.mul_mem _ haN hbN, ?_⟩
    have h1 : a * b * v * (a * b)⁻¹ * v⁻¹ =
        (a * (b * v * b⁻¹ * v⁻¹) * a⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
    rw [h1]
    exact V₀.mul_mem ((mem_normalizer_iff.1 haN _).1 hb) ha
  inv_mem' := by
    rintro a ⟨haM, haN, ha⟩
    refine ⟨M.inv_mem haM, Subgroup.inv_mem _ haN, ?_⟩
    have h1 : a⁻¹ * v * a⁻¹⁻¹ * v⁻¹ = (a⁻¹ * (a * v * a⁻¹ * v⁻¹) * a⁻¹⁻¹)⁻¹ := by group
    rw [h1]
    exact V₀.inv_mem ((mem_normalizer_iff.1 (Subgroup.inv_mem _ haN) _).1 ha)

@[expose] def CTilde (M V₀ V : Subgroup G) : Subgroup G :=
  ⨅ v ∈ V, CElt M V₀ v

abbrev MBar11 (M V₀ V : Subgroup G) : Type :=
  ↥M ⧸ (CTilde M V₀ V).subgroupOf M

@[expose] def barImage11 (M V₀ V X : Subgroup G) [((CTilde M V₀ V).subgroupOf M).Normal] :
    Subgroup (MBar11 M V₀ V) :=
  (X.subgroupOf M).map (QuotientGroup.mk' ((CTilde M V₀ V).subgroupOf M))

@[expose] def barPreimage11 (M V₀ V : Subgroup G) [((CTilde M V₀ V).subgroupOf M).Normal]
    (Xbar : Subgroup (MBar11 M V₀ V)) : Subgroup G :=
  (Xbar.comap (QuotientGroup.mk' ((CTilde M V₀ V).subgroupOf M))).map M.subtype

@[expose] def InP11 (D : Data G) (X : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ X ≤ D.M ∧ IsPGroup p ↥X ∧ (∀ x ∈ X, x ^ p = 1) ∧ ¬ IsCyclic ↥X ∧
    Permutes X D.T ∧ rankThreeGamma 1 p X ≤ D.M ∧
    (CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M ∨
      ∃ Y : Subgroup G, ¬ IsCyclic ↥Y ∧
        (∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P D.M ∧ Y ≤ P ∧
          P ≤ normalizer (Y : Set G)) ∧ rankThreeGamma 1 p Y ≤ D.M)

@[expose] def Hyp11 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  (InCalV0 D.M V₀ V ∨ (V₀ = ⊥ ∧ InCalW D.M D.T V)) ∧
    ¬ CFSG.CGT.Timmesfeld75.IsTI V ∧
    (8 ≤ Nat.card V₀ → ¬ InCalV1 D.M D.T V₀ ∧ ∀ X : Subgroup G, ¬ InP11 D X)

@[expose] def O2E (Y : Subgroup G) : Subgroup G :=
  ((rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map
    Y.subtype

@[expose] def O2p (p : ℕ) (M : Subgroup G) : Subgroup G :=
  ((CFSG.pCore p (Bar2 M)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

@[expose] def Omega1p (p : ℕ) (R : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ R ∧ x ^ p = 1}

@[expose] def R111 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp11 D V₀ V → D.sig3 = ∅

@[expose] def R112 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp11 D V₀ V → D.sig2.Nonempty → CTilde D.M V₀ V = pCoreOf 2 D.M

@[expose] def R115 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp11 D V₀ V → Nat.card V₀ ≤ 4 → ∀ p ∈ D.sig,
    CFSG.Open.pRank p (CTilde D.M V₀ V) ≤ 1 ∧
    (∀ [((CTilde D.M V₀ V).subgroupOf D.M).Normal],
      CFSG.Open.pRank p D.M - 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MBar11 D.M V₀ V))) ∧
    2 ≤ CFSG.Open.pRank p D.M - 1

@[expose] def IsY119 (M V₀ V X Y : Subgroup G) [((CTilde M V₀ V).subgroupOf M).Normal] : Prop :=
  Y ≤ X ∧ ⁅Y, Y⁆ = Y ∧ O2E Y = Y ∧ X ≤ normalizer (Y : Set G) ∧ Y ⊓ CTilde M V₀ V ≤ OInf Y ∧
    barImage11 M V₀ V Y = barImage11 M V₀ V X

@[expose] def R119 (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp11 D V₀ V →
    ∀ [((CTilde D.M V₀ V).subgroupOf D.M).Normal] (X : Subgroup G),
      CTilde D.M V₀ V ≤ X → X ≤ D.M →
      rankThreeLayer (barImage11 D.M V₀ V X) = barImage11 D.M V₀ V X →
      ∃ Y : Subgroup G, IsY119 D.M V₀ V X Y ∧
        ((∃ Lbar : Subgroup (MBar11 D.M V₀ V), IsComponentOf Lbar ⊤ ∧
            barImage11 D.M V₀ V X =
              ⨆ g : MBar11 D.M V₀ V, Lbar.map (MulAut.conj g).toMonoidHom) →
          ¬ F09.Thin9 Y → ⁅Y, V₀⁆ = ⊥)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F11
