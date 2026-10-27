module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
public import CFSG.GH74.E2.DirectProd
public import CFSG.Quasithin.H13.A5S1327j
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltModule
public import CFSG.Quasithin.Vol2.Ch10SecQ3CWrF
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsComp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def KA5PairIrr : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L₁ L₂ X : Subgroup (MulAut W)) (I : Subgroup W), X = L₁ ⊔ L₂ →
      (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) → IsAlt ↥L₁ 5 → IsAlt ↥L₂ 5 →
      IsIrrOn X I ⊥ → commSub I L₁ ≠ ⊥ → commSub I L₂ ≠ ⊥ →
      (rk ↥I = 8 ∧ NatOmegaPlus X I ⊥ 4 2) ∨ rk ↥I = 16

@[expose] def K144Swap16 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L₁ L₂ X : Subgroup (MulAut W), X = L₁ ⊔ L₂ → (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) →
      IsAlt ↥L₁ 5 → IsAlt ↥L₂ 5 → X ≤ Y → (X.subgroupOf Y).Normal →
      (∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) →
      IsIrrOn X ⊤ ⊥ → rk W = 16 → bParam L₁ Y ≤ 1

@[expose] def KA5Homog : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W), L ≤ Y → (L.subgroupOf Y).Normal → IsAlt ↥L 5 →
      fixV L = ⊥ → IrrSpanTrans Y L →
      (∀ I ∈ irrSet L, BinaryNaturalSL L I ⊥ 2 2) ∨ (∀ I ∈ irrSet L, AlternatingNatural L I ⊥ 5)

@[expose] def KA5OmegaMinusB : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W), L ≤ Y → (L.subgroupOf Y).Normal → IsAlt ↥L 5 →
      fixV L = ⊥ → (⨆ I ∈ irrSet L, I) = ⊤ → (∀ I ∈ irrSet L, AlternatingNatural L I ⊥ 5) →
      bParam L Y ≤ 1

@[expose] def KA5NatSum : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L₁ L₂ X : Subgroup (MulAut W), X = L₁ ⊔ L₂ → (∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) →
      IsAlt ↥L₁ 5 → IsAlt ↥L₂ 5 →
      (⨆ I ∈ irrSet L₁, I) = ⊤ → (⨆ I ∈ irrSet L₂, I) = ⊤ →
      (∀ I ∈ irrSet L₁, BinaryNaturalSL L₁ I ⊥ 2 2) →
      (∀ I ∈ irrSet L₂, BinaryNaturalSL L₂ I ⊥ 2 2) →
      (∀ I ∈ irrSet X, rk ↥I = 8) ∧
        ∃ n : ℕ, rk W = 8 * n ∧ SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ n

@[expose] def KA5InvertsThree : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G) (t : G), IsAlt ↥L 5 → t ^ 2 = 1 →
    (∀ x ∈ L, t * x * t⁻¹ ∈ L) → (∃ x ∈ L, t * x ≠ x * t) →
    ∃ z ∈ L, orderOf z = 3 ∧ t * z * t⁻¹ = z⁻¹

@[expose] def KA5NatFpf : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W), IsAlt ↥L 5 → (⨆ I ∈ irrSet L, I) = ⊤ →
      (∀ I ∈ irrSet L, BinaryNaturalSL L I ⊥ 2 2) →
      ∀ z ∈ L, orderOf z = 3 → fixV (Subgroup.zpowers z) = ⊥

theorem isOmegaPlus_sup_of_isAlt_five {G : Type} [Group G] {L₁ L₂ : Subgroup G}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hdisj : L₁ ⊓ L₂ = ⊥)
    (h₁ : IsAlt ↥L₁ 5) (h₂ : IsAlt ↥L₂ 5) : IsOmegaPlus ↥(L₁ ⊔ L₂) 4 2 := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  refine isOmegaPlus_of_isL2Square le_rfl ⟨↥L₁, ↥L₂, inferInstance, inferInstance,
    ⟨(CFSG.GH74.E2.prodSupEquiv L₁ L₂ hcomm hdisj).symm⟩, ?_, ?_⟩
  · exact CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e₁
  · exact CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e₂

theorem two_mul_rk_commV_of_inv_fpf {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {z t : MulAut W} (hz : z ^ 3 = 1)
    (hfix : fixV (Subgroup.zpowers z) = ⊥) (ht : t * t = 1) (htz : t * z * t⁻¹ = z⁻¹) :
    2 * rk ↥(commV (Subgroup.zpowers t)) = rk W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt.exists_card_eq_four_pow hW hz
    (U := ⊤) (fun u _ => Subgroup.mem_top _) (fun u _ hu => by
      have h : u ∈ fixV (Subgroup.zpowers z) := CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr hu
      rw [hfix] at h
      exact Subgroup.mem_bot.mp h)
  have hk' : Nat.card W = 4 ^ k := by rwa [Subgroup.card_top] at hk
  have hidx :=
    CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt.index_fixV_of_inv_fpf hW hz hfix ht htz hk'
  have h4 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have hrkW : rk W = 2 * k := by
    show padicValNat 2 (Nat.card W) = 2 * k
    rw [hk', h4, padicValNat.prime_pow]
  have hrkI : rkIdx (fixV (Subgroup.zpowers t)) = k := by
    show padicValNat 2 (fixV (Subgroup.zpowers t)).index = k
    rw [hidx, padicValNat.prime_pow]
  rw [← rkIdx_fixV_zpowers, hrkI, hrkW]

theorem inf_eq_bot_of_commute_isAlt_five {G : Type} [Group G] {L₁ L₂ : Subgroup G}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h₁ : IsAlt ↥L₁ 5) : L₁ ⊓ L₂ = ⊥ := by
  obtain ⟨e⟩ := h₁
  exact CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.WrCore.inf_eq_bot_of_commute e hcomm

theorem w4Thm14_4_dichotomy {W : Type} [CommGroup W] [Finite W]
    {Y L₁ L₂ X : Subgroup (MulAut W)} (hc₁ : IsComponentOf L₁ Y) (hc₂ : IsComponentOf L₂ Y)
    (ha₁ : IsAlt ↥L₁ 5) (ha₂ : IsAlt ↥L₂ 5) (hne : L₁ ≠ L₂) (hX : X = L₁ ⊔ L₂)
    (hXn : (X.subgroupOf Y).Normal) :
    (∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) ∨
      ((L₁.subgroupOf Y).Normal ∧ (L₂.subgroupOf Y).Normal) := by
  have hXle : X ≤ Y := hX.le.trans (sup_le hc₁.1 hc₂.1)
  have hnormX : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXle).mp hXn
  have hXmap : ∀ g ∈ Y, X.map (MulAut.conj g).toMonoidHom = X := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormX hg)
  have hL₁X : L₁ ≤ X := by rw [hX]; exact le_sup_left
  have hL₂X : L₂ ≤ X := by rw [hX]; exact le_sup_right
  have key : ∀ K : Subgroup (MulAut W), IsComponentOf K Y → K ≤ X → K = L₁ ∨ K = L₂ := by
    intro K hK hKX
    rcases eq_or_commute_of_isComponentOf hK hc₁ with h1 | h1
    · exact Or.inl h1
    rcases eq_or_commute_of_isComponentOf hK hc₂ with h2 | h2
    · exact Or.inr h2
    exfalso
    have hKcomm : ∀ k ∈ K, ∀ x ∈ (L₁ ⊔ L₂ : Subgroup (MulAut W)), k * x = x * k := by
      intro k hk x hx
      rw [Subgroup.sup_eq_closure] at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
          rcases hx with hx | hx
          · exact h1 k hk x hx
          · exact h2 k hk x hx
      | one => simp
      | mul x y hx hy ihx ihy =>
          calc k * (x * y) = k * x * y := (mul_assoc _ _ _).symm
            _ = x * k * y := by rw [ihx]
            _ = x * (k * y) := mul_assoc _ _ _
            _ = x * (y * k) := by rw [ihy]
            _ = x * y * k := (mul_assoc _ _ _).symm
      | inv x hx ih =>
          have h' : x⁻¹ * k = k * x⁻¹ := by
            calc x⁻¹ * k = x⁻¹ * (k * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * k) * x⁻¹ := by rw [ih]
              _ = k * x⁻¹ := by group
          exact h'.symm
    have hKabel : IsMulCommutative ↥K := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have hb : (b : MulAut W) ∈ L₁ ⊔ L₂ := by
        have hbx := hKX b.2
        rwa [hX] at hbx
      exact hKcomm a.1 a.2 b.1 hb
    have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
    have hbot : commutator ↥K = ⊥ := (commutator_eq_bot_iff (G := ↥K)).mpr hKabel
    haveI : _root_.IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
    haveI : Nontrivial ↥K :=
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥K)).nontrivial
    have htopbot : (⊤ : Subgroup ↥K) = ⊥ := by rw [← hq.1, hbot]
    exact top_ne_bot htopbot
  by_cases hsw : ∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom
  · exact Or.inl hsw
  · right
    have hconj : ∀ g ∈ Y, IsComponentOf (L₁.map (MulAut.conj g).toMonoidHom) Y :=
      fun g hg => isComponentOf_map_conj_of_mem hc₁ hg
    have hconj₂ : ∀ g ∈ Y, IsComponentOf (L₂.map (MulAut.conj g).toMonoidHom) Y :=
      fun g hg => isComponentOf_map_conj_of_mem hc₂ hg
    have hKX' : ∀ g ∈ Y, L₁.map (MulAut.conj g).toMonoidHom ≤ X := by
      intro g hg
      have hle : L₁.map (MulAut.conj g).toMonoidHom ≤ X.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hL₁X
      rwa [hXmap g hg] at hle
    have hKX₂ : ∀ g ∈ Y, L₂.map (MulAut.conj g).toMonoidHom ≤ X := by
      intro g hg
      have hle : L₂.map (MulAut.conj g).toMonoidHom ≤ X.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hL₂X
      rwa [hXmap g hg] at hle
    have hL₁ : ∀ g ∈ Y, L₁.map (MulAut.conj g).toMonoidHom = L₁ := by
      intro g hg
      rcases key _ (hconj g hg) (hKX' g hg) with h | h
      · exact h
      · exact absurd ⟨g, hg, h.symm⟩ hsw
    have hL₂ : ∀ g ∈ Y, L₂.map (MulAut.conj g).toMonoidHom = L₂ := by
      intro g hg
      rcases key _ (hconj₂ g hg) (hKX₂ g hg) with h | h
      · exfalso
        have h2 := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) h
        have hcomp : ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
            MonoidHom.id (MulAut W) := by
          ext x
          simp [MulAut.conj_apply]
        rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h2
        rw [hL₁ g⁻¹ (Y.inv_mem hg)] at h2
        exact hne h2.symm
      · exact h
    constructor
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hc₁.1]
      intro y hy
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hL₁ y hy
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hc₂.1]
      intro y hy
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hL₂ y hy

theorem iSup_conj_eq_of_swap {W : Type} [CommGroup W] [Finite W]
    {Y L₁ L₂ X : Subgroup (MulAut W)} (hc₁ : IsComponentOf L₁ Y) (hc₂ : IsComponentOf L₂ Y)
    (ha₁ : IsAlt ↥L₁ 5) (ha₂ : IsAlt ↥L₂ 5) (hne : L₁ ≠ L₂) (hX : X = L₁ ⊔ L₂)
    (hXn : (X.subgroupOf Y).Normal)
    (hsw : ∃ g ∈ Y, L₂ = L₁.map (MulAut.conj g).toMonoidHom) :
    (⨆ g ∈ Y, L₁.map (MulAut.conj g).toMonoidHom) = X := by
  have hXle : X ≤ Y := hX.le.trans (sup_le hc₁.1 hc₂.1)
  have hnormX : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXle).mp hXn
  have hXmap : ∀ g ∈ Y, X.map (MulAut.conj g).toMonoidHom = X := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormX hg)
  have hL₁X : L₁ ≤ X := by rw [hX]; exact le_sup_left
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun g hg => ?_
    have hle : L₁.map (MulAut.conj g).toMonoidHom ≤ X.map (MulAut.conj g).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hL₁X
    rw [hXmap g hg] at hle
    exact hle
  · rw [hX]
    refine sup_le ?_ ?_
    · have h1 : L₁.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L₁ := by
        rw [show (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) by
          ext x
          simp]
        exact Subgroup.map_id L₁
      exact (le_of_eq h1.symm).trans (le_iSup₂_of_le (1 : MulAut W) Y.one_mem le_rfl)
    · obtain ⟨g, hg, hg2⟩ := hsw
      rw [hg2]
      exact le_iSup₂_of_le g hg le_rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
