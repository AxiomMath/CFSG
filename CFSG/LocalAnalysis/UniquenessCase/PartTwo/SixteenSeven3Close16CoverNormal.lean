module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem close16_perfect_quot_two {X : Type*} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) (N : Subgroup X) [N.Normal]
    (h : IsPGroup 2 (X ⧸ N)) : N = ⊤ := by
  haveI : Group.IsPerfect X := hperf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hNt
  haveI : Nontrivial (X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNt
  exact Group.IsPerfect.not_isNilpotent (X ⧸ N) h.isNilpotent

private theorem close16_commutator_le_of_subgroupOf {X C : Subgroup G} (hCX : C ≤ X)
    (h : ⁅(⊤ : Subgroup ↥X), ⊤⁆ ≤ C.subgroupOf X) : ⁅X, X⁆ ≤ C := by
  have hmap := Subgroup.map_mono (f := Subgroup.subtype X) h
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le hCX] at hmap
  exact hmap

theorem close16_normal_of_cover {M C X Y : Subgroup G}
    (hCM : (C.subgroupOf M).Normal) (hXM : X ≤ M) (hXN : (X.subgroupOf M).Normal)
    (hCX : C ≤ X) (hYX : Y ≤ X) (hXY : X ≤ normalizer (Y : Set G)) (hYperf : ⁅Y, Y⁆ = Y)
    (hXYC : X = Y ⊔ C) (hY2 : IsPGroup 2 ↥(Y ⊓ C))
    (hXC : ∀ N : Subgroup G, C ≤ N → N ≤ X → (N.subgroupOf X).Normal → N = C ∨ N = X)
    (hXab : ¬ ⁅X, X⁆ ≤ C) :
    (Y.subgroupOf M).Normal := by
  have hYM : Y ≤ M := hYX.trans hXM
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYM]
  intro m hm
  have hCnormM : M ≤ normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hCX.trans hXM)).mp hCM
  have hXnormM : M ≤ normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mp hXN
  have hXnormC : X ≤ normalizer (C : Set G) := hXM.trans hCnormM
  have hmX : ∀ x ∈ X, m * x * m⁻¹ ∈ X :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp (hXnormM hm) x).mp hx
  have hmXinv : ∀ x ∈ X, m⁻¹ * x * m ∈ X := by
    intro x hx
    have h := (Subgroup.mem_normalizer_iff.mp (hXnormM (M.inv_mem hm)) x).mp hx
    simpa using h
  set Y₁ : Subgroup G := conjSubgroup Y m with hY₁
  have hY1mem : ∀ a : G, a ∈ Y₁ ↔ m * a * m⁻¹ ∈ Y := by
    intro a; rw [hY₁]; exact mem_conjSubgroup_iff
  have hY1X : Y₁ ≤ X := by
    intro a ha
    have h1 : m * a * m⁻¹ ∈ Y := (hY1mem a).mp ha
    have h2 : m⁻¹ * (m * a * m⁻¹) * m ∈ X := hmXinv _ (hYX h1)
    simpa [mul_assoc] using h2
  have hY1conj : ∀ x ∈ X, ∀ a ∈ Y₁, x * a * x⁻¹ ∈ Y₁ := by
    intro x hx a ha
    rw [hY1mem] at ha ⊢
    have hmx : m * x * m⁻¹ ∈ X := hmX x hx
    have hconj : (m * x * m⁻¹) * (m * a * m⁻¹) * (m * x * m⁻¹)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hXY hmx) (m * a * m⁻¹)).mp ha
    have hEq : (m * x * m⁻¹) * (m * a * m⁻¹) * (m * x * m⁻¹)⁻¹
        = m * (x * a * x⁻¹) * m⁻¹ := by group
    rwa [hEq] at hconj
  have hY1normX : X ≤ normalizer (Y₁ : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro a
    exact ⟨fun ha => hY1conj x hx a ha, fun ha => by
      have h := hY1conj x⁻¹ (X.inv_mem hx) (x * a * x⁻¹) ha
      simpa [mul_assoc] using h⟩
  have hNnormX : X ≤ normalizer ((Y ⊓ Y₁ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [Subgroup.mem_inf] at hn ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hXY hx) n).mp hn.1,
             (Subgroup.mem_normalizer_iff.mp (hY1normX hx) n).mp hn.2⟩
    · intro hn
      rw [Subgroup.mem_inf] at hn ⊢
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hXY hx) n).mpr hn.1,
             (Subgroup.mem_normalizer_iff.mp (hY1normX hx) n).mpr hn.2⟩
  have hN_le_X : Y ⊓ Y₁ ≤ X := inf_le_left.trans hYX
  have hNCsub : (((Y ⊓ Y₁) ⊔ C).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hN_le_X hCX)).mpr (by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_sup (Y ⊓ Y₁) C ⟨hNnormX hx, hXnormC hx⟩)
  have hYle : Y ≤ Y₁ := by
    rcases hXC ((Y ⊓ Y₁) ⊔ C) le_sup_right (sup_le hN_le_X hCX) hNCsub with hNC | hNC
    · exfalso
      have hN_le_C : Y ⊓ Y₁ ≤ C := le_sup_left.trans hNC.le
      have hYY1_le : ⁅Y, Y₁⁆ ≤ C := by
        have hleY : ⁅Y, Y₁⁆ ≤ Y := by
          rw [Subgroup.commutator_comm]
          exact (Subgroup.le_normalizer_iff_commutator_le_right).mp (hY1X.trans hXY)
        have hleY1 : ⁅Y, Y₁⁆ ≤ Y₁ :=
          (Subgroup.le_normalizer_iff_commutator_le_right).mp (hYX.trans hY1normX)
        exact (le_inf hleY hleY1).trans hN_le_C
      haveI : (Y.subgroupOf X).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXY
      haveI : (C.subgroupOf X).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hXnormC
      haveI : (Y₁.subgroupOf X).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hY1X).mpr hY1normX
      have hconjX : conjSubgroup X m = X :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (hXnormM hm)
      have hconjC : conjSubgroup C m = C :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (hCnormM hm)
      have hconj_sup : conjSubgroup (Y ⊔ C) m = conjSubgroup Y m ⊔ conjSubgroup C m := by
        rw [conjSubgroup, conjSubgroup, conjSubgroup, Subgroup.map_sup]
      have hXY1C : X = Y₁ ⊔ C := by
        rw [← hconjX, hXYC, hconj_sup, ← hY₁, hconjC]
      have hsupY : Y.subgroupOf X ⊔ C.subgroupOf X = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hYX hCX, ← hXYC, Subgroup.subgroupOf_self]
      have hsupY1 : Y₁.subgroupOf X ⊔ C.subgroupOf X = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hY1X hCX, ← hXY1C, Subgroup.subgroupOf_self]
      have hYY1' : ⁅Y.subgroupOf X, Y₁.subgroupOf X⁆ ≤ C.subgroupOf X := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        have h := hYY1_le (Subgroup.commutator_mem_commutator
          (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb))
        have hcoe : (↑⁅a, b⁆ : G) = ⁅(↑a : G), (↑b : G)⁆ :=
          map_commutatorElement (Subgroup.subtype X) a b
        rw [Subgroup.mem_subgroupOf, hcoe]
        exact h
      have hmain : ⁅Y₁.subgroupOf X ⊔ C.subgroupOf X,
          Y.subgroupOf X ⊔ C.subgroupOf X⁆ ≤ C.subgroupOf X := by
        rw [Subgroup.commutator_sup_right]
        apply sup_le
        · rw [Subgroup.commutator_comm, Subgroup.commutator_sup_right]
          exact sup_le hYY1' (Subgroup.commutator_le_left _ _)
        · exact Subgroup.commutator_le_left _ _
      have htop : ⁅(⊤ : Subgroup ↥X), ⊤⁆ ≤ C.subgroupOf X := by
        rw [hsupY1, hsupY] at hmain
        exact hmain
      exact hXab (close16_commutator_le_of_subgroupOf hCX htop)
    · have hperfY : Group.IsPerfect ↥Y := (Subgroup.isPerfect_iff (H := Y)).mpr hYperf
      haveI : ((Y ⊓ Y₁).subgroupOf Y).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left : Y ⊓ Y₁ ≤ Y)).mpr
          (hYX.trans hNnormX)
      have hD2 : IsPGroup 2 ↥((Y ⊓ C).subgroupOf Y) :=
        hY2.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ⊓ C ≤ Y)).symm
      have hdecomp : ∀ y : ↥Y,
          ∃ c ∈ (Y ⊓ C).subgroupOf Y,
            QuotientGroup.mk' ((Y ⊓ Y₁).subgroupOf Y) c
              = QuotientGroup.mk' ((Y ⊓ Y₁).subgroupOf Y) y := by
        intro y
        have hsupNC : ((Y ⊓ Y₁).subgroupOf X) ⊔ C.subgroupOf X = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hN_le_X hCX, hNC, Subgroup.subgroupOf_self]
        haveI : (C.subgroupOf X).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).mpr hXnormC
        have hyx : (⟨(y : G), hYX y.2⟩ : ↥X)
            ∈ (Y ⊓ Y₁).subgroupOf X ⊔ C.subgroupOf X := by
          rw [hsupNC]; trivial
        obtain ⟨n, hn, c, hc, hnc⟩ := (Subgroup.mem_sup_of_normal_right).mp hyx
        have hnN : (n : G) ∈ Y ⊓ Y₁ := Subgroup.mem_subgroupOf.mp hn
        have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
        have hmul : (n : G) * (c : G) = (y : G) := by
          have h := congrArg (fun z : ↥X => (z : G)) hnc
          simpa using h
        have hcY : (c : G) ∈ Y := by
          have h1 : (c : G) = (n : G)⁻¹ * (y : G) := by rw [← hmul]; group
          rw [h1]
          exact Y.mul_mem (Y.inv_mem hnN.1) y.2
        refine ⟨⟨(c : G), hcY⟩, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]; exact ⟨hcY, hcC⟩
        · let nn : ↥Y := ⟨(n : G), hnN.1⟩
          have hnn : nn ∈ (Y ⊓ Y₁).subgroupOf Y := by
            rw [Subgroup.mem_subgroupOf]; simpa [nn] using hnN
          have hπnn : QuotientGroup.mk' ((Y ⊓ Y₁).subgroupOf Y) nn = 1 := by
            rw [QuotientGroup.mk'_apply]
            exact (QuotientGroup.eq_one_iff nn).mpr hnn
          have hnnc : nn * ⟨(c : G), hcY⟩ = y := by
            apply Subtype.ext
            simpa [nn] using hmul
          have hthis : QuotientGroup.mk' ((Y ⊓ Y₁).subgroupOf Y) y
              = QuotientGroup.mk' ((Y ⊓ Y₁).subgroupOf Y) ⟨(c : G), hcY⟩ := by
            rw [← hnnc, map_mul, hπnn, one_mul]
          exact hthis.symm
      have hDmap : ((Y ⊓ C).subgroupOf Y).map
            (QuotientGroup.mk' ((Y ⊓ Y₁).subgroupOf Y)) = ⊤ := by
        rw [Subgroup.eq_top_iff']
        intro g
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((Y ⊓ Y₁).subgroupOf Y) g
        obtain ⟨c, hc, hcy⟩ := hdecomp y
        exact ⟨c, hc, hcy⟩
      have hTop2 : IsPGroup 2 (⊤ : Subgroup (↥Y ⧸ (Y ⊓ Y₁).subgroupOf Y)) :=
        hDmap.symm ▸ hD2.map (QuotientGroup.mk' ((Y ⊓ Y₁).subgroupOf Y))
      have hQ2 : IsPGroup 2 (↥Y ⧸ (Y ⊓ Y₁).subgroupOf Y) :=
        hTop2.of_equiv Subgroup.topEquiv
      have hN'top : (Y ⊓ Y₁).subgroupOf Y = ⊤ :=
        close16_perfect_quot_two hperfY ((Y ⊓ Y₁).subgroupOf Y) hQ2
      have hYleN : Y ≤ Y ⊓ Y₁ := (Subgroup.subgroupOf_eq_top).mp hN'top
      exact hYleN.trans inf_le_right
  have hcard : Nat.card Y₁ ≤ Nat.card Y := by
    rw [hY₁, conjSubgroup]
    exact (Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective).le
  have hconj : conjSubgroup Y m = Y := by
    rw [← hY₁]
    exact (Subgroup.eq_of_le_of_card_ge hYle hcard).symm
  exact conjSubgroup_eq_iff_mem_normalizer.mp hconj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
