module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Data
public import CFSG.Adapters.LieModelSimple
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel classicalTags)

theorem k329_centralizer_le_normalizer {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (hΓ : CFSG.Open.rankThreeGamma 1 3 P ≤ Subgroup.normalizer (X : Set G))
    {x : G} (hxP : x ∈ P) (hx3 : orderOf x = 3) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  intro c hc
  have hz : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.2 hxP
  have hrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
      (CFSG.Open.isElemAbelian_zpowers (p := 3) (by rw [← hx3]; exact pow_orderOf_eq_one x))
      (by rw [Nat.card_zpowers, hx3, pow_one])
  have hn : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤
      CFSG.Open.rankThreeGamma 1 3 P :=
    CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hz hrank
  have hcz : c ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hc
  exact hΓ (hn (Subgroup.centralizer_le_normalizer _ hcz))

private theorem k329cr_mem_Z {K : Type} [Group K] {Z : Subgroup K} [Z.Normal] {w k : K}
    (hk : QuotientGroup.mk k ∈
      Subgroup.centralizer ({(QuotientGroup.mk w : K ⧸ Z)} : Set (K ⧸ Z))) :
    k * w * k⁻¹ * w⁻¹ ∈ Z := by
  have hcomm : QuotientGroup.mk k * QuotientGroup.mk w =
      QuotientGroup.mk w * QuotientGroup.mk k :=
    Subgroup.mem_centralizer_singleton_iff.mp hk
  rw [← QuotientGroup.eq_one_iff]
  rw [show ((k * w * k⁻¹ * w⁻¹ : K) : K ⧸ Z) =
      QuotientGroup.mk k * QuotientGroup.mk w * (QuotientGroup.mk k)⁻¹ *
        (QuotientGroup.mk w)⁻¹ by simp]
  rw [hcomm]
  group

private theorem k329cr_conj_inv {K : Type} [Group K] {Z : Subgroup K} [Z.Normal] {w d z : K}
    (hZ : Z ≤ Subgroup.center K) (hz : z ∈ Z) (hd : d * w * d⁻¹ = z * w) :
    d⁻¹ * w * d = z⁻¹ * w := by
  have hzc : ∀ t : K, t * z = z * t := fun t => Subgroup.mem_center_iff.mp (hZ hz) t
  have h : w = z * (d⁻¹ * w * d) := by
    calc w = d⁻¹ * (d * w * d⁻¹) * d := by group
      _ = d⁻¹ * (z * w) * d := by rw [hd]
      _ = z * (d⁻¹ * w * d) := by simp only [← mul_assoc, hzc]
  have h3 := congrArg (fun t : K => z⁻¹ * t) h
  calc d⁻¹ * w * d = z⁻¹ * (z * (d⁻¹ * w * d)) := by group
    _ = z⁻¹ * w := by rw [h3]

private theorem k329cr_conj_commute {K : Type} [Group K] {Z : Subgroup K} [Z.Normal] {w d c : K}
    (hZ : Z ≤ Subgroup.center K) (hd : d * w * d⁻¹ * w⁻¹ ∈ Z) (hc : c * w = w * c) :
    (d * c * d⁻¹) * w = w * (d * c * d⁻¹) := by
  obtain ⟨z, hz, hdz⟩ : ∃ z ∈ Z, d * w * d⁻¹ = z * w := ⟨_, hd, by group⟩
  have h3 : Commute (d * c * d⁻¹) z :=
    Subgroup.mem_center_iff.mp (hZ hz) (d * c * d⁻¹)
  have h1 : Commute (d * c * d⁻¹) (d * w * d⁻¹) :=
    (show Commute c w from hc).conj d
  have h2 : Commute (d * c * d⁻¹) (z * w) := by simpa [hdz] using h1
  have h4 : Commute (d * c * d⁻¹) w := by
    have h := h3.inv_right.mul_right h2
    simpa [inv_mul_cancel_left] using h
  exact h4.eq

private theorem k329cr_commutator_commute {K : Type} [Group K] {Z : Subgroup K} [Z.Normal]
    {w d c : K} (hZ : Z ≤ Subgroup.center K) (hd : d * w * d⁻¹ * w⁻¹ ∈ Z)
    (hc : c * w * c⁻¹ * w⁻¹ ∈ Z) :
    (d * c * d⁻¹ * c⁻¹) * w = w * (d * c * d⁻¹ * c⁻¹) := by
  obtain ⟨z₁, hz₁, hdz₁⟩ : ∃ z ∈ Z, d * w * d⁻¹ = z * w := ⟨_, hd, by group⟩
  obtain ⟨z₂, hz₂, hdz₂⟩ : ∃ z ∈ Z, c * w * c⁻¹ = z * w := ⟨_, hc, by group⟩
  have hz₁c : ∀ t : K, t * z₁ = z₁ * t := fun t => Subgroup.mem_center_iff.mp (hZ hz₁) t
  have hz₂c : ∀ t : K, t * z₂ = z₂ * t := fun t => Subgroup.mem_center_iff.mp (hZ hz₂) t
  have hz₁inv : ∀ t : K, t * z₁⁻¹ = z₁⁻¹ * t :=
    fun t => Subgroup.mem_center_iff.mp (inv_mem (hZ hz₁)) t
  have hz₂inv : ∀ t : K, t * z₂⁻¹ = z₂⁻¹ * t :=
    fun t => Subgroup.mem_center_iff.mp (inv_mem (hZ hz₂)) t
  have hd₁' : d⁻¹ * w * d = z₁⁻¹ * w := k329cr_conj_inv hZ hz₁ hdz₁
  have hd₂' : c⁻¹ * w * c = z₂⁻¹ * w := k329cr_conj_inv hZ hz₂ hdz₂
  have hprod : z₂⁻¹ * z₁⁻¹ * z₂ * z₁ = 1 := by
    calc z₂⁻¹ * z₁⁻¹ * z₂ * z₁ = z₂⁻¹ * (z₁⁻¹ * z₂) * z₁ := by group
      _ = z₂⁻¹ * (z₂ * z₁⁻¹) * z₁ := by rw [hz₁inv z₂]
      _ = z₂⁻¹ * z₂ * (z₁⁻¹ * z₁) := by group
      _ = 1 := by group
  have hconj : (d * c * d⁻¹ * c⁻¹) * w * (d * c * d⁻¹ * c⁻¹)⁻¹ = w := by
    calc
      (d * c * d⁻¹ * c⁻¹) * w * (d * c * d⁻¹ * c⁻¹)⁻¹
          = d * c * d⁻¹ * (c⁻¹ * w * c) * d * c⁻¹ * d⁻¹ := by group
      _ = d * c * d⁻¹ * (z₂⁻¹ * w) * d * c⁻¹ * d⁻¹ := by rw [hd₂']
      _ = z₂⁻¹ * (d * c * (d⁻¹ * w * d) * c⁻¹ * d⁻¹) := by
            simp only [← mul_assoc, hz₂inv]
      _ = z₂⁻¹ * (d * c * (z₁⁻¹ * w) * c⁻¹ * d⁻¹) := by rw [hd₁']
      _ = z₂⁻¹ * z₁⁻¹ * (d * (c * w * c⁻¹) * d⁻¹) := by
            simp only [← mul_assoc, hz₁inv]
      _ = z₂⁻¹ * z₁⁻¹ * (d * (z₂ * w) * d⁻¹) := by rw [hdz₂]
      _ = z₂⁻¹ * z₁⁻¹ * z₂ * (d * w * d⁻¹) := by
            simp only [← mul_assoc, hz₂c]
      _ = z₂⁻¹ * z₁⁻¹ * z₂ * (z₁ * w) := by rw [hdz₁]
      _ = w := by
            rw [show z₂⁻¹ * z₁⁻¹ * z₂ * (z₁ * w) =
              (z₂⁻¹ * z₁⁻¹ * z₂ * z₁) * w by group, hprod, one_mul]
  have hfin := congrArg (fun t : K => t * (d * c * d⁻¹ * c⁻¹)) hconj
  simpa [mul_assoc] using hfin

theorem k329_commutator_reduction {K : Type} [Group K] (Z : Subgroup K) [Z.Normal]
    (hZ : Z ≤ Subgroup.center K) (w : K) :
    Subgroup.map (QuotientGroup.mk' Z) (Subgroup.centralizer ({w} : Set K)) ≤
        Subgroup.centralizer ({(QuotientGroup.mk w : K ⧸ Z)} : Set (K ⧸ Z)) ∧
      ((Subgroup.map (QuotientGroup.mk' Z) (Subgroup.centralizer ({w} : Set K))).subgroupOf
        (Subgroup.centralizer ({(QuotientGroup.mk w : K ⧸ Z)} : Set (K ⧸ Z)))).Normal ∧
      ⁅Subgroup.centralizer ({(QuotientGroup.mk w : K ⧸ Z)} : Set (K ⧸ Z)),
        Subgroup.centralizer ({(QuotientGroup.mk w : K ⧸ Z)} : Set (K ⧸ Z))⁆ ≤
        Subgroup.map (QuotientGroup.mk' Z) (Subgroup.centralizer ({w} : Set K)) := by
  have hMC : Subgroup.map (QuotientGroup.mk' Z) (Subgroup.centralizer ({w} : Set K)) ≤
      Subgroup.centralizer ({(QuotientGroup.mk w : K ⧸ Z)} : Set (K ⧸ Z)) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    change QuotientGroup.mk' Z c * QuotientGroup.mk' Z w =
      QuotientGroup.mk' Z w * QuotientGroup.mk' Z c
    rw [← map_mul, ← map_mul, hc]
  refine ⟨hMC, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hMC]
    intro m k hm hk
    rw [Subgroup.mem_map] at hm
    obtain ⟨c, hc, rfl⟩ := hm
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective (s := Z) k
    refine Subgroup.mem_map.mpr ⟨d * c * d⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      exact k329cr_conj_commute hZ (k329cr_mem_Z (w := w) (k := d) hk) hc
    · simp [map_mul]
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective (s := Z) a
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective (s := Z) b
    refine Subgroup.mem_map.mpr ⟨d * c * d⁻¹ * c⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact k329cr_commutator_commute hZ
        (k329cr_mem_Z (w := w) (k := d) ha) (k329cr_mem_Z (w := w) (k := c) hb)
    · exact map_commutatorElement (f := QuotientGroup.mk' Z) (g₁ := d) (g₂ := c)

private theorem k329lt_map_centralizer_eq {G : Type} [Group G] (X : Subgroup G) (z₀ : ↥X) :
    (Subgroup.centralizer ({z₀} : Set ↥X)).map X.subtype =
      X ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G) := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨g', hg'c, rfl⟩ := hg
    refine ⟨g'.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst h
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg'c z₀ (by simp)))
  · intro g hg
    rcases hg with ⟨hgX, hgc⟩
    refine Subgroup.mem_map.mpr ⟨⟨g, hgX⟩, ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst h
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc (↑z₀) (by simp)))

private theorem k329lt_inf_centralizer_eq {G : Type} [Group G] {X P : Subgroup G}
    (hPX : P ≤ X) {Q : Sylow 3 ↥X} (hQ : (Q : Subgroup ↥X) = P.subgroupOf X)
    {u₀ : ↥X} (hCu₀ : Subgroup.centralizer ({u₀} : Set ↥X) = (Q : Subgroup ↥X)) :
    X ⊓ Subgroup.centralizer ({(u₀ : G)} : Set G) = P := by
  apply le_antisymm
  · rintro g ⟨hgX, hgc⟩
    have hg'Q : (⟨g, hgX⟩ : ↥X) ∈ (Q : Subgroup ↥X) := by
      rw [← hCu₀]
      exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        subst h
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc (↑u₀) (by simp)))
    have hg'Q' : (⟨g, hgX⟩ : ↥X) ∈ P.subgroupOf X := by
      rw [← hQ]; exact hg'Q
    exact Subgroup.mem_subgroupOf.mp hg'Q'
  · intro g hgP
    have hgX : g ∈ X := hPX hgP
    refine ⟨hgX, ?_⟩
    have hg'Q : (⟨g, hgX⟩ : ↥X) ∈ (Q : Subgroup ↥X) := by
      rw [hQ]
      exact Subgroup.mem_subgroupOf.mpr hgP
    have hg'c : (⟨g, hgX⟩ : ↥X) ∈ Subgroup.centralizer ({u₀} : Set ↥X) := by
      rw [hCu₀]; exact hg'Q
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst h
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg'c u₀ (by simp)))

private theorem k329lt_lieModel_commutator_map {G : Type} [Group G] {X : Subgroup G}
    (z₀ : ↥X)
    (hY : LieModel ↥⁅Subgroup.centralizer ({z₀} : Set ↥X),
        Subgroup.centralizer ({z₀} : Set ↥X)⁆ .PSL 2 2 3) :
    LieModel ↥⁅X ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G),
        X ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G)⁆ .PSL 2 2 3 := by
  have hmap := k329lt_map_centralizer_eq X z₀
  have hcomm : (⁅Subgroup.centralizer ({z₀} : Set ↥X),
      Subgroup.centralizer ({z₀} : Set ↥X)⁆).map X.subtype =
      ⁅X ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G),
        X ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G)⁆ := by
    rw [Subgroup.map_commutator, hmap]
  exact hcomm ▸ LieModel.of_mulEquiv
    (Subgroup.equivMapOfInjective ⁅Subgroup.centralizer ({z₀} : Set ↥X),
      Subgroup.centralizer ({z₀} : Set ↥X)⁆ X.subtype X.subtype_injective) hY

theorem k329_leafA_transport {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (hA : k329U38LocalFactsStatement) (hX : LieModel ↥X .PSU 3 2 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X) :
    (∃ u ∈ P, orderOf u = 3 ∧ X ⊓ Subgroup.centralizer ({u} : Set G) = P ∧
        ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) ∧
      ∃ z ∈ P, orderOf z = 3 ∧
        LieModel ↥⁅X ⊓ Subgroup.centralizer ({z} : Set G),
          X ⊓ Subgroup.centralizer ({z} : Set G)⁆ .PSL 2 2 3 := by
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hPX : P ≤ X := hP.le
  obtain ⟨⟨u₀, hu₀Q, hu₀3, hCu₀, a₀, ha₀Q, b₀, hb₀Q, hab₀⟩,
      ⟨z₀, hz₀Q, hz₀3, hY₀⟩⟩ := hA ↥X hX Q
  have hu₀P : (u₀ : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp (by rw [← hQ]; exact hu₀Q)
  have hz₀P : (z₀ : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp (by rw [← hQ]; exact hz₀Q)
  have ha₀P : (a₀ : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp (by rw [← hQ]; exact ha₀Q)
  have hb₀P : (b₀ : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp (by rw [← hQ]; exact hb₀Q)
  constructor
  · exact ⟨(u₀ : G), hu₀P, by rw [Subgroup.orderOf_coe]; exact hu₀3,
      k329lt_inf_centralizer_eq hPX hQ hCu₀,
      ⟨(a₀ : G), ha₀P, (b₀ : G), hb₀P, fun h => hab₀ (Subtype.ext h)⟩⟩
  · exact ⟨(z₀ : G), hz₀P, by rw [Subgroup.orderOf_coe]; exact hz₀3,
      k329lt_lieModel_commutator_map z₀ hY₀⟩

private theorem k329ud_inf_center_eq_bot {G : Type*} [Group G] {K X P : Subgroup G}
    (hXK : X ≤ K) (hXs : IsSimpleGroup ↥X) (hPX : P ≤ X)
    (hPna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) :
    X.subgroupOf K ⊓ Subgroup.center ↥K = ⊥ := by
  let X' : Subgroup ↥K := X.subgroupOf K
  let Z : Subgroup ↥K := Subgroup.center ↥K
  have hinstX : IsSimpleGroup ↥X := hXs
  have hinstX' : IsSimpleGroup X' := (Subgroup.subgroupOfEquivOfLe hXK).isSimpleGroup
  have hnormal : ((X' ⊓ Z).subgroupOf X').Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    infer_instance
  have hinstN : ((X' ⊓ Z).subgroupOf X').Normal := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((X' ⊓ Z).subgroupOf X') with h | h
  · rw [eq_bot_iff]
    intro x hx
    have hx1 : (⟨x, hx.1⟩ : X') ∈ (X' ⊓ Z).subgroupOf X' := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    rw [h, Subgroup.mem_bot] at hx1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx1
  · have hXZ : X' ≤ Z := (Subgroup.subgroupOf_eq_top.mp h).trans inf_le_right
    obtain ⟨a, haP, b, hbP, hab⟩ := hPna
    have haX : a ∈ X := hPX haP
    have hbX : b ∈ X := hPX hbP
    have haZ : (⟨a, hXK haX⟩ : ↥K) ∈ Z := hXZ (by rw [Subgroup.mem_subgroupOf]; exact haX)
    have hbZ : (⟨b, hXK hbX⟩ : ↥K) ∈ Z := hXZ (by rw [Subgroup.mem_subgroupOf]; exact hbX)
    have hcomm : (⟨b, hXK hbX⟩ : ↥K) * ⟨a, hXK haX⟩ = ⟨a, hXK haX⟩ * ⟨b, hXK hbX⟩ :=
      (Subgroup.mem_center_iff.mp haZ) ⟨b, hXK hbX⟩
    have hba : b * a = a * b := by
      simpa using congrArg Subtype.val hcomm
    exact (hab hba.symm).elim

private theorem k329ud_pi_injective {G : Type*} [Group G] {K X : Subgroup G}
    (hXbot : X.subgroupOf K ⊓ Subgroup.center ↥K = ⊥) :
    Function.Injective
      ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype) := by
  let X' : Subgroup ↥K := X.subgroupOf K
  let Z : Subgroup ↥K := Subgroup.center ↥K
  have hbot : X' ⊓ Z = ⊥ := hXbot
  intro a b hab
  have hf : ((a : ↥K) * (b : ↥K)⁻¹ : ↥K ⧸ Z) = 1 := by
    show (QuotientGroup.mk' Z) ((a : ↥K) * (b : ↥K)⁻¹) = 1
    have hab' : (QuotientGroup.mk' Z) (a : ↥K) = (QuotientGroup.mk' Z) (b : ↥K) := hab
    rw [map_mul, map_inv, hab', mul_inv_cancel]
  have hcent : (a : ↥K) * (b : ↥K)⁻¹ ∈ Z := (QuotientGroup.eq_one_iff _).mp hf
  have hmem : (a : ↥K) * (b : ↥K)⁻¹ ∈ X' ⊓ Z :=
    ⟨X'.mul_mem a.2 (X'.inv_mem b.2), hcent⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply Subtype.ext
  have := congrArg (fun t : ↥K => t * (b : ↥K)) hmem
  simpa using this

private theorem k329ud_orderOf {G : Type*} [Group G] {K X : Subgroup G} {u : G}
    (huX : u ∈ X) (huK : u ∈ K)
    (hinj : Function.Injective
      ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype))
    (hu3 : orderOf u = 3) :
    orderOf ((QuotientGroup.mk' (Subgroup.center ↥K)) (⟨u, huK⟩ : ↥K)) = 3 := by
  let Z : Subgroup ↥K := Subgroup.center ↥K
  let X' : Subgroup ↥K := X.subgroupOf K
  change orderOf (((QuotientGroup.mk' Z).comp X'.subtype)
    (⟨⟨u, huK⟩, by rw [Subgroup.mem_subgroupOf]; exact huX⟩ : X')) = 3
  rw [orderOf_injective _ hinj, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  exact hu3

private theorem k329ud_Pprime_le_centralizer {G : Type*} [Group G]
    {K X P : Subgroup G} {u : G} (huK : u ∈ K)
    (hCu : X ⊓ Subgroup.centralizer ({u} : Set G) = P) :
    P.subgroupOf K ≤ Subgroup.centralizer ({(⟨u, huK⟩ : ↥K)} : Set ↥K) := by
  intro p hp
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hpP : (p : G) ∈ P := hp
  have hpC : (p : G) ∈ Subgroup.centralizer ({u} : Set G) := by
    have h : (p : G) ∈ X ⊓ Subgroup.centralizer ({u} : Set G) := by
      rw [hCu]; exact hpP
    exact h.2
  simpa using Subgroup.mem_centralizer_singleton_iff.mp hpC

private theorem k329ud_Pprime_normal_centralizer {G : Type*} [Group G]
    {K X P : Subgroup G} {u : G} (huK : u ∈ K) (hPX : P ≤ X)
    (hCu : X ⊓ Subgroup.centralizer ({u} : Set G) = P)
    (hN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    ((P.subgroupOf K).subgroupOf
      (Subgroup.centralizer ({(⟨u, huK⟩ : ↥K)} : Set ↥K))).Normal := by
  let C : Subgroup ↥K := Subgroup.centralizer ({(⟨u, huK⟩ : ↥K)} : Set ↥K)
  have hle : P.subgroupOf K ≤ C := k329ud_Pprime_le_centralizer huK hCu
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro p c hp hc
  have hpP : (p : G) ∈ P := hp
  have hpX : (p : G) ∈ X := hPX hpP
  have hpC : (p : G) ∈ Subgroup.centralizer ({u} : Set G) := by
    have h : (p : G) ∈ X ⊓ Subgroup.centralizer ({u} : Set G) := by
      rw [hCu]; exact hpP
    exact h.2
  have hcC : (c : G) ∈ Subgroup.centralizer ({u} : Set G) := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using congrArg Subtype.val this)
  have hcN : (c : G) ∈ Subgroup.normalizer (X : Set G) := hN hcC
  have hconjX : (c : G) * (p : G) * (c : G)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hcN (p : G)).mp hpX
  have hconjC : (c : G) * (p : G) * (c : G)⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcm : Commute (c : G) u := Subgroup.mem_centralizer_singleton_iff.mp hcC
    have hpm : Commute (p : G) u := Subgroup.mem_centralizer_singleton_iff.mp hpC
    have hconj : Commute ((c : G) * (p : G) * (c : G)⁻¹) u := by
      have h1 : Commute ((c : G) * (p : G)) u := hcm.mul_left hpm
      have h2 : Commute ((c : G)⁻¹) u := hcm.inv_left
      simpa [mul_assoc] using h1.mul_left h2
    exact hconj
  have hmem : (c : G) * (p : G) * (c : G)⁻¹ ∈
      X ⊓ Subgroup.centralizer ({u} : Set G) := ⟨hconjX, hconjC⟩
  rw [hCu] at hmem
  rw [Subgroup.mem_subgroupOf]
  exact hmem

private theorem k329ud_map_nonabelian {G : Type*} [Group G] {K X P : Subgroup G}
    (hXK : X ≤ K) (hPX : P ≤ X)
    (hinj : Function.Injective
      ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype))
    (hPna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) :
    ∃ a ∈ Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K)) (P.subgroupOf K),
      ∃ b ∈ Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K)) (P.subgroupOf K),
        a * b ≠ b * a := by
  let Z : Subgroup ↥K := Subgroup.center ↥K
  obtain ⟨a, haP, b, hbP, hab⟩ := hPna
  have haX : a ∈ X := hPX haP
  have hbX : b ∈ X := hPX hbP
  have haK : a ∈ K := hXK haX
  have hbK : b ∈ K := hXK hbX
  refine ⟨QuotientGroup.mk' Z (⟨a, haK⟩ : ↥K), ?_,
    QuotientGroup.mk' Z (⟨b, hbK⟩ : ↥K), ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨⟨a, haK⟩, by rw [Subgroup.mem_subgroupOf]; exact haP, rfl⟩
  · exact Subgroup.mem_map.mpr ⟨⟨b, hbK⟩, by rw [Subgroup.mem_subgroupOf]; exact hbP, rfl⟩
  · intro h
    have h' : ((QuotientGroup.mk' Z).comp (X.subgroupOf K).subtype)
          ((⟨⟨a, haK⟩, by rw [Subgroup.mem_subgroupOf]; exact haX⟩ : X.subgroupOf K) *
            ⟨⟨b, hbK⟩, by rw [Subgroup.mem_subgroupOf]; exact hbX⟩) =
        ((QuotientGroup.mk' Z).comp (X.subgroupOf K).subtype)
          ((⟨⟨b, hbK⟩, by rw [Subgroup.mem_subgroupOf]; exact hbX⟩ : X.subgroupOf K) *
            ⟨⟨a, haK⟩, by rw [Subgroup.mem_subgroupOf]; exact haX⟩) := by
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul] using h
    have heq := hinj h'
    have hval : (⟨a, haK⟩ : ↥K) * ⟨b, hbK⟩ = ⟨b, hbK⟩ * ⟨a, haK⟩ :=
      congrArg Subtype.val heq
    have hab' : a * b = b * a := by simpa using congrArg Subtype.val hval
    exact hab hab'

private theorem k329ud_core {G : Type} [Group G] [Finite G] {K X P : Subgroup G}
    (hXK : X ≤ K) (hXs : IsSimpleGroup ↥X) (hPX : P ≤ X) (hP3 : IsPGroup 3 P)
    {u : G} (huP : u ∈ P) (hu3 : orderOf u = 3)
    (hCu : X ⊓ Subgroup.centralizer ({u} : Set G) = P)
    (hPna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    (hN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hcomm : Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K))
          (Subgroup.centralizer ({(⟨u, hXK (hPX huP)⟩ : ↥K)} : Set ↥K)) ≤
        Subgroup.centralizer
          ({(QuotientGroup.mk' (Subgroup.center ↥K) (⟨u, hXK (hPX huP)⟩ : ↥K))} :
            Set (↥K ⧸ Subgroup.center ↥K)) ∧
      ((Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K))
          (Subgroup.centralizer ({(⟨u, hXK (hPX huP)⟩ : ↥K)} : Set ↥K))).subgroupOf
        (Subgroup.centralizer
          ({(QuotientGroup.mk' (Subgroup.center ↥K) (⟨u, hXK (hPX huP)⟩ : ↥K))} :
            Set (↥K ⧸ Subgroup.center ↥K)))).Normal) :
    K329UDatum (↥K ⧸ Subgroup.center ↥K)
      (QuotientGroup.mk' (Subgroup.center ↥K) (⟨u, hXK (hPX huP)⟩ : ↥K)) := by
  let Z : Subgroup ↥K := Subgroup.center ↥K
  let X' : Subgroup ↥K := X.subgroupOf K
  let P' : Subgroup ↥K := P.subgroupOf K
  let C : Subgroup ↥K := Subgroup.centralizer ({(⟨u, hXK (hPX huP)⟩ : ↥K)} : Set ↥K)
  let M := Subgroup.map (QuotientGroup.mk' Z) C
  let N := Subgroup.map (QuotientGroup.mk' Z) P'
  have hbot : X' ⊓ Z = ⊥ := k329ud_inf_center_eq_bot hXK hXs hPX hPna
  have hinj : Function.Injective ((QuotientGroup.mk' Z).comp X'.subtype) :=
    k329ud_pi_injective hbot
  have horder : orderOf (QuotientGroup.mk' Z (⟨u, hXK (hPX huP)⟩ : ↥K)) = 3 :=
    k329ud_orderOf (hPX huP) (hXK (hPX huP)) hinj hu3
  have hP'C : P' ≤ C := k329ud_Pprime_le_centralizer (hXK (hPX huP)) hCu
  have hNM : N ≤ M := Subgroup.map_mono hP'C
  have hP'N : (P'.subgroupOf C).Normal :=
    k329ud_Pprime_normal_centralizer (hXK (hPX huP)) hPX hCu hN
  have hNnormal : (N.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNM]
    intro n m hn hm
    rw [Subgroup.mem_map] at hn hm ⊢
    obtain ⟨p, hp, rfl⟩ := hn
    obtain ⟨c, hc, rfl⟩ := hm
    refine ⟨c * p * c⁻¹, ?_, ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff hP'C).mp hP'N p c hp hc
    · simp [map_mul]
  have hN3 : IsPGroup 3 N := (hP3.comap_subtype).map (QuotientGroup.mk' Z)
  have hNna : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a :=
    k329ud_map_nonabelian hXK hPX hinj hPna
  exact ⟨horder, M, N, hcomm.1, hcomm.2, hNM, hNnormal, hN3, hNna⟩

theorem k329_uDatum_of_centralizer {G : Type} [Group G] [Finite G] {X P : Subgroup G}
    (hXK : X ≤ CFSG.Open.genFittingFStar G) (hXs : IsSimpleGroup ↥X) (hPX : P ≤ X)
    (hP3 : IsPGroup 3 P) {u : G} (huP : u ∈ P) (hu3 : orderOf u = 3)
    (hCu : X ⊓ Subgroup.centralizer ({u} : Set G) = P)
    (hPna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    (hN : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    K329UDatum (↥(CFSG.Open.genFittingFStar G) ⧸ Subgroup.center ↥(CFSG.Open.genFittingFStar G))
      (QuotientGroup.mk ⟨u, hXK (hPX huP)⟩) := by
  have hcr := k329_commutator_reduction (Subgroup.center ↥(CFSG.Open.genFittingFStar G)) le_rfl
    ⟨u, hXK (hPX huP)⟩
  exact k329ud_core hXK hXs hPX hP3 huP hu3 hCu hPna hN ⟨hcr.1, hcr.2.1⟩

private theorem k329zd_pi_injective {G : Type} [Group G] {K X : Subgroup G}
    (hXK : X ≤ K) (hXs : IsSimpleGroup ↥X) (hXna : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype) := by
  have hXs' : IsSimpleGroup ↥(X.subgroupOf K) :=
    (Subgroup.subgroupOfEquivOfLe hXK).isSimpleGroup
  have hker : (Subgroup.center ↥K).subgroupOf (X.subgroupOf K) = ⊥ := by
    rcases hXs'.eq_bot_or_eq_top_of_normal
        ((Subgroup.center ↥K).subgroupOf (X.subgroupOf K)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hXna
      have haK : a ∈ K := hXK ha
      have hbK : b ∈ K := hXK hb
      have hA : (⟨⟨a, haK⟩, ha⟩ : X.subgroupOf K) ∈
          (Subgroup.center ↥K).subgroupOf (X.subgroupOf K) := by
        rw [h]; exact Subgroup.mem_top _
      have hB : (⟨⟨b, hbK⟩, hb⟩ : X.subgroupOf K) ∈
          (Subgroup.center ↥K).subgroupOf (X.subgroupOf K) := by
        rw [h]; exact Subgroup.mem_top _
      rw [Subgroup.mem_subgroupOf] at hA hB
      have hcomm : (⟨a, haK⟩ : ↥K) * ⟨b, hbK⟩ = ⟨b, hbK⟩ * ⟨a, haK⟩ :=
        Subgroup.mem_center_iff.mp hB _
      exact hab (by simpa using congrArg Subtype.val hcomm)
  rw [← MonoidHom.ker_eq_bot_iff]
  have hker_comp : ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype).ker =
      (Subgroup.center ↥K).subgroupOf (X.subgroupOf K) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype]
  rw [hker_comp]
  exact hker

private theorem k329zd_order {G : Type} [Group G] {K X : Subgroup G} {z : G}
    (hXK : X ≤ K) (hXs : IsSimpleGroup ↥X) (hXna : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a)
    (hzX : z ∈ X) (hz3 : orderOf z = 3) :
    orderOf ((QuotientGroup.mk' (Subgroup.center ↥K)) ⟨z, hXK hzX⟩) = 3 := by
  have hinj := k329zd_pi_injective hXK hXs hXna
  let x : X.subgroupOf K := ⟨⟨z, hXK hzX⟩, hzX⟩
  have h1 : orderOf ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype x) =
      orderOf x := orderOf_injective _ hinj x
  have h2 : orderOf x = orderOf z := by
    calc orderOf x = orderOf (x : ↥K) := (Subgroup.orderOf_coe x).symm
      _ = orderOf (⟨z, hXK hzX⟩ : ↥K) := rfl
      _ = orderOf z := Subgroup.orderOf_mk z (hXK hzX)
  have h3 : ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (X.subgroupOf K).subtype x) =
      QuotientGroup.mk' (Subgroup.center ↥K) (⟨z, hXK hzX⟩ : ↥K) := rfl
  rw [← h3, h1, h2, hz3]

private theorem k329zd_Y0_le_CK {G : Type} [Group G] {K X : Subgroup G} {z : G}
    (hXK : X ≤ K) (hzX : z ∈ X) :
    (⁅X ⊓ Subgroup.centralizer ({z} : Set G),
      X ⊓ Subgroup.centralizer ({z} : Set G)⁆).subgroupOf K ≤
      Subgroup.centralizer ({⟨z, hXK hzX⟩} : Set ↥K) := by
  intro y hy
  rw [Subgroup.mem_subgroupOf] at hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hyC : (y : G) ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.commutator_le_of_le inf_le_right inf_le_right hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hyC
  exact Subtype.ext hyC

private theorem k329zd_conj_mem_A {G : Type} [Group G] {K X : Subgroup G} {z : G}
    (hXK : X ≤ K) (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hzX : z ∈ X) {g : ↥K}
    (hg : g ∈ Subgroup.centralizer ({⟨z, hXK hzX⟩} : Set ↥K)) :
    ∀ a ∈ X ⊓ Subgroup.centralizer ({z} : Set G),
      (g : G) * a * (g : G)⁻¹ ∈ X ⊓ Subgroup.centralizer ({z} : Set G) := by
  intro a ha
  rcases Subgroup.mem_inf.mp ha with ⟨haX, haC⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hg_NX : (g : G) ∈ Subgroup.normalizer (X : Set G) := by
      apply hN
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hg)
    exact (Subgroup.mem_normalizer_iff.mp hg_NX a).mp haX
  · rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at haC
    have hgC : (g : G) * z = z * (g : G) :=
      Subtype.ext_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hg)
    calc (g : G) * a * (g : G)⁻¹ * z
        = (g : G) * a * ((g : G)⁻¹ * z) := by group
      _ = (g : G) * a * (z * (g : G)⁻¹) := by
            rw [show (g : G)⁻¹ * z = z * (g : G)⁻¹ from by
              calc (g : G)⁻¹ * z
                  = (g : G)⁻¹ * z * (g : G) * (g : G)⁻¹ := by group
                _ = (g : G)⁻¹ * (z * (g : G)) * (g : G)⁻¹ := by group
                _ = (g : G)⁻¹ * ((g : G) * z) * (g : G)⁻¹ := by rw [← hgC]
                _ = z * (g : G)⁻¹ := by group]
      _ = (g : G) * (a * z) * (g : G)⁻¹ := by group
      _ = (g : G) * (z * a) * (g : G)⁻¹ := by rw [haC]
      _ = z * ((g : G) * a * (g : G)⁻¹) := by
            rw [show (g : G) * (z * a) * (g : G)⁻¹ = ((g : G) * z) * a * (g : G)⁻¹ from by group]
            rw [hgC]
            group

private theorem k329zd_Y0_normal_in_CK {G : Type} [Group G] {K X : Subgroup G} {z : G}
    (hXK : X ≤ K) (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hzX : z ∈ X) :
    (((⁅X ⊓ Subgroup.centralizer ({z} : Set G),
        X ⊓ Subgroup.centralizer ({z} : Set G)⁆).subgroupOf K).subgroupOf
      (Subgroup.centralizer ({⟨z, hXK hzX⟩} : Set ↥K))).Normal := by
  let A : Subgroup G := X ⊓ Subgroup.centralizer ({z} : Set G)
  let Y₀ : Subgroup G := ⁅A, A⁆
  let Y₀' : Subgroup ↥K := Y₀.subgroupOf K
  let C : Subgroup ↥K := Subgroup.centralizer ({⟨z, hXK hzX⟩} : Set ↥K)
  have hY0'_le_C : Y₀' ≤ C := k329zd_Y0_le_CK hXK hzX
  rw [Subgroup.normal_subgroupOf_iff hY0'_le_C]
  intro h k hh hk
  have hk_normalizer_A : (k : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact k329zd_conj_mem_A hXK hN hzX hk a
    · intro ha
      have hk_inv : k⁻¹ ∈ C := C.inv_mem hk
      have h := k329zd_conj_mem_A hXK hN hzX hk_inv ((k : G) * a * (k : G)⁻¹) ha
      change a ∈ X ⊓ Subgroup.centralizer ({z} : Set G)
      simpa [mul_assoc] using h
  have hY0_map : Y₀.map (MulAut.conj (k : G)) = Y₀ := by
    rw [show Y₀ = ⁅A, A⁆ from rfl, Subgroup.map_commutator]
    congr 1
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hk_normalizer_A
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hk_normalizer_A
  rw [Subgroup.mem_subgroupOf]
  have hmem : ((k : G) * (h : G) * (k : G)⁻¹) ∈ Y₀.map (MulAut.conj (k : G)) := by
    rw [Subgroup.mem_map]
    exact ⟨(h : G), hh, rfl⟩
  rw [hY0_map] at hmem
  simpa using hmem

private theorem k329zd_Y_lieModel {G : Type} [Group G] {K X : Subgroup G} {z : G}
    (hXK : X ≤ K) (hXs : IsSimpleGroup ↥X) (hXna : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a)
    (hY : LieModel ↥⁅X ⊓ Subgroup.centralizer ({z} : Set G),
      X ⊓ Subgroup.centralizer ({z} : Set G)⁆ .PSL 2 2 3) :
    LieModel ↥(Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K))
        (Subgroup.subgroupOf ⁅X ⊓ Subgroup.centralizer ({z} : Set G),
          X ⊓ Subgroup.centralizer ({z} : Set G)⁆ K)) .PSL 2 2 3 := by
  let A : Subgroup G := X ⊓ Subgroup.centralizer ({z} : Set G)
  let Y₀ : Subgroup G := ⁅A, A⁆
  let Y₀' : Subgroup ↥K := Y₀.subgroupOf K
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  let Y : Subgroup (↥K ⧸ Subgroup.center ↥K) := Y₀'.map π
  have hY0_le_X : Y₀ ≤ X := Subgroup.commutator_le_of_le inf_le_left inf_le_left
  have hY0K : Y₀ ≤ K := le_trans hY0_le_X hXK
  have hY0'_le_X' : Y₀' ≤ X.subgroupOf K := Subgroup.subgroupOf_mono K hY0_le_X
  have hinj : Function.Injective (π.comp (X.subgroupOf K).subtype) :=
    k329zd_pi_injective hXK hXs hXna
  let φ : Y₀' →* Y :=
    { toFun := fun y => ⟨π (y : ↥K), Subgroup.mem_map.mpr ⟨(y : ↥K), y.2, rfl⟩⟩
      map_one' := by ext; simp [π]
      map_mul' := by intro x y; ext; simp [π, map_mul] }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have h : π (x : ↥K) = π (y : ↥K) := congrArg Subtype.val hxy
    have hxX : (x : ↥K) ∈ X.subgroupOf K := hY0'_le_X' x.2
    have hyX : (y : ↥K) ∈ X.subgroupOf K := hY0'_le_X' y.2
    have hx' : (⟨(x : ↥K), hxX⟩ : X.subgroupOf K) = ⟨(y : ↥K), hyX⟩ := by
      apply hinj
      simpa [π] using h
    exact Subtype.ext (congrArg (fun t : X.subgroupOf K => (t : ↥K)) hx')
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : Y₀' ≃* Y := MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  exact LieModel.of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hY0K).symm.trans e) hY

private theorem k329zd_zDatum_core {G : Type} [Group G] [Finite G] {K X : Subgroup G}
    (hXK : X ≤ K) (hXs : IsSimpleGroup ↥X)
    (hXna : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) {z : G} (hzX : z ∈ X) (hz3 : orderOf z = 3)
    (hY : LieModel ↥⁅X ⊓ Subgroup.centralizer ({z} : Set G),
      X ⊓ Subgroup.centralizer ({z} : Set G)⁆ .PSL 2 2 3)
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hcomm : Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K))
        (Subgroup.centralizer ({⟨z, hXK hzX⟩} : Set ↥K)) ≤
        Subgroup.centralizer ({(QuotientGroup.mk ⟨z, hXK hzX⟩ : ↥K ⧸ Subgroup.center ↥K)} : Set _) ∧
      ((Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K))
        (Subgroup.centralizer ({⟨z, hXK hzX⟩} : Set ↥K))).subgroupOf
        (Subgroup.centralizer ({(QuotientGroup.mk ⟨z, hXK hzX⟩ : ↥K ⧸ Subgroup.center ↥K)} : Set _))).Normal ∧
      ⁅Subgroup.centralizer ({(QuotientGroup.mk ⟨z, hXK hzX⟩ : ↥K ⧸ Subgroup.center ↥K)} : Set _),
        Subgroup.centralizer ({(QuotientGroup.mk ⟨z, hXK hzX⟩ : ↥K ⧸ Subgroup.center ↥K)} : Set _)⁆ ≤
        Subgroup.map (QuotientGroup.mk' (Subgroup.center ↥K))
        (Subgroup.centralizer ({⟨z, hXK hzX⟩} : Set ↥K))) :
    K329ZDatum (↥K ⧸ Subgroup.center ↥K) (QuotientGroup.mk ⟨z, hXK hzX⟩) := by
  let A : Subgroup G := X ⊓ Subgroup.centralizer ({z} : Set G)
  let Y₀ : Subgroup G := ⁅A, A⁆
  let Y₀' : Subgroup ↥K := Y₀.subgroupOf K
  let C : Subgroup ↥K := Subgroup.centralizer ({⟨z, hXK hzX⟩} : Set ↥K)
  let π : ↥K →* (↥K ⧸ Subgroup.center ↥K) := QuotientGroup.mk' (Subgroup.center ↥K)
  let M : Subgroup (↥K ⧸ Subgroup.center ↥K) := C.map π
  let Y : Subgroup (↥K ⧸ Subgroup.center ↥K) := Y₀'.map π
  have hY0'_le_C : Y₀' ≤ C := k329zd_Y0_le_CK hXK hzX
  have hY0'_normal : (Y₀'.subgroupOf C).Normal := k329zd_Y0_normal_in_CK hXK hN hzX
  have hY_le_M : Y ≤ M := Subgroup.map_mono hY0'_le_C
  have hY_normal : (Y.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hY_le_M]
    intro y m hy hm
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hm
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_inv, ← map_mul]
    refine Subgroup.mem_map.mpr ⟨c * y' * c⁻¹, ?_, rfl⟩
    exact (Subgroup.normal_subgroupOf_iff hY0'_le_C).mp hY0'_normal y' c hy' hc
  exact ⟨k329zd_order hXK hXs hXna hzX hz3, M, Y, hcomm.1, hcomm.2.1, hcomm.2.2,
    hY_le_M, hY_normal, k329zd_Y_lieModel hXK hXs hXna hY⟩

theorem k329_zDatum_of_centralizer {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hXK : X ≤ CFSG.Open.genFittingFStar G) (hXs : IsSimpleGroup ↥X)
    (hXna : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) {z : G} (hzX : z ∈ X) (hz3 : orderOf z = 3)
    (hY : LieModel ↥⁅X ⊓ Subgroup.centralizer ({z} : Set G),
      X ⊓ Subgroup.centralizer ({z} : Set G)⁆ .PSL 2 2 3)
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    K329ZDatum (↥(CFSG.Open.genFittingFStar G) ⧸ Subgroup.center ↥(CFSG.Open.genFittingFStar G))
      (QuotientGroup.mk ⟨z, hXK hzX⟩) := by
  exact k329zd_zDatum_core hXK hXs hXna hzX hz3 hY hN
    (k329_commutator_reduction (Subgroup.center ↥(CFSG.Open.genFittingFStar G)) le_rfl
      ⟨z, hXK hzX⟩)

theorem k329TwoCentralizerReduction_of_parts :
    k329U38LocalFactsStatement →
    ∀ (G : Type) [Group G] [Finite G],
      CFSG.Open.IsQuasisimple ↥(CFSG.Open.genFittingFStar G) →
      ∀ X P : Subgroup G, X ≤ CFSG.Open.genFittingFStar G → LieModel ↥X .PSU 3 2 3 →
        CFSG.ABGLocalTools.IsSylowOf 3 P X →
        CFSG.Open.rankThreeGamma 1 3 P ≤ Subgroup.normalizer (X : Set G) →
        (∃ u, K329UDatum (↥(CFSG.Open.genFittingFStar G) ⧸
            Subgroup.center ↥(CFSG.Open.genFittingFStar G)) u) ∧
          ∃ z, K329ZDatum (↥(CFSG.Open.genFittingFStar G) ⧸
            Subgroup.center ↥(CFSG.Open.genFittingFStar G)) z := by
  intro hA G _ _ _ X P hXK hX hP hΓ
  obtain ⟨⟨u, huP, hu3, hCu, hPna⟩, ⟨z, hzP, hz3, hY⟩⟩ := k329_leafA_transport hA hX hP
  have hXs : IsSimpleGroup ↥X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
      (by simp [CFSG.Blueprint.classicalTags]) hX
  have hPX : P ≤ X := hP.le
  obtain ⟨a, ha, b, hb, hab⟩ := hPna
  exact ⟨⟨_, k329_uDatum_of_centralizer hXK hXs hPX hP.isPGroup huP hu3 hCu
      ⟨a, ha, b, hb, hab⟩ (k329_centralizer_le_normalizer hΓ huP hu3)⟩,
    ⟨_, k329_zDatum_of_centralizer hXK hXs ⟨a, hPX ha, b, hPX hb, hab⟩ (hPX hzP) hz3 hY
      (k329_centralizer_le_normalizer hΓ hzP hz3)⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
