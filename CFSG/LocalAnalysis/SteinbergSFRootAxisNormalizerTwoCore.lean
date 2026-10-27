module

public import CFSG.LocalAnalysis.SteinbergSFCentralInvolutionFusion
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
public import CFSG.LocalAnalysis.SteinbergCDAffineSharplyTwoTransitive
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace RootAxisTwoCore

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.LocalAnalysis.SteinbergCD

section General

variable {G : Type*} [Group G]

theorem conj_mem_sup {H₁ H₂ : Subgroup G} {g : G} (h₁ : ∀ x ∈ H₁, g * x * g⁻¹ ∈ H₁)
    (h₂ : ∀ x ∈ H₂, g * x * g⁻¹ ∈ H₂) {x : G} (hx : x ∈ H₁ ⊔ H₂) : g * x * g⁻¹ ∈ H₁ ⊔ H₂ := by
  have hle : H₁ ⊔ H₂ ≤ (H₁ ⊔ H₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun y hy => mem_sup_left (h₁ y hy)) fun y hy => mem_sup_right (h₂ y hy)
  exact hle hx

theorem pCore_map_eq {p : ℕ} {H S : Subgroup G} (hSH : S ≤ H)
    (hSn : ∀ h ∈ H, ∀ s ∈ S, h * s * h⁻¹ ∈ S) (hSp : IsPGroup p S)
    (hmax : ∀ R : Subgroup G, R ≤ H → (∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) → IsPGroup p R →
      R ≤ S) :
    (CFSG.pCore p H).map H.subtype = S := by
  apply le_antisymm
  · refine hmax _ (map_subtype_le _) ?_ (CFSG.pCore_isPGroup.map _)
    rintro h hh _ ⟨r, hr, rfl⟩
    exact ⟨⟨h, hh⟩ * r * ⟨h, hh⟩⁻¹, CFSG.pCore_normal.conj_mem r hr ⟨h, hh⟩, rfl⟩
  · have hn : (S.subgroupOf H).Normal := ⟨fun s hs h => by
      rw [mem_subgroupOf] at hs ⊢
      exact hSn h h.2 s hs⟩
    have hle : S.subgroupOf H ≤ CFSG.pCore p H :=
      le_sSup ⟨hn, hSp.of_equiv (subgroupOfEquivOfLe hSH).symm⟩
    intro s hs
    exact ⟨⟨s, hSH hs⟩, hle (mem_subgroupOf.mpr hs), rfl⟩

theorem zpow_eq_one_or_eq {t : G} (htt : t * t = 1) (j : ℤ) : t ^ j = 1 ∨ t ^ j = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  rcases Int.even_or_odd' j with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem mem_zpowers_sup_iff {t : G} (htt : t * t = 1) {W : Subgroup G}
    (hc : ∀ w ∈ W, t * w = w * t) {x : G} : x ∈ zpowers t ⊔ W ↔ x ∈ W ∨ t * x ∈ W := by
  have hc' : ∀ y ∈ zpowers t, ∀ w ∈ W, y * w = w * y := by
    rintro _ ⟨j, rfl⟩ w hw
    exact (Commute.zpow_left (hc w hw) j).eq
  constructor
  · intro hx
    obtain ⟨y, hy, w, hw, rfl⟩ := (mem_sup_of_commute hc').mp hx
    have hy' : y = 1 ∨ y = t := by
      obtain ⟨j, rfl⟩ := hy
      exact zpow_eq_one_or_eq htt j
    rcases hy' with rfl | rfl
    · left
      rw [one_mul]
      exact hw
    · right
      rw [← mul_assoc, htt, one_mul]
      exact hw
  · rintro (h | h)
    · exact mem_sup_right h
    · have e : x = t * (t * x) := by rw [← mul_assoc, htt, one_mul]
      rw [e]
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right h)

theorem zpowers_sup_inf_eq {t : G} (htt : t * t = 1) {W L : Subgroup G} (hWL : W ≤ L)
    (htL : t ∉ L) (hc : ∀ w ∈ W, t * w = w * t) : (zpowers t ⊔ W) ⊓ L = W := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hWL)
  rcases (mem_zpowers_sup_iff htt hc).mp hx.1 with h | h
  · exact h
  · exact absurd (by simpa using mul_mem (hWL h) (inv_mem hx.2)) htL

theorem mem_centralizer_sup_iff {H₁ H₂ : Subgroup G} {g : G} :
    g ∈ centralizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) ↔
      g ∈ centralizer (H₁ : Set G) ∧ g ∈ centralizer (H₂ : Set G) := by
  constructor
  · intro h
    exact ⟨centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) h,
      centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) h⟩
  · rintro ⟨h₁, h₂⟩
    have hle : H₁ ⊔ H₂ ≤ centralizer ({g} : Set G) :=
      sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h₁ x hx))
        fun x hx => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h₂ x hx)
    exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hle hx)

theorem mem_centralizer_zpowers_iff' {t g : G} :
    g ∈ centralizer ((zpowers t : Subgroup G) : Set G) ↔ g * t = t * g := by
  constructor
  · intro h
    exact (mem_centralizer_iff.mp h t (mem_zpowers t)).symm
  · intro h
    rw [mem_centralizer_iff]
    rintro _ ⟨j, rfl⟩
    exact (Commute.zpow_left (Commute.symm h) j).eq

theorem isPGroup_zpowers_sup {t : G} (htt : t * t = 1) {W : Subgroup G} (hW : IsPGroup 2 W)
    (hc : ∀ w ∈ W, t * w = w * t) : IsPGroup 2 (zpowers t ⊔ W : Subgroup G) := by
  have ht : IsPGroup 2 (zpowers t) := by
    rintro ⟨_, j, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rcases zpow_eq_one_or_eq htt j with h | h <;> simp [h, pow_two, htt]
  refine ht.to_sup_of_normal_right' hW (le_normalizer_of_commute ?_)
  rintro _ ⟨j, rfl⟩ w hw
  exact (Commute.zpow_left (hc w hw) j).eq

theorem mem_normalizer_of_conj_le [Finite G] {Q : Subgroup G} {g : G}
    (h : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) : g ∈ normalizer (Q : Set G) := by
  have hle : Q.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  have heq : Q.map (MulAut.conj g).toMonoidHom = Q := eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro q
  refine ⟨h q, fun hq => ?_⟩
  rw [← heq] at hq
  obtain ⟨q', hq', hqq⟩ := hq
  have : q' = q := by
    have h1 : g * q' * g⁻¹ = g * q * g⁻¹ := hqq
    simpa using h1
  rwa [← this]

theorem conj_mem_centralizer_of_mem_normalizer' {V : Subgroup G} {g k : G}
    (hg : g ∈ normalizer (V : Set G)) (hk : k ∈ centralizer (V : Set G)) :
    g * k * g⁻¹ ∈ centralizer (V : Set G) := by
  rw [mem_centralizer_iff] at hk ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := (mem_normalizer_iff''.mp hg v).mp hv
  have h1 := hk _ hv'
  calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g) * k) * g⁻¹ := by group
    _ = g * (k * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * k * g⁻¹ * v := by group

end General

section Pull

variable {G : Type*} [Group G] {L : Subgroup G} {X : Type*} [Group X]

theorem exists_eq_symm_of_mem_pull {φ : L ≃* X} {S : Subgroup X} {x : G} (hx : x ∈ pull φ S) :
    ∃ a ∈ S, ((φ.symm a : L) : G) = x := by
  obtain ⟨hxL, hxS⟩ := mem_pull.mp hx
  exact ⟨_, hxS, by rw [MulEquiv.symm_apply_apply]⟩

theorem mem_normalizer_pull_iff (φ : L ≃* X) (S : Subgroup X) (h : normalizer (L : Set G)) :
    (h : G) ∈ normalizer (pull φ S : Set G) ↔ normAct φ h ∈ autStab S := by
  rw [mem_autStab]
  constructor
  · intro hh a
    have h1 := mem_normalizer_iff.mp hh ((φ.symm a : L) : G)
    rw [← normAct_symm_apply, symm_mem_pull, symm_mem_pull] at h1
    exact h1.symm
  · intro hα
    rw [mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ L
    · obtain ⟨a, rfl⟩ : ∃ a, ((φ.symm a : L) : G) = y := ⟨φ ⟨y, hy⟩, by simp⟩
      rw [← normAct_symm_apply, symm_mem_pull, symm_mem_pull]
      exact (hα a).symm
    · refine iff_of_false (fun h' => hy (pull_le φ S h')) fun h' => hy ?_
      exact (mem_normalizer_iff.mp h.2 y).mpr (pull_le φ S h')

theorem forall_conj_pull_iff (φ : L ≃* X) (S : Subgroup X) (h : normalizer (L : Set G)) :
    (∀ u ∈ pull φ S, (h : G) * u * (h : G)⁻¹ = u) ↔ ∀ a ∈ S, normAct φ h a = a := by
  constructor
  · intro hh a ha
    apply φ.symm.injective
    apply Subtype.ext
    rw [normAct_symm_apply]
    exact hh _ (symm_mem_pull.mpr ha)
  · intro hα u hu
    obtain ⟨a, ha, rfl⟩ := exists_eq_symm_of_mem_pull hu
    rw [← normAct_symm_apply, hα a ha]

theorem symm_conj_eq (φ : L ≃* X) (a b : X) :
    ((φ.symm a : L) : G) * ((φ.symm b : L) : G) * ((φ.symm a : L) : G)⁻¹ =
      ((φ.symm (a * b * a⁻¹) : L) : G) := by
  simp [map_mul, map_inv]

end Pull

section Affine

variable {G : Type*} [Group G] {K : Type*} [Field K]

structure AffHyp (ι : K → G) (t : G) (N : Subgroup G) : Prop where
  inj : Function.Injective ι
  add : ∀ x y, ι (x + y) = ι x * ι y
  t_mul_t : t * t = 1
  t_comm : ∀ x, t * ι x = ι x * t
  conj_t : ∀ g ∈ N, ∃ x, g * t * g⁻¹ = t * ι x
  conj_ι : ∀ g ∈ N, ∀ x, ∃ y, g * ι x * g⁻¹ = ι y

@[expose] noncomputable def affFun (ι : K → G) (t g : G) (x : K) : K :=
  Function.invFun ι (t * (g * (t * ι x) * g⁻¹))

namespace AffHyp

variable {ι : K → G} {t : G} {N : Subgroup G}

theorem ι_zero (h : AffHyp ι t N) : ι 0 = 1 := by
  have h0 := h.add 0 0
  rw [add_zero] at h0
  calc ι 0 = ι 0 * ι 0 * (ι 0)⁻¹ := by rw [mul_inv_cancel_right]
    _ = 1 := by rw [← h0, mul_inv_cancel]

theorem ι_comm (h : AffHyp ι t N) (x y : K) : ι x * ι y = ι y * ι x := by
  rw [← h.add, ← h.add, add_comm]

theorem ι_mul_self [CharP K 2] (h : AffHyp ι t N) (x : K) : ι x * ι x = 1 := by
  rw [← h.add, CharTwo.add_self_eq_zero, h.ι_zero]

theorem mem_range (h : AffHyp ι t N) {g : G} (hg : g ∈ N) (x : K) :
    ∃ y, ι y = t * (g * (t * ι x) * g⁻¹) := by
  obtain ⟨b, hb⟩ := h.conj_t g hg
  obtain ⟨y, hy⟩ := h.conj_ι g hg x
  refine ⟨b + y, ?_⟩
  rw [h.add, ← hy]
  calc ι b * (g * ι x * g⁻¹) = t * (t * ι b) * (g * ι x * g⁻¹) := by
        rw [← mul_assoc t t, h.t_mul_t, one_mul]
    _ = t * (g * t * g⁻¹) * (g * ι x * g⁻¹) := by rw [hb]
    _ = t * (g * (t * ι x) * g⁻¹) := by group

theorem ι_affFun (h : AffHyp ι t N) {g : G} (hg : g ∈ N) (x : K) :
    ι (affFun ι t g x) = t * (g * (t * ι x) * g⁻¹) :=
  Function.invFun_eq (h.mem_range hg x)

theorem affFun_mul (h : AffHyp ι t N) {g g' : G} (hg : g ∈ N) (hg' : g' ∈ N) (x : K) :
    affFun ι t (g * g') x = affFun ι t g (affFun ι t g' x) := by
  apply h.inj
  rw [h.ι_affFun (mul_mem hg hg'), h.ι_affFun hg, h.ι_affFun hg']
  calc t * (g * g' * (t * ι x) * (g * g')⁻¹)
      = t * (g * (1 * (g' * (t * ι x) * g'⁻¹)) * g⁻¹) := by group
    _ = t * (g * (t * (t * (g' * (t * ι x) * g'⁻¹))) * g⁻¹) := by
        rw [← h.t_mul_t]
        group

theorem affFun_one (h : AffHyp ι t N) (x : K) : affFun ι t 1 x = x := by
  apply h.inj
  rw [h.ι_affFun (one_mem N)]
  calc t * (1 * (t * ι x) * 1⁻¹) = (t * t) * ι x := by group
    _ = ι x := by rw [h.t_mul_t, one_mul]

@[expose] noncomputable def affRep (h : AffHyp ι t N) : N →* Equiv.Perm K where
  toFun g :=
    { toFun := affFun ι t g
      invFun := affFun ι t (g : G)⁻¹
      left_inv := fun x => by
        rw [← h.affFun_mul (inv_mem g.2) g.2, inv_mul_cancel, h.affFun_one]
      right_inv := fun x => by
        rw [← h.affFun_mul g.2 (inv_mem g.2), mul_inv_cancel, h.affFun_one] }
  map_one' := Equiv.ext fun x => h.affFun_one x
  map_mul' g g' := Equiv.ext fun x => h.affFun_mul g.2 g'.2 x

theorem ι_affRep (h : AffHyp ι t N) (g : N) (x : K) :
    ι (h.affRep g x) = t * ((g : G) * (t * ι x) * (g : G)⁻¹) :=
  h.ι_affFun g.2 x

theorem ι_affRep_zero (h : AffHyp ι t N) (g : N) :
    ι (h.affRep g 0) = t * ((g : G) * t * (g : G)⁻¹) := by
  rw [h.ι_affRep, h.ι_zero, mul_one]

theorem affRep_zero_eq_zero_iff (h : AffHyp ι t N) (g : N) :
    h.affRep g 0 = 0 ↔ (g : G) * t = t * g := by
  rw [← h.inj.eq_iff, h.ι_affRep_zero, h.ι_zero]
  constructor
  · intro e
    have e' : (g : G) * t * (g : G)⁻¹ = t := by
      calc (g : G) * t * (g : G)⁻¹ = t * t * ((g : G) * t * (g : G)⁻¹) := by
            rw [h.t_mul_t, one_mul]
        _ = t := by rw [mul_assoc, e, mul_one]
    calc (g : G) * t = ((g : G) * t * (g : G)⁻¹) * g := by group
      _ = t * g := by rw [e']
  · intro e
    rw [e, mul_inv_cancel_right, h.t_mul_t]

theorem affRep_eq_one_iff (h : AffHyp ι t N) (g : N) :
    h.affRep g = 1 ↔ (g : G) * t = t * g ∧ ∀ x, (g : G) * ι x = ι x * g := by
  constructor
  · intro e
    have h0 : (g : G) * t = t * g := (h.affRep_zero_eq_zero_iff g).mp (by rw [e]; rfl)
    refine ⟨h0, fun x => ?_⟩
    have hx : ι (h.affRep g x) = ι x := by rw [e]; rfl
    have hgt : (g : G) * t * (g : G)⁻¹ = t := by rw [h0, mul_inv_cancel_right]
    have e2 : t * ((g : G) * (t * ι x) * (g : G)⁻¹) = (g : G) * ι x * (g : G)⁻¹ := by
      calc t * ((g : G) * (t * ι x) * (g : G)⁻¹)
          = t * (((g : G) * t * (g : G)⁻¹) * ((g : G) * ι x * (g : G)⁻¹)) := by group
        _ = (g : G) * ι x * (g : G)⁻¹ := by rw [hgt, ← mul_assoc, h.t_mul_t, one_mul]
    rw [h.ι_affRep, e2] at hx
    calc (g : G) * ι x = ((g : G) * ι x * (g : G)⁻¹) * g := by group
      _ = ι x * g := by rw [hx]
  · rintro ⟨h0, h1⟩
    ext x
    apply h.inj
    rw [h.ι_affRep]
    show t * ((g : G) * (t * ι x) * (g : G)⁻¹) = ι x
    calc t * ((g : G) * (t * ι x) * (g : G)⁻¹) = t * (((g : G) * t) * ι x * (g : G)⁻¹) := by
          group
      _ = t * (t * ((g : G) * ι x) * (g : G)⁻¹) := by rw [h0]; group
      _ = t * (t * (ι x * g) * (g : G)⁻¹) := by rw [h1]
      _ = ι x := by
          rw [show t * (t * (ι x * (g : G)) * (g : G)⁻¹) = (t * t) * ι x by group, h.t_mul_t,
            one_mul]

theorem affRep_mem_affPerm (h : AffHyp ι t N) (g : N) : h.affRep g ∈ affPerm K := by
  have hσ : ∀ g' : G, g' ∈ N → ∀ x, ι (Function.invFun ι (g' * ι x * g'⁻¹)) = g' * ι x * g'⁻¹ :=
    fun g' hg' x => Function.invFun_eq (by
      obtain ⟨y, hy⟩ := h.conj_ι g' hg' x
      exact ⟨y, hy.symm⟩)
  let σ : K ≃+ K :=
    { toFun := fun x => Function.invFun ι ((g : G) * ι x * (g : G)⁻¹)
      invFun := fun x => Function.invFun ι ((g : G)⁻¹ * ι x * (g : G)⁻¹⁻¹)
      left_inv := fun x => h.inj (by
        rw [hσ _ (inv_mem g.2), hσ _ g.2]
        group)
      right_inv := fun x => h.inj (by
        rw [hσ _ g.2, hσ _ (inv_mem g.2)]
        group)
      map_add' := fun x y => h.inj (by
        rw [h.add (Function.invFun ι _) (Function.invFun ι _), hσ _ g.2 x, hσ _ g.2 y,
          hσ _ g.2 (x + y), h.add x y]
        group) }
  refine ⟨σ, h.affRep g 0, fun x => h.inj ?_⟩
  rw [add_comm, h.add, h.ι_affRep_zero, h.ι_affRep]
  show t * ((g : G) * (t * ι x) * (g : G)⁻¹) =
    t * ((g : G) * t * (g : G)⁻¹) * ι (Function.invFun ι ((g : G) * ι x * (g : G)⁻¹))
  rw [hσ _ g.2]
  group

theorem conj_ι_of_mem_translPerm (h : AffHyp ι t N) {g : N} (hg : h.affRep g ∈ translPerm K)
    (x : K) : (g : G) * ι x * (g : G)⁻¹ = ι x := by
  obtain ⟨b, hb⟩ := hg
  have h0 : h.affRep g 0 = b := by rw [hb, zero_add]
  have hx := congrArg ι (hb x)
  rw [h.ι_affRep, add_comm, h.add, ← h0, h.ι_affRep_zero] at hx
  calc (g : G) * ι x * (g : G)⁻¹
      = ((g : G) * t * (g : G)⁻¹)⁻¹ * t⁻¹ * (t * ((g : G) * (t * ι x) * (g : G)⁻¹)) := by group
    _ = ι x := by rw [hx]; group

theorem affRep_apply_of_scalar (h : AffHyp ι t N) {g : N} (hgt : (g : G) * t = t * g) {a : K}
    (hga : ∀ x, (g : G) * ι x * (g : G)⁻¹ = ι (a * x)) (x : K) : h.affRep g x = a * x := by
  apply h.inj
  rw [h.ι_affRep, ← hga]
  calc t * ((g : G) * (t * ι x) * (g : G)⁻¹) = t * (((g : G) * t) * ι x * (g : G)⁻¹) := by group
    _ = (t * t) * ((g : G) * ι x * (g : G)⁻¹) := by rw [hgt]; group
    _ = (g : G) * ι x * (g : G)⁻¹ := by rw [h.t_mul_t, one_mul]

end AffHyp

end Affine

section QuotCent

variable {G : Type*} [Group G]

@[expose] def quotCent (N K₀ B : Subgroup G) (hK : ∀ g ∈ N, ∀ y ∈ K₀, g * y * g⁻¹ ∈ K₀)
    (hB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B) : Subgroup G where
  carrier := {g | g ∈ N ∧ ∀ y ∈ K₀, g * y * g⁻¹ * y⁻¹ ∈ B}
  mul_mem' := by
    rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
    refine ⟨mul_mem hgN hhN, fun y hy => ?_⟩
    have e : g * h * y * (g * h)⁻¹ * y⁻¹ =
        g * (h * y * h⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem (hB g hgN _ (hh y hy)) (hg y hy)
  one_mem' := ⟨one_mem N, fun y _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem B⟩
  inv_mem' := by
    rintro g ⟨hgN, hg⟩
    refine ⟨inv_mem hgN, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ K₀ := by simpa using hK g⁻¹ (inv_mem hgN) y hy
    have h1 := inv_mem (hg _ hy')
    have e : (g * (g⁻¹ * y * g) * g⁻¹ * (g⁻¹ * y * g)⁻¹)⁻¹ = g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ := by group
    rwa [e] at h1

theorem mem_quotCent {N K₀ B : Subgroup G} {hK : ∀ g ∈ N, ∀ y ∈ K₀, g * y * g⁻¹ ∈ K₀}
    {hB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B} {g : G} :
    g ∈ quotCent N K₀ B hK hB ↔ g ∈ N ∧ ∀ y ∈ K₀, g * y * g⁻¹ * y⁻¹ ∈ B :=
  Iff.rfl

theorem conj_mem_quotCent {N K₀ B : Subgroup G} {hK : ∀ g ∈ N, ∀ y ∈ K₀, g * y * g⁻¹ ∈ K₀}
    {hB : ∀ g ∈ N, ∀ b ∈ B, g * b * g⁻¹ ∈ B} {h z : G} (hh : h ∈ N)
    (hz : z ∈ quotCent N K₀ B hK hB) : h * z * h⁻¹ ∈ quotCent N K₀ B hK hB := by
  obtain ⟨hzN, hz⟩ := hz
  refine ⟨mul_mem (mul_mem hh hzN) (inv_mem hh), fun y hy => ?_⟩
  have hy' : h⁻¹ * y * h ∈ K₀ := by simpa using hK h⁻¹ (inv_mem hh) y hy
  have h1 := hB h hh _ (hz _ hy')
  have e : h * (z * (h⁻¹ * y * h) * z⁻¹ * (h⁻¹ * y * h)⁻¹) * h⁻¹ =
      h * z * h⁻¹ * y * (h * z * h⁻¹)⁻¹ * y⁻¹ := by group
  rwa [e] at h1

end QuotCent

structure TwoCoreSetup {G : Type*} [Group G] (L : Subgroup G) (K : Type) [Field K] (n : ℕ)
    (t : G) : Prop where
  two_le : 2 ≤ n
  card_K : Nat.card K = 2 ^ n
  t_mul_t : t * t = 1
  L_le : L ≤ centralizer ({t} : Set G)
  cent_le : centralizer ({t} : Set G) ≤ normalizer (L : Set G)
  cent_inf : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t
  not_conj : ∀ g : G, g⁻¹ * t * g ∉ L

namespace TwoCoreSetup

section Basic

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ} {t : G}

theorem t_not_mem (hS : TwoCoreSetup L K n t) : t ∉ L := by
  simpa using hS.not_conj 1

theorem comm (hS : TwoCoreSetup L K n t) {x : G} (hx : x ∈ L) : t * x = x * t :=
  (mem_centralizer_singleton_iff.mp (hS.L_le hx)).symm

theorem t_inv (hS : TwoCoreSetup L K n t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right hS.t_mul_t

theorem zpowers_comm (hS : TwoCoreSetup L K n t) {y x : G} (hy : y ∈ zpowers t) (hx : x ∈ L) :
    y * x = x * y := by
  obtain ⟨j, rfl⟩ := hy
  exact (Commute.zpow_left (hS.comm hx) j).eq

theorem mem_zpowers_of_mem (hS : TwoCoreSetup L K n t) {x : G} (h1 : x ∈ centralizer (L : Set G))
    (h2 : x ∈ centralizer ({t} : Set G)) : x ∈ zpowers t :=
  hS.cent_inf ▸ ⟨h1, h2⟩

theorem zpowers_inf (hS : TwoCoreSetup L K n t) {W : Subgroup G} (hW : W ≤ L) :
    zpowers t ⊓ W = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxW⟩
  have hx : x = 1 ∨ x = t := by
    obtain ⟨j, rfl⟩ := hxt
    exact zpow_eq_one_or_eq hS.t_mul_t j
  rcases hx with rfl | rfl
  · exact one_mem _
  · exact absurd (hW hxW) hS.t_not_mem

theorem mem_normalizer_zpowers_sup_iff [Finite G] (hS : TwoCoreSetup L K n t) {h : G}
    (hh : h ∈ centralizer ({t} : Set G)) {W : Subgroup G} (hW : W ≤ L) :
    h ∈ normalizer ((zpowers t ⊔ W : Subgroup G) : Set G) ↔ h ∈ normalizer (W : Set G) := by
  have hc : ∀ w ∈ W, t * w = w * t := fun w hw => hS.comm (hW hw)
  have hht : h * t * h⁻¹ = t := by rw [mem_centralizer_singleton_iff.mp hh, mul_inv_cancel_right]
  constructor
  · intro hN
    refine mem_normalizer_of_conj_le fun w hw => ?_
    have h1 : h * w * h⁻¹ ∈ zpowers t ⊔ W := (mem_normalizer_iff.mp hN w).mp (mem_sup_right hw)
    have h2 : h * w * h⁻¹ ∈ L := (mem_normalizer_iff.mp (hS.cent_le hh) w).mp (hW hw)
    rw [← zpowers_sup_inf_eq hS.t_mul_t hW hS.t_not_mem hc]
    exact ⟨h1, h2⟩
  · intro hN
    refine mem_normalizer_of_conj_le fun x hx => conj_mem_sup ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      have e := map_zpow (MulAut.conj h) t j
      rw [MulAut.conj_apply, MulAut.conj_apply, hht] at e
      exact e.symm
    · exact fun w hw => (mem_normalizer_iff.mp hN w).mp hw

end Basic

section Facts

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]
  {n : ℕ} {t : G}

theorem axisStr (hS : TwoCoreSetup L K n t) (i : Axis) :
    RootAxisStructure (rootU K i) (rootA K i) (sHom K i) (dHom K i) (rootCoord K i)
      (vecOf K i) :=
  even_symplectic_four_root_axis_centralizer_structure hS.card_K hS.two_le i

theorem axisAut (hS : TwoCoreSetup L K n t) (i : Axis) :
    AutNormalizerFacts n (rootU K i) (rootA K i) (sHom K i) (dHom K i) (rootCoord K i)
      (frobAut K) :=
  autNormalizerFacts_axis hS.two_le hS.card_K i

end Facts

section Axis

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ} {t : G}
  (φ : L ≃* antiSp K) (i : Axis)

local notation "𝐔" => pull φ (rootU K i)
local notation "𝐀" => pull φ (rootA K i)
local notation "𝐕" => (zpowers t ⊔ pull φ (rootU K i) : Subgroup G)
local notation "𝐁" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐊" => centralizer ((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Set G)
local notation "𝐌" => normalizer ((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

omit [CharP K 2] in
theorem comm_pull (hS : TwoCoreSetup L K n t) {S : Subgroup (antiSp K)} :
    ∀ w ∈ pull φ S, t * w = w * t :=
  fun _ hw => hS.comm (pull_le φ S hw)

theorem mem_pull_rootC_iff {x : G} : x ∈ pull φ (rootC K i) ↔ x ∈ L ∧ ∀ u ∈ 𝐔, u * x = x * u := by
  constructor
  · intro hx
    obtain ⟨hxL, hxC⟩ := mem_pull.mp hx
    refine ⟨hxL, fun u hu => ?_⟩
    obtain ⟨a, ha, rfl⟩ := exists_eq_symm_of_mem_pull hu
    have h1 := congrArg (fun z => ((φ.symm z : L) : G)) (mem_centralizer_iff.mp hxC a ha)
    simpa [map_mul] using h1
  · rintro ⟨hxL, hx⟩
    refine mem_pull.mpr ⟨hxL, mem_centralizer_iff.mpr fun a ha => ?_⟩
    apply φ.symm.injective
    apply Subtype.ext
    simpa [map_mul] using hx _ (symm_mem_pull.mpr ha)

theorem pull_rootC_eq : pull φ (rootC K i) = L ⊓ centralizer (𝐔 : Set G) := by
  ext x
  rw [mem_pull_rootC_iff, mem_inf, mem_centralizer_iff]
  exact Iff.rfl

theorem K_le_C : 𝐊 ≤ 𝐂 := fun _ hg =>
  mem_centralizer_singleton_iff.mpr
    (mem_centralizer_zpowers_iff'.mp (mem_centralizer_sup_iff.mp hg).1)

theorem centralizer_eq [Finite K] (hS : TwoCoreSetup L K n t) :
    𝐊 = zpowers t ⊔ pull φ (rootC K i) := by
  apply le_antisymm
  · intro g hg
    have hgU := (mem_centralizer_sup_iff.mp hg).2
    have hgC : g ∈ 𝐂 := K_le_C φ i hg
    set g' : normalizer (L : Set G) := ⟨g, hS.cent_le hgC⟩ with hg'
    have hfix : ∀ a ∈ rootU K i, normAct φ g' a = a := by
      refine (forall_conj_pull_iff φ _ g').mp fun u hu => ?_
      show g * u * g⁻¹ = u
      rw [← mem_centralizer_iff.mp hgU u hu, mul_inv_cancel_right]
    obtain ⟨y, hyC, hy⟩ := ((hS.axisAut i).centralizer _).mp hfix
    have h1 : ((φ.symm y : L) : G)⁻¹ * g ∈ zpowers t := by
      refine hS.mem_zpowers_of_mem (inv_mul_mem_centralizer φ g' (φ.symm y) ?_)
        (mul_mem (inv_mem (hS.L_le (φ.symm y).2)) hgC)
      rw [MulEquiv.apply_symm_apply]
      exact hy
    have h2 := mul_mem (mem_sup_right (symm_mem_pull.mpr hyC) :
      ((φ.symm y : L) : G) ∈ zpowers t ⊔ pull φ (rootC K i)) (mem_sup_left h1)
    rwa [mul_inv_cancel_left] at h2
  · refine sup_le (zpowers_le.mpr ?_) fun c hc => ?_
    · refine mem_centralizer_sup_iff.mpr ⟨mem_centralizer_zpowers_iff'.mpr rfl, ?_⟩
      exact mem_centralizer_iff.mpr fun u hu => (hS.comm (pull_le φ _ hu)).symm
    · obtain ⟨hcL, hcU⟩ := (mem_pull_rootC_iff φ i).mp hc
      refine mem_centralizer_sup_iff.mpr
        ⟨mem_centralizer_zpowers_iff'.mpr (hS.comm hcL).symm, ?_⟩
      exact mem_centralizer_iff.mpr hcU

theorem mem_K_iff [Finite K] (hS : TwoCoreSetup L K n t) {g : G} :
    g ∈ 𝐊 ↔ ∃ τ ∈ zpowers t, ∃ c ∈ pull φ (rootC K i), τ * c = g := by
  rw [hS.centralizer_eq φ i]
  exact mem_sup_of_commute fun y hy x hx => hS.zpowers_comm hy (pull_le φ _ hx)

theorem A_le_rootC [Finite K] (hS : TwoCoreSetup L K n t) : 𝐀 ≤ pull φ (rootC K i) :=
  pull_mono φ (hS.axisStr i).A_le_C

theorem B_le_K [Finite K] (hS : TwoCoreSetup L K n t) : 𝐁 ≤ 𝐊 := by
  rw [hS.centralizer_eq φ i]
  exact sup_le_sup_left (hS.A_le_rootC φ i) _

theorem K_inf_L_le [Finite K] (hS : TwoCoreSetup L K n t) : 𝐊 ⊓ L ≤ pull φ (rootC K i) := by
  rw [hS.centralizer_eq φ i, zpowers_sup_inf_eq hS.t_mul_t (pull_le φ _) hS.t_not_mem
    (comm_pull φ hS)]

theorem conj_mem_A [Finite K] (hS : TwoCoreSetup L K n t) {k : G} (hk : k ∈ 𝐊) {a : G}
    (ha : a ∈ 𝐀) : k * a * k⁻¹ ∈ 𝐀 := by
  obtain ⟨τ, hτ, c, hc, rfl⟩ := (hS.mem_K_iff φ i).mp hk
  obtain ⟨c', hc', rfl⟩ := exists_eq_symm_of_mem_pull hc
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  have h1 : ((φ.symm c' : L) : G) * ((φ.symm a' : L) : G) * ((φ.symm c' : L) : G)⁻¹ ∈ 𝐀 := by
    rw [symm_conj_eq]
    exact symm_mem_pull.mpr ((hS.axisStr i).A_normal_C c' hc' a' ha')
  have e : τ * ((φ.symm c' : L) : G) * ((φ.symm a' : L) : G) * (τ * ((φ.symm c' : L) : G))⁻¹ =
      τ * (((φ.symm c' : L) : G) * ((φ.symm a' : L) : G) * ((φ.symm c' : L) : G)⁻¹) * τ⁻¹ := by
    group
  rw [e, hS.zpowers_comm hτ (pull_le φ _ h1), mul_inv_cancel_right]
  exact h1

theorem conj_mem_B [Finite K] (hS : TwoCoreSetup L K n t) {k : G} (hk : k ∈ 𝐊) {b : G}
    (hb : b ∈ 𝐁) : k * b * k⁻¹ ∈ 𝐁 := by
  refine conj_mem_sup (fun x hx => ?_) (fun a ha => hS.conj_mem_A φ i hk ha) hb
  rw [← mem_centralizer_iff.mp (mem_centralizer_sup_iff.mp hk).1 x hx, mul_inv_cancel_right]
  exact hx

theorem isPGroup_A [Finite K] : IsPGroup 2 𝐀 := by
  obtain ⟨-, -, hU2, -⟩ := card_and_isSylowTwoOf_antiUnipotent (K := K)
  have hAU : rootA K i ≤ antiUnipotent K := by
    cases i
    exacts [radA1_le_antiUnipotent, radA2_le_antiUnipotent]
  exact ((hU2.to_le hAU).comap_of_injective _ φ.injective).map _

theorem isPGroup_B [Finite K] (hS : TwoCoreSetup L K n t) : IsPGroup 2 𝐁 :=
  isPGroup_zpowers_sup hS.t_mul_t (isPGroup_A φ i) (comm_pull φ hS)

theorem le_rootA_of_normal [Finite K] (hS : TwoCoreSetup L K n t) {W : Subgroup (antiSp K)}
    (hWC : W ≤ rootC K i) (hWn : ∀ g ∈ rootC K i, ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hW2 : IsPGroup 2 W) : W ≤ rootA K i := by
  have hn : (W.subgroupOf (rootC K i)).Normal := ⟨fun w hw g => by
    rw [mem_subgroupOf] at hw ⊢
    exact hWn g g.2 w hw⟩
  have hle : W.subgroupOf (rootC K i) ≤ CFSG.pCore 2 (rootC K i) :=
    le_sSup ⟨hn, hW2.of_equiv (subgroupOfEquivOfLe hWC).symm⟩
  have hcore := (hS.axisStr i).C_pCore
  intro w hw
  have h1 : (⟨w, hWC hw⟩ : rootC K i) ∈ CFSG.pCore 2 (rootC K i) :=
    hle (mem_subgroupOf.mpr hw)
  change (⟨w, hWC hw⟩ : rootC K i) ∈ CFSG.pCore 2 (centralizer ((rootU K i : Subgroup _) :
    Set (antiSp K))) at h1
  rw [hcore] at h1
  exact mem_subgroupOf.mp h1

theorem le_B [Finite K] (hS : TwoCoreSetup L K n t) {R : Subgroup G} (hR : R ≤ 𝐊)
    (hRn : ∀ k ∈ 𝐊, ∀ r ∈ R, k * r * k⁻¹ ∈ R) (hR2 : IsPGroup 2 R) : R ≤ 𝐁 := by
  have htK : t ∈ 𝐊 := by
    rw [hS.centralizer_eq φ i]
    exact mem_sup_left (mem_zpowers t)
  have htR : ∀ r ∈ R, t * r * t⁻¹ ∈ R := hRn t htK
  have hRt2 : IsPGroup 2 (zpowers t ⊔ R : Subgroup G) := by
    refine IsPGroup.to_sup_of_normal_right' ?_ hR2 (zpowers_le.mpr ?_)
    · exact (isPGroup_zpowers_sup hS.t_mul_t IsPGroup.of_bot (by simp)).to_le le_sup_left
    · rw [mem_normalizer_iff]
      intro r
      refine ⟨htR r, fun h => ?_⟩
      have := htR _ h
      rwa [hS.t_inv, ← mul_assoc, ← mul_assoc, hS.t_mul_t, one_mul, mul_assoc, hS.t_mul_t,
        mul_one] at this
  have hRtK : zpowers t ⊔ R ≤ 𝐊 := sup_le (zpowers_le.mpr htK) hR
  set W : Subgroup (antiSp K) := ((zpowers t ⊔ R) ⊓ L).comap (L.subtype.comp φ.symm.toMonoidHom)
    with hWdef
  have hmemW : ∀ a, a ∈ W ↔ ((φ.symm a : L) : G) ∈ zpowers t ⊔ R := fun a =>
    ⟨fun h => h.1, fun h => ⟨h, (φ.symm a).2⟩⟩
  have hWA : W ≤ rootA K i := by
    refine hS.le_rootA_of_normal i (fun a ha => ?_) (fun g hg a ha => ?_) ?_
    · have h1 : ((φ.symm a : L) : G) ∈ pull φ (rootC K i) :=
        hS.K_inf_L_le φ i ⟨hRtK ((hmemW a).mp ha), (φ.symm a).2⟩
      exact symm_mem_pull.mp h1
    · rw [hmemW, ← symm_conj_eq]
      have hgK : ((φ.symm g : L) : G) ∈ 𝐊 := by
        rw [hS.centralizer_eq φ i]
        exact mem_sup_right (symm_mem_pull.mpr hg)
      refine conj_mem_sup (fun x hx => ?_) (fun r hr => hRn _ hgK r hr) ((hmemW a).mp ha)
      rw [← hS.zpowers_comm hx (φ.symm g).2, mul_inv_cancel_right]
      exact hx
    · exact (hRt2.to_le inf_le_left).comap_of_injective _
        ((Subtype.val_injective).comp φ.symm.injective)
  intro r hr
  obtain ⟨τ, hτ, c, hc, rfl⟩ := (hS.mem_K_iff φ i).mp (hR hr)
  have hcL : c ∈ L := pull_le φ _ hc
  have hcW : φ ⟨c, hcL⟩ ∈ W := by
    rw [hmemW, MulEquiv.symm_apply_apply]
    have := mul_mem (mem_sup_left (inv_mem hτ)) (mem_sup_right hr :
      τ * c ∈ zpowers t ⊔ R)
    rwa [inv_mul_cancel_left] at this
  have hcA : c ∈ 𝐀 := mem_pull.mpr ⟨hcL, hWA hcW⟩
  exact mul_mem (mem_sup_left hτ) (mem_sup_right hcA)

theorem pCore_K_eq [Finite K] (hS : TwoCoreSetup L K n t) :
    (CFSG.pCore 2 𝐊).map 𝐊.subtype = 𝐁 :=
  pCore_map_eq (hS.B_le_K φ i) (fun _ hk _ hb => hS.conj_mem_B φ i hk hb) (hS.isPGroup_B φ i)
    fun _ hR hRn hR2 => hS.le_B φ i hR hRn hR2

theorem M_le_normalizer_B [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) :
    𝐌 ≤ normalizer (𝐁 : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_le fun b hb => ?_
  have hle := hS.le_B φ i (R := (𝐁).map (MulAut.conj g).toMonoidHom) ?_ ?_
    ((hS.isPGroup_B φ i).map _)
  · exact hle ⟨b, hb, rfl⟩
  · rintro _ ⟨b', hb', rfl⟩
    exact conj_mem_centralizer_of_mem_normalizer' hg (hS.B_le_K φ i hb')
  · rintro k hk _ ⟨b', hb', rfl⟩
    have hk' : g⁻¹ * k * g ∈ 𝐊 := by
      simpa using conj_mem_centralizer_of_mem_normalizer' (inv_mem hg) hk
    refine ⟨(g⁻¹ * k * g) * b' * (g⁻¹ * k * g)⁻¹, hS.conj_mem_B φ i hk' hb', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem inf_normalizer_eq [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) :
    𝐂 ⊓ 𝐌 = 𝐂 ⊓ normalizer (𝐁 : Set G) := by
  ext h
  simp only [mem_inf]
  refine and_congr_right fun hhC => ?_
  rw [hS.mem_normalizer_zpowers_sup_iff hhC (pull_le φ _),
    hS.mem_normalizer_zpowers_sup_iff hhC (pull_le φ _)]
  rw [mem_normalizer_pull_iff φ _ ⟨h, hS.cent_le hhC⟩,
    mem_normalizer_pull_iff φ _ ⟨h, hS.cent_le hhC⟩, (hS.axisAut i).stab_eq]

theorem conj_t_mem (hS : TwoCoreSetup L K n t) {m : G} (hm : m ∈ 𝐌) :
    t * (m⁻¹ * t * m) ∈ 𝐔 := by
  have h1 : m⁻¹ * t * m ∈ 𝐕 := (mem_normalizer_iff''.mp hm t).mp (mem_sup_left (mem_zpowers t))
  rcases (mem_zpowers_sup_iff hS.t_mul_t (comm_pull φ hS)).mp h1 with h | h
  · exact absurd (pull_le φ _ h) (hS.not_conj m)
  · exact h

end Axis

end TwoCoreSetup

section Coord

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def coordG (φ : L ≃* antiSp K) (i : Axis) (x : K) : G :=
  ((φ.symm (rootCoord K i x) : L) : G)

variable (φ : L ≃* antiSp K) (i : Axis)

theorem rootCoord_add' (x y : K) :
    rootCoord K i (x + y) = rootCoord K i x * rootCoord K i y := by
  cases i
  · show uElt 0 (x + y) 0 0 = uElt 0 x 0 0 * uElt 0 y 0 0
    rw [uElt_mul]
    congr 1 <;> ring
  · show uElt 0 0 (x + y) 0 = uElt 0 0 x 0 * uElt 0 0 y 0
    rw [uElt_mul]
    congr 1 <;> ring

theorem rootCoord_mem' (x : K) : rootCoord K i x ∈ rootU K i := by
  cases i
  · exact ⟨x, rfl⟩
  · exact ⟨x, rfl⟩

theorem exists_rootCoord_eq {a : antiSp K} (ha : a ∈ rootU K i) : ∃ x, rootCoord K i x = a := by
  cases i
  · obtain ⟨b, rfl⟩ := ha
    exact ⟨b, rfl⟩
  · obtain ⟨c, rfl⟩ := ha
    exact ⟨c, rfl⟩

theorem coordG_mem (x : K) : coordG φ i x ∈ pull φ (rootU K i) :=
  symm_mem_pull.mpr (rootCoord_mem' i x)

theorem exists_coordG_eq {u : G} (hu : u ∈ pull φ (rootU K i)) : ∃ x, coordG φ i x = u := by
  obtain ⟨a, ha, rfl⟩ := exists_eq_symm_of_mem_pull hu
  obtain ⟨x, rfl⟩ := exists_rootCoord_eq i ha
  exact ⟨x, rfl⟩

theorem coordG_injective : Function.Injective (coordG φ i) := fun _ _ h =>
  rootCoord_injective i (φ.symm.injective (Subtype.ext h))

theorem coordG_add (x y : K) : coordG φ i (x + y) = coordG φ i x * coordG φ i y := by
  simp only [coordG, rootCoord_add', map_mul, coe_mul]

theorem coordG_zero : coordG φ i 0 = 1 := by
  have h := coordG_add φ i 0 0
  rw [add_zero] at h
  calc coordG φ i 0 = coordG φ i 0 * coordG φ i 0 * (coordG φ i 0)⁻¹ := by
        rw [mul_inv_cancel_right]
    _ = 1 := by rw [← h, mul_inv_cancel]

theorem card_U : Nat.card (pull φ (rootU K i)) = Nat.card K :=
  (Nat.card_congr (Equiv.ofBijective (fun x : K => (⟨coordG φ i x, coordG_mem φ i x⟩ :
    pull φ (rootU K i))) ⟨fun x y h => coordG_injective φ i (by simpa using h),
    fun u => by
      obtain ⟨x, hx⟩ := exists_coordG_eq φ i u.2
      exact ⟨x, Subtype.ext hx⟩⟩)).symm

end Coord

namespace TwoCoreSetup

section Cond

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {n : ℕ} {t : G}
  (φ : L ≃* antiSp K) (i : Axis)

local notation "𝐔" => pull φ (rootU K i)
local notation "𝐀" => pull φ (rootA K i)
local notation "𝐁" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐊" => centralizer ((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Set G)
local notation "𝐌" => normalizer ((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)

theorem torus_conj [Finite K] (hS : TwoCoreSetup L K n t) (l : Kˣ) (x : K) :
    ((φ.symm (dHom K i l) : L) : G) * coordG φ i x * ((φ.symm (dHom K i l) : L) : G)⁻¹ =
      coordG φ i ((l : K) ^ 2 * x) := by
  rw [coordG, coordG, symm_conj_eq, (hS.axisStr i).d_coord l x]

theorem dHom_mem_normalizer [Finite K] (hS : TwoCoreSetup L K n t) (l : Kˣ) :
    dHom K i l ∈ normalizer ((rootU K i : Subgroup (antiSp K)) : Set (antiSp K)) := by
  simpa using (hS.axisStr i).ds_mem_N l 1

theorem torus_mem_M [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) (l : Kˣ) :
    ((φ.symm (dHom K i l) : L) : G) ∈ 𝐌 := by
  rw [hS.mem_normalizer_zpowers_sup_iff (hS.L_le (φ.symm _).2) (pull_le φ _)]
  have hN : ((φ.symm (dHom K i l) : L) : G) ∈ normalizer (L : Set G) := le_normalizer (φ.symm _).2
  refine (mem_normalizer_pull_iff φ _ ⟨_, hN⟩).mpr ?_
  rw [normAct_of_mem φ hN, MulEquiv.apply_symm_apply, mem_autStab]
  exact fun x => conj_mem_autStab_iff (hS.dHom_mem_normalizer i l) x

theorem torus_mem_quotCent [Finite K] (hS : TwoCoreSetup L K n t) (l : Kˣ) :
    ∀ y ∈ 𝐊, ((φ.symm (dHom K i l) : L) : G) * y * ((φ.symm (dHom K i l) : L) : G)⁻¹ * y⁻¹ ∈ 𝐁 := by
  intro y hy
  set δ : G := ((φ.symm (dHom K i l) : L) : G) with hδ
  obtain ⟨τ, hτ, c, hc, rfl⟩ := (hS.mem_K_iff φ i).mp hy
  obtain ⟨c', hc', rfl⟩ := exists_eq_symm_of_mem_pull hc
  have hX : dHom K i l * c' * (dHom K i l)⁻¹ * c'⁻¹ ∈ rootA K i := by
    have hstab : MulAut.conj (1 * dHom K i l) ∈ autStab (rootU K i) := by
      rw [one_mul, mem_autStab]
      exact fun x => conj_mem_autStab_iff (hS.dHom_mem_normalizer i l) x
    have h1 := ((hS.axisAut i).kernel_action _ hstab).mpr ⟨1, one_mem _, l, rfl⟩ c' hc'
    rw [MulAut.conj_apply, one_mul] at h1
    have h2 := (hS.axisStr i).A_normal_C c' hc' _ h1
    rwa [show c' * (c'⁻¹ * (dHom K i l * c' * (dHom K i l)⁻¹)) * c'⁻¹ =
      dHom K i l * c' * (dHom K i l)⁻¹ * c'⁻¹ by group] at h2
  have hXG : δ * ((φ.symm c' : L) : G) * δ⁻¹ * ((φ.symm c' : L) : G)⁻¹ ∈ 𝐀 := by
    rw [show δ * ((φ.symm c' : L) : G) * δ⁻¹ * ((φ.symm c' : L) : G)⁻¹ =
      ((φ.symm (dHom K i l * c' * (dHom K i l)⁻¹ * c'⁻¹) : L) : G) by simp [hδ, map_mul, map_inv]]
    exact symm_mem_pull.mpr hX
  have h1 : τ * δ = δ * τ := hS.zpowers_comm hτ (φ.symm _).2
  have h3 := hS.zpowers_comm hτ (pull_le φ _ hXG)
  have e : δ * (τ * ((φ.symm c' : L) : G)) * δ⁻¹ * (τ * ((φ.symm c' : L) : G))⁻¹ =
      δ * ((φ.symm c' : L) : G) * δ⁻¹ * ((φ.symm c' : L) : G)⁻¹ := by
    calc δ * (τ * ((φ.symm c' : L) : G)) * δ⁻¹ * (τ * ((φ.symm c' : L) : G))⁻¹
        = (δ * τ) * ((φ.symm c' : L) : G) * δ⁻¹ * ((φ.symm c' : L) : G)⁻¹ * τ⁻¹ := by group
      _ = τ * (δ * ((φ.symm c' : L) : G) * δ⁻¹ * ((φ.symm c' : L) : G)⁻¹) * τ⁻¹ := by
          rw [← h1]
          group
      _ = δ * ((φ.symm c' : L) : G) * δ⁻¹ * ((φ.symm c' : L) : G)⁻¹ := by
          rw [h3, mul_inv_cancel_right]
  rw [e]
  exact mem_sup_right hXG

theorem mem_rootA_of_comm [Finite K] (hS : TwoCoreSetup L K n t) {c : antiSp K}
    (hc : c ∈ rootC K i) (hcA : ∀ y ∈ rootC K i, c * y * c⁻¹ * y⁻¹ ∈ rootA K i) :
    c ∈ rootA K i := by
  have hst := hS.axisStr i
  obtain ⟨a, ha, M, rfl⟩ := hst.C_decomp c hc
  have hM : M ∈ center (SL₂ K) := by
    rw [mem_center_iff]
    intro M'
    have h1 := hcA (sHom K i M') (hst.s_mem_C M')
    have h2 : sHom K i (M * M' * M⁻¹ * M'⁻¹) ∈ rootA K i := by
      have e : sHom K i (M * M' * M⁻¹ * M'⁻¹) = a⁻¹ * (a * sHom K i M * sHom K i M' *
          (a * sHom K i M)⁻¹ * (sHom K i M')⁻¹) * (sHom K i M' * a * (sHom K i M')⁻¹) := by
        simp only [map_mul, map_inv]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem ha) h1) (hst.A_normal_C _ (hst.s_mem_C M') a ha)
    have h3 := hst.C_unique 1 (one_mem _) _ h2 (M * M' * M⁻¹ * M'⁻¹) 1
      (by rw [one_mul, map_one, mul_one])
    calc M' * M = (M * M' * M⁻¹ * M'⁻¹)⁻¹ * (M * M') := by group
      _ = M * M' := by rw [h3.2, inv_one, one_mul]
  rw [hst.S_center, mem_bot] at hM
  rw [hM, map_one, mul_one]
  exact ha

theorem mem_B_of_comm [Finite K] (hS : TwoCoreSetup L K n t) {g : G} (hgK : g ∈ 𝐊)
    (hg : ∀ y ∈ 𝐊, g * y * g⁻¹ * y⁻¹ ∈ 𝐁) : g ∈ 𝐁 := by
  obtain ⟨τ, hτ, c, hc, rfl⟩ := (hS.mem_K_iff φ i).mp hgK
  obtain ⟨c', hc', rfl⟩ := exists_eq_symm_of_mem_pull hc
  have hcA : c' ∈ rootA K i := by
    refine hS.mem_rootA_of_comm i hc' fun y hy => ?_
    have hyK : ((φ.symm y : L) : G) ∈ 𝐊 := by
      rw [hS.centralizer_eq φ i]
      exact mem_sup_right (symm_mem_pull.mpr hy)
    have h1 := hg _ hyK
    have hXL : ((φ.symm c' : L) : G) * ((φ.symm y : L) : G) * ((φ.symm c' : L) : G)⁻¹ ∈ L :=
      mul_mem (mul_mem (φ.symm c').2 (φ.symm y).2) (inv_mem (φ.symm c').2)
    have hτX := hS.zpowers_comm hτ hXL
    have e : τ * ((φ.symm c' : L) : G) * ((φ.symm y : L) : G) *
        (τ * ((φ.symm c' : L) : G))⁻¹ * ((φ.symm y : L) : G)⁻¹ =
        ((φ.symm (c' * y * c'⁻¹ * y⁻¹) : L) : G) := by
      calc τ * ((φ.symm c' : L) : G) * ((φ.symm y : L) : G) *
            (τ * ((φ.symm c' : L) : G))⁻¹ * ((φ.symm y : L) : G)⁻¹
          = (τ * (((φ.symm c' : L) : G) * ((φ.symm y : L) : G) * ((φ.symm c' : L) : G)⁻¹)) *
              τ⁻¹ * ((φ.symm y : L) : G)⁻¹ := by group
        _ = ((φ.symm c' : L) : G) * ((φ.symm y : L) : G) * ((φ.symm c' : L) : G)⁻¹ *
              ((φ.symm y : L) : G)⁻¹ := by rw [hτX]; group
        _ = ((φ.symm (c' * y * c'⁻¹ * y⁻¹) : L) : G) := by simp [map_mul, map_inv]
    rw [e] at h1
    have h2 : ((φ.symm (c' * y * c'⁻¹ * y⁻¹) : L) : G) ∈ 𝐁 ⊓ L := ⟨h1, (φ.symm _).2⟩
    rw [zpowers_sup_inf_eq hS.t_mul_t (pull_le φ _) hS.t_not_mem (comm_pull φ hS)] at h2
    exact symm_mem_pull.mp h2
  exact mul_mem (mem_sup_left hτ) (mem_sup_right (symm_mem_pull.mpr hcA))

theorem exists_conj_eq [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) (hMC : ¬ 𝐌 ≤ 𝐂)
    {u : G} (hu : u ∈ 𝐔) : ∃ m ∈ 𝐌, m⁻¹ * t * m = t * u := by
  obtain ⟨m₀, hm₀, hm₀C⟩ := Set.not_subset.mp hMC
  obtain ⟨x₀, hx₀⟩ := exists_coordG_eq φ i (hS.conj_t_mem φ i hm₀)
  obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
  by_cases hx : x = 0
  · refine ⟨1, one_mem _, ?_⟩
    rw [hx, coordG_zero, mul_one]
    group
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    apply hm₀C
    rw [coordG_zero] at hx₀
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have h1 : m₀⁻¹ * t * m₀ = t := by
      calc m₀⁻¹ * t * m₀ = t * (t * (m₀⁻¹ * t * m₀)) := by rw [← mul_assoc, hS.t_mul_t, one_mul]
        _ = t := by rw [← hx₀, mul_one]
    calc m₀ * t = m₀ * (m₀⁻¹ * t * m₀) := by rw [h1]
      _ = t * m₀ := by group
  obtain ⟨y, hy⟩ := exists_sq_eq (x₀ * x⁻¹)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, mul_eq_zero] at hy
    exact hy.elim hx₀0 (inv_ne_zero hx)
  set l := Units.mk0 y hy0
  set δ : G := ((φ.symm (dHom K i l) : L) : G) with hδ
  refine ⟨m₀ * δ, mul_mem hm₀ (hS.torus_mem_M φ i l), ?_⟩
  have h1 : m₀⁻¹ * t * m₀ = t * coordG φ i x₀ := by rw [hx₀, ← mul_assoc, hS.t_mul_t, one_mul]
  have h2 : δ * coordG φ i x * δ⁻¹ = coordG φ i x₀ := by
    rw [hS.torus_conj φ i l x]
    congr 1
    simp only [l, Units.val_mk0, hy]
    field_simp
  have hδt : δ⁻¹ * t * δ = t := by
    rw [mul_assoc, hS.comm (show δ ∈ L from (φ.symm _).2), ← mul_assoc, inv_mul_cancel, one_mul]
  calc (m₀ * δ)⁻¹ * t * (m₀ * δ) = δ⁻¹ * (m₀⁻¹ * t * m₀) * δ := by group
    _ = (δ⁻¹ * t * δ) * coordG φ i x := by rw [h1, ← h2]; group
    _ = t * coordG φ i x := by rw [hδt]

theorem conj_mem_U [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) (hMC : ¬ 𝐌 ≤ 𝐂) {g : G}
    (hg : g ∈ 𝐌) {u : G} (hu : u ∈ 𝐔) : g * u * g⁻¹ ∈ 𝐔 := by
  obtain ⟨a, ha, hau⟩ := hS.exists_conj_eq φ i hMC hu
  have h1 := hS.conj_t_mem φ i (mul_mem ha (inv_mem hg))
  have h2 := hS.conj_t_mem φ i (inv_mem hg)
  have e1 : (a * g⁻¹)⁻¹ * t * (a * g⁻¹) = g * (t * u) * g⁻¹ := by
    rw [← hau]
    group
  have e : g * u * g⁻¹ = (t * (g⁻¹⁻¹ * t * g⁻¹))⁻¹ * (t * ((a * g⁻¹)⁻¹ * t * (a * g⁻¹))) := by
    rw [e1]
    group
  rw [e]
  exact mul_mem (inv_mem h2) h1

theorem affHyp [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) (hMC : ¬ 𝐌 ≤ 𝐂) :
    AffHyp (coordG φ i) t 𝐌 where
  inj := coordG_injective φ i
  add := coordG_add φ i
  t_mul_t := hS.t_mul_t
  t_comm := fun _ => hS.comm (φ.symm _).2
  conj_t := fun g hg => by
    obtain ⟨x, hx⟩ := exists_coordG_eq φ i (hS.conj_t_mem φ i (inv_mem hg))
    refine ⟨x, ?_⟩
    rw [hx, ← mul_assoc, hS.t_mul_t, one_mul, inv_inv]
  conj_ι := fun g hg x => by
    obtain ⟨y, hy⟩ := exists_coordG_eq φ i (hS.conj_mem_U φ i hMC hg (coordG_mem φ i x))
    exact ⟨y, hy.symm⟩

theorem exists_scalar [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) (hMC : ¬ 𝐌 ≤ 𝐂) {z : G}
    (hzM : z ∈ 𝐌) (hzC : z ∈ 𝐂) (hzZ : ∀ y ∈ 𝐊, z * y * z⁻¹ * y⁻¹ ∈ 𝐁) :
    ∃ l : Kˣ, ∀ x, z * coordG φ i x * z⁻¹ = coordG φ i ((l : K) ^ 2 * x) := by
  set z' : normalizer (L : Set G) := ⟨z, hS.cent_le hzC⟩
  have key : ∀ a, ((φ.symm (normAct φ z' a) : L) : G) = z * φ.symm a * z⁻¹ :=
    fun a => normAct_symm_apply φ z' a
  have hzU : z ∈ normalizer (𝐔 : Set G) :=
    mem_normalizer_of_conj_le fun u hu => hS.conj_mem_U φ i hMC hzM hu
  have hαU : normAct φ z' ∈ autStab (rootU K i) := (mem_normalizer_pull_iff φ _ z').mp hzU
  have hker : ∀ y ∈ centralizer ((rootU K i : Subgroup (antiSp K)) : Set (antiSp K)),
      y⁻¹ * normAct φ z' y ∈ rootA K i := by
    intro y hy
    have hyK : ((φ.symm y : L) : G) ∈ 𝐊 := by
      rw [hS.centralizer_eq φ i]
      exact mem_sup_right (symm_mem_pull.mpr hy)
    have h1 := hzZ _ hyK
    rw [← key] at h1
    have h2 : ((φ.symm (normAct φ z' y * y⁻¹) : L) : G) ∈ 𝐁 ⊓ L :=
      ⟨by simpa [map_mul, map_inv] using h1, (φ.symm _).2⟩
    rw [zpowers_sup_inf_eq hS.t_mul_t (pull_le φ _) hS.t_not_mem (comm_pull φ hS)] at h2
    have h3 : normAct φ z' y * y⁻¹ ∈ rootA K i := symm_mem_pull.mp h2
    have h4 := (hS.axisStr i).A_normal_C y⁻¹ (inv_mem hy) _ h3
    rwa [show y⁻¹ * (normAct φ z' y * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * normAct φ z' y by group] at h4
  obtain ⟨a, ha, l, hα⟩ := ((hS.axisAut i).kernel_action _ hαU).mp hker
  refine ⟨l, fun x => ?_⟩
  have hcomm : rootCoord K i ((l : K) ^ 2 * x) * a = a * rootCoord K i ((l : K) ^ 2 * x) :=
    mem_centralizer_iff.mp ((hS.axisStr i).A_le_C ha) _ (rootCoord_mem' i _)
  have hd := (hS.axisStr i).d_coord l x
  have hX : (a * dHom K i l) * rootCoord K i x * (a * dHom K i l)⁻¹ =
      rootCoord K i ((l : K) ^ 2 * x) := by
    calc (a * dHom K i l) * rootCoord K i x * (a * dHom K i l)⁻¹
        = a * (dHom K i l * rootCoord K i x * (dHom K i l)⁻¹) * a⁻¹ := by group
      _ = rootCoord K i ((l : K) ^ 2 * x) := by rw [hd, ← hcomm, mul_inv_cancel_right]
  show z * ((φ.symm (rootCoord K i x) : L) : G) * z⁻¹ =
    ((φ.symm (rootCoord K i ((l : K) ^ 2 * x)) : L) : G)
  rw [← key, hα, MulAut.conj_apply, hX]

theorem cond [Finite G] [Finite K] (hS : TwoCoreSetup L K n t) (hMC : ¬ 𝐌 ≤ 𝐂) :
    (∀ m ∈ 𝐌, ∃ d ∈ (CFSG.pCore 2 𝐌).map 𝐌.subtype, ∃ h ∈ 𝐂 ⊓ 𝐌, d * h = m) ∧
      (CFSG.pCore 2 𝐌).map 𝐌.subtype ⊓ (𝐂 ⊓ 𝐌) = 𝐁 ∧
      (∀ d ∈ (CFSG.pCore 2 𝐌).map 𝐌.subtype, ∀ u ∈ 𝐔, d * u = u * d) ∧
      (∀ u ∈ 𝐔, ∃ d ∈ (CFSG.pCore 2 𝐌).map 𝐌.subtype, t⁻¹ * (d⁻¹ * t * d) = u) := by
  have hA := hS.affHyp φ i hMC
  set ρ := hA.affRep with hρ
  have hK : ∀ g ∈ 𝐌, ∀ y ∈ 𝐊, g * y * g⁻¹ ∈ 𝐊 :=
    fun g hg y hy => conj_mem_centralizer_of_mem_normalizer' hg hy
  have hBn : ∀ g ∈ 𝐌, ∀ b ∈ 𝐁, g * b * g⁻¹ ∈ 𝐁 :=
    fun g hg b hb => (mem_normalizer_iff.mp (hS.M_le_normalizer_B φ i hg) b).mp hb
  set Z := quotCent 𝐌 𝐊 𝐁 hK hBn with hZ
  have hKM : 𝐊 ≤ 𝐌 := centralizer_le_normalizer _
  have hker : ∀ g : 𝐌, ρ g = 1 ↔ (g : G) ∈ 𝐊 := by
    intro g
    rw [hA.affRep_eq_one_iff, mem_centralizer_sup_iff, mem_centralizer_zpowers_iff',
      mem_centralizer_iff]
    refine and_congr_right fun _ => ⟨fun h u hu => ?_, fun h x => (h _ (coordG_mem φ i x)).symm⟩
    obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
    exact (h x).symm
  have hzero : ∀ g : 𝐌, ρ g 0 = 0 ↔ (g : G) ∈ 𝐂 := by
    intro g
    rw [hA.affRep_zero_eq_zero_iff, mem_centralizer_singleton_iff]
  have hscalar : ∀ a : K, a ≠ 0 → ∃ z : 𝐌, (z : G) ∈ Z ∧ (z : G) ∈ 𝐂 ∧ ∀ x, ρ z x = a * x := by
    intro a ha
    obtain ⟨y, hy⟩ := exists_sq_eq a
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact ha (by rw [← hy]; ring)
    set l := Units.mk0 y hy0
    refine ⟨⟨_, hS.torus_mem_M φ i l⟩, ⟨hS.torus_mem_M φ i l, hS.torus_mem_quotCent φ i l⟩,
      hS.L_le (φ.symm _).2, fun x => ?_⟩
    refine hA.affRep_apply_of_scalar (hS.comm (φ.symm _).2).symm (fun x => ?_) x
    rw [hS.torus_conj φ i l x]
    simp only [l, Units.val_mk0, hy]
  have hZC : ∀ z : 𝐌, (z : G) ∈ Z → (z : G) ∈ 𝐂 → ρ z ∈ scalarPerm K := by
    intro z hzZ hzC
    obtain ⟨l, hl⟩ := hS.exists_scalar φ i hMC z.2 hzC hzZ.2
    exact ⟨(l : K) ^ 2, pow_ne_zero 2 l.ne_zero,
      hA.affRep_apply_of_scalar (mem_centralizer_singleton_iff.mp hzC) hl⟩
  set H : Subgroup (Equiv.Perm K) := ρ.range with hH
  set F : Subgroup (Equiv.Perm K) := (Z.subgroupOf 𝐌).map ρ with hF
  have hHaff : H ≤ affPerm K := by
    rintro _ ⟨g, rfl⟩
    exact hA.affRep_mem_affPerm g
  have hSH : scalarPerm K ≤ H := by
    rintro s ⟨a, ha, hs⟩
    obtain ⟨z, -, -, hz⟩ := hscalar a ha
    exact ⟨z, Equiv.ext fun x => (hz x).trans (hs x).symm⟩
  have hFH : F ≤ H := map_le_range _ _
  have hFn : (F.subgroupOf H).Normal := by
    refine ⟨fun f hf h' => ?_⟩
    rw [mem_subgroupOf] at hf ⊢
    obtain ⟨z, hz, hzf⟩ := hf
    obtain ⟨g, hg⟩ := h'.2
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf] at hz ⊢
      exact conj_mem_quotCent g.2 hz
    · rw [map_mul, map_mul, map_inv, hg, hzf]
      rfl
  have hK2 : 2 < Nat.card K := by
    rw [hS.card_K]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hS.two_le
  have hfrom0 : ∀ y : K, ∃ f ∈ F, f 0 = y := by
    obtain ⟨m, hmM, hmC⟩ := Set.not_subset.mp hMC
    set g : 𝐌 := ⟨m, hmM⟩
    have hw : ρ g⁻¹ 0 ≠ 0 := by
      rw [Ne, hzero]
      intro h
      exact hmC (by simpa using inv_mem h)
    obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne hK2 (1 : K)
    obtain ⟨z, hzZ, -, hz⟩ := hscalar a ha0
    have hfF : ρ (g * z * g⁻¹) ∈ F :=
      ⟨g * z * g⁻¹, mem_subgroupOf.mpr (conj_mem_quotCent g.2 hzZ), rfl⟩
    have hf0 : ρ (g * z * g⁻¹) 0 ≠ 0 := by
      obtain ⟨σ, b, hσ⟩ := hA.affRep_mem_affPerm g
      have h1 : ρ (g * z * g⁻¹) 0 = ρ g (a * ρ g⁻¹ 0) := by
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hz]
      have h2 : ρ g (ρ g⁻¹ 0) = 0 := by
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [h1, hσ]
      rw [hσ] at h2
      intro h3
      have h4 : σ (a * ρ g⁻¹ 0 - ρ g⁻¹ 0) = 0 := by
        rw [map_sub]
        linear_combination h3 - h2
      have h5 : a * ρ g⁻¹ 0 - ρ g⁻¹ 0 = 0 := σ.injective (h4.trans (map_zero σ).symm)
      have h6 : (a - 1) * ρ g⁻¹ 0 = 0 := by linear_combination h5
      rcases mul_eq_zero.mp h6 with h7 | h7
      · exact ha1 (sub_eq_zero.mp h7).symm
      · exact hw h7
    intro y
    by_cases hy : y = 0
    · exact ⟨1, one_mem F, by rw [hy]; rfl⟩
    · obtain ⟨z', hz'Z, -, hz'⟩ := hscalar (y / ρ (g * z * g⁻¹) 0) (div_ne_zero hy hf0)
      refine ⟨ρ z' * ρ (g * z * g⁻¹), mul_mem ⟨z', mem_subgroupOf.mpr hz'Z, rfl⟩ hfF, ?_⟩
      rw [Equiv.Perm.mul_apply, hz', div_mul_cancel₀ y hf0]
  have htrans : ∀ x y : K, ∃ f ∈ F, f x = y := by
    intro x y
    obtain ⟨f₁, hf₁, h₁⟩ := hfrom0 x
    obtain ⟨f₂, hf₂, h₂⟩ := hfrom0 y
    refine ⟨f₂ * f₁⁻¹, mul_mem hf₂ (inv_mem hf₁), ?_⟩
    rw [Equiv.Perm.mul_apply, ← h₁, show f₁⁻¹ (f₁ 0) = 0 from Equiv.Perm.inv_eq_iff_eq.mpr rfl,
      h₂]
  have hF0 : ∀ f : Equiv.Perm K, f ∈ F ∧ f 0 = 0 ↔ f ∈ scalarPerm K := by
    intro f
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, h0⟩
      exact hZC z (mem_subgroupOf.mp hz) ((hzero z).mp h0)
    · rintro ⟨a, ha, hf⟩
      obtain ⟨z, hzZ, -, hz⟩ := hscalar a ha
      have e : ρ z = f := Equiv.ext fun x => (hz x).trans (hf x).symm
      exact ⟨⟨z, mem_subgroupOf.mpr hzZ, e⟩, by rw [hf, mul_zero]⟩
  obtain ⟨-, hcore, hTF, -⟩ :=
    affine_scalar_sharply_two_transitive_normal_translations K H F hHaff hSH hFH hFn htrans hF0
  set D' : Subgroup G := Z ⊓ ((translPerm K).comap ρ).map 𝐌.subtype with hD'
  have hmemD' : ∀ g : 𝐌, (g : G) ∈ D' ↔ (g : G) ∈ Z ∧ ρ g ∈ translPerm K := by
    intro g
    constructor
    · rintro ⟨hgZ, g', hg', hgg'⟩
      have e : g' = g := Subtype.ext hgg'
      exact ⟨hgZ, e ▸ hg'⟩
    · rintro ⟨hgZ, hg⟩
      exact ⟨hgZ, g, hg, rfl⟩
  have hD'M : D' ≤ 𝐌 := fun _ hg => hg.1.1
  have hD'K : ∀ g ∈ D', g ∈ 𝐊 → g ∈ 𝐁 := fun g hg hgK => hS.mem_B_of_comm φ i hgK hg.1.2
  have hBD' : 𝐁 ≤ D' := by
    intro b hb
    have hbK := hS.B_le_K φ i hb
    have hbM := hKM hbK
    refine (hmemD' ⟨b, hbM⟩).mpr ⟨⟨hbM, fun y hy => ?_⟩, ?_⟩
    · have h1 := hS.conj_mem_B φ i hy (inv_mem hb)
      have e : b * y * b⁻¹ * y⁻¹ = b * (y * b⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hb h1
    · rw [(hker _).mpr hbK]
      exact one_mem _
  have hD'2 : IsPGroup 2 D' := by
    intro g
    have hgM := hD'M g.2
    obtain ⟨-, hgT⟩ := (hmemD' ⟨g, hgM⟩).mp g.2
    have hsq : ρ (⟨g, hgM⟩ ^ 2) = 1 := by
      obtain ⟨b, hb⟩ := hgT
      ext x
      rw [map_pow, pow_two, Equiv.Perm.mul_apply, hb, hb, add_assoc, CharTwo.add_self_eq_zero,
        add_zero]
      rfl
    have hg2B : (g : G) ^ 2 ∈ 𝐁 := hD'K _ (pow_mem g.2 2) ((hker _).mp hsq)
    obtain ⟨k, hk⟩ := hS.isPGroup_B φ i ⟨_, hg2B⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hk' ⊢
    rw [pow_succ', pow_mul]
    exact hk'
  have hTn : ((translPerm K).subgroupOf H).Normal := hcore ▸ CFSG.pCore_normal
  have hD'n : ∀ h ∈ 𝐌, ∀ d ∈ D', h * d * h⁻¹ ∈ D' := by
    intro h hh d hd
    have hdM := hD'M hd
    obtain ⟨hdZ, hdT⟩ := (hmemD' ⟨d, hdM⟩).mp hd
    refine (hmemD' ⟨h * d * h⁻¹, mul_mem (mul_mem hh hdM) (inv_mem hh)⟩).mpr
      ⟨conj_mem_quotCent hh hdZ, ?_⟩
    have h1 := hTn.conj_mem ⟨ρ ⟨d, hdM⟩, ⟨_, rfl⟩⟩ (mem_subgroupOf.mpr hdT) ⟨ρ ⟨h, hh⟩, ⟨_, rfl⟩⟩
    rw [mem_subgroupOf] at h1
    have e : ρ ⟨h * d * h⁻¹, mul_mem (mul_mem hh hdM) (inv_mem hh)⟩ =
        ρ ⟨h, hh⟩ * ρ ⟨d, hdM⟩ * (ρ ⟨h, hh⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact h1
  have hmaxD' : ∀ R : Subgroup G, R ≤ 𝐌 → (∀ h ∈ 𝐌, ∀ r ∈ R, h * r * h⁻¹ ∈ R) →
      IsPGroup 2 R → R ≤ D' := by
    intro R hRM hRn hR2
    have hRK : R ⊓ 𝐊 ≤ 𝐁 := hS.le_B φ i inf_le_right
      (fun k hk r hr => mem_inf.mpr ⟨hRn k (hKM hk) r (mem_inf.mp hr).1,
        (𝐊).mul_mem ((𝐊).mul_mem hk (mem_inf.mp hr).2) ((𝐊).inv_mem hk)⟩)
      (hR2.to_le inf_le_left)
    set R' : Subgroup (Equiv.Perm K) := (R.subgroupOf 𝐌).map ρ with hR'
    have hR'H : R' ≤ H := map_le_range _ _
    have hR'n : (R'.subgroupOf H).Normal := by
      refine ⟨fun f hf h' => ?_⟩
      rw [mem_subgroupOf] at hf ⊢
      obtain ⟨r, hr, hrf⟩ := hf
      obtain ⟨g, hg⟩ := h'.2
      refine ⟨g * r * g⁻¹, ?_, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf] at hr ⊢
        exact hRn g g.2 r hr
      · rw [map_mul, map_mul, map_inv, hg, hrf]
        rfl
    have hR'2 : IsPGroup 2 (R'.subgroupOf H) :=
      ((hR2.of_equiv (subgroupOfEquivOfLe hRM).symm).map ρ).of_equiv
        (subgroupOfEquivOfLe hR'H).symm
    have hle : R'.subgroupOf H ≤ CFSG.pCore 2 H := le_sSup ⟨hR'n, hR'2⟩
    rw [hcore] at hle
    intro r hr
    have hrT : ρ ⟨r, hRM hr⟩ ∈ translPerm K := by
      have h1 : (⟨ρ ⟨r, hRM hr⟩, ⟨_, rfl⟩⟩ : H) ∈ R'.subgroupOf H :=
        mem_subgroupOf.mpr ⟨⟨r, hRM hr⟩, mem_subgroupOf.mpr hr, rfl⟩
      exact mem_subgroupOf.mp (hle h1)
    refine (hmemD' ⟨r, hRM hr⟩).mpr ⟨⟨hRM hr, fun y hy => ?_⟩, hrT⟩
    have h1 : r * y * r⁻¹ * y⁻¹ ∈ R := by
      have h2 := hRn y (hKM hy) r⁻¹ (inv_mem hr)
      have e : r * y * r⁻¹ * y⁻¹ = r * (y * r⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hr h2
    exact hRK (mem_inf.mpr ⟨h1, (𝐊).mul_mem (hK r (hRM hr) y hy) ((𝐊).inv_mem hy)⟩)
  have hDeq : (CFSG.pCore 2 𝐌).map 𝐌.subtype = D' := pCore_map_eq hD'M hD'n hD'2 hmaxD'
  have htransl : ∀ b : K, ∃ z : 𝐌, (z : G) ∈ D' ∧ ρ z = Equiv.addRight b := by
    intro b
    obtain ⟨z, hz, hzτ⟩ := hTF (⟨b, fun _ => rfl⟩ : Equiv.addRight b ∈ translPerm K)
    refine ⟨z, (hmemD' z).mpr ⟨mem_subgroupOf.mp hz, ?_⟩, hzτ⟩
    rw [hzτ]
    exact ⟨b, fun _ => rfl⟩
  rw [hDeq]
  refine ⟨fun m hm => ?_, le_antisymm ?_ ?_, fun d hd u hu => ?_, fun u hu => ?_⟩
  ·
    obtain ⟨z, hzD, hzτ⟩ := htransl (ρ ⟨m, hm⟩ 0)
    refine ⟨z, hzD, (z : G)⁻¹ * m, mem_inf.mpr ⟨?_, (𝐌).mul_mem ((𝐌).inv_mem z.2) hm⟩,
      by group⟩
    have h0 : ρ (z⁻¹ * ⟨m, hm⟩) 0 = 0 := by
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, hzτ, Equiv.Perm.inv_eq_iff_eq]
      exact (zero_add _).symm
    exact (hzero _).mp h0
  ·
    rintro d ⟨hdD, hdC, hdM⟩
    obtain ⟨-, b, hb⟩ := (hmemD' ⟨d, hdM⟩).mp hdD
    have h0 := (hzero ⟨d, hdM⟩).mpr hdC
    have hb0 : b = 0 := by
      have := hb 0
      rw [h0, zero_add] at this
      exact this.symm
    have h1 : ρ ⟨d, hdM⟩ = 1 := Equiv.ext fun x => by
      rw [hb, hb0, add_zero]
      rfl
    exact hD'K d hdD ((hker _).mp h1)
  ·
    intro b hb
    exact ⟨hBD' hb, K_le_C φ i (hS.B_le_K φ i hb), hKM (hS.B_le_K φ i hb)⟩
  ·
    have hdM := hD'M hd
    obtain ⟨-, hdT⟩ := (hmemD' ⟨d, hdM⟩).mp hd
    obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
    have h1 := hA.conj_ι_of_mem_translPerm hdT x
    calc d * coordG φ i x = (d * coordG φ i x * d⁻¹) * d := by group
      _ = coordG φ i x * d := by rw [h1]
  ·
    obtain ⟨b, rfl⟩ := exists_coordG_eq φ i hu
    obtain ⟨z, hzD, hzτ⟩ := htransl b
    refine ⟨(z : G)⁻¹, inv_mem hzD, ?_⟩
    have h1 := hA.ι_affRep_zero z
    rw [← hρ, hzτ, show (Equiv.addRight b) (0 : K) = b from zero_add b] at h1
    rw [h1, inv_inv, hS.t_inv]

end Cond

end TwoCoreSetup

section Quotient

variable {G : Type*} [Group G]

theorem exists_quotient_mulEquiv {D B U : Subgroup G} {t : G} [(B.subgroupOf D).Normal]
    (hU : ∀ d ∈ D, t⁻¹ * (d⁻¹ * t * d) ∈ U) (hcomm : ∀ d ∈ D, ∀ u ∈ U, d * u = u * d)
    (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hker : ∀ d ∈ D, d⁻¹ * t * d = t ↔ d ∈ B)
    (hsurj : ∀ u ∈ U, ∃ d ∈ D, t⁻¹ * (d⁻¹ * t * d) = u) :
    ∃ e : (↥D ⧸ B.subgroupOf D) ≃* ↥U, ∀ d : D, (e d : G) = t⁻¹ * ((d : G)⁻¹ * t * d) := by
  let θ : D →* U :=
    { toFun := fun d => ⟨t⁻¹ * ((d : G)⁻¹ * t * d), hU d d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun d₁ d₂ => Subtype.ext (by
        have h1 := hcomm d₂ d₂.2 _ (hU d₁ d₁.2)
        show t⁻¹ * (((d₁ : G) * d₂)⁻¹ * t * (d₁ * d₂)) =
          t⁻¹ * ((d₁ : G)⁻¹ * t * d₁) * (t⁻¹ * ((d₂ : G)⁻¹ * t * d₂))
        rw [hUc _ (hU d₁ d₁.2) _ (hU d₂ d₂.2)]
        calc t⁻¹ * (((d₁ : G) * d₂)⁻¹ * t * (d₁ * d₂))
            = t⁻¹ * ((d₂ : G)⁻¹ * t * d₂) * ((d₂ : G)⁻¹ * (t⁻¹ * ((d₁ : G)⁻¹ * t * d₁)) * d₂) := by
              group
          _ = t⁻¹ * ((d₂ : G)⁻¹ * t * d₂) * (t⁻¹ * ((d₁ : G)⁻¹ * t * d₁)) := by
              rw [show (d₂ : G)⁻¹ * (t⁻¹ * ((d₁ : G)⁻¹ * t * d₁)) * d₂ =
                t⁻¹ * ((d₁ : G)⁻¹ * t * d₁) by rw [mul_assoc, ← h1, inv_mul_cancel_left]]) }
  have hθker : θ.ker = B.subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hker d d.2, Subtype.ext_iff]
    show t⁻¹ * ((d : G)⁻¹ * t * d) = 1 ↔ _
    rw [inv_mul_eq_one, eq_comm]
  have hθsurj : Function.Surjective θ := fun u => by
    obtain ⟨d, hd, hdu⟩ := hsurj u u.2
    exact ⟨⟨d, hd⟩, Subtype.ext hdu⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hθker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj), fun d => rfl⟩

end Quotient

end RootAxisTwoCore

open Subgroup GomiFusion RootAxisTwoCore
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.RankThree.PartOne.KCRootAxis
open scoped Pointwise

theorem standard_symplectic_four_root_axis_normalizer_two_core
    {G : Type} [Group G] [Finite G] (hO : CFSG.Open.standardComponentOddCore G = ⊥)
    {L : Subgroup G} (hL : CFSG.Open.standardComponentIsStandard L) (hLn : ¬ L.Normal)
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G))))
    {t : centralizer (L : Set G)} (htT : t ∈ T) (ht : orderOf t = 2)
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({(t : G)} : Set G)) = ⊥)
    (φ : L ≃* antiSp K) (i : Axis) :
    let C := centralizer ({(t : G)} : Set G)
    let U := ((rootU K i).comap φ.toMonoidHom).map L.subtype
    let A := ((rootA K i).comap φ.toMonoidHom).map L.subtype
    let Ci := L ⊓ centralizer (U : Set G)
    let V := zpowers (t : G) ⊔ U
    let B := zpowers (t : G) ⊔ A
    let M := normalizer (V : Set G)
    let D := (CFSG.pCore 2 M).map M.subtype
    (centralizer (V : Set G) = zpowers (t : G) ⊔ Ci ∧ zpowers (t : G) ⊓ Ci = ⊥ ∧
        ∀ c ∈ Ci, (t : G) * c = c * t) ∧
      (CFSG.pCore 2 (centralizer (V : Set G))).map (centralizer (V : Set G)).subtype = B ∧
      M ≤ normalizer (B : Set G) ∧ C ⊓ M = C ⊓ normalizer (B : Set G) ∧
      (¬ M ≤ C →
        {x : G | ∃ m ∈ M, x = m⁻¹ * t * m} = {x | ∃ u ∈ U, x = t * u} ∧
        (D : Set G) * ((C ⊓ M : Subgroup G) : Set G) = M ∧
        D ⊓ (C ⊓ M) = B ∧ (B ≤ M ∧ (B.subgroupOf M).Normal) ∧
        ∃ _ : (B.subgroupOf D).Normal, ∃ e : (↥D ⧸ B.subgroupOf D) ≃* ↥U,
          (∀ d : D, (e d : G) = (t : G)⁻¹ * ((d : G)⁻¹ * t * d)) ∧
          (∀ h ∈ C ⊓ M, ∀ d : D, ∃ d' : D, (d' : G) = h⁻¹ * d * h ∧
            (e d' : G) = h⁻¹ * e d * h) ∧
          Nat.card (↥D ⧸ B.subgroupOf D) = 2 ^ n ∧
          IsElementaryAbelian 2 (↥D ⧸ B.subgroupOf D)) := by
  intro C U A Ci V B M D
  have hS0 := setup_of_standard hL hn hK φ T hT htT ht hcore
  have hS : TwoCoreSetup L K n (t : G) :=
    { two_le := hn
      card_K := hK
      t_mul_t := hS0.t_mul_t
      L_le := hS0.L_le
      cent_le := hS0.cent_le
      cent_inf := hS0.cent_inf.trans (hS0.T_eq_zpowers hO hLn)
      not_conj := hS0.conj_not_mem_L hO hLn }
  have hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := by
    intro u hu v hv
    obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
    obtain ⟨y, rfl⟩ := exists_coordG_eq φ i hv
    rw [← coordG_add, ← coordG_add, add_comm]
  have hsq : ∀ u ∈ U, u ^ 2 = 1 := by
    intro u hu
    obtain ⟨x, rfl⟩ := exists_coordG_eq φ i hu
    rw [pow_two, ← coordG_add, CharTwo.add_self_eq_zero, coordG_zero]
  have hMB : M ≤ normalizer (B : Set G) := hS.M_le_normalizer_B φ i
  have hBM : B ≤ M := (hS.B_le_K φ i).trans (centralizer_le_normalizer _)
  refine ⟨⟨(hS.centralizer_eq φ i).trans
    (congrArg (zpowers (t : G) ⊔ ·) (TwoCoreSetup.pull_rootC_eq φ i)), hS.zpowers_inf inf_le_left,
    fun c hc => hS.comm hc.1⟩, hS.pCore_K_eq φ i, hMB, hS.inf_normalizer_eq φ i, fun hMC => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hS.cond φ i hMC
  have hDM : D ≤ M := map_subtype_le _
  have hBD : (B.subgroupOf D).Normal := ⟨fun b hb d => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (hMB (hDM d.2)) b).mp (mem_subgroupOf.mp hb))⟩
  have hU : ∀ d ∈ D, (t : G)⁻¹ * (d⁻¹ * t * d) ∈ U := fun d hd => by
    rw [hS.t_inv]
    exact hS.conj_t_mem φ i (hDM hd)
  have hker : ∀ d ∈ D, d⁻¹ * t * d = t ↔ d ∈ B := by
    intro d hd
    constructor
    · intro e
      have hdC : d ∈ C := by
        rw [mem_centralizer_singleton_iff]
        calc d * t = d * (d⁻¹ * t * d) := by rw [e]
          _ = t * d := by group
      exact h2.le (mem_inf.mpr ⟨hd, mem_inf.mpr ⟨hdC, hDM hd⟩⟩)
    · intro hb
      have hdC := TwoCoreSetup.K_le_C φ i (hS.B_le_K φ i hb)
      rw [mem_centralizer_singleton_iff] at hdC
      rw [mul_assoc, ← hdC, inv_mul_cancel_left]
  obtain ⟨e, he⟩ := exists_quotient_mulEquiv hU h3 hUc hker h4
  refine ⟨?_, ?_, h2, ⟨hBM, ⟨fun b hb m => ?_⟩⟩, hBD, e, he, fun h hh d => ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨_, hS.conj_t_mem φ i hm, by rw [← mul_assoc, hS.t_mul_t, one_mul]⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨m, hm, hmu⟩ := hS.exists_conj_eq φ i hMC hu
      exact ⟨m, hm, hmu.symm⟩
  · ext m
    simp only [Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨d, hd, h, hh, rfl⟩
      exact mul_mem (hDM hd) hh.2
    · intro hm
      exact h1 m hm
  · exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp (hMB m.2) b).mp (mem_subgroupOf.mp hb))
  · have hd' : h⁻¹ * d * h ∈ D := by
      obtain ⟨p, hp, hpd⟩ := d.2
      refine ⟨⟨h, hh.2⟩⁻¹ * p * ⟨h, hh.2⟩, ?_, by rw [← hpd]; rfl⟩
      simpa using CFSG.pCore_normal.conj_mem p hp ⟨h, hh.2⟩⁻¹
    refine ⟨⟨_, hd'⟩, rfl, ?_⟩
    rw [he, he]
    have e1 : h * t * h⁻¹ = t := by
      rw [mem_centralizer_singleton_iff.mp hh.1, mul_inv_cancel_right]
    have e2 : h * (t : G)⁻¹ * h⁻¹ = (t : G)⁻¹ := by
      calc h * (t : G)⁻¹ * h⁻¹ = (h * t * h⁻¹)⁻¹ := by group
        _ = (t : G)⁻¹ := by rw [e1]
    calc (t : G)⁻¹ * ((h⁻¹ * d * h)⁻¹ * t * (h⁻¹ * d * h))
        = h⁻¹ * (h * (t : G)⁻¹ * h⁻¹) * (d : G)⁻¹ * (h * t * h⁻¹) * d * h := by group
      _ = h⁻¹ * ((t : G)⁻¹ * ((d : G)⁻¹ * t * d)) * h := by rw [e1, e2]; group
  · exact (Nat.card_congr e.toEquiv).trans ((card_U φ i).trans hK)
  · refine { is_comm := ⟨fun a b => e.injective ?_⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => e.injective ?_ }
    · rw [map_mul, map_mul]
      exact Subtype.ext (hUc _ (e a).2 _ (e b).2)
    · rw [map_pow, map_one]
      exact Subtype.ext (hsq _ (e g).2)

end CFSG.LocalAnalysis.SymplecticFourStandard
