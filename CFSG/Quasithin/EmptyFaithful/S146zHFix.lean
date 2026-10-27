module

public import CFSG.Quasithin.EmptyFaithful.S146zHFpf
public import CFSG.Quasithin.EmptyFaithful.S146zHWsub
public import CFSG.Quasithin.EmptyFaithful.S146zHFaith
public import CFSG.Quasithin.EmptyFaithful.S146D5
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.G10Four
public import CFSG.Quasithin.Background.G10Three
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.Quasithin.EmptyFaithful.S143EB
public import CFSG.Quasithin.EmptyFaithful.S143VFin
public import CFSG.Quasithin.EmptyFaithful.S143VG94
public import CFSG.Quasithin.EmptyFaithful.S143VQG
public import CFSG.Quasithin.EmptyFaithful.S143VTwo
public import CFSG.Quasithin.EmptyFaithful.S143VZU
public import CFSG.Quasithin.EmptyFaithful.S143WAL
public import CFSG.Quasithin.EmptyFaithful.S143WCl
public import CFSG.Quasithin.EmptyFaithful.S143WE
public import CFSG.Quasithin.EmptyFaithful.S143WNo
public import CFSG.Quasithin.EmptyFaithful.S143WT
public import CFSG.Quasithin.EmptyFaithful.S146F10
public import CFSG.Quasithin.EmptyFaithful.S146F13
public import CFSG.Quasithin.EmptyFaithful.S146F15
public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146F17
public import CFSG.Quasithin.EmptyFaithful.S146F20
public import CFSG.Quasithin.EmptyFaithful.S146zHDih
public import CFSG.Quasithin.EmptyFaithful.S151cCasei
public import CFSG.Quasithin.EmptyFaithful.S151cStmt
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabInputs
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
open scoped commutatorElement Pointwise

section Fix

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem clsU_mem_kOf_uHi (S : Setting146 G T M) (hH : IsHTM T M H)
    (h : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {Hi : Subgroup G} (hHi : Hi ≤ H) {u : G} (hu : u ∈ conjClosure (VZ T M) H)
    (hui : u ∈ uHi T M H Hi) : clsU h hu ∈ kOf (rhoH h) := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hcomm_le : ⁅conjClosure (VZ T M) H, Hi⁆ ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer (hHi.trans hHU)
  have hAN : ⁅conjClosure (VZ T M) H, Hi⁆ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hcomm_le.trans hUZ
  have hmul : (↑(⁅conjClosure (VZ T M) H, Hi⁆ ⊔ quasithinOmegaOneCenter T) : Set G) =
      ↑⁅conjClosure (VZ T M) H, Hi⁆ * ↑(quasithinOmegaOneCenter T) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN
  have hu' : u ∈ (↑(⁅conjClosure (VZ T M) H, Hi⁆ ⊔ quasithinOmegaOneCenter T) : Set G) := hui
  rw [hmul] at hu'
  obtain ⟨k, hk, z, hz, rfl⟩ := Set.mem_mul.mp hu'
  have hkUK : k ∈ ⁅conjClosure (VZ T M) H, H⁆ := Subgroup.commutator_mono le_rfl hHi hk
  have h1 := clsU_mem_kOf h hkUK
  have h2 : clsU h hu =
      clsU h (S145.commutator_le_of_le_normalizer hHU hkUK) := by
    rw [clsU_eq_iff]
    have e : (k * z)⁻¹ * k = z⁻¹ := by group
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem hz
  rw [h2]
  exact h1

@[expose] def fixerOf {T V L V₁ Vp : Subgroup G} (h : HypF91 T V L V₁ Vp H) (w : UMod h) : Subgroup G where
  carrier := {y | ∃ hy : y ∈ H, rhoH h ⟨y, hy⟩ w = w}
  mul_mem' := by
    rintro y y' ⟨hy, hyw⟩ ⟨hy', hy'w⟩
    refine ⟨H.mul_mem hy hy', ?_⟩
    have e : (⟨y * y', H.mul_mem hy hy'⟩ : ↥H) = ⟨y, hy⟩ * ⟨y', hy'⟩ := rfl
    rw [e, map_mul, MulAut.mul_apply, hy'w, hyw]
  one_mem' := ⟨H.one_mem, by
    have e : (⟨1, H.one_mem⟩ : ↥H) = 1 := rfl
    rw [e, map_one]
    rfl⟩
  inv_mem' := by
    rintro y ⟨hy, hyw⟩
    refine ⟨H.inv_mem hy, ?_⟩
    have e : (⟨y⁻¹, H.inv_mem hy⟩ : ↥H) = (⟨y, hy⟩ : ↥H)⁻¹ := rfl
    rw [e, map_inv]
    calc ((rhoH h ⟨y, hy⟩)⁻¹) w = ((rhoH h ⟨y, hy⟩)⁻¹) (rhoH h ⟨y, hy⟩ w) := by rw [hyw]
      _ = w := by simp

theorem mem_fixerOf {T V L V₁ Vp : Subgroup G} (h : HypF91 T V L V₁ Vp H) {w : UMod h} {y : G}
    (hy : y ∈ H) : y ∈ fixerOf h w ↔ rhoH h ⟨y, hy⟩ w = w :=
  ⟨fun ⟨_, hyw⟩ => hyw, fun hyw => ⟨hy, hyw⟩⟩

theorem IsDecP.eq_one_of_fix (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    (φ : ↥H₁ →* DihedralGroup p) (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H)
    {a : ↥H₁} (ha : φ a = DihedralGroup.r 1) {w : UMod h91}
    (hw : w ∈ Wsub h91 (uHi T M H H₁))
    (hfix : rhoH h91 ⟨a, h.le (h.le₁ a.2)⟩ w = w) : w = 1 := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  obtain ⟨u, hu, hui, rfl⟩ := exists_clsU_of_mem_Wsub h91 (uHi_le_conjClosure hH₁H) hw
  have hwK := clsU_mem_kOf_uHi S hH h91 hH₁H hu hui
  refine S.cfpMod hred h91 _ hwK ?_
  intro y hyPQ
  have hsup := h.le_sup_zpowers S hred φ hker ha hyPQ
  have haF : (a : G) ∈ fixerOf h91 (clsU h91 hu) := (mem_fixerOf h91 (h.le (h.le₁ a.2))).mpr hfix
  have hH₂F : H₂ ≤ fixerOf h91 (clsU h91 hu) := by
    intro y hy
    have hyH : y ∈ H := hH₂H hy
    rw [mem_fixerOf h91 hyH, rhoH_clsU_eq_iff]
    have h1 : ⁅u, y⁆ ∈ quasithinOmegaOneCenter T := h.cent₁ (Subgroup.commutator_mem_commutator hui hy)
    have e : y * u * y⁻¹ * u⁻¹ = (⁅u, y⁆)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem h1
  have hle : Subgroup.zpowers (a : G) ⊔ H₂ ≤ fixerOf h91 (clsU h91 hu) :=
    sup_le ((Subgroup.zpowers_le).mpr haF) hH₂F
  exact ((mem_fixerOf h91 y.2).mp (hle hsup))

end Fix

end CFSG.Quasithin
