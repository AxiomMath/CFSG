module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommParts

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Canon

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

theorem canon_conj_of_normalizer {R : Subgroup G} {c x : G} (hc : c ∈ normalizer (R : Set G))
    (hx : x ∈ R) : c * x * c⁻¹ ∈ R :=
  (mem_normalizer_iff.mp hc x).mp hx

theorem canon_conj_mem_normalizer {R : Subgroup G} {c x : G} (hc : c ∈ normalizer (R : Set G))
    (hx : x ∈ normalizer (R : Set G)) : c * x * c⁻¹ ∈ normalizer (R : Set G) := by
  rw [mem_normalizer_iff]
  intro r
  have hc' := mem_normalizer_iff.mp hc
  have hx' := mem_normalizer_iff.mp hx
  have e : c * x * c⁻¹ * r * (c * x * c⁻¹)⁻¹ = c * (x * (c⁻¹ * r * c) * x⁻¹) * c⁻¹ := by
    group
  rw [e, ← hc' (x * (c⁻¹ * r * c) * x⁻¹), ← hx' (c⁻¹ * r * c)]
  have h3 := hc' (c⁻¹ * r * c)
  rw [show c * (c⁻¹ * r * c) * c⁻¹ = r by group] at h3
  exact h3.symm

theorem canon_N5_1 (h : FullCenter.FCHyp L K n φ t) (i : Axis)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    (k : Axis) {c : G} (hc : c ∈ normalizer ((Q φ t : Subgroup G) : Set G)) :
    c ∈ normalizer ((zpowers t ⊔ pull φ (rootA K k) : Subgroup G) : Set G) :=
  SingleComm.normalizer_Q_le_N h i hne hbot k hc

theorem canon_N5_2 (h : FullCenter.FCHyp L K n φ t) (i : Axis) {c : G}
    (hc : c ∈ normalizer ((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Set G)) :
    c ∈ normalizer (U φ i : Set G) :=
  h.N_le_normalizer_U i hc

theorem canon_N5_3 (h : FullCenter.FCHyp L K n φ t) (i : Axis) {c : G}
    (hcC : c ∈ centralizer ({t} : Set G)) (hcU : c ∈ normalizer (U φ i : Set G)) :
    c ∈ normalizer ((zpowers t ⊔ U φ i : Subgroup G) : Set G) :=
  (h.twoCore.mem_normalizer_zpowers_sup_iff hcC (pull_le φ (rootU K i))).mpr hcU

theorem canon_N5_4 (h : FullCenter.FCHyp L K n φ t) (i : Axis)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    {c : G} (hcC : c ∈ centralizer ({t} : Set G))
    (hcN : c ∈ normalizer ((Q φ t : Subgroup G) : Set G)) :
    c ∈ normalizer ((D φ t i : Subgroup G) : Set G) :=
  RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx =>
    FullCenter.conj_mem_pCore_map
      (canon_N5_3 h i hcC (canon_N5_2 h i (canon_N5_1 h i hne hbot i hcN))) hx

theorem canon_N5_5 (h : FullCenter.FCHyp L K n φ t) (i : Axis)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    (k : Axis) {c : G} (hcN : c ∈ normalizer ((Q φ t : Subgroup G) : Set G)) :
    c ∈ normalizer ((R φ t k : Subgroup G) : Set G) :=
  SingleComm.normalizer_Q_le_normalizer_R h i hne hbot k hcN

theorem canon_N5_6 (h : FullCenter.FCHyp L K n φ t) (i : Axis)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    {c : G} (hcN : c ∈ normalizer ((Q φ t : Subgroup G) : Set G)) :
    c ∈ normalizer ((Kc φ t i.swap : Subgroup G) : Set G) :=
  SingleComm.Nhat_le_normalizer_K_swap h i hne hbot (SingleComm.W_sq_eq' h i hne hbot) one_ne_zero
    (SingleComm.normalizer_Q_le_Nhat h i hne hbot hcN)

theorem canon_N5_7 (h : FullCenter.FCHyp L K n φ t) (i : Axis)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    {c : G} (hcN : c ∈ normalizer ((Q φ t : Subgroup G) : Set G)) :
    c ∈ En φ t i.swap :=
  mem_inf.mpr ⟨RootAxisTwoCore.mem_normalizer_of_conj_le fun e he =>
      SingleComm.conj_normalizer_Q_mem_E h i hne hbot i.swap hcN he,
    canon_N5_6 h i hne hbot hcN⟩

theorem canon_N5_8 (h : FullCenter.FCHyp L K n φ t) (i : Axis)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    {c : G} (hcC : c ∈ centralizer ({t} : Set G))
    (hcN : c ∈ normalizer ((P φ ⊔ zpowers t : Subgroup G) : Set G)) :
    c ∈ normalizer (Tplus φ t i : Set G) := by
  have hcR_i : c ∈ normalizer ((R φ t i : Subgroup G) : Set G) :=
    canon_N5_5 h i hne hbot i hcN
  have hcR_j : c ∈ normalizer ((R φ t i.swap : Subgroup G) : Set G) :=
    canon_N5_5 h i hne hbot i.swap hcN
  have hcD : c ∈ normalizer ((D φ t i : Subgroup G) : Set G) :=
    canon_N5_4 h i hne hbot hcC hcN
  have hcEn : c ∈ En φ t i.swap := canon_N5_7 h i hne hbot hcN
  have hP1 : ∀ x ∈ P₁ φ t i, c * x * c⁻¹ ∈ P₁ φ t i :=
    fun x hx => FullCenter.conj_mem_pCore_map hcD hx
  have hP2 : ∀ x ∈ P₂ φ t i.swap, c * x * c⁻¹ ∈ P₂ φ t i.swap :=
    fun x hx => FullCenter.conj_mem_pCore_map hcEn hx
  have hRi : ∀ x ∈ R φ t i, c * x * c⁻¹ ∈ R φ t i :=
    fun x hx => canon_conj_of_normalizer hcR_i hx
  have hRj : ∀ x ∈ R φ t i.swap, c * x * c⁻¹ ∈ R φ t i.swap :=
    fun x hx => canon_conj_of_normalizer hcR_j hx
  have hT1 : ∀ x ∈ T₁ φ t i, c * x * c⁻¹ ∈ T₁ φ t i :=
    fun x hx => RootAxisTwoCore.conj_mem_sup hRi hP1 hx
  have hT0 : ∀ x ∈ T₀ φ t i.swap, c * x * c⁻¹ ∈ T₀ φ t i.swap :=
    fun x hx => RootAxisTwoCore.conj_mem_sup hRj hP2 hx
  have hT2 : ∀ x ∈ T₂ φ t i.swap, c * x * c⁻¹ ∈ T₂ φ t i.swap := fun x hx =>
    mem_inf.mpr ⟨hT0 x (mem_inf.mp hx).1, canon_conj_mem_normalizer hcR_j (mem_inf.mp hx).2⟩
  have hTbar : ∀ x ∈ Tbar φ t i, c * x * c⁻¹ ∈ Tbar φ t i :=
    fun x hx => RootAxisTwoCore.conj_mem_sup hT1 hT2 hx
  exact RootAxisTwoCore.mem_normalizer_of_conj_le fun x hx =>
    RootAxisTwoCore.conj_mem_sup hTbar hT0 hx

end Canon

theorem canonicity : CanonicityStatement := by
  intro G _ _ _ L K _ _ _ n φ t i hS c hc
  exact canon_N5_8 hS.fc i hS.ne_bot hS.eq_bot (mem_inf.mp hc).1 (mem_inf.mp hc).2

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
