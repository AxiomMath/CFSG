module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2214_pCoreOf_inf_le {M X : Subgroup G} (hXM : X ≤ M) : pCoreOf 2 M ⊓ X ≤ pCoreOf 2 X := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ ?_
  · intro x hx
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨uc22br4_conj_mem_map_of_characteristic (D := CFSG.pCore 2 ↥M) (le_normalizer (hXM hx)) hy1,
        X.mul_mem (X.mul_mem hx hy2) (X.inv_mem hx)⟩
    · rintro ⟨hy1, hy2⟩
      have e : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
      rw [e]
      refine ⟨uc22br4_conj_mem_map_of_characteristic (D := CFSG.pCore 2 ↥M) (le_normalizer (M.inv_mem (hXM hx)))
        hy1, X.mul_mem (X.mul_mem (X.inv_mem hx) hy2) (X.inv_mem (X.inv_mem hx))⟩
  · exact (CFSG.pCore_isPGroup.map M.subtype).to_le inf_le_left

theorem uc22p2214_centralizesBar_conjClosure {M K : Subgroup G} {a : G}
    (ha : a ∈ normalizer (conjClosure M K : Set G))
    (h : ∀ K' ∈ conjSetOf M K, ∀ k ∈ K', a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure M K)) :
    CentralizesBar a (conjClosure M K) := by
  set X := conjClosure M K
  have hnorm : ∀ x ∈ X, ∀ y ∈ pCoreOf 2 X, x * y * x⁻¹ ∈ pCoreOf 2 X := fun x hx y hy =>
    uc22br4_conj_mem_map_of_characteristic (D := CFSG.pCore 2 ↥X) (le_normalizer hx) hy
  let H : Subgroup G :=
    { carrier := {x | x ∈ X ∧ a * x * a⁻¹ * x⁻¹ ∈ pCoreOf 2 X}
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨X.mul_mem hx hy, ?_⟩
        have e : a * (x * y) * a⁻¹ * (x * y)⁻¹ =
            (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e]
        exact (pCoreOf 2 X).mul_mem hx' (hnorm x hx _ hy')
      one_mem' := ⟨X.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨X.inv_mem hx, ?_⟩
        have e : a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact hnorm _ (X.inv_mem hx) _ ((pCoreOf 2 X).inv_mem hx') }
  have hXH : X ≤ H := iSup₂_le fun K' hK' k hk =>
    ⟨le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) K' hK' le_rfl hk, h K' hK' k hk⟩
  exact ⟨ha, fun x hx => (hXH hx).2⟩

theorem uc22p2214_calC_of_mem_conjSetOf {M K K' : Subgroup G} (hK : K ∈ calC M) (hK' : K' ∈ conjSetOf M K) :
    K' ∈ calC M := by
  obtain ⟨g, hg, rfl⟩ := hK'
  have hconj : K.map (MulAut.conj g).toMonoidHom = uniqueFourConj g⁻¹ K := by
    simp [uniqueFourConj]
  rw [hconj]
  exact uc22p22u_calC_conj Subgroup.le_normalizer hK (M.inv_mem hg)

theorem uc22p2214_not_le_centralizer_of_mem_conjSetOf {M V K K' : Subgroup G} (hVM : M ≤ normalizer (V : Set G))
    (hKV : ¬ K ≤ centralizer (V : Set G)) (hK' : K' ∈ conjSetOf M K) : ¬ K' ≤ centralizer (V : Set G) := by
  obtain ⟨g, hg, rfl⟩ := hK'
  intro hle
  apply hKV
  intro k hk
  rw [mem_centralizer_iff]
  intro v hv
  have hgv : g * v * g⁻¹ ∈ V := (mem_normalizer_iff.1 (hVM hg) v).1 hv
  have h1 := mem_centralizer_iff.1 (hle ⟨k, hk, rfl⟩) _ hgv
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have h2 : g * (v * k) * g⁻¹ = g * (k * v) * g⁻¹ := by
    calc g * (v * k) * g⁻¹ = g * v * g⁻¹ * (g * k * g⁻¹) := by group
      _ = g * k * g⁻¹ * (g * v * g⁻¹) := h1
      _ = g * (k * v) * g⁻¹ := by group
  simpa using h2

end CFSG.LocalAnalysis.UniquenessCase.UC22
