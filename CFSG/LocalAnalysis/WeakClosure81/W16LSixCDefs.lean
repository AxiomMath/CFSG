module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2G1Bar
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIa

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem IsMinFam16.V_le_H (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) : V ≤ H :=
  h.V_le_S.trans hH.1.1

theorem IsMinFam16.conjClosure_le_H (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) :
    CFSG.Quasithin.conjClosure V H ≤ H :=
  CFSG.Quasithin.conjClosure_le fun g hg z hz =>
    H.mul_mem (H.mul_mem hg (IsMinFam16.V_le_H h hH hz)) (H.inv_mem hg)

theorem iSub16_le_conjClosure (V H : Subgroup G) :
    iSub16 V H ≤ CFSG.Quasithin.conjClosure V H :=
  CFSG.Quasithin.conjClosure_mono inf_le_left le_rfl

@[expose] def IsMinFam16.inclK (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) :
    ↥(CFSG.Quasithin.conjClosure V H) →* ↥H :=
  Subgroup.inclusion (IsMinFam16.conjClosure_le_H h hH)

@[expose] noncomputable def IsMinFam16.kToHatX (h : Cex16 M V₀ V U S)
    (hH : IsMinFam16 M U S H) (D : ModDataE H (iSub16 V H)) :
    ↥(CFSG.Quasithin.conjClosure V H) →* hatX D V :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))).comp
    ((D.ρ.comp (IsMinFam16.inclK h hH)).codRestrict (hatK D V) fun k =>
      D.mem_img.2 ⟨IsMinFam16.inclK h hH k, k.2, rfl⟩)

private lemma w16l_kToHatX_apply (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H)
    (D : ModDataE H (iSub16 V H)) (k : ↥(CFSG.Quasithin.conjClosure V H)) :
    IsMinFam16.kToHatX h hH D k =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))
        (⟨D.ρ (IsMinFam16.inclK h hH k),
          D.mem_img.2 ⟨IsMinFam16.inclK h hH k, k.2, rfl⟩⟩ : ↥(hatK D V)) :=
  rfl

private lemma w16l_coe_inclK (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H)
    (k : ↥(CFSG.Quasithin.conjClosure V H)) :
    ((IsMinFam16.inclK h hH k : ↥H) : G) = (k : G) :=
  rfl

private lemma w16l_surjective_kToHatX (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H)
    (D : ModDataE H (iSub16 V H)) :
    Function.Surjective (IsMinFam16.kToHatX h hH D) := by
  intro y
  obtain ⟨y', hy'⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK D V)) y
  obtain ⟨j, hjK, hjρ⟩ := D.mem_img.1 y'.2
  refine ⟨⟨(j : G), hjK⟩, ?_⟩
  rw [w16l_kToHatX_apply]
  have hyeq : (⟨D.ρ (IsMinFam16.inclK h hH ⟨(j : G), hjK⟩),
      D.mem_img.2 ⟨IsMinFam16.inclK h hH ⟨(j : G), hjK⟩,
        by rw [w16l_coe_inclK h hH]; exact hjK, rfl⟩⟩ :
        ↥(hatK D V)) = y' := by
    apply Subtype.ext
    change D.ρ (IsMinFam16.inclK h hH ⟨(j : G), hjK⟩) = (y' : LGL 2 D.W)
    rw [show IsMinFam16.inclK h hH ⟨(j : G), hjK⟩ = j from Subtype.ext rfl]
    exact hjρ
  rw [hyeq, hy']

private lemma w16l_map_kToHatX_V (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H)
    (D : ModDataE H (iSub16 V H)) :
    (V.subgroupOf (CFSG.Quasithin.conjClosure V H)).map (IsMinFam16.kToHatX h hH D) =
      hatS D V := by
  change (V.subgroupOf (CFSG.Quasithin.conjClosure V H)).map (IsMinFam16.kToHatX h hH D) =
    ((D.img V).subgroupOf (hatK D V)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)))
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨k, hkV, rfl⟩ := hx
    refine Subgroup.mem_map.2 ⟨⟨D.ρ (IsMinFam16.inclK h hH k),
      D.mem_img.2 ⟨IsMinFam16.inclK h hH k, k.2, rfl⟩⟩,
      Subgroup.mem_subgroupOf.2 (D.mem_img.2 ⟨IsMinFam16.inclK h hH k,
        (Subgroup.mem_subgroupOf.1 hkV), rfl⟩), (w16l_kToHatX_apply h hH D k).symm⟩
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨j, hjV, hjρ⟩ := D.mem_img.1 hy
    have hkK : (j : G) ∈ CFSG.Quasithin.conjClosure V H :=
      CFSG.Quasithin.le_conjClosure V H hjV
    refine Subgroup.mem_map.2 ⟨⟨(j : G), hkK⟩, Subgroup.mem_subgroupOf.2 hjV, ?_⟩
    rw [← hyx, w16l_kToHatX_apply]
    have hyeq : (⟨D.ρ (IsMinFam16.inclK h hH ⟨(j : G), hkK⟩),
        D.mem_img.2 ⟨IsMinFam16.inclK h hH ⟨(j : G), hkK⟩,
          by rw [w16l_coe_inclK h hH]; exact hkK, rfl⟩⟩ :
          ↥(hatK D V)) = y := by
      apply Subtype.ext
      change D.ρ (IsMinFam16.inclK h hH ⟨(j : G), hkK⟩) = (y : LGL 2 D.W)
      rw [show IsMinFam16.inclK h hH ⟨(j : G), hkK⟩ = j from Subtype.ext rfl]
      exact hjρ
    rw [hyeq]

section Certified


theorem IsMinFam16.exists_barRep (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X]
    {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ) :
    ∃ ρ : X →* LGL 2 D.W, ∀ k : ↥(CFSG.Quasithin.conjClosure V H),
      ρ (φ k) = D.ρ (IsMinFam16.inclK h hH k) := by
  classical
  have hI : IsElemAbelian 2 (iSub16 V H) := Cex16.isElemAbelian_iSub16 h1 hS h hH.1
  let ρ₀ : ↥(CFSG.Quasithin.conjClosure V H) →* LGL 2 D.W :=
    D.ρ.comp (IsMinFam16.inclK h hH)
  have hle : φ.ker ≤ ρ₀.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    show D.ρ (IsMinFam16.inclK h hH k) = 1
    rw [D.ρ_eq_one_iff (IsMinFam16.inclK h hH k)]
    exact Subgroup.mem_centralizer_iff.2 fun y hy => hI.comm hy ((hφ.ker_iff k).1 hk)
  exact ⟨φ.liftOfSurjective hφ.surjective ⟨ρ₀, hle⟩, fun k =>
    φ.liftOfRightInverse_comp_apply (Function.surjInv hφ.surjective)
      (Function.rightInverse_surjInv hφ.surjective) ⟨ρ₀, hle⟩ k⟩

theorem IsMinFam16.exists_barTheta (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X]
    {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ) :
    ∃ θ : X →* hatX D V,
      (∀ k : ↥(CFSG.Quasithin.conjClosure V H), θ (φ k) = IsMinFam16.kToHatX h hH D k) ∧
      Function.Surjective θ ∧
      (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V).map θ = hatS D V := by
  classical
  have hI : IsElemAbelian 2 (iSub16 V H) := Cex16.isElemAbelian_iSub16 h1 hS h hH.1
  have hle : φ.ker ≤ (IsMinFam16.kToHatX h hH D).ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    have hkI : (k : G) ∈ iSub16 V H := (hφ.ker_iff k).1 hk
    have hρ1 : D.ρ (IsMinFam16.inclK h hH k) = 1 := by
      rw [D.ρ_eq_one_iff (IsMinFam16.inclK h hH k)]
      exact Subgroup.mem_centralizer_iff.2 fun y hy => hI.comm hy hkI
    rw [w16l_kToHatX_apply]
    have hsub : (⟨D.ρ (IsMinFam16.inclK h hH k),
        D.mem_img.2 ⟨IsMinFam16.inclK h hH k, k.2, rfl⟩⟩ : ↥(hatK D V)) = 1 :=
      Subtype.ext hρ1
    rw [hsub, map_one]
  let θ : X →* hatX D V :=
    φ.liftOfSurjective hφ.surjective ⟨IsMinFam16.kToHatX h hH D, hle⟩
  have hθ : ∀ k : ↥(CFSG.Quasithin.conjClosure V H),
      θ (φ k) = IsMinFam16.kToHatX h hH D k := fun k =>
    φ.liftOfRightInverse_comp_apply (Function.surjInv hφ.surjective)
      (Function.rightInverse_surjInv hφ.surjective) ⟨IsMinFam16.kToHatX h hH D, hle⟩ k
  refine ⟨θ, hθ, ?_, ?_⟩
  · intro y
    obtain ⟨k, hk⟩ := w16l_surjective_kToHatX h hH D y
    exact ⟨φ k, by rw [hθ k]; exact hk⟩
  · change ((V.subgroupOf (CFSG.Quasithin.conjClosure V H)).map φ).map θ = hatS D V
    rw [Subgroup.map_map]
    rw [show θ.comp φ = IsMinFam16.kToHatX h hH D from MonoidHom.ext hθ]
    exact w16l_map_kToHatX_V h hH D

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
