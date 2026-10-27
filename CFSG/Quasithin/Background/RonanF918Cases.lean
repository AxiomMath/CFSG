module

public import CFSG.Quasithin.Background.RonanF918Nat

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section Cases

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

@[expose] def HatDSumU (V₁ Vp H K T J I' : Subgroup G) (t : G) : Prop :=
  hat' V₁ Vp H K T J = hat' V₁ Vp H K T I' ⊔ hat' V₁ Vp H K T (conjSub t⁻¹ I') ∧
    hat' V₁ Vp H K T I' ⊓ hat' V₁ Vp H K T (conjSub t⁻¹ I') = ⊥

theorem subM_self (V₁ IH : Subgroup G) : subM V₁ IH IH = ⊤ := Subgroup.subgroupOf_self _

theorem conjSub_inv_le_conjClosure {t : G} (htH : t ∈ H) (I : Subgroup G) :
    conjSub t⁻¹ I ≤ conjClosure I H := by
  intro y hy
  have h1 := mem_conjSub.mp hy
  have h2 := mem_conjClosure (H.inv_mem htH) h1
  have e : t⁻¹ * (t⁻¹⁻¹ * y * t⁻¹) * t⁻¹⁻¹ = y := by group
  rwa [e] at h2

theorem V₁_le_conjSub_inv (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I) {t : G} (htH : t ∈ H) :
    V₁ ≤ conjSub t⁻¹ I := by
  intro v hv
  rw [mem_conjSub, inv_inv]
  exact hV₁I ((Subgroup.mem_normalizer_iff.mp (h.H_le_normalizer_V₁ htH) v).mp hv)

theorem K₀_le_normalizer_conjSub_inv (h : HypF918 T V L V₁ Vp H K)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G)) {t : G} (htH : t ∈ H) :
    conjClosure K T ≤ Subgroup.normalizer (conjSub t⁻¹ I : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hk' : t * k * t⁻¹ ∈ conjClosure K T :=
    (Subgroup.mem_normalizer_iff.mp (h.K₀_normal htH) k).mp hk
  have hN := Subgroup.mem_normalizer_iff.mp (hKI hk') (t * y * t⁻¹)
  rw [mem_conjSub, mem_conjSub, inv_inv]
  have e : t * (k * y * k⁻¹) * t⁻¹ = (t * k * t⁻¹) * (t * y * t⁻¹) * (t * k * t⁻¹)⁻¹ := by group
  rw [e]
  exact hN

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem autIH_le_stabSub_subM (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {J : Subgroup G} (hV₁J : V₁ ≤ J) (hJI : J ≤ conjClosure I H)
    (hKJ : conjClosure K T ≤ Subgroup.normalizer (J : Set G)) :
    autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) J) := by
  intro l hl
  have hl' : l ∈ ((conjClosure K T).subgroupOf H).map
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [← autIH_eq_map h h.K₀_le_H]
    exact hl
  obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hl'
  exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ (h.conjClosure_le_normalizer_V₁ hIU)
    (le_normalizer_conjClosure I H) hV₁J hJI ⟨k, hkH⟩).mpr
    (hKJ (Subgroup.mem_subgroupOf.mp hk))

theorem hatDSumU_of_isSumMod (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {t : G}
    (htH : t ∈ H)
    (hsum : IsSumMod (fixV (autIH V₁ I H (conjClosure K T))) (subM V₁ (conjClosure I H) I)
      (subM V₁ (conjClosure I H) (conjSub t⁻¹ I)) ⊤) :
    HatDSumU V₁ Vp H K T (conjClosure I H) I t := by
  have hQ := conjSub_inv_le_conjClosure htH I
  have key := map_sup_inf_of_isSumMod (thetaMap h hIU)
    (C := fixV (autIH V₁ I H (conjClosure K T)))
    (fun w => ⟨mem_fixV_of_thetaMap_eq_one h hIU, thetaMap_eq_one_of_mem_fixV h hIU⟩)
    hsum.1 hsum.2
  refine ⟨?_, ?_⟩
  · rw [hat_eq_map_theta h hIU le_rfl, hat_eq_map_theta h hIU (le_conjClosure I H),
      hat_eq_map_theta h hIU hQ, subM_self]
    exact key.1
  · rw [hat_eq_map_theta h hIU (le_conjClosure I H), hat_eq_map_theta h hIU hQ]
    exact key.2

theorem not_modIso_of_not_secIsoL (h : HypF918 T V L V₁ Vp H K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G)) {t : G}
    (htH : t ∈ H)
    (hSec : ¬ SecIsoL (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
      (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T)))
      (subM V₁ (conjClosure I H) (conjSub t⁻¹ I))
      (subM V₁ (conjClosure I H) (conjSub t⁻¹ I) ⊓ fixV (autIH V₁ I H (conjClosure K T)))) :
    ¬ ModIso (hat' V₁ Vp H K T (conjClosure K T)) (hat' V₁ Vp H K T I)
      (hat' V₁ Vp H K T (conjSub t⁻¹ I)) := by
  rintro ⟨-, -, φ0, hφ0⟩
  apply hSec
  have hQ := conjSub_inv_le_conjClosure htH I
  have hP : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I) :=
    autIH_le_stabSub_subM h hIU hV₁I (le_conjClosure I H) hKI
  have hQs : autIH V₁ I H (conjClosure K T) ≤
      stabSub (subM V₁ (conjClosure I H) (conjSub t⁻¹ I)) :=
    autIH_le_stabSub_subM h hIU (V₁_le_conjSub_inv h hV₁I htH) hQ
      (K₀_le_normalizer_conjSub_inv h hKI htH)
  have e1 : (subM V₁ (conjClosure I H) I).map (thetaMap h hIU) = hat' V₁ Vp H K T I :=
    (hat_eq_map_theta h hIU (le_conjClosure I H)).symm
  have e2 : (subM V₁ (conjClosure I H) (conjSub t⁻¹ I)).map (thetaMap h hIU) =
      hat' V₁ Vp H K T (conjSub t⁻¹ I) :=
    (hat_eq_map_theta h hIU hQ).symm
  let φ : ↥((subM V₁ (conjClosure I H) I).map (thetaMap h hIU)) ≃*
      ↥((subM V₁ (conjClosure I H) (conjSub t⁻¹ I)).map (thetaMap h hIU)) :=
    (MulEquiv.subgroupCongr e1).trans (φ0.trans (MulEquiv.subgroupCongr e2.symm))
  refine secIsoL_of_equivariant_iso (thetaMap h hIU) hP hQs
    (fun w => ⟨mem_fixV_of_thetaMap_eq_one h hIU, thetaMap_eq_one_of_mem_fixV h hIU⟩) φ ?_
  intro l hl
  have hl' : l ∈ ((conjClosure K T).subgroupOf H).map
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [← autIH_eq_map h h.K₀_le_H]
    exact hl
  obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hl'
  have hkK : k ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hk
  refine ⟨kbarOf h hkH, fun w => thetaMap_actH h hIU hkH w, ?_⟩
  intro x x' hxx'
  have h1 := hφ0 (kbarOf h hkH) (kbarOf_mem_hat h hkK) (MulEquiv.subgroupCongr e1 x)
    (MulEquiv.subgroupCongr e1 x') (by simpa using hxx')
  simpa [φ] using h1

end Cases

end CFSG.Quasithin.RonanF918
