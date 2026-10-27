module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYOrbit
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYCore
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYDescent
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Transport
public import Mathlib.FieldTheory.Perfect
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Classes
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Classes
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8TwoLift
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVRoots
public import TauCeti.RepresentationTheory.Unipotent.PowerOrder

public section

namespace CFSG.StandardType.RCKC1

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.E6Pilot (rootProd)
open CFSG.SeitzReduction.E7Pilot
open CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.C14ExcBridgeU CFSG.Open
open CFSG.ComponentClassification.RankTwoExceptional.E7Sec8 (linConjSubgroup)

theorem e7K2_baseChangeGL_rootProd
    {R S : Type} [Field R] [Field S] (f : R →+* S)
    (l : List (Fin Tag.E7.rank → ℤ)) (c : (Fin Tag.E7.rank → ℤ) → R) :
    baseChangeGL f (rootProd .E7 R l c) =
      rootProd .E7 S l (fun β => f (c β)) := by
  rw [rootProd, rootProd, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun β _ => baseChangeGL_pinnedX f β (c β)

theorem e7K2_fixed_iff_exists_baseChange
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    [Algebra (ZMod 2) L] {k : ModGL .E7 L} (hk : k ∈ adjointGroup .E7 L) :
    entrywiseFrobGL .E7 L 2 1 k = k ↔
      ∃ k₀ ∈ adjointGroup .E7 (ZMod 2),
        (baseChangeGL (algebraMap (ZMod 2) L) k₀ : ModGL .E7 L) = k := by
  haveI : PerfectRing L 2 := inferInstance
  have hFr : ∀ c : L, iterateFrobenius L 2 1 c = c ^ Nat.card (ZMod 2) := by
    intro c
    rw [iterateFrobenius_def, Nat.card_zmod]
    norm_num
  have hbij : Function.Bijective (iterateFrobenius L 2 1) :=
    bijective_iterateFrobenius L 2 1
  have hfixed := fixed_eq_map (K := ZMod 2) (L := L) (τ := .E7)
    (Or.inr (Or.inr (Or.inl rfl))) (Fr := iterateFrobenius L 2 1) hFr hbij
  constructor
  · intro hfix
    have hmem : k ∈ adjointGroup .E7 L ⊓
        (Units.map (entrywiseHom (iterateFrobenius L 2 1))).eqLocus (MonoidHom.id _) :=
      ⟨hk, hfix⟩
    rw [hfixed] at hmem
    obtain ⟨k₀, hk₀, hval⟩ := hmem
    exact ⟨k₀, hk₀, hval⟩
  · rintro ⟨k₀, hk₀, rfl⟩
    have hmem : baseChangeGL (algebraMap (ZMod 2) L) k₀ ∈
        adjointGroup .E7 L ⊓
          (Units.map (entrywiseHom (iterateFrobenius L 2 1))).eqLocus (MonoidHom.id _) := by
      rw [hfixed]
      exact Subgroup.mem_map_of_mem _ hk₀
    exact hmem.2

open scoped Classical in
noncomputable def e7K2_coeffDesc {L : Type} [Zero L] [One L]
    (c : (Fin Tag.E7.rank → ℤ) → L) : (Fin Tag.E7.rank → ℤ) → ZMod 2 :=
  fun β => if c β = 0 then 0 else 1

theorem e7K2_algebraMap_coeffDesc {L : Type} [Field L] [Algebra (ZMod 2) L]
    {l : List (Fin Tag.E7.rank → ℤ)} {c : (Fin Tag.E7.rank → ℤ) → L}
    (hc : ∀ β ∈ l, c β ^ 2 = c β) {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ l) :
    algebraMap (ZMod 2) L (e7K2_coeffDesc c β) = c β := by
  rcases eq_zero_or_one_of_sq_eq_self (hc β hβ) with h | h <;>
    simp [e7K2_coeffDesc, h]

theorem e7K2_exists_rootProd_descend
    {L : Type} [Field L] [Algebra (ZMod 2) L]
    (l : List (Fin Tag.E7.rank → ℤ)) {c : (Fin Tag.E7.rank → ℤ) → L}
    (hc : ∀ β ∈ l, c β ^ 2 = c β) :
    ∃ c₀ : (Fin Tag.E7.rank → ℤ) → ZMod 2,
      (∀ β ∈ l, algebraMap (ZMod 2) L (c₀ β) = c β) ∧
        baseChangeGL (algebraMap (ZMod 2) L) (rootProd .E7 (ZMod 2) l c₀) =
          rootProd .E7 L l c := by
  refine ⟨e7K2_coeffDesc c, fun β hβ => e7K2_algebraMap_coeffDesc hc hβ, ?_⟩
  rw [e7K2_baseChangeGL_rootProd]
  simp only [rootProd]
  congr 1
  exact List.map_congr_left fun β hβ => by rw [e7K2_algebraMap_coeffDesc hc hβ]

theorem k2At_of_baseChange_conj_yAS
    {X : Type} [Group X] {K V : Subgroup X} {r : X}
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra (ZMod 2) L]
    (hrK : r ∈ K) (hVK : V ≤ K) (hrV : r ∈ V) (e : ↥K ≃* ↥(adjointGroup .E7 (ZMod 2)))
    {x : ModGL .E7 L} (hx : x ∈ adjointGroup .E7 L)
    (hxr : x * yAS L * x⁻¹ =
      baseChangeGL (algebraMap (ZMod 2) L) (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)))
    (hxV : ∀ v (hv : v ∈ V), ∃ c : (Fin Tag.E7.rank → ℤ) → L,
      x⁻¹ * baseChangeGL (algebraMap (ZMod 2) L) (e ⟨v, hVK hv⟩ : ModGL .E7 (ZMod 2)) * x =
        rootProd .E7 L yPsi c) :
    K2At K V r := by
  classical
  haveI : PerfectRing L 2 := inferInstance
  set bc : ModGL .E7 (ZMod 2) →* ModGL .E7 L :=
    baseChangeGL (algebraMap (ZMod 2) L) with hbc_def
  have hFix_bc : ∀ g : adjointGroup .E7 (ZMod 2),
      entrywiseFrobGL .E7 L 2 1 (bc (g : ModGL .E7 (ZMod 2))) =
        bc (g : ModGL .E7 (ZMod 2)) := by
    intro g
    exact (e7K2_fixed_iff_exists_baseChange (k := bc (g : ModGL .E7 (ZMod 2)))
      (baseChangeGL_mem_adjointGroup _ g.2)).2 ⟨g, g.2, rfl⟩
  have hxr' : x * yAS L * x⁻¹ = bc (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) := by
    simpa only [hbc_def] using hxr
  have hFix : entrywiseFrobGL .E7 L 2 1 (x * yAS L * x⁻¹) = x * yAS L * x⁻¹ := by
    rw [hxr']
    exact hFix_bc (e ⟨r, hrK⟩)
  let W : Set (ModGL .E7 L) :=
    {w | ∃ u : ↥K, (u : X) ∈ V ∧ w = bc (e u : ModGL .E7 (ZMod 2))}
  have hWF : ∀ w ∈ W, entrywiseFrobGL .E7 L 2 1 w = w := by
    rintro w ⟨u, -, rfl⟩
    exact hFix_bc (e u)
  have hWR : ∀ w ∈ W, ∃ c : (Fin Tag.E7.rank → ℤ) → L,
      x⁻¹ * w * x = rootProd .E7 L yPsi c := by
    rintro w ⟨u, huV, rfl⟩
    obtain ⟨c, hc⟩ := hxV (u : X) huV
    exact ⟨c, by simpa only [hbc_def] using hc⟩
  obtain ⟨k, hkC, hkFix, ⟨z, hzP, hzk⟩, hWk⟩ :=
    exists_frobFixed_conj_into_yPsi (L := L) hx hFix hWF hWR
  obtain ⟨k₀, hk₀C, hk₀eq⟩ :=
    (e7K2_fixed_iff_exists_baseChange (k := k) hkC).1 hkFix
  have hw_r : bc (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) ∈ W :=
    ⟨⟨r, hrK⟩, hrV, rfl⟩
  obtain ⟨c_r, hc_r2, hkW_r⟩ := hWk _ hw_r
  have hzY : z * yAS L * z⁻¹ = rootProd .E7 L yPsi c_r := by
    rw [← hzk, hxr', hkW_r]
  have hQc_r : yQc c_r = 1 := yQc_eq_one_of_conj_yAS hzP hzY hc_r2
  obtain ⟨c₀, hc₀map, hbc₀⟩ := e7K2_exists_rootProd_descend (l := yPsi) hc_r2
  have hQc₀ : yQc c₀ = 1 := by
    have h1 : yQc (fun β => algebraMap (ZMod 2) L (c₀ β)) = yQc c_r :=
      yQc_congr hc₀map
    have h2 : yQc (fun β => algebraMap (ZMod 2) L (c₀ β)) =
        algebraMap (ZMod 2) L (yQc c₀) := yQc_map _ c₀
    have h3 : algebraMap (ZMod 2) L (yQc c₀) = 1 := by
      rw [← h2, h1, hQc_r]
    exact (RingHom.injective (algebraMap (ZMod 2) L)) (by
      rw [h3]
      simp)
  have hbc_r : bc ((k₀ : ModGL .E7 (ZMod 2)) * (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) *
      (k₀ : ModGL .E7 (ZMod 2))⁻¹) = rootProd .E7 L yPsi c_r := by
    rw [map_mul, map_mul, map_inv, hk₀eq, hkW_r]
  have hk₀r : (k₀ : ModGL .E7 (ZMod 2)) * (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) *
      (k₀ : ModGL .E7 (ZMod 2))⁻¹ = rootProd .E7 (ZMod 2) yPsi c₀ := by
    have hbc₀' : bc (rootProd .E7 (ZMod 2) yPsi c₀) = rootProd .E7 L yPsi c_r := by
      simpa only [hbc_def] using hbc₀
    refine baseChangeGL_injective (τ := .E7) (f := algebraMap (ZMod 2) L) ?_
    change bc ((k₀ : ModGL .E7 (ZMod 2)) * (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) *
        (k₀ : ModGL .E7 (ZMod 2))⁻¹) = bc (rootProd .E7 (ZMod 2) yPsi c₀)
    rw [hbc_r, hbc₀']
  obtain ⟨m, hmC, hmLin, hmConj⟩ := exists_conj_yAS_of_yQc_eq_one hQc₀
  let gA : adjointGroup .E7 (ZMod 2) :=
    ⟨m * (k₀ : ModGL .E7 (ZMod 2)), mul_mem hmC hk₀C⟩
  let e' : ↥K ≃* ↥(adjointGroup .E7 (ZMod 2)) := e.trans (MulAut.conj gA)
  have hgA : (gA : ModGL .E7 (ZMod 2)) = m * (k₀ : ModGL .E7 (ZMod 2)) := rfl
  have he'r : e' ⟨r, hrK⟩ = e7ASRep (ZMod 2) 1 := by
    apply Subtype.ext
    rw [coe_e7ASRep_one]
    change (gA : ModGL .E7 (ZMod 2)) * (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) *
        (gA : ModGL .E7 (ZMod 2))⁻¹ = yAS (ZMod 2)
    rw [hgA]
    calc m * (k₀ : ModGL .E7 (ZMod 2)) * (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) *
          (m * (k₀ : ModGL .E7 (ZMod 2)))⁻¹
        = m * ((k₀ : ModGL .E7 (ZMod 2)) * (e ⟨r, hrK⟩ : ModGL .E7 (ZMod 2)) *
            (k₀ : ModGL .E7 (ZMod 2))⁻¹) * m⁻¹ := by group
      _ = m * rootProd .E7 (ZMod 2) yPsi c₀ * m⁻¹ := by rw [hk₀r]
      _ = yAS (ZMod 2) := hmConj
  let V' : Subgroup (adjointGroup .E7 (ZMod 2)) := (V.subgroupOf K).map e'.toMonoidHom
  have hyV' : e7ASRep (ZMod 2) 1 ∈ V' := by
    rw [← he'r]
    exact Subgroup.mem_map_of_mem e'.toMonoidHom (Subgroup.mem_subgroupOf.2 hrV)
  have hdescend : ∀ u : ↥K, (u : X) ∈ V →
      ∃ c : (Fin Tag.E7.rank → ℤ) → ZMod 2,
        (k₀ : ModGL .E7 (ZMod 2)) * (e u : ModGL .E7 (ZMod 2)) *
            (k₀ : ModGL .E7 (ZMod 2))⁻¹ = rootProd .E7 (ZMod 2) yPsi c := by
    intro u huV
    obtain ⟨cv, hcv2, hkv⟩ := hWk _ ⟨u, huV, rfl⟩
    obtain ⟨c0u, -, hbc0u⟩ := e7K2_exists_rootProd_descend (l := yPsi) hcv2
    refine ⟨c0u, ?_⟩
    refine baseChangeGL_injective (τ := .E7) (f := algebraMap (ZMod 2) L) ?_
    have h1 : bc ((k₀ : ModGL .E7 (ZMod 2)) * (e u : ModGL .E7 (ZMod 2)) *
        (k₀ : ModGL .E7 (ZMod 2))⁻¹) = rootProd .E7 L yPsi cv := by
      rw [map_mul, map_mul, map_inv, hk₀eq, hkv]
    have h2 : bc (rootProd .E7 (ZMod 2) yPsi c0u) = rootProd .E7 L yPsi cv := by
      simpa only [hbc_def] using hbc0u
    change bc ((k₀ : ModGL .E7 (ZMod 2)) * (e u : ModGL .E7 (ZMod 2)) *
        (k₀ : ModGL .E7 (ZMod 2))⁻¹) = bc (rootProd .E7 (ZMod 2) yPsi c0u)
    rw [h1, h2]
  have hV' : ∀ v ∈ V', ∃ c : (Fin Tag.E7.rank → ℤ) → ZMod 2,
      (v : ModGL .E7 (ZMod 2)) = rootProd .E7 (ZMod 2) yPsi c := by
    intro v hv
    obtain ⟨u, huV, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨c0u, hk0u⟩ := hdescend u huV
    obtain ⟨c'', hc'', -⟩ := hmLin.1 c0u
    refine ⟨c'', ?_⟩
    calc (e' u : ModGL .E7 (ZMod 2))
        = (gA : ModGL .E7 (ZMod 2)) * (e u : ModGL .E7 (ZMod 2)) *
            (gA : ModGL .E7 (ZMod 2))⁻¹ := rfl
      _ = m * ((k₀ : ModGL .E7 (ZMod 2)) * (e u : ModGL .E7 (ZMod 2)) *
            (k₀ : ModGL .E7 (ZMod 2))⁻¹) * m⁻¹ := by
          rw [hgA]
          group
      _ = m * rootProd .E7 (ZMod 2) yPsi c0u * m⁻¹ := by rw [hk0u]
      _ = rootProd .E7 (ZMod 2) yPsi c'' := hc''
  have hK2model : pCoreOf 2
      (centralizer ({e' ⟨r, hrK⟩} : Set (adjointGroup .E7 (ZMod 2)))) ≤
      Subgroup.normalizer (V' : Set (adjointGroup .E7 (ZMod 2))) := by
    rw [he'r]
    exact pCoreOf_centralizer_e7ASRep_one_le_normalizer hyV' hV'
  exact k2At_of_mulEquiv e' hrK hVK hK2model

end CFSG.StandardType.RCKC1
