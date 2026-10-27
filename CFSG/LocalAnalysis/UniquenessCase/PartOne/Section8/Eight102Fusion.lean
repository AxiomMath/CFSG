module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.FocalSubgroup
import CFSG.RankThree.PartTwo.Sec12.SylowIndependence
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SylowIntersectionNormalizerGrowth
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma isSylowOf_top_of_sylow {r : ℕ} [Fact r.Prime] (P : Sylow r G) :
    IsSylowOf r (P : Subgroup G) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact P.not_dvd_index

private lemma exists_sylow_coe_eq_of_isSylowOf_top {r : ℕ} [Fact r.Prime] {S : Subgroup G}
    (hS : IsSylowOf r S ⊤) : ∃ P : Sylow r G, (P : Subgroup G) = S := by
  obtain ⟨-, hpg, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hpg.toSylow hdvd, IsPGroup.toSylow_coe hpg hdvd⟩

private lemma isPGroup_le_of_mem_uniqueSet {r : ℕ} (hr : r.Prime) {M S X T : Subgroup G}
    (hS : IsSylowOf r S ⊤) (hSM : S ≤ M) (hX : X ∈ uniqueSet M) (hXT : X ≤ T)
    (hT : IsPGroup r T) : T ≤ M := by
  haveI := Fact.mk hr
  obtain ⟨R, hTR⟩ := hT.exists_le_sylow
  obtain ⟨k, -, hk⟩ :=
    CFSG.RankThree.PartTwo.Sec12.isSylowOf_exists_conj hS (isSylowOf_top_of_sylow R)
  have hXSk : X ≤ S.map (MulAut.conj k).toMonoidHom := hXT.trans (hTR.trans (le_of_eq hk))
  have hMk : M.map (MulAut.conj k).toMonoidHom = M :=
    hX.2 k (hXSk.trans (Subgroup.map_mono hSM))
  calc T ≤ R := hTR
    _ = S.map (MulAut.conj k).toMonoidHom := hk
    _ ≤ M.map (MulAut.conj k).toMonoidHom := Subgroup.map_mono hSM
    _ = M := hMk

private lemma mem_of_map_conj_le_of_mem_uniqueSet {M X : Subgroup G} {m : G}
    (hM : rankThreeIsMaxTwoLocal M) (hX : X ∈ uniqueSet M)
    (h : X.map (MulAut.conj m).toMonoidHom ≤ M) : m ∈ M := by
  have hMinv : M.map (MulAut.conj m⁻¹).toMonoidHom = M := by
    refine hX.2 m⁻¹ ?_
    intro z hz
    exact Subgroup.mem_map.mpr ⟨MulAut.conj m z, h (Subgroup.mem_map_of_mem _ hz), by
      simp [MulAut.conj_apply, mul_assoc]⟩
  have hMm : M.map (MulAut.conj m).toMonoidHom = M := by
    have h1 : (M.map (MulAut.conj m⁻¹).toMonoidHom).map (MulAut.conj m).toMonoidHom = M := by
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom =
          MonoidHom.id G := by
        ext z
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp, Subgroup.map_id]
    rwa [hMinv] at h1
  have hnorm : m ∈ normalizer (M : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMm
  rwa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M hM] at hnorm

private lemma le_centralizer_conj_of_le_centralizer {S X : Subgroup G} {x g : G} (hx : x ∈ S)
    (hgx : g * x * g⁻¹ ∈ S) (hXleC : X ≤ centralizer (S : Set G)) :
    X ≤ centralizer ({g * x * g⁻¹} : Set G) ∧
      X.map (MulAut.conj g).toMonoidHom ≤ centralizer ({g * x * g⁻¹} : Set G) := by
  constructor
  · intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact Subgroup.mem_centralizer_iff.mp (hXleC hz) _ hgx
  · rintro z ⟨z', hz', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    have hcomm : z' * x = x * z' := (Subgroup.mem_centralizer_iff.mp (hXleC hz') x hx).symm
    have hc : (g * x * g⁻¹) * (g * z' * g⁻¹) = (g * z' * g⁻¹) * (g * x * g⁻¹) := by
      calc (g * x * g⁻¹) * (g * z' * g⁻¹) = g * (x * z') * g⁻¹ := by group
        _ = g * (z' * x) * g⁻¹ := by rw [hcomm]
        _ = (g * z' * g⁻¹) * (g * x * g⁻¹) := by group
    simpa [MulAut.conj_apply] using hc

private lemma exists_mem_centralizer_map_conj_le {r : ℕ} (hr : r.Prime) {M S X : Subgroup G}
    (hS : IsSylowOf r S ⊤) (hSM : S ≤ M) (hX : X ∈ uniqueSet M) {x g : G}
    (hXpg : IsPGroup r X) (hXcent : X ≤ centralizer ({g * x * g⁻¹} : Set G))
    (hXgcent : X.map (MulAut.conj g).toMonoidHom ≤ centralizer ({g * x * g⁻¹} : Set G)) :
    ∃ c ∈ centralizer ({g * x * g⁻¹} : Set G),
      X.map (MulAut.conj (c⁻¹ * g)).toMonoidHom ≤ M := by
  haveI := Fact.mk hr
  set C : Subgroup G := centralizer ({g * x * g⁻¹} : Set G) with hC
  obtain ⟨Q₁, hXQ₁⟩ := (hXpg.comap_subtype (K := C)).exists_le_sylow
  let R₁ : Subgroup G := (Q₁ : Subgroup ↥C).map C.subtype
  have hR₁ : IsSylowOf r R₁ C := ⟨Q₁, rfl⟩
  have hXR₁ : X ≤ R₁ := by
    intro z hz
    have hz' : (⟨z, hXcent hz⟩ : ↥C) ∈ Subgroup.comap C.subtype X := by
      rw [Subgroup.mem_comap]
      exact hz
    exact Subgroup.mem_map.mpr ⟨⟨z, hXcent hz⟩, hXQ₁ hz', rfl⟩
  obtain ⟨Q₂, hXgQ₂⟩ :=
    ((hXpg.map (MulAut.conj g).toMonoidHom).comap_subtype (K := C)).exists_le_sylow
  let R₂ : Subgroup G := (Q₂ : Subgroup ↥C).map C.subtype
  have hR₂ : IsSylowOf r R₂ C := ⟨Q₂, rfl⟩
  have hXgR₂ : X.map (MulAut.conj g).toMonoidHom ≤ R₂ := by
    intro z hz
    have hz' : (⟨z, hXgcent hz⟩ : ↥C) ∈
        Subgroup.comap C.subtype (X.map (MulAut.conj g).toMonoidHom) := by
      rw [Subgroup.mem_comap]
      exact hz
    exact Subgroup.mem_map.mpr ⟨⟨z, hXgcent hz⟩, hXgQ₂ hz', rfl⟩
  obtain ⟨c, hcC, hc⟩ := CFSG.RankThree.PartTwo.Sec12.isSylowOf_exists_conj hR₁ hR₂
  have hcR : R₂.map (MulAut.conj c⁻¹).toMonoidHom = R₁ := by
    rw [hc, Subgroup.map_map]
    have hcomp : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  have hmcomp : (MulAut.conj (c⁻¹ * g)).toMonoidHom =
      (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨c, hcC, ?_⟩
  rw [hmcomp, ← Subgroup.map_map]
  exact ((Subgroup.map_mono hXgR₂).trans (le_of_eq hcR)).trans
    (isPGroup_le_of_mem_uniqueSet hr hS hSM hX hXR₁ hR₁.isPGroup)

theorem isSylowOf_top_of_mem_uniqueSet {M S X : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowOf r S M) (hX : X ∈ uniqueSet M)
    (hXS : X ≤ S) : IsSylowOf r S ⊤ := by
  haveI := Fact.mk hr
  have hSX : S ∈ uniqueSet M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hX hXS hS.le
  have hN : normalizer (S : Set G) ≤ M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet hM hSX
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hS.isPGroup, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro hdvd
  obtain ⟨P, hSP⟩ := hS.isPGroup.exists_le_sylow
  have hPnotS : ¬ (P : Subgroup G) ≤ S := by
    intro hle
    have heq : (P : Subgroup G) = S := le_antisymm hle hSP
    have hnot := Sylow.not_dvd_index P
    rw [heq] at hnot
    exact hnot hdvd
  have hnotle : ¬ ((P : Subgroup G) ⊓ M ≤ S) := by
    refine CFSG.GorensteinWalter.sylow_intersection_not_le_of_inner_normalizer_le P S M hPnotS ?_
    rw [inf_eq_right.mpr hSP]
    exact inf_le_right.trans hN
  obtain ⟨z, hzPM, hzS⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hQle : S ⊔ ((P : Subgroup G) ⊓ M) ≤ M := sup_le hS.le inf_le_right
  have hQpg : IsPGroup r ↥(S ⊔ ((P : Subgroup G) ⊓ M)) :=
    (Sylow.isPGroup' P).to_le (sup_le hSP inf_le_left)
  have hQeq : S ⊔ ((P : Subgroup G) ⊓ M) = S :=
    IsSylowOf.eq_of_le hS le_sup_left hQle hQpg
  have hzQ : z ∈ S ⊔ ((P : Subgroup G) ⊓ M) := Subgroup.mem_sup_right hzPM
  rw [hQeq] at hzQ
  exact hzS hzQ

theorem exists_conj_eq_of_mem_uniqueSet {M S X : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowOf r S ⊤) (hSM : S ≤ M)
    (hX : X ∈ uniqueSet M) (hXS : X ≤ S ⊓ centralizer (S : Set G)) {x g : G} (hx : x ∈ S)
    (hgx : g * x * g⁻¹ ∈ S) : ∃ m ∈ M, g * x * g⁻¹ = m * x * m⁻¹ := by
  haveI := Fact.mk hr
  have hXleS : X ≤ S := hXS.trans inf_le_left
  have hXleC : X ≤ centralizer (S : Set G) := hXS.trans inf_le_right
  have hXpg : IsPGroup r X := hS.isPGroup.to_le hXleS
  obtain ⟨hXcent, hXgcent⟩ := le_centralizer_conj_of_le_centralizer hx hgx hXleC
  obtain ⟨c, hcC, hcM⟩ :=
    exists_mem_centralizer_map_conj_le hr hS hSM hX hXpg hXcent hXgcent
  have hmM : c⁻¹ * g ∈ M := mem_of_map_conj_le_of_mem_uniqueSet hM hX hcM
  refine ⟨c⁻¹ * g, hmM, ?_⟩
  have hcomm : (g * x * g⁻¹) * c = c * (g * x * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hcC _ (Set.mem_singleton _)
  have hcy : c⁻¹ * (g * x * g⁻¹) * c = g * x * g⁻¹ := by
    calc c⁻¹ * (g * x * g⁻¹) * c = c⁻¹ * ((g * x * g⁻¹) * c) := mul_assoc _ _ _
      _ = c⁻¹ * (c * (g * x * g⁻¹)) := by rw [hcomm]
      _ = (c⁻¹ * c) * (g * x * g⁻¹) := (mul_assoc _ _ _).symm
      _ = g * x * g⁻¹ := by rw [inv_mul_cancel, one_mul]
  calc g * x * g⁻¹ = c⁻¹ * (g * x * g⁻¹) * c := hcy.symm
    _ = (c⁻¹ * g) * x * (c⁻¹ * g)⁻¹ := by group

theorem le_commutator_of_control {M S : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hG : commutator G = ⊤) (hS : IsSylowOf r S ⊤) (hSM : S ≤ M)
    (hctl : ∀ x ∈ S, ∀ g : G, g * x * g⁻¹ ∈ S → ∃ m ∈ M, g * x * g⁻¹ = m * x * m⁻¹) :
    S ≤ ⁅M, M⁆ := by
  haveI := Fact.mk hr
  obtain ⟨P, hP⟩ := exists_sylow_coe_eq_of_isSylowOf_top hS
  have hfocal := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup (G := G) r P
  have hder : CFSG.derivedSubgroup G = ⊤ := by
    rw [show CFSG.derivedSubgroup G = derivedSeries G 1 from rfl, derivedSeries_one, hG]
  have hSder : S ⊓ CFSG.derivedSubgroup G = S := by rw [hder, inf_top_eq]
  rw [hP, hSder] at hfocal
  rw [hfocal, Subgroup.closure_le]
  rintro z ⟨x, hxS, y, hyS, hxy, rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  obtain ⟨m, hmM, hm⟩ := hctl x hxS g (by rw [hg]; exact hyS)
  have hmem : x⁻¹ * m * x * m⁻¹ ∈ ⁅M, M⁆ := by
    have hc := Subgroup.commutator_mem_commutator (H₁ := M) (H₂ := M)
      (M.inv_mem (hSM hxS)) hmM
    rwa [commutatorElement_def, inv_inv] at hc
  rw [← hg, hm]
  simpa [mul_assoc] using hmem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
