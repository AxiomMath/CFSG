module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

open Subgroup

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem s16h_card_inf_comap {G Q : Type*} [Group G] [Group Q] (φ : G →* Q)
    {K : Subgroup G} {B : Subgroup Q} (hB : B ≤ K.map φ) :
    Nat.card ↥(K ⊓ B.comap φ) = Nat.card B * Nat.card ↥(K ⊓ φ.ker) := by
  classical
  let H : Subgroup G := K ⊓ B.comap φ
  let f : ↥H →* ↥B := (φ.comp H.subtype).codRestrict B (fun x => x.2.2)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨k, hkK, hkφ⟩ := Subgroup.mem_map.mp (hB b.2)
    refine ⟨⟨k, ⟨hkK, ?_⟩⟩, Subtype.ext hkφ⟩
    show φ k ∈ B
    rw [hkφ]
    exact b.2
  have hcard := Subgroup.card_ker_mul_card_of_surjective (f := f) hf
  have hker_le : φ.ker ≤ B.comap φ := by
    intro x hx
    change φ x ∈ B
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact B.one_mem
  have hfker : f.ker = (φ.comp H.subtype).ker :=
    MonoidHom.ker_codRestrict (φ.comp H.subtype) B (fun x => x.2.2)
  have hker : f.ker = (K ⊓ φ.ker).subgroupOf H := by
    rw [hfker, ← MonoidHom.comap_ker, Subgroup.comap_subtype]
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨x.2.1, hx⟩, fun hx => hx.2⟩
  have hcardker : Nat.card ↥f.ker = Nat.card ↥(K ⊓ φ.ker) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_inf inf_le_left (inf_le_right.trans hker_le))).toEquiv
  calc Nat.card ↥(K ⊓ B.comap φ) = Nat.card ↥H := rfl
    _ = Nat.card ↥f.ker * Nat.card ↥B := hcard.symm
    _ = Nat.card ↥(K ⊓ φ.ker) * Nat.card ↥B := by rw [hcardker]
    _ = Nat.card B * Nat.card ↥(K ⊓ φ.ker) := by ring

theorem s16h_isSylowOf_inf_comap_of_map_eq {G Q : Type*} [Group G] [Finite G] [Group Q]
    [Finite Q] {p : ℕ} [Fact p.Prime] (φ : G →* Q) {K T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T K) {B : Subgroup Q} (hB : B ≤ T.map φ) :
    CFSG.ABGLocalTools.IsSylowOf p (T ⊓ B.comap φ) (K ⊓ B.comap φ) := by
  classical
  have hTK : T ≤ K := hT.le
  have hB' : B ≤ K.map φ := hB.trans (Subgroup.map_mono hTK)
  have hcardR : Nat.card ↥(T ⊓ B.comap φ) = Nat.card B * Nat.card ↥(T ⊓ φ.ker) :=
    s16h_card_inf_comap φ hB
  have hcardH : Nat.card ↥(K ⊓ B.comap φ) = Nat.card B * Nat.card ↥(K ⊓ φ.ker) :=
    s16h_card_inf_comap φ hB'
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  have hRleH : T ⊓ B.comap φ ≤ K ⊓ B.comap φ := inf_le_inf hTK le_rfl
  refine ⟨hRleH, hT.isPGroup.to_le inf_le_left, ?_⟩
  have hmul : (T ⊓ B.comap φ).relIndex (K ⊓ B.comap φ) *
      Nat.card ↥(T ⊓ B.comap φ) = Nat.card ↥(K ⊓ B.comap φ) := by
    have h := Subgroup.relIndex_mul_card (H := T ⊓ B.comap φ) (K := K ⊓ B.comap φ)
    rwa [inf_eq_left.mpr hRleH] at h
  have hkey : (T ⊓ B.comap φ).relIndex (K ⊓ B.comap φ) *
      Nat.card ↥(T ⊓ φ.ker) = Nat.card ↥(K ⊓ φ.ker) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥B))
    calc Nat.card B * ((T ⊓ B.comap φ).relIndex (K ⊓ B.comap φ) *
            Nat.card ↥(T ⊓ φ.ker))
        = (T ⊓ B.comap φ).relIndex (K ⊓ B.comap φ) *
            (Nat.card B * Nat.card ↥(T ⊓ φ.ker)) := by ring
      _ = (T ⊓ B.comap φ).relIndex (K ⊓ B.comap φ) *
            Nat.card ↥(T ⊓ B.comap φ) := by rw [← hcardR]
      _ = Nat.card ↥(K ⊓ B.comap φ) := hmul
      _ = Nat.card B * Nat.card ↥(K ⊓ φ.ker) := hcardH
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p (T ⊓ φ.ker) (K ⊓ φ.ker) := by
    have hKN : K ≤ Subgroup.normalizer ((K ⊓ φ.ker : Subgroup G) : Set G) := by
      have hnormal : (φ.ker.subgroupOf K).Normal := inferInstance
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf] at hnormal
      rwa [inf_comm] at hnormal
    have h := hT.inf_of_le_normalizer (N := K ⊓ φ.ker) inf_le_left hKN
    rwa [← inf_assoc, inf_eq_left.mpr hTK] at h
  have hrelT : (T ⊓ φ.ker).relIndex (K ⊓ φ.ker) *
      Nat.card ↥(T ⊓ φ.ker) = Nat.card ↥(K ⊓ φ.ker) := by
    have h := Subgroup.relIndex_mul_card (H := T ⊓ φ.ker) (K := K ⊓ φ.ker)
    rwa [inf_eq_left.mpr (le_inf (inf_le_left.trans hTK) inf_le_right)] at h
  have hrel_eq : (T ⊓ B.comap φ).relIndex (K ⊓ B.comap φ) =
      (T ⊓ φ.ker).relIndex (K ⊓ φ.ker) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(T ⊓ φ.ker)))
    rw [hkey, hrelT]
  rw [hrel_eq]
  exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl).2.2

theorem s16h_exists_mul_mem_of_isSylowOf {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H X R : Subgroup G} (hHX : H ≤ X)
    (hXH : X ≤ Subgroup.normalizer (H : Set G))
    (hR : CFSG.ABGLocalTools.IsSylowOf p R H) :
    ∀ x ∈ X, ∃ h ∈ H, ∃ n ∈ Subgroup.normalizer (R : Set G), h * n = x := by
  intro x hx
  let N : Subgroup X := H.subgroupOf X
  haveI hN : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHX).mpr hXH
  obtain ⟨Q, hQ⟩ := hR.exists_sylow_eq_subgroupOf
  let e : H ≃* N := (Subgroup.subgroupOfEquivOfLe hHX).symm
  let P : Sylow p N := Sylow.mapSurjective (f := e.toMonoidHom) (EquivLike.surjective e) Q
  have hPcoe : (P : Subgroup N) = (Q : Subgroup H).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (EquivLike.surjective e) Q
  have hRleH : R ≤ H := hR.le
  have hRleX : R ≤ X := hRleH.trans hHX
  have hPmap : P.map N.subtype = R.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    calc (P.map N.subtype).map X.subtype
        = P.map (X.subtype.comp N.subtype) := by rw [Subgroup.map_map]
      _ = ((Q : Subgroup H).map e.toMonoidHom).map (X.subtype.comp N.subtype) := by
            rw [hPcoe]
      _ = (Q : Subgroup H).map ((X.subtype.comp N.subtype).comp e.toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = (Q : Subgroup H).map H.subtype := by
            congr 1
      _ = R := by
            rw [hQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRleH]
      _ = (R.subgroupOf X).map X.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRleX]
  have hfr : Subgroup.normalizer (R.subgroupOf X) ⊔ N = ⊤ := by
    have := Sylow.normalizer_sup_eq_top P
    rwa [hPmap] at this
  have hxX' : (⟨x, hx⟩ : X) ∈ N ⊔ Subgroup.normalizer (R.subgroupOf X) := by
    rw [sup_comm, hfr]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_left).mp hxX'
  refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), ?_, ?_⟩
  · have hbmem : b ∈ (Subgroup.normalizer (R : Set G)).subgroupOf X := by
      rw [Subgroup.subgroupOf_normalizer_eq hRleX]
      exact hb
    exact Subgroup.mem_subgroupOf.mp hbmem
  · have := congrArg (fun t : X => (t : G)) hab
    simpa using this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end