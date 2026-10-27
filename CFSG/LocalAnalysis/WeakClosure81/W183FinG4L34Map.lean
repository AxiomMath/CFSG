module

import CFSG.LocalAnalysis.WeakClosure81.FiveSixOrbit
public import CFSG.Holt.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.Quasithin CFSG.Open

private theorem w183finL34map_conjSubgroup_map {G₁ G₂ : Type*} [Group G₁] [Group G₂]
    (ι : G₁ →* G₂) (A : Subgroup G₁) (g : G₁) :
    (conjSubgroup A g).map ι = conjSubgroup (A.map ι) (ι g) := by
  have hcomp : (MulAut.conj (ι g)⁻¹).toMonoidHom.comp ι
      = ι.comp (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_inv_apply, map_mul,
      map_inv, inv_inv]
  rw [conjSubgroup, conjSubgroup, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem isSylowIn_map {G₁ G₂ : Type*} [Group G₁] [Group G₂] (ι : G₁ →* G₂)
    (hι : Function.Injective ι) {P H : Subgroup G₁} (h : IsSylowIn 2 P H) :
    IsSylowIn 2 (P.map ι) (H.map ι) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map ι, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective P H hι]
  exact h.2.2

theorem exists_conj_isSylowIn {G : Type*} [Group G] [Finite G] {H P Q : Subgroup G}
    (hP : IsSylowIn 2 P H) (hQ : IsSylowIn 2 Q H) :
    ∃ k ∈ H, Q = P.map (MulAut.conj k).toMonoidHom := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : fusionIsSylowIn 2 P H := fusionIsSylowIn_of_isSylowIn_two hP
  have hQ' : fusionIsSylowIn 2 Q H := fusionIsSylowIn_of_isSylowIn_two hQ
  obtain ⟨k, hkH, hk⟩ := CFSG.Holt.exists_mem_conj_of_fusionIsSylowIn hP' hQ'
  refine ⟨k, hkH, ?_⟩
  ext x
  rw [hk x, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨k⁻¹ * x * k, hx, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
  · rintro ⟨p, hp, hpx⟩
    rw [← hpx]
    convert hp using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_conj_le_isSylowIn {G : Type*} [Group G] [Finite G] {H A P : Subgroup G}
    (hAH : A ≤ H) (hA : IsPGroup 2 A) (hP : IsSylowIn 2 P H) :
    ∃ k ∈ H, A.map (MulAut.conj k).toMonoidHom ≤ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : fusionIsSylowIn 2 P H := fusionIsSylowIn_of_isSylowIn_two hP
  obtain ⟨Q, hAQ, hQ⟩ := CFSG.Holt.exists_fusionIsSylowIn_ge hA hAH
  obtain ⟨k, hkH, hk⟩ := CFSG.Holt.exists_mem_conj_of_fusionIsSylowIn hP' hQ
  refine ⟨k⁻¹, H.inv_mem hkH, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  have hmem : k⁻¹ * a * k ∈ P := (hk a).mp (hAQ ha)
  simpa [MulAut.conj_apply] using hmem

theorem isMaxParabolicMod_map {G₁ G₂ : Type} [Group G₁] [Group G₂] (ι : G₁ →* G₂)
    (hι : Function.Injective ι) {L P : Subgroup G₁} (h : IsMaxParabolicMod ⊥ L P) :
    IsMaxParabolicMod ⊥ (L.map ι) (P.map ι) := by
  obtain ⟨-, hPL, hmax, S, -, hSL, hpow, hidx, hnorm⟩ := h
  refine ⟨bot_le, ?_, ?_, S.map ι, bot_le, Subgroup.map_mono hSL, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne (Subgroup.map_mono hPL.le) ?_
    intro hEq
    exact hPL.ne (Subgroup.map_injective hι hEq)
  · intro Y hPY hYL
    have hrange : Y ≤ ι.range := hYL.trans (Subgroup.map_le_range (f := ι) L)
    have hYcL : Y.comap ι ≤ L := by
      have := Subgroup.comap_mono (f := ι) hYL
      rwa [Subgroup.comap_map_eq_self_of_injective hι] at this
    have hPYc : P < Y.comap ι := by
      refine lt_of_le_of_ne ((Subgroup.map_le_iff_le_comap).mp hPY.le) ?_
      intro hEq
      have hY : Y = P.map ι := by
        rw [hEq, Subgroup.map_comap_eq_self hrange]
      exact hPY.ne hY.symm
    have hLc : Y.comap ι = L := hmax (Y.comap ι) hPYc hYcL
    rw [← Subgroup.map_comap_eq_self hrange, hLc]
  · rintro s ⟨t, htS, rfl⟩
    obtain ⟨k, hk⟩ := hpow t htS
    refine ⟨k, ?_⟩
    rw [← map_pow]
    simp [Subgroup.mem_bot.mp hk]
  · rw [Subgroup.relIndex_map_map_of_injective S L hι]
    exact hidx
  · intro y hy
    obtain ⟨l, hlL, rfl⟩ := hy.1
    have heq : conjSubgroup S l = S := by
      apply Subgroup.map_injective hι
      rw [w183finL34map_conjSubgroup_map, (conjSubgroup_eq_iff_mem_normalizer).mpr hy.2]
    have hnormS : l ∈ Subgroup.normalizer (S : Set G₁) :=
      (conjSubgroup_eq_iff_mem_normalizer).mp heq
    exact Subgroup.mem_map.mpr ⟨l, hnorm ⟨hlL, hnormS⟩, rfl⟩

theorem isMaxParabolicMod_conj {G : Type} [Group G] {L P : Subgroup G} {τ : G}
    (hτ : τ ∈ Subgroup.normalizer (L : Set G)) (h : IsMaxParabolicMod ⊥ L P) :
    IsMaxParabolicMod ⊥ L (conjSubgroup P τ⁻¹) := by
  have hτinv : τ⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hτ
  have hmap := isMaxParabolicMod_map (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective h
  have hLmap : L.map (MulAut.conj τ).toMonoidHom = L := by
    simpa [conjSubgroup] using
      (conjSubgroup_eq_iff_mem_normalizer (A := L) (g := τ⁻¹)).mpr hτinv
  have hPmap : P.map (MulAut.conj τ).toMonoidHom = conjSubgroup P τ⁻¹ := by
    simp [conjSubgroup]
  rwa [hLmap, hPmap] at hmap

theorem actsOnDynkinMod_map {G₁ G₂ : Type} [Group G₁] [Group G₂] (ι : G₁ →* G₂)
    (hι : Function.Injective ι) {L : Subgroup G₁} {τ : G₁} (h : ActsOnDynkinMod ⊥ L τ) :
    ActsOnDynkinMod ⊥ (L.map ι) (ι τ) := by
  obtain ⟨hτ, P, hPmax, hPne⟩ := h
  refine ⟨?_, P.map ι, isMaxParabolicMod_map ι hι hPmax, ?_⟩
  · rw [← conjSubgroup_eq_iff_mem_normalizer, ← w183finL34map_conjSubgroup_map,
      (conjSubgroup_eq_iff_mem_normalizer).mpr hτ]
  · rintro l' ⟨l, hlL, rfl⟩ heq
    exact hPne l hlL (Subgroup.map_injective hι (by
      rw [w183finL34map_conjSubgroup_map, map_mul, map_inv]
      exact heq))

theorem actsOnDynkinMod_conj {G : Type} [Group G] {L : Subgroup G} {τ k : G} (hk : k ∈ L)
    (h : ActsOnDynkinMod ⊥ L τ) : ActsOnDynkinMod ⊥ L (k⁻¹ * τ * k) := by
  obtain ⟨hτ, P, hPmax, hPne⟩ := h
  have hkL : k ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hk
  have hkinv : k⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hkL
  refine ⟨?_, conjSubgroup P k, ?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem hkL) hτ) hkL
  · have := isMaxParabolicMod_conj (L := L) (P := P) (τ := k⁻¹) hkinv hPmax
    simpa using this
  · intro l hl heq
    have h1 : conjSubgroup P (τ⁻¹ * (k * l)) = conjSubgroup P k := by
      have h := heq
      rw [conjSubgroup_conjSubgroup] at h
      have harg : k * ((k⁻¹ * τ * k)⁻¹ * l) = τ⁻¹ * (k * l) := by group
      rwa [harg] at h
    have h2 : conjSubgroup P (τ⁻¹ * (k * l * k⁻¹)) = P := by
      have h := congrArg (fun A => conjSubgroup A k⁻¹) h1
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, mul_inv_cancel,
        conjSubgroup_one] at h
      have harg : (τ⁻¹ * (k * l)) * k⁻¹ = τ⁻¹ * (k * l * k⁻¹) := by group
      rwa [harg] at h
    exact hPne (k * l * k⁻¹) (L.mul_mem (L.mul_mem hk hl) (L.inv_mem hk)) h2

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
