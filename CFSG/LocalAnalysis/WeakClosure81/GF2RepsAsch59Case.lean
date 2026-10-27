module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch59CF
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch59Perm
public import CFSG.Quasithin.EmptyFaithful.S151S9UPerf
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveTypes

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch59

open Equiv CFSG.Quasithin

open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {Q : Type} [Group Q]

theorem pullback_lt_of_lt {H : Subgroup Q} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}
    {Y₀ : Subgroup (Perm (Fin n))} (hY₀ : Y₀ < ψ.range) :
    (Y₀.comap ψ).map H.subtype < H := by
  refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun hEq => ?_
  have hmap : (Y₀.comap ψ).map ψ = Y₀ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hY₀.le]
  have htop : Y₀.comap ψ = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hEq, Subgroup.map_top, Subgroup.range_subtype]
  exact hY₀.ne (by rw [← hmap, htop, Subgroup.map_top])

theorem pullback_sup_eq_of_sup_eq {H : Subgroup Q} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}
    (hψ : Function.Injective ψ) {Y₀ X₀ : Subgroup (Perm (Fin n))}
    (hY₀ : Y₀ ≤ ψ.range) (hX₀ : X₀ ≤ ψ.range) (hsup : Y₀ ⊔ X₀ = ψ.range) :
    (Y₀.comap ψ).map H.subtype ⊔ (X₀.comap ψ).map H.subtype = H := by
  have hYmap : (Y₀.comap ψ).map ψ = Y₀ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hY₀]
  have hXmap : (X₀.comap ψ).map ψ = X₀ := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hX₀]
  have htop : Y₀.comap ψ ⊔ X₀.comap ψ = ⊤ := by
    apply Subgroup.map_injective hψ
    rw [Subgroup.map_sup, hYmap, hXmap, hsup, Subgroup.map_top]
  rw [← Subgroup.map_sup, htop, Subgroup.map_top, Subgroup.range_subtype]

noncomputable def pullbackMulEquiv {H : Subgroup Q} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}
    (hψ : Function.Injective ψ) {Y₀ : Subgroup (Perm (Fin n))} (hY₀ : Y₀ ≤ ψ.range) :
    ↥((Y₀.comap ψ).map H.subtype) ≃* ↥Y₀ :=
  ((Y₀.comap ψ).equivMapOfInjective H.subtype H.subtype_injective).symm.trans
    ((Y₀.comap ψ).equivMapOfInjective ψ hψ |>.trans
      (MulEquiv.subgroupCongr (by rw [Subgroup.map_comap_eq, inf_eq_right.mpr hY₀])))

theorem le_pullback_of_map_subgroupOf_le {H T : Subgroup Q} {n : ℕ}
    {ψ : ↥H →* Perm (Fin n)} (hTH : T ≤ H) {Y₀ : Subgroup (Perm (Fin n))}
    (hTY : (T.subgroupOf H).map ψ ≤ Y₀) : T ≤ (Y₀.comap ψ).map H.subtype := by
  intro t ht
  refine Subgroup.mem_map.mpr ⟨⟨t, hTH ht⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
  exact hTY (Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.mpr ht))

theorem not_hasCompFactor_isCalL0_of_isSolvable [Finite Q]
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧
        ∃ a b : L, a * b ≠ b * a)
    {X : Subgroup Q} (hX : Group.IsSolvable ↥X) : ¬ HasCompFactor X IsCalL0 := by
  rintro ⟨L, hgrpL, hcf, hL0L⟩
  let hgrp : Group L := hgrpL
  obtain ⟨-, -, a, b, hab⟩ := hL0 L hL0L
  exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
    hX hcf a b)

theorem not_hasCompFactor_isCalL0_of_ker_isPGroup [Finite Q]
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧
        ∃ a b : L, a * b ≠ b * a)
    {X : Subgroup Q} (φ : ↥X →* Perm (Fin 5)) (hker : IsPGroup 2 φ.ker) :
    ¬ HasCompFactor X IsCalL0 := by
  rintro ⟨L, hgrpL, hcf, hL0L⟩
  let hgrp : Group L := hgrpL
  obtain ⟨hLfin, hLrank, a, b, hab⟩ := hL0 L hL0L
  have hLfin' : Finite L := hLfin
  rcases isCompositionFactor_comm_or_pRank_two_le_two φ hker hcf with hcomm | hrank
  · exact hab (hcomm a b)
  · omega

theorem eq_lGen_of_injective_perm {Q : Type} [Group Q] [Finite Q] {H T : Subgroup Q}
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a)
    {n : ℕ} (h6 : 6 ≤ n) (h11 : n ≤ 11) (h9 : n ≠ 9) (ψ : ↥H →* Perm (Fin n))
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin n) ≤ ψ.range) (hTH : T ≤ H)
    (hT : IsPGroup 2 T) :
    H = lGen IsCalL0 H T := by
  classical
  have hT₀ : IsPGroup 2 ((T.subgroupOf H).map ψ) :=
    (IsPGroup.comap_subtype (K := H) hT).map ψ
  obtain ⟨Y₀, X₀, hTY₀, hY₀lt, hTX₀, hX₀lt, hsup, hY₀solv, φ₀, hφ₀ker⟩ :=
    exists_sup_eq_of_card (Ω := Fin n) (G := ψ.range) (T := (T.subgroupOf H).map ψ)
      (by simpa using h6) (by simpa using h11) (by simpa using h9) hA
      (Subgroup.map_le_range ψ (T.subgroupOf H)) hT₀
  have hY₀le : Y₀ ≤ ψ.range := hY₀lt.le
  have hX₀le : X₀ ≤ ψ.range := hX₀lt.le
  have hYlt : (Y₀.comap ψ).map H.subtype < H := pullback_lt_of_lt hY₀lt
  have hXlt : (X₀.comap ψ).map H.subtype < H := pullback_lt_of_lt hX₀lt
  have hTY : T ≤ (Y₀.comap ψ).map H.subtype :=
    le_pullback_of_map_subgroupOf_le hTH hTY₀
  have hTX : T ≤ (X₀.comap ψ).map H.subtype :=
    le_pullback_of_map_subgroupOf_le hTH hTX₀
  have hsolvY : Group.IsSolvable ↥((Y₀.comap ψ).map H.subtype) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (pullbackMulEquiv hψ hY₀le).toMonoidHom)
      (pullbackMulEquiv hψ hY₀le).injective
  have hnoY : ¬ HasCompFactor ((Y₀.comap ψ).map H.subtype) IsCalL0 :=
    not_hasCompFactor_isCalL0_of_isSolvable hL0 hsolvY
  have hnoX : ¬ HasCompFactor ((X₀.comap ψ).map H.subtype) IsCalL0 := by
    refine not_hasCompFactor_isCalL0_of_ker_isPGroup hL0
      (φ₀.comp (pullbackMulEquiv hψ hX₀le).toMonoidHom) ?_
    have hker : (φ₀.comp (pullbackMulEquiv hψ hX₀le).toMonoidHom).ker =
        φ₀.ker.comap (pullbackMulEquiv hψ hX₀le).toMonoidHom := by
      ext x
      rfl
    rw [hker]
    exact hφ₀ker.comap_of_injective _ (pullbackMulEquiv hψ hX₀le).injective
  have hYmem : (Y₀.comap ψ).map H.subtype ∈ calLT IsCalL0 H T := ⟨hTY, hYlt, hnoY⟩
  have hXmem : (X₀.comap ψ).map H.subtype ∈ calLT IsCalL0 H T := ⟨hTX, hXlt, hnoX⟩
  have hsup' : (Y₀.comap ψ).map H.subtype ⊔ (X₀.comap ψ).map H.subtype = H :=
    pullback_sup_eq_of_sup_eq hψ hY₀le hX₀le hsup
  have hHle : H ≤ lGen IsCalL0 H T :=
    hsup'.ge.trans (sup_le (le_iSup₂_of_le _ hYmem le_rfl)
      (le_iSup₂_of_le _ hXmem le_rfl))
  have hle : lGen IsCalL0 H T ≤ H := iSup₂_le fun X hX => hX.2.1.le
  exact le_antisymm hHle hle

theorem pRank_three_of_injective_perm {Q : Type} [Group Q] [Finite Q] {H T : Subgroup Q}
    (hL0 : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧ ∃ a b : L, a * b ≠ b * a)
    {n : ℕ} (h12 : 12 ≤ n) (ψ : ↥H →* Perm (Fin n)) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) (hTH : T ≤ H) (hT : IsPGroup 2 T) :
    3 < CFSG.Open.pRank 3 (perfectCore H) ∧ 1 < CFSG.Open.pRank 3 (lGen IsCalL0 H T) := by
  classical
  have hT₀ : IsPGroup 2 ((T.subgroupOf H).map ψ) :=
    (IsPGroup.comap_subtype (K := H) hT).map ψ
  obtain ⟨H', hT₀H', hH'lt, hH'solv, hH'rank⟩ :=
    exists_isSolvable_two_le_pRank_three (Ω := Fin n) (G := ψ.range)
      (T := (T.subgroupOf H).map ψ) (by rw [Fintype.card_fin]; omega) hA
      (Subgroup.map_le_range ψ (T.subgroupOf H)) hT₀
  have hH'le : H' ≤ ψ.range := hH'lt.le
  have hKlt : (H'.comap ψ).map H.subtype < H := pullback_lt_of_lt hH'lt
  have hTK : T ≤ (H'.comap ψ).map H.subtype :=
    le_pullback_of_map_subgroupOf_le hTH hT₀H'
  have hsolvK : Group.IsSolvable ↥((H'.comap ψ).map H.subtype) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (pullbackMulEquiv hψ hH'le).toMonoidHom)
      (pullbackMulEquiv hψ hH'le).injective
  have hnoK : ¬ HasCompFactor ((H'.comap ψ).map H.subtype) IsCalL0 :=
    not_hasCompFactor_isCalL0_of_isSolvable hL0 hsolvK
  have hKmem : (H'.comap ψ).map H.subtype ∈ calLT IsCalL0 H T := ⟨hTK, hKlt, hnoK⟩
  have hKle : (H'.comap ψ).map H.subtype ≤ lGen IsCalL0 H T :=
    le_iSup₂_of_le _ hKmem le_rfl
  have hrankK : 2 ≤ CFSG.Open.pRank 3 ((H'.comap ψ).map H.subtype) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
      (pullbackMulEquiv hψ hH'le)]
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H']
  have hlgen : 1 < CFSG.Open.pRank 3 (lGen IsCalL0 H T) :=
    lt_of_lt_of_le (by norm_num : 1 < 2)
      (hrankK.trans (CFSG.SectionRank.pRank_mono (by norm_num) hKle))
  let P : Subgroup ↥H := perfectCore (⊤ : Subgroup ↥H)
  have hPH : P.map H.subtype = perfectCore H := by
    have h := map_perfectCore H.subtype (⊤ : Subgroup ↥H)
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  have hPψ : P.map ψ = alternatingGroup (Fin n) := by
    have h := map_perfectCore ψ (⊤ : Subgroup ↥H)
    rw [Subgroup.map_top] at h
    rw [h, CFSG.Quasithin.S151S9U.perfectCore_eq_alternatingGroup (m := n) (by omega) hA]
  have ePerf : ↥(perfectCore H) ≃* ↥(alternatingGroup (Fin n)) :=
    ((MulEquiv.subgroupCongr hPH).symm.trans
      (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).symm).trans
        ((Subgroup.equivMapOfInjective P ψ hψ).trans (MulEquiv.subgroupCongr hPψ))
  have hperfRank : 3 < CFSG.Open.pRank 3 (perfectCore H) := by
    have h1 : n / 3 ≤ CFSG.Open.pRank 3 (perfectCore H) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP.div_three_le_pRank_of_alt
        ePerf
    have h2 : 4 ≤ n / 3 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mpr (by omega)
    omega
  exact ⟨hperfRank, hlgen⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch59

end
