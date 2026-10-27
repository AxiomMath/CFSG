module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Ind

public section

namespace CFSG.Quasithin.H13.C1294

open Module MulAction

section Values

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]

@[expose] def subgroupSuperAct {W : Submodule (ZMod 2) I} {H : Subgroup (I ≃ₗ[ZMod 2] I)}
    (hH : H ≤ stabS W) (j : ℕ) : MulAction H (SuperOf W j) where
  smul h U := ⟨U.1.map (h.1 : I →ₗ[ZMod 2] I), by
    refine ⟨?_, ?_⟩
    · have hW : W.map (h.1 : I →ₗ[ZMod 2] I) = W := map_eq_of_mem_stabS (hH h.2)
      exact (le_of_eq hW.symm).trans (Submodule.map_mono U.2.1)
    · rw [LinearEquiv.finrank_map_eq]
      exact U.2.2⟩
  one_smul U := Subtype.ext (Submodule.map_id _)
  mul_smul g h U := Subtype.ext (by
    show U.1.map ((g * h).1 : I →ₗ[ZMod 2] I) =
      (U.1.map (h.1 : I →ₗ[ZMod 2] I)).map (g.1 : I →ₗ[ZMod 2] I)
    rw [← Submodule.map_comp]
    rfl)

theorem index_flag_B {p ℓ Pl : Submodule (ZMod 2) I} (hI : finrank (ZMod 2) I = 4)
    (hp : finrank (ZMod 2) p = 1) (hℓ : finrank (ZMod 2) ℓ = 2) (hPl : finrank (ZMod 2) Pl = 3)
    (hpℓ : p ≤ ℓ) (hℓPl : ℓ ≤ Pl) :
    (stabS p ⊓ stabS ℓ ⊓ stabS Pl).index = (stabS p ⊓ stabS ℓ).index * 3 := by
  set H : Subgroup (I ≃ₗ[ZMod 2] I) := stabS p ⊓ stabS ℓ with hHdef
  have hHle : H ≤ stabS ℓ := inf_le_right
  letI : MulAction H (SuperOf ℓ 3) := subgroupSuperAct hHle 3
  have htrans : IsPretransitive H (SuperOf ℓ 3) := by
    constructor
    rintro ⟨U, hU, hUj⟩ ⟨U', hU', hUj'⟩
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl ℓ
    obtain ⟨g, hgℓ, hfix, hmap⟩ := exists_stabS_fix_map_super hC hU hU' (hUj.trans hUj'.symm)
    have hgp : g ∈ stabS p := by
      show ∀ v, v ∈ p ↔ g v ∈ p
      intro v
      constructor
      · intro hv
        rw [hfix v (hpℓ hv)]
        exact hv
      · intro hv
        have hvℓ : v ∈ ℓ := (hgℓ v).2 (hpℓ hv)
        rw [hfix v hvℓ] at hv
        exact hv
    refine ⟨⟨g, Subgroup.mem_inf.2 ⟨hgp, hgℓ⟩⟩, Subtype.ext ?_⟩
    exact hmap
  have hcard : Nat.card (SuperOf ℓ 3) = 3 := by
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl ℓ
    have hCd : finrank (ZMod 2) C = 2 := by
      have h := Submodule.finrank_add_eq_of_isCompl hC
      omega
    rw [card_superOf ℓ C hC 3 (by omega) (by omega), hCd, hℓ]
    rfl
  have hstab : stabilizer H (⟨Pl, hℓPl.trans (le_refl Pl), hPl⟩ : SuperOf ℓ 3) =
      (stabS Pl).subgroupOf H := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      have hPl' : Pl.map (g.1 : I →ₗ[ZMod 2] I) = Pl := h'
      exact (map_eq_iff_mem_stabS Pl _).1 hPl'
    · intro h
      apply Subtype.ext
      exact (map_eq_iff_mem_stabS Pl _).2 h
  have h1 := Subgroup.relIndex_mul_index (inf_le_left : stabS p ⊓ stabS ℓ ⊓ stabS Pl ≤ H)
  have hrel : (stabS p ⊓ stabS ℓ ⊓ stabS Pl).relIndex H = 3 := by
    rw [Subgroup.relIndex]
    have e : (stabS p ⊓ stabS ℓ ⊓ stabS Pl).subgroupOf H = (stabS Pl).subgroupOf H := by
      ext h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ⟨fun h' => h'.2, fun h' => ⟨h.2, h'⟩⟩
    rw [e, ← hstab, MulAction.index_stabilizer_of_transitive, hcard]
  rw [← h1, hrel, mul_comm]


theorem exists_K1_map_super {p ℓ : Submodule (ZMod 2) I} (hpℓ : p ≤ ℓ) {U U' : Submodule (ZMod 2) I}
    (hU : ℓ ≤ U) (hU' : ℓ ≤ U') (h : finrank (ZMod 2) U = finrank (ZMod 2) U') :
    ∃ g ∈ stabS p ⊓ stabS ℓ, Submodule.map (g : I →ₗ[ZMod 2] I) U = U' := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl ℓ
  obtain ⟨g, hgℓ, hfix, hmap⟩ := exists_stabS_fix_map_super hC hU hU' h
  refine ⟨g, Subgroup.mem_inf.2 ⟨?_, hgℓ⟩, hmap⟩
  show ∀ v, v ∈ p ↔ g v ∈ p
  intro v
  constructor
  · intro hv
    rw [hfix v (hpℓ hv)]
    exact hv
  · intro hv
    have hvℓ : v ∈ ℓ := (hgℓ v).2 (hpℓ hv)
    rw [hfix v hvℓ] at hv
    exact hv

theorem index_flag_values {p ℓ Pl : Submodule (ZMod 2) I} (hI : finrank (ZMod 2) I = 4)
    (hp : finrank (ZMod 2) p = 1) (hℓ : finrank (ZMod 2) ℓ = 2) (hPl : finrank (ZMod 2) Pl = 3)
    (hpℓ : p ≤ ℓ) (hℓPl : ℓ ≤ Pl) :
    (stabS p).index = 15 ∧ (stabS ℓ).index = 35 ∧ (stabS Pl).index = 15 ∧
      (stabS p ⊓ stabS ℓ).index = 105 ∧ (stabS p ⊓ stabS Pl).index = 105 ∧
      (stabS ℓ ⊓ stabS Pl).index = 105 ∧ (stabS p ⊓ stabS ℓ ⊓ stabS Pl).index = 315 := by
  have hpPl : p ≤ Pl := hpℓ.trans hℓPl
  have hK1 : (stabS p ⊓ stabS ℓ).index = 105 := by
    rw [index_inf_sub hpℓ, index_stabS_two hℓ hI, hp]
    rw [card_subsOf ℓ 1 (by omega), hℓ]
    rfl
  have hK2 : (stabS p ⊓ stabS Pl).index = 105 := by
    rw [index_inf_super hpPl, index_stabS_one hp hI, hPl]
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl p
    have hCd : finrank (ZMod 2) C = 3 := by
      have h := Submodule.finrank_add_eq_of_isCompl hC
      omega
    rw [card_superOf p C hC 3 (by omega) (by omega), hCd, hp]
    rfl
  have hK3 : (stabS ℓ ⊓ stabS Pl).index = 105 := by
    rw [index_inf_super hℓPl, index_stabS_two hℓ hI, hPl]
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl ℓ
    have hCd : finrank (ZMod 2) C = 2 := by
      have h := Submodule.finrank_add_eq_of_isCompl hC
      omega
    rw [card_superOf ℓ C hC 3 (by omega) (by omega), hCd, hℓ]
    rfl
  refine ⟨index_stabS_one hp hI, index_stabS_two hℓ hI, index_stabS_three hPl hI, hK1, hK2, hK3, ?_⟩
  rw [index_flag_B hI hp hℓ hPl hpℓ hℓPl, hK1]

theorem not_le_stabS_of_flag {p ℓ Pl : Submodule (ZMod 2) I} (hI : finrank (ZMod 2) I = 4)
    (hℓ : finrank (ZMod 2) ℓ = 2) (hPl : finrank (ZMod 2) Pl = 3) (hpℓ : p ≤ ℓ) (hℓPl : ℓ ≤ Pl) :
    ¬ (stabS p ⊓ stabS ℓ ≤ stabS Pl) := by
  intro hle
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl ℓ
  have hCd : finrank (ZMod 2) C = 2 := by
    have h := Submodule.finrank_add_eq_of_isCompl hC
    omega
  have hcard : Nat.card (SuperOf ℓ 3) = 3 := by
    rw [card_superOf ℓ C hC 3 (by omega) (by omega), hCd, hℓ]
    rfl
  have hnot : ∃ U : SuperOf ℓ 3, U.1 ≠ Pl := by
    by_contra hcon
    push_neg at hcon
    have hsub : Subsingleton (SuperOf ℓ 3) :=
      ⟨fun a b => Subtype.ext ((hcon a).trans (hcon b).symm)⟩
    have h1 := (Finite.card_le_one_iff_subsingleton (α := SuperOf ℓ 3)).2 hsub
    omega
  obtain ⟨U, hU⟩ := hnot
  obtain ⟨g, hg, hmap⟩ := exists_K1_map_super hpℓ hℓPl U.2.1 (by rw [hPl, U.2.2])
  have hgPl : g ∈ stabS Pl := hle hg
  have hPl' : Pl.map (g : I →ₗ[ZMod 2] I) = Pl := (map_eq_iff_mem_stabS Pl _).2 hgPl
  exact hU (hmap.symm.trans hPl')

end Values

end CFSG.Quasithin.H13.C1294
