module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}


theorem s16k_su4z_v0 (h : S16gRowCtx D V₀ V L hV) (hZ : fixV (lBar V₀ V hV L) ≠ ⊥) :
    V₀ = ⊥ := by
  by_contra hV₀
  have hZinv : ∀ φ ∈ Mbar D.M V₀ V hV, ∀ u ∈ fixV (lBar V₀ V hV L),
      φ u ∈ fixV (lBar V₀ V hV L) :=
    fun φ hφ u hu => fixV_apply_mem_of_mem_normalizer (h.mBar_le_normalizer hφ) hu
  rcases s15_Kbar_irreducible h.setting.hyp151.hyp125 hV₀ (fixV (lBar V₀ V hV L)) hZinv with
    hbot | htop
  · exact hZ hbot
  · have hcomm : commSub ⊤ (lBar V₀ V hV L) = ⊥ :=
      commSub_eq_bot_iff.2 (le_of_eq htop.symm)
    have htopne : (⊤ : Subgroup (Vtil V₀ V hV)) ≠ ⊥ := htop ▸ hZ
    exact htopne (by rw [← h.comm_top, hcomm])

theorem s16k_su4z_v1_ne_bot (h : S16gRowCtx D V₀ V L hV) (hV0 : V₀ = ⊥)
    (hZ : fixV (lBar V₀ V hV L) ≠ ⊥) : v1Sub D.M V₀ V hV L ≠ ⊥ := by
  rw [hV0] at h hZ ⊢
  intro hbot
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hzne' : (z : Vtil (⊥ : Subgroup G) V hV) ≠ 1 := fun h1 => hzne (Subtype.ext h1)
  obtain ⟨v, hv⟩ := mkTil_surjective (⊥ : Subgroup G) V hV z
  have hvne : v.val ≠ 1 := by
    intro h1
    apply hzne'
    rw [← hv, show v = (1 : IntMod V hV) from IntMod.val_injective (by simpa using h1)]
    simp
  have hw : wSub (⊥ : Subgroup G) V hV L = V := by
    change preTil (⊥ : Subgroup G) V hV (wTil (⊥ : Subgroup G) V hV L) = V
    have hcomm : wTil (⊥ : Subgroup G) V hV L = ⊤ := by
      simpa only [wTil, lBar] using h.comm_top
    rw [hcomm, preTil_top]
  have hLs : L ≤ stabTil (⊥ : Subgroup G) V :=
    h.setting.hyp151.le.trans (s16g_le_stabTil h.setting)
  have hcen : v.val ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hφ : actTil (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ ∈ lBar (⊥ : Subgroup G) V hV L :=
      actTil_mem_barSub (⊥ : Subgroup G) V hV hl (hLs hl)
    have hfix : actTil (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ z = z := (mem_fixV.1 z.2) _ hφ
    have h1 : mkTil (⊥ : Subgroup G) V hV (actStab (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ v) =
        mkTil (⊥ : Subgroup G) V hV v := by
      calc mkTil (⊥ : Subgroup G) V hV (actStab (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ v)
          = actTil (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ (mkTil (⊥ : Subgroup G) V hV v) :=
            (actTil_mk (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ v).symm
        _ = actTil (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ z := by rw [hv]
        _ = z := hfix
        _ = mkTil (⊥ : Subgroup G) V hV v := hv.symm
    have h2 : (actStab (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ v).val * v.val⁻¹ ∈
        (⊥ : Subgroup G) :=
      (mkTil_eq_iff (⊥ : Subgroup G) V hV _ _).1 h1
    rw [Subgroup.mem_bot] at h2
    have h3 : (actStab (⊥ : Subgroup G) V hV ⟨l, hLs hl⟩ v).val = v.val :=
      mul_inv_eq_one.1 h2
    rw [actStab_apply_val] at h3
    calc l * v.val = (l * v.val * l⁻¹) * l := by group
      _ = v.val * l := by rw [h3]
  have hmem : v.val ∈ v1Sub D.M (⊥ : Subgroup G) V hV L := by
    unfold v1Sub
    rw [if_pos rfl]
    refine Subgroup.mem_iSup_of_mem (1 : D.M) ?_
    change v.val ∈ conjSubgroup (wSub (⊥ : Subgroup G) V hV L ⊓ centralizer (L : Set G)) (1 : G)
    rw [conjSubgroup_one]
    exact ⟨hw.symm ▸ v.val_mem, hcen⟩
  rw [hbot] at hmem
  exact hvne (Subgroup.mem_bot.mp hmem)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
