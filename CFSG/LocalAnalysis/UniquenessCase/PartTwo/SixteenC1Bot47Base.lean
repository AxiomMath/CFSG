module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_conjSubgroup_hConjClosure {z : G} (A : Subgroup G) {k : G}
    (hk : k ∈ centralizer ({z} : Set G)) :
    conjSubgroup (hConjClosure z A) k = hConjClosure z A := by
  have key : conjSubgroup (hConjClosure z A) k
      = ⨆ h : ↥(centralizer ({z} : Set G)), conjSubgroup A ((h : G) * k) := by
    simp only [hConjClosure]
    change ((⨆ h : ↥(centralizer ({z} : Set G)), conjSubgroup A (h : G)).map
        (MulAut.conj k⁻¹).toMonoidHom)
      = ⨆ h : ↥(centralizer ({z} : Set G)), conjSubgroup A ((h : G) * k)
    rw [Subgroup.map_iSup]
    refine iSup_congr fun h => ?_
    change conjSubgroup (conjSubgroup A (h : G)) k = conjSubgroup A ((h : G) * k)
    rw [conjSubgroup_conjSubgroup]
  rw [key, hConjClosure]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun h => le_iSup (fun h : ↥(centralizer ({z} : Set G)) =>
      conjSubgroup A (h : G)) ⟨(h : G) * k, mul_mem h.2 hk⟩
  · refine iSup_le fun h => ?_
    have hh : ((⟨(h : G) * k⁻¹, mul_mem h.2 (inv_mem hk)⟩ :
        ↥(centralizer ({z} : Set G))) : G) * k = (h : G) := by group
    rw [← hh]
    exact le_iSup (fun h : ↥(centralizer ({z} : Set G)) =>
      conjSubgroup A ((h : G) * k)) ⟨(h : G) * k⁻¹, mul_mem h.2 (inv_mem hk)⟩

theorem s16c1_centralizes_of_comm_le_zpowers {V : Subgroup G} {hV : IsElemAbelian 2 V}
    {H : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV))} (hNT : OmegaNoTrans H)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) {t : G} (ht : t ∈ stabTil (⊥ : Subgroup G) V)
    (htH : actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ ∈ H)
    (hcomm : ∀ v ∈ V, t * v * t⁻¹ * v⁻¹ ∈ Subgroup.zpowers z) :
    ∀ v ∈ V, t * v * t⁻¹ = v := by
  let zmk : IntMod V hV := IntMod.mk hV ⟨z, hz⟩
  let c : Vtil (⊥ : Subgroup G) V hV := mkTil ⊥ V hV zmk
  have hzsq : z ^ (2 : ℤ) = 1 := by simpa using hV.2 z hz
  have hc1 : c ≠ 1 := by
    intro hc
    have h1 : mkTil (⊥ : Subgroup G) V hV zmk
        = mkTil (⊥ : Subgroup G) V hV (1 : IntMod V hV) := by
      rw [map_one]
      exact hc
    have hmem : z ∈ (⊥ : Subgroup G) := by
      have h := (mkTil_eq_iff (⊥ : Subgroup G) V hV zmk 1).1 h1
      have hzmk : zmk.val = z := rfl
      rw [Subgroup.mem_bot, hzmk, IntMod.val_one, inv_one, mul_one] at h
      exact h
    exact hz1 (Subgroup.mem_bot.1 hmem)
  have hphi : ∀ w : Vtil (⊥ : Subgroup G) V hV,
      actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ w = w ∨
        actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ w = w * c := by
    intro w
    obtain ⟨y, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).1 (hcomm y.val y.val_mem)
    have hty : t * y.val * t⁻¹ = z ^ k * y.val := by rw [hk]; group
    rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
    · left
      have hze : z ^ k = 1 := by rw [hm, zpow_mul, hzsq, one_zpow]
      have hstab : actStab (⊥ : Subgroup G) V hV ⟨t, ht⟩ y = y := by
        apply IntMod.val_injective
        rw [actStab_apply_val, hty, hze, one_mul]
      change actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ (mkTil (⊥ : Subgroup G) V hV y)
        = mkTil (⊥ : Subgroup G) V hV y
      rw [actTil_mk, hstab]
    · right
      have hzo : z ^ k = z := by
        rw [hm, zpow_add, zpow_mul, hzsq, one_zpow, one_mul, zpow_one]
      have hstab : actStab (⊥ : Subgroup G) V hV ⟨t, ht⟩ y = zmk * y := by
        apply IntMod.val_injective
        rw [actStab_apply_val, IntMod.val_mul]
        rw [hty, hzo]
        rfl
      change actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ (mkTil (⊥ : Subgroup G) V hV y)
        = mkTil (⊥ : Subgroup G) V hV y * c
      rw [actTil_mk, hstab, map_mul]
      exact mul_comm _ _
  have hphi1 : actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩ = 1 :=
    hNT (actTil (⊥ : Subgroup G) V hV ⟨t, ht⟩) htH c hc1 hphi
  intro v hv
  have h := (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨t, ht⟩).1 hphi1 v hv
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h
  exact h

theorem s16c1_hyp1643_conj_V (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V) {h : G}
    (hle : conjSubgroup V h ≤ D.M) : Hyp1643 D ⊥ V 0 (conjSubgroup V h) h := by
  have hV2 : IsPGroup 2 V := fun y => ⟨1, Subtype.ext (by simpa using hV.2 y y.2)⟩
  have hpg : IsPGroup 2 (conjSubgroup V h) := IsPGroup.map hV2 _
  exact ⟨Or.inl rfl, ⟨hle, h, le_rfl, (E3.mQuot_eq_zero_iff hpg le_rfl).2 rfl⟩, le_rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
