module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem s16h_zresGroup_commSub_stab {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

private theorem s16h_zresGroup_stab_fixV {L : Subgroup (MulAut W)} :
    normalizer (L : Set (MulAut W)) ≤ stabSub (commSub ⊤ L ⊓ fixV L) := by
  intro x hx
  have hxnorm : ∀ l ∈ L, x * l * x⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp hx l).mp hl
  have hxinvnorm : ∀ l ∈ L, x⁻¹ * l * (x⁻¹)⁻¹ ∈ L := fun l hl =>
    (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hx) l).mp hl
  have hxZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxnorm u hu.1, ?_⟩
    intro l hl
    calc l (x u) = x ((x⁻¹ * l * x) u) := by simp [MulAut.mul_apply]
      _ = x u := by rw [mem_fixV.mp hu.2 (x⁻¹ * l * x) (by simpa using hxinvnorm l hl)]
  have hxinvZ : ∀ u ∈ commSub ⊤ L ⊓ fixV L, x⁻¹ u ∈ commSub ⊤ L ⊓ fixV L := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨commSub_top_stable151b hxinvnorm u hu.1, ?_⟩
    intro l hl
    calc l (x⁻¹ u) = x⁻¹ ((x * l * x⁻¹) u) := by simp [MulAut.mul_apply]
      _ = x⁻¹ u := by rw [mem_fixV.mp hu.2 (x * l * x⁻¹) (hxnorm l hl)]
  rw [mem_stabSub]
  intro u
  exact ⟨fun hu => by have := hxinvZ (x u) hu; simpa using this, hxZ u⟩

theorem s16h_H5_zcondGroup_of_world {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hc : s16h_H5Cfg A L t)
    (hW : s16h_L3World (autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L))
      (autSub L (commSub ⊤ L))) :
    s16h_ZCondGroup ↥(autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W)))
      (commSub ⊤ L ⊓ fixV L)) := by
  classical
  set N : Subgroup (MulAut W) := A ⊓ normalizer (L : Set (MulAut W)) with hN
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hNU : N ≤ stabSub U := by
    rw [hU]
    exact fun g hg => s16h_zresGroup_commSub_stab (L := L) (Subgroup.mem_inf.mp hg).2
  have hNZ : N ≤ stabSub Z := by
    rw [hZ]
    exact fun g hg => s16h_zresGroup_stab_fixV (L := L) (Subgroup.mem_inf.mp hg).2
  let gU : ↥N →* MulAut U := (resHom U).comp (Subgroup.inclusion hNU)
  have hgUrange : gU.range = autSub N U := by
    change ((resHom U).comp (Subgroup.inclusion hNU)).range = autSub N U
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  let res : ↥N →* ↥(autSub N U) :=
    gU.codRestrict (autSub N U) fun n => hgUrange ▸ (show gU n ∈ gU.range from ⟨n, rfl⟩)
  have hres_surj : Function.Surjective res := by
    intro y
    have hy : (y : MulAut U) ∈ gU.range := by rw [hgUrange]; exact y.2
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, Subtype.ext hn⟩
  have hres_top : res.range = ⊤ := MonoidHom.range_eq_top.mpr hres_surj
  let gZ : ↥N →* MulAut Z := (resHom Z).comp (Subgroup.inclusion hNZ)
  have hgZrange : gZ.range = autSub N Z := by
    change ((resHom Z).comp (Subgroup.inclusion hNZ)).range = autSub N Z
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  let κ : ↥N →* ↥(autSub N Z) :=
    gZ.codRestrict (autSub N Z) fun n => hgZrange ▸ (show gZ n ∈ gZ.range from ⟨n, rfl⟩)
  have hκ_surj : Function.Surjective κ := by
    intro y
    have hy : (y : MulAut Z) ∈ gZ.range := by rw [hgZrange]; exact y.2
    obtain ⟨n, hn⟩ := hy
    exact ⟨n, Subtype.ext hn⟩
  obtain ⟨P, hP, ρ, hkerρ, hρ⟩ := s16h_L3World_group hW
  letI := hP
  let ρ' : ↥N →* P := ρ.comp res
  have hρ'range : ρ'.range = ρ.range := by
    change (ρ.comp res).range = ρ.range
    rw [MonoidHom.range_comp, hres_top, Subgroup.map_top]
  have hρ' : s16h_ZCondGroup ↥ρ'.range := by
    rw [hρ'range]
    exact hρ
  have hker : ρ'.ker ≤ κ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    change ρ (res x) = 1 at hx
    have hLmem : (res x : MulAut U) ∈ autSub L U := hkerρ (res x) hx
    obtain ⟨g, hgL, hgres⟩ := mem_autSub.mp hLmem
    have htriv : ∀ z : Z, (x : MulAut W) (z : W) = (z : W) := by
      intro z
      have hzZ : (z : W) ∈ commSub ⊤ L ⊓ fixV L := z.2
      have hzU : (z : W) ∈ commSub ⊤ L := (Subgroup.mem_inf.mp hzZ).1
      have hzfix : (z : W) ∈ fixV L := (Subgroup.mem_inf.mp hzZ).2
      have hval : ((res x : MulAut U) ⟨(z : W), hzU⟩ : W) = (x : MulAut W) (z : W) := by
        change ((resHom U (Subgroup.inclusion hNU x)) ⟨(z : W), hzU⟩ : W) = _
        rw [resHom_apply]
        rfl
      have h1 : ((res x : MulAut U) ⟨(z : W), hzU⟩ : W) = (g : MulAut W) (z : W) := by
        rw [← hgres]
        exact resHom_apply U g ⟨(z : W), hzU⟩
      exact hval.symm.trans (h1.trans (mem_fixV.mp hzfix g hgL))
    have hgZx : gZ x = 1 := by
      ext z
      change ((resHom Z (Subgroup.inclusion hNZ x)) z : W) = (z : W)
      rw [resHom_apply]
      exact htriv z
    exact Subtype.ext hgZx
  exact s16h_zcondGroup_of_ker_le ρ' κ hκ_surj hker hρ'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
