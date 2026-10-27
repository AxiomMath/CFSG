module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Quot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {W : Type} [CommGroup W]

theorem commSub_map_conj (g : MulAut W) (A : Subgroup W) (X : Subgroup (MulAut W)) :
    commSub (A.map g.toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) =
      (commSub A X).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨x a * a⁻¹, ⟨x, hx, a, ha, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]
  · rintro ⟨_, ⟨x, hx, a, ha, rfl⟩, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, _, ⟨a, ha, rfl⟩, ?_⟩
    simp [MulAut.conj_apply]

theorem commSub_map_mk {X : Subgroup (MulAut W)} {C : Subgroup W} (hX : X ≤ stabSub C)
    (A : Subgroup W) :
    commSub (A.map (QuotientGroup.mk' C)) (autQuot X C) =
      (commSub A X).map (QuotientGroup.mk' C) := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨_, hφ, _, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨g, hgX, rfl⟩ := mem_autQuot.mp hφ
    refine ⟨g.1 a * a⁻¹, ⟨g.1, hgX, a, ha, rfl⟩, ?_⟩
    simp [quotHom_mk]
  · rintro ⟨_, ⟨x, hx, a, ha, rfl⟩, rfl⟩
    refine ⟨quotHom C ⟨x, hX hx⟩, mem_autQuot.mpr ⟨⟨x, hX hx⟩, hx, rfl⟩, _, ⟨a, ha, rfl⟩, ?_⟩
    simp [quotHom_mk]

theorem commV_autQuot {X : Subgroup (MulAut W)} {C : Subgroup W} (hX : X ≤ stabSub C) :
    commV (autQuot X C) = (commV X).map (QuotientGroup.mk' C) := by
  rw [commV_eq_commSub, commV_eq_commSub, ← commSub_map_mk hX, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective C)]

theorem secIsoOn_commSub_le {X X' : Subgroup (MulAut W)} {A A₀ B B₀ : Subgroup W}
    (h : SecIsoOn X A A₀ B B₀) (hX' : X' ≤ X) (hA : commSub A X' ≤ A₀) :
    commSub B X' ≤ B₀ := by
  obtain ⟨hA₀A, hB₀B, hXA, -, -, hXB₀, β, hβB, hβiff, hβsurj, hβeq⟩ := h
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, b, hb, rfl⟩
  obtain ⟨a, ha⟩ := hβsurj b hb
  set c := (β a * b⁻¹)⁻¹ with hc
  have hcB₀ : c ∈ B₀ := B₀.inv_mem ha
  have hb' : b = β a * c := by
    rw [hc, mul_inv_rev, inv_inv, mul_comm b, mul_inv_cancel_left]
  have hxc : x c * c⁻¹ ∈ B₀ := B₀.mul_mem (hXB₀ x (hX' hx) c hcB₀) (B₀.inv_mem hcB₀)
  set a' : ↥A := ⟨x a, hXA x (hX' hx) a a.2⟩ with ha'
  have h1 : β a' * (x (β a))⁻¹ ∈ B₀ := hβeq x (hX' hx) a a' rfl
  have hxa : (x (a : W)) * (a : W)⁻¹ ∈ A₀ := hA (Subgroup.subset_closure ⟨x, hx, a, a.2, rfl⟩)
  have h2 : β (a' * a⁻¹) ∈ B₀ := (hβiff _).mpr (by simpa [ha'] using hxa)
  have he : x b * b⁻¹ = (β a' * (x (β a))⁻¹)⁻¹ * β (a' * a⁻¹) * (x c * c⁻¹) := by
    have e1 : x (β a) * (β a)⁻¹ = (β a' * (x (β a))⁻¹)⁻¹ * β (a' * a⁻¹) := by
      rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [hb', map_mul, mul_inv, mul_mul_mul_comm, e1]
  rw [he]
  exact B₀.mul_mem (B₀.mul_mem (B₀.inv_mem h1) h2) hxc

variable [Finite W]

omit [Finite W] in
theorem fixV_autQuot_eq_bot {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) : fixV (autQuot H (fixV H)) = ⊥ := by
  obtain ⟨h1, -, -, hn, -, -⟩ := h_facts hL hH
  have hQ : QuadTrivial H := by
    rw [h1]
    exact quadTrivial_biSup_conj hL.2.2.1 Y
  have hHstab : H ≤ stabSub (fixV H) := by
    intro h hh u
    refine ⟨fun hu => ?_, fun hu => by rw [hu h hh]; exact hu⟩
    have h2 : h⁻¹ (h u) = h u := hu h⁻¹ (H.inv_mem hh)
    rw [MulAut.inv_apply_self] at h2
    rw [h2]
    exact hu
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (fixV H) v
  have hw : ∀ h ∈ H, h w * w⁻¹ ∈ fixV H := by
    intro h hh
    have := hv (quotHom (fixV H) ⟨h, hHstab hh⟩) (mem_autQuot.mpr ⟨⟨h, hHstab hh⟩, hh, rfl⟩)
    rw [QuotientGroup.mk'_apply, quotHom_mk] at this
    exact (mk_eq_mk_iff _ _).mp this
  set J := Subgroup.closure {w} ⊔ fixV H with hJ
  have hJs : StableUnder H J := by
    intro h hh u hu
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, hc h hh]
    refine J.mul_mem ?_ (le_sup_right (α := Subgroup W) hc)
    obtain ⟨k, rfl⟩ := Subgroup.mem_closure_singleton.mp ha
    rw [map_zpow]
    refine J.zpow_mem ?_ k
    have hhw : h w = (h w * w⁻¹) * w := by group
    rw [hhw]
    exact J.mul_mem (le_sup_right (α := Subgroup W) (hw h hh))
      (le_sup_left (α := Subgroup W) (Subgroup.mem_closure_singleton.mpr ⟨1, by simp⟩))
  have hJc : commSub J H ≤ fixV H := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨h, hh, u, hu, rfl⟩
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul, hc h hh, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    obtain ⟨k, rfl⟩ := Subgroup.mem_closure_singleton.mp ha
    rw [map_zpow, ← inv_zpow, ← mul_zpow]
    exact (fixV H).zpow_mem (hw h hh) k
  have h0 := hQ J hJs hJc
  have hwJ : w ∈ fixV H := by
    have hwmem : w ∈ J := le_sup_left (α := Subgroup W) (Subgroup.mem_closure_singleton.mpr ⟨1, by simp⟩)
    exact commSub_eq_bot_iff.mp h0 hwmem
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hwJ

omit [Finite W] in
theorem iSup_conjSet_conj {Y L X : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) :
    (⨆ φ ∈ Y, X.map (MulAut.conj φ).toMonoidHom) = ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom := by
  obtain ⟨n, hn, rfl⟩ := hX
  apply le_antisymm
  · refine iSup₂_le fun φ hφ => ?_
    rw [Subgroup.map_map]
    refine le_iSup₂_of_le (φ * n) (Y.mul_mem hφ hn) ?_
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨l, hl, by simp [MulAut.conj_apply, mul_assoc]⟩
  · refine iSup₂_le fun φ hφ => ?_
    refine le_iSup₂_of_le (φ * n⁻¹) (Y.mul_mem hφ (Y.inv_mem hn)) ?_
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨n * l * n⁻¹, ⟨l, hl, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem conjSet_facts {Y L H X : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) (hX : X ∈ conjSet L Y) :
    IsComponentOf X Y ∧ X ≤ H ∧ (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) := by
  obtain ⟨h1, -, -, -, -, -⟩ := h_facts hL hH
  have hXc : IsComponentOf X Y := by
    obtain ⟨n, hn, rfl⟩ := hX
    exact isComponentOf_map_conj_of_mem hL hn
  have hXH : X ≤ H := by
    rw [hH]
    exact le_iSup₂_of_le X hX le_rfl
  have hH' : H = ⨆ φ ∈ Y, X.map (MulAut.conj φ).toMonoidHom := by
    rw [iSup_conjSet_conj hX, h1]
  exact ⟨hXc, hXH, conj_mem_of_eq_biSup_conj hXc hH'⟩

end CFSG.LocalAnalysis.WeakClosure81
