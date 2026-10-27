module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IT
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IQ

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  Module CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin.A38c15
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_inf_centralizer_le (hp2 : p ≠ 2) {L : Subgroup G} [L.Normal]
    (e' : ↥L ≃* PSL3 p) {y : G} (hyL : y ∈ L) (hy2 : orderOf y = 2)
    (he' : e' ⟨y, hyL⟩ = zc p) :
    Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({y} : Set G) := by
  intro n hn
  set f : PSL3 p →* G := L.subtype.comp e'.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp e'.symm.injective
  have hfz : f (zc p) = y := by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he', MulEquiv.symm_apply_apply]
    rfl
  have hCL := inf_centralizer_eq_map_leviC hp2 e' hyL he'
  have hyC : y ∈ L ⊓ Subgroup.centralizer ({y} : Set G) :=
    ⟨hyL, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have h1 : n * y * n⁻¹ ∈ L ⊓ Subgroup.centralizer ({y} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hn y).mp hyC
  have hcen : ∀ w ∈ L ⊓ Subgroup.centralizer ({y} : Set G),
      n * y * n⁻¹ * w = w * (n * y * n⁻¹) := by
    intro w hw
    have hw' : n⁻¹ * w * n ∈ L ⊓ Subgroup.centralizer ({y} : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) w).mp hw
      simpa using this
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp hw'.2
    calc n * y * n⁻¹ * w = n * (y * (n⁻¹ * w * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * w * n) * y) * n⁻¹ := by rw [← h2]
      _ = w * (n * y * n⁻¹) := by group
  rw [hCL] at h1
  obtain ⟨c, hc, hcy⟩ := h1
  have hc' : c ∈ Subgroup.centralizer (leviY p : Set (PSL3 p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h3 := hcen (f s) (by rw [hCL]; exact ⟨s, leviY_le_leviC hs, rfl⟩)
    rw [← hcy, ← map_mul, ← map_mul] at h3
    exact (hfinj h3).symm
  have hconj : orderOf (n * y * n⁻¹) = orderOf y :=
    orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective y
  have hc2 : orderOf c = 2 := by
    rw [← orderOf_injective f hfinj c, hcy, hconj, hy2]
  have hcz := eq_zc_of_mem_centralizer_leviY hp2 hc' hc2
  have hny : n * y * n⁻¹ = y := by rw [← hcy, hcz, hfz]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * y = (n * y * n⁻¹) * n := by group
    _ = y * n := by rw [hny]

theorem finrank_lineE3 : finrank (ZMod p) (lineE3 p) = 1 :=
  finrank_span_singleton (by simp)

theorem isCoatom_centralizer_L3 (hirr : SL3OddIrr) (hp2 : p ≠ 2)
    {L : Subgroup G} (hAS : SecE3.AlmostSimple L) (e : ↥L ≃* PSL3 p) (hGL : ∃ t : G, t ∉ L)
    {y : G} (hyL : y ∈ L) (hy2 : orderOf y = 2) :
    IsCoatom (Subgroup.centralizer ({y} : Set G)) := by
  have := hAS.normal
  obtain ⟨e', he'⟩ := exists_equiv_zc hp2 e hyL hy2
  set f : PSL3 p →* G := L.subtype.comp e'.symm.toMonoidHom with hf
  have hfz : f (zc p) = y := by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he', MulEquiv.symm_apply_apply]
    rfl
  have hfe : ∀ (x : G) (hx : x ∈ L), f (e' ⟨x, hx⟩) = x := fun x hx => by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hfr : f.range = L := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact (e'.symm c).2
    · intro hx
      exact ⟨e' ⟨x, hx⟩, hfe x hx⟩
  have hCL := inf_centralizer_eq_map_leviC hp2 e' hyL he'
  set C := Subgroup.centralizer ({y} : Set G) with hC
  have hy1 : y ≠ 1 := by
    rintro rfl
    simp at hy2
  have hLC : ∀ g : G, ∃ l ∈ L, l * g ∈ C := by
    intro g
    have hgy : g * y * g⁻¹ ∈ L := hAS.normal.conj_mem y hyL g
    have h2 : orderOf (e' ⟨g * y * g⁻¹, hgy⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y).trans hy2
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_zc hp2 h2)
    refine ⟨f c, (e'.symm c).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h3 := congrArg f hc
    rw [map_mul, map_mul, map_inv, hfe, hfz] at h3
    calc f c * g * y = (f c * (g * y * g⁻¹) * (f c)⁻¹) * (f c * g) := by group
      _ = y * (f c * g) := by rw [h3]
  obtain ⟨t₀, ht₀⟩ := hGL
  obtain ⟨l₀, hl₀, hl₀C⟩ := hLC t₀
  have htL : l₀ * t₀ ∉ L := fun h => ht₀ (by
    have := L.mul_mem (L.inv_mem hl₀) h
    simpa using this)
  refine ⟨fun htop => hy1 ?_, fun Y hY => ?_⟩
  ·
    have hyc : y ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l _
      have hl : l ∈ C := htop ▸ Subgroup.mem_top l
      exact Subgroup.mem_centralizer_singleton_iff.mp hl
    rw [hAS.centralizer_eq] at hyc
    exact Subgroup.mem_bot.mp hyc
  set M := (L ⊓ Y).comap f with hM
  have hBM : leviC p ≤ M := fun c hc => by
    have h1 : f c ∈ L ⊓ C := by
      rw [hCL]
      exact ⟨c, hc, rfl⟩
    exact ⟨h1.1, hY.le h1.2⟩
  have hMmap : M.map f = L ⊓ Y := by
    rw [hM, Subgroup.map_comap_eq, hfr, ← inf_assoc, inf_idem]
  have hYN : Y ≤ Subgroup.normalizer ((L ⊓ Y : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨hhL, hhY⟩
      exact ⟨hAS.normal.conj_mem h hhL g, Y.mul_mem (Y.mul_mem hg hhY) (Y.inv_mem hg)⟩
    · rintro ⟨hhL, hhY⟩
      refine ⟨?_, ?_⟩
      · have := hAS.normal.conj_mem _ hhL g⁻¹
        simpa [mul_assoc] using this
      · have := Y.mul_mem (Y.mul_mem (Y.inv_mem hg) hhY) hg
        simpa [mul_assoc] using this
  by_cases hMtop : M = ⊤
  ·
    have hLY : L ≤ Y := fun l hl => by
      have h1 : e' ⟨l, hl⟩ ∈ M := hMtop ▸ Subgroup.mem_top _
      have h2 := h1.2
      rwa [hfe] at h2
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨l, hl, hlg⟩ := hLC g
    have hg : g = l⁻¹ * (l * g) := by group
    rw [hg]
    exact Y.mul_mem (Y.inv_mem (hLY hl)) (hY.le hlg)
  exfalso
  have hcaseB : M = leviC p → False := fun h => by
    have hLY : L ⊓ Y = L ⊓ C := by rw [← hMmap, h, hCL]
    have hYC : Y ≤ C := fun g hg =>
      normalizer_inf_centralizer_le hp2 e' hyL hy2 he' (by rw [← hLY]; exact hYN hg)
    exact hY.ne (le_antisymm hY.le hYC)
  have hcaseP : ∀ (P₀ : Subgroup (PSL3 p)) (W : Submodule (ZMod p) (Fin 3 → ZMod p)),
      (finrank (ZMod p) W = 1 ∨ finrank (ZMod p) W = 2) →
      P₀.map (psl3EquivP p).toMonoidHom = projStabilizer W → M = P₀ → False := by
    intro P₀ W hW hP₀ hMP
    refine not_mem_normalizer_projStabilizer hAS e' hW hP₀ htL ?_
    rw [← hMP, hMmap]
    exact hYN (hY.le hl₀C)
  rcases le_parabolics_of_le_levi hirr hp2 hBM hMtop with hle | hle
  · rcases eq_levi_or_eq_lineC hBM hle with h | h
    · exact hcaseB h
    · exact hcaseP (lineC p) (lineE3 p) (Or.inl finrank_lineE3) map_lineC_eq h
  · rcases eq_levi_or_eq_planeC hBM hle with h | h
    · exact hcaseB h
    · refine hcaseP (planeC p) (dotOrth (lineE3 p)) (Or.inr ?_) map_planeC_eq h
      rw [finrank_dotOrth, finrank_lineE3]

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
