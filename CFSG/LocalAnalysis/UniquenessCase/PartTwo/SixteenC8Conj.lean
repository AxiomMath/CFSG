module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem c8_exists_conj_of_isSylowOf {M T T' : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' M) :
    ∃ g ∈ M, ∀ x : G, x ∈ T ↔ g⁻¹ * x * g ∈ T' := by
  obtain ⟨Q, rfl⟩ := hT'
  obtain ⟨Q', rfl⟩ := hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M Q Q'
  have key : ∀ y : M, y ∈ (Q' : Subgroup M) ↔ g⁻¹ * y * g ∈ (Q : Subgroup M) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup M) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (key y).mp hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : (z : G) = (g : G)⁻¹ * x * g := hzx
    have hx : x = (g : G) * z * (g : G)⁻¹ := by rw [hzx']; group
    have hxK : x ∈ M := by
      rw [hx]
      exact M.mul_mem (M.mul_mem g.2 z.2) (M.inv_mem g.2)
    refine ⟨⟨x, hxK⟩, (key _).mpr ?_, rfl⟩
    have : g⁻¹ * ⟨x, hxK⟩ * g = z := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hzx'.symm)
    rw [this]
    exact hz

private theorem actTil_conj {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {g t : G}
    (hgs : g ∈ stabTil V₀ V) (ht : t ∈ stabTil V₀ V)
    (hgtil : g⁻¹ * t * g ∈ stabTil V₀ V) :
    actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩ =
      (actTil V₀ V hV ⟨g, hgs⟩)⁻¹ * actTil V₀ V hV ⟨t, ht⟩ *
        actTil V₀ V hV ⟨g, hgs⟩ := by
  have h : (⟨g⁻¹ * t * g, hgtil⟩ : ↥(stabTil V₀ V)) =
      (⟨g, hgs⟩ : ↥(stabTil V₀ V))⁻¹ * ⟨t, ht⟩ * ⟨g, hgs⟩ := Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv]

theorem c8_star_sylowT (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hMs : D.M ≤ stabTil V₀ V) (hM : Mbar D.M V₀ V hV = lBar V₀ V hV L)
    (h : C8Star D V₀ V L hV) :
    ∃ ψ : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 (ZMod 2)),
      barSub V₀ V hV D.T ≤ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) ∧
        ∀ t ∈ D.T, t ^ 2 = 1 → ∀ ht : t ∈ stabTil V₀ V,
          actTil V₀ V hV ⟨t, ht⟩ ∈ pullSub ψ (tauSym 3).range := by
  obtain ⟨T', ψ, hT', hTP, hTR⟩ := h
  obtain ⟨g, hgM, hg⟩ := c8_exists_conj_of_isSylowOf D.sylowM hT'
  have hgs : g ∈ stabTil V₀ V := hMs hgM
  have hTle : D.T ≤ D.M := D.sylowM.le
  have hbarTle : barSub V₀ V hV T' ≤ lBar V₀ V hV L :=
    hTP.trans (pullSub_le ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)))
  have hgbarM : actTil V₀ V hV ⟨g, hgs⟩ ∈ Mbar D.M V₀ V hV :=
    actTil_mem_barSub V₀ V hV hgM hgs
  have hgbarL : actTil V₀ V hV ⟨g, hgs⟩ ∈ lBar V₀ V hV L := by
    rw [← hM]
    exact hgbarM
  let g' : ↥(lBar V₀ V hV L) := ⟨actTil V₀ V hV ⟨g, hgs⟩, hgbarL⟩
  let ψ' : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 (ZMod 2)) := (MulAut.conj g').symm.trans ψ
  have key : ∀ (t : G) (ht : t ∈ stabTil V₀ V)
      (hmem : actTil V₀ V hV ⟨t, ht⟩ ∈ lBar V₀ V hV L)
      (hgtil : g⁻¹ * t * g ∈ stabTil V₀ V)
      (hmem2 : actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩ ∈ lBar V₀ V hV L),
      ψ' ⟨actTil V₀ V hV ⟨t, ht⟩, hmem⟩ =
        ψ ⟨actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩, hmem2⟩ := by
    intro t ht hmem hgtil hmem2
    have hX : g'⁻¹ * (⟨actTil V₀ V hV ⟨t, ht⟩, hmem⟩ : ↥(lBar V₀ V hV L)) * g' =
        ⟨actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩, hmem2⟩ := by
      apply Subtype.ext
      show (actTil V₀ V hV ⟨g, hgs⟩)⁻¹ * actTil V₀ V hV ⟨t, ht⟩ *
          actTil V₀ V hV ⟨g, hgs⟩ = actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩
      exact (actTil_conj hV hgs ht hgtil).symm
    rw [show ψ' = (MulAut.conj g').symm.trans ψ from rfl, MulEquiv.trans_apply,
      MulAut.conj_symm_apply, hX]
  refine ⟨ψ', ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hsT, rfl⟩ := (mem_barSub V₀ V hV D.T x).1 hx
    obtain ⟨t, ht⟩ := s
    have hmem : actTil V₀ V hV ⟨t, ht⟩ ∈ lBar V₀ V hV L := by
      rw [← hM]
      exact actTil_mem_barSub V₀ V hV (hTle hsT) ht
    have hgtil : g⁻¹ * t * g ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem
        ((stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem hgs) ht) hgs
    have hmem2 : actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩ ∈ lBar V₀ V hV L :=
      hbarTle (actTil_mem_barSub V₀ V hV ((hg t).mp hsT) hgtil)
    refine (mem_pullSub (φ := ψ')
      (P := stabilizer 3 (ZMod 2) (lagrangianZero 3))).2 ⟨hmem, ?_⟩
    rw [key t ht hmem hgtil hmem2]
    obtain ⟨h', h'P⟩ := (mem_pullSub (φ := ψ)
      (P := stabilizer 3 (ZMod 2) (lagrangianZero 3))).1
        (hTP (actTil_mem_barSub V₀ V hV ((hg t).mp hsT) hgtil))
    have heq : (⟨actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩, hmem2⟩ :
        ↥(lBar V₀ V hV L)) =
        ⟨actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩, h'⟩ := Subtype.ext rfl
    rw [heq]
    exact h'P
  · intro t htT ht2 ht
    have hmem : actTil V₀ V hV ⟨t, ht⟩ ∈ lBar V₀ V hV L := by
      rw [← hM]
      exact actTil_mem_barSub V₀ V hV (hTle htT) ht
    have hgtil : g⁻¹ * t * g ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem
        ((stabTil V₀ V).mul_mem ((stabTil V₀ V).inv_mem hgs) ht) hgs
    have hmem2 : actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩ ∈ lBar V₀ V hV L :=
      hbarTle (actTil_mem_barSub V₀ V hV ((hg t).mp htT) hgtil)
    have hgt2 : (g⁻¹ * t * g) ^ 2 = 1 := by
      have h1 : (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g := by
        rw [show g⁻¹ * t * g = g⁻¹ * t * (g⁻¹)⁻¹ from by rw [inv_inv], conj_pow, inv_inv]
      rw [h1, ht2]
      simp
    refine (mem_pullSub (φ := ψ') (P := (tauSym 3).range)).2 ⟨hmem, ?_⟩
    rw [key t ht hmem hgtil hmem2]
    obtain ⟨h', h'P⟩ := (mem_pullSub (φ := ψ) (P := (tauSym 3).range)).1
      (hTR (g⁻¹ * t * g) ((hg t).mp htT) hgt2 hgtil)
    have heq : (⟨actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩, hmem2⟩ :
        ↥(lBar V₀ V hV L)) =
        ⟨actTil V₀ V hV ⟨g⁻¹ * t * g, hgtil⟩, h'⟩ := Subtype.ext rfl
    rw [heq]
    exact h'P

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
