module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenVocab
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IQ

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Quasithin.E2P.Asc80
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
open Matrix
open scoped MatrixGroups

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_leviC_not_mem_centralizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ g ∈ leviC p, ∀ s ∈ leviY p,
      s⁻¹ * g ∉ Subgroup.centralizer (leviY p : Set (PSL3 p)) := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by
    rw [ZMod.ringChar_zmod_n]
    exact hp2)
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  let ν : (ZMod p)ˣ := Units.mk0 a ha0
  have hν : ¬ IsSquare (ν : ZMod p) := by simpa [ν] using ha
  let A : GL (Fin 2) (ZMod p) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(ν : ZMod p), 0; 0, 1] (by
      rw [Matrix.det_fin_two]
      simp [ν.ne_zero])
  refine ⟨leviPsi p A, ?_, ?_⟩
  · rw [← leviPsi_range]
    exact MonoidHom.mem_range.mpr ⟨A, rfl⟩
  · intro s hs hmem
    obtain ⟨S, hS⟩ := hs
    obtain ⟨u, hu⟩ := mem_centralizer_leviY hp2 hmem
    have hS' : leviPsi p (Matrix.SpecialLinearGroup.toGL S) = s := by
      rw [← ofSL2_eq_leviPsi]
      exact hS
    have hg : leviPsi p A = leviPsi p (Matrix.SpecialLinearGroup.toGL S *
        Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
      calc leviPsi p A = s * (s⁻¹ * leviPsi p A) := by group
        _ = leviPsi p (Matrix.SpecialLinearGroup.toGL S) *
              leviPsi p (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
            rw [hS', hu]
        _ = leviPsi p (Matrix.SpecialLinearGroup.toGL S *
              Matrix.GeneralLinearGroup.scalar (Fin 2) u) := (map_mul _ _ _).symm
    have hprod : leviPsi p (A * (Matrix.SpecialLinearGroup.toGL S *
        Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹) = 1 := by
      rw [map_mul, map_inv, hg, mul_inv_cancel]
    obtain ⟨μ, -, hμ⟩ := leviPsi_eq_one_iff.mp hprod
    have hAeq : A = Matrix.GeneralLinearGroup.scalar (Fin 2) μ *
        (Matrix.SpecialLinearGroup.toGL S *
          Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
      rw [← hμ, mul_assoc, inv_mul_cancel, mul_one]
    have hdet := congrArg (fun X : GL (Fin 2) (ZMod p) =>
      ((Matrix.GeneralLinearGroup.det X : (ZMod p)ˣ) : ZMod p)) hAeq
    have hνA : ((Matrix.GeneralLinearGroup.det A : (ZMod p)ˣ) : ZMod p) = (ν : ZMod p) := by
      simp [A, Matrix.det_fin_two]
    rw [hνA] at hdet
    simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar,
      Matrix.SpecialLinearGroup.coeToGL_det, Fintype.card_fin, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_one] at hdet
    exact hν ⟨(μ : ZMod p) * (u : ZMod p), by rw [hdet]; ring⟩

omit [Finite Q] in
theorem exists_leviData_psl3 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {L : Subgroup Q} [L.Normal]
    (e : ↥L ≃* PSL3 p) {y : Q} (hyL : y ∈ L) (hy2 : orderOf y = 2) :
    ∃ Y : Subgroup Q, LeviData L p y Y := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e', he'⟩ := exists_equiv_zc hp2 e hyL hy2
  set f : PSL3 p →* Q := L.subtype.comp e'.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp e'.symm.injective
  have hfz : f (zc p) = y := by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he', MulEquiv.symm_apply_apply]
    rfl
  have hfL : ∀ c, f c ∈ L := fun c => (e'.symm c).2
  have hfe : ∀ (x : Q) (hx : x ∈ L), f (e' ⟨x, hx⟩) = x := fun x hx => by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hcomm_f : ∀ (x : Q) (hx : x ∈ L) (c : PSL3 p),
      x * f c = f c * x ↔ e' ⟨x, hx⟩ * c = c * e' ⟨x, hx⟩ := by
    intro x hx c
    constructor
    · intro h
      apply hfinj
      rw [map_mul, map_mul, hfe x hx]
      exact h
    · intro h
      have h1 := congrArg f h
      rwa [map_mul, map_mul, hfe x hx] at h1
  have hCL : L ⊓ Subgroup.centralizer ({y} : Set Q) = (leviC p).map f :=
    inf_centralizer_eq_map_leviC hp2 e' hyL he'
  set Y : Subgroup Q := (leviY p).map f with hY
  have hYcomm : Y = ⁅L ⊓ Subgroup.centralizer ({y} : Set Q),
      L ⊓ Subgroup.centralizer ({y} : Set Q)⁆ := by
    rw [hCL, ← Subgroup.map_commutator, commutator_leviC hp5]
  have hYC0 : Y ≤ L ⊓ Subgroup.centralizer ({y} : Set Q) := by
    rw [hCL]
    exact Subgroup.map_mono leviY_le_leviC
  have hCY : L ⊓ Subgroup.centralizer (Y : Set Q) =
      (Subgroup.centralizer (leviY p : Set (PSL3 p))).map f := by
    ext x
    constructor
    · rintro ⟨hxL, hxY⟩
      refine ⟨e' ⟨x, hxL⟩, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_, hfe x hxL⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxY (f s) ⟨s, hs, rfl⟩
      exact ((hcomm_f x hxL s).mp h1.symm).symm
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hfL c, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc s hs]
  refine ⟨Y, hYcomm, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨zc p, zc_mem_leviY, hfz⟩
  ·
    intro n hn
    rw [hYcomm]
    refine mem_normalizer_commutator ?_
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hgy : ∀ m ∈ Subgroup.centralizer ({y} : Set Q), ∀ g ∈
        L ⊓ Subgroup.centralizer ({y} : Set Q), m * g * m⁻¹ ∈
          L ⊓ Subgroup.centralizer ({y} : Set Q) := by
      rintro m hm g ⟨hgL, hgy⟩
      exact ⟨(inferInstance : L.Normal).conj_mem g hgL m,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hgy) (Subgroup.inv_mem _ hm)⟩
    refine ⟨hgy n hn g, fun h => ?_⟩
    have := hgy n⁻¹ (Subgroup.inv_mem _ hn) _ h
    simpa [mul_assoc] using this
  ·
    have hrange : Y = (f.comp (ofSL2 p)).range := by
      rw [hY, MonoidHom.range_comp]
      rfl
    have hinj : Function.Injective (f.comp (ofSL2 p)) := hfinj.comp (ofSL2_injective (p := p))
    exact ⟨(MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hinj).symm⟩
  ·
    intro c hc hc2
    obtain ⟨hcL, hcY⟩ := hc
    have hcC : e' ⟨c, hcL⟩ ∈ Subgroup.centralizer (leviY p : Set (PSL3 p)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h1 := Subgroup.mem_centralizer_iff.mp hcY (f s) ⟨s, hs, rfl⟩
      exact ((hcomm_f c hcL s).mp h1.symm).symm
    have hc2' : orderOf (e' ⟨c, hcL⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hc2]
    rw [← hfe c hcL, eq_zc_of_mem_centralizer_leviY hp2 hcC hc2', hfz]
  ·
    obtain ⟨g₀, hg₀C, hg₀not⟩ := exists_leviC_not_mem_centralizer hp2
    refine ⟨f g₀, ⟨hfL g₀, ?_⟩, ?_⟩
    · have h := congrArg f (zc_comm_levi hg₀C)
      rw [map_mul, map_mul, hfz] at h
      exact Subgroup.mem_centralizer_singleton_iff.mpr h.symm
    · intro s hs
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      intro hmem
      have hmemL : (f s₀)⁻¹ * f g₀ ∈ L := L.mul_mem (L.inv_mem (hfL s₀)) (hfL g₀)
      have hmem' : (f s₀)⁻¹ * f g₀ ∈ L ⊓ Subgroup.centralizer (Y : Set Q) :=
        ⟨hmemL, hmem⟩
      rw [hCY] at hmem'
      obtain ⟨c₀, hc₀, hc₀eq⟩ := hmem'
      have heq : s₀⁻¹ * g₀ = c₀ := by
        apply hfinj
        rw [map_mul, map_inv, hc₀eq]
      rw [← heq] at hc₀
      exact hg₀not s₀ hs₀ hc₀

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
