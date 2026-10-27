module

public import CFSG.LocalAnalysis.UniquenessCase.UC6M591R

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem map_pPrimeCore_normalizerMonoidHom (y : ↥(normalizer (m.L : Set G))) :
    (CFSG.pPrimeCore m.r ↥m.L).map (Subgroup.normalizerMonoidHom m.L y).toMonoidHom =
      CFSG.pPrimeCore m.r ↥m.L :=
  Subgroup.characteristic_iff_map_eq.1 inferInstance _

@[expose] noncomputable def actLbar : ↥(normalizer (m.L : Set G)) →* MulAut m.Lbar where
  toFun y := QuotientGroup.congr (CFSG.pPrimeCore m.r ↥m.L) (CFSG.pPrimeCore m.r ↥m.L)
    (Subgroup.normalizerMonoidHom m.L y) (m.map_pPrimeCore_normalizerMonoidHom y)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      show QuotientGroup.mk (Subgroup.normalizerMonoidHom m.L 1 l) = QuotientGroup.mk l
      rw [map_one]
      rfl
  map_mul' y z := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      show QuotientGroup.mk (Subgroup.normalizerMonoidHom m.L (y * z) l) =
        QuotientGroup.mk (Subgroup.normalizerMonoidHom m.L y (Subgroup.normalizerMonoidHom m.L z l))
      rw [map_mul]
      rfl

theorem actLbar_mk (y : ↥(normalizer (m.L : Set G))) (l : ↥m.L) :
    m.actLbar y (QuotientGroup.mk l) = QuotientGroup.mk (Subgroup.normalizerMonoidHom m.L y l) :=
  rfl

theorem mem_OL_iff (l : ↥m.L) : (l : G) ∈ m.OL ↔ l ∈ CFSG.pPrimeCore m.r ↥m.L :=
  Subgroup.mem_map_iff_mem m.L.subtype_injective (x := l)

theorem mk_eq_iff (a b : ↥m.L) :
    (QuotientGroup.mk a : m.Lbar) = QuotientGroup.mk b ↔ (a : G)⁻¹ * (b : G) ∈ m.OL := by
  rw [QuotientGroup.eq, ← m.mem_OL_iff]
  rfl

theorem actLbar_fix_iff (y : ↥(normalizer (m.L : Set G))) (e : ↥m.L) :
    m.actLbar y (QuotientGroup.mk e) = QuotientGroup.mk e ↔
      (y : G) * (e : G) * (y : G)⁻¹ * (e : G)⁻¹ ∈ m.OL := by
  rw [actLbar_mk, mk_eq_iff]
  have hval : ((Subgroup.normalizerMonoidHom m.L y e : ↥m.L) : G) = (y : G) * (e : G) * (y : G)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe m.L y e
  rw [hval]
  have heq : ((y : G) * (e : G) * (y : G)⁻¹)⁻¹ * (e : G) =
      ((e : G)⁻¹ * ((y : G) * (e : G) * (y : G)⁻¹ * (e : G)⁻¹) * (e : G))⁻¹ := by group
  rw [heq, m.OL.inv_mem_iff]
  have hn := mem_normalizer_iff.1 (m.L_le_normalizer_OL (inv_mem e.2))
    ((y : G) * (e : G) * (y : G)⁻¹ * (e : G)⁻¹)
  simp only [inv_inv] at hn
  exact hn.symm

theorem actLbar_eq_one_iff (y : ↥(normalizer (m.L : Set G))) :
    m.actLbar y = 1 ↔ (y : G) ∈ m.KerL := by
  constructor
  · intro h
    refine m.mem_CenL.2 ⟨y.2, fun s hs => ?_⟩
    have := (m.actLbar_fix_iff y ⟨s, hs⟩).1 (by rw [h]; rfl)
    exact this
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H l =>
      exact (m.actLbar_fix_iff y l).2 ((m.mem_CenL.1 h).2 l l.2)

theorem actLbar_of_mem_L (e : ↥m.L) :
    m.actLbar ⟨(e : G), Subgroup.le_normalizer e.2⟩ = MulAut.conj (QuotientGroup.mk e : m.Lbar) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H l =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      m.actLbar_mk]
    congr 1

theorem orderOf_actLbar_dvd (y : ↥(normalizer (m.L : Set G))) :
    orderOf (m.actLbar y) ∣ orderOf (y : G) := by
  rw [Subgroup.orderOf_coe]
  exact orderOf_map_dvd m.actLbar y

noncomputable def Ebar : Subgroup m.Lbar :=
  (m.EL.subgroupOf m.L).map (QuotientGroup.mk' (CFSG.pPrimeCore m.r ↥m.L))

theorem mem_Ebar_iff {x : m.Lbar} :
    x ∈ m.Ebar ↔ ∃ e : ↥m.L, (e : G) ∈ m.EL ∧ (QuotientGroup.mk e : m.Lbar) = x := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, rfl⟩

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
