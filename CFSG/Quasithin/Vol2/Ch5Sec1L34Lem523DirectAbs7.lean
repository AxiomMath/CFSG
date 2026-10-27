module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs1

public section

namespace CFSG.Quasithin.H13.Abs523

variable {E : Type} [CommGroup E] [Finite E]

@[expose] def stabY (Y₀ Y₁ : Subgroup E) : Subgroup (MulAut E) where
  carrier := {g | (∀ y, y ∈ Y₁ ↔ g y ∈ Y₁) ∧ (∀ y, y ∈ Y₀ ↔ g y ∈ Y₀)}
  mul_mem' := fun {a b} ha hb =>
    ⟨fun y => by
      rw [MulAut.mul_apply]
      exact (hb.1 y).trans (ha.1 (b y)),
     fun y => by
      rw [MulAut.mul_apply]
      exact (hb.2 y).trans (ha.2 (b y))⟩
  one_mem' := ⟨fun y => Iff.rfl, fun y => Iff.rfl⟩
  inv_mem' := fun {a} ha =>
    ⟨fun y => by
      have h := ha.1 (a⁻¹ y)
      rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at h
      exact h.symm,
     fun y => by
      have h := ha.2 (a⁻¹ y)
      rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at h
      exact h.symm⟩

abbrev Qt (Y₀ : Subgroup E) : Type := E ⧸ Y₀

@[expose] def Vq (Y₀ Y₁ : Subgroup E) : Subgroup (Qt Y₀) := Y₁.map (QuotientGroup.mk' Y₀)

abbrev Vsec (Y₀ Y₁ : Subgroup E) : Type := ↥(Vq Y₀ Y₁)

theorem mem_Vq {Y₀ Y₁ : Subgroup E} {q : Qt Y₀} : q ∈ Vq Y₀ Y₁ ↔ ∃ y ∈ Y₁, (y : Qt Y₀) = q := by
  unfold Vq
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem Vsec_sq (Y₀ Y₁ : Subgroup E) (hE2 : ∀ x : E, x ^ 2 = 1) (x : Vsec Y₀ Y₁) :
    x ^ 2 = 1 := by
  obtain ⟨q, hq⟩ := x
  obtain ⟨y, -, rfl⟩ := mem_Vq.mp hq
  apply Subtype.ext
  show ((y : E) : Qt Y₀) ^ 2 = 1
  rw [← QuotientGroup.mk_pow, hE2 y]
  rfl

theorem mk_eq_one_of_mem {Y₀ : Subgroup E} {x : E} (hx : x ∈ Y₀) : (x : Qt Y₀) = 1 :=
  (QuotientGroup.eq_one_iff x).mpr hx

@[expose] def gQ {Y₀ Y₁ : Subgroup E} (g : MulAut E) (hg : g ∈ stabY Y₀ Y₁) :
    Qt Y₀ ≃* Qt Y₀ :=
  QuotientGroup.congr Y₀ Y₀ g (by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hg.2 y).mp hy
    · intro hx
      have hgx : g (g.symm x) = x := MulEquiv.apply_symm_apply g x
      refine ⟨g.symm x, (hg.2 (g.symm x)).mpr (by rw [hgx]; exact hx), hgx⟩)

theorem gQ_mk {Y₀ Y₁ : Subgroup E} {g : MulAut E} {hg : g ∈ stabY Y₀ Y₁} (x : E) :
    gQ g hg (x : Qt Y₀) = ((g x : E) : Qt Y₀) := by
  unfold gQ
  rw [QuotientGroup.congr_mk]

theorem map_Vq_eq {Y₀ Y₁ : Subgroup E} {g : MulAut E} (hg : g ∈ stabY Y₀ Y₁) :
    (Vq Y₀ Y₁).map (gQ g hg : Qt Y₀ →* Qt Y₀) = Vq Y₀ Y₁ := by
  ext q
  rw [Subgroup.mem_map, mem_Vq]
  constructor
  · rintro ⟨q', hq', rfl⟩
    obtain ⟨y, hy, rfl⟩ := mem_Vq.mp hq'
    refine ⟨g y, (hg.1 y).mp hy, ?_⟩
    show gQ g hg ((y : E) : Qt Y₀) = _
    rw [gQ_mk]
    rfl
  · rintro ⟨y, hy, rfl⟩
    have hgx : g (g.symm y) = y := MulEquiv.apply_symm_apply g y
    refine ⟨((g.symm y : E) : Qt Y₀), mem_Vq.mpr ⟨g.symm y, (hg.1 (g.symm y)).mpr (by rw [hgx]; exact hy), rfl⟩, ?_⟩
    show gQ g hg ((g.symm y : E) : Qt Y₀) = _
    rw [gQ_mk, hgx]

@[expose] def gV {Y₀ Y₁ : Subgroup E} (g : MulAut E) (hg : g ∈ stabY Y₀ Y₁) :
    Vsec Y₀ Y₁ ≃* Vsec Y₀ Y₁ :=
  (MulEquiv.subgroupMap (gQ g hg) (Vq Y₀ Y₁)).trans (MulEquiv.subgroupCongr (map_Vq_eq hg))

theorem gV_coe {Y₀ Y₁ : Subgroup E} {g : MulAut E} (hg : g ∈ stabY Y₀ Y₁) (x : Vsec Y₀ Y₁) :
    ((gV g hg x : Vsec Y₀ Y₁) : Qt Y₀) = gQ g hg (x : Qt Y₀) := rfl

theorem exists_mk_of_Vsec {Y₀ Y₁ : Subgroup E} (x : Vsec Y₀ Y₁) :
    ∃ y ∈ Y₁, ((y : E) : Qt Y₀) = (x : Qt Y₀) :=
  mem_Vq.mp x.2

@[expose] def secHom (Y₀ Y₁ : Subgroup E) : stabY Y₀ Y₁ →* MulAut (Vsec Y₀ Y₁) where
  toFun g := gV g.1 g.2
  map_one' := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy, hyx⟩ := exists_mk_of_Vsec x
    show ((gV _ _ x : Vsec Y₀ Y₁) : Qt Y₀) = ((x : Vsec Y₀ Y₁) : Qt Y₀)
    rw [gV_coe, ← hyx, gQ_mk]
    rfl
  map_mul' := fun g h => by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy, hyx⟩ := exists_mk_of_Vsec x
    show ((gV _ _ x : Vsec Y₀ Y₁) : Qt Y₀) = ((gV _ _ (gV _ _ x) : Vsec Y₀ Y₁) : Qt Y₀)
    rw [gV_coe, gV_coe, gV_coe, ← hyx, gQ_mk, gQ_mk, gQ_mk]
    rfl

end CFSG.Quasithin.H13.Abs523
