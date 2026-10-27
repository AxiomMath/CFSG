module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Odd

variable {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal]

theorem mem_center_iff_mem_centerOf (c : ↥L) : c ∈ Subgroup.center ↥L ↔ (c : G) ∈ centerOf L := by
  rw [mem_centerOf, Subgroup.mem_center_iff]
  constructor
  · intro hc
    exact ⟨c.2, fun y hy => congrArg Subtype.val (hc ⟨y, hy⟩)⟩
  · rintro ⟨-, hc⟩ g
    exact Subtype.ext (hc g g.2)

@[expose] def actEquiv (g : G) : ↥L ⧸ Subgroup.center ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (MulAut.conjNormal (H := L) g)
    (Subgroup.characteristic_iff_map_eq.1 inferInstance _)

theorem actEquiv_mk (g : G) (y : ↥L) :
    actEquiv L g (QuotientGroup.mk y) = QuotientGroup.mk (MulAut.conjNormal (H := L) g y) := rfl

@[expose] def actHom : G →* MulAut (↥L ⧸ Subgroup.center ↥L) where
  toFun := actEquiv L
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => simp [actEquiv_mk]
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y => simp [actEquiv_mk, map_mul]

theorem actHom_apply_mk (g : G) (y : ↥L) :
    actHom L g (QuotientGroup.mk y) = QuotientGroup.mk (MulAut.conjNormal (H := L) g y) := rfl

theorem actHom_mk_eq_iff (g : G) {y : G} (hy : y ∈ L) :
    actHom L g (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ ↔
      g * y * g⁻¹ * y⁻¹ ∈ centerOf L := by
  rw [actHom_apply_mk, QuotientGroup.eq, mem_center_iff_mem_centerOf]
  have h1 : (((MulAut.conjNormal (H := L) g ⟨y, hy⟩)⁻¹ * ⟨y, hy⟩ : ↥L) : G) =
      (g * y * g⁻¹)⁻¹ * y := by
    simp [MulAut.conjNormal_apply]
  rw [h1]
  have key : g * y * g⁻¹ * y⁻¹ = y * ((g * y * g⁻¹)⁻¹ * y)⁻¹ * y⁻¹ := by group
  constructor
  · intro hc
    rw [key]
    exact conj_mem_centerOf L ((centerOf L).inv_mem hc) y
  · intro hc
    have h3 := conj_mem_centerOf L hc y⁻¹
    have h4 : y⁻¹ * (g * y * g⁻¹ * y⁻¹) * y⁻¹⁻¹ = ((g * y * g⁻¹)⁻¹ * y)⁻¹ := by group
    rw [h4] at h3
    simpa using (centerOf L).inv_mem h3

theorem centralizes_of_forall_comm_mem (hL : commutator ↥L = ⊤) {g : G}
    (hg : ∀ y ∈ L, g * y * g⁻¹ * y⁻¹ ∈ centerOf L) : ∀ y ∈ L, g * y = y * g := by
  let δ : ↥L →* G :=
    { toFun := fun y => g * (y : G) * g⁻¹ * (y : G)⁻¹
      map_one' := by simp
      map_mul' := fun y y' => by
        simpa only [Subgroup.coe_mul] using comm_mul L (e := g) y.2 (hg y' y'.2) }
  have hker : commutator ↥L ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_centerOf.1 (hg b b.2)).2 _ (comm_mem L a.2)
  intro y hy
  have h1 : δ ⟨y, hy⟩ = 1 := hker (by rw [hL]; exact Subgroup.mem_top _)
  change g * y * g⁻¹ * y⁻¹ = 1 at h1
  calc g * y = (g * y * g⁻¹ * y⁻¹) * y * g := by group
    _ = y * g := by rw [h1, one_mul]

theorem comm_central_mul_left {H : Type*} [Group H] {c : H} (hc : c ∈ Subgroup.center H) (x y : H) :
    (c * x) * y * (c * x)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have h := Subgroup.mem_center_iff.1 hc
  calc (c * x) * y * (c * x)⁻¹ * y⁻¹ = (c * (x * y * x⁻¹)) * c⁻¹ * y⁻¹ := by group
    _ = ((x * y * x⁻¹) * c) * c⁻¹ * y⁻¹ := by rw [← h (x * y * x⁻¹)]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_central_mul_right {H : Type*} [Group H] {c : H} (hc : c ∈ Subgroup.center H) (x y : H) :
    x * (c * y) * x⁻¹ * (c * y)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have h := Subgroup.mem_center_iff.1 hc
  calc x * (c * y) * x⁻¹ * (c * y)⁻¹ = (x * c) * y * x⁻¹ * y⁻¹ * c⁻¹ := by group
    _ = (c * x) * y * x⁻¹ * y⁻¹ * c⁻¹ := by rw [h x]
    _ = (c * (x * y * x⁻¹ * y⁻¹)) * c⁻¹ := by group
    _ = ((x * y * x⁻¹ * y⁻¹) * c) * c⁻¹ := by rw [← h (x * y * x⁻¹ * y⁻¹)]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem le_of_mul_centerOf {M : Subgroup G} (hL : commutator ↥L = ⊤)
    (hgen : ∀ y ∈ L, ∃ m ∈ M ⊓ L, ∃ z ∈ centerOf L, y = m * z) : L ≤ M := by
  have hcl : commutator ↥L ≤ (M.subgroupOf L) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨m₁, hm₁, z₁, hz₁, h₁⟩ := hgen a a.2
    obtain ⟨m₂, hm₂, z₂, hz₂, h₂⟩ := hgen b b.2
    have ha : a = (⟨z₁, centerOf_le L hz₁⟩ : ↥L) * ⟨m₁, hm₁.2⟩ := by
      apply Subtype.ext
      change (a : G) = z₁ * m₁
      rw [h₁]
      exact (mem_centerOf.1 hz₁).2 m₁ hm₁.2
    have hb : b = (⟨z₂, centerOf_le L hz₂⟩ : ↥L) * ⟨m₂, hm₂.2⟩ := by
      apply Subtype.ext
      change (b : G) = z₂ * m₂
      rw [h₂]
      exact (mem_centerOf.1 hz₂).2 m₂ hm₂.2
    have hz₁' : (⟨z₁, centerOf_le L hz₁⟩ : ↥L) ∈ Subgroup.center ↥L :=
      (mem_center_iff_mem_centerOf L _).2 hz₁
    have hz₂' : (⟨z₂, centerOf_le L hz₂⟩ : ↥L) ∈ Subgroup.center ↥L :=
      (mem_center_iff_mem_centerOf L _).2 hz₂
    have hc : a * b * a⁻¹ * b⁻¹ = (⟨m₁, hm₁.2⟩ : ↥L) * ⟨m₂, hm₂.2⟩ * (⟨m₁, hm₁.2⟩ : ↥L)⁻¹ *
        (⟨m₂, hm₂.2⟩ : ↥L)⁻¹ := by
      rw [ha, hb, comm_central_mul_left hz₁', comm_central_mul_right hz₂']
    rw [commutatorElement_def, hc, Subgroup.mem_subgroupOf]
    exact M.mul_mem (M.mul_mem (M.mul_mem hm₁.1 hm₂.1) (M.inv_mem hm₁.1)) (M.inv_mem hm₂.1)
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥L) ∈ commutator ↥L := by rw [hL]; exact Subgroup.mem_top _
  exact hcl hmem

end Odd

end CFSG.LocalAnalysis.UniquenessCase.UCK
