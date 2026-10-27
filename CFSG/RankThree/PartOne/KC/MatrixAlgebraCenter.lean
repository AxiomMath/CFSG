module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.RankThree.PartOne

section ScalarCenter

variable {ι : Type*} (K : ι → Type*) [∀ i, Field (K i)] (m : ι → ℕ)

@[expose] def scalarPi : (∀ i, K i) →+* (∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) :=
  RingHom.pi fun i => (Matrix.scalar (Fin (m i))).comp (Pi.evalRingHom K i)

@[simp] theorem scalarPi_apply (c : ∀ i, K i) (i : ι) :
    scalarPi K m c i = Matrix.scalar (Fin (m i)) (c i) := rfl

theorem mem_center_iff_exists_scalarPi (x : ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) :
    x ∈ Subring.center (∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) ↔ ∃ c, scalarPi K m c = x := by
  rw [← SetLike.mem_coe, Subring.coe_center, Set.center_pi]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Matrix.center_eq_range, Set.mem_range]
  constructor
  · intro h
    choose c hc using h
    exact ⟨c, funext fun i => hc i⟩
  · rintro ⟨c, rfl⟩ i
    exact ⟨c i, rfl⟩

theorem scalarPi_injective (hm : ∀ i, 0 < m i) : Function.Injective (scalarPi K m) := by
  intro c d h
  funext i
  have := congrFun (congrFun (congrFun h i) ⟨0, hm i⟩) ⟨0, hm i⟩
  simpa using this

@[expose] noncomputable def scalarCenterEquiv (hm : ∀ i, 0 < m i) :
    (∀ i, K i) ≃+* Subring.center (∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) :=
  RingEquiv.ofBijective
    ((scalarPi K m).codRestrict _ fun c => (mem_center_iff_exists_scalarPi K m _).2 ⟨c, rfl⟩)
    ⟨fun _ _ h => scalarPi_injective K m hm (congrArg Subtype.val h), fun z =>
      let ⟨c, hc⟩ := (mem_center_iff_exists_scalarPi K m z.1).1 z.2
      ⟨c, Subtype.ext hc⟩⟩

@[simp] theorem coe_scalarCenterEquiv (hm : ∀ i, 0 < m i) (c : ∀ i, K i) :
    ((scalarCenterEquiv K m hm c : Subring.center (∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i))) :
      ∀ i, Matrix (Fin (m i)) (Fin (m i)) (K i)) = scalarPi K m c := rfl

end ScalarCenter

section InducedActions

variable {R : Type*} [Ring R]

@[expose] def centerRingAut : RingAut R →* RingAut (Subring.center R) where
  toFun σ := Subring.centerCongr σ
  map_one' := RingEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := RingEquiv.ext fun _ => Subtype.ext rfl

@[simp] theorem coe_centerRingAut (σ : RingAut R) (z : Subring.center R) :
    ((centerRingAut σ z : Subring.center R) : R) = σ (z : R) := rfl

@[expose] def centerUnitsAut (σ : RingAut R) : MulAut (Subring.center R)ˣ :=
  Units.mapEquiv (centerRingAut σ).toMulEquiv

@[simp] theorem coe_coe_centerUnitsAut (σ : RingAut R) (x : (Subring.center R)ˣ) :
    (((centerUnitsAut σ x : (Subring.center R)ˣ) : Subring.center R) : R) = σ (x : R) := rfl

end InducedActions

section Quotient

variable {G : Type*} [CommGroup G]

@[expose] def quotientInduced (g : MulAut G) (U C : Subgroup G) (hU : ∀ x ∈ U, g x ∈ U)
    (hC : ∀ x ∈ C, g x ∈ C) : U ⧸ C.subgroupOf U →* U ⧸ C.subgroupOf U :=
  QuotientGroup.map _ _ (MonoidHom.mk' (fun x : U => (⟨g x, hU x x.2⟩ : U)) (fun a b => by
    ext; simp)) (fun x hx => hC x hx)

@[simp] theorem quotientInduced_mk (g : MulAut G) (U C : Subgroup G) (hU : ∀ x ∈ U, g x ∈ U)
    (hC : ∀ x ∈ C, g x ∈ C) (x : U) :
    quotientInduced g U C hU hC (QuotientGroup.mk x) = QuotientGroup.mk ⟨g x, hU x x.2⟩ := rfl

end Quotient

end CFSG.RankThree.PartOne
