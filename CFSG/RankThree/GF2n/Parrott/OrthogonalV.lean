module

public import CFSG.RankThree.GF2n.Parrott.QuadraticV

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

@[expose] def isometryGroup (h : Tim79a.ParrottHyp z) :
    Subgroup (MulAut (QuotientV.V z)) where
  carrier := {α | ∀ v, qVZMod h (α v) = qVZMod h v}
  one_mem' := by
    intro v
    simp
  mul_mem' := by
    intro α β hα hβ v
    simp only [Set.mem_setOf_eq] at hα hβ ⊢
    rw [MulAut.mul_apply, hα, hβ]
  inv_mem' := by
    intro α hα v
    calc qVZMod h (α⁻¹ v) = qVZMod h (α (α⁻¹ v)) := (hα (α⁻¹ v)).symm
      _ = qVZMod h v := by rw [MulAut.apply_inv_self]

@[simp] theorem mem_isometryGroup_iff (h : Tim79a.ParrottHyp z) (α : MulAut (QuotientV.V z)) :
    α ∈ isometryGroup h ↔ ∀ v, qVZMod h (α v) = qVZMod h v :=
  Iff.rfl

theorem conjV_mem_isometry (h : Tim79a.ParrottHyp z) (g : H z) :
    conjV h g ∈ isometryGroup h := by
  intro v
  exact qVZMod_conj h g v

@[expose] noncomputable def conjOrth (h : Tim79a.ParrottHyp z) :
    H z →* isometryGroup h :=
  (conjV h).codRestrict (isometryGroup h) (conjV_mem_isometry h)

@[simp] theorem conjOrth_apply_coe (h : Tim79a.ParrottHyp z) (g : H z) :
    ((conjOrth h g : isometryGroup h) : MulAut (QuotientV.V z)) = conjV h g :=
  rfl

@[expose] noncomputable def actionOrth (h : Tim79a.ParrottHyp z) :
    (↥(H z) ⧸ (J z).subgroupOf (H z)) →* isometryGroup h :=
  (actionA h).codRestrict (isometryGroup h) (by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective ((J z).subgroupOf (H z)) a
    rw [actionA_mk]
    exact conjV_mem_isometry h g)

@[simp] theorem actionOrth_apply_coe (h : Tim79a.ParrottHyp z)
    (a : ↥(H z) ⧸ (J z).subgroupOf (H z)) :
    ((actionOrth h a : isometryGroup h) : MulAut (QuotientV.V z)) = actionA h a :=
  rfl

@[simp] theorem actionOrth_mk (h : Tim79a.ParrottHyp z) (g : H z) :
    actionOrth h (QuotientGroup.mk' ((J z).subgroupOf (H z)) g) = conjOrth h g := by
  apply Subtype.ext
  rw [actionOrth_apply_coe, actionA_mk, conjOrth_apply_coe]

private theorem toAdd_eq_zero_iff {x : Multiplicative (ZMod 2)} :
    x.toAdd = 0 ↔ x = 1 :=
  Iff.rfl

@[simp] theorem qVZMod_one (h : Tim79a.ParrottHyp z) :
    qVZMod h (1 : QuotientV.V z) = 0 := by
  have hq : qV h (1 : QuotientV.V z) = 1 := by
    rw [show (1 : QuotientV.V z) = QuotientV.pi z 1 by simp]
    rw [qV_pi]
    apply Subtype.ext
    simp [qJ_coe]
  unfold qVZMod
  rw [hq, map_one]
  simp

theorem polarVZMod_self (h : Tim79a.ParrottHyp z) (v : QuotientV.V z) :
    polarVZMod h v v = 0 := by
  have hvv : v * v = 1 := by
    rw [← pow_two, QuotientV.pow_two_eq_one_V h v]
  have hmul := qVZMod_mul_add h v v
  rw [hvv, qVZMod_one] at hmul
  have h2 : qVZMod h v + qVZMod h v = 0 := by
    calc qVZMod h v + qVZMod h v = 2 * qVZMod h v := (two_mul _).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by exact ZMod.natCast_self 2, zero_mul]
  rw [h2, zero_add] at hmul
  exact hmul.symm

theorem polarVZMod_comm (h : Tim79a.ParrottHyp z) (v w : QuotientV.V z) :
    polarVZMod h v w = polarVZMod h w v := by
  unfold polarVZMod
  rw [polarV_comm h v w]

theorem polarVZMod_pi_eq_zero_iff (h : Tim79a.ParrottHyp z) (x y : J z) :
    polarVZMod h (QuotientV.pi z x) (QuotientV.pi z y) = 0 ↔
      Commute (x : G) (y : G) := by
  rw [polarVZMod, polarV_pi, toAdd_eq_zero_iff,
    (zpowersEquivZModTwo h).map_eq_one_iff]
  constructor
  · intro hxy
    have hval : ⁅(x : G), (y : G)⁆ = 1 := by
      simpa using Subtype.ext_iff.mp hxy
    exact commutatorElement_eq_one_iff_commute.mp hval
  · intro hxy
    apply Subtype.ext
    simpa using commutatorElement_eq_one_iff_commute.mpr hxy

theorem pi_mem_radical_iff (h : Tim79a.ParrottHyp z) (x : J z) :
    (∀ w : QuotientV.V z,
        polarVZMod h (QuotientV.pi z x) w = 0) ↔
      (x : G) ∈ Subgroup.centralizer (J z : Set G) := by
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
    intro y hy
    exact commutatorElement_eq_one_iff_commute.mpr
      ((polarVZMod_pi_eq_zero_iff h x ⟨y, hy⟩).mp (hx (QuotientV.pi z ⟨y, hy⟩)))
  · intro hx w
    obtain ⟨y, rfl⟩ := QuotientV.pi_surjective z w
    exact (polarVZMod_pi_eq_zero_iff h x y).mpr ((hx (y : G) y.2).symm)

theorem polarVZMod_nondegenerate (h : Tim79a.ParrottHyp z) (v : QuotientV.V z)
    (hv : ∀ w, polarVZMod h v w = 0) : v = 1 := by
  obtain ⟨x, rfl⟩ := QuotientV.pi_surjective z v
  have hxcent : (x : G) ∈ Subgroup.centralizer (J z : Set G) :=
    (pi_mem_radical_iff h x).mp hv
  have hxcenter : (x : G) ∈ centerIn (J z) := ⟨x.2, hxcent⟩
  have hker : x ∈ (QuotientV.pi z).ker := by
    rw [QuotientV.pi_ker]
    exact Subgroup.mem_subgroupOf.mpr hxcenter
  exact MonoidHom.mem_ker.mp hker

end CFSG.RankThree.GF2n.Parrott
