module


import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem conj_mem_Q_of_mem_H (S : Setting z E F) {h x : G} (hh : h ∈ H z) (hx : x ∈ Q z) :
    h * x * h⁻¹ ∈ Q z := by
  have := (instNormalQH z).conj_mem ⟨x, Q_le_H S hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨h, hh⟩
  exact Subgroup.mem_subgroupOf.mp this

@[expose] noncomputable def XsubPre (S : Setting z E F) (a : G) : Subgroup ↥(H z) :=
  (Xsub S a).comap (QuotientGroup.mk' ((Q z).subgroupOf (H z)))

theorem mem_XsubPre_iff (S : Setting z E F) (a : G) {x : ↥(H z)} :
    x ∈ XsubPre S a ↔ (QuotientGroup.mk x : Hbar z) ∈ Xsub S a := Iff.rfl

@[expose] noncomputable def XsubHat (S : Setting z E F) (a : G) : Subgroup G :=
  (XsubPre S a).map (H z).subtype

theorem mem_XsubHat_iff (S : Setting z E F) (a : G) {x : G} :
    x ∈ XsubHat S a ↔
      ∃ hx : x ∈ H z, (QuotientGroup.mk (⟨x, hx⟩ : ↥(H z)) : Hbar z) ∈ Xsub S a := by
  unfold XsubHat
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hmem⟩
    exact ⟨⟨x, hx⟩, hmem, rfl⟩

theorem XsubHat_le_H (S : Setting z E F) (a : G) : XsubHat S a ≤ H z := fun _ hx =>
  ((mem_XsubHat_iff S a).mp hx).1

theorem Q_le_XsubHat (S : Setting z E F) (a : G) : Q z ≤ XsubHat S a := by
  intro x hx
  refine (mem_XsubHat_iff S a).mpr ⟨Q_le_H S hx, ?_⟩
  have h1 : (QuotientGroup.mk (⟨x, Q_le_H S hx⟩ : ↥(H z)) : Hbar z) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hx)
  rw [h1]
  exact (Xsub S a).one_mem

@[expose] noncomputable def toXsub (S : Setting z E F) (a : G) :
    ↥(XsubPre S a) →* ↥(Xsub S a) :=
  ((QuotientGroup.mk' ((Q z).subgroupOf (H z))).comp (XsubPre S a).subtype).codRestrict
    (Xsub S a) (fun g => g.2)

theorem toXsub_surjective (S : Setting z E F) (a : G) : Function.Surjective (toXsub S a) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨⟨x, hy⟩, rfl⟩

theorem toXsub_eq_one_iff (S : Setting z E F) (a : G) (g : ↥(XsubPre S a)) :
    toXsub S a g = 1 ↔ ((g : ↥(H z)) : G) ∈ Q z := by
  have h1 : toXsub S a g = 1 ↔ (QuotientGroup.mk (g : ↥(H z)) : Hbar z) = 1 := by
    rw [← Subtype.coe_inj]
    rfl
  rw [h1, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem conj_mem_XsubHat (S : Setting z E F) (a : G) {h x : G} (hh : h ∈ H z)
    (hx : x ∈ XsubHat S a) : h * x * h⁻¹ ∈ XsubHat S a := by
  obtain ⟨hxH, hxX⟩ := (mem_XsubHat_iff S a).mp hx
  have hconjH : h * x * h⁻¹ ∈ H z := (H z).mul_mem ((H z).mul_mem hh hxH) ((H z).inv_mem hh)
  refine (mem_XsubHat_iff S a).mpr ⟨hconjH, ?_⟩
  haveI := Xsub_normal S a
  have h1 : (QuotientGroup.mk (⟨h * x * h⁻¹, hconjH⟩ : ↥(H z)) : Hbar z) =
      (QuotientGroup.mk (⟨h, hh⟩ : ↥(H z)) : Hbar z) * QuotientGroup.mk (⟨x, hxH⟩ : ↥(H z)) *
        (QuotientGroup.mk (⟨h, hh⟩ : ↥(H z)) : Hbar z)⁻¹ := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  rw [h1]
  exact (Xsub_normal S a).conj_mem _ hxX _

@[expose] noncomputable def FsubH (S : Setting z E F) (a : G) : Subgroup G :=
  ⁅Q z, XsubHat S a⁆

theorem FsubH_le_Q (S : Setting z E F) (a : G) : FsubH S a ≤ Q z := by
  rw [FsubH, Subgroup.commutator_le]
  intro q hq x hx
  have h1 : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h1]
  exact (Q z).mul_mem hq (conj_mem_Q_of_mem_H S (XsubHat_le_H S a hx) ((Q z).inv_mem hq))

theorem z_mem_FsubH (S : Setting z E F) (a : G) : z ∈ FsubH S a := by
  have h1 : ⁅Q z, Q z⁆ ≤ FsubH S a := Subgroup.commutator_mono le_rfl (Q_le_XsubHat S a)
  rw [Q_deriv_eq S] at h1
  exact h1 (Subgroup.mem_zpowers z)

theorem conj_mem_FsubH (S : Setting z E F) (a : G) {h f : G} (hh : h ∈ H z)
    (hf : f ∈ FsubH S a) : h * f * h⁻¹ ∈ FsubH S a := by
  unfold FsubH at hf ⊢
  rw [Subgroup.commutator_def] at hf ⊢
  induction hf using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨q, hq, x, hx, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨h * q * h⁻¹, conj_mem_Q_of_mem_H S hh hq,
      h * x * h⁻¹, conj_mem_XsubHat S a hh hx, ?_⟩
    simp only [commutatorElement_def]
    group
  | one => simp
  | mul x y _ _ ihx ihy =>
    have e : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ihx =>
    have e : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ihx

end CFSG.RankThree.GF2n.Stroth78
