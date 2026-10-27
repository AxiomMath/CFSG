module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45PairSpPlane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
variable {B : LinearMap.BilinForm (ZMod 2) W}

@[expose] def commSp (a : W ≃ₗ[ZMod 2] W) : Submodule (ZMod 2) W :=
  LinearMap.range ((a : W →ₗ[ZMod 2] W) - LinearMap.id)

structure OrdThree (B : LinearMap.BilinForm (ZMod 2) W) (a : W ≃ₗ[ZMod 2] W) : Prop where
  isom : ∀ x y, B (a x) (a y) = B x y
  ord : orderOf a = 3
  rank : Module.finrank (ZMod 2) (commSp a) = 2

structure PairHyp (B : LinearMap.BilinForm (ZMod 2) W) (a b : W ≃ₗ[ZMod 2] W) : Prop where
  nondeg : B.Nondegenerate
  alt : B.IsAlt
  ha : OrdThree B a
  hb : OrdThree B b

variable {a : W ≃ₗ[ZMod 2] W}

theorem mem_commSp_iff {x : W} : x ∈ commSp a ↔ ∃ y, a y - y = x := by
  simp [commSp]

theorem sub_mem_commSp (a : W ≃ₗ[ZMod 2] W) (y : W) : a y - y ∈ commSp a :=
  mem_commSp_iff.mpr ⟨y, rfl⟩

theorem OrdThree.pow_three (ha : OrdThree B a) : a ^ 3 = 1 := by
  rw [← ha.ord]; exact pow_orderOf_eq_one a

theorem OrdThree.apply_cube (ha : OrdThree B a) (x : W) : a (a (a x)) = x := by
  have h := congrArg (fun f : W ≃ₗ[ZMod 2] W => f x) ha.pow_three
  simpa [pow_succ] using h

theorem apply_mem_commSp {x : W} (hx : x ∈ commSp a) : a x ∈ commSp a := by
  obtain ⟨y, rfl⟩ := mem_commSp_iff.mp hx
  exact mem_commSp_iff.mpr ⟨a y, by simp⟩

theorem fixed_iff_mem_orth (hB : B.Nondegenerate) (hiso : ∀ x y, B (a x) (a y) = B x y) (v : W) :
    a v = v ↔ v ∈ B.orthogonal (commSp a) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hv n hn
    obtain ⟨y, rfl⟩ := mem_commSp_iff.mp hn
    have h := hiso y v
    rw [hv] at h
    rw [map_sub, LinearMap.sub_apply, h, sub_self]
  · intro hv
    refine sub_eq_zero.mp (hB.2 (a v - v) fun w => ?_)
    have hmem : w - a.symm w ∈ commSp a := by
      rw [mem_commSp_iff]
      exact ⟨a.symm w, by simp⟩
    have hw : B (w - a.symm w) v = 0 := hv _ hmem
    have hwv : B w v = B (a.symm w) v := by
      have h : B w v - B (a.symm w) v = 0 := by simpa [map_sub] using hw
      exact sub_eq_zero.mp h
    have hisov : B w (a v) = B (a.symm w) v := by
      have h := hiso (a.symm w) v
      simpa using h
    rw [map_sub, hisov, hwv, sub_self]

theorem sq_add_add_one (ha : OrdThree B a) {x : W} (hx : x ∈ commSp a) :
    a (a x) + a x + x = 0 := by
  obtain ⟨y, rfl⟩ := mem_commSp_iff.mp hx
  have h3 := ha.apply_cube y
  simp only [map_sub]
  rw [h3]
  abel

theorem apply_sq_of_mem (ha : OrdThree B a) {x : W} (hx : x ∈ commSp a) :
    a (a x) = x + a x := by
  have h := sq_add_add_one ha hx
  rw [add_assoc] at h
  rw [eq_neg_of_add_eq_zero_left h, neg_eq_self', add_comm]

theorem isCompl_commSp_orth (hB : B.Nondegenerate) (ha : OrdThree B a) :
    IsCompl (commSp a) (B.orthogonal (commSp a)) := by
  constructor
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxO⟩ := Submodule.mem_inf.mp hx
    have hfix : a x = x := (fixed_iff_mem_orth hB ha.isom x).mpr hxO
    have h := sq_add_add_one ha hxP
    rw [hfix, hfix, add_self_eq_zero', zero_add] at h
    exact h
  · rw [codisjoint_iff, eq_top_iff]
    intro w _
    have hfix : a (w - (a (a w) - a w)) = w - (a (a w) - a w) := by
      have h := add_self_eq_zero' (a (a w) - w)
      have h' : a (w - (a (a w) - a w)) - (w - (a (a w) - a w)) =
          (a (a w) - w) + (a (a w) - w) := by
        simp only [map_sub, ha.apply_cube]
        abel
      exact sub_eq_zero.mp (h'.trans h)
    exact Submodule.mem_sup.mpr ⟨a (a w) - a w, sub_mem_commSp a (a w), w - (a (a w) - a w),
      (fixed_iff_mem_orth hB ha.isom _).mp hfix, by abel⟩

theorem commSp_inf_orth (hB : B.Nondegenerate) (ha : OrdThree B a) :
    commSp a ⊓ B.orthogonal (commSp a) = ⊥ :=
  (isCompl_commSp_orth hB ha).inf_eq_bot

theorem apply_ne_of_mem (hB : B.Nondegenerate) (ha : OrdThree B a) {x : W} (hx : x ∈ commSp a)
    (hx0 : x ≠ 0) : a x ≠ x := by
  intro h
  have hmem : x ∈ commSp a ⊓ B.orthogonal (commSp a) :=
    Submodule.mem_inf.mpr ⟨hx, (fixed_iff_mem_orth hB ha.isom x).mp h⟩
  rw [commSp_inf_orth hB ha, Submodule.mem_bot] at hmem
  exact hx0 hmem

theorem apply_ne_zero {x : W} (hx0 : x ≠ 0) : a x ≠ 0 := fun h =>
  hx0 (a.injective (by rw [h, map_zero]))

theorem commSp_cases (hB : B.Nondegenerate) (ha : OrdThree B a) {p : W} (hp : p ∈ commSp a)
    (hp0 : p ≠ 0) : ∀ x ∈ commSp a, x = 0 ∨ x = p ∨ x = a p ∨ x = a (a p) := by
  intro x hx
  rcases plane_mem_cases ha.rank hp (apply_mem_commSp hp) hp0 (apply_ne_zero hp0)
      (apply_ne_of_mem hB ha hp hp0) x hx with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, apply_sq_of_mem ha hp])))

theorem bil_self_apply (hB : B.Nondegenerate) (hAlt : B.IsAlt) (ha : OrdThree B a) {p : W}
    (hp : p ∈ commSp a) (hp0 : p ≠ 0) : B p (a p) = 1 :=
  plane_pairing_one hAlt ha.rank (commSp_inf_orth hB ha) hp (apply_mem_commSp hp) hp0
    (apply_ne_zero hp0) (apply_ne_of_mem hB ha hp hp0).symm

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
