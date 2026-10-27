module

public import CFSG.Quasithin.EmptyFaithful.SBc15WDefs

public section

namespace CFSG.Quasithin

namespace SBc15

namespace F5

section Embedding

variable {D : Type} [Group D]

theorem left_mul_of_right_eq_one {Q : Type} [Group Q] {a b : D ≀ᵣ Q} (ha : a.right = 1) :
    (a * b).left = a.left * b.left := by
  funext z
  simp [RegularWreathProduct.mul_left, ha]

theorem mem_wrPerf {D' : Subgroup D} {x : D ≀ᵣ Multiplicative (ZMod 2)} :
    x ∈ wrPerf D' ↔ x.right = 1 ∧ ∀ i, x.left i ∈ D' := Iff.rfl

@[expose] def z2gen : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

theorem z2gen_ne_one : z2gen ≠ 1 := by decide

theorem eq_one_or_z2gen (i : Multiplicative (ZMod 2)) : i = 1 ∨ i = z2gen := by
  revert i
  decide

variable (D) in
@[expose] def wrEmb : D × D →* D ≀ᵣ Multiplicative (ZMod 2) where
  toFun p := ⟨fun i => if i = 1 then p.1 else p.2, 1⟩
  map_one' := by
    refine RegularWreathProduct.ext (funext fun i => ?_) rfl
    by_cases hi : i = 1 <;> simp [hi]
  map_mul' p q := by
    refine RegularWreathProduct.ext ?_ (by simp)
    rw [left_mul_of_right_eq_one rfl]
    funext i
    by_cases hi : i = 1 <;> simp [hi]

theorem wrEmb_left (p : D × D) (i : Multiplicative (ZMod 2)) :
    (wrEmb D p).left i = if i = 1 then p.1 else p.2 := rfl

theorem wrEmb_injective : Function.Injective (wrEmb D) := by
  intro p q h
  have h1 := congrArg (fun w : D ≀ᵣ Multiplicative (ZMod 2) => w.left 1) h
  have h2 := congrArg (fun w : D ≀ᵣ Multiplicative (ZMod 2) => w.left z2gen) h
  simp [wrEmb_left, z2gen_ne_one] at h1 h2
  exact Prod.ext h1 h2

theorem wrPerf_eq_map (D' : Subgroup D) : wrPerf D' = (D'.prod D').map (wrEmb D) := by
  ext w
  constructor
  · intro hw
    obtain ⟨hw1, hw2⟩ := mem_wrPerf.mp hw
    refine ⟨(w.left 1, w.left z2gen), Subgroup.mem_prod.mpr ⟨hw2 _, hw2 _⟩, ?_⟩
    refine RegularWreathProduct.ext (funext fun i => ?_) hw1.symm
    rcases eq_one_or_z2gen i with rfl | rfl
    · simp [wrEmb_left]
    · simp [wrEmb_left, z2gen_ne_one]
  · rintro ⟨p, hp, rfl⟩
    refine mem_wrPerf.mpr ⟨rfl, fun i => ?_⟩
    rw [wrEmb_left]
    split_ifs
    · exact (Subgroup.mem_prod.mp hp).1
    · exact (Subgroup.mem_prod.mp hp).2

theorem comap_wrEmb_le {D' : Subgroup D} {Y : Subgroup (D ≀ᵣ Multiplicative (ZMod 2))}
    (hY : Y ≤ wrPerf D') : Y.comap (wrEmb D) ≤ D'.prod D' := by
  intro p hp
  have : wrEmb D p ∈ wrPerf D' := hY hp
  rw [wrPerf_eq_map] at this
  obtain ⟨z, hz, hzp⟩ := this
  rwa [← wrEmb_injective hzp]

theorem map_comap_wrEmb {D' : Subgroup D} {Y : Subgroup (D ≀ᵣ Multiplicative (ZMod 2))}
    (hY : Y ≤ wrPerf D') : (Y.comap (wrEmb D)).map (wrEmb D) = Y := by
  refine Subgroup.map_comap_eq_self (hY.trans ?_)
  rw [wrPerf_eq_map]
  exact Subgroup.map_le_range _ _

theorem wrPerf_normal {D' : Subgroup D} (hD' : D'.Normal) : (wrPerf D').Normal where
  conj_mem n hn g := by
    obtain ⟨hn1, hn2⟩ := mem_wrPerf.mp hn
    refine mem_wrPerf.mpr ⟨by simp [hn1], fun i => ?_⟩
    have key : (g * n * g⁻¹).left i = g.left i * n.left (g.right⁻¹ * i) * (g.left i)⁻¹ := by
      simp only [RegularWreathProduct.mul_left, RegularWreathProduct.inv_left,
        RegularWreathProduct.mul_right, hn1, Pi.mul_apply, Pi.inv_apply, mul_one,
        mul_inv_cancel_left]
      rfl
    rw [key]
    exact hD'.conj_mem _ (hn2 _) _

end Embedding

section Counting

theorem card_wr {D : Type} [Group D] (hD : Nat.card D = 120) :
    Nat.card (D ≀ᵣ Multiplicative (ZMod 2)) = 28800 := by
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [RegularWreathProduct.card, hD, h2]
  norm_num

end Counting

end F5

end SBc15

end CFSG.Quasithin
