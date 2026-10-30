module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.SpFrame

private lemma exists_pow_eq_of_ne_one {p : ℕ} (hp : p.Prime)
    {a b : Multiplicative (ZMod p)} (ha : a ≠ 1) : ∃ c : ℕ, a ^ c = b := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hA : a.toAdd ≠ 0 := fun h => ha (toAdd_eq_zero.mp h)
  refine ⟨(b.toAdd / a.toAdd).val, ?_⟩
  apply (Multiplicative.toAdd).injective
  rw [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact div_mul_cancel₀ b.toAdd hA

private lemma mem_zpowers_of_supported {p N : ℕ} (hp : p.Prime)
    {u w : Fin N → Multiplicative (ZMod p)} (i0 : Fin N)
    (hu : ∀ i, i ≠ i0 → u i = 1) (hw : ∀ i, i ≠ i0 → w i = 1)
    (hui : u i0 ≠ 1) : w ∈ Subgroup.zpowers u := by
  obtain ⟨c, hc⟩ := exists_pow_eq_of_ne_one hp hui
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨(c : ℤ), ?_⟩
  rw [zpow_natCast]
  funext i
  rw [Pi.pow_apply]
  by_cases hi : i = i0
  · subst hi; exact hc
  · rw [hu i hi, hw i hi, one_pow]

private lemma exists_nontrivial_coord {p N : ℕ}
    {v : Fin N → Multiplicative (ZMod p)}
    (hv : ∀ i j, i ≠ j → v i = 1 ∨ v j = 1) (hv1 : v ≠ 1) :
    ∃ i0, v i0 ≠ 1 ∧ ∀ i, i ≠ i0 → v i = 1 := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 1 := by
    by_contra h
    push Not at h
    exact hv1 (funext fun i => h i)
  refine ⟨i0, hi0, fun i hi => ?_⟩
  rcases hv i i0 hi with h | h
  · exact h
  · exact absurd h hi0

theorem zpowers_eq_of_coords {p N : ℕ} (hp : p.Prime)
    {x y z : Fin N → Multiplicative (ZMod p)}
    (hx : ∀ i j, i ≠ j → x i = 1 ∨ x j = 1) (hy : ∀ i j, i ≠ j → y i = 1 ∨ y j = 1)
    (hz : ∀ i j, i ≠ j → z i = 1 ∨ z j = 1) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) (hzx : z ∉ Subgroup.zpowers x)
    (hzD : z ∈ Subgroup.closure ({x, y} : Set (Fin N → Multiplicative (ZMod p)))) :
    Subgroup.zpowers z = Subgroup.zpowers y := by
  have hy1 : y ≠ 1 := fun h => hyx (by rw [h]; exact Subgroup.one_mem _)
  have hz1 : z ≠ 1 := fun h => hzx (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨i0, hxi0, hxoff⟩ := exists_nontrivial_coord hx hx1
  obtain ⟨j0, hyj0, hyoff⟩ := exists_nontrivial_coord hy hy1
  obtain ⟨k0, hzk0, hzoff⟩ := exists_nontrivial_coord hz hz1
  have hji : j0 ≠ i0 := by
    intro h
    apply hyx
    refine mem_zpowers_of_supported hp i0 (u := x) (w := y) hxoff ?_ hxi0
    intro i hi
    exact hyoff i (fun hij => hi (hij.trans h))
  have hzS : ∀ i, i ≠ i0 → i ≠ j0 → z i = 1 := by
    let S : Subgroup (Fin N → Multiplicative (ZMod p)) :=
      { carrier := {w | ∀ i, i ≠ i0 → i ≠ j0 → w i = 1}
        one_mem' := by intro i _ _; rfl
        mul_mem' := by
          intro a b ha hb i hi hj
          rw [Pi.mul_apply, ha i hi hj, hb i hi hj, one_mul]
        inv_mem' := by
          intro a ha i hi hj
          rw [Pi.inv_apply, ha i hi hj, inv_one] }
    have hle : Subgroup.closure ({x, y} : Set (Fin N → Multiplicative (ZMod p))) ≤ S := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · intro i hi _; exact hxoff i hi
      · intro i _ hj; exact hyoff i hj
    exact hle hzD
  have hk : k0 = j0 := by
    rcases eq_or_ne k0 i0 with h | h
    · exfalso
      apply hzx
      refine mem_zpowers_of_supported hp i0 (u := x) (w := z) hxoff ?_ hxi0
      intro i hi
      exact hzoff i (fun hik => hi (hik.trans h))
    · rcases eq_or_ne k0 j0 with h2 | h2
      · exact h2
      · exact absurd (hzS k0 h h2) hzk0
  have hzoffj : ∀ i, i ≠ j0 → z i = 1 := by
    intro i hi
    exact hzoff i (fun hik => hi (hik.trans hk))
  have hzjy : z ∈ Subgroup.zpowers y :=
    mem_zpowers_of_supported hp j0 hyoff hzoffj hyj0
  have hyjz : y ∈ Subgroup.zpowers z :=
    mem_zpowers_of_supported hp j0 hzoffj hyoff (by rw [← hk]; exact hzk0)
  exact le_antisymm (Subgroup.zpowers_le.mpr hzjy) (Subgroup.zpowers_le.mpr hyjz)

end CFSG.StandardType.SpFrame
