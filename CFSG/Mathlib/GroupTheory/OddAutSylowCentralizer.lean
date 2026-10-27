module

public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace CFSG.OddAutSylowCentralizer

theorem exists_mem_conj_eq {G : Type*} [Group G] {J Y : Subgroup G}
    (hinn : ∀ α : MulAut ↥J, ∀ m : ℕ, Odd m → α ^ m = 1 → ∃ k : ↥J, α = MulAut.conj k)
    (hZ : ∀ x ∈ J, (∀ y ∈ J, x * y = y * x) → x = 1) (hYJ : Y ≤ J) (hY : IsPGroup 3 Y)
    (hYmax : ∀ P : Subgroup G, P ≤ J → IsPGroup 3 P → Y ≤ P → P = Y) {t : G} (ht : t ^ 3 = 1)
    (htJ : ∀ x ∈ J, t * x * t⁻¹ ∈ J) (htY : ∀ y ∈ Y, t * y = y * t) :
    ∃ y ∈ Y, ∀ x ∈ J, t * x * t⁻¹ = y * x * y⁻¹ := by
  let f : ↥J → ↥J := fun x => ⟨t * (x : G) * t⁻¹, htJ x x.2⟩
  have hf3 : ∀ x : ↥J, f (f (f x)) = x := by
    intro x
    apply Subtype.ext
    change t * (t * (t * (x : G) * t⁻¹) * t⁻¹) * t⁻¹ = (x : G)
    calc
      t * (t * (t * (x : G) * t⁻¹) * t⁻¹) * t⁻¹
          = (t * t * t) * ((x : G) * (t⁻¹ * t⁻¹ * t⁻¹)) := by
              simp only [mul_assoc]
      _ = (x : G) := by
              have ht3 : t * t * t = 1 := by simpa only [pow_three'] using ht
              have htinv3 : t⁻¹ * t⁻¹ * t⁻¹ = 1 := by
                simpa only [pow_three'] using
                  (show (t⁻¹) ^ 3 = 1 by rw [inv_pow, ht, inv_one])
              rw [ht3, htinv3]
              simp
  let α : MulAut ↥J :=
    { toFun := f
      invFun := fun x => f (f x)
      left_inv := hf3
      right_inv := hf3
      map_mul' := by
        intro x y
        apply Subtype.ext
        change t * ((x : G) * (y : G)) * t⁻¹ =
          (t * (x : G) * t⁻¹) * (t * (y : G) * t⁻¹)
        group }
  have hα3 : α ^ 3 = 1 := by
    ext x
    rw [pow_three', MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply]
    exact congrArg Subtype.val (hf3 x)
  obtain ⟨k, hk⟩ := hinn α 3 (by decide : Odd 3) hα3
  have hkY : ∀ y ∈ Y, (k : G) * y = y * (k : G) := by
    intro y hy
    have hyJ : y ∈ J := hYJ hy
    have hαy : α ⟨y, hyJ⟩ = ⟨y, hyJ⟩ := by
      change f ⟨y, hyJ⟩ = ⟨y, hyJ⟩
      apply Subtype.ext
      change t * y * t⁻¹ = y
      rw [htY y hy, mul_assoc, mul_inv_cancel, mul_one]
    have hconjy : MulAut.conj k ⟨y, hyJ⟩ = ⟨y, hyJ⟩ := by
      rw [← hk]
      exact hαy
    have hky : k * ⟨y, hyJ⟩ * k⁻¹ = ⟨y, hyJ⟩ := by
      simpa only [MulAut.conj_apply] using hconjy
    have hky' : k * ⟨y, hyJ⟩ = ⟨y, hyJ⟩ * k := by
      calc
        k * ⟨y, hyJ⟩ = (k * ⟨y, hyJ⟩ * k⁻¹) * k := by group
        _ = ⟨y, hyJ⟩ * k := by rw [hky]
    simpa using congrArg Subtype.val hky'
  have hconj3 : MulAut.conj (k ^ 3) = 1 := by
    calc
      MulAut.conj (k ^ 3) = (MulAut.conj k) ^ 3 := by rw [map_pow]
      _ = α ^ 3 := by rw [← hk]
      _ = 1 := hα3
  have hk3central : ∀ x ∈ J, ((k ^ 3 : ↥J) : G) * x = x * ((k ^ 3 : ↥J) : G) := by
    intro x hx
    have hx' : MulAut.conj (k ^ 3) ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [hconj3]
      rfl
    have hco : ((k ^ 3 : ↥J) : G) * x * (((k ^ 3 : ↥J) : G))⁻¹ = x := by
      have h := congrArg Subtype.val hx'
      rw [MulAut.conj_apply] at h
      simpa using h
    calc
      ((k ^ 3 : ↥J) : G) * x
          = (((k ^ 3 : ↥J) : G) * x * (((k ^ 3 : ↥J) : G))⁻¹) *
              ((k ^ 3 : ↥J) : G) := by group
      _ = x * ((k ^ 3 : ↥J) : G) := by rw [hco]
  have hk3 : k ^ 3 = 1 := by
    apply Subtype.ext
    exact hZ _ (k ^ 3).2 hk3central
  have hk3G : (k : G) ^ 3 = 1 := by
    simpa using congrArg Subtype.val hk3
  have hkord : orderOf (k : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hk3G
  have hzk : IsPGroup 3 (Subgroup.zpowers (k : G)) := by
    intro x
    refine ⟨1, ?_⟩
    have hx3G : (x : G) ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      exact (orderOf_dvd_of_mem_zpowers x.2).trans hkord
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hx3G
    simpa [pow_one] using hx3
  have hYcentral : Y ≤ Subgroup.centralizer (Subgroup.zpowers (k : G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hyk : Commute y (k : G) := (hkY y hy).symm
    simpa [hm] using (hyk.zpow_right m).eq.symm
  have hYle : Y ≤ Subgroup.normalizer (Subgroup.zpowers (k : G)) :=
    hYcentral.trans (Subgroup.centralizer_le_normalizer _)
  have hP3 : IsPGroup 3 ↥(Y ⊔ Subgroup.zpowers (k : G)) :=
    IsPGroup.to_sup_of_normal_right' hY hzk hYle
  have hPJ : Y ⊔ Subgroup.zpowers (k : G) ≤ J :=
    sup_le hYJ (Subgroup.zpowers_le.mpr k.2)
  have hP_eq : Y ⊔ Subgroup.zpowers (k : G) = Y :=
    hYmax _ hPJ hP3 le_sup_left
  have hkYmem : (k : G) ∈ Y := by
    rw [← hP_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (k : G))
  refine ⟨(k : G), hkYmem, ?_⟩
  intro x hx
  have hαx : α ⟨x, hx⟩ = MulAut.conj k ⟨x, hx⟩ := by rw [hk]
  have hval := congrArg Subtype.val hαx
  simpa [α, f, MulAut.conj_apply] using hval

end CFSG.OddAutSylowCentralizer

end
