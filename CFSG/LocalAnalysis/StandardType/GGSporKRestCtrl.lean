module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

variable {K : Type} [Group K]

theorem SporKRestControlsAt.mem_self [Finite K] {p : ℕ} (hp : p.Prime) {x : K} {Y : Subgroup K}
    (hx : x ^ p = 1) (hS : ∃ S : Sylow p K, (S : Subgroup K) ≤ Y) (hY : SporKRestControlsAt x Y) :
    x ∈ Y := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSY⟩ := hS
  have hP : IsPGroup p (Subgroup.zpowers x) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hx))
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K Q S
  have hxQ : x ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers x)
  have hcx : c * x * c⁻¹ ∈ (S : Subgroup K) := by
    have hm : c * x * c⁻¹ ∈ ((c • Q : Sylow p K) : Set K) := by
      rw [Sylow.coe_smul]
      exact Set.mem_smul_set.2 ⟨x, hxQ, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hc] at hm
    exact hm
  have hc' : c⁻¹ ∈ Y := hY c⁻¹ (by rw [inv_inv]; exact hSY hcx)
  have hcx' : c * x * c⁻¹ ∈ Y := hSY hcx
  have hxe : x = c⁻¹ * (c * x * c⁻¹) * c := by group
  rw [hxe]
  exact Y.mul_mem (Y.mul_mem hc' hcx') (by simpa using Y.inv_mem hc')

theorem SporKRestControlsAt.mem_of_comm {x c : K} {Y : Subgroup K} (hY : SporKRestControlsAt x Y)
    (hx : x ∈ Y) (hc : c * x = x * c) : c ∈ Y :=
  hY c (by rwa [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul])

theorem SporKRestControlsAt.mem_of_conj {x y h g : K} {Y : Subgroup K}
    (hY : SporKRestControlsAt x Y) (hh : h ∈ Y) (hy : x * h = h * y) (hg : g⁻¹ * y * g ∈ Y) :
    g ∈ Y := by
  have hyx : y = h⁻¹ * x * h := by rw [mul_assoc, hy, ← mul_assoc, inv_mul_cancel, one_mul]
  have hhg : h * g ∈ Y := hY (h * g) (by rw [hyx] at hg; simpa [mul_assoc] using hg)
  have hge : g = h⁻¹ * (h * g) := by group
  rw [hge]
  exact Y.mul_mem (Y.inv_mem hh) hhg

theorem sporKRest_generating_of_ctrl [Finite K] {p : ℕ} (hp : p.Prime) (a b : K)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {x y h : K} (hx : x ^ p = 1)
    (hxb : x * b = b * x) (hxy : x * y = y * x) (hxh : x * h = h * y)
    (hya : y * a = a * y ∨ h = a) : SporKRestGenerating p x := by
  intro Y hS hY
  have hxY : x ∈ Y := hY.mem_self hp hx hS
  have hbY : b ∈ Y := hY.mem_of_comm hxY hxb.symm
  have hyY : y ∈ Y := hY.mem_of_comm hxY hxy.symm
  have hhY : h ∈ Y := hY h (by rw [mul_assoc, hxh, ← mul_assoc, inv_mul_cancel, one_mul]; exact hyY)
  have haY : a ∈ Y := by
    rcases hya with hya | rfl
    · have hay : a⁻¹ * y * a ∈ Y := by
        rw [mul_assoc, hya, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hyY
      exact hY.mem_of_conj hhY hxh hay
    · exact hhY
  rw [eq_top_iff, ← hab, Subgroup.closure_le]
  rintro z (rfl | rfl)
  · exact haY
  · exact hbY

theorem SporKRestGenerating.of_isConj {p : ℕ} {x x' : K} (hc : IsConj x x')
    (h : SporKRestGenerating p x) : SporKRestGenerating p x' := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  have := h.of_mulEquiv (MulAut.conj c)
  rwa [MulAut.conj_apply, hc] at this

end CFSG.StandardType.SporadicShape
