module

public import CFSG.Permutation.UnitaryThreeRecognition.CentralTorus

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem commute_of_mem_centralizer [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {w : G} (hw : w ∈ swapFix G a b s) {c : G} (hc : c * j = j * c) : c * w = w * c := by
  classical
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]
  have hwZ : ∀ z ∈ centQ Q j, w * z = z * w := fun z hz =>
    hQ.swapFix_commute_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hQcard
      hΩcard hTcard hsa hs2 hw hz
  have hwT : ∀ t ∈ pairStab G a b, w * t = t * w := fun t ht =>
    hcomm w (mem_swapFix.mp hw).1 t ht
  have hws : w * s = s * w := (mem_swapFix.mp hw).2.symm
  have hsj : s * j = j * s := by
    have hmem : s * j * s⁻¹ ∈ pairStab G a b := conj_mem_pairStab hsa hsb hj
    have hsq' : s * j * s⁻¹ * (s * j * s⁻¹) = 1 := by
      calc s * j * s⁻¹ * (s * j * s⁻¹) = s * (j * j) * s⁻¹ := by group
        _ = 1 := by rw [hj2]; group
    rcases hsq _ hmem hsq' with h | h
    · exfalso; apply hj1
      have := congrArg (fun z => s⁻¹ * z * s) h
      simpa [mul_assoc] using this
    · calc s * j = s * j * s⁻¹ * s := by group
        _ = j * s := by rw [h]
  have hstab : ∀ c' : G, c' * j = j * c' → c' • a = a → c' * w = w * c' := by
    intro c' hc' hc'a
    obtain ⟨x, hxQ, h, hh, rfl⟩ := hQ.exists_mul_pairStab hb hc'a
    have hhj : h * j = j * h := hcomm h hh j hj
    have hxj : j * x = x * j := by
      have : x * h * j = x * j * h := by
        calc x * h * j = x * (h * j) := by group
          _ = x * (j * h) := by rw [hhj]
          _ = x * j * h := by group
      have h2 : x * j * h = j * x * h := by
        calc x * j * h = x * h * j := this.symm
          _ = j * (x * h) := hc'
          _ = j * x * h := by group
      exact (mul_right_cancel h2).symm
    have hxw : x * w = w * x := (hwZ x (mem_centQ.mpr ⟨hxQ, hxj⟩)).symm
    have hhw : h * w = w * h := (hwT h hh).symm
    calc x * h * w = x * (h * w) := by group
      _ = x * (w * h) := by rw [hhw]
      _ = (x * w) * h := by group
      _ = (w * x) * h := by rw [hxw]
      _ = w * (x * h) := by group
  by_cases hca : c • a = a
  · exact hstab c hc hca
  ·
    have hfix : j • (c • a) = c • a := by rw [smul_smul, ← hc, mul_smul, hj.1]
    obtain ⟨z, hzQ, hz⟩ := hQ.exists_smul_eq hb hca
    have hzj : j * z = z * j := (hQ.fixes_iff hb hj hzQ).mp (by rw [hz]; exact hfix)
    have hzZ : z ∈ centQ Q j := mem_centQ.mpr ⟨hzQ, hzj⟩
    set c' := (z * s)⁻¹ * c with hc'def
    have hc'j : c' * j = j * c' := by
      have hzsj : (z * s) * j = j * (z * s) := by
        calc (z * s) * j = z * (s * j) := by group
          _ = z * (j * s) := by rw [hsj]
          _ = (z * j) * s := by group
          _ = (j * z) * s := by rw [hzj]
          _ = j * (z * s) := by group
      have hzsj' : (z * s)⁻¹ * j = j * (z * s)⁻¹ := by
        calc (z * s)⁻¹ * j = (z * s)⁻¹ * (j * (z * s)) * (z * s)⁻¹ := by group
          _ = (z * s)⁻¹ * ((z * s) * j) * (z * s)⁻¹ := by rw [hzsj]
          _ = j * (z * s)⁻¹ := by group
      calc c' * j = (z * s)⁻¹ * (c * j) := by rw [hc'def]; group
        _ = (z * s)⁻¹ * (j * c) := by rw [hc]
        _ = ((z * s)⁻¹ * j) * c := by group
        _ = (j * (z * s)⁻¹) * c := by rw [hzsj']
        _ = j * c' := by rw [hc'def]; group
    have hc'a : c' • a = a := by
      rw [hc'def, mul_smul, inv_smul_eq_iff, mul_smul, hsa, hz]
    have h1 := hstab c' hc'j hc'a
    have hzsw : (z * s) * w = w * (z * s) := by
      have hzw : z * w = w * z := (hwZ z hzZ).symm
      calc (z * s) * w = z * (s * w) := by group
        _ = z * (w * s) := by rw [hws]
        _ = (z * w) * s := by group
        _ = (w * z) * s := by rw [hzw]
        _ = w * (z * s) := by group
    have hc_eq : c = (z * s) * c' := by rw [hc'def]; group
    rw [hc_eq]
    calc (z * s) * c' * w = (z * s) * (c' * w) := by group
      _ = (z * s) * (w * c') := by rw [h1]
      _ = ((z * s) * w) * c' := by group
      _ = (w * (z * s)) * c' := by rw [hzsw]
      _ = w * ((z * s) * c') := by group

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
