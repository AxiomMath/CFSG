module

public import CFSG.Permutation.UnitaryThreeRecognition.CentralTorusOrbit
public import CFSG.Permutation.UnitaryThreeRecognition.SMap

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem involution_mem_mul_involution [Finite G] {b : Ω} (hb : b ≠ a)
    {j : G} (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    (hQodd : Odd (Nat.card Q)) {i : G} (hia : i • a = a) (hi2 : i * i = 1) (hi1 : i ≠ 1) :
    ∃ v ∈ Q, i = v * j := by
  obtain ⟨v, hv, h, hh, rfl⟩ := hQ.exists_mul_pairStab hb hia
  have hh2 : h * h = 1 := by
    have hmem : h * h ∈ Q := by
      have e : h * h = (h * v * h⁻¹)⁻¹ * v⁻¹ := by
        have : v * h * (v * h) = 1 := hi2
        calc h * h = (h * v * h⁻¹)⁻¹ * v⁻¹ * (v * h * (v * h)) := by group
          _ = (h * v * h⁻¹)⁻¹ * v⁻¹ := by rw [this, mul_one]
      rw [e]
      exact Q.mul_mem (Q.inv_mem (hQ.normal h hh.1 v hv)) (Q.inv_mem hv)
    exact Subgroup.disjoint_def.mp (hQ.disjoint_pairStab hb) hmem
      ((pairStab G a b).mul_mem hh hh)
  rcases hsq h hh hh2 with h1 | h1
  · exfalso
    subst h1
    rw [mul_one] at hi2 hi1
    have hv2 : (⟨v, hv⟩ : Q) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hi2)
    have hord : orderOf (⟨v, hv⟩ : Q) ∣ 2 := orderOf_dvd_of_pow_eq_one hv2
    have hord' : orderOf (⟨v, hv⟩ : Q) ∣ Nat.card Q := orderOf_dvd_natCard _
    have hodd : Odd (orderOf (⟨v, hv⟩ : Q)) := Odd.of_dvd_nat hQodd hord'
    have h1' : orderOf (⟨v, hv⟩ : Q) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
      · exact h
      · rw [h] at hodd; exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff] at h1'
    exact hi1 (congrArg Subtype.val h1')
  · exact ⟨v, hv, by rw [h1]⟩

theorem sLeft_block [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {u : G} (hu : u ∈ Q) (huZ : u ∉ centQ Q j)
    {w : G} (hw : w ∈ swapFix G a b s) (hw1 : w ≠ 1)
    {w' : G} (hw' : w' ∈ swapFix G a b s) (hw'1 : w' ≠ 1) :
    (sLeft Q a b s (u⁻¹ * w * u * w⁻¹))⁻¹ * sLeft Q a b s (u⁻¹ * w' * u * w'⁻¹) ∈
      centQ Q j := by
  classical
  have hsb := swap_smul_b hsa hs2
  have hab : a ≠ b := fun h => hb h.symm
  have hQodd : Odd (Nat.card Q) := by rw [hQcard]; exact hpodd.pow
  have hux : j • (u • b) ≠ u • b := by
    intro h
    exact huZ (mem_centQ.mpr ⟨hu, (hQ.fixes_iff hb hj hu).mp h⟩)
  obtain ⟨g, hga, hgb⟩ := htwo hab (fun h => hux h.symm)
  set x := u • b with hxdef
  set jx := g * j * g⁻¹ with hjxdef
  have hjxx : jx • x = x := by
    rw [hjxdef, mul_smul, mul_smul, ← hga, inv_smul_smul, hj.1]
  have hjxjx : jx • (j • x) = j • x := by
    rw [hjxdef, mul_smul, mul_smul, ← hgb, inv_smul_smul, hj.2]
  have hjx2 : jx * jx = 1 := by
    rw [hjxdef]
    calc g * j * g⁻¹ * (g * j * g⁻¹) = g * (j * j) * g⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  have hjx1 : jx ≠ 1 := by
    intro h
    apply hj1
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [hjxdef, mul_assoc] using this
  have hjxj : jx * j = j * jx := by
    set i := j * jx * j with hidef
    have hi : g⁻¹ * i * g ∈ pairStab G a b := by
      refine ⟨?_, ?_⟩
      · change (g⁻¹ * i * g) • a = a
        calc (g⁻¹ * i * g) • a = g⁻¹ • (j • (jx • (j • (g • a)))) := by
              simp only [hidef, mul_smul]
          _ = g⁻¹ • (j • (j • x)) := by rw [hga, hjxjx]
          _ = g⁻¹ • x := by rw [← mul_smul j j x, hj2, one_smul]
          _ = a := by rw [← hga, inv_smul_smul]
      · change (g⁻¹ * i * g) • b = b
        calc (g⁻¹ * i * g) • b = g⁻¹ • (j • (jx • (j • (g • b)))) := by
              simp only [hidef, mul_smul]
          _ = g⁻¹ • (j • (jx • x)) := by rw [hgb, ← mul_smul j j x, hj2, one_smul]
          _ = g⁻¹ • (j • x) := by rw [hjxx]
          _ = b := by rw [← hgb, inv_smul_smul]
    have hii : i * i = 1 := by
      rw [hidef]
      calc j * jx * j * (j * jx * j) = j * jx * (j * j) * jx * j := by group
        _ = j * (jx * jx) * j := by rw [hj2]; group
        _ = 1 := by rw [hjx2, mul_one, hj2]
    have hi2 : g⁻¹ * i * g * (g⁻¹ * i * g) = 1 := by
      calc g⁻¹ * i * g * (g⁻¹ * i * g) = g⁻¹ * (i * i) * g := by group
        _ = 1 := by rw [hii]; group
    rcases hsq _ hi hi2 with h | h
    · exfalso
      apply hjx1
      have h' : i = 1 := by
        calc i = g * (g⁻¹ * i * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
      calc jx = j⁻¹ * (j * jx * j) * j⁻¹ := by group
        _ = j⁻¹ * j⁻¹ := by rw [← hidef, h', mul_one]
        _ = (j * j)⁻¹ := by group
        _ = 1 := by rw [hj2, inv_one]
    · have h' : i = jx := by
        calc i = g * (g⁻¹ * i * g) * g⁻¹ := by group
          _ = jx := by rw [h]
      calc jx * j = j * jx * j * j := by rw [← hidef, h']
        _ = j * jx * (j * j) := by group
        _ = j * jx := by rw [hj2, mul_one]
  have hWjx : ∀ v ∈ swapFix G a b s, jx * v = v * jx := fun v hv =>
    hQ.commute_of_mem_centralizer hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd
      hQcard hΩcard hTcard hsa hs2 hv hjxj
  set i' := s * u⁻¹ * jx * u * s with hi'def
  have hi'a : i' • a = a := by
    calc i' • a = s • (u⁻¹ • (jx • (u • (s • a)))) := by simp only [hi'def, mul_smul]
      _ = s • (u⁻¹ • (jx • x)) := by rw [hsa]
      _ = s • (u⁻¹ • x) := by rw [hjxx]
      _ = a := by rw [hxdef, inv_smul_smul, hsb]
  have hi'2 : i' * i' = 1 := by
    rw [hi'def]
    calc s * u⁻¹ * jx * u * s * (s * u⁻¹ * jx * u * s) =
        s * u⁻¹ * jx * u * (s * s) * u⁻¹ * jx * u * s := by group
      _ = s * u⁻¹ * (jx * jx) * u * s := by rw [hs2]; group
      _ = s * s := by rw [hjx2]; group
      _ = 1 := hs2
  have hi'1 : i' ≠ 1 := by
    intro h
    apply hjx1
    calc jx = u * (s * s) * u⁻¹ * jx * u * (s * s) * u⁻¹ := by rw [hs2]; group
      _ = u * s * (s * u⁻¹ * jx * u * s) * s * u⁻¹ := by group
      _ = u * s * s * u⁻¹ := by rw [← hi'def, h, mul_one]
      _ = 1 := by rw [mul_assoc u s s, hs2, mul_one, mul_inv_cancel]
  obtain ⟨v, hv, hi'v⟩ := hQ.involution_mem_mul_involution hb hsq hQodd hi'a hi'2 hi'1
  have hfix : ∀ y ∈ swapFix G a b s, y ≠ 1 →
      u⁻¹ * y * u * y⁻¹ ∈ Q ∧ u⁻¹ * y * u * y⁻¹ ≠ 1 ∧
      v * (j * sLeft Q a b s (u⁻¹ * y * u * y⁻¹) * j⁻¹) =
        sLeft Q a b s (u⁻¹ * y * u * y⁻¹) := by
    intro y hy hy1
    have hyT : y ∈ pairStab G a b := (mem_swapFix.mp hy).1
    have hyuQ : u⁻¹ * y * u * y⁻¹ ∈ Q := by
      have := hQ.normal y hyT.1 u hu
      have e : u⁻¹ * y * u * y⁻¹ = u⁻¹ * (y * u * y⁻¹) := by group
      rw [e]
      exact Q.mul_mem (Q.inv_mem hu) this
    have hyu1 : u⁻¹ * y * u * y⁻¹ ≠ 1 := by
      intro e
      have hyu : y * u = u * y := by
        calc y * u = u * (u⁻¹ * y * u * y⁻¹) * y := by group
          _ = u * y := by rw [e, mul_one]
      exact huZ (mem_centQ.mpr ⟨hu, hQ.commute_involution_of_commute hb htwo hfaith hcomm hj
        hj2 hj1 hsq hpp hp hf hpodd hd hQcard hΩcard hTcard hsa hs2 hy hy1 hu hyu⟩)
    refine ⟨hyuQ, hyu1, ?_⟩
    set yl := sLeft Q a b s (u⁻¹ * y * u * y⁻¹) with hyldef
    have hyl : yl ∈ Q := hQ.sLeft_mem hb hsa hs2 hyuQ hyu1
    have hyb : y⁻¹ • b = b := by rw [inv_smul_eq_iff, hyT.2]
    have hpt : yl • b = s • (u⁻¹ • (y • x)) := by
      rw [hyldef, ← hQ.smul_sLeft hb hsa hs2 hyuQ hyu1]
      simp only [mul_smul, hyb, hxdef]
    have hyx : jx • (y • x) = y • x := by
      rw [smul_smul, hWjx y hy, mul_smul, hjxx]
    have h1 : i' • (yl • b) = yl • b := by
      rw [hpt]
      calc i' • (s • (u⁻¹ • (y • x))) =
          s • (u⁻¹ • (jx • (u • ((s * s) • (u⁻¹ • (y • x)))))) := by
            simp only [hi'def, mul_smul]
        _ = s • (u⁻¹ • (y • x)) := by rw [hs2, one_smul, smul_inv_smul, hyx]
    rw [hi'v] at h1
    have hjb : j⁻¹ • b = b := by rw [inv_smul_eq_iff, hj.2]
    have h2 : (v * (j * yl * j⁻¹)) • b = yl • b := by
      calc (v * (j * yl * j⁻¹)) • b = (v * j) • (yl • (j⁻¹ • b)) := by simp only [mul_smul]
        _ = yl • b := by rw [hjb, h1]
    exact hQ.eq_of_smul_eq (Q.mul_mem hv (hQ.normal j hj.1 yl hyl)) hyl hb h2
  obtain ⟨h1Q, h11, e1⟩ := hfix w hw hw1
  obtain ⟨h2Q, h21, e2⟩ := hfix w' hw' hw'1
  set y₁ := sLeft Q a b s (u⁻¹ * w * u * w⁻¹)
  set y₂ := sLeft Q a b s (u⁻¹ * w' * u * w'⁻¹)
  have hy₁ : y₁ ∈ Q := hQ.sLeft_mem hb hsa hs2 h1Q h11
  have hy₂ : y₂ ∈ Q := hQ.sLeft_mem hb hsa hs2 h2Q h21
  refine mem_centQ.mpr ⟨Q.mul_mem (Q.inv_mem hy₁) hy₂, ?_⟩
  have key : y₁⁻¹ * y₂ = j * (y₁⁻¹ * y₂) * j⁻¹ := by
    calc y₁⁻¹ * y₂ = (v * (j * y₁ * j⁻¹))⁻¹ * (v * (j * y₂ * j⁻¹)) := by rw [e1, e2]
      _ = j * (y₁⁻¹ * y₂) * j⁻¹ := by group
  calc j * (y₁⁻¹ * y₂) = j * (y₁⁻¹ * y₂) * j⁻¹ * j := by group
    _ = y₁⁻¹ * y₂ * j := by rw [← key]

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
