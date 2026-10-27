module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQCount
public import CFSG.Permutation.UnitaryThreeRecognition.CentralTorusOrbit
public import CFSG.Permutation.UnitaryThreeRecognition.ZTransitive

public section

open MulAction

open scoped Classical

namespace CFSG.UnitaryThreeRecognition

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace AbelianQ

variable {Q : Subgroup G} {j : G} {hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x}

theorem exists_smul_eq_of_two {a b : Ω} (hab : a ≠ b)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w) (c : Ω) :
    ∃ k : G, k • a = c := by
  by_cases hc : c = a
  · exact ⟨1, by rw [hc, one_smul]⟩
  · obtain ⟨k, hk, -⟩ := htwo hab hc
    exact ⟨k, hk⟩

theorem exists_mul_eq_of_involution {a b : Ω} (hQ : IsRootSubgroup Q a) (hb : b ≠ a)
    [Finite Q] (hodd : Odd (Nat.card Q)) (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {i : G} (hia : i • a = a) (hi2 : i * i = 1) (hi1 : i ≠ 1) : ∃ y ∈ Q, i = y * j := by
  obtain ⟨y, hy, t, ht, rfl⟩ := hQ.exists_mul_pairStab hb hia
  have hy' : t * y * t⁻¹ ∈ Q := hQ.normal t ht.1 y hy
  have htt : t * t = (y * (t * y * t⁻¹))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc y * (t * y * t⁻¹) * (t * t) = y * t * (y * t) := by group
      _ = 1 := hi2
  have htt1 : t * t = 1 := by
    have hmemQ : t * t ∈ Q := by rw [htt]; exact Q.inv_mem (Q.mul_mem hy hy')
    exact Subgroup.disjoint_def.mp (hQ.disjoint_pairStab hb) hmemQ
      ((pairStab G a b).mul_mem ht ht)
  rcases hsq t ht htt1 with rfl | rfl
  · exfalso
    apply hi1
    rw [mul_one] at hi2 ⊢
    exact eq_one_of_mul_self_eq_one hodd hy hi2
  · exact ⟨y, hy, rfl⟩

theorem eq_of_commute_of_smul_eq {a b : Ω} (hQ : IsRootSubgroup Q a) (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    [Finite Q] (hodd : Odd (Nat.card Q)) (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) {i₁ i₂ : G} (h1 : i₁ * i₁ = 1) (h1' : i₁ ≠ 1)
    (h2 : i₂ * i₂ = 1) (h2' : i₂ ≠ 1) (hc : i₁ * i₂ = i₂ * i₁) {x : Ω} (hx1 : i₁ • x = x)
    (hx2 : i₂ • x = x) :
    i₁ = i₂ := by
  obtain ⟨k, hk⟩ := exists_smul_eq_of_two (fun h => hb h.symm) htwo x
  have hfix : ∀ {i : G}, i • x = x → (k⁻¹ * i * k) • a = a := by
    intro i hi
    rw [mul_smul, mul_smul, hk, hi, inv_smul_eq_iff, hk]
  have hsq' : ∀ {i : G}, i * i = 1 → (k⁻¹ * i * k) * (k⁻¹ * i * k) = 1 := by
    intro i hi
    calc (k⁻¹ * i * k) * (k⁻¹ * i * k) = k⁻¹ * (i * i) * k := by group
      _ = 1 := by rw [hi]; group
  have hne : ∀ {i : G}, i ≠ 1 → k⁻¹ * i * k ≠ 1 := by
    intro i hi h
    apply hi
    calc i = k * (k⁻¹ * i * k) * k⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨y₁, hy₁, e₁⟩ := exists_mul_eq_of_involution hQ hb hodd hsq (hfix hx1) (hsq' h1) (hne h1')
  obtain ⟨y₂, hy₂, e₂⟩ := exists_mul_eq_of_involution hQ hb hodd hsq (hfix hx2) (hsq' h2) (hne h2')
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj2
  have hprod : (k⁻¹ * i₁ * k) * (k⁻¹ * i₂ * k) = y₁ * (j * y₂ * j⁻¹) := by
    rw [e₁, e₂, hjinv]; group
  have hmem : (k⁻¹ * i₁ * k) * (k⁻¹ * i₂ * k) ∈ Q := by
    rw [hprod]
    exact Q.mul_mem hy₁ (hQ.normal j hj.1 y₂ hy₂)
  have hsq3 : ((k⁻¹ * i₁ * k) * (k⁻¹ * i₂ * k)) * ((k⁻¹ * i₁ * k) * (k⁻¹ * i₂ * k)) = 1 := by
    calc ((k⁻¹ * i₁ * k) * (k⁻¹ * i₂ * k)) * ((k⁻¹ * i₁ * k) * (k⁻¹ * i₂ * k)) =
          k⁻¹ * (i₁ * i₂ * (i₁ * i₂)) * k := by group
      _ = k⁻¹ * (i₁ * (i₂ * i₁) * i₂) * k := by group
      _ = k⁻¹ * (i₁ * (i₁ * i₂) * i₂) * k := by rw [hc]
      _ = k⁻¹ * ((i₁ * i₁) * (i₂ * i₂)) * k := by group
      _ = 1 := by rw [h1, h2]; group
  have hone := eq_one_of_mul_self_eq_one hodd hmem hsq3
  have : i₁ * i₂ = 1 := by
    calc i₁ * i₂ = k * ((k⁻¹ * i₁ * k) * (k⁻¹ * i₂ * k)) * k⁻¹ := by group
      _ = 1 := by rw [hone]; group
  calc i₁ = i₁ * (i₂ * i₂) := by rw [h2, mul_one]
    _ = (i₁ * i₂) * i₂ := by group
    _ = i₂ := by rw [this, one_mul]

theorem swap_commute_of_unique {a b : Ω}
    (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j) {s : G} (hsa : s • a = b)
    (hsb : s • b = a) : s * j = j * s := by
  have hmem : s * j * s⁻¹ ∈ pairStab G a b := IsRootSubgroup.conj_mem_pairStab hsa hsb hj
  have hsq' : s * j * s⁻¹ * (s * j * s⁻¹) = 1 := by
    calc s * j * s⁻¹ * (s * j * s⁻¹) = s * (j * j) * s⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  rcases hsq _ hmem hsq' with h | h
  · exfalso
    apply hj1
    have := congrArg (fun z => s⁻¹ * z * s) h
    simpa [mul_assoc] using this
  · calc s * j = s * j * s⁻¹ * s := by group
      _ = j * s := by rw [h]

theorem conj_commute_of_mem_swapFix {a b : Ω}
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hj2 : j * j = 1) {s : G} (hsa : s • a = b) (hsb : s • b = a) {g : G} {c : Ω}
    (hga : g • a = c) (hgb : g • b = j • c) {w : G} (hw : w ∈ swapFix G a b s) :
    j * (g * w * g⁻¹) = (g * w * g⁻¹) * j := by
  have hs'a : (g⁻¹ * j * g) • a = b := by
    rw [mul_smul, mul_smul, hga, ← hgb, inv_smul_smul]
  have hs'b : (g⁻¹ * j * g) • b = a := by
    rw [mul_smul, mul_smul, hgb, smul_smul j j, hj2, one_smul, ← hga, inv_smul_smul]
  rw [swapFix_eq hsa hsb hs'a hs'b hcomm] at hw
  have hcw : g⁻¹ * j * g * w = w * (g⁻¹ * j * g) := (mem_swapFix.mp hw).2
  calc j * (g * w * g⁻¹) = g * (g⁻¹ * j * g * w) * g⁻¹ := by group
    _ = g * (w * (g⁻¹ * j * g)) * g⁻¹ := by rw [hcw]
    _ = g * w * g⁻¹ * j := by group

section Setting

variable [Finite G] [Finite Ω] {a b : Ω} (hQ : IsRootSubgroup Q a) (hb : b ≠ a)
  (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
  (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
  (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
  (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
  (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
  {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
  (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
  (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
  {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
include hQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hQcard hΩcard hTcard hsa hs2

omit [Finite Ω] in
theorem smul_eq_iff_of_mem_swapFix [Finite Ω] {w : G} (hw : w ∈ swapFix G a b s)
    (hw1 : w ≠ 1) (x : Ω) : w • x = x ↔ j • x = x := by
  have hwT : w ∈ pairStab G a b := (mem_swapFix.mp hw).1
  by_cases hx : x = a
  · subst hx
    exact ⟨fun _ => hj.1, fun _ => hwT.1⟩
  · obtain ⟨u, hu, rfl⟩ := hQ.exists_smul_eq hb hx
    rw [hQ.fixes_iff hb hwT hu, hQ.fixes_iff hb hj hu]
    constructor
    · intro hwu
      exact hQ.commute_involution_of_commute hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd
        hd hQcard hΩcard hTcard hsa hs2 hw hw1 hu hwu
    · intro hju
      exact hQ.swapFix_commute_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd
        hQcard hΩcard hTcard hsa hs2 hw (mem_centQ.mpr ⟨hu, hju⟩)

theorem smul_ne_of_mem_swapFix {g : G} {c : Ω} (hga : g • a = c) (hgb : g • b = j • c)
    (hc : j • c ≠ c) {w : G} (hw : w ∈ swapFix G a b s) (hw1 : w ≠ 1) {x : Ω}
    (hx : j • x = x) : (g * w * g⁻¹) • x ≠ x := by
  intro h
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]
  have hQodd : Odd (Nat.card Q) := by rw [hQcard]; exact hpodd.pow
  have h1 : w • (g⁻¹ • x) = g⁻¹ • x := by
    rw [eq_inv_smul_iff]
    rw [mul_smul, mul_smul] at h
    exact h
  have h2 : j • (g⁻¹ • x) = g⁻¹ • x :=
    (smul_eq_iff_of_mem_swapFix hQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd
      hQcard hΩcard hTcard hsa hs2 hw hw1 _).mp h1
  have h3 : (g * j * g⁻¹) • x = x := by
    rw [mul_smul, mul_smul, h2, smul_inv_smul]
  have hjW : j ∈ swapFix G a b s :=
    mem_swapFix.mpr ⟨hj, swap_commute_of_unique hj hj2 hj1 hsq hsa hsb⟩
  have hcj := conj_commute_of_mem_swapFix hcomm hj2 hsa hsb hga hgb hjW
  have hsq1 : (g * j * g⁻¹) * (g * j * g⁻¹) = 1 := by
    calc (g * j * g⁻¹) * (g * j * g⁻¹) = g * (j * j) * g⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  have hne1 : g * j * g⁻¹ ≠ 1 := by
    intro h'
    apply hj1
    calc j = g⁻¹ * (g * j * g⁻¹) * g := by group
      _ = 1 := by rw [h']; group
  have heq := eq_of_commute_of_smul_eq hQ hb htwo hQodd hsq hj hj2 hsq1 hne1 hj2 hj1 hcj.symm h3 hx
  apply hc
  calc j • c = (g * j * g⁻¹) • c := by rw [heq]
    _ = c := by rw [mul_smul, mul_smul, ← hga, inv_smul_smul, hj.1]

theorem sameLevel_conj_swapFix (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {g w : G}
    (hw : w ∈ swapFix G a b s) {x : Ω} (hx : x ≠ g • a) :
    SameLevel Q j hQab a (g • a) x ((g * w * g⁻¹) • x) := by
  have hwT : w ∈ pairStab G a b := (mem_swapFix.mp hw).1
  have hQodd : Odd (Nat.card Q) := by rw [hQcard]; exact hpodd.pow
  have hjQ : ∀ y ∈ Q, j * y * j⁻¹ ∈ Q := fun y hy => hQ.normal j hj.1 y hy
  have hx' : g⁻¹ • x ≠ a := by
    intro h
    apply hx
    rw [← h, smul_inv_smul]
  obtain ⟨u, hu, hux⟩ := hQ.exists_smul_eq hb hx'
  obtain ⟨z, hz, v, hv, rfl⟩ := exists_centQ_mul_invSub (hQab := hQab) hQodd hjQ hj2 hu
  have hzQ : z ∈ Q := (mem_centQ.mp hz).1
  have hvQ : v ∈ Q := invSub_le hv
  have hwz : w * z = z * w := hQ.swapFix_commute_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp
    hp hf hpodd hd hQcard hΩcard hTcard hsa hs2 hw hz
  have hwv : w * v * w⁻¹ ∈ invSub Q j hQab := conj_mem_invSub hQ hb hcomm hj hwT.1 hv
  refine ⟨g, rfl, (w * v * w⁻¹) * v⁻¹,
    (invSub Q j hQab).mul_mem hwv ((invSub Q j hQab).inv_mem hv), ?_⟩
  have hxg : x = g • ((z * v) • b) := by rw [hux, smul_inv_smul]
  have hzv : v⁻¹ * z = z * v⁻¹ := hQab _ (Q.inv_mem hvQ) _ hzQ
  have hz2 : (w * v * w⁻¹) * z = z * (w * v * w⁻¹) := hQab _ (invSub_le hwv) _ hzQ
  have hL : (w * v * w⁻¹ * v⁻¹) * (z * v) = z * (w * v * w⁻¹) := by
    calc (w * v * w⁻¹ * v⁻¹) * (z * v) = (w * v * w⁻¹) * (v⁻¹ * z) * v := by group
      _ = (w * v * w⁻¹) * (z * v⁻¹) * v := by rw [hzv]
      _ = (w * v * w⁻¹) * z := by group
      _ = z * (w * v * w⁻¹) := hz2
  have hR : w * (z * v) = z * (w * v * w⁻¹) * w := by
    calc w * (z * v) = (w * z) * v := by group
      _ = (z * w) * v := by rw [hwz]
      _ = z * (w * v * w⁻¹) * w := by group
  rw [hxg]
  calc (g * (w * v * w⁻¹ * v⁻¹) * g⁻¹) • g • (z * v) • b
      = g • (((w * v * w⁻¹ * v⁻¹) * (z * v)) • b) := by
        simp only [mul_smul, inv_smul_smul]
    _ = g • ((z * (w * v * w⁻¹)) • b) := by rw [hL]
    _ = g • ((w * (z * v)) • b) := by rw [hR, mul_smul _ w b, hwT.2]
    _ = (g * w * g⁻¹) • g • (z * v) • b := by
        simp only [mul_smul, inv_smul_smul]

end Setting

theorem card_levelPoints [Fintype G] [Fintype Ω] {a b : Ω} (hQ : IsRootSubgroup Q a)
    (hb : b ≠ a) (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hj : j ∈ pairStab G a b) {x y : Ω} (hxy : x ≠ y) :
    (levelPoints Q j hQab a x y).card = Nat.card (invSub Q j hQab) - 1 := by
  have hab : a ≠ b := fun h => hb h.symm
  have hN : ∀ {x y : Ω}, x ≠ y →
      (levelPoints Q j hQab a x y).card = (levelPoints Q j hQab a a b).card := by
    intro x y hxy
    obtain ⟨k, hka, hkb⟩ := htwo hab hxy
    rw [← hka, ← hkb, card_levelPoints_smul]
  have hP : ∀ c, (levelPairs Q j hQab a c).card =
      (Fintype.card Ω - 1) * (Nat.card (invSub Q j hQab) - 1) := by
    intro c
    obtain ⟨k, hk⟩ := exists_smul_eq_of_two hab htwo c
    rw [← hk, card_levelPairs_smul, card_levelPairs_base hQ hb hcomm hj]
  have hsum := sum_card_levelPairs (Q := Q) (j := j) (hQab := hQab) a
  have hinner : ∀ x : Ω, (∑ y : Ω, if x = y then 0 else (levelPoints Q j hQab a x y).card) =
      (Fintype.card Ω - 1) * (levelPoints Q j hQab a a b).card := by
    intro x
    rw [← sum_ite_ne x]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : x = y
    · subst h
      simp
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), hN h]
  rw [Fintype.sum_prod_type] at hsum
  simp only [hP, hinner, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hpos : 0 < Fintype.card Ω * (Fintype.card Ω - 1) := by
    have : 1 < Fintype.card Ω := Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    exact Nat.mul_pos (by omega) (by omega)
  rw [hN hxy]
  rw [← mul_assoc, ← mul_assoc] at hsum
  exact (Nat.eq_of_mul_eq_mul_left hpos hsum).symm


theorem card_eq_five_of_abelian [Finite G] [Finite Ω] {a b : Ω} (hQ : IsRootSubgroup Q a)
    (hb : b ≠ a) (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p)
    (hd : d = Nat.gcd (p ^ f + 1) 3)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : p ^ f = 5 := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite Ω
  have hab : a ≠ b := fun h => hb h.symm
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]
  have hd3 : d ∣ 3 := hd ▸ Nat.gcd_dvd_right _ _
  have hdodd : Odd d := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h <;> rw [h] <;> decide
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  have hZ : Nat.card (centQ Q j) = p ^ f := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj
    hj2 hj1 hsq hpp hp hf hQcard hΩcard hTdvd
  have hQodd : Odd (Nat.card Q) := by rw [hQcard]; exact hpodd.pow
  have hjQ : ∀ x ∈ Q, j * x * j⁻¹ ∈ Q := fun x hx => hQ.normal j hj.1 x hx
  have hV := card_eq_card_centQ_mul (hQab := hQab) hQodd hjQ hj2
  set q := p ^ f with hq
  have hq3 : 3 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  have hqodd : Odd q := hpodd.pow
  have hp3 : p ^ (3 * f) = q ^ 3 := by rw [hq, ← pow_mul, mul_comm]
  have hp2 : p ^ (2 * f) = q ^ 2 := by rw [hq, ← pow_mul, mul_comm]
  have hVcard : Nat.card (invSub Q j hQab) = q ^ 2 := by
    rw [hQcard, hZ, hp3] at hV
    have h' : q * q ^ 2 = q * Nat.card (invSub Q j hQab) := by rw [← hV]; ring
    exact (Nat.eq_of_mul_eq_mul_left (by omega) h').symm
  have hW := hQ.card_swapFix_mul hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hdodd hQcard
    hΩcard hTcard hsa hs2
  set w₀ := Nat.card (swapFix G a b s) with hw₀
  have hw₀pos : 0 < w₀ := Nat.card_pos
  set F : Finset Ω := Finset.univ.filter fun x => j • x = x with hFdef
  have hFcard : F.card = q + 1 := by
    rw [hFdef, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hQ.card_fixedPoints hb hj, hZ]
  have hΩ : Fintype.card Ω = q ^ 3 + 1 := by rw [← Nat.card_eq_fintype_card, hΩcard, hp3]
  set K : Ω → Finset (Ω × Ω) := fun c =>
    F.offDiag.filter fun ff => ff.1 ≠ c ∧ ff.2 ≠ c ∧ SameLevel Q j hQab a c ff.1 ff.2 with hK
  have hsumK : ∑ c : Ω, (K c).card = F.offDiag.card * (q ^ 2 - 1) := by
    simp only [hK, Finset.card_filter]
    rw [Finset.sum_comm, ← hVcard, Finset.sum_const_nat]
    intro ff hff
    have hne : ff.1 ≠ ff.2 := (Finset.mem_offDiag.mp hff).2.2
    rw [← card_levelPoints hQ hb htwo hcomm hj hne, levelPoints, Finset.card_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    apply propext
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨fun h => h1 h.symm, fun h => h2 h.symm, h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨fun h => h1 h.symm, fun h => h2 h.symm, h3⟩⟩
  have hlow : ∀ c : Ω, j • c ≠ c → F.card * (w₀ - 1) ≤ (K c).card := by
    intro c hc
    obtain ⟨g, hga, hgb⟩ := htwo hab (Ne.symm hc)
    set W' : Finset G := (Finset.univ.filter (· ∈ swapFix G a b s)).erase 1 with hW'
    have hW'card : W'.card = w₀ - 1 := by
      rw [hW', Finset.card_erase_of_mem, card_filter_mem]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (swapFix G a b s).one_mem
    have hmemW : ∀ w ∈ W', w ∈ swapFix G a b s ∧ w ≠ 1 := by
      intro w hw
      simp only [hW', Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact ⟨hw.2, hw.1⟩
    rw [← hW'card, ← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun fw : Ω × G => (fw.1, (g * fw.2 * g⁻¹) • fw.1))
    · rintro ⟨x, w⟩ hxw
      obtain ⟨hx, hw⟩ := Finset.mem_product.mp hxw
      obtain ⟨hwW, hw1⟩ := hmemW w hw
      have hxF : j • x = x := by simpa [hFdef] using hx
      have hyF : j • ((g * w * g⁻¹) • x) = (g * w * g⁻¹) • x := by
        rw [smul_smul, conj_commute_of_mem_swapFix hcomm hj2 hsa hsb hga hgb hwW, mul_smul, hxF]
      have hxc : x ≠ c := fun h => hc (h ▸ hxF)
      have hyc : (g * w * g⁻¹) • x ≠ c := fun h => hc (h ▸ hyF)
      have hne : (g * w * g⁻¹) • x ≠ x := smul_ne_of_mem_swapFix hQ hb htwo hfaith hcomm hj hj2
        hj1 hsq hpp hp hf hpodd hdodd hQcard hΩcard hTcard hsa hs2 hga hgb hc hwW hw1 hxF
      simp only [hK, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_offDiag, hFdef,
        Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨hxF, hyF, Ne.symm hne⟩, hxc, hyc, ?_⟩
      rw [← hga]
      exact sameLevel_conj_swapFix hQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hdodd
        hQcard hΩcard hTcard hsa hs2 hQab hwW (hga ▸ hxc)
    · rintro ⟨x, w⟩ hxw ⟨x', w'⟩ hxw' heq
      obtain ⟨hx, hw⟩ := Finset.mem_product.mp hxw
      obtain ⟨hx', hw'⟩ := Finset.mem_product.mp hxw'
      have h1 : x = x' := congrArg Prod.fst heq
      subst h1
      have h2 : (g * w * g⁻¹) • x = (g * w' * g⁻¹) • x := congrArg Prod.snd heq
      have hxF : j • x = x := by simpa [hFdef] using hx
      obtain ⟨hwW, -⟩ := hmemW w hw
      obtain ⟨hwW', -⟩ := hmemW w' hw'
      by_contra hww
      have hne : w'⁻¹ * w ≠ 1 := by
        intro h
        apply hww
        have : w = w' := by
          calc w = w' * (w'⁻¹ * w) := by group
            _ = w' := by rw [h, mul_one]
        rw [this]
      have hmem : w'⁻¹ * w ∈ swapFix G a b s :=
        (swapFix G a b s).mul_mem ((swapFix G a b s).inv_mem hwW') hwW
      apply smul_ne_of_mem_swapFix hQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hdodd
        hQcard hΩcard hTcard hsa hs2 hga hgb hc hmem hne hxF
      calc (g * (w'⁻¹ * w) * g⁻¹) • x = (g * w'⁻¹ * g⁻¹) • ((g * w * g⁻¹) • x) := by
            rw [smul_smul]; group
        _ = (g * w'⁻¹ * g⁻¹) • ((g * w' * g⁻¹) • x) := by rw [h2]
        _ = x := by rw [smul_smul]; group; simp
  have hmoved : (Finset.univ.filter fun c : Ω => j • c ≠ c).card = q ^ 3 - q := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Ω))
      (fun c : Ω => j • c = c)
    rw [← hFdef, hFcard, Finset.card_univ, hΩ] at this
    simp only [ne_eq] at this ⊢
    omega
  have hineq : (q ^ 3 - q) * ((q + 1) * (w₀ - 1)) ≤ ((q + 1) * (q + 1) - (q + 1)) * (q ^ 2 - 1) :=
    by
    calc (q ^ 3 - q) * ((q + 1) * (w₀ - 1))
        = ∑ c ∈ Finset.univ.filter (fun c : Ω => j • c ≠ c), F.card * (w₀ - 1) := by
          rw [Finset.sum_const, smul_eq_mul, hmoved, hFcard]
      _ ≤ ∑ c ∈ Finset.univ.filter (fun c : Ω => j • c ≠ c), (K c).card := by
          refine Finset.sum_le_sum fun c hc => hlow c ?_
          simpa using hc
      _ ≤ ∑ c : Ω, (K c).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.zero_le _)
      _ = ((q + 1) * (q + 1) - (q + 1)) * (q ^ 2 - 1) := by
          rw [hsumK, Finset.offDiag_card, hFcard]
  obtain ⟨r, hr⟩ : ∃ r, q ^ 2 = r + 1 :=
    ⟨q ^ 2 - 1, by have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hq3' : q ^ 3 - q = q * r := by
    have : q ^ 3 = q * q ^ 2 := by ring
    rw [this, hr]
    rw [Nat.mul_add, mul_one, Nat.add_sub_cancel]
  have hoff : (q + 1) * (q + 1) - (q + 1) = (q + 1) * q := by
    rw [Nat.mul_add (q + 1) q 1, mul_one, Nat.add_sub_cancel]
  rw [hq3', hoff, hr, Nat.add_sub_cancel] at hineq
  have hrpos : 0 < r := by nlinarith
  have hkey : (q * r * (q + 1)) * (w₀ - 1) ≤ (q * r * (q + 1)) * 1 := by
    calc (q * r * (q + 1)) * (w₀ - 1) = q * r * ((q + 1) * (w₀ - 1)) := by ring
      _ ≤ (q + 1) * q * r := hineq
      _ = (q * r * (q + 1)) * 1 := by ring
  have hw₀2 : w₀ ≤ 2 := by
    have := Nat.le_of_mul_le_mul_left hkey (by positivity)
    omega
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h1 | h3
  · rw [h1, mul_one] at hW
    omega
  · have hdq : 3 ∣ q + 1 := by
      have := Nat.gcd_dvd_left (p ^ f + 1) 3
      rw [← hd, h3] at this
      exact this
    rw [h3] at hW
    obtain ⟨k, hk⟩ := hqodd
    omega

theorem exists_not_commute_of_ne_five [Finite G] [Finite Ω] {a b : Ω} (hQ : IsRootSubgroup Q a)
    (hb : b ≠ a) (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p)
    (hd : d = Nat.gcd (p ^ f + 1) 3)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1) (h5 : p ^ f ≠ 5) :
    ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x := by
  by_contra hcon
  apply h5
  refine card_eq_five_of_abelian hQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hQcard
    hΩcard hTcard hsa hs2 ?_
  intro x hx y hy
  by_contra hxy
  exact hcon ⟨x, hx, y, hy, hxy⟩

end AbelianQ

end CFSG.UnitaryThreeRecognition
