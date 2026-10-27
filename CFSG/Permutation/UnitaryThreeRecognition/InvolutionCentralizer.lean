module

public import CFSG.Permutation.UnitaryThreeRecognition.Involutions
public import CFSG.Permutation.UnitaryThreeRecognition.Arith
public import CFSG.Permutation.UnitaryThreeRecognition.Counting
public import CFSG.Permutation.UnitaryThreeRecognition.Fixed

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem swapFix_eq {a b : Ω} {s s' : G} (hsa : s • a = b) (hsb : s • b = a) (hs'a : s' • a = b)
    (hs'b : s' • b = a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁) :
    swapFix G a b s = swapFix G a b s' := by
  have hmem : s' * s⁻¹ ∈ pairStab G a b := by
    have hsinvb : s⁻¹ • b = a := by rw [inv_smul_eq_iff, hsa]
    have hsinva : s⁻¹ • a = b := by rw [inv_smul_eq_iff, hsb]
    exact ⟨by change (s' * s⁻¹) • a = a; rw [mul_smul, hsinva, hs'b],
      by change (s' * s⁻¹) • b = b; rw [mul_smul, hsinvb, hs'a]⟩
  set r := s' * s⁻¹ with hr
  have hs' : s' = r * s := by rw [hr]; group
  ext t
  simp only [mem_swapFix]
  constructor
  · rintro ⟨ht, hst⟩
    refine ⟨ht, ?_⟩
    rw [hs']
    calc r * s * t = r * (t * s) := by rw [mul_assoc, hst]
      _ = (r * t) * s := by group
      _ = (t * r) * s := by rw [hcomm r hmem t ht]
      _ = t * (r * s) := by group
  · rintro ⟨ht, hst⟩
    refine ⟨ht, ?_⟩
    rw [hs'] at hst
    have : r * (s * t) = r * (t * s) := by
      calc r * (s * t) = r * s * t := by group
        _ = t * (r * s) := hst
        _ = (t * r) * s := by group
        _ = (r * t) * s := by rw [hcomm t ht r hmem]
        _ = r * (t * s) := by group
    exact mul_left_cancel this

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem card_centQ_involution_eq [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1) :
    Nat.card (centQ Q j) = p ^ f := by
  classical
  set T := pairStab G a b with hTdef
  have hab : a ≠ b := fun h => hb h.symm
  obtain ⟨g, hga, hgb⟩ := htwo hab hb
  have hcj : ∀ s : G, s • a = b → s • b = a → s * j = j * s := by
    intro s hsa hsb
    have hmem : s * j * s⁻¹ ∈ T := conj_mem_pairStab hsa hsb hj
    have hsq' : s * j * s⁻¹ * (s * j * s⁻¹) = 1 := by
      calc s * j * s⁻¹ * (s * j * s⁻¹) = s * (j * j) * s⁻¹ := by group
        _ = 1 := by rw [hj2]; group
    rcases hsq _ hmem hsq' with h | h
    · exfalso; apply hj1
      have := congrArg (fun z => s⁻¹ * z * s) h
      simpa [mul_assoc] using this
    · calc s * j = s * j * s⁻¹ * s := by group
        _ = j * s := by rw [h]
  have hgj := hcj g hga hgb
  have hC := hQ.card_centralizer hb hcomm hj hga hgj
  set z := Nat.card (centQ Q j) with hzdef
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hmoved : Nat.card {x : Ω // j • x ≠ x} = p ^ (3 * f) - z := by
    let : Fintype Ω := Fintype.ofFinite Ω
    have h1 := Fintype.card_subtype_compl (fun x : Ω => j • x = x)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hQ.card_fixedPoints hb hj, hΩcard] at h1
    rw [h1]; omega
  have hS1 := card_swapSet_eq_pairStab_mul hab htwo j
  have hS2 := card_swapSet_eq_centralizer_mul (G := G) a b j
  set k := Nat.card (ConjSwap G j a b) with hkdef
  have hcount : p ^ (3 * f) - z = (z + 1) * z * k := by
    have : Nat.card T * (p ^ (3 * f) - z) = Nat.card T * ((z + 1) * z * k) := by
      rw [← hmoved, ← hS1, hS2, hC]; ring
    exact Nat.eq_of_mul_eq_mul_left hTpos this
  have hzdvd : z ∣ p ^ (3 * f) := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le (inf_le_left : centQ Q j ≤ Q)
  obtain ⟨s, hs3, hzs⟩ := (Nat.dvd_prime_pow hpp).mp hzdvd
  have hzlt : z < p ^ (3 * f) := by
    rcases (Nat.le_of_dvd (by positivity) hzdvd).lt_or_eq with h | h
    · exact h
    · exfalso
      have hle : centQ Q j ≤ Q := inf_le_left
      have heqQ : centQ Q j = Q := Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, ← hzdef, h])
      apply hj1
      apply hfaith
      intro x
      by_cases hxa : x = a
      · rw [hxa]; exact hj.1
      · obtain ⟨u, huQ, hu⟩ := hQ.exists_smul_eq hb hxa
        rw [← hu]
        have huc : u ∈ centQ Q j := by rw [heqQ]; exact huQ
        exact (hQ.fixes_iff hb hj huQ).mpr (mem_centQ.mp huc).2
  have hslt : s < 3 * f := by
    by_contra h
    push Not at h
    have : p ^ (3 * f) ≤ p ^ s := Nat.pow_le_pow_right (by omega) h
    omega
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hcount; omega
    · exact h
  have : Nonempty (ConjSwap G j a b) := (Nat.card_pos_iff.mp hkpos).1
  obtain ⟨⟨s₀, ⟨c, hc⟩, hs₀a⟩⟩ := this
  have hs₀2 : s₀ * s₀ = 1 := by
    rw [hc]
    calc c⁻¹ * j * c * (c⁻¹ * j * c) = c⁻¹ * (j * j) * c := by group
      _ = 1 := by rw [hj2]; group
  have hs₀b : s₀ • b = a := by rw [← hs₀a, ← mul_smul, hs₀2, one_smul]
  have hsqcard : Nat.card {t : G // t ∈ T ∧ t * t = 1} ≤ 2 := by
    have : Nat.card {t : G // t ∈ T ∧ t * t = 1} ≤ Nat.card ({1, j} : Set G) := by
      apply Nat.card_le_card_of_injective (fun t => (⟨t.1, by
          rcases hsq t.1 t.2.1 t.2.2 with h | h
          · left; exact h
          · right; exact h⟩ : ({1, j} : Set G)))
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext hxy
    refine this.trans ?_
    rw [Nat.card_coe_set_eq]
    calc ({1, j} : Set G).ncard ≤ ({j} : Set G).ncard + 1 := Set.ncard_insert_le 1 {j}
      _ = 2 := by rw [Set.ncard_singleton]
  have hinv := card_involutions_mul_le hs₀a hs₀2 hcomm hsqcard
  have hkle_inv : k ≤ Nat.card {h : G // h * h = 1 ∧ h • a = b} := by
    apply Nat.card_le_card_of_injective (fun h => (⟨h.1, by
        obtain ⟨⟨c', hc'⟩, ha'⟩ := h.2
        refine ⟨?_, ha'⟩
        rw [hc']
        calc c'⁻¹ * j * c' * (c'⁻¹ * j * c') = c'⁻¹ * (j * j) * c' := by group
          _ = 1 := by rw [hj2]; group⟩ : {h : G // h * h = 1 ∧ h • a = b}))
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext hxy
  have hdvd1 := hQ.card_pairStab_dvd_swapFix_mul hb hs₀a hs₀b hcomm
  rw [hQcard] at hdvd1
  have hTs_dvd : Nat.card (swapFix G a b s₀) ∣ Nat.card T :=
    Subgroup.card_dvd_of_le (inf_le_left : swapFix G a b s₀ ≤ T)
  obtain ⟨m, hm⟩ := hTs_dvd
  have hTspos : 0 < Nat.card (swapFix G a b s₀) := Nat.card_pos
  have hm1 : m ∣ p ^ (3 * f) - 1 := by
    rw [hm] at hdvd1
    exact (Nat.mul_dvd_mul_iff_left hTspos).mp hdvd1
  have hm2 : m ∣ p ^ (2 * f) - 1 := by
    have : m ∣ Nat.card T := ⟨_, by rw [hm, mul_comm]⟩
    exact this.trans hTdvd
  have hm3 : m ∣ p ^ f - 1 := by
    have := Nat.dvd_gcd hm1 hm2
    rw [Nat.pow_sub_one_gcd_pow_sub_one] at this
    have hg : Nat.gcd (3 * f) (2 * f) = f := by
      rw [Nat.gcd_mul_right]; norm_num
    rwa [hg] at this
  have hqpos : 0 < p ^ f - 1 := by
    have : 3 ≤ p ^ f := le_trans hp (Nat.le_self_pow (by omega) p)
    omega
  have hmle : m ≤ p ^ f - 1 := Nat.le_of_dvd hqpos hm3
  have hk2 : k ≤ 2 * (p ^ f - 1) := by
    have h1 : k * Nat.card (swapFix G a b s₀) ≤ 2 * (Nat.card (swapFix G a b s₀) * m) := by
      calc k * Nat.card (swapFix G a b s₀)
          ≤ Nat.card {h : G // h * h = 1 ∧ h • a = b} * Nat.card (swapFix G a b s₀) :=
            Nat.mul_le_mul_right _ hkle_inv
        _ ≤ 2 * Nat.card T := hinv
        _ = 2 * (Nat.card (swapFix G a b s₀) * m) := by rw [hm]
    have h2 : k ≤ 2 * m := by
      have : k * Nat.card (swapFix G a b s₀) ≤ (2 * m) * Nat.card (swapFix G a b s₀) := by
        calc k * Nat.card (swapFix G a b s₀) ≤ 2 * (Nat.card (swapFix G a b s₀) * m) := h1
          _ = (2 * m) * Nat.card (swapFix G a b s₀) := by ring
      exact Nat.le_of_mul_le_mul_right this hTspos
    omega
  have hsf := exponent_eq_of_count hp hslt (by rw [← hzs]; exact hcount) hk2
  rw [hzs, hsf]

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
