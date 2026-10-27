module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H]

theorem parity_three_cosets {K G : Subgroup H} (hKG : K ≤ G) [Finite K]
    (hcard : Nat.card G = 3 * Nat.card K) {x : H} (hxG : x ∈ G) (hx : x ∉ K) (hx2 : x ^ 2 ∉ K)
    {g : H} (hg : g ∈ G) : g ∈ K ∨ x⁻¹ * g ∈ K ∨ x * g ∈ K := by
  classical
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hindex : (K.subgroupOf G).index = 3 := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf G)
    have h2 : Nat.card (K.subgroupOf G) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKG).toEquiv
    rw [h2, hcard] at h1
    have h3 : Nat.card K * (K.subgroupOf G).index = Nat.card K * 3 := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h3
  have hQ : Nat.card (↥G ⧸ K.subgroupOf G) = 3 := by rw [← Subgroup.index_eq_card]; exact hindex
  have : Finite (↥G ⧸ K.subgroupOf G) := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  have : Fintype (↥G ⧸ K.subgroupOf G) := Fintype.ofFinite _
  set q₀ : ↥G ⧸ K.subgroupOf G := QuotientGroup.mk 1 with hq₀
  set q₁ : ↥G ⧸ K.subgroupOf G := QuotientGroup.mk ⟨x, hxG⟩ with hq₁
  set q₂ : ↥G ⧸ K.subgroupOf G := QuotientGroup.mk ⟨x⁻¹, G.inv_mem hxG⟩ with hq₂
  have h01 : q₀ ≠ q₁ := by
    intro h
    rw [hq₀, hq₁, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simp at h
    exact hx h
  have h02 : q₀ ≠ q₂ := by
    intro h
    rw [hq₀, hq₂, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simp at h
    exact hx h
  have h12 : q₁ ≠ q₂ := by
    intro h
    rw [hq₁, hq₂, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    apply hx2
    have : ((⟨x, hxG⟩ : ↥G)⁻¹ * ⟨x⁻¹, G.inv_mem hxG⟩ : ↥G).1 = (x ^ 2)⁻¹ := by
      simp [pow_two, mul_inv_rev]
    rw [this] at h
    simpa using h
  have hS : ({q₀, q₁, q₂} : Finset (↥G ⧸ K.subgroupOf G)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_eq_three.2 ⟨q₀, q₁, q₂, h01, h02, h12, rfl⟩, ← Nat.card_eq_fintype_card, hQ]
  have hmem : (QuotientGroup.mk ⟨g, hg⟩ : ↥G ⧸ K.subgroupOf G) ∈
      ({q₀, q₁, q₂} : Finset (↥G ⧸ K.subgroupOf G)) := by
    rw [hS]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · left
    rw [hq₀, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simpa using K.inv_mem h
  · right; left
    rw [hq₁, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simpa [mul_inv_rev] using K.inv_mem h
  · right; right
    rw [hq₂, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simpa [mul_inv_rev] using K.inv_mem h

theorem parity_core {K G : Subgroup H} (hKG : K ≤ G) [Finite K]
    (hcard : Nat.card G = 3 * Nat.card K) {x : H} (hxG : x ∈ G) (hx : x ∉ K) (hx2 : x ^ 2 ∉ K) :
    ∃ ε : K →* Multiplicative (ZMod 2), ∀ z : K,
      (ε z = Multiplicative.ofAdd 1 ↔ x * z * x ∈ K) ∧ (ε z = 1 ↔ x⁻¹ * z * x ∈ K) := by
  classical
  have hex : ∀ z : K, x⁻¹ * z * x ∈ K ∨ x * z * x ∈ K := by
    intro z
    have hg : (z : H) * x ∈ G := G.mul_mem (hKG z.2) hxG
    rcases parity_three_cosets hKG hcard hxG hx hx2 hg with h | h | h
    · exact absurd (by simpa using K.mul_mem (K.inv_mem z.2) h) hx
    · left; simpa [mul_assoc] using h
    · right; simpa [mul_assoc] using h
  have hnot : ∀ z : K, ¬ (x⁻¹ * z * x ∈ K ∧ x * z * x ∈ K) := by
    rintro z ⟨h1, h2⟩
    apply hx2
    have : x ^ 2 = (x * z * x) * (x⁻¹ * z * x)⁻¹ := by rw [pow_two]; group
    rw [this]
    exact K.mul_mem h2 (K.inv_mem h1)
  have hFmul : ∀ z z' : K, x⁻¹ * z * x ∈ K → x⁻¹ * z' * x ∈ K → x⁻¹ * ↑(z * z') * x ∈ K := by
    intro z z' h1 h2
    have : x⁻¹ * ((z * z' : K) : H) * x = (x⁻¹ * z * x) * (x⁻¹ * z' * x) := by
      simp [mul_assoc]
    rw [this]
    exact K.mul_mem h1 h2
  have hFinv : ∀ z : K, x⁻¹ * z * x ∈ K → x⁻¹ * ↑(z⁻¹) * x ∈ K := by
    intro z h1
    have : x⁻¹ * ((z⁻¹ : K) : H) * x = (x⁻¹ * z * x)⁻¹ := by simp [mul_assoc]
    rw [this]
    exact K.inv_mem h1
  have hWinv : ∀ z : K, x * z * x ∈ K → x * ↑(z⁻¹) * x ∈ K := by
    intro z hz
    by_contra hcon
    rcases hex z⁻¹ with h | h
    · have := hFinv _ h
      rw [inv_inv] at this
      exact hnot z ⟨this, hz⟩
    · exact hcon h
  have hFWW : ∀ z z' : K, x * z * x ∈ K → x * z' * x ∈ K → x⁻¹ * ↑(z * z') * x ∈ K := by
    intro z z' h1 h2
    have h1' := hWinv z h1
    have : x⁻¹ * ((z * z' : K) : H) * x = (x * ((z⁻¹ : K) : H) * x)⁻¹ * (x * z' * x) := by
      simp [mul_assoc]
    rw [this]
    exact K.mul_mem (K.inv_mem h1') h2
  have hWF : ∀ z z' : K, x * z * x ∈ K → x⁻¹ * z' * x ∈ K → x * ↑(z * z') * x ∈ K := by
    intro z z' h1 h2
    have : x * ((z * z' : K) : H) * x = (x * z * x) * (x⁻¹ * z' * x) := by
      simp [mul_assoc]
    rw [this]
    exact K.mul_mem h1 h2
  have hFW : ∀ z z' : K, x⁻¹ * z * x ∈ K → x * z' * x ∈ K → x * ↑(z * z') * x ∈ K := by
    intro z z' h1 h2
    by_contra hcon
    rcases hex (z * z') with h | h
    · have h3 := hFmul _ _ (hFinv z h1) h
      have : z⁻¹ * (z * z') = z' := by simp
      rw [this] at h3
      exact hnot z' ⟨h3, h2⟩
    · exact hcon h
  have hone : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  let f : K → Multiplicative (ZMod 2) := fun z =>
    if x * z * x ∈ K then Multiplicative.ofAdd 1 else 1
  have hmul : ∀ z z' : K, f (z * z') = f z * f z' := by
    intro z z'
    by_cases hz : x * z * x ∈ K <;> by_cases hz' : x * z' * x ∈ K
    · have hf := hFWW z z' hz hz'
      have hw : ¬ x * ((z * z' : K) : H) * x ∈ K := fun hw => hnot _ ⟨hf, hw⟩
      simp only [f, hz, hz', hw, ↓reduceIte, hone]
    · have hf' : x⁻¹ * z' * x ∈ K := (hex z').resolve_right hz'
      have hw := hWF z z' hz hf'
      simp only [f, hz, hz', hw, ↓reduceIte, mul_one]
    · have hf : x⁻¹ * z * x ∈ K := (hex z).resolve_right hz
      have hw := hFW z z' hf hz'
      simp only [f, hz, hz', hw, ↓reduceIte, one_mul]
    · have hf : x⁻¹ * z * x ∈ K := (hex z).resolve_right hz
      have hf' : x⁻¹ * z' * x ∈ K := (hex z').resolve_right hz'
      have hw : ¬ x * ((z * z' : K) : H) * x ∈ K := fun hw => hnot _ ⟨hFmul z z' hf hf', hw⟩
      simp only [f, hz, hz', hw, ↓reduceIte, mul_one]
  refine ⟨MonoidHom.mk' f hmul, fun z => ?_⟩
  show (f z = Multiplicative.ofAdd 1 ↔ x * z * x ∈ K) ∧ (f z = 1 ↔ x⁻¹ * z * x ∈ K)
  by_cases hz : x * z * x ∈ K
  · have hf : ¬ x⁻¹ * z * x ∈ K := fun hf => hnot z ⟨hf, hz⟩
    have hfz : f z = Multiplicative.ofAdd 1 := by simp [f, hz]
    exact ⟨⟨fun _ => hz, fun _ => hfz⟩,
      ⟨fun h => absurd (hfz.symm.trans h) hne, fun hf' => absurd hf' hf⟩⟩
  · have hf : x⁻¹ * z * x ∈ K := (hex z).resolve_right hz
    have hfz : f z = 1 := by simp [f, hz]
    exact ⟨⟨fun h => absurd (hfz.symm.trans h).symm hne, fun hw => absurd hw hz⟩,
      ⟨fun _ => hf, fun _ => hfz⟩⟩

end CFSG.Quasithin.Fan86.Tutte
