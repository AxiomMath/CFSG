module

public import CFSG.RankThree.GF2n.Parrott.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_conjugate_iff {P : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate P g ↔ g * x * g⁻¹ ∈ P := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hp
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem prop4_fusion {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) (hPne : P ≠ ⊥) (hPH : P ≤ H z)
    (hstar : ∀ g : G, CFSG.conjugate P g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate P g = CFSG.conjugate P h)
    {t : G} (ht2 : orderOf t = 2) (htH : t ∈ H z)
    (htP : ∀ x ∈ P, t * x = x * t) :
    (∃ g : G, g⁻¹ * t * g = z) ↔
      ∃ n : G, n ∈ Subgroup.normalizer (P : Set G) ∧ n * t * n⁻¹ = z := by
  constructor
  · rintro ⟨g, hg⟩
    have hconj_le : CFSG.conjugate P g ≤ H z := by
      intro x hx
      rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have hx' : g * x * g⁻¹ ∈ P := mem_conjugate_iff.mp hx
      have ht_x : t * (g * x * g⁻¹) = (g * x * g⁻¹) * t := htP (g * x * g⁻¹) hx'
      calc x * z = x * (g⁻¹ * t * g) := by rw [hg]
        _ = g⁻¹ * ((g * x * g⁻¹) * t) * g := by group
        _ = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [ht_x]
        _ = z * x := by rw [← hg]; group
    obtain ⟨h, hhH, hheq⟩ := hstar g hconj_le
    have hz_h : z * h = h * z := by
      rw [H_eq_centralizer] at hhH
      exact (Subgroup.mem_centralizer_singleton_iff.mp hhH).symm
    refine ⟨h * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hxP
        have hgx : g⁻¹ * x * g ∈ CFSG.conjugate P g := by
          rw [mem_conjugate_iff]
          simpa [mul_assoc] using hxP
        rw [hheq] at hgx
        have hmem : h * (g⁻¹ * x * g) * h⁻¹ ∈ P := mem_conjugate_iff.mp hgx
        have hcalc : (h * g⁻¹) * x * (h * g⁻¹)⁻¹ = h * (g⁻¹ * x * g) * h⁻¹ := by group
        rw [hcalc]
        exact hmem
      · intro hxP
        have hmem : g⁻¹ * x * g ∈ CFSG.conjugate P g := by
          rw [hheq, mem_conjugate_iff]
          have hcalc : h * (g⁻¹ * x * g) * h⁻¹ = (h * g⁻¹) * x * (h * g⁻¹)⁻¹ := by group
          rw [hcalc]
          exact hxP
        simpa [mul_assoc] using mem_conjugate_iff.mp hmem
    · calc (h * g⁻¹) * t * (h * g⁻¹)⁻¹ = h * (g⁻¹ * t * g) * h⁻¹ := by group
        _ = h * z * h⁻¹ := by rw [hg]
        _ = z := by rw [← hz_h]; group
  · rintro ⟨n, -, hn⟩
    exact ⟨n⁻¹, by simpa using hn⟩



theorem prop4_fusion_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) (hPne : P ≠ ⊥) (hPH : P ≤ H z)
    (hstar : ∀ g : G, CFSG.conjugate P g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate P g = CFSG.conjugate P h)
    (hN : ∀ n ∈ Subgroup.normalizer (P : Set G),
      ∃ h ∈ Subgroup.normalizer (P : Set G) ⊓ H z,
      ∃ c ∈ Subgroup.centralizer (P : Set G), h * c = n)
    {t : G} (ht2 : orderOf t = 2) (htH : t ∈ H z)
    (htP : ∀ x ∈ P, t * x = x * t) :
    (∃ g : G, g⁻¹ * t * g = z) ↔
      ∃ c : G, c ∈ Subgroup.centralizer (P : Set G) ∧ c * t * c⁻¹ = z := by
  constructor
  · intro hconj
    obtain ⟨n, hnN, hn⟩ := (prop4_fusion hp hp2 hP hPne hPH hstar ht2 htH htP).mp hconj
    obtain ⟨h, hh, c, hc, rfl⟩ := hN n hnN
    have hhH : h ∈ H z := hh.2
    have hz_h : z * h = h * z := by
      rw [H_eq_centralizer] at hhH
      exact (Subgroup.mem_centralizer_singleton_iff.mp hhH).symm
    refine ⟨c, hc, ?_⟩
    calc c * t * c⁻¹ = h⁻¹ * ((h * c) * t * (h * c)⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [hn]
      _ = z := by rw [mul_assoc, hz_h]; group
  · rintro ⟨c, -, hc⟩
    exact ⟨c⁻¹, by simpa using hc⟩

end CFSG.RankThree.GF2n.Parrott
