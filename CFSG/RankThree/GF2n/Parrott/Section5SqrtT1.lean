module

public import CFSG.GroupTheory.QuaternionQuotientSquareRoots
public import CFSG.RankThree.GF2n.Parrott.Section5NoE16T1

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem mem_commutator_or_ncard_sqrt_ne_of_isSylowOf_centralizer_sigma1Nine
    (h : Tim79a.ParrottHyp z) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)))
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    {t : G} (htJ : t ∉ J z) :
    z₁ ∈ ⁅T₁, T₁⁆ ∨
      {k : G | k ∈ T₁ ∧ k * k = z}.ncard ≠ {k : G | k ∈ T₁ ∧ k * k = t}.ncard ∨
      {k : G | k ∈ T₁ ∧ k * k = z}.ncard ≠ {k : G | k ∈ T₁ ∧ k * k = t * z}.ncard := by
  have hNT := J_inf_centralizer_le_of_isSylowOf h hT₁
  have hZN := centerIn_J_inf_centralizer_sigma1Nine_eq (z := z) D h
  obtain ⟨π, hπ, hker⟩ := exists_quaternion_quotient_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  obtain ⟨ρ, hρK, hρT, hρ3, g, hgT, hg⟩ :=
    exists_pow_three_eq_one_normalizes_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  have hz1 : z ≠ 1 := by
    intro hz
    have h2 := h.1
    rw [hz, orderOf_one] at h2
    exact absurd h2 (by decide)
  refine mem_commutator_or_ncard_sqrt_ne_of_quaternion_quotient hNT
    (fun c hc n hn => conj_mem_J_inf_centralizer (hT₁.le hc) hn) π hπ hker
    (card_J_inf_centralizer_sigma1Nine (z := z) D h) (by rw [hZN]; exact card_centerIn_J h)
    (by rw [hZN]; exact fun x hx => centerIn_J_sq h hx) (by rw [hZN]; exact z_mem_centerIn_J h)
    hz1 (by rw [hZN]; exact hz₁) (fun h1 => hz₁z (by rw [h1]; exact Subgroup.one_mem _))
    (fun h1 => hz₁z (by rw [h1]; exact Subgroup.mem_zpowers z))
    (fun n hn => mul_self_eq_one_or_eq_of_mem_J h (mem_inf.mp hn).1)
    (fun x hx y hy => commutator_eq_one_or_eq_of_mem_J h (mem_inf.mp hx).1 (mem_inf.mp hy).1)
    hρT (fun n hn => conj_mem_J_inf_centralizer hρK hn)
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hρK).1) hρ3
    ⟨g, hgT, fun hmem => hg (mem_inf.mp hmem).1⟩ (fun hmem => htJ (mem_inf.mp hmem).1)

end CFSG.RankThree.GF2n.Parrott
