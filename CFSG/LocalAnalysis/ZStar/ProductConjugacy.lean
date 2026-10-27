module

public import CFSG.LocalAnalysis.ZStar.DihedralCentralizer

public section

namespace CFSG

namespace ZStar.ProductConjugacy

open ZStar.TransferReduction ZStar.DihedralCentralizer

universe u

private theorem exists_conjugator_mem_subgroup_of_involutions_odd_product
    {X : Type u} [Group X] {a b : X}
    (K : Subgroup X) (haK : a ∈ K) (hbK : b ∈ K)
    (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hodd : Odd (orderOf (a * b))) :
    ∃ c : X, c ∈ K ∧ c * a * c⁻¹ = b := by
  let aK : K := ⟨a, haK⟩
  let bK : K := ⟨b, hbK⟩
  have haK2 : aK * aK = 1 := by
    apply Subtype.ext
    exact ha2
  have hbK2 : bK * bK = 1 := by
    apply Subtype.ext
    exact hb2
  have hoddK : Odd (orderOf (aK * bK)) := by
    rw [← Subgroup.orderOf_coe (aK * bK)]
    simpa only [aK, bK, Subgroup.coe_mul, Subgroup.coe_mk] using hodd
  have hconjK : IsConj aK bK :=
    isConj_of_involutions_odd_product haK2 hbK2 hoddK
  obtain ⟨c, hc⟩ := isConj_iff.mp hconjK
  refine ⟨(c : X), c.property, ?_⟩
  exact congrArg Subtype.val hc

theorem product_isConj_of_isolated
    {X : Type u} [Group X] [Fintype X] {t σ μ : X}
    (ht : Isolated t) (ht2 : t * t = 1)
    (htσ : Commute t σ) (htμ : Commute t μ)
    (hσμ : IsConj σ μ) :
    IsConj (t * σ) (t * μ) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hσμ
  let a : X := g * t * g⁻¹
  let K : Subgroup X := Subgroup.centralizer ({μ} : Set X)
  have ha2 : a * a = 1 := by
    dsimp only [a]
    calc
      (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by
        group
      _ = 1 := by rw [ht2]; simp
  have haK : a ∈ K := by
    change a ∈ Subgroup.centralizer ({μ} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    dsimp only [a]
    rw [← hg]
    calc
      (g * t * g⁻¹) * (g * σ * g⁻¹) = g * (t * σ) * g⁻¹ := by group
      _ = g * (σ * t) * g⁻¹ := by rw [htσ.eq]
      _ = (g * σ * g⁻¹) * (g * t * g⁻¹) := by group
  have htK : t ∈ K := by
    change t ∈ Subgroup.centralizer ({μ} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact htμ.eq
  have hodd : Odd (orderOf (a * t)) := by
    simpa only [a] using odd_orderOf_conjugate_mul ht ht2 g
  obtain ⟨c, hcK, hcat⟩ :=
    exists_conjugator_mem_subgroup_of_involutions_odd_product
      K haK htK ha2 ht2 hodd
  have hcμ : Commute c μ := by
    change c ∈ Subgroup.centralizer ({μ} : Set X) at hcK
    rw [Subgroup.mem_centralizer_singleton_iff] at hcK
    exact hcK
  have hcμconj : c * μ * c⁻¹ = μ := by
    calc
      c * μ * c⁻¹ = μ * c * c⁻¹ := by rw [hcμ.eq]
      _ = μ := by group
  rw [isConj_iff]
  refine ⟨c * g, ?_⟩
  calc
    (c * g) * (t * σ) * (c * g)⁻¹ =
        c * (g * t * g⁻¹) * (g * σ * g⁻¹) * c⁻¹ := by group
    _ = c * a * μ * c⁻¹ := by
      dsimp only [a]
      rw [hg]
    _ = (c * a * c⁻¹) * (c * μ * c⁻¹) := by group
    _ = t * μ := by rw [hcat, hcμconj]

end ZStar.ProductConjugacy

end CFSG
