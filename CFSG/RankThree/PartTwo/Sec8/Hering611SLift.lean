module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SGenB
public import CFSG.RankThree.PartTwo.Sec11.FixedCentralizer
public import CFSG.RankThree.PartTwo.KFacts.K73Lines

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

private theorem closure_pair_pow_three {c d z : G} (hcd : c * d = d * c)
    (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1) (hz : z ∈ Subgroup.closure ({c, d} : Set G)) :
    z ^ 3 = 1 := by
  obtain ⟨i, j, -, -, rfl⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_pow_mul_pow_of_mem_closure_pair hcd hc3 hd3 hz
  have hc : Commute (c ^ i) (d ^ j) := (show Commute c d from hcd).pow_pow i j
  rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul, hc3, hd3,
    one_pow, one_pow, one_mul]

private theorem isPGroup_three_of_pow_three {H : Subgroup G} (h : ∀ x ∈ H, x ^ 3 = 1) :
    IsPGroup 3 H := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact h g.1 g.2

theorem exists_lift_fusion {L : Subgroup G} {b d : G} (hdN : d ∈ Subgroup.normalizer (L : Set G))
    (hd3 : d ^ 3 = 1) (hbL : b ∈ L) (hb3 : b ^ 3 = 1) (hbd : b * d = d * b) {u₀ : G}
    (hu₀ : u₀ ∈ L)
    (h1 : u₀⁻¹ * b * u₀ * b⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L)
    (h2 : u₀⁻¹ * d * u₀ * (d * b)⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L) :
    ∃ u ∈ L, u⁻¹ * b * u = b ∧ u⁻¹ * d * u = d * b := by
  set N : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hNdef
  set B : Subgroup G := Subgroup.closure ({b, d} : Set G) with hBdef
  have hNL : N ≤ L := Subgroup.map_subtype_le _
  have hN3 : ¬ 3 ∣ Nat.card N := CFSG.RankThree.PartTwo.Sec11.not_three_dvd_card_inSubgroup_theta L
  have hLN : L ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.le_normalizer_theta L
  have hbN : b ∈ Subgroup.normalizer (N : Set G) := hLN hbL
  have hdN' : d ∈ Subgroup.normalizer (N : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.normalizer_le_normalizer_theta L hdN
  have hu₀N : u₀ ∈ Subgroup.normalizer (N : Set G) := hLN hu₀
  have hu₀invN : u₀⁻¹ ∈ Subgroup.normalizer (N : Set G) := Subgroup.inv_mem _ hu₀N
  have hbB : b ∈ B := Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := Subgroup.subset_closure (Set.mem_insert_of_mem b (Set.mem_singleton d))
  have hdbB : d * b ∈ B := B.mul_mem hdB hbB
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := fun x hx => closure_pair_pow_three hbd hb3 hd3 hx
  have hBp : IsPGroup 3 B := isPGroup_three_of_pow_three hB3
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := by
    rw [hBdef, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]
      exact hbN
    · rw [hx]
      exact hdN'
  have hyB : ∀ x ∈ B, u₀⁻¹ * x * (u₀⁻¹)⁻¹ ∈ B ⊔ N := by
    have key : B ≤ (B ⊔ N).comap (MulAut.conj u₀⁻¹).toMonoidHom := by
      rw [hBdef, Subgroup.closure_le]
      rintro x (hx | hx)
      · rw [hx]
        show u₀⁻¹ * b * (u₀⁻¹)⁻¹ ∈ B ⊔ N
        rw [inv_inv]
        have e : u₀⁻¹ * b * u₀ = (u₀⁻¹ * b * u₀ * b⁻¹) * b := by group
        rw [e]
        exact (B ⊔ N).mul_mem ((le_sup_right : N ≤ B ⊔ N) h1)
          ((le_sup_left : B ≤ B ⊔ N) hbB)
      · rw [hx]
        show u₀⁻¹ * d * (u₀⁻¹)⁻¹ ∈ B ⊔ N
        rw [inv_inv]
        have e : u₀⁻¹ * d * u₀ = (u₀⁻¹ * d * u₀ * (d * b)⁻¹) * (d * b) := by group
        rw [e]
        exact (B ⊔ N).mul_mem ((le_sup_right : N ≤ B ⊔ N) h2)
          ((le_sup_left : B ≤ B ⊔ N) hdbB)
    exact fun x hx => key hx
  obtain ⟨n, hnN, hn⟩ := exists_mul_mem_normalizer hBp hN3 hBN hu₀invN hyB
  have hconjB : ∀ x ∈ B, u₀⁻¹ * n * x * (u₀⁻¹ * n)⁻¹ ∈ B := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have hconjN : ∀ s ∈ N, u₀⁻¹ * s * u₀ ∈ N := by
    intro s hs
    have := (Subgroup.mem_normalizer_iff.mp hu₀invN s).mp hs
    rwa [inv_inv] at this
  have hconjb : ∀ s ∈ N, b * s * b⁻¹ ∈ N := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp hbN s).mp hs
  have hconjd : ∀ s ∈ N, d * s * d⁻¹ ∈ N := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp hdN' s).mp hs
  have hnL : n ∈ L := hNL hnN
  have hninvN : n⁻¹ ∈ N := N.inv_mem hnN
  have he : n * (b * n⁻¹ * b⁻¹) ∈ N := N.mul_mem hnN (hconjb _ hninvN)
  have he' : n * (d * n⁻¹ * d⁻¹) ∈ N := N.mul_mem hnN (hconjd _ hninvN)
  have hu : (u₀⁻¹ * n)⁻¹ ∈ L := by
    rw [mul_inv_rev, inv_inv]
    exact L.mul_mem (L.inv_mem hnL) hu₀
  refine ⟨(u₀⁻¹ * n)⁻¹, hu, ?_, ?_⟩
  · rw [inv_inv]
    have hcB : u₀⁻¹ * n * b * (u₀⁻¹ * n)⁻¹ * b⁻¹ ∈ B :=
      B.mul_mem (hconjB b hbB) (B.inv_mem hbB)
    have hcN : u₀⁻¹ * n * b * (u₀⁻¹ * n)⁻¹ * b⁻¹ ∈ N := by
      have e : u₀⁻¹ * n * b * (u₀⁻¹ * n)⁻¹ * b⁻¹
          = (u₀⁻¹ * (n * (b * n⁻¹ * b⁻¹)) * u₀) * (u₀⁻¹ * b * u₀ * b⁻¹) := by
        group
      rw [e]
      exact N.mul_mem (hconjN _ he) h1
    exact mul_inv_eq_one.mp
      (CFSG.RankThree.PartTwo.Sec11.eq_one_of_mem_inSubgroup_theta (L := L) hcN
        (hB3 _ hcB))
  · rw [inv_inv]
    have hcB : u₀⁻¹ * n * d * (u₀⁻¹ * n)⁻¹ * (d * b)⁻¹ ∈ B :=
      B.mul_mem (hconjB d hdB) (B.inv_mem hdbB)
    have hcN : u₀⁻¹ * n * d * (u₀⁻¹ * n)⁻¹ * (d * b)⁻¹ ∈ N := by
      have e : u₀⁻¹ * n * d * (u₀⁻¹ * n)⁻¹ * (d * b)⁻¹
          = (u₀⁻¹ * (n * (d * n⁻¹ * d⁻¹)) * u₀) * (u₀⁻¹ * d * u₀ * (d * b)⁻¹) := by
        group
      rw [e]
      exact N.mul_mem (hconjN _ he') h2
    exact mul_inv_eq_one.mp
      (CFSG.RankThree.PartTwo.Sec11.eq_one_of_mem_inSubgroup_theta (L := L) hcN
        (hB3 _ hcB))

end CFSG.RankThree.PartTwo.Sec8.Hering611
