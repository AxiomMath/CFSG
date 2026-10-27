module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_pCoreOf_centralizer (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer
        ((CFSG.Open.pCoreOf 2 (Subgroup.centralizer (V : Set G)) : Subgroup G) : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      m * c * m⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro m hm c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      refine (Subgroup.mem_normalizer_iff.mp hm (m⁻¹ * v * m)).2 ?_
      rwa [show m * (m⁻¹ * v * m) * m⁻¹ = v by group]
    have h1 := hc (m⁻¹ * v * m) hv'
    calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [h1]
      _ = m * c * m⁻¹ * v := by group
  refine le_trans ?_ (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
    (Subgroup.centralizer (V : Set G)))
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key n hn c hc, fun hc => ?_⟩
  have := key n⁻¹ (inv_mem hn) (n * c * n⁻¹) hc
  rwa [inv_inv, show n⁻¹ * (n * c * n⁻¹) * n = c by group] at this

theorem isPGroup_sup_of_le_normalizer {p : ℕ} [Fact p.Prime] {U P : Subgroup G}
    (hU : IsPGroup p U) (hP : IsPGroup p P) (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    IsPGroup p (U ⊔ P : Subgroup G) :=
  IsPGroup.to_sup_of_normal_left' hU hP hPU

theorem mem_normalizer_sup {U W : Subgroup G} {x : G}
    (hU : x ∈ Subgroup.normalizer (U : Set G)) (hW : x ∈ Subgroup.normalizer (W : Set G)) :
    x ∈ Subgroup.normalizer ((U ⊔ W : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hU hW ⊢
  rw [Subgroup.map_sup, hU, hW]

theorem disjoint_zpowers_of_not_mem {K B : Subgroup G} {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hdK : d ∉ K) (hBK : B ≤ K) : Disjoint (Subgroup.zpowers d) B := by
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  rw [Subgroup.disjoint_def]
  intro x hx hxB
  by_contra hx1
  have hxd : orderOf x ∣ 3 := by
    rw [← hord]
    exact orderOf_dvd_of_mem_zpowers hx
  have hx3 : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hxd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hx
  have hcard : Nat.card (Subgroup.zpowers d) ≤ Nat.card (Subgroup.zpowers x) :=
    le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hx3])
  have heq : Subgroup.zpowers x = Subgroup.zpowers d := Subgroup.eq_of_le_of_card_ge hle hcard
  have hdx : d ∈ Subgroup.zpowers x := by
    rw [heq]
    exact Subgroup.mem_zpowers d
  exact hdK (hBK ((Subgroup.zpowers_le.mpr hxB) hdx))

end CFSG.RankThree.PartTwo.Sec8.Hering611
