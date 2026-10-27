module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

variable {G : Type} [Group G] [Finite G]

theorem frattini_isSylowIn {p : ℕ} [Fact p.Prime] {H Y S : Subgroup G} (hYH : Y ≤ H)
    (hY : (Y.subgroupOf H).Normal) (hS : IsSylowIn p S Y) :
    ∀ x ∈ H, ∃ y ∈ Y, ∃ n ∈ H, n ∈ normalizer (S : Set G) ∧ y * n = x := by
  intro x hx
  haveI := hY
  have hSY : S ≤ Y := hS.le
  have hSH : S ≤ H := hSY.trans hYH
  set N : Subgroup H := Y.subgroupOf H with hN
  have hSN : S.subgroupOf H ≤ N := fun z hz => hSY hz
  set S₁ : Subgroup N := (S.subgroupOf H).subgroupOf N with hS₁
  have hc1 : Nat.card S₁ = Nat.card S :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv).trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv)
  have hc2 : Nat.card N = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYH).toEquiv
  have hcard : Nat.card S₁ = p ^ (Nat.card N).factorization p := by
    rw [hc1, hc2]
    exact hS.card_eq
  let P : Sylow p N := Sylow.ofCard S₁ hcard
  have key := Sylow.normalizer_sup_eq_top P
  have hmap : (P : Subgroup N).map N.subtype = S.subgroupOf H := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, hSN hz⟩, hz, rfl⟩
  rw [hmap, sup_comm] at key
  have hx' : (⟨x, hx⟩ : H) ∈ N ⊔ normalizer ((S.subgroupOf H : Subgroup H) : Set H) := by
    rw [key]
    exact Subgroup.mem_top _
  obtain ⟨y', hy', n', hn', hxy⟩ := Subgroup.mem_sup_of_normal_left.1 hx'
  have hnorm : ((n' : H) : G) ∈ normalizer (S : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact ((mem_normalizer_iff.1 hn') ⟨g, hSH hg⟩).1 hg
    · intro hg
      have hgH : g ∈ H := by
        have h1 : ((n' : G))⁻¹ * ((n' : G) * g * (n' : G)⁻¹) * (n' : G) ∈ H :=
          H.mul_mem (H.mul_mem (H.inv_mem n'.2) (hSH hg)) n'.2
        simpa [mul_assoc] using h1
      exact ((mem_normalizer_iff.1 hn') ⟨g, hgH⟩).2 hg
  exact ⟨y', hy', n', n'.2, hnorm, by simpa using congrArg Subtype.val hxy⟩

end CFSG.LocalAnalysis.WeakClosure81
