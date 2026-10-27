module

public import CFSG.RankThree.PartOne.Q1327.GpConn
public import CFSG.RankThree.PartOne.K1320.L4Weyl

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec1322Fin CFSG.RankThree.PartOne.Sec1322
  CFSG.RankThree.PartOne.K1320

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 100000

variable {G : Type} [Group G] [Finite G]

section BridgeConn

variable {p : ℕ} {E : Subgroup G} (B : Bridge p E)

include B

theorem bridge_conn {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hcard : Nat.card E = p ^ 3) {a b z : MulAut E} (ha : a ∈ reflectionSet p E)
    (hb : b ∈ reflectionSet p E) (hz : z ∈ reflectionSet p E) (hab : orderOf (a * b) = 4)
    (cas : a * z = z * a) (cbs : b * z = z * b) (hza : z ≠ a) (hzb : z ≠ b)
    (hzaba : z ≠ a * b * a⁻¹) (hzbab : z ≠ b * a * b⁻¹)
    (hzconj : ∃ g ∈ reflectionGroup p E, g * b * g⁻¹ = z) {x : MulAut E}
    (hx : ∃ g ∈ reflectionGroup p E, g * a * g⁻¹ = x) :
    x = a ∨ a * x ≠ x * a ∨ ∃ u : MulAut E, (∃ g ∈ reflectionGroup p E, g * a * g⁻¹ = u) ∧
      a * u ≠ u * a ∧ x * u ≠ u * x := by
  obtain ⟨a', rfl, -, -, -⟩ := B.refl_data h hcard ha
  obtain ⟨b', rfl, -, -, -⟩ := B.refl_data h hcard hb
  obtain ⟨z', rfl, -, -, -⟩ := B.refl_data h hcard hz
  have hinv : ∀ g : Gp, B.φ g⁻¹ = (B.φ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have ho : orderOf (a' * b') = 4 := by
    rw [← orderOf_injective B.φ B.inj, map_mul]; exact hab
  have h4 : (a' * b') ^ 4 = 1 := by
    have := pow_orderOf_eq_one (a' * b')
    rwa [ho] at this
  have h2 : (a' * b') ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at this
    omega
  have hφcomm : ∀ x y : Gp, B.φ x * B.φ y = B.φ y * B.φ x → x * y = y * x := fun x y hxy =>
    B.inj (by rw [map_mul, map_mul]; exact hxy)
  have c1 : a' * z' = z' * a' := B.inj (by rw [map_mul, map_mul]; exact cas)
  have c2 : b' * z' = z' * b' := B.inj (by rw [map_mul, map_mul]; exact cbs)
  have n1 : z' ≠ a' := fun h1 => hza (by rw [h1])
  have n2 : z' ≠ b' := fun h1 => hzb (by rw [h1])
  have n3 : z' ≠ a' * b' * a'⁻¹ := fun h1 => hzaba (by rw [h1, map_mul, map_mul, hinv])
  have n4 : z' ≠ b' * a' * b'⁻¹ := fun h1 => hzbab (by rw [h1, map_mul, map_mul, hinv])
  have hconj' : ∃ g : Gp, g * b' * g⁻¹ = z' := by
    obtain ⟨g, hg, hgs⟩ := hzconj
    obtain ⟨g', rfl⟩ := B.surj g hg
    exact ⟨g', B.inj (by rw [map_mul, map_mul, hinv]; exact hgs)⟩
  obtain ⟨g, hgX, rfl⟩ := hx
  obtain ⟨g', rfl⟩ := B.surj g hgX
  have hxg : B.φ g' * B.φ a' * (B.φ g')⁻¹ = B.φ (g' * a' * g'⁻¹) := by
    rw [map_mul, map_mul, hinv]
  have key : ∀ y : Gp, (∃ g : Gp, g * a' * g⁻¹ = y) →
      y = a' ∨ a' * y ≠ y * a' ∨ ∃ u : Gp, (∃ g : Gp, g * a' * g⁻¹ = u) ∧ a' * u ≠ u * a' ∧
        y * u ≠ u * y := by
    intro y hy
    rcases B.shape with hshape | hshape
    · exact gp_conn1 a' b' z' ((hshape a').1 ha) ((hshape b').1 hb) h4 h2 ((hshape z').1 hz) c1 c2
        n1 n2 n3 n4 hconj' y hy
    · exact gp_conn2 a' b' z' ((hshape a').1 ha) ((hshape b').1 hb) h4 h2 ((hshape z').1 hz) c1 c2
        n1 n2 n3 n4 hconj' y hy
  rw [hxg]
  rcases key (g' * a' * g'⁻¹) ⟨g', rfl⟩ with h1 | h1 | ⟨u', ⟨g₂, hg₂⟩, hu1, hu2⟩
  · left
    rw [h1]
  · right
    left
    intro hc
    exact h1 (hφcomm _ _ hc)
  · right
    right
    refine ⟨B.φ u', ⟨B.φ g₂, B.mem g₂, ?_⟩, ?_, ?_⟩
    · rw [← hinv, ← map_mul, ← map_mul, hg₂]
    · intro hc
      exact hu1 (hφcomm _ _ hc)
    · intro hc
      exact hu2 (hφcomm _ _ hc)

end BridgeConn

end CFSG.RankThree.PartOne.Q1327
