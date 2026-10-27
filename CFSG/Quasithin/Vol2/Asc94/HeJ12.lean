module

public import CFSG.Quasithin.Vol2.Asc94.HeJ11

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gl2_swap_inter : ∀ g s : GL2, g ^ 3 = 1 → g ≠ 1 → s * g * s⁻¹ = g⁻¹ →
    ∀ M M' : M2, g.val * M = M * g.val → g.val * M' = M' * g.val → M' = s.val * M → M = 0 := by
  set_option synthInstance.maxSize 1000 in
  set_option synthInstance.maxHeartbeats 200000 in
  decide +kernel

theorem gl2_swap_sum : ∀ g s : GL2, g ^ 3 = 1 → g ≠ 1 → s * g * s⁻¹ = g⁻¹ →
    ∀ M : M2, ∃ M₁ M₂ : M2, g.val * M₁ = M₁ * g.val ∧ g.val * M₂ = M₂ * g.val ∧
      M = M₁ + s.val * M₂ := by
  set_option synthInstance.maxSize 1000 in
  set_option synthInstance.maxHeartbeats 200000 in
  decide +kernel

section D40

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G} {a : G}
  (hD : Data40 A A' u w m N T a)

include hD

section X

variable {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)

include hxN hxa hx3

theorem Data40.exists_swap :
    ∃ n ∈ N, (∀ y ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G), ∀ y' ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G),
        y' = n * y * n⁻¹ → y = 1) ∧
      ∀ z ∈ A ⊓ A', ∃ y₁ ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G),
        ∃ y₂ ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G), z = y₁ * (n * y₂ * n⁻¹) := by
  set g := ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2) with hg
  have hg3 := hD.g_pow_three hxN hxa hx3
  have hg1 := hD.g_ne_one hxN hxa hx3
  obtain ⟨s, hs⟩ := gl2_exists_inverting g hg3
  obtain ⟨n, hn⟩ := hD.hT.rho_surjective hD.hK (s, 1)
  have hn1 : ((hD.hT.rho N hD.hK.norm n).1 : GL2) = s := by rw [hn]
  have hn2 : ((hD.hT.rho N hD.hK.norm n).2 : GL2) = 1 := by rw [hn]
  have hconj : ∀ y ∈ A ⊓ A', m ((n : G) * y * (n : G)⁻¹) = s.val * m y := by
    intro y hy
    rw [hD.hT.m_conj N hD.hK.norm n hy, hn1, hn2]
    simp
  refine ⟨n, n.2, ?_, ?_⟩
  · intro y hy y' hy' hyy
    have hyB := (hD.mem_B_iff hxN hxa hx3).1 hy
    have hy'B := (hD.mem_B_iff hxN hxa hx3).1 hy'
    have hm' : m y' = s.val * m y := by rw [hyy]; exact hconj y hyB.1
    have h0 := gl2_swap_inter g s hg3 hg1 hs (m y) (m y') hyB.2 hy'B.2 hm'
    exact hD.hT.minj _ hyB.1 _ (Subgroup.one_mem _) (by rw [h0, hD.hT.m_one])
  · intro z hz
    obtain ⟨M₁, M₂, h1, h2, hM⟩ := gl2_swap_sum g s hg3 hg1 hs (m z)
    obtain ⟨y₁, hy₁Z, hy₁m⟩ := hD.hT.msurj M₁
    obtain ⟨y₂, hy₂Z, hy₂m⟩ := hD.hT.msurj M₂
    have hy₁ : y₁ ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G) :=
      (hD.mem_B_iff hxN hxa hx3).2 ⟨hy₁Z, by rw [hy₁m]; exact h1⟩
    have hy₂ : y₂ ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G) :=
      (hD.mem_B_iff hxN hxa hx3).2 ⟨hy₂Z, by rw [hy₂m]; exact h2⟩
    refine ⟨y₁, hy₁, y₂, hy₂, ?_⟩
    have hZ2 : (n : G) * y₂ * (n : G)⁻¹ ∈ A ⊓ A' := hD.mem_Z_conj n.2 hy₂Z
    apply hD.hT.minj _ hz _ ((A ⊓ A').mul_mem hy₁Z hZ2)
    rw [hD.hT.mmul _ hy₁Z _ hZ2, hconj y₂ hy₂Z, hy₁m, hy₂m, ← hM]

end X

end D40

end CFSG.Quasithin.A94.HeJ
