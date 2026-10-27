module

public import CFSG.Quasithin.Vol2.Asc94.HeJ12

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gl2_sq : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → g.val * g.val = 1 + g.val := by
  decide +kernel

section D40

variable {A A' : Subgroup G} {u w : G → V2} {m : G → M2} {N T : Subgroup G} {a : G}
  (hD : Data40 A A' u w m N T a)

include hD

theorem Data40.exists_rot (g : GL2) :
    ∃ n : G, n ∈ N ∧ ∀ y ∈ A ⊓ A', m (n * y * n⁻¹) = g.val * m y := by
  obtain ⟨n, hn⟩ := hD.hT.rho_surjective hD.hK (g, 1)
  refine ⟨n, n.2, fun y hy => ?_⟩
  rw [hD.hT.m_conj N hD.hK.norm n hy, hn]
  simp

section X

variable {x : G} (hxN : x ∈ N) (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)
  {b : G} (hb : b ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G)) (hb1 : b ≠ 1) (hba : b ≠ a)
  (hbm : m b = ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2).val)

include hxN hxa hx3 hb hb1 hba hbm

theorem Data40.exists_rot_B : ∃ n : G, n ∈ N ∧
    n ∈ normalizer (((A ⊓ A') ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ∧
    n * a * n⁻¹ = b ∧ n * b * n⁻¹ = a * b := by
  set g := ((hD.hT.rho N hD.hK.norm ⟨x, hxN⟩).1 : GL2) with hg
  have hg3 := hD.g_pow_three hxN hxa hx3
  have hg1 := hD.g_ne_one hxN hxa hx3
  obtain ⟨n, hnN, hconj⟩ := hD.exists_rot g
  have hbZ : b ∈ A ⊓ A' := hb.1
  have haZ : a ∈ A ⊓ A' := hD.ha
  have hnb : n * a * n⁻¹ = b := by
    apply hD.hT.minj _ (hD.mem_Z_conj hnN haZ) _ hbZ
    rw [hconj a haZ, hD.ham, mul_one, hbm]
  refine ⟨n, hnN, ?_, hnb, ?_⟩
  · apply Subgroup.mem_normalizer_fintype
    intro y hy
    have hy' := (hD.mem_B_iff hxN hxa hx3).1 hy
    show n * y * n⁻¹ ∈ (A ⊓ A') ⊓ centralizer ({x} : Set G)
    rw [hD.mem_B_iff hxN hxa hx3]
    refine ⟨hD.mem_Z_conj hnN hy'.1, ?_⟩
    rw [hconj y hy'.1]
    calc g.val * (g.val * m y) = g.val * (m y * g.val) := by rw [hy'.2]
      _ = (g.val * m y) * g.val := by rw [mul_assoc]
  · have hbZ' : n * b * n⁻¹ ∈ A ⊓ A' := hD.mem_Z_conj hnN hbZ
    apply hD.hT.minj _ hbZ' _ ((A ⊓ A').mul_mem haZ hbZ)
    rw [hconj b hbZ, hD.hT.mmul a haZ b hbZ, hD.ham, hbm]
    exact gl2_sq g hg3 hg1

end X

end D40

end CFSG.Quasithin.A94.HeJ
