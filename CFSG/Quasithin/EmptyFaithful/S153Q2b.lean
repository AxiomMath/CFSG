module

public import CFSG.Quasithin.EmptyFaithful.S153QDef

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q2

open scoped commutatorElement

section Faithful

variable {G : Type*} [Group G]

theorem eq_one_of_mem_zpowers {z j : G} {J : Subgroup G} (h3 : z ^ 3 = 1)
    (hj : j ∈ Subgroup.zpowers z) (hjJ : j ∈ J) (hzJ : z ∉ J) : j = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hj
  have hz1 : z ≠ 1 := fun h => hzJ (h ▸ J.one_mem)
  have ho : orderOf z = 3 := orderOf_eq_prime h3 hz1
  rw [← zpow_mod_orderOf, ho] at hjJ ⊢
  have : i % ((3 : ℕ) : ℤ) = 0 ∨ i % ((3 : ℕ) : ℤ) = 1 ∨ i % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases this with h | h | h
  · rw [h]; simp
  · rw [h] at hjJ; exact absurd (by simpa using hjJ) hzJ
  · rw [h] at hjJ
    have h2 : z ^ 2 ∈ J := by simpa using hjJ
    have h4 : (z ^ 2) ^ 2 ∈ J := J.pow_mem h2 2
    have : (z ^ 2) ^ 2 = z := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    exact absurd (this ▸ h4) hzJ

theorem eq_bot_of_normal {Γ Ah : Subgroup G} {z : G} (hG : HatGrp Γ Ah z) (J : Subgroup G)
    (hJA : J ≤ Ah) (hJn : ∀ g ∈ Ah, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hzJ : z ∉ J) : J = ⊥ := by
  obtain ⟨ψ, hψs, hψk⟩ := hG.psi
  have hJn' : (J.subgroupOf Ah).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hJn g g.2 n hn⟩
  have hN : ((J.subgroupOf Ah).map ψ).Normal := hJn'.map ψ hψs
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((J.subgroupOf Ah).map ψ) with h | h
  · rw [eq_bot_iff]
    intro j hj
    rw [Subgroup.mem_bot]
    refine eq_one_of_mem_zpowers hG.z_cube ?_ hj hzJ
    have : ψ ⟨j, hJA hj⟩ = 1 := by
      have hm : ψ ⟨j, hJA hj⟩ ∈ (J.subgroupOf Ah).map ψ :=
        Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 hj)
      rw [h] at hm
      exact hm
    exact (hψk _).1 this
  · exfalso
    apply hzJ
    have hdec : ∀ a ∈ Ah, ∃ x ∈ J, ∃ u ∈ Subgroup.zpowers z, a = x * u := by
      intro a ha
      have hm : ψ ⟨a, ha⟩ ∈ (J.subgroupOf Ah).map ψ := by rw [h]; trivial
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 hm
      refine ⟨x, Subgroup.mem_subgroupOf.1 hx, (x : G)⁻¹ * a, ?_, by simp⟩
      have : ψ (x⁻¹ * ⟨a, ha⟩) = 1 := by rw [map_mul, map_inv, hxa, inv_mul_cancel]
      simpa using (hψk _).1 this
    have hcen : ∀ g ∈ Ah, ∀ u ∈ Subgroup.zpowers z, Commute g u := by
      intro g hg u hu
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      exact (show Commute g z from hG.z_central g hg).zpow_right i
    have hzA : Subgroup.zpowers z ≤ Ah := (Subgroup.zpowers_le).2 hG.z_mem
    have hcomm : ∀ a ∈ Ah, ∀ b ∈ Ah, ⁅a, b⁆ ∈ J := by
      intro a ha b hb
      obtain ⟨x, hx, u, hu, rfl⟩ := hdec a ha
      obtain ⟨y, hy, v, hv, rfl⟩ := hdec b hb
      have hxA := hJA hx
      have hyA := hJA hy
      have c1 : Commute u (y * v) :=
        ((hcen y hyA u hu).symm).mul_right (hcen v (hzA hv) u hu).symm
      have c2 : Commute x v := hcen x hxA v hv
      have key : ⁅x * u, y * v⁆ = ⁅x, y⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul, c1.commutator_eq,
          commutatorElement_mul_right_eq_mul_conj, c2.commutator_eq]
        simp
      rw [key]
      exact J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)
    exact (hG.perfect.trans (Subgroup.commutator_le.2 hcomm)) hG.z_mem

end Faithful

end Q2

end S153Q

end CFSG.Quasithin
