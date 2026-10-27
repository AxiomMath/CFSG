module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

namespace CFSG.Quasithin.JonesParshall

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] {μ : G →* AddMonoid.End M}

theorem odd_nsmul_eq {n : ℕ} (hn : Odd n) (h2 : ∀ m : M, m + m = 0) (m : M) : n • m = m := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul, two_nsmul, h2, nsmul_zero, zero_add]

theorem exists_equivariant {T : Type*} [Group T] [Fintype T] (ι : T →* G)
    (hodd : Odd (Fintype.card T)) (h2 : ∀ m : M, m + m = 0) {f : G → M} (hf : f ∈ Z1A μ) :
    ∃ ψ ∈ Z1A μ, f - ψ ∈ B1A μ ∧
      ∀ (s : T) (g : G), ψ (ι s * g * (ι s)⁻¹) = μ (ι s) (ψ g) := by
  set m : M := ∑ t, f (ι t) with hm
  have key : ∀ s : T, μ (ι s) m = m - f (ι s) := fun s => by
    have h1 : μ (ι s) m = ∑ t, (f (ι (s * t)) - f (ι s)) := by
      rw [hm, map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_mul, hf]
      abel
    have h3 : ∑ t, f (ι (s * t)) = m :=
      Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun _ => rfl
    rw [h1, Finset.sum_sub_distrib, h3, Finset.sum_const, Finset.card_univ,
      odd_nsmul_eq hodd h2]
  refine ⟨f + coboundaryA μ m, add_mem hf (B1A_le_Z1A μ ⟨m, rfl⟩), ?_, fun s g => ?_⟩
  · rw [sub_add_cancel_left]
    exact neg_mem ⟨m, rfl⟩
  · have e1 : μ (ι s * g * (ι s)⁻¹) m - μ (ι s * g * (ι s)⁻¹) (f (ι s)) =
        μ (ι s) (μ g m) := by
      rw [← map_sub, ← key]
      change (μ (ι s * g * (ι s)⁻¹) * μ (ι s)) m = (μ (ι s) * μ g) m
      rw [← map_mul, ← map_mul, inv_mul_cancel_right]
    simp only [Pi.add_apply, coboundaryA_apply]
    rw [Z1A_conj hf, map_add, map_sub, ← e1, key]
    abel

end CFSG.Quasithin.JonesParshall
