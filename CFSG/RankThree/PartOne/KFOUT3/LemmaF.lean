module

public import CFSG.RankThree.PartOne.KFOUT3.Conj
public import CFSG.RankThree.PartOne.N143.JFacts
public import CFSG.RankThree.PartOne.KFOUT3.Galois
public import CFSG.RankThree.PartOne.KFOUT3.JModel
public import CFSG.RankThree.PartOne.KFOUT3.Semilin

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143 CFSG.Assembly.LowTwoRank

theorem not_dvd_of_pow_three_mod {p k : ℕ} (hk3 : k ^ 3 % p = 1) : ¬ p ∣ k := by
  intro hd
  have : p ∣ k ^ 3 := dvd_pow hd (by norm_num)
  have h0 : k ^ 3 % p = 0 := Nat.mod_eq_zero_of_dvd this
  omega

theorem jLemmaF : JLemmaF := by
  intro G _ _ p A c J h f hpf hmodel z hz hz3 k hk1 hk3 hact
  have hf1 : 1 ≤ f := hmodel.1.2.1
  obtain ⟨K, hKf, hKfin, hchar, hK, ζ, hζ, ι, hmaps, honto⟩ := exists_model_of_JGood h hpf hmodel
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hz' : IsZeta p ζ := IsZeta.of_orderOf h5 hζ
  have hzN : z ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.1 hz).1
  have hTu : ∀ t ∈ Tof A J, z * t * z⁻¹ ∈ Tof A J := fun t ht => by
    rw [hact t ht]
    exact Subgroup.pow_mem _ ht k
  have hT := conjAut_Tbar (Tof_le_J h) ι hmaps honto hzN hTu
  have hk : ¬ p ∣ k := not_dvd_of_pow_three_mod hk3
  have hact' := conjAut_action (Tof_le_J h) ι honto hzN hact
  obtain ⟨π, ε, σ, c', hc', hform⟩ := exists_hasForm hz' (conjAut ι hzN) hT
  obtain ⟨-, hσ⟩ := scalar_action hp hz' hc' hform hk hact'
  have hσ2 : (σ ^ 2) (ζ : K) = (ζ : K) ^ (k ^ 2) := by
    rcases hσ with ⟨-, h1⟩ | ⟨-, h1⟩
    · rw [pow_two, RingAut.mul_apply, h1, map_pow, h1, ← pow_mul, pow_two]
    · rw [pow_two, RingAut.mul_apply, h1, map_inv₀, map_pow, h1, inv_pow, inv_inv, ← pow_mul,
        pow_two]
  have hσf : (σ ^ 2) ^ f = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, aut_pow_card hf1 hK σ, one_pow]
  have h1 := aut_pow_apply (σ ^ 2) hσ2 f
  rw [hσf, RingAut.one_apply] at h1
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hk3
      simp at hk3
    · exact h0
  have hm : 0 < (k ^ 2) ^ f := by positivity
  have h2 : ζ ^ (k ^ 2) ^ f = ζ := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact h1.symm
  have h3 : ζ ^ ((k ^ 2) ^ f - 1) = 1 := by
    have : ζ ^ ((k ^ 2) ^ f - 1) * ζ = ζ := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
      exact h2
    exact mul_eq_right.1 this
  rw [hz'.pow_eq_one_iff hp] at h3
  have h4 : (k ^ 2) ^ f % p = 1 := by
    obtain ⟨t, ht⟩ := h3
    have h6 : (k ^ 2) ^ f = p * t + 1 := by omega
    rw [h6, Nat.mul_add_mod, Nat.mod_eq_of_lt hp.one_lt]
  have h7 : k ^ (2 * f) % p = 1 := by rw [pow_mul]; exact h4
  have h8 := three_dvd_of_pow_mod hp hk1 hk3 h7
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h8)

end CFSG.RankThree.PartOne.KFOUT3
