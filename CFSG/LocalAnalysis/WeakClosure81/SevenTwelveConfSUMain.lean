module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfRoot
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSURad
public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem suConf_mul_self_of_rank_one {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (g : ↥(SUid (unitaryInvolution F 2 n) m))
    (hg : Matrix.rank (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) - 1) = 1) : g * g = 1 := by
  obtain ⟨e, -, he, rfl⟩ := suConf_exists_tv hF g hg
  exact suConfT_mul_self he

theorem exists_sevenTwelveConfig_suid {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 < n) {m : ℕ}
    (g : ↥(SUid (unitaryInvolution F 2 n) m))
    (hg : Matrix.rank (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) - 1) = 1) :
    ∃ (g₂ g₃ y : ↥(SUid (unitaryInvolution F 2 n) m))
      (W T : Subgroup ↥(SUid (unitaryInvolution F 2 n) m)),
      SevenTwelveConfig (Subgroup.zpowers g) g₂ g₃ y W T := by
  have hσ := isUnitaryInvolution_unitaryInvolution (K := F) (p := 2) (f := n) hF
  obtain ⟨e, he0, he, rfl⟩ := suConf_exists_tv hF g hg
  obtain ⟨f, hf, hef⟩ := exists_partner hσ he0 he
  obtain ⟨c, hcσ, hc0, hc1, m', j, hm, hj⟩ := exists_zech_unitary hF hn
  have hs : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have h3 : m = 3 → ∃ s : F, s ≠ 0 ∧ unitaryInvolution F 2 n s * s ≠ 1 := fun _ =>
    exists_norm_ne_one hF fun h2 => by
      have := Nat.pow_right_injective (le_refl 2) (h2.trans (pow_one 2).symm)
      omega
  exact ⟨_, _, _, _, _, sevenTwelveConfig_of_root (t := suConfT hσ e)
    (y := suConfY hσ e f c) (n := suConfN hσ e f c) (u := suConfU hσ f) (m := m') (j := j)
    (Q := suConfRad e) (suConfT_mul_self he) rfl (suConfU_eq he hf hef hcσ hc0)
    (suConfN_eq he hf hef hcσ hc0 hm) (suConf_zech he hf hef hcσ hc0 hj)
    (suConf_ne_t he hf hef hcσ hc0 hc1) (suConf_comm_tn he hf hef hcσ hc0)
    (suConf_comm_ytn he hf hef hcσ hc0) (isPGroup_suConfRad e)
    (by simpa [suConfT] using suTv_mem_suConfRad e hσ he 1 1 hs)
    (by
      rw [suConfT, suTv_conj hσ _ he hs, (suConfY_apply he hf hef hcσ hc0).1]
      exact suTv_mem_suConfRad e hσ he c 1 hs)
    (fun q hq => commute_suConfT_of_mem_suConfRad e hσ he hq)
    (mem_normalizer_suConfRad e hc0 (suConfY_apply he hf hef hcσ hc0).1)
    (fun H hn hQ => suConf_gen he hf hef hcσ hc0 (suConf_two_le he0 he) h3 H hn hQ)⟩

end CFSG.LocalAnalysis.WeakClosure81

end
