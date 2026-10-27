module

public import CFSG.Quasithin.Background.F7TwoInvSp4Inner
public import CFSG.Quasithin.Background.F7TwoInvSp4Field
public import CFSG.Quasithin.Background.F7TwoInvSp4Odd
public import CFSG.Quasithin.Background.F7TwoInvSQTKFam

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedCatalog

theorem invAutGen_of_statedPSp4_even (hodd : InvAutGenSp4OddEta) {f : ℕ} (hf : 2 ≤ f)
    {S : Type} [Group S] (h : StatedClassicalModel S .PSp 2 2 f) (φ : MulAut S) (hφ2 : φ * φ = 1)
    (hφ1 : φ ≠ 1) : InvAutGen S φ := by
  obtain ⟨-, K, _, hfin, hK, ⟨e⟩⟩ := h
  have hch : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hs := isSimpleGroup_sp4_proj h4
  have hnonab := sp4_proj_nonabelian h4
  rw [← invAutGen_congr_iff e φ]
  have hβ2 : MulAut.congr e φ * MulAut.congr e φ = 1 := by rw [← map_mul, hφ2, map_one]
  have hβ1 : MulAut.congr e φ ≠ 1 := fun hh => hφ1 ((MulAut.congr e).injective (hh.trans
    (map_one _).symm))
  by_cases hin : MulAut.congr e φ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 K))
  · obtain ⟨g, hg2, hg1, hβg⟩ := exists_inner_involution hs hnonab hβ2 hβ1 hin
    rw [hβg, invAutGen_congr_iff]
    exact invAutGen_conj_of_sp4_involution hg2 hg1
  · rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨σ, k, hσ, hσσ, hβ⟩ := exists_field_involution (by omega) hK hfe hβ2 hin
      rw [hβ]
      refine (InvAutGen.conj_iff (SpChain.spInner 2 K k) _).1 ?_
      rw [fieldAut_eq_congr, invAutGen_congr_iff]
      exact invAutGen_sp4_fieldSp hf hK hσ hσσ
    · obtain ⟨m, rfl⟩ := hfo
      exact invAutGen_of_odd_outer hodd (by omega) hK (center_eq_bot_of_isSimpleGroup hs hnonab)
        (by rw [sq]; exact hβ2) hin

theorem invAutGenFamSp4Even_of_odd (hodd : InvAutGenSp4OddEta) : InvAutGenFamSp4Even := by
  intro f S _ _ hf h φ hφ2 hφ1
  exact invAutGen_of_statedPSp4_even hodd hf h φ hφ2 hφ1

theorem invAutGenSp4OddEta_proved : InvAutGenSp4OddEta :=
  fun _ _ _ _ _ hm hK => invAutGen_antiSp_eta hm hK

theorem invAutGenFamSp4Even_proved : InvAutGenFamSp4Even :=
  invAutGenFamSp4Even_of_odd invAutGenSp4OddEta_proved

end CFSG.Quasithin.F7Two
