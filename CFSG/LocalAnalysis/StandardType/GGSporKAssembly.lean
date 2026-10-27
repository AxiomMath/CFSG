module

public import CFSG.LocalAnalysis.StandardType.GGSporKPairs

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggSporK_card_mulAut_eq {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hInn : ∀ φ : MulAut K, ∃ g : K, φ = MulAut.conj g) :
    Nat.card (MulAut K) = Nat.card K := by
  have hcenter : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have ha : a ∈ Subgroup.center K := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := congrArg (fun φ : MulAut K => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      have h1 : g * h = h * g := by
        calc g * h = (g * h * g⁻¹) * g := by group
          _ = h * g := by rw [this]
      exact h1.symm
    rw [hcenter, Subgroup.mem_bot] at hmem
    exact hmem
  have hsurj : Function.Surjective (MulAut.conj : K →* MulAut K) := fun φ => by
    obtain ⟨g, hg⟩ := hInn φ
    exact ⟨g, hg.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

theorem ggSporK_pair_of_not_sq_dvd_card (s : TauCeti.SporadicName) (p : ℕ)
    [Finite (TauCeti.CFSGIndex.sporadic s).Group]
    (hInn : ∀ φ : MulAut (TauCeti.CFSGIndex.sporadic s).Group, ∃ g, φ = MulAut.conj g)
    (hp : ¬ p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group) :
    GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨e⟩ := he
  haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hyp.2.1.1
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := e.symm.isSimpleGroup
  have hnab : ∃ a b : (TauCeti.CFSGIndex.sporadic s).Group, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hyp.2.1.2.1
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hcard := ggSporK_card_mulAut_eq hnab hInn
  refine (hp ?_).elim
  have h2 : Nat.card E = q ^ 2 := hyp.1.2.2.2.1
  rw [← hcard, ← h2]
  exact (Subgroup.card_subgroup_dvd_card E).trans (ggSporK_card_dvd_aut hyp e)

theorem ggSporK_pair_of_not_odd_prime (s : TauCeti.SporadicName) (p : ℕ)
    (h : ¬ p.Prime ∨ p = 2) : GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  rcases h with h | h
  · exact absurd hyp.1.1 h
  · exact absurd h hyp.1.2.1

theorem ggSporK_sq_dvd_B {p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ 4154781481226426191177580544000000) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have hN : (4154781481226426191177580544000000 : ℕ) =
      2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47 := by norm_num
  have hpd : p ∣ 4154781481226426191177580544000000 := (dvd_pow_self p two_ne_zero).trans h
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
  rw [hN] at hpd
  simp only [hp.dvd_mul] at hpd
  rcases hpd with (((((((((h2 | h3) | h5) | h7) | h11) | h13) | h17) | h19) | h23) | h31) | h47
  · exact Or.inl (key 2 Nat.prime_two (hp.dvd_of_dvd_pow h2))
  · exact Or.inr (Or.inl (key 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)))
  · exact Or.inr (Or.inr (Or.inl (key 5 (by norm_num) (hp.dvd_of_dvd_pow h5))))
  · exact Or.inr (Or.inr (Or.inr (key 7 (by norm_num) (hp.dvd_of_dvd_pow h7))))
  · exfalso; rw [key 11 (by norm_num) h11] at h; revert h; norm_num
  · exfalso; rw [key 13 (by norm_num) h13] at h; revert h; norm_num
  · exfalso; rw [key 17 (by norm_num) h17] at h; revert h; norm_num
  · exfalso; rw [key 19 (by norm_num) h19] at h; revert h; norm_num
  · exfalso; rw [key 23 (by norm_num) h23] at h; revert h; norm_num
  · exfalso; rw [key 31 (by norm_num) h31] at h; revert h; norm_num
  · exfalso; rw [key 47 (by norm_num) h47] at h; revert h; norm_num

theorem ggSporK_sq_dvd_M {p : ℕ} (hp : p.Prime)
    (h : p ^ 2 ∣ 808017424794512875886459904961710757005754368000000000) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
  have hN : (808017424794512875886459904961710757005754368000000000 : ℕ) =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 *
        71 := by norm_num
  have hpd : p ∣ 808017424794512875886459904961710757005754368000000000 :=
    (dvd_pow_self p two_ne_zero).trans h
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
  rw [hN] at hpd
  simp only [hp.dvd_mul] at hpd
  rcases hpd with (((((((((((((h2 | h3) | h5) | h7) | h11) | h13) | h17) | h19) | h23) | h29) |
    h31) | h41) | h47) | h59) | h71
  · exact Or.inl (key 2 Nat.prime_two (hp.dvd_of_dvd_pow h2))
  · exact Or.inr (Or.inl (key 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)))
  · exact Or.inr (Or.inr (Or.inl (key 5 (by norm_num) (hp.dvd_of_dvd_pow h5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key 7 (by norm_num) (hp.dvd_of_dvd_pow h7)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 11 (by norm_num) (hp.dvd_of_dvd_pow h11))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key 13 (by norm_num) (hp.dvd_of_dvd_pow h13))))))
  · exfalso; rw [key 17 (by norm_num) h17] at h; revert h; norm_num
  · exfalso; rw [key 19 (by norm_num) h19] at h; revert h; norm_num
  · exfalso; rw [key 23 (by norm_num) h23] at h; revert h; norm_num
  · exfalso; rw [key 29 (by norm_num) h29] at h; revert h; norm_num
  · exfalso; rw [key 31 (by norm_num) h31] at h; revert h; norm_num
  · exfalso; rw [key 41 (by norm_num) h41] at h; revert h; norm_num
  · exfalso; rw [key 47 (by norm_num) h47] at h; revert h; norm_num
  · exfalso; rw [key 59 (by norm_num) h59] at h; revert h; norm_num
  · exfalso; rw [key 71 (by norm_num) h71] at h; revert h; norm_num

end CFSG.StandardType.SporadicShape
