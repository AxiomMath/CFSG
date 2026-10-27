module

public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
public import CFSG.RankThree.OddKernel.SporadicKernelCases
public import CFSG.RankThree.PartOne.Mult.Alternating
public import CFSG.RankThree.PartOne.S11c.Sec68
public import CFSG.Models.PGL
public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

theorem not_dvd_forty_eight_of_three_lt {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) : ¬ r ∣ 48 := by
  intro h
  have hle : r ≤ 48 := Nat.le_of_dvd (by norm_num) h
  interval_cases r <;> revert hr h <;> norm_num

theorem false_of_kernel_trivial {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hdvd : r ∣ Nat.card (Subgroup.center K))
    (htriv : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
      (π : E →* K ⧸ Subgroup.center K), Function.Surjective π →
        π.ker ≤ Subgroup.center E → Nat.Coprime (Nat.card π.ker) 6 → π.ker = ⊥) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨N, _, π, hperf, -, hsurj, hker, hpg, hne⟩ :=
    CFSG.RankThree.PartOne.Mult.exists_central_p_extension (K := K) hdvd
  haveI : Group.IsPerfect (K ⧸ N) := hperf
  exact hne (htriv (K ⧸ N) π hsurj hker
    (CFSG.RankThree.PartOne.Mult.coprime_six_card_of_isPGroup hr hr3 hpg))

theorem not_dvd_card_center_of_type429
    (hGA : CFSG.Open.GriessAllModelsStatement) {K T : Type} [Group K] [Group T] [Finite K]
    (hK : CFSG.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* T)
    (hT : CFSG.RankThree.PartTwo.Sec14.Main148.Type429 T) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) :
    ¬ r ∣ Nat.card (Subgroup.center K) := by
  intro hdvd
  haveI : Group.IsPerfect K := hK.1
  rcases hT with hL | hA | hM12 | hM22 | hJ2
  · obtain ⟨p, f, hp, hf, hiso⟩ := hL
    have hK' : CFSG.RankThree.PartTwo.Sec4.IsoLThreePi (K ⧸ Subgroup.center K) p f := by
      rcases hiso with ⟨h1, ⟨ψ⟩⟩ | ⟨h2, ⟨ψ⟩⟩
      · exact Or.inl ⟨h1, ⟨e.trans ψ⟩⟩
      · exact Or.inr ⟨h2, ⟨e.trans ψ⟩⟩
    exact not_dvd_forty_eight_of_three_lt hr hr3
      (hdvd.trans (CFSG.RankThree.PartTwo.Sec4.Res417.card_center_dvd_forty_eight hGA hK hf hK'))
  · obtain ⟨φ⟩ := hA
    exact (CFSG.RankThree.PartOne.Mult.alternating_center_small_primes (by norm_num : 5 ≤ 7)
      (e.trans φ) hr hr3) hdvd
  · obtain ⟨φ⟩ := hM12
    have hS : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K)
        TauCeti.SporadicName.M12 := ⟨e.trans φ⟩
    exact false_of_kernel_trivial hr hr3 hdvd (by
      intro E _ _ _ π hπ hC h6
      exact CFSG.RankThree.OddKernel.ker_eq_bot_of_isSporadic_M12 π hπ hC h6 hS)
  · obtain ⟨φ⟩ := hM22
    have hS : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K)
        TauCeti.SporadicName.M22 := ⟨e.trans φ⟩
    exact false_of_kernel_trivial hr hr3 hdvd (by
      intro E _ _ _ π hπ hC h6
      exact CFSG.RankThree.OddKernel.ker_eq_bot_of_isSporadic_small π hπ hC h6
        (s := TauCeti.SporadicName.M22) (Or.inr (Or.inl rfl)) hS)
  · obtain ⟨φ⟩ := hJ2
    have hS : CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Subgroup.center K)
        TauCeti.SporadicName.J2 := ⟨e.trans φ⟩
    exact false_of_kernel_trivial hr hr3 hdvd (by
      intro E _ _ _ π hπ hC h6
      exact CFSG.RankThree.OddKernel.ker_eq_bot_of_isSporadic_J2 π hπ hC h6 hS)

theorem isPGroup_two_center_of_type429
    (hGA : CFSG.Open.GriessAllModelsStatement) {K T : Type} [Group K] [Group T] [Finite K]
    (hK : CFSG.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* T)
    (hT : CFSG.RankThree.PartTwo.Sec14.Main148.Type429 T)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center K)) : IsPGroup 2 (Subgroup.center K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Nat.card (Subgroup.center K) ≠ 0 := (Nat.card_pos).ne'
  refine IsPGroup.iff_card.mpr ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) hZ ?_⟩
  intro d hd hdvd
  by_contra hne
  rcases (show d = 3 ∨ 3 < d by have := hd.two_le; omega) with rfl | hd3
  · exact h3 hdvd
  · exact not_dvd_card_center_of_type429 hGA hK e hT hd hd3 hdvd

theorem center_eq_bot_of_wrong_sign_sl (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type}
    [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 2) (hq2 : p ^ f ≠ 2)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p f)) :
    Subgroup.center K = ⊥ := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 p f :=
    ⟨Fact.out, hf, by norm_num, by simp, by simp⟩
  have hmod := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hK hmod
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 p f = (1, 1) := by
    have h1 : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 p f =
        (Nat.gcd 3 (p ^ f - 1), 1) := rfl
    have h2 : Nat.gcd 3 (p ^ f - 1) = 1 := by
      rw [Nat.gcd_rec, show (p ^ f - 1) % 3 = 1 by omega] <;> norm_num
    rw [h1, h2]
  have hx : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [hg, hx] at hdvd
  have h1 : Nat.card (Subgroup.center K) ∣ 1 := by simpa using hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

theorem center_eq_bot_of_wrong_sign_su (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type}
    [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f)
    (e : K ⧸ Subgroup.center K ≃* CFSG.Assembly.RankThreeEven.projSU 3 p f) :
    Subgroup.center K = ⊥ := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 p f :=
    ⟨Fact.out, hf, le_refl 3, fun h3 => by have := (Prod.mk.inj h3).2; omega⟩
  have hmod := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e
  have hdvd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hK hmod
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 p f = (1, 1) := by
    have h1 : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 p f =
        (Nat.gcd 3 (p ^ f + 1), 1) := rfl
    have h2 : Nat.gcd 3 (p ^ f + 1) = 1 := by
      rw [Nat.gcd_rec, show (p ^ f + 1) % 3 = 2 by omega] <;> norm_num
    rw [h1, h2]
  have hx : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 p f = (1, 1) := rfl
  rw [hg, hx] at hdvd
  have h1 : Nat.card (Subgroup.center K) ∣ 1 := by simpa using hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
