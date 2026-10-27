module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2TwoOrder

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.ComponentClassification.CatLeaf
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

@[expose] def Asch58SmallParabolic (t : StatedLieTag) (n f : ℕ) : Prop :=
  t = .PSL ∧ (n = 2 ∧ f = 2 ∨ n = 3 ∧ (f = 1 ∨ f = 2)) ∨ t = .PSp ∧ n = 2 ∧ f = 2 ∨
    t = .PSU ∧ n = 3 ∧ f = 2 ∨ t = .Tits

theorem not_hasCompFactor_of_sylow_le_small (hO : LieOrderFormulasInput) {X : Type} [Group X]
    [Finite X] [IsSimpleGroup X] {t : StatedLieTag} {n f : ℕ}
    (hm : CFSG.Blueprint.LieModel X t n 2 f) (hs : Asch58SmallParabolic t n f) (S : Sylow 2 X)
    {Y : Subgroup X} (hSY : (S : Subgroup X) ≤ Y) (hY : Y < ⊤) : ¬ HasCompFactor Y IsCalL0 := by
  rcases hs with hPSL | hPSp | hPSU | hTits
  · obtain ⟨rfl, hcases⟩ := hPSL
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, hf⟩
    ·
      obtain ⟨-, hord, -⟩ := hO X .PSL 2 2 2 hm.admissible hm
      have hcard : Nat.card X = 60 := by
        rw [show lieOrderNumerator .PSL 2 (2 ^ 2) = 60 by decide +kernel,
          show lieOrderDivisor .PSL 2 (2 ^ 2) = 1 by decide +kernel] at hord
        simpa using hord
      exact not_hasCompFactor_isCalL0_of_dvd hO (k := 2) (by decide +kernel)
        (hcard ▸ Subgroup.card_subgroup_dvd_card Y)
    · rcases hf with rfl | rfl
      ·
        obtain ⟨-, hord, -⟩ := hO X .PSL 3 2 1 hm.admissible hm
        have hcard : Nat.card X = 168 := by
          rw [show lieOrderNumerator .PSL 3 (2 ^ 1) = 168 by decide +kernel,
            show lieOrderDivisor .PSL 3 (2 ^ 1) = 1 by decide +kernel] at hord
          simpa using hord
        exact not_hasCompFactor_isCalL0_of_dvd hO (k := 3) (by decide +kernel)
          (hcard ▸ Subgroup.card_subgroup_dvd_card Y)
      ·
        obtain ⟨-, hord, -⟩ := hO X .PSL 3 2 2 hm.admissible hm
        have hcard : Nat.card X = 20160 := by
          rw [show lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 by decide +kernel,
            show lieOrderDivisor .PSL 3 (2 ^ 2) = 3 by decide +kernel] at hord
          omega
        have hov : overgroupCheck 6 (Nat.card X) 7 = true := by
          rw [hcard]
          decide +kernel
        have hdv : 7 ∣ Nat.card X := by
          rw [hcard]
          decide +kernel
        exact not_hasCompFactor_isCalL0_of_overgroupCheck hO (k := 6) (p := 7)
          Nat.prime_seven hdv hov S hSY hY
  ·
    obtain ⟨rfl, rfl, rfl⟩ := hPSp
    obtain ⟨-, hord, -⟩ := hO X .PSp 2 2 2 hm.admissible hm
    have hcard : Nat.card X = 979200 := by
      rw [show lieOrderNumerator .PSp 2 (2 ^ 2) = 979200 by decide +kernel,
        show lieOrderDivisor .PSp 2 (2 ^ 2) = 1 by decide +kernel] at hord
      simpa using hord
    have hov : overgroupCheck 8 (Nat.card X) 17 = true := by
      rw [hcard]
      decide +kernel
    have hdv : 17 ∣ Nat.card X := by
      rw [hcard]
      decide +kernel
    exact not_hasCompFactor_isCalL0_of_overgroupCheck hO (k := 8) (p := 17)
      (by decide +kernel : Nat.Prime 17) hdv hov S hSY hY
  ·
    obtain ⟨rfl, rfl, rfl⟩ := hPSU
    obtain ⟨-, hord, -⟩ := hO X .PSU 3 2 2 hm.admissible hm
    have hcard : Nat.card X = 62400 := by
      rw [show lieOrderNumerator .PSU 3 (2 ^ 2) = 62400 by decide +kernel,
        show lieOrderDivisor .PSU 3 (2 ^ 2) = 1 by decide +kernel] at hord
      simpa using hord
    exact not_hasCompFactor_isCalL0_of_dvd hO (k := 6) (by decide +kernel)
      (hcard ▸ Subgroup.card_subgroup_dvd_card Y)
  ·
    subst t
    obtain ⟨-, -, hn, -, hf⟩ := hm.admissible
    subst n
    subst f
    obtain ⟨-, hord, -⟩ := hO X .Tits 0 2 1 hm.admissible hm
    have hcard : Nat.card X = 17971200 := by
      rw [show lieOrderNumerator .Tits 0 (2 ^ 1) = 17971200 by decide +kernel,
        show lieOrderDivisor .Tits 0 (2 ^ 1) = 1 by decide +kernel] at hord
      simpa using hord
    exact not_hasCompFactor_isCalL0_of_dvd hO (k := 11) (by decide +kernel)
      (hcard ▸ Subgroup.card_subgroup_dvd_card Y)

end CFSG.LocalAnalysis.WeakClosure81
