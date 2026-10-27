module

public import CFSG.Quasithin.H13.KGLieTwSL3

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] [Finite V]

theorem factLieNineFourRow1321_holds : A5.FactLieNineFourRow1321 := by
  intro V _ _ hV2 G L v hB4 hc h
  obtain ⟨F, _, _, _, hF, hr⟩ := h
  have hF' : Nat.card F = 2 ^ (2 * 2) := hF
  have h16 : 16 < Nat.card ↥(hermSub 2 (Fin 3) F) := by
    have h1 := card_hermSub_ge hF' (i₀ := (0 : Fin 3)) (i₁ := 1) (by decide)
    have h2 := card_fix_ge hF'
    rw [hF'] at h1
    have h3 : 4 * 4 * 16 ≤ Nat.card {k : F // k ^ 2 ^ 2 = k} *
        Nat.card {k : F // k ^ 2 ^ 2 = k} * 2 ^ (2 * 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul h2 h2) le_rfl
    omega
  obtain ⟨T, hT⟩ := exists_twData hV2 hB4 hc hF' (usl3 F) (isPGroup_usl3 hF')
    (not_dvd_index_usl3 hF' (by norm_num)) (Or.inr h16) hr
  exact false_of_twData hF' (Or.inr rfl) det_stated3 (isPGroup_usl3 hF') (hi := 0) (lo := 2)
    (by decide) (fix_usl3 (by norm_num) hF') (chi_usl3 (by norm_num) hF') (wsl3 F)
    (twist_wsl3_E00 2) (twist_wsl3_one 2) hT (fun h => absurd h (by norm_num))

end CFSG.Quasithin.H13.KGLie
