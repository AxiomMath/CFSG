module

public import CFSG.LocalAnalysis.UniquenessCase.UC6ProjFive
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm

theorem kProjRep_A10 (J : Type) [Group J] (hq : CFSG.Open.IsQuasisimple J) (N : Subgroup J) [N.Normal]
    (hN : N ≤ center J) (hA : CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt (J ⧸ N) 10) (q : ℕ) (hqp : q.Prime)
    (hq5 : q ≠ 5) (d : ℕ) (hd : d ≤ 6)
    (f : J →* (Matrix.GeneralLinearGroup (Fin d) (ZMod q)) ⧸
      center (Matrix.GeneralLinearGroup (Fin d) (ZMod q))) : f = 1 := by
  obtain ⟨e⟩ := hA
  haveI : Fact q.Prime := ⟨hqp⟩
  have h5 : (5 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((5 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod q) q] at h'
    exact hq5 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_five).1 h')
  have hZ : center (J ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ center (alternatingGroup (Fin 10)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hex
    exact Subgroup.mem_bot.2 hex
  refine projRep_eq_one_of_five J hq N hN hZ (a := e.symm a₁) (b := e.symm a₂) (ν := e.symm ν₀)
    (by rw [← map_mul, a₁₂_comm, map_mul]) ?_ ?_ (by rw [← map_pow, a₁_pow, map_one])
    (by rw [← map_pow, a₂_pow, map_one]) ?_ h5 (by omega) f
  · rw [← map_inv, ← map_mul, ← map_mul, ν₀_a₁, pow_zero, mul_one, map_pow]
  · rw [← map_inv, ← map_mul, ← map_mul, ν₀_a₂, pow_zero, one_mul, map_pow]
  · intro s t hs ht hst h
    rw [← map_pow, ← map_pow, ← map_mul, MulEquiv.map_eq_one_iff] at h
    have h' := key_inj ⟨s, hs⟩ ⟨t, ht⟩ 0 0 (by simpa using h)
    simp only [Fin.ext_iff, Fin.val_zero] at h'
    omega

end CFSG.LocalAnalysis.UniquenessCase.UCK
