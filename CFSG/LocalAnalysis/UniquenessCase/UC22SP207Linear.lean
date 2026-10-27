module

import CFSG.LocalAnalysis.UniquenessCase.UC22SP207LinCuts
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207LinFlag
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207LinOpp
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207LinTorus
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem uc22sp207_linear {m n : ℕ} (hm : m = 3 ∨ m = 4) (hn : 2 < n) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n) {X : Type} [Group X] [Finite X]
    (α : SpecialLinearGroup (Fin m) K →* X) (hα : Function.Surjective α)
    (hαc : α.ker ≤ center (SpecialLinearGroup (Fin m) K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup X} (hY : IsParabolicTwo X Y) (hYp : IsStronglyPEmbedded p Y) :
    ¬ 2 ^ n ≡ 1 [MOD p] ∧
      Nonempty (↥(Opp p (⊤ : Subgroup (Bar2 Y))) ≃*
        CFSG.Open.StatedSL (m - 1) (GaloisField 2 n)) := by
  have hm1 : 1 ≤ m := by omega
  obtain ⟨S, hS⟩ := hY
  obtain ⟨c, hc⟩ := uc22sp207_exists_conj_cover hm1 α hα S
  set α' : SpecialLinearGroup (Fin m) K →* X := (MulAut.conj c).toMonoidHom.comp α with hα'
  have hα's : Function.Surjective α' := (MulAut.conj c).surjective.comp hα
  have hα'c : α'.ker ≤ center (SpecialLinearGroup (Fin m) K) := fun x hx =>
    hαc (MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff (MulAut.conj c)).1 hx))
  obtain ⟨hcuts, hYI⟩ := uc22sp207_comap_eq_flagStabilizer hm1 α' hc hS
  obtain ⟨d, hd, hdI⟩ : ∃ d, (d = 1 ∨ d = m - 1) ∧
      LinearFlag.borelOvergroupCuts (Y.comap α') = {d} := by
    rcases uc22sp207_cuts hm α' hα's hcuts hYI hp hp2 hYp with h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨m - 1, Or.inr rfl, h⟩
  have hd1 : 1 ≤ d ∧ d < m := by omega
  have hdQ : Y.comap α' = LinearFlag.stabilizer (LinearFlag.flagSpace m K d) := by
    rw [hYI, hdI, LinearFlag.flagStabilizer_singleton]
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    uc22sp207_not_dvd_card_sub_one (by omega) α' hα'c (hdI ▸ Set.mem_singleton d) hd1.1 hd1.2
      hYI hp hYp
  refine ⟨fun hmod => hpq ?_, uc22sp207_opp_bar2 hm hd hn hK α' hα's hα'c hdQ hp hp2 hpq hYp.2.1⟩
  rw [hK]
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 hmod.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
