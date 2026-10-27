module

public import CFSG.RankThree.PartOne.K133C.UnitaryRad
public import CFSG.RankThree.PartOne.K133C.LinearLeaves
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.S13K
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem center_bot_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center X = ⊥) : Subgroup.center Y = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  have : e.symm c ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    have := hc (e y)
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this
  rw [h, Subgroup.mem_bot] at this
  have h2 := congrArg e this
  rwa [MulEquiv.apply_symm_apply, map_one] at h2

theorem radAut_of_model_PSU {X : Type} [Group X] {n m : ℕ} (hZ : Subgroup.center X = ⊥)
    (h : StatedClassicalModel X .PSU n 2 m) : RadAut X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 2 m K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ 2 ^ m = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact RadAut.of_mulEquiv e' (radAut_primeFormP hU hC hn3 hq (center_bot_of_mulEquiv' e' hZ))

theorem goodResV_of_model_PSU {X : Type} [Group X] {n m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center X = ⊥) (h : StatedClassicalModel X .PSU n 2 m) : GoodResV p X :=
  goodResV_of_radAut hp hp2 hZ (radAut_of_model_PSU hZ h)

theorem kf133ResMaxAt_leaf7_two (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf7 2) := by
  refine KF133ResMaxAt.of_goodResV hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e0
  rw [hq2] at hmod
  exact goodResV_of_model_PSU hp (by omega) (center_bot_of_simple hne) hmod

theorem kf133ResMaxAt_leaf7_six (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf7 6) := by
  refine KF133ResMaxAt.of_goodResV hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e0
  rw [hq2] at hmod
  exact goodResV_of_model_PSU hp (by omega) (center_bot_of_simple hne) hmod

theorem kf133ResMaxAt_leaf7_seven (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf7 7) := by
  refine KF133ResMaxAt.of_goodResV hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e0
  rw [hq2] at hmod
  exact goodResV_of_model_PSU hp (by omega) (center_bot_of_simple hne) hmod

end CFSG.RankThree.PartOne.K133C
