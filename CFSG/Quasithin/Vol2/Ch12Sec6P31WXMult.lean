module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.P31X

theorem center_eq_bot_of_isPSL_two_even
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    {m : ℕ} (hm : 3 ≤ m) (h : CFSG.Quasithin.IsPSL 2 2 m (X ⧸ Subgroup.center X)) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ m := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hpow : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2m : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hk5 : 5 ≤ Fintype.card F := by
    rw [hFc]
    norm_num at hpow
    omega
  have hk9 : Fintype.card F ≠ 9 := by
    rw [hFc]
    intro h9
    rw [h9] at h2m
    norm_num at h2m
  have hgcd : Nat.gcd 2 (Fintype.card F - 1) = 1 := by
    rw [hFc, Nat.gcd_rec]
    have hodd : (2 ^ m - 1) % 2 = 1 := by
      have : 2 ^ m ≠ 0 := by positivity
      omega
    rw [hodd, Nat.gcd_one_left]
  have eP : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* (X ⧸ Subgroup.center X) :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm
  obtain ⟨-, ⟨hM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv hk5 hk9 eP
  rw [hgcd] at hM
  have hsub : Subsingleton (CFSG.Open.griessHopfMultiplier (X ⧸ Subgroup.center X)) := by
    refine ⟨fun a b => ?_⟩
    exact hM.injective (Subsingleton.elim _ _)
  exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_of_hopf_subsingleton hq
    (MulEquiv.refl _) hsub

end CFSG.Quasithin.H13.P31X
