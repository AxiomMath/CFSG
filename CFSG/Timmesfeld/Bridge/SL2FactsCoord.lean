module

public import CFSG.Timmesfeld.Bridge.RootClosureL2Defs

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld CFSG.BenderSuzuki

theorem isPGroup_upperUnipotent {n : ℕ} (hn : n ≠ 0) :
    IsPGroup 2 (upperUnipotent (GaloisField 2 n)) :=
  IsPGroup.of_card (n := n) (by rw [RankOne.card_upperUnipotent, GaloisField.card 2 n hn])

theorem not_two_dvd_index_upperUnipotent {n : ℕ} (hn : n ≠ 0) :
    ¬ 2 ∣ (upperUnipotent (GaloisField 2 n)).index := by
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n hn]
  have hS : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
      2 ^ n * (2 ^ n * 2 ^ n - 1) := by
    have h2n : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hn)
    rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have h2 : (2 ^ n) ^ 2 - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by
      rw [Nat.mul_sub_one, sq]
    rw [h2, ← mul_assoc, Nat.mul_div_cancel _ (by omega), sq, mul_comm]
  have hmul := Subgroup.card_mul_index (upperUnipotent (GaloisField 2 n))
  rw [RankOne.card_upperUnipotent, GaloisField.card 2 n hn, hS] at hmul
  have hidx : (upperUnipotent (GaloisField 2 n)).index = 2 ^ n * 2 ^ n - 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  rw [hidx]
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
  have h4 : 2 ∣ 2 ^ n * 2 ^ n := h2.mul_right _
  have h1 : 1 ≤ 2 ^ n * 2 ^ n := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

theorem psl2SylowCoordStmt : PSL2SylowCoordStmt := by
  intro n hn L _ ⟨e⟩ P
  have hn0 : n ≠ 0 := by omega
  have : Finite L := Finite.of_equiv _ e.toEquiv.symm
  let ψ : L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    e.trans (RankOne.psl2EquivSL2 (GaloisField 2 n))
  let U : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    (isPGroup_upperUnipotent hn0).toSylow (not_two_dvd_index_upperUnipotent hn0)
  let P' : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Sylow.mapSurjective (f := ψ.toMonoidHom) ψ.surjective P
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) P' U
  refine ⟨ψ.trans (MulAut.conj g), ?_⟩
  have hφ : (ψ.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp ψ.toMonoidHom := MonoidHom.ext fun _ => rfl
  have hP' : (P' : Subgroup _) = (P : Subgroup L).map ψ.toMonoidHom :=
    Sylow.coe_mapSurjective (f := ψ.toMonoidHom) ψ.surjective P
  have h := congrArg Sylow.toSubgroup hg
  rw [Sylow.coe_subgroup_smul, hP', IsPGroup.toSylow_coe] at h
  rw [hφ, ← Subgroup.map_map]
  exact h

end CFSG.Timmesfeld.Bridge.RootClosure
