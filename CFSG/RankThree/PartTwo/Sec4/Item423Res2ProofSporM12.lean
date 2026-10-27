module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.GH74.M12.Hyp (G12)
open CFSG.RankThree.PartTwo.Toolkit.M12 (P0 basisE basisF)

namespace Res423Two

theorem card_P0_eq :
    Nat.card P0 = 3 ^ (Nat.card G12).factorization 3 := by
  rw [CFSG.RankThree.PartTwo.Toolkit.M12.card_P0]
  change 27 = 3 ^ (Nat.card NativeSporadic.M12).factorization 3
  rw [CFSG.Sporadic.Mathieu.card_M12, show (95040 : ℕ) = 3 ^ 3 * 3520 by norm_num,
    Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  norm_num

theorem nonempty_autIn_of_conj {X : Type} [Group X] (e : X ≃* G12) {D : Subgroup X}
    {B : Subgroup G12} (g : G12) (hD : D.map e.toMonoidHom = B.map (MulAut.conj g).toMonoidHom)
    (hB : Nonempty (CFSG.RankThree.Asc83Table.Automizer B ≃* Equiv.Perm (Fin 3))) :
    Nonempty (autIn (⊤ : Subgroup X) D ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨f⟩ := hB
  have f1 := Sporadic.autInTopCongr e D
  rw [hD] at f1
  exact ⟨f1.trans ((Sporadic.autInTopCongr (MulAut.conj g) B).symm.trans
    ((Sporadic.automizerEquivAutIn B).symm.trans f))⟩

theorem census423_of_m12
    {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* NativeSporadic.Carrier .M12) : Census423 X := by
  intro D hD hD9 Y hY hα
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e' : X ≃* G12 := e with he'
  set D' : Subgroup G12 := D.map e'.toMonoidHom with hD'
  have hD'e : CFSG.Assembly.IsElemAbelian 3 D' := isElemAbelian_map' _ hD.prop
  have hD'9 : Nat.card D' = 9 := by
    rw [hD', Subgroup.card_map_of_injective e'.injective, hD9]
  have hD'p : IsPGroup 3 D' := IsPGroup.of_card (n := 2) (by rw [hD'9]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card card_P0_eq hD'p
  set P' := D'.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'e : CFSG.Assembly.IsElemAbelian 3 P' := isElemAbelian_map' _ hD'e
  have hmem : P' ∈ {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9} :=
    ⟨Item434AltPerm.map_conj_inv_le hg,
      by rw [hP', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hD'9]⟩
  rw [CFSG.RankThree.PartTwo.Toolkit.M12.nine_eq] at hmem
  have hPeq : D' = P'.map (MulAut.conj g).toMonoidHom :=
    (Item434AltPerm.map_conj_map_conj_inv D' g).symm
  have hcomm := comm_of_isElemAbelian hD.prop
  have hne := ne_bot_of_card_nine hD9
  rcases hmem with h | h | h | h
  · exfalso
    apply hα
    rw [h] at hP'e
    have hNS : Item434SporGen.NoSignalizer D' := by
      rw [hPeq, h]
      exact (Item434SporGen.noSignalizer_E hP'e).map_conj g
    exact alphaVanishes_of_noSignalizer_mulEquiv hZ e' hcomm hne hNS Y hY
  · exfalso
    apply hα
    rw [h] at hP'e
    have hNS : Item434SporGen.NoSignalizer D' := by
      rw [hPeq, h]
      exact (Item434SporGen.noSignalizer_F hP'e).map_conj g
    exact alphaVanishes_of_noSignalizer_mulEquiv hZ e' hcomm hne hNS Y hY
  · refine Or.inr (Or.inr ⟨Or.inl ⟨e⟩, ?_⟩)
    rw [h] at hPeq
    exact nonempty_autIn_of_conj e' g hPeq CFSG.RankThree.PartTwo.Toolkit.M12.automizer_A
  · refine Or.inr (Or.inr ⟨Or.inl ⟨e⟩, ?_⟩)
    rw [Set.mem_singleton_iff] at h
    rw [h] at hPeq
    exact nonempty_autIn_of_conj e' g hPeq CFSG.RankThree.PartTwo.Toolkit.M12.automizer_A'

end Res423Two

end CFSG.RankThree.PartTwo.Sec4
