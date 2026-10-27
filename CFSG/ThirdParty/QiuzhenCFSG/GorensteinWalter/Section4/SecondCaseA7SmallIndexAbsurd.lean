module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AmbientModel
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A maximal A₇-quotient subgroup cannot have index at most seven

The count estimate only needs to produce `M.index ≤ 7`.  Minimality makes
the ambient group simple, so the action on `G ⧸ M` is faithful.  The resulting
permutation embedding, together with `|M/O₂′(M)| = |A₇| = 2520`, gives the
small numerical contradiction.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_small_index_absurd
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (hindex : w.M.index ≤ 7) : False := by
  classical
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let Ω := G ⧸ M
  let : Fintype Ω := Fintype.ofFinite Ω
  have hMproper : M ≠ ⊤ := w.M_maximal.ne_top
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  have hcore : M.normalCore = ⊥ := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple M.normalCore
      M.normalCore_normal with hbot | htop
    · exact hbot
    · apply False.elim
      apply hMproper
      apply top_unique
      exact htop ▸ M.normalCore_le
  let : FaithfulSMul G Ω := faithfulSMul_iff.mpr (by
    intro g hg
    have hperm : MulAction.toPermHom G Ω g = 1 := by
      apply Equiv.ext
      intro x
      simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using hg x
    have hgker : g ∈ (MulAction.toPermHom G Ω).ker :=
      MonoidHom.mem_ker.mpr hperm
    rw [← Subgroup.normalCore_eq_ker, hcore] at hgker
    exact Subgroup.mem_bot.mp hgker)
  have hGle : Nat.card G ≤ (Nat.card Ω).factorial := by
    have h := Nat.card_le_card_of_injective
      (MulAction.toPermHom G Ω) (MulAction.toPerm_injective (α := G) (β := Ω))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using h
  have hΩ : Nat.card Ω = M.index := by
    exact (Subgroup.index_eq_card M).symm
  have hcardQ : Nat.card (M ⧸ O) = 2520 := by
    let : Fintype (M ⧸ O) := Fintype.ofFinite _
    have hAmbient := secondCase_a7_ambient_quotient_model hmin c w d hA7 hmodel
    have h : Nat.card (M ⧸ O) = Nat.card (alternatingGroup (Fin 7)) := by
      simpa [M, O] using Nat.card_congr hAmbient.some.toEquiv
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card] at h
    norm_num at h ⊢
    exact h
  have hcardMO : Nat.card M = Nat.card (M ⧸ O) * Nat.card O :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup O
  have hMge : 2520 ≤ Nat.card M := by
    rw [hcardMO, hcardQ]
    exact Nat.le_mul_of_pos_right 2520 (Nat.card_pos)
  have hmul : Nat.card M * M.index = Nat.card G :=
    Subgroup.card_mul_index M
  have hfactor : 2520 * M.index ≤ (M.index).factorial := by
    calc
      2520 * M.index ≤ Nat.card M * M.index :=
        Nat.mul_le_mul_right M.index hMge
      _ = Nat.card G := hmul
      _ ≤ (Nat.card Ω).factorial := hGle
      _ = (M.index).factorial := by rw [hΩ]
  have hindex_ne_one : M.index ≠ 1 :=
    Subgroup.index_eq_one.not.mpr hMproper
  have hindex_two : 2 ≤ M.index := by
    have hpos : 0 < M.index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    omega
  interval_cases h : M.index <;> norm_num [h] at hfactor

end CFSG.GorensteinWalter
