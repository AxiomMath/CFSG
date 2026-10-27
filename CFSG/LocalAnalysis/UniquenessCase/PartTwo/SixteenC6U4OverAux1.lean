module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.Quasithin.EmptyFaithful.S153H30
public import CFSG.LocalAnalysis.WeakClosure81.W15SixC
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c6_isL2_param_unique {X : Type} [Group X] {a b : ℕ}
    (ha : IsL2 X a) (hb : IsL2 X b) : a = b := by
  have ha1 := (CFSG.Quasithin.S153H.card_psl_two_two
    (CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL.mp ha)).1
  have hb1 := (CFSG.Quasithin.S153H.card_psl_two_two
    (CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL.mp hb)).1
  have hcard_a := (CFSG.Quasithin.S153H.card_psl_two_two
    (CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL.mp ha)).2
  have hcard_b := (CFSG.Quasithin.S153H.card_psl_two_two
    (CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL.mp hb)).2
  have hodd_a : Odd ((2 ^ a) ^ 2 - 1) := by
    have he : Even ((2 ^ a) ^ 2) := by
      have h2 : Even (2 ^ a) := (by decide : Even 2).pow_of_ne_zero (by omega)
      exact h2.pow_of_ne_zero (by norm_num)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (Nat.two_pow_pos a)) he odd_one
  have hodd_b : Odd ((2 ^ b) ^ 2 - 1) := by
    have he : Even ((2 ^ b) ^ 2) := by
      have h2 : Even (2 ^ b) := (by decide : Even 2).pow_of_ne_zero (by omega)
      exact h2.pow_of_ne_zero (by norm_num)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (Nat.two_pow_pos b)) he odd_one
  have heq : 2 ^ a * ((2 ^ a) ^ 2 - 1) = 2 ^ b * ((2 ^ b) ^ 2 - 1) := by
    rw [← hcard_a, hcard_b]
  exact CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hodd_a hodd_b heq

theorem s16c6_bar2_map_equiv {U V : Type} [Group U] [Group V] (X : Subgroup U) (e : U ≃* V) :
    Nonempty (Bar2 X ≃* Bar2 (X.map e.toMonoidHom)) := by
  refine ⟨?_⟩
  let eX : ↥X ≃* ↥(X.map e.toMonoidHom) := X.equivMapOfInjective e.toMonoidHom e.injective
  exact QuotientGroup.congr (CFSG.pCore 2 ↥X) (CFSG.pCore 2 ↥(X.map e.toMonoidHom)) eX
    (CFSG.pCore_map_iso 2 eX)

theorem s16c6_derInf_map_equiv {U V : Type} [Group U] [Group V] [Finite U] [Finite V] (e : U ≃* V)
    (P : Subgroup U) :
    (F07.DerInf P).map e.toMonoidHom = F07.DerInf (P.map e.toMonoidHom) := by
  rw [← hinf_eq_derInf, ← hinf_eq_derInf]
  exact Hinf_map e.toMonoidHom P

theorem s16c6_isL2_bar2_map_equiv {U V : Type} [Group U] [Group V] (e : U ≃* V)
    (X : Subgroup U) {k : ℕ} (h : IsL2 (Bar2 X) k) :
    IsL2 (Bar2 (X.map e.toMonoidHom)) k := by
  obtain ⟨e'⟩ := s16c6_bar2_map_equiv X e
  exact CFSG.Blueprint.LieModel.of_mulEquiv e' h

theorem s16c6_map_equiv_eq_top_iff {U V : Type} [Group U] [Group V] (e : U ≃* V)
    {A : Subgroup U} : A.map e.toMonoidHom = ⊤ ↔ A = ⊤ := by
  constructor
  · intro h
    have h2 := congrArg (Subgroup.map e.symm.toMonoidHom) h
    rw [Subgroup.map_map] at h2
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id U := by
      ext x; simp
    rw [hcomp, Subgroup.map_id, Subgroup.map_top_of_surjective _ e.symm.surjective] at h2
    exact h2
  · intro h
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]

theorem s16c6_map_equiv_le_iff {U V : Type} [Group U] [Group V] (e : U ≃* V)
    {A B : Subgroup U} : A.map e.toMonoidHom ≤ B.map e.toMonoidHom ↔ A ≤ B := by
  constructor
  · intro h
    exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h
  · exact Subgroup.map_mono

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
