module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega4
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelSolvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Quasithin.S151S4

private theorem isSolvable_of_map_D5 {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) (hA : Group.IsSolvable ↥(A.map e.toMonoidHom)) :
    Group.IsSolvable ↥A := by
  haveI := hA
  exact Group.isSolvable_of_isSolvable_injective
    (f := e.toMonoidHom.subgroupMap A)
    (MonoidHom.subgroupMap_injective e.toMonoidHom A e.injective)

private theorem isSolvable_Bsub_D5 (K : Type) [Field K] : Group.IsSolvable ↥(Bsub K) := by
  have h : Bsub K = CFSG.PSL2Table.borelSL K := by
    ext g
    rfl
  have := CFSG.AGLEmbedding.isSolvable_borelSL (F := K)
  rw [← h] at this
  exact this

theorem isSolvable_normalizer_sylow_of_isL2 {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (hX : IsL2 X m) (S : Sylow 2 X) :
    Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
  obtain ⟨K, hField, hFinite, hKcard, ⟨e⟩⟩ := nonempty_mulEquiv_sl2_of_isL2 hX
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := uc22p22d_charP_two (by omega) hKcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  let P : Sylow 2 (SL2 K) := Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective S
  have hN : Subgroup.normalizer (P : Set (SL2 K)) =
      (Subgroup.normalizer ((S : Subgroup X) : Set X)).map e.toMonoidHom := by
    change Subgroup.normalizer ((P : Subgroup (SL2 K)) : Set (SL2 K)) =
      (Subgroup.normalizer ((S : Subgroup X) : Set X)).map e.toMonoidHom
    rw [show (P : Subgroup (SL2 K)) = (S : Subgroup X).map e.toMonoidHom from rfl]
    exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup X) e).symm
  have hNP : Group.IsSolvable ↥(Subgroup.normalizer (P : Set (SL2 K))) := by
    obtain ⟨g, hP⟩ := exists_conj_eq_Usub (K := K) hK4 P
    let f : SL2 K ≃* SL2 K := MulAut.conj g⁻¹
    have hN2 : Subgroup.normalizer (P : Set (SL2 K)) = (Bsub K).map f.toMonoidHom := by
      change Subgroup.normalizer ((P : Subgroup (SL2 K)) : Set (SL2 K)) =
        (Bsub K).map f.toMonoidHom
      rw [show (P : Subgroup (SL2 K)) = (Usub K).map f.toMonoidHom from hP,
        (Subgroup.map_equiv_normalizer_eq (Usub K) f).symm, normalizer_Usub_eq_Bsub]
    have hcomp : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id (SL2 K) :=
      MulEquiv.toMonoidHom_symm_comp_toMonoidHom f
    have hmap : (Subgroup.normalizer (P : Set (SL2 K))).map f.symm.toMonoidHom = Bsub K := by
      rw [hN2, Subgroup.map_map, hcomp, Subgroup.map_id]
    exact isSolvable_of_map_D5 f.symm (Subgroup.normalizer (P : Set (SL2 K)))
      (hmap.symm ▸ isSolvable_Bsub_D5 K)
  exact isSolvable_of_map_D5 e (Subgroup.normalizer ((S : Subgroup X) : Set X))
    (hN.symm ▸ hNP)

theorem hinf_eq_bot_of_isL2_of_sylow_le {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 2 ≤ m)
    (hX : IsL2 X m) (S : Sylow 2 X) (P : Subgroup X) (hSP : (S : Subgroup X) ≤ P)
    (hP : P ≠ ⊤) : Hinf P = ⊥ := by
  haveI : Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup X) : Set X)) :=
    isSolvable_normalizer_sylow_of_isL2 hm hX S
  have hPN : P ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) :=
    l2_sylow_le_normalizer hm hX S P hSP hP
  haveI : Group.IsSolvable ↥(P.subgroupOf (Subgroup.normalizer ((S : Subgroup X) : Set X))) :=
    inferInstance
  haveI : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hPN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPN).symm.injective
  have hsol : CFSG.perfectResidual ↥P = ⊥ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mpr
      inferInstance
  simp [Hinf, CFSG.inSubgroup, hsol, Subgroup.map_bot]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
