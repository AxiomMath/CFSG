module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankThreeBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSU4Hyp
import CFSG.ClassicalGroups.Unitary.ComponentBorelUnitary
import CFSG.Quasithin.H13.U4ParPointQuot
import CFSG.Quasithin.Vol2.GoldschmidtF431UnModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par
open scoped Pointwise

theorem isSUn_four_of_isU4 {X : Type} [Group X] {e : ℕ} (hS : IsU4 X e) : IsSUn X 4 e := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK'
  have hbot := CFSG.Quasithin.H13.F431.Un.statedScalars_inf_eq_bot (f := e) hK
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨φ.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot)⟩⟩

theorem nParam_eq_of_isU4_parabolic {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    {e n : ℕ} (hq : CFSG.Open.IsQuasisimple ↥L) (hS : IsU4 ↥L e) (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥) (hN : NParam (Hinf P) n) :
    n = e ∨ n = 2 * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, h, ⟨φ⟩⟩ := exists_hypSU_equiv_of_lieModel hS
  have he1 : 1 ≤ e := h.one_le
  have : Finite K := h.finite
  have : Finite h.fixedField := Subtype.finite
  obtain ⟨S, hSN⟩ := IsParabolicTwo.comap φ.toMonoidHom φ.surjective hpar
  obtain ⟨-, ⟨U₀, hU₀⟩, -⟩ :=
    unitary_order_and_Sylow h (r := 2) (ε := 0) (by norm_num) (by norm_num)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (hypSU h 2 0) S U₀
  set Q₀ := (P.subgroupOf L).comap φ.toMonoidHom with hQ₀
  set Q := Q₀.map (MulAut.conj c).toMonoidHom with hQ
  have heq : (S : Subgroup (hypSU h 2 0)).map (MulAut.conj c).toMonoidHom =
      hypUnitriangular h 2 0 := by
    rw [← hU₀]
    change MulAut.conj c • (S : Subgroup (hypSU h 2 0)) = (U₀ : Subgroup (hypSU h 2 0))
    rw [← Sylow.coe_subgroup_smul, hc]
  have hBQ : hypBorel h 2 0 ≤ Q := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular h
      (by norm_num) (by norm_num), ← heq, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hSN
  let φ' : ↥(hypSU h 2 0) ≃* ↥L := (MulAut.conj c).symm.trans φ
  have hPQ : P.subgroupOf L = Q.map φ'.toMonoidHom := by
    rw [hQ, Subgroup.map_map]
    have hid : (φ'.toMonoidHom.comp (MulAut.conj c).toMonoidHom) = φ.toMonoidHom := by
      ext x
      simp only [φ', MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.trans_apply, MulAut.conj_symm_apply, MulAut.conj_apply]
      congr 1
      group
    rw [hid, hQ₀, Subgroup.map_comap_eq_self_of_surjective φ.surjective]
  obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_subgroupOf_eq_map hPL φ' hPQ
  have hQne : Hinf Q ≠ ⊥ := by
    intro hQb
    apply hinf
    have hPeq : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
    rw [← hPeq, ← Hinf_map L.subtype, hPQ, Hinf_map_eq_bot φ' _ hQb, Subgroup.map_bot]
  rcases overgroups_hypBorel_model h hBQ with hB | hP1 | hP2 | htop
  ·
    exact absurd (by
      rw [hB, Hinf_eq_perfectCore]
      exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).mp
        (isSolvable_hypBorel h (by norm_num) (by norm_num))) hQne
  ·
    left
    rcases (show e = 1 ∨ 2 ≤ e by omega) with he | he2
    · exact absurd (by rw [hP1, Hinf_eq_perfectCore]; exact perfectCore_parP_eq_bot h he) hQne
    · have ε : Bar2 (Hinf Q) ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField := by
        rw [hP1, Hinf_eq_perfectCore]
        exact modO2PerfectCoreParPEquivSL2 h he2
      exact kNshape_holds _ _ n e hN
        (Or.inl (KTabD.isL2_of_mulEquiv_sl2 he2 h.card_fixedField (χ.trans ε)))
  ·
    right
    have hL2 : IsL2 (Bar2 (Hinf Q)) (2 * e) := by
      rw [hP2, CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL, Hinf_eq_perfectCore]
      exact isPSL_modO2_perfectCore_parP2 h
    exact kNshape_holds _ _ n (2 * e) hN
      (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv χ.symm hL2))
  ·
    exfalso
    have hPL' : P = L := by
      refine le_antisymm hPL (Subgroup.subgroupOf_eq_top.mp ?_)
      rw [hPQ, htop, Subgroup.map_top_of_surjective _ φ'.surjective]
    have hsimpL : IsSimpleGroup ↥L :=
      uc22p22r_lieModel_isSimple_classical (Or.inr (Or.inl rfl)) hS
    have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperfL
    have hO2 : CFSG.pCore 2 ↥L = ⊥ := by
      rcases (CFSG.pCore_normal (p := 2) (G := ↥L)).eq_bot_or_eq_top with hbot | htop'
      · exact hbot
      · exact absurd ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).of_equiv
          ((MulEquiv.subgroupCongr htop').trans Subgroup.topEquiv)).isNilpotent
          (Group.IsPerfect.not_isNilpotent ↥L)
    obtain ⟨ξ⟩ := nonempty_bar2_hinf_equiv_of_eq hPL' hperf hO2
    obtain ⟨K', hK'f, hK'fin, hK', ⟨ψ⟩⟩ := isSUn_four_of_isU4 hS
    exact not_nParam_of_isSUn_four ⟨K', hK'f, hK'fin, hK', ⟨ξ.trans ψ⟩⟩ he1 hN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
