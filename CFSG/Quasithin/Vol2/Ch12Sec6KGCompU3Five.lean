module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompResid
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompL3Small
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompDescend
import CFSG.Quasithin.SteinbergBSQTEOddUnitaryThree
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddU3AutFinal

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem center_eq_bot_of_isQuasisimple {M : Type*} [Group M] [IsSimpleGroup M]
    (hq : CFSG.IsQuasisimple M) : Subgroup.center M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top a) b).symm

theorem nonempty_residual_sl2_five {F : Type} [Field F] (hU : UnitaryFieldData 5 1 F)
    (D : Subgroup (unitarySU 5 1 F 3)) [D.Normal] (hD : D ≤ unitaryScalars hU 3)
    {t : unitarySU 5 1 F 3 ⧸ D} (ht : orderOf t = 2) :
    Nonempty (↥(CFSG.perfectResidual
        ↥(Subgroup.centralizer ({t} : Set (unitarySU 5 1 F 3 ⧸ D)))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) hU.fixedField) := by
  obtain ⟨-, hst⟩ := CFSG.Quasithin.SteinbergBS.odd_unitary_three_involution_and_Sylow_structure
    hU (by norm_num) (by norm_num) D hD
  obtain ⟨z, -, -, -, -, -, -, -, hJ, -, ⟨eJ⟩, -, -⟩ := hst t ht
  exact ⟨(Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).trans
    ((MulEquiv.subgroupCongr hJ).trans eJ)⟩

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.not_psu3_five (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    (hK : StatedClassicalModel ↥K .PSU 3 5 1) : False := by
  have := hQ.finite
  obtain ⟨-, F, _, _, hFc, ⟨e⟩⟩ := id hK
  have hU : UnitaryFieldData 5 1 F := ⟨by norm_num, le_rfl, by rw [hFc]; norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsSimpleGroup (StatedProj (StatedSU 3 (5 ^ 1) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 5 1 hFc 3 le_rfl (by decide)
  have : IsSimpleGroup ↥K := e.isSimpleGroup
  have hZ := center_eq_bot_of_isQuasisimple h.comp.1
  obtain ⟨l, hl⟩ := CFSG.QuasithinUnique.Ch1.oddAutInner_psu3 (by norm_num) (by norm_num) hK h.nu
    (apply_apply_of_sq h.autConf.sq) h.autConf.exists_sylow_fixed
  obtain ⟨hl2, -⟩ := h.autConf.involution_of_inner hZ hl
  set e' : ↥K ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  have ht2 : orderOf (e' l⁻¹) = 2 := by rw [MulEquiv.orderOf_eq, orderOf_inv, hl2]
  obtain ⟨eR⟩ := nonempty_residual_sl2_five hU (unitaryScalars hU 3) le_rfl ht2
  exact h.false_of_conj_residual hQ e' (fun k => by rw [hl, map_mul, map_mul, map_inv, inv_inv])
    (by rw [hU.card_fixedField, pow_one]) eR

theorem Conf12626.not_su3_five (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v)
    (hSU : IsSLEps3 false 5 ↥K) : False := by
  have := hQ.finite
  obtain ⟨F, _, _, hFc, ⟨e₀⟩⟩ := hSU
  have hq : Nat.card F = (5 ^ 1) ^ 2 := by rw [hFc, pow_one]
  have hU : UnitaryFieldData 5 1 F := ⟨by norm_num, le_rfl, by rw [hFc]⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set e : ↥K ≃* ↥(unitarySU 5 1 F 3) := e₀.trans (MulEquiv.subgroupCongr (by
    show StatedSU 3 5 F = StatedSU 3 (5 ^ 1) F
    rw [pow_one]))
  have hc := h.autConf.map e
  obtain ⟨-, hYZ⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hq le_rfl (by decide)
  have : Group.IsPerfect ↥(unitarySU 5 1 F 3) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hq le_rfl (by decide)
  have hZc : Nat.card (Subgroup.center ↥(unitarySU 5 1 F 3)) = 3 := by
    rw [hYZ, ← unitaryScalars_eq hU (by norm_num)]
    exact (card_unitaryScalars hU (by norm_num)).trans (by norm_num)
  have hd := hc.descend (N := Subgroup.center ↥(unitarySU 5 1 F 3)) le_rfl
    (by rw [hZc]; decide)
  have hm : StatedClassicalModel (↥(unitarySU 5 1 F 3) ⧸ Subgroup.center ↥(unitarySU 5 1 F 3))
      .PSU 3 5 1 :=
    ⟨⟨by norm_num, le_rfl, le_rfl, by decide⟩, F, inferInstance, inferInstance, hq,
      ⟨QuotientGroup.quotientMulEquivOfEq hYZ⟩⟩
  obtain ⟨lb, hlb⟩ := CFSG.QuasithinUnique.Ch1.oddAutInner_psu3 (by norm_num) (by norm_num) hm _
    (apply_apply_of_sq hd.sq) hd.exists_sylow_fixed
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective lb
  have hνY : MulAut.congr e h.nu = MulAut.conj l⁻¹ := by
    apply quotient_injective (N := Subgroup.center ↥(unitarySU 5 1 F 3)) le_rfl
    rw [quotient_conj]
    refine MulEquiv.ext fun x => ?_
    rw [hlb, MulAut.conj_apply, QuotientGroup.mk_inv, inv_inv]
  have hw3 : ∀ z ∈ Subgroup.center ↥(unitarySU 5 1 F 3), z ^ 3 = 1 := fun z hz => by
    rw [hYZ, Subgroup.mem_subgroupOf] at hz
    obtain ⟨u, hu⟩ := hz
    have hdet := CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU z.2
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hu, ← map_pow, hu3, map_one]
    rfl
  have hl2c : l⁻¹ ^ 2 ∈ Subgroup.center ↥(unitarySU 5 1 F 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj (l⁻¹ ^ 2) = 1 := by rw [map_pow, ← hνY, hc.sq]
    have h2 := DFunLike.congr_fun h1 g
    rw [MulAut.conj_apply, MulAut.one_apply] at h2
    calc g * l⁻¹ ^ 2 = l⁻¹ ^ 2 * g * (l⁻¹ ^ 2)⁻¹ * l⁻¹ ^ 2 := by rw [h2]
      _ = l⁻¹ ^ 2 * g := by group
  have hs : MulAut.congr e h.nu = MulAut.conj (l⁻¹ ^ 3) := by
    rw [map_pow, ← hνY, pow_succ, hc.sq, one_mul]
  have hs2 : orderOf (l⁻¹ ^ 3) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ fun h1 => hc.ne_one (by rw [hs, h1, map_one])
    rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul]
    exact hw3 _ hl2c
  set e' : ↥K ≃* unitarySU 5 1 F 3 ⧸ (⊥ : Subgroup ↥(unitarySU 5 1 F 3)) :=
    e.trans QuotientGroup.quotientBot.symm
  have ht2 : orderOf (e' (e.symm (l⁻¹ ^ 3))) = 2 := by
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hs2]
  obtain ⟨eR⟩ := nonempty_residual_sl2_five hU ⊥ bot_le ht2
  refine h.false_of_conj_residual hQ e' (fun k => ?_) (by rw [hU.card_fixedField, pow_one]) eR
  have h1 : e (h.nu k) = l⁻¹ ^ 3 * e k * (l⁻¹ ^ 3)⁻¹ := by
    have := DFunLike.congr_fun hs (e k)
    rwa [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulAut.conj_apply] at this
  simp only [e', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [h1, map_mul, map_mul, map_inv]

end CFSG.Quasithin.H13.S126C
