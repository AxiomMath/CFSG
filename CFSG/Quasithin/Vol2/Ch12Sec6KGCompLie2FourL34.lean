module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section L34

variable {F : Type} [Field F]

theorem exists_conj_mem_l34 (hF : Nat.card F = 4)
    {Pb : Subgroup (MulAut (projectiveSL 3 F))} (hPe : ∀ p ∈ Pb, p ^ 3 = 1) (hP : Nat.card Pb = 9) :
    ∃ c : projectiveSL 3 F, c ≠ 1 ∧ MulAut.conj c ∈ Pb := by
  have := LinearFieldFour.finite_of_card_eq_four hF
  have := LinearFieldFour.charP_two_of_card_eq_four hF
  have hσ : ∀ a, frobeniusEquiv F 2 a = a ^ 2 := fun a => frobeniusEquiv_apply F 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hF
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hF hΨ
  have hright : ∀ p ∈ Pb, (Ψ p).right = 1 := by
    intro p hp
    have h3 : SemidirectProduct.rightHom (Ψ p) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hPe p hp, map_one, map_one]
    have key : ∀ x : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), x ^ 3 = 1 → x = 1 := by
      decide
    rw [← SemidirectProduct.rightHom_eq_right]
    exact key _ h3
  have hlt : Nat.card Fˣ < Nat.card Pb := by
    rw [LinearThreeFourOuter.card_units_eq_three hF, hP]
    norm_num
  have : Finite Fˣ := Nat.finite_of_card_ne_zero (by
    rw [LinearThreeFourOuter.card_units_eq_three hF]; norm_num)
  have hni : ¬ Function.Injective (fun p : Pb => (Ψ (p : MulAut (projectiveSL 3 F))).left) :=
    fun hinj => absurd (Nat.card_le_card_of_injective _ hinj) (not_le.mpr hlt)
  obtain ⟨x, y, hfxy, hxy⟩ := Function.not_injective_iff.mp hni
  have hΨxy : Ψ x = Ψ y := SemidirectProduct.ext hfxy (by rw [hright x x.2, hright y y.2])
  have hq : (x : MulAut (projectiveSL 3 F))⁻¹ * y ∈ Ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΨxy, inv_mul_cancel]
  rw [hker] at hq
  obtain ⟨c, hc⟩ := hq
  refine ⟨c, fun h1 => hxy (Subtype.ext ?_), ?_⟩
  · rw [h1, map_one, eq_comm, inv_mul_eq_one] at hc
    exact hc
  · rw [hc]
    exact mul_mem (inv_mem x.2) y.2

theorem false_of_autConf_l34 (hF : Nat.card F = 4) {ν : MulAut (projectiveSL 3 F)}
    {Lb Pb : Subgroup (MulAut (projectiveSL 3 F))} (h : AutConf (projectiveSL 3 F) ν Lb Pb)
    (hP : Nat.card Pb = 9) : False := by
  have := LinearFieldFour.finite_of_card_eq_four hF
  have := LinearFieldFour.charP_two_of_card_eq_four hF
  have hZ := LinearThreeFourOuter.center_projectiveSL_three_eq_bot hF
  have hcj := conj_injective_of_center_eq_bot hZ
  obtain ⟨S, hS, hSν⟩ := h.sylow
  obtain ⟨x, hx⟩ := CFSG.QuasithinUnique.K1.sylowCentralizingAutInner_projectiveSL
    (K := F) (le_refl 3) S hS ν hSν
  have hν : ν = MulAut.conj x⁻¹ := MulEquiv.ext fun y => by
    rw [hx, MulAut.conj_apply, inv_inv]
  subst hν
  have hz2 : orderOf x⁻¹ = 2 := by
    refine orderOf_eq_prime (hcj ?_) fun h1 => h.ne_one (by rw [h1, map_one])
    rw [map_pow, h.sq, map_one]
  obtain ⟨c, hc1, hcP⟩ := exists_conj_mem_l34 hF h.elem.2 hP
  have hc3 : orderOf c = 3 := by
    refine orderOf_eq_prime (hcj ?_) hc1
    rw [map_pow, h.elem.2 _ hcP, map_one]
  have hfix := h.fix_of_mem_innerPart hZ (show c ∈ innerPart Lb from h.le hcP)
  rw [MulAut.conj_apply] at hfix
  refine CFSG.RankThree.PartTwo.KFacts.L34.mul_ne_mul_of_orderOf hF hc3 hz2 ?_
  calc c * x⁻¹ = x⁻¹ * c * x⁻¹⁻¹ * x⁻¹ := by rw [hfix]
    _ = x⁻¹ * c := by group

theorem exists_E9_l34 (hF : Nat.card F = 4) :
    ∃ E : Subgroup (projectiveSL 3 F), IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  refine ⟨(LinearThreeFourFixedNine.qSub (k := F)).map (proj 3 F), ⟨?_, fun x hx =>
    LinearThreeFourFixedNine.pow_three_of_mem_map_proj hF hx⟩,
    LinearThreeFourFixedNine.card_map_proj_qSub hF⟩
  exact (LinearThreeFourFixedNine.isElementaryAbelian_three_of_card
    (LinearThreeFourFixedNine.card_map_proj_qSub hF) fun x hx =>
      LinearThreeFourFixedNine.pow_three_of_mem_map_proj hF hx).toIsMulCommutative

theorem not_psl34 {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) :
    ¬ StatedClassicalModel ↥K .PSL 3 2 2 := fun hK => by
  have := hQ.finite
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hK
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  let e' : ↥K ≃* projectiveSL 3 F := e.trans (K1.statedProjEquivProjectiveSL 3 F)
  obtain ⟨E, hE, hE9⟩ := exists_E9_l34 hF4
  exact false_of_autConf_l34 hF4 (h.autConf.map e') (h.card_map_rhoP_eq_nine hQ e'
    (fun z hz => by
      rwa [LinearThreeFourOuter.center_projectiveSL_three_eq_bot hF4, Subgroup.mem_bot] at hz)
    hE hE9)

end L34

end CFSG.Quasithin.H13.S126C
