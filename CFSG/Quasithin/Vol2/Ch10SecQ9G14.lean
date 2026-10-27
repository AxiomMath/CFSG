module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G13
public import CFSG.Quasithin.Vol2.Ch10SecQ9G11
public import CFSG.Quasithin.Vol2.Ch10SecQ9G12
public import CFSG.Quasithin.Vol2.Ch10SecQ9G8

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_y (c : Conf T L I t w J) (h37 : Vol2Native.A37ForSQTKCat)
    (hVe : IsElemAbelian 2 (VI T L I J w))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    {S : Type} [Group S] [Finite S] (e : ↥(autI hVe J) ≃* S)
    (hS : ∀ a b : S, orderOf a = 7 → orderOf b = 3 → Commute a b → False) {y : G}
    (hyLt : y ∈ CFSG.conjugate L t) (hy3 : orderOf y = 3) (hyJ : y ∈ J) : False := by
  have hyp := c.hyp
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  obtain ⟨ρ, -, hρ1⟩ := exists_autI_hom hVe hJN
  set ψ := e.toMonoidHom.comp ρ with hψdef
  have hψ : ∀ j : ↥J, ψ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1 := by
    intro j hj
    have h1 : ρ j = 1 := by
      rw [hψdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hj
      exact (MulEquiv.map_eq_one_iff e).mp hj
    have h2 : (j : G) ∈ pCoreOf 2 J := hCJ ▸ ⟨j.2, (hρ1 j).mp h1⟩
    exact exists_two_pow_of_mem_pCoreOf h2
  obtain ⟨x, hxL, hx7⟩ := exists_orderOf_seven eL
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := conjugate_le_normalizer hyp c.ht hyLt
  have hyc : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro l hl
    have h1 : ⁅y, l⁆ ∈ ⁅CFSG.conjugate L t, L⁆ := Subgroup.commutator_mem_commutator hyLt hl
    rw [Subgroup.commutator_comm] at h1
    exact (SecA.commutator_conjugate_le h37 hyp c.ht c.htn h1).1
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_commute_seven_three ψ hψ (c.le hxL) hyJ hxL hx7 hy3 hyN hyc
  exact hS a b ha hb hab

theorem Conf.false_of_case3_A7 (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (h318 : A318Facts) (h36' : A36ForSQTK) (hK7 : FactK7) (hE : Ch11.SecA.FactA318ExclTwo)
    (hVe : IsElemAbelian 2 (VI T L I J w))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (e : ↥(autI hVe J) ≃* ↥(alternatingGroup (Fin 7))) (h3 : Case10_1_1Three T L I) : False := by
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  obtain ⟨eJ⟩ := nonempty_quotient_equiv hVe hJN hCJ e
  obtain ⟨y, hyLt, hy3, hyw⟩ := Conf.exists_y_of_case3 c h37 h38 h1011 h3
  have hyJ := c.mem_J_of_orderOf_three h38 h318 h36' hK7 hE eJ hyw hy3
  exact Conf.false_of_y c h37 hVe hCJ eL e (fun a b ha hb hab => alt7_false ha hb hab) hyLt hy3 hyJ

theorem Conf.mem_J_of_L4 (c : Conf T L I t w J) (h38 : Vol2Native.A38ForSQTKCat)
    (h318 : A318Facts) (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo)
    (hK7L4 : FactK7L4) (hVe : IsElemAbelian 2 (VI T L I J w))
    (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (e : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) {y : G}
    (hy : y ∈ Subgroup.centralizer ({w} : Set G)) (hy3 : orderOf y = 3) : y ∈ J := by
  have hJN : J ≤ Subgroup.normalizer (VI T L I J w : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  obtain ⟨eJ⟩ := nonempty_quotient_equiv hVe hJN hCJ e
  exact Conf.mem_J_of_orderOf_three' c h38 h318 h36' hE eJ
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_of_open' hq))
    (center_SL_eq_bot 4) three_dvd_card_SL4 two_le_pRank_SL4 hK7L4 hy hy3

theorem Conf.false_of_case3_L4 (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1)
    (h318 : A318Facts) (h36' : A36ForSQTK) (hE : Ch11.SecA.FactA318ExclTwo)
    (hK7L4 : FactK7L4) (hVe : IsElemAbelian 2 (VI T L I J w))
    (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (e : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (h3 : Case10_1_1Three T L I) : False := by
  obtain ⟨y, hyLt, hy3, hyw⟩ := Conf.exists_y_of_case3 c h37 h38 h1011 h3
  have hyJ := Conf.mem_J_of_L4 c h38 h318 h36' hE hK7L4 hVe hq hCJ e hyw hy3
  exact Conf.false_of_y c h37 hVe hCJ eL e (fun a b ha hb hab => sl4_false ha hb hab) hyLt hy3 hyJ

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
