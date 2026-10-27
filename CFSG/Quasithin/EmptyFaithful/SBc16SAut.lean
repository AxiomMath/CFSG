module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Fischer.Aut.TwoPower

public section

namespace CFSG.Quasithin

namespace SBc16

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter
  CFSG.Fischer

abbrev L216 : Type := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)

theorem center_L216 : Subgroup.center L216 = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (2 : GaloisField 2 4) = 0 := CharTwo.two_eq_zero
    have h : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

noncomputable def equivPSL2 : L216 ≃* PSL2 (GaloisField 2 4) :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq center_L216.symm)

theorem card_galoisField16 : Nat.card (GaloisField 2 4) = 2 ^ 4 :=
  GaloisField.card 2 4 (by norm_num)

theorem card_L216 : Nat.card L216 = 4080 := by
  rw [sl2_card_formula, card_galoisField16]
  norm_num

theorem card_mulAut_L216 : Nat.card (MulAut L216) = 16320 := by
  have h1 : Nat.card (MulAut L216) = Nat.card (MulAut (PSL2 (GaloisField 2 4))) :=
    Nat.card_congr (MulAut.congr equivPSL2).toEquiv
  have h2 : Nat.card (MulAut (PSL2 (GaloisField 2 4))) = Nat.card (PGammaL2 (GaloisField 2 4)) :=
    (Nat.card_congr (semilinearEquivAut (GaloisField 2 4)).toEquiv).symm
  have h3 : Nat.card (PGammaL2 (GaloisField 2 4)) =
      Nat.card (PGL2 (GaloisField 2 4)) * Nat.card (GaloisField 2 4 ≃+* GaloisField 2 4) :=
    SemidirectProduct.card
  have h4 := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two
    (GaloisField 2 4) card_galoisField16).1
  rw [h1, h2, h3, pgl2_card_formula, card_galoisField16]
  change _ * Nat.card (RingAut (GaloisField 2 4)) = _
  rw [h4]
  norm_num

theorem isSimpleGroup_L216 : IsSimpleGroup L216 := by
  have h4 : 4 ≤ Nat.card (GaloisField 2 4) := by rw [card_galoisField16]; norm_num
  have : IsSimpleGroup (PSL2 (GaloisField 2 4)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact equivPSL2.isSimpleGroup

theorem conj_L216_injective : Function.Injective (MulAut.conj : L216 →* MulAut L216) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro g hg
  have hz : g ∈ Subgroup.center L216 := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut L216 => φ x) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rwa [center_L216, Subgroup.mem_bot] at hz

noncomputable abbrev innerL216 : Subgroup (MulAut L216) := innerAut L216

instance innerL216_normal : innerL216.Normal := innerAut_normal

noncomputable def innerL216Equiv : L216 ≃* innerL216 :=
  MonoidHom.ofInjective conj_L216_injective

theorem card_innerL216 : Nat.card innerL216 = 4080 := by
  rw [← Nat.card_congr innerL216Equiv.toEquiv, card_L216]

theorem index_innerL216 : innerL216.index = 4 := by
  have h := innerL216.card_mul_index
  rw [card_innerL216, card_mulAut_L216] at h
  omega

theorem isPGroup_quotient_innerL216 : IsPGroup 2 (MulAut L216 ⧸ innerL216) := by
  have h : Nat.card (MulAut L216 ⧸ innerL216) = 2 ^ 2 := by
    rw [← Subgroup.index_eq_card, index_innerL216]
    norm_num
  exact IsPGroup.of_card h

instance solvable_quotient_innerL216 : Group.IsSolvable (MulAut L216 ⧸ innerL216) := by
  have := isPGroup_quotient_innerL216.isNilpotent
  infer_instance

instance innerL216_isSimpleGroup : IsSimpleGroup innerL216 := by
  have := isSimpleGroup_L216
  exact innerL216Equiv.symm.isSimpleGroup

end SBc16

end CFSG.Quasithin
