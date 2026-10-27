module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.GroupTheory.GLSmallCoprimeTrivial
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG

open CFSG.RankThree.PartTwo.Sec21.FF79

theorem MulAut.eq_one_of_coprime_six_of_card_nine
    {G : Type} [Group G] {W : Subgroup G} [Finite W] (hW : IsElemAb 3 2 W)
    {Y : Type*} [Group Y] [Finite Y] (hcop : Nat.Coprime (Nat.card Y) 6)
    (ρ : Y →* MulAut W) : ρ = 1 := by
  haveI : IsElementaryAbelian 3 W := hW.1
  have hcomm : ∀ a b : W, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := W)).comm a b
  have hpow : ∀ a : W, a ^ 3 = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 W) a
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := 3) (n := 2) hcomm hpow hW.2
  let φ : MulAut W ≃* GL (Fin 2) (ZMod 3) := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  have hcomp : φ.toMonoidHom.comp ρ = 1 :=
    MonoidHom.eq_one_of_coprime_six_GL_fin_two hcop (φ.toMonoidHom.comp ρ)
  apply MonoidHom.ext
  intro y
  exact φ.injective (by simpa using DFunLike.congr_fun hcomp y)

theorem MulAut.eq_one_of_odd_of_card_three
    {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 3)
    {Y : Type*} [Group Y] [Finite Y] (hodd : Odd (Nat.card Y))
    (ρ : Y →* MulAut W) : ρ = 1 := by
  letI : IsCyclic W := isCyclic_of_prime_card (p := 3) hW
  haveI : IsElementaryAbelian 3 W :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := by simpa [hW] using Group.exponent_dvd_nat_card (G := W) }
  have hcomm : ∀ a b : W, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := W)).comm a b
  have hpow : ∀ a : W, a ^ 3 = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 W) a
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (p := 3) (n := 1) hcomm hpow (by simpa using hW)
  have hcardAut : Nat.card (MulAut W) = 2 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e,
      CFSG.card_GL_fin_one_zmod_three]
  have hdvd : Nat.card ρ.range ∣ 2 := by
    rw [← hcardAut]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hcopY2 : Nat.Coprime (Nat.card Y) 2 := Nat.coprime_two_right.mpr hodd
  have hcardRange : Nat.card ρ.range = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopY2 (Subgroup.card_range_dvd ρ) hdvd
  exact MonoidHom.range_eq_bot_iff.mp (Subgroup.card_eq_one.mp hcardRange)

end CFSG
