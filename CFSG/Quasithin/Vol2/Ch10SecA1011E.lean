module

public import CFSG.Quasithin.Vol2.Ch10SecA1011D
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase
public import CFSG.Quasithin.Vol2.Ch10SecA1011A
public import CFSG.Quasithin.Vol2.Ch10SecA1011B
public import CFSG.Quasithin.Vol2.Ch10SecANat3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_normalizer_and_commutator_ne_bot (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I) (hIU : I ≤ fsuUL T L I) :
    L ≤ Subgroup.normalizer (I : Set G) ∧ ⁅I, L⁆ ≠ ⊥ := by
  have hL0I : fsuL0 T L ≤ Subgroup.normalizer (I : Set G) := hyp.fsu.irrPlus.2.2.1
  refine ⟨(le_fsuL0 T L).trans hL0I, fun h => ?_⟩
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hIt : I ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) := hIU.trans (ha t ht htn).2.2
  have h0 : ⁅I, CFSG.conjugate L t⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hIt
  have hsup := commutator_sup_left_of_le (X := fsuL0 T L ⊔ I) le_sup_right
    ((le_fsuL0 T L).trans le_sup_left) ((conjugate_le_fsuL0 ht).trans le_sup_left)
    (sup_le hL0I Subgroup.le_normalizer)
  rw [← fsuL0_eq_sup h37 h38 hyp ht htn, h, h0, sup_bot_eq] at hsup
  exact hyp.fsu.irrPlus.2.1 (hyp.fsu.irrPlus.2.2.2.1.symm.trans hsup)

theorem case_five_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hshape : Stmt7_0_1_shape) (hyp : Ch10.Hyp10 G T L I) (hcard : Nat.card ↥I = 2 ^ 3)
    {s : G} (hsT : s ∈ T) (hsN : s ∈ Subgroup.normalizer (L : Set G))
    (hsO : s ∉ L ⊔ pCoreOf 2 (L ⊔ T ⊓ Subgroup.normalizer (L : Set G)))
    (hU : fsuUL T L I = I ⊔ CFSG.conjugate I s) (hinf : I ⊓ CFSG.conjugate I s = ⊥) :
    Ch10.Case10_1_1Five T L I := by
  obtain ⟨hab, hel, -⟩ := hyp.three
  have hIU : I ≤ fsuUL T L I := hU ▸ le_sup_left
  obtain ⟨hLI, hcomm⟩ := le_normalizer_and_commutator_ne_bot h37 h38 hyp hIU
  have hC := inf_centralizer_le_pCoreOf h37 h38 hyp hLI hcomm
  have hIab : IsMulCommutative ↥I := isMulCommutative_of_le (le_fsuVM T L I)
  have h2 : ∀ w : ↥I, w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using hel.2 _ (le_fsuVM T L I w.2))
  have hAut : Nat.card (MulAut ↥I) = 168 := by
    rw [card_mulAut_of_sq_eq_one h2 hcard, card_GL_three_two]
  have hdvd1 := card_quot_dvd_card_autOn hLI hC
  have hdvd2 : Nat.card ↥(autOn L I) ∣ 168 := hAut ▸ Subgroup.card_subgroup_dvd_card _
  have hL32 : LBarL32 L :=
    lBarL32_of_shape_dvd (hshape G T L I hyp.fsu hyp.lt hyp.three) (hdvd1.trans hdvd2)
  have hLcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
    obtain ⟨e⟩ := hL32
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field]
    simp [Fin.prod_univ_three]
  have htop : autOn L I = ⊤ := by
    refine (Subgroup.card_eq_iff_eq_top _).mp ?_
    rw [hAut]
    exact Nat.dvd_antisymm hdvd2 (hLcard ▸ hdvd1)
  exact ⟨hL32, s, hsT, hsN, I, hIU, hLI, hU.symm, hinf,
    ⟨hIab, binaryNaturalSL_three_of_eq_top h2 hcard htop⟩,
    not_isXSectionIso_of h37 h38 hyp hsT hsN hsO hLI htop hC⟩

theorem case_six_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) [IsMulCommutative ↥(fsuVM T L I)]
    (hiii : Nonempty (↥(autOn L (fsuVM T L I)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      DirectSumOfCopies (V := ↥(fsuVM T L I)) (autOn L (fsuVM T L I))
        ((fsuUL T L I).subgroupOf (fsuVM T L I)) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 ∧
      (Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
            Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
              Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5)) ∨
        Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
            Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
              Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5 × ZMod 5)))) :
    Ch10.Case10_1_1Six T L I := by
  obtain ⟨⟨e⟩, hsum, h5⟩ := hiii
  have := Vol2Native.A312L.Seven.slThree_isSimple
  exact ⟨nonempty_quot_equiv_of_autOn h37 h38 hyp e, inferInstance, hsum, h5⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
