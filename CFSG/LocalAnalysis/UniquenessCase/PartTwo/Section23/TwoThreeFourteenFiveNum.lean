module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveW0
public import CFSG.GroupTheory.SteinbergCBFTPSolvable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeFourteenFiveTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem T_le_normalizer_conjClosure {S H T : Subgroup G}
    (hS : T ≤ Subgroup.normalizer (S : Set G))
    (hH : T ≤ Subgroup.normalizer (H : Set G)) :
    T ≤ Subgroup.normalizer (conjClosure H S : Set G) := by
  rw [← quasithin_conjClosure_eq]
  exact CFSG.Quasithin.Vol2.Ch11.SecA.le_normalizer_conjClosure_of_le hS hH

theorem H_le_normalizer_conjClosure (H S : Subgroup G) :
    H ≤ Subgroup.normalizer (conjClosure H S : Set G) := by
  rw [← quasithin_conjClosure_eq]
  exact CFSG.Quasithin.le_normalizer_conjClosure S H

theorem aBar_bounds_W4Thm14_5 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1A : S23_1A D Ch) (h1930 : H1930 D)
    {A P : Subgroup G} (hA : IsElemAbelian 2 A) (hAV : A ≤ c.V)
    (hAne : A ≠ ⊥) (hAN : c.N ≤ Subgroup.normalizer (A : Set G))
    (hmin : ∀ B : Subgroup G, B ≤ A →
      c.N ≤ Subgroup.normalizer (B : Set G) → B = ⊥ ∨ B = A)
    (hP : MinTInvParabolic D.T D.M c.L P) (hL0P : c.L0 = Hinf P) :
    ∃ (K : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)))
      (W₀ : Subgroup (Vtil (⊥ : Subgroup G) A hA)),
      K = (⨆ t ∈ barSub (⊥ : Subgroup G) A hA D.T,
        (Hinf (barSub (⊥ : Subgroup G) A hA P)).map
          (MulAut.conj t).toMonoidHom) ∧
      W₀ = (⨆ k ∈ K, (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map
        (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom) ∧
      E3.mParam (Mbar c.N (⊥ : Subgroup G) A hA) ≤
        E3.aParam (autSub (K ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) + 1 ∧
      E3.aParam (autSub (K ⊔ barSub (⊥ : Subgroup G) A hA D.T) W₀) ≤ c.n := by
  set S : Subgroup G := A ⊓ D.Z with hSdef
  set WB : Subgroup G := conjClosure c.L0 S with hWBdef
  have hS : S ≤ A := hSdef ▸ inf_le_left
  have hL0N : c.L0 ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.L0_le_N c).trans hAN
  have hTN : D.T ≤ Subgroup.normalizer (A : Set G) := (Ctx23L.T_le_N c).trans hAN
  have hTZ : D.T ≤ Subgroup.normalizer (D.Z : Set G) := by
    have hZ : D.Z ≤ Subgroup.centralizer (D.T : Set G) := fun x hx =>
      (omegaOneCenterIn_le_inf_centralizer D.T hx).2
    exact (Subgroup.le_centralizer_iff.mp hZ).trans
      (Subgroup.centralizer_le_normalizer (D.Z : Set G))
  have hTS : D.T ≤ Subgroup.normalizer (S : Set G) :=
    hSdef ▸ CFSG.GroupTheory.FT63ChII.le_normalizer_inf_of_le hTN hTZ
  have hTL0 : D.T ≤ Subgroup.normalizer (c.L0 : Set G) := c.T_le_normalizer_L0
  have hL0W : c.L0 ≤ Subgroup.normalizer (WB : Set G) :=
    hWBdef ▸ H_le_normalizer_conjClosure c.L0 S
  have hTW : D.T ≤ Subgroup.normalizer (WB : Set G) :=
    hWBdef ▸ T_le_normalizer_conjClosure hTS hTL0
  let TA : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)) := barSub (⊥ : Subgroup G) A hA D.T
  let KA : Subgroup (MulAut (Vtil (⊥ : Subgroup G) A hA)) := barSub (⊥ : Subgroup G) A hA c.L0
  have hK : (⨆ t ∈ TA, (Hinf (barSub (⊥ : Subgroup G) A hA P)).map
      (MulAut.conj t).toMonoidHom) = KA := by
    rw [Hinf_barSub_eq c hA hAN (parabolicOf_iff.mp hP.1.1).1 hL0P]
    exact iSup_map_conj_eq_self hA
      (le_inf hL0N (by rw [Subgroup.normalizer_eq_top]; exact le_top))
      (le_inf hTN (by rw [Subgroup.normalizer_eq_top]; exact le_top)) hTL0
  have hfixS : fixV (barSub (⊥ : Subgroup G) A hA D.T) = imgTil (⊥ : Subgroup G) A hA S :=
    hSdef ▸ fixV_T_barSub_eq c hA hAV hAN
  have hW₀ : (⨆ k ∈ KA, (fixV (barSub (⊥ : Subgroup G) A hA D.T)).map
      (k : MulAut (Vtil (⊥ : Subgroup G) A hA)).toMonoidHom) =
      imgTil (⊥ : Subgroup G) A hA WB := by
    rw [hfixS, hWBdef]
    exact imgTil_conjClosure_eq_iSup hA hS hL0N (K := KA) rfl rfl
  obtain ⟨hWBab, hb1, hb2⟩ := aBar_bound_of_S23_1A c h1A h1930 hA hAV hAne hAN hmin
  have hWBleA : WB ≤ A := hWBdef ▸ uc22p22v_conjClosure_le hL0N hS
  obtain ⟨e, hmap⟩ := Mbar_sup_eq_autSub_map hA hWBab hWBleA hL0N hTN hL0W hTW
  rw [aBar_eq_aParam_autSub c hA hWBab hmap] at hb1 hb2
  refine ⟨KA, imgTil (⊥ : Subgroup G) A hA WB, hK.symm, hW₀.symm, ?_, ?_⟩
  · simpa [mBar, KA, TA] using hb1
  · simpa [KA, TA] using hb2

end CFSG.LocalAnalysis.UniquenessCase.UC22
