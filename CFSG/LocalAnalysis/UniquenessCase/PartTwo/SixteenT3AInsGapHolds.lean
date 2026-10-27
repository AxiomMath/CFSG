module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsGap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16GapA168FourThree_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) : S16GapA168FourThree D := by
  intro _ V L hV hc _ _ h4 hrank h27 ι _ Y hcard _ hinj hsup hrk hperm hsurj hall
  exfalso
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have h4' : ∀ i, Nat.card ↥(Y i) = 4 := by
    intro i
    rw [card_eq_two_pow (s15_Infra_vtil_sq_eq_one ⊥ V hV) (Y i), hrk i, s16c1610_dParam_three]
    norm_num
  have hH : S16tW3Hyp Y (Mbar D.M ⊥ V hV) := ⟨hcard, hinj, hsup, h4', hperm, hsurj, hrank, h27⟩
  obtain ⟨E₀, hE₀, hE₀c, -⟩ := exists_rank_data (uc22p22q_r115_of D hx h61)
    (Hyp125.hyp11 h127 h125) (by simp) h4.2.2
  have hEM : E₀.map D.M.subtype ≤ D.M := Subgroup.map_subtype_le E₀
  have hEel : IsElemAbelian 3 (E₀.map D.M.subtype) := hE₀.map D.M.subtype
  have hEc : 3 ^ 3 ≤ Nat.card ↥(E₀.map D.M.subtype) := by
    rw [Subgroup.card_map_of_injective D.M.subtype_injective]
    exact hE₀c
  obtain ⟨⟨f, hf, hfm⟩, -⟩ := hall _ hEM hEel hEc
  have hfX : f ∈ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hEM hf
  have hΛel : IsElemAbelian 3 (barSub ⊥ V hV (E₀.map D.M.subtype)) :=
    (hEel.subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV)
  have hO := s16t_w3_isPOnePlusTwo_pCoreOf hH hfX (hΛel.2 f hf) hfm
  have hsig : D.sig = {3} :=
    s16t_w3_sig_eq D hx h61 h127 h125 h4.2.2 fun g hg => s16t_w3_pow_36 hH hg
  exact hc.norm h4 hsig hO

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
