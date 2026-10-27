module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.GroupTheory.RegularRepGF2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem barSub_centerQuot_equiv_barInf {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    Nonempty (BarInf L ≃*
      (barSub V₀ V h.isElemAbelian L ⧸
        Subgroup.center (barSub V₀ V h.isElemAbelian L))) := by
  classical
  let φ : Bar2 L →* ↥(barSub V₀ V h.isElemAbelian L) := barSubBar2HomOfHyp125 h hL
  have hφ : Function.Surjective φ := barSubBar2HomOfHyp125_surjective h hL
  have hnt : ∃ x, φ x ≠ 1 := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL1
    obtain ⟨y, hy⟩ := hφ ⟨x, hx⟩
    exact ⟨y, by rw [hy]; exact hx1⟩
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).2 hL.2.2
  have hker : φ.ker ≤ Subgroup.center (Bar2 L) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hnt
  obtain ⟨e1⟩ := uc22p21k_barInf_equiv_of_calC hL
  exact ⟨e1.trans
    (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hφ hker)⟩

theorem o2zIn17_eq_solvableRadical {M L : Subgroup G} (hL : L ∈ calC M) :
    O2ZIn17 L = CFSG.solvableRadical ↥L := by
  classical
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have h1 : (O2ZIn17 L).map π = Subgroup.center (Bar2 L) := by
    unfold O2ZIn17
    exact Subgroup.map_comap_eq_self_of_surjective hπ _
  have h2 : (CFSG.solvableRadical ↥L).map π = Subgroup.center (Bar2 L) :=
    uc22p21k_map_solvableRadical_eq_center hL.2.2
  have hkerA : π.ker ≤ O2ZIn17 L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [O2ZIn17, Subgroup.mem_comap, hx]
    exact Subgroup.one_mem _
  have hkerB : π.ker ≤ CFSG.solvableRadical ↥L := by
    rw [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _]
    haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥L) :=
      @IsNilpotent.to_isSolvable _ _
        ((CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)).isNilpotent)
    exact le_sSup ⟨inferInstance, inferInstance⟩
  calc O2ZIn17 L = ((O2ZIn17 L).map π).comap π := (Subgroup.comap_map_eq_self hkerA).symm
    _ = (Subgroup.center (Bar2 L)).comap π := by rw [h1]
    _ = ((CFSG.solvableRadical ↥L).map π).comap π := by rw [h2]
    _ = CFSG.solvableRadical ↥L := Subgroup.comap_map_eq_self hkerB

theorem barO2Z17_equiv_barInf {M L : Subgroup G} (hL : L ∈ calC M) :
    Nonempty (BarO2Z17 L ≃* BarInf L) :=
  ⟨QuotientGroup.quotientMulEquivOfEq (o2zIn17_eq_solvableRadical hL)⟩

theorem false_of_lieModel_barInf_psl_two_three_two
    {D : Data G} {V₀ V L : Subgroup G} (hL : L ∈ calC D.M)
    (h17_5 : R17_5At D V₀ V) (hmodel : LieModel (BarInf L) .PSL 2 3 2) : False := by
  obtain ⟨e1⟩ := barO2Z17_equiv_barInf hL
  obtain ⟨e2⟩ := LieModel.nonempty_mulEquiv_alternating_six hmodel
  exact h17_5 L hL 6 (by norm_num) ⟨e1.trans e2⟩

theorem odd_center_barSub {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hL : L ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    Odd (Nat.card (Subgroup.center ↥(barSub V₀ V h.isElemAbelian L))) := by
  classical
  let K := ↥(barSub V₀ V h.isElemAbelian L)
  let φ : Bar2 L →* K := barSubBar2HomOfHyp125 h hL
  have hφs : Function.Surjective φ := barSubBar2HomOfHyp125_surjective h hL
  have hqBar : CFSG.IsQuasisimple (Bar2 L) :=
    CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL.2.2
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨y, hy⟩ := hφs x
  have hφnt : ∃ z, φ z ≠ 1 := ⟨y, by rw [hy]; exact hx⟩
  have hkerle : φ.ker ≤ Subgroup.center (Bar2 L) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqBar hφnt
  have hcenterK : Subgroup.center K = (Subgroup.center (Bar2 L)).map φ :=
    CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hqBar hφs hkerle
  have hoddBar : Odd (Nat.card (Subgroup.center (Bar2 L))) := by
    simpa [Bar2] using uc22p20p_odd_center_bar2 ↥L
  rw [hcenterK]
  exact Odd.of_dvd_nat hoddBar (Subgroup.card_map_dvd (H := Subgroup.center (Bar2 L)) (f := φ))

theorem exists_nontrivial_repr_dMinDeg (K : Type) [Group K] [Finite K] [Nontrivial K] :
    ∃ f : K →* Matrix.GeneralLinearGroup (Fin (dMinDeg K)) (ZMod 2), f ≠ 1 := by
  obtain ⟨n, f, hf⟩ := CFSG.GroupTheory.exists_nontrivial_repr_card K
  have hne : {m : ℕ | ∃ f : K →* Matrix.GeneralLinearGroup (Fin m) (ZMod 2), f ≠ 1}.Nonempty :=
    ⟨n, f, hf⟩
  have hmem := Nat.sInf_mem hne
  have hmem' : dMinDeg K ∈
      {m : ℕ | ∃ f : K →* Matrix.GeneralLinearGroup (Fin m) (ZMod 2), f ≠ 1} := hmem
  exact (Set.mem_setOf_eq.mp hmem')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
