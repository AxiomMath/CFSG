module

public import CFSG.RankThree.PartOne.K1320.L4Comm
public import CFSG.RankThree.PartOne.K156.Full

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem exists_member (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} {f : ℕ} (h : Sec12Hyp G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hEA : E = A) (hpf : p ∣ 2 ^ f + 1) {zs r₁ : MulAut E} (hzs : zs ∈ reflectionSet p E)
    (hKt : KFAt p E (2 * f) zs) (hr₁L : r₁ ∈ torusImage E L) {y : G}
    (hy : y ∈ Subgroup.normalizer (E : Set G))
    (hty : zs = conjAut E y hy * r₁ * (conjAut E y hy)⁻¹) {b : G}
    (hb : b ∈ autFixedInG E zs) (hb1 : b ≠ 1) :
    ∃ I ∈ thetaComponentsAt p b, kZero p E zs ≤ I ∧
      (I = kZero p E zs ⊔ inSubgroup (aschbacherSolvableCore p) I ∨
        I ∈ thetaCompZeroStarE p E) := by
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  have hLt : KFLiftAt p E zs := KFAt.toLiftAt hKt
  have hqt := hLt.1
  have hbE : b ∈ E := Subgroup.map_subtype_le _ hb
  obtain ⟨I, hI, hKI⟩ := exists_thetaComponentsAt_ge_of_hyp h hS hb1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hb
    (kZero_le_centralizer_fixed p E zs) (kZero_mem_thetaComponents hp hqt)
  refine ⟨I, hI, hKI, ?_⟩
  have hYmem : conjBy y L ∈ thetaCompZeroStarE p E :=
    conjBy_mem_thetaCompZeroStarE hp hy hF13.inZeroStar
  obtain ⟨B', c'', hB', -, -, hY12, -, hY13, -⟩ := hRe G p A c L E h hF13 hT _ hYmem
  have htY : zs ∈ torusImage E (conjBy y L) := by
    rw [torusImage_conjBy E L hy, hty]
    exact Subgroup.mem_map_of_mem (MulAut.conj (conjAut E y hy)).toMonoidHom hr₁L
  have hEBp : E = B' :=
    (Subgroup.eq_of_le_of_card_ge hB'.1 (by rw [hcard, hB'.2.2.1])).symm
  have hsplit : K133.SplitType p (kZero p E zs) :=
    K133.splitType_of_psl_two hp hp2 hKt.2.1 (dvd_two_pow_double_sub_one hpf)
  exact K133One.kf133One_clause_one_of_liftAt hS hY12 hY13 hEBp hzs htY hLt hsplit hb hb1 hI hKI

theorem eq_of_alt_one (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hpf : p ∣ 2 ^ f + 1) {zs : MulAut E}
    (hzs : zs ∈ reflectionSet p E) (hKt : KFAt p E (2 * f) zs)
    {b : G} (hb : b ∈ autFixedInG E zs)
    (hb1 : b ≠ 1) {I : Subgroup G} (hI : I ∈ thetaComponentsAt p b)
    (hKI : kZero p E zs ≤ I)
    (hi : I = kZero p E zs ⊔ inSubgroup (aschbacherSolvableCore p) I) :
    kZero p E zs ∈ thetaComponentsAt p b := by
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hLt : KFLiftAt p E zs := KFAt.toLiftAt hKt
  have hsplit : K133.SplitType p (kZero p E zs) :=
    K133.splitType_of_psl_two hp hp2 hKt.2.1 (dvd_two_pow_double_sub_one hpf)
  have hmovK : autMovedInG E zs ≤ kZero p E zs := hKt.2.2.2.1
  have hI0 : I ∈ sectionTenZero p E :=
    K133.mem_sectionTenZero_of_split h hzs hLt.isKt hsplit hmovK hb hb1 hI hKI
  have hsetup : SteinbergBM.SectionTenSetup G p E := by
    rw [hEA]
    exact h.setup
  have hIq : CFSG.IsQuasisimple ↥I := hFull hS hTwo G p E hsetup I hI0
  have hrel : sectionTenRel p I (kZero p E zs) := by
    unfold sectionTenRel
    rw [inf_eq_right.2 hKI]
    exact hi
  have hIK : I ≤ kZero p E zs := K156.le_of_sectionTenRel_of_quasisimple hp hIq hrel
  have : I = kZero p E zs := le_antisymm hIK hKI
  rw [← this]
  exact hI

end CFSG.RankThree.PartOne.K1327
