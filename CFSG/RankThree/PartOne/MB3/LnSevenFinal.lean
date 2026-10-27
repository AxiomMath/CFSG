module

public import CFSG.RankThree.PartOne.MB3.LnSevenReduce
public import CFSG.RankThree.PartOne.MB3.FieldTail
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj
  StatedProj StatedSL)

noncomputable def slEquivStatedProj (m : ℕ) (hm : 1 ≤ m) :
    SpecialLinearGroup (Fin m) (ZMod 2) ≃* StatedProj (StatedSL m (ZMod 2)) :=
  (CFSG.RankThree.PartOne.Sec109.projectiveSLEquivSL_two (K := ZMod 2) (by simp) hm).trans
    ((LinearCover.projectiveSpecialLinearEquivProjectiveSL m (ZMod 2)).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj m (ZMod 2)))

theorem isSimpleGroup_sl_two {m : ℕ} (hm : 3 ≤ m) :
    IsSimpleGroup (SpecialLinearGroup (Fin m) (ZMod 2)) := by
  have h := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := m) (by omega)
    (Or.inl hm)).2.1
  exact ((CFSG.RankThree.PartOne.Sec109.projectiveSLEquivSL_two (K := ZMod 2) (by simp)
    (by omega)).trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL m (ZMod 2)).symm
    ).isSimpleGroup

theorem statedModel_two {m : ℕ} (hm : 3 ≤ m) {H : Type} [Group H]
    (e : H ≃* SpecialLinearGroup (Fin m) (ZMod 2)) : StatedClassicalModel H .PSL m 2 1 := by
  refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, ZMod 2, inferInstance, inferInstance,
    by simp, ⟨e.trans (slEquivStatedProj m (by omega))⟩⟩
  · intro h
    have := congrArg Prod.fst h
    simp at this
    omega
  · intro h
    have := congrArg Prod.fst h
    simp at this
    omega

theorem statedModel_F8 {H : Type} [Group H] (e : H ≃* SpecialLinearGroup (Fin 2) F8) :
    StatedClassicalModel H .PSL 2 2 3 := by
  refine ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, F8, inferInstance,
    inferInstance, by rw [card_F8]; norm_num,
    ⟨e.trans (slPslEquiv_F8.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F8))⟩⟩

@[expose] def infCenEquiv {G : Type} [Group G] (L : Subgroup G) (b : L) :
    ↥(L ⊓ Subgroup.centralizer ({(b : G)} : Set G)) ≃*
      ↥(Subgroup.centralizer ({b} : Set L)) where
  toFun x := ⟨⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext h⟩
  invFun x := ⟨x.1.1, Subgroup.mem_inf.mpr ⟨x.1.2, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl

theorem det_eq_one_fin {k : ℕ} (hk : k ≤ 1) (T : Matrix (Fin k) (Fin k) (ZMod 2))
    (hT : T.det = 1) : T = 1 := by
  interval_cases k
  · exact Subsingleton.elim _ _
  · ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_unique] using hT

theorem not_dvd_card_SL_six (k : ℕ) (hk : k ≤ 1) :
    ¬ 7 ^ 3 ∣ Nat.card (SpecialLinearGroup (Fin (6 + k)) (ZMod 2)) := by
  rw [card_SL_eq (by omega), Nat.card_zmod]
  interval_cases k <;> decide +kernel

theorem isSimpleGroup_sl_sum (k : ℕ) :
    IsSimpleGroup (SpecialLinearGroup (Fin 3 ⊕ Fin k) (ZMod 2)) := by
  have h := isSimpleGroup_sl_two (m := 3 + k) (by omega)
  exact (slReEquiv (finSumFinEquiv : Fin 3 ⊕ Fin k ≃ Fin (3 + k))).isSimpleGroup

theorem compModel_inf_centralizer {k : ℕ} (hk : k ≤ 1) {G : Type} [Group G] (L : Subgroup G)
    (θ : L ≃* SpecialLinearGroup (Fin (6 + k)) (ZMod 2)) {b : G} (hb : b ∈ L)
    (hb7 : orderOf b = 7) :
    CompModel (SpecialLinearGroup (Fin 3 ⊕ Fin k) (ZMod 2)) (SpecialLinearGroup (Fin 2) F8)
      ↥(L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  let e : (Fin 3 ⊕ Fin 3) ⊕ Fin k ≃ Fin (6 + k) :=
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin k))).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  have hM : ¬ 7 ^ 3 ∣ Nat.card (SpecialLinearGroup ((Fin 3 ⊕ Fin 3) ⊕ Fin k) (ZMod 2)) := by
    rw [Nat.card_congr (slReEquiv e).toEquiv]
    exact not_dvd_card_SL_six k hk
  let b' : L := ⟨b, hb⟩
  have hb'7 : orderOf (slReEquiv e.symm (θ b')) = 7 := by
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, ← hb7]
    exact (orderOf_injective L.subtype Subtype.val_injective b').symm
  have hgood : Good (Fin 3 ⊕ Fin k) (slReEquiv e.symm (θ b')) :=
    good_of_orderOf_seven (det_eq_one_fin hk) (isSimpleGroup_sl_sum k) hM hb'7
  exact CompModel.of_mulEquiv (infCenEquiv L b')
    (Good.of_mulEquiv θ (Good.of_mulEquiv (slReEquiv e.symm) hgood))

theorem fieldComponentsLn2_holds : FieldComponentsLn2 := by
  intro G _ _ L n hn hL b hb hb7 E hE hcomp
  obtain ⟨θ⟩ := CFSG.RankThree.PartOne.Sec109.exists_mulEquiv_sl_two hL
  obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k ≤ 1 ∧ n = 6 + k := by
    rcases hn with rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  have hmodel := compModel_inf_centralizer hk L θ hb hb7
  have e : ↥E ≃* ↥(E.subgroupOf (L ⊓ Subgroup.centralizer ({b} : Set G))) :=
    (Subgroup.subgroupOfEquivOfLe hE).symm
  obtain ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ := hmodel _ hcomp
  · left
    have h3 : 6 + k - 3 = 3 + k := by omega
    rw [h3]
    exact statedModel_two (by omega) ((e.trans f).trans (slReEquiv finSumFinEquiv))
  · right
    exact statedModel_F8 (e.trans f)

end CFSG.RankThree.PartOne.MB3
