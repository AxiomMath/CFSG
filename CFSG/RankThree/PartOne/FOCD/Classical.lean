module

public import CFSG.RankThree.PartOne.FOCD.Bridge
import CFSG.RankThree.PartOne.KF.F128Cls
import CFSG.RankThree.PartOne.S11c.SpFourNoComponent
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimePrimeCentralizer

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel
  projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)

theorem localRank_le_three {p : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime)
    (hLR : LocalRankLeTwo p T) : localRank p T ≤ 3 := by
  by_contra h
  exact false_of_three_le_localRank hp hLR (by omega)

theorem statedModel_top {T : Type} [Group T] (hZ : Subgroup.center T = ⊥) {t : StatedLieTag}
    {n p f : ℕ} (h : StatedClassicalModel T t n p f) :
    StatedClassicalModel (↥(⊤ : Subgroup T) ⧸ Subgroup.center ↥(⊤ : Subgroup T)) t n p f :=
  statedClassicalModel_congr (topQuotEquiv hZ) h

theorem psl_params {p n f : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Subgroup.center T = ⊥) (hLR : LocalRankLeTwo p T) (hn : 3 ≤ n)
    (hmod : StatedClassicalModel T .PSL n p f) : n ≤ 4 ∧ f ≤ 3 := by
  have h := linear_small_parameters (X := T) (Y := ⊤) hn hp (by omega) (statedModel_top hZ hmod)
    (localRank_le_three hp hLR)
  omega

theorem psu_params {p n f : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Subgroup.center T = ⊥) (hLR : LocalRankLeTwo p T) (hn : 3 ≤ n)
    (hmod : StatedClassicalModel T .PSU n p f) : n ≤ 4 ∧ f ≤ 3 := by
  have h := unitary_small_parameters (X := T) (Y := ⊤) hn hp (by omega) (statedModel_top hZ hmod)
    (localRank_le_three hp hLR)
  omega

theorem psp_params {p n f : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Subgroup.center T = ⊥) (hLR : LocalRankLeTwo p T)
    (hmod : StatedClassicalModel T .PSp n p f) : n = 2 ∧ f ≤ 3 :=
  (CFSG.RankThree.GroupTheory.odd_symplectic_actual_cover_rank_four_and_small_parameters.{0} hp
    (by omega)).2 T ⊤ n (Or.inr (Or.inr (localRank_le_three hp hLR))) (statedModel_top hZ hmod)

theorem orth_false {p n f : ℕ} {T : Type} [Group T] [Finite T] {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Subgroup.center T = ⊥) (hLR : LocalRankLeTwo p T)
    (hmod : StatedClassicalModel T t n p f) : False :=
  orthogonal_model_absurd (X := ⊤) (H := T) ht hp (by omega) (statedModel_top hZ hmod)
    (localRank_le_three hp hLR)

theorem noCompOf_psl2 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) : NoCompOf p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  have : Fact p.Prime := ⟨hp⟩
  refine noCompOf_of_forall fun b hb1 hbp L => ?_
  have hb : orderOf b = p := orderOf_eq_prime hbp hb1
  have hpg : IsPGroup p ↥(Subgroup.centralizer
      ({b} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) := by
    rw [IsPGroup.iff_card]
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrd => ?_⟩
    by_contra hrp
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrd
    exact GorensteinWalter.psl2_no_commuting_distinct_prime_order (r := p) (p := r) hK hrp hb
      (a := b) (b := (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
      (by rw [Subgroup.orderOf_coe]; exact hy)
      (Subgroup.mem_centralizer_singleton_iff.1 y.2).symm
  have : Group.IsNilpotent ↥(Subgroup.centralizer
      ({b} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) := hpg.isNilpotent
  have : Group.IsSolvable ↥(Subgroup.centralizer
      ({b} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) := inferInstance
  exact not_isComponent_of_isSolvable L

theorem noCompOf_of_inner_fixed {p : ℕ} {T : Type} [Group T] (hp : p.Prime)
    (hZ : Subgroup.center T = ⊥)
    (h : ∀ β : MulAut T, β ∈ (MulAut.conj : T →* MulAut T).range → orderOf β = p →
      ∀ L : Subgroup ((β : T →* T).eqLocus (MonoidHom.id T)), ¬ CFSG.IsComponent L) :
    NoCompOf p T := by
  have : Fact p.Prime := ⟨hp⟩
  refine noCompOf_of_forall fun b hb1 hbp L => ?_
  have hβp : (MulAut.conj b : MulAut T) ^ p = 1 := by
    rw [← map_pow (MulAut.conj : T →* MulAut T), hbp, map_one]
  have hβ1 : (MulAut.conj b : MulAut T) ≠ 1 := by
    intro h1
    apply hb1
    have hb : b ∈ Subgroup.center T := Subgroup.mem_center_iff.2 fun g => by
      have := congrArg (fun γ : MulAut T => γ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [hZ] at hb
    exact hb
  have hord := orderOf_eq_prime hβp hβ1
  have h2 := h (MulAut.conj b) ⟨b, rfl⟩ hord
  rw [CFSG.RankThree.CAInnerDefining.eqLocus_conj_eq_centralizer] at h2
  exact h2 L

theorem noCompOf_psl {n p f : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Subgroup.center T = ⊥) (hLR : LocalRankLeTwo p T)
    (hmod : StatedClassicalModel T .PSL n p f) : NoCompOf p T := by
  have hf : 1 ≤ f := hmod.1.2.1
  have hn2 : 2 ≤ n := hmod.1.2.2.1
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    exact NoCompOf.of_mulEquiv (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
      (noCompOf_psl2 hp hK)
  · obtain ⟨hn4, -⟩ := psl_params hp hp5 hZ hLR h hmod
    exact noCompOf_of_inner_fixed hp hZ fun β hβ hord =>
      CFSG.RankThree.CAInnerDefining.linear_unitary_three_four_inner_defining_fixed_component_free
        hp (by omega) hf (by omega) (Or.inl rfl) hmod β hβ hord

theorem noCompOf_psu {n p f : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Subgroup.center T = ⊥) (hLR : LocalRankLeTwo p T)
    (hmod : StatedClassicalModel T .PSU n p f) : NoCompOf p T := by
  have hf : 1 ≤ f := hmod.1.2.1
  have hn3 : 3 ≤ n := hmod.1.2.2.1
  obtain ⟨hn4, -⟩ := psu_params hp hp5 hZ hLR hn3 hmod
  exact noCompOf_of_inner_fixed hp hZ fun β hβ hord =>
    CFSG.RankThree.CAInnerDefining.linear_unitary_three_four_inner_defining_fixed_component_free
      hp (by omega) hf (by omega) (Or.inr rfl) hmod β hβ hord

theorem noCompOf_psp {n p f : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Subgroup.center T = ⊥) (hLR : LocalRankLeTwo p T)
    (hmod : StatedClassicalModel T .PSp n p f) : NoCompOf p T := by
  have hf : 1 ≤ f := hmod.1.2.1
  obtain ⟨rfl, -⟩ := psp_params hp hp5 hZ hLR hmod
  exact noCompOf_of_inner_fixed hp hZ fun β hβ hord =>
    HNRed.oddSymplecticFourInnerDefiningFixedComponentFree_holds p f hp (by omega) hf T hmod β hβ
      hord

theorem innerComp_classical {t : StatedLieTag} {n p f : ℕ} {T : Type} [Group T] [Finite T]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hs : IsSimpleGroup T)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hmod : StatedClassicalModel T t n p f) : InnerComp p T := by
  have := hs
  refine innerComp_of_noCompOf fun hLR => ?_
  by_cases hcomm : ∀ a b : T, a * b = b * a
  · exact noCompOf_of_comm hcomm
  · have hnab : ∃ a b : T, a * b ≠ b * a := by
      by_contra h
      exact hcomm fun a b => by_contra fun h' => h ⟨a, b, h'⟩
    have hZ := center_eq_bot_of_nonab hs hnab
    rcases ht with rfl | rfl | rfl | ht
    · exact noCompOf_psl hp hp5 hZ hLR hmod
    · exact noCompOf_psu hp hp5 hZ hLR hmod
    · exact noCompOf_psp hp hp5 hZ hLR hmod
    · exact (orth_false ht hp hp5 hZ hLR hmod).elim

end CFSG.RankThree.PartOne.FOCD
