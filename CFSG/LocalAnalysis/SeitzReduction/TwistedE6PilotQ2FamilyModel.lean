module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyRigid
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)


section Torus

variable {k K : Type} [Field k] [Field K]

theorem highRoot_E6_eq : CFSG.SeitzReduction.highRoot .E6 = e6HighestRoot := by
  funext i
  fin_cases i <;> rfl

theorem le_subsystemGroup_of_perfect_of_le_centralizer [Finite k] [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K) {a : ModGL TwistTag.E6.tag K}
    (ha : a ∈ thetaRankOneGroup ι) (ha3 : orderOf a = 3) {Q : Subgroup (ModGL TwistTag.E6.tag K)}
    (hQ : ⁅Q, Q⁆ = Q) (hQC : Q ≤ adjointGroup TwistTag.E6.tag K)
    (hQa : Q ≤ centralizer ({a} : Set (ModGL TwistTag.E6.tag K))) :
    Q ≤ subsystemGroup TwistTag.E6.tag K setA := by
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hk]; rfl)
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [thetaRankOneGroup_eq_range h2K] at ha
  obtain ⟨B, rfl⟩ := ha
  set x : ModGL .E6 k := rootSL2 .E6 k (CFSG.SeitzReduction.highRoot .E6) B with hx
  have hxJ : x ∈ EPilot.highRootSL2 .E6 k := E6Pilot.rootSL2_highRoot_mem_highRootSL2 B
  have hxa : baseChangeGL ι x =
      (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map ι) B := by
    rw [hx, E6Pilot.baseChangeGL_rootSL2_highRoot, highRoot_E6_eq]
    rfl
  have hB3 : orderOf B = 3 := by
    rw [← ha3, orderOf_injective _ (injective_thetaSL2_comp_map h2K ι)]
  have hx3 : orderOf x = 3 := by
    rw [hx, orderOf_injective _ E6Pilot.rootSL2_highRoot_injective, hB3]
  refine (E6Pilot.le_rootSpan_perpRoots_of_perfect_of_le_centralizer_E6 hk hK ι hxJ hx3 hQ hQC
    ?_).trans rootSpan_perpRoots_le_subsystemGroup
  rw [hxa]
  exact hQa

end Torus

section Overlap

variable {K : Type} [Field K]

theorem ovlLevi_le_centralizer_rootRankOneGroup (h2 : (2 : K) = 0) (p : Fin 3) {k : Type}
    [Field k] (ι : k →+* K) :
    ovlLevi h2 p ≤ centralizer (TwistedE6Pilot.rootRankOneGroup ι
      (matRoot (ovlPt p) (Fin.rev (ovlPt p))) : Set (ModGL TwistTag.E6.tag K)) := by
  rw [Subgroup.le_centralizer_iff]
  obtain ⟨-, -, -, -, -, -, -, hpp⟩ := ovl_check p
  have hdisj : Disjoint (ovlSet p) ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) :=
    disjoint_compl_left
  have key : ∀ {x y : Fin 6} (hxy : x ≠ y), x ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) →
      y ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) → ∀ c : K,
      realize h2 (SpecialLinearGroup.transvection hxy c) ∈
        centralizer (ovlLevi h2 p : Set (ModGL TwistTag.E6.tag K)) := by
    intro x y hxy hx hy c
    rw [mem_centralizer_iff]
    rintro _ ⟨M, hM, rfl⟩
    rw [← map_mul, ← map_mul, (LinearPilot.commute_blockSpecialLinear_of_disjoint hdisj hM
      (LinearPilot.transvection_mem_blockSpecialLinear hxy hx hy c)).eq]
  refine sup_le ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    dsimp only
    rw [← realize_transvection_ovl h2 hpp]
    exact key hpp (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (ι c)
  · rintro _ ⟨c, rfl⟩
    dsimp only
    rw [← matRoot_swap_ovl, ← realize_transvection_ovl h2 hpp.symm]
    exact key hpp.symm (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (Finset.mem_insert_self _ _) (ι c)

theorem perfect_le_ovlLevi [Finite K] (h2 : (2 : K) = 0) (p : Fin 3) {k : Type} [Field k]
    (ι : k →+* K) {P : Subgroup (ModGL TwistTag.E6.tag K)}
    (hPA : P ≤ subsystemGroup TwistTag.E6.tag K setA)
    (hPJ : P ≤ centralizer (TwistedE6Pilot.rootRankOneGroup ι
      (matRoot (ovlPt p) (Fin.rev (ovlPt p))) : Set (ModGL TwistTag.E6.tag K)))
    (hP : ⁅P, P⁆ = P) : P ≤ ovlLevi h2 p := by
  obtain ⟨-, -, -, -, -, -, -, hpp⟩ := ovl_check p
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Q₀ := P.comap (realize h2) with hQ₀
  have hQ₀P : Q₀.map (realize h2) = P := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
    · intro x hx
      have hx' : x ∈ (realize h2).range := by
        rw [E6GraphLevi.range_realize h2]
        exact hPA hx
      obtain ⟨B, rfl⟩ := hx'
      exact ⟨B, hx, rfl⟩
  set Q := perfectCore Q₀ with hQ
  have hQperf : ⁅Q, Q⁆ = Q := perfectCore_perfect Q₀
  have hQP : Q.map (realize h2) = P := by
    rw [hQ, CFSG.Quasithin.map_perfectCore, hQ₀P,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hP]
  have hcent := le_centralizer_comap_of_perfect_ovl (realize h2) (ker_realize_le_center_ovl h2)
    hQperf
  rw [hQP] at hcent
  have hJP : TwistedE6Pilot.rootRankOneGroup ι (matRoot (ovlPt p) (Fin.rev (ovlPt p))) ≤
      centralizer (P : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← Subgroup.le_centralizer_iff]
    exact hPJ
  have hT : ∀ {x y : Fin 6} (hxy : x ≠ y),
      x ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) →
      y ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)) →
      SpecialLinearGroup.transvection hxy (1 : K) ∈
        (centralizer (P : Set (ModGL TwistTag.E6.tag K))).comap (realize h2) := by
    intro x y hxy hx hy
    rw [mem_comap, realize_transvection_ovl h2 hxy]
    apply hJP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact mem_sup_left (subset_closure ⟨1, by simp only [map_one]⟩)
    · rw [matRoot_swap_ovl (ovlPt p) (Fin.rev (ovlPt p))]
      exact mem_sup_right (subset_closure ⟨1, by simp only [map_one]⟩)
    · exact absurd rfl hxy
  have hcomm : ∀ A ∈ Q, ∀ i ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)),
      ∀ j ∈ ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6)), ∀ hij : i ≠ j,
        A * SpecialLinearGroup.transvection hij 1 = SpecialLinearGroup.transvection hij 1 * A := by
    intro A hA i hi j hj hij
    exact (mem_centralizer_iff.1 (hcent hA) _ (hT hij hi hj)).symm
  have hQB := LinearPilot.le_blockSpecialLinear_sdiff_of_commute (N := Finset.univ)
    (T := ({ovlPt p, Fin.rev (ovlPt p)} : Finset (Fin 6))) (by rw [Finset.card_pair hpp])
    (by rw [LinearPilot.blockSpecialLinear_univ]; exact le_top) hQperf hcomm
  rw [← Finset.compl_eq_univ_sdiff] at hQB
  rw [← hQP]
  exact Subgroup.map_mono hQB

end Overlap

section TwoTori

variable {k K : Type} [Field k] [Field K]

theorem exists_orderOf_eq_three_of_card {M : Type*} [Group M] {Y : Subgroup M}
    (hY : Nat.card Y = 3) : ∃ y ∈ Y, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 (by rw [hY])
  exact ⟨y, y.2, by rw [← Subgroup.orderOf_coe] at hy; exact hy⟩

theorem le_centralizer_rootRankOneGroup_of_perfect' [Finite k] [Finite K] [CharP K 2]
    (hk : Nat.card k = 2) (hK : Nat.card K = 2 ^ 2) (ι : k →+* K) (p : Fin 3)
    {Y : Subgroup (ModGL TwistTag.E6.tag K)}
    (hYJ : Y ≤ TwistedE6Pilot.rootRankOneGroup ι (matRoot (ovlPt p) (Fin.rev (ovlPt p))))
    (hY : Nat.card Y = 3) {P : Subgroup (ModGL TwistTag.E6.tag K)} (hP : ⁅P, P⁆ = P)
    (hPC : P ≤ adjointGroup TwistTag.E6.tag K)
    (hPY : P ≤ centralizer (Y : Set (ModGL TwistTag.E6.tag K))) :
    P ≤ centralizer (TwistedE6Pilot.rootRankOneGroup ι
      (matRoot (ovlPt p) (Fin.rev (ovlPt p))) : Set (ModGL TwistTag.E6.tag K)) := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  set n := twistedE6RelWeyl K (ovlWord p) with hn
  set α := MulAut.conj n with hα
  have hnC : n ∈ adjointGroup TwistTag.E6.tag K :=
    ((graphFixedRootGroup_le TwistTag.E6 K (RingHom.id K)).trans inf_le_left)
      (twistedE6RelWeyl_mem _ (ovlWord p))
  have hJ := rootRankOneGroup_eq_map_ovlWord (K := K) ι p
  rw [hJ] at hYJ ⊢
  obtain ⟨Y', hY'J, rfl⟩ := exists_le_map_eq_of_le_map_ovl α hYJ
  have hY'card : Nat.card Y' = 3 := by
    rwa [Subgroup.card_map_of_injective α.injective] at hY
  obtain ⟨a, haY, ha3⟩ := exists_orderOf_eq_three_of_card hY'card
  have hPmap : P ≤ (⊤ : Subgroup (ModGL TwistTag.E6.tag K)).map α.toMonoidHom := by
    rw [Subgroup.map_top_of_surjective _ α.surjective]
    exact le_top
  obtain ⟨P', -, rfl⟩ := exists_le_map_eq_of_le_map_ovl α hPmap
  have hP'perf : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective (f := α.toMonoidHom) α.injective
    rw [Subgroup.map_commutator, hP]
  have hP'C : P' ≤ adjointGroup TwistTag.E6.tag K := by
    intro x hx
    have h1 := hPC ⟨x, hx, rfl⟩
    have h2 : x = n⁻¹ * (n * x * n⁻¹) * n := by group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem hnC) h1) hnC
  have hP'Y : P' ≤ centralizer (Y' : Set (ModGL TwistTag.E6.tag K)) := by
    rw [centralizer_map_mulAut_ovl] at hPY
    exact (Subgroup.map_le_map_iff_of_injective α.injective).1 hPY
  have hP'a : P' ≤ centralizer ({a} : Set (ModGL TwistTag.E6.tag K)) :=
    hP'Y.trans (centralizer_le (Set.singleton_subset_iff.2 haY))
  have hP'A := le_subsystemGroup_of_perfect_of_le_centralizer hk hK ι (hY'J haY) ha3 hP'perf
    hP'C hP'a
  have hAJ : P' ≤ centralizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag K)) :=
    hP'A.trans ((subsystemGroup_le_centralizer_thetaSL2 h2K).trans
      (centralizer_le (thetaRankOneGroup_le_range h2K ι)))
  rw [centralizer_map_mulAut_ovl]
  exact Subgroup.map_mono hAJ

theorem le_ovlLevi_of_perfect [Finite k] [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = 2 ^ 2) (h2 : (2 : K) = 0) (ι : k →+* K) (p : Fin 3)
    {A Y : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup ι) (hA : Nat.card A = 3)
    (hYJ : Y ≤ TwistedE6Pilot.rootRankOneGroup ι (matRoot (ovlPt p) (Fin.rev (ovlPt p))))
    (hY : Nat.card Y = 3) {P : Subgroup (ModGL TwistTag.E6.tag K)} (hP : ⁅P, P⁆ = P)
    (hPC : P ≤ adjointGroup TwistTag.E6.tag K)
    (hPA : P ≤ centralizer (A : Set (ModGL TwistTag.E6.tag K)))
    (hPY : P ≤ centralizer (Y : Set (ModGL TwistTag.E6.tag K))) :
    P ≤ ovlLevi h2 p := by
  obtain ⟨a, haA, ha3⟩ := exists_orderOf_eq_three_of_card hA
  have hPL := le_subsystemGroup_of_perfect_of_le_centralizer hk hK ι (hAJ haA) ha3 hP hPC
    (hPA.trans (centralizer_le (Set.singleton_subset_iff.2 haA)))
  exact perfect_le_ovlLevi h2 p ι hPL
    (le_centralizer_rootRankOneGroup_of_perfect' hk hK ι p hYJ hY hP hPC hPY) hP

end TwoTori

end CFSG.SeitzReduction.TwistedE6Pilot
