module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4ParabolicsGen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4
public import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Step
public import CFSG.Quasithin.Recognition.St84.Gen.D4qRadical
public import CFSG.Quasithin.Background.RonanF918Four
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint
open CFSG.Blueprint.Chevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect map_perfectCore)
open CFSG.Quasithin.CLG2
open CFSG.GroupTheory
open CFSG.SL2MinimalFaithful
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
open CFSG.LieType.Chevalley
open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement MatrixGroups

section Certificates


theorem card_fixedPosWeylGroup_fa1 {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1)) :
    Nat.card ↥(fixedPosWeylGroup TwistTag.D4 K σ.toRingHom fa1) =
      3 * Nat.card ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set U := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom with hU
  set V := graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom fa1 with hV
  set N := fixedPosWeylGroup TwistTag.D4 K σ.toRingHom fa1 with hN
  obtain ⟨R, -, hNV, hsup, hRV, hker⟩ := fixed_structure (t := TwistTag.D4) σ fa1
  have hRinj : Function.Injective R := fixed_rankOne_injective σ fa1 hker
  have hLa : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) = 2 := by
    have h := card_orbitField_D4_orientation (ℓ := 2) Nat.prime_two (f := 1) le_rfl
      (K := K) hK (r := 1) (Or.inl rfl) (σ := σ.toRingHom)
      (fun c => by rw [pow_one]; exact hσ c) fa1
    simpa [orbit_card_fa1, pow_one] using h
  have hRcard : Nat.card ↥R.range = 6 := by
    let e : SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) ≃* ↥R.range :=
      MonoidHom.ofInjective hRinj
    rw [← Nat.card_congr e.toEquiv, card_specialLinearGroup_fin_two, hLa]
    norm_num
  have hUcard : Nat.card ↥U = 2 ^ 12 := by
    rw [hU]
    simpa [pow_one] using
      (CFSG.Quasithin.H13.F431.D4q.NFq.card_U (f := 1) σ le_rfl hK
        (fun c => by rw [pow_one]; exact hσ c))
  have hVcard : Nat.card ↥V = 2 ^ 11 := by
    rw [hV]
    have h := CFSG.Quasithin.F112R.card_d4Q1 σ (f := 1) le_rfl hK
      (fun c => by rw [pow_one]; exact hσ c)
    rwa [show Q1 σ = graphFixedSimpleComplement TwistTag.D4 K σ.toRingHom fa1 from
      radical_eq_simpleComplement σ.toRingHom fa1 supp_fa1] at h
  set d := V.relIndex N with hd
  have hd_eq : d = (R.range ⊓ V).relIndex R.range := by
    have h := (relIndex_sup_eq_relIndex_inf_of_le_normalizer (H := R.range) (K := V) hRV).2
    rw [sup_comm] at h
    rw [hd, hN, ← hsup]
    exact h
  have hdvd : d ∣ 6 := by
    rw [hd_eq, ← hRcard]
    exact Subgroup.relIndex_dvd_card _ _
  have hUleN : U ≤ N := by
    rw [hU, hN]
    exact graphFixedPosUnipotent_le_fixedPosWeylGroup fa1
  have hlag : Nat.card ↥U ∣ Nat.card ↥N := by
    have h := Subgroup.card_subgroup_dvd_card (U.subgroupOf N)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleN).toEquiv] at h
  have hNcard : Nat.card ↥N = 2 ^ 11 * d := by
    have h := Subgroup.relIndex_mul_card (H := V) (K := N)
    rw [inf_eq_left.mpr (by rw [hN, ← hsup]; exact le_sup_left), hVcard] at h
    rw [mul_comm] at h
    exact h.symm
  have h2dvd : 2 ∣ d := by
    have h : 2 ^ 12 ∣ 2 ^ 11 * d := by
      rw [← hUcard, ← hNcard]
      exact hlag
    have h' : 2 ^ 11 * 2 ∣ 2 ^ 11 * d := by
      simpa using h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2 ^ 11) h'
  have hdne2 : d ≠ 2 := by
    intro hd2
    have hN2 : Nat.card ↥N = Nat.card ↥U := by
      rw [hNcard, hd2, hUcard]
      norm_num
    have hUN : N = U := (Subgroup.eq_of_le_of_card_ge hUleN (le_of_eq hN2)).symm
    have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa1) ∈ N := by
      rw [hN]
      exact canonicalRep_orbitReflection_mem_fixedPosWeylGroup fa1
    rw [hUN] at hn
    have hP : canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa1) ∈
        graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa0} :=
      (graphFixedPosUnipotent_le_graphFixedRootBorel (t := TwistTag.D4) (K := K)
        (σ := σ.toRingHom)).trans
        (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _) hn
    have hiff := (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff (t := TwistTag.D4)
      (K := K) (σ := σ.toRingHom) (hσ := σ.surjective)
      (J := ({fa0} : Set (Fin TwistTag.D4.foldedTag.rank))) (a := fa1)).1 hP
    simp only [Set.mem_singleton_iff] at hiff
    exact absurd hiff (by decide)
  have hdpos : 0 < d := by
    by_contra h
    have h0 : d = 0 := by omega
    rw [h0, mul_zero] at hNcard
    exact (Nat.card_pos (α := ↥N)).ne' hNcard
  have hd6 : d = 6 := by
    have hdle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨e, he⟩ := h2dvd
    have he1 : 1 ≤ e := by omega
    have he3 : e ≤ 3 := by omega
    interval_cases e
    · exact absurd (he.trans (by norm_num)) hdne2
    · rw [he] at hdvd; norm_num at hdvd
    · exact he.trans (by norm_num)
  rw [hNcard, hd6, hUcard]
  norm_num

theorem fixedPosWeylGroup_fa1_subgroupOf_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1)) :
    (fixedPosWeylGroup TwistTag.D4 K σ.toRingHom fa1).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      ⁅(graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        (graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)⁆ ⊔
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set U := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom with hU
  set N := fixedPosWeylGroup TwistTag.D4 K σ.toRingHom fa1 with hN
  set P := graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1} with hP
  set A := ⁅P.subgroupOf C, P.subgroupOf C⁆ ⊔ U.subgroupOf C with hA
  have hPC : P ≤ C := graphFixedParabolic_le _ _ _ _
  have hUC : U ≤ C := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hNC : N ≤ C :=
    (fixedPosWeylGroup_le_graphFixedParabolic_singleton σ.surjective fa1).trans hPC
  have hPN : ⁅P, P⁆ ≤ N := commutator_graphFixedParabolic_le_fixedPosWeylGroup σ.surjective fa1
  have hUleN : U ≤ N := graphFixedPosUnipotent_le_fixedPosWeylGroup fa1
  have hUP : U ≤ P := (graphFixedPosUnipotent_le_graphFixedRootBorel (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom)).trans (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
  have hcomm : ⁅P.subgroupOf C, P.subgroupOf C⁆ = (⁅P, P⁆).subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPC,
      Subgroup.map_subgroupOf_eq_of_le (hPN.trans hNC)]
  have hA_le_N : A ≤ N.subgroupOf C := by
    rw [hA]
    refine sup_le ?_ (Subgroup.subgroupOf_mono C hUleN)
    rw [hcomm]
    exact Subgroup.subgroupOf_mono C hPN
  have hNcard : Nat.card ↥(N.subgroupOf C) = 3 * Nat.card ↥(U.subgroupOf C) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv]
    exact card_fixedPosWeylGroup_fa1 σ hK hσ
  have hAne : A ≠ U.subgroupOf C := by
    intro hAeq
    have hcommle : ⁅P.subgroupOf C, P.subgroupOf C⁆ ≤ U.subgroupOf C := by
      rw [← hAeq]
      exact le_sup_left
    have hforward : ∀ g ∈ P.subgroupOf C, ∀ u ∈ U.subgroupOf C,
        g * u * g⁻¹ ∈ U.subgroupOf C := by
      intro g hg u hu
      have huP : u ∈ P.subgroupOf C := Subgroup.subgroupOf_mono C hUP hu
      have hc : ⁅g, u⁆ ∈ ⁅P.subgroupOf C, P.subgroupOf C⁆ :=
        Subgroup.commutator_mem_commutator hg huP
      have hcU : ⁅g, u⁆ ∈ U.subgroupOf C := hcommle hc
      have hconj : g * u * g⁻¹ = ⁅g, u⁆ * u := by
        simp [commutatorElement_def, mul_assoc]
      rw [hconj]
      exact (U.subgroupOf C).mul_mem hcU hu
    have hnorm : P.subgroupOf C ≤ Subgroup.normalizer (U.subgroupOf C : Set C) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · exact hforward g hg u
      · intro hgu
        have hinv : g⁻¹ ∈ P.subgroupOf C := (P.subgroupOf C).inv_mem hg
        have h := hforward g⁻¹ hinv (g * u * g⁻¹) hgu
        convert h using 2
        group
    obtain ⟨-, hcov, -, -, -, -, -⟩ := triality_named_covers (f := 1) le_rfl σ hK hσ
    have hlt : Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C) < P.subgroupOf C :=
      ((hcov (P.subgroupOf C)).2 (Or.inr rfl)).lt
    exact hlt.not_ge hnorm
  have hAcard_dvd : Nat.card ↥A ∣ Nat.card ↥(N.subgroupOf C) := by
    have h := Subgroup.card_subgroup_dvd_card (A.subgroupOf (N.subgroupOf C))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_N).toEquiv] at h
  have hUleA : U.subgroupOf C ≤ A := by
    rw [hA]
    exact le_sup_right
  have hUcard_dvd_A : Nat.card ↥(U.subgroupOf C) ∣ Nat.card ↥A := by
    have h := Subgroup.card_subgroup_dvd_card ((U.subgroupOf C).subgroupOf A)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUleA).toEquiv] at h
  obtain ⟨k, hk⟩ := hUcard_dvd_A
  obtain ⟨l, hl⟩ := hAcard_dvd
  have hlt : Nat.card ↥(U.subgroupOf C) < Nat.card ↥A := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hUleA) ?_
    intro heq
    exact hAne (Subgroup.eq_of_le_of_card_ge hUleA (le_of_eq heq.symm)).symm
  have hk1 : 1 < k := by
    have h : Nat.card ↥(U.subgroupOf C) * 1 < Nat.card ↥(U.subgroupOf C) * k := by
      simpa [hk] using hlt
    exact Nat.lt_of_mul_lt_mul_left (a := Nat.card ↥(U.subgroupOf C))
      (by simpa using h)
  have hkl : k * l = 3 := by
    have h1 : 3 * Nat.card ↥(U.subgroupOf C) = Nat.card ↥(U.subgroupOf C) * (k * l) := by
      rw [← hNcard, hl, hk, mul_assoc]
    have h1' : 3 * Nat.card ↥(U.subgroupOf C) =
        (k * l) * Nat.card ↥(U.subgroupOf C) := by
      rwa [mul_comm (Nat.card ↥(U.subgroupOf C)) (k * l)] at h1
    exact (Nat.mul_right_cancel (Nat.card_pos (α := ↥(U.subgroupOf C))) h1').symm
  have hk3 : k = 3 := by
    have hkdvd : k ∣ 3 := ⟨l, hkl.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 hkdvd with h | h
    · omega
    · exact h
  have hl1 : l = 1 := by
    have h : 3 * l = 3 * 1 := by
      calc 3 * l = k * l := by rw [hk3]
        _ = 3 := hkl
        _ = 3 * 1 := (mul_one 3).symm
    exact Nat.mul_left_cancel (by norm_num : 0 < 3) h
  have hAcardN : Nat.card ↥A = Nat.card ↥(N.subgroupOf C) := by
    have h1 : Nat.card ↥A = Nat.card ↥(U.subgroupOf C) * 3 := by
      rw [hk, hk3]
    have h2 : Nat.card ↥(N.subgroupOf C) = Nat.card ↥(U.subgroupOf C) * 3 := by
      rw [hl, hk, hk3, hl1, mul_one]
    rw [h1, h2]
  have hAeq : A = N.subgroupOf C :=
    Subgroup.eq_of_le_of_card_ge hA_le_N (le_of_eq hAcardN.symm)
  exact hAeq.symm

theorem perfectCore_P0_sup_eq_top {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1)) :
    perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa0}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ⊔
      (fixedPosWeylGroup TwistTag.D4 K σ.toRingHom fa1).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  set U := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom with hU
  set N := fixedPosWeylGroup TwistTag.D4 K σ.toRingHom fa1 with hN
  set P0 := graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa0} with hP0
  set P1 := graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1} with hP1
  have hP0C : P0 ≤ C := graphFixedParabolic_le _ _ _ _
  have hP1C : P1 ≤ C := graphFixedParabolic_le _ _ _ _
  have hNC : N ≤ C :=
    (fixedPosWeylGroup_le_graphFixedParabolic_singleton σ.surjective fa1).trans hP1C
  have hUC : U ≤ C := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUleN : U ≤ N := graphFixedPosUnipotent_le_fixedPosWeylGroup fa1
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    refine RingHom.ext fun c => ?_
    have hc : c ^ ((2 ^ 1) ^ 3) = c := by
      have : Fintype K := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    convert hc using 2
  have hU2 : IsPGroup 2 U := by
    rw [hU]
    exact isPGroup_posUnipotent σ hσ3
  have hL0 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) = 2 ^ 3 := by
    have h := card_orbitField_D4_orientation (ℓ := 2) Nat.prime_two (f := 1) le_rfl
      (K := K) hK (r := 1) (Or.inl rfl) (σ := σ.toRingHom)
      (fun c => by rw [pow_one]; exact hσ c) fa0
    simpa [orbit_card_fa0, pow_one] using h
  have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom fa0), s.card = 4 :=
    exists_finset_card_four (by rw [hL0]; norm_num)
  have hns : ¬ Group.IsSolvable ↥(perfectCore (P0.subgroupOf C)) := by
    obtain ⟨g, hg, hk⟩ := exists_levi_hom_fixed (t := TwistTag.D4) σ fa0 hU2 hL4
    intro hs
    haveI : Group.IsSolvable ↥(perfectCore (P0.subgroupOf C)) := hs
    haveI : IsSimpleGroup (SL2 ↥(orbitField TwistTag.D4 K σ.toRingHom fa0)) :=
      sl2_isSimple (K := ↥(orbitField TwistTag.D4 K σ.toRingHom fa0)) hL4
    obtain ⟨a, b, hab⟩ := sl2_nonabelian (K := ↥(orbitField TwistTag.D4 K σ.toRingHom fa0)) hL4
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr
      (Group.isSolvable_of_surjective (f := g) hg) a b)
  set A := perfectCore (P0.subgroupOf C) ⊔ N.subgroupOf C with hA
  by_contra hne
  obtain ⟨M, hMcoat, hAM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom A).resolve_left hne
  have hUM : U.subgroupOf C ≤ M :=
    (Subgroup.subgroupOf_mono C hUleN).trans (le_sup_right.trans hAM)
  have hres := triality_residualOvergroupsAt σ
  obtain ⟨j, hMj⟩ := (hres.2.2.1 M hUM).1 (IsCoatom.covBy_top hMcoat)
  rcases foldedRank_D4_cases (d4Index j) with hj | hj
  · have hMP0 : M = P0.subgroupOf C := by
      rw [hMj]
      change (graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf C =
        P0.subgroupOf C
      rw [hj, hP0]
      rfl
    have hNle : N.subgroupOf C ≤ P0.subgroupOf C :=
      (le_sup_right.trans hAM).trans (le_of_eq hMP0)
    have hn : canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa1) ∈ N := by
      rw [hN]
      exact canonicalRep_orbitReflection_mem_fixedPosWeylGroup fa1
    have hnC : canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa1) ∈ C := hNC hn
    have hnN : (⟨canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa1), hnC⟩ : C) ∈ N.subgroupOf C := hn
    have hnP0 : (⟨canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa1), hnC⟩ : C) ∈ P0.subgroupOf C := hNle hnN
    have hnP0' : canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection fa1) ∈ P0 := by
      simpa using (Subgroup.mem_subgroupOf.mp hnP0)
    have hiff := (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff (t := TwistTag.D4)
      (K := K) (σ := σ.toRingHom) (hσ := σ.surjective)
      (J := ({fa0} : Set (Fin TwistTag.D4.foldedTag.rank)))
      (a := fa1)).1 (by simpa [hP0] using hnP0')
    simp only [Set.mem_singleton_iff] at hiff
    exact absurd hiff (by decide)
  · have hMP1 : M = P1.subgroupOf C := by
      rw [hMj]
      change (graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf C =
        P1.subgroupOf C
      rw [hj, hP1]
      rfl
    have hpc_le : perfectCore (P0.subgroupOf C) ≤ P0.subgroupOf C ⊓ P1.subgroupOf C := by
      refine le_inf (perfectCore_le _) ?_
      exact (le_sup_left.trans hAM).trans (le_of_eq hMP1)
    have hd01 : (d4Index (0 : Fin 2) = fa0 ∧ d4Index (1 : Fin 2) = fa1) ∨
        (d4Index (0 : Fin 2) = fa1 ∧ d4Index (1 : Fin 2) = fa0) := by
      rcases foldedRank_D4_cases (d4Index (0 : Fin 2)) with h0 | h0 <;>
        rcases foldedRank_D4_cases (d4Index (1 : Fin 2)) with h1 | h1
      · exfalso
        exact (by decide : (0 : Fin 2) ≠ 1) (d4Index_injective (h0.trans h1.symm))
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
      · exfalso
        exact (by decide : (0 : Fin 2) ≠ 1) (d4Index_injective (h0.trans h1.symm))
    haveI hsolv : Group.IsSolvable ↥(P0.subgroupOf C ⊓ P1.subgroupOf C) := by
      rcases hd01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have hh : Group.IsSolvable ↥((graphFixedParabolic TwistTag.D4 K σ.toRingHom
            {d4Index (0 : Fin 2)}).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓
            (graphFixedParabolic TwistTag.D4 K σ.toRingHom
              {d4Index (1 : Fin 2)}).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hres.2.2.2.1
        rw [h0, h1] at hh
        exact hh
      · have hh : Group.IsSolvable ↥((graphFixedParabolic TwistTag.D4 K σ.toRingHom
            {d4Index (0 : Fin 2)}).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓
            (graphFixedParabolic TwistTag.D4 K σ.toRingHom
              {d4Index (1 : Fin 2)}).subgroupOf
              (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hres.2.2.2.1
        rw [h0, h1] at hh
        rw [inf_comm] at hh
        exact hh
    exact hns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hpc_le)
      (Subgroup.inclusion_injective hpc_le))

end Certificates

theorem k_3D4TwoParabolicGen_holds :
    K_3D4TwoParabolicGen := by
  intro X _ _ hD S hS
  classical
  have hCE : ChevalleyExceptionalModel X .trialityD4 2 1 :=
    LieModel.chevalleyExceptionalModel hD (by decide)
  obtain ⟨K, hF, hFin, σ, φ, hK, hσ, hUφ, -, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.even_rank_two_residual_triality hCE hS
  letI : Field K := hF
  letI : Finite K := hFin
  have hK3 : Nat.card K = 2 ^ (3 * 1) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  let C : Subgroup (ModGL TwistTag.D4.tag K) :=
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  set U := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom with hU
  set N := fixedPosWeylGroup TwistTag.D4 K σ.toRingHom fa1 with hN
  set P0 := graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa0} with hP0
  set P1 := graphFixedParabolic TwistTag.D4 K σ.toRingHom {fa1} with hP1
  have hP0C : P0 ≤ C := graphFixedParabolic_le _ _ _ _
  have hP1C : P1 ≤ C := graphFixedParabolic_le _ _ _ _
  have hUC : U ≤ C := graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUleN : U ≤ N := graphFixedPosUnipotent_le_fixedPosWeylGroup fa1
  have hNC : N ≤ C :=
    (fixedPosWeylGroup_le_graphFixedParabolic_singleton σ.surjective fa1).trans hP1C
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    refine RingHom.ext fun c => ?_
    have hc : c ^ ((2 ^ 1) ^ 3) = c := by
      have : Fintype K := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    convert hc using 2
  have hU2 : IsPGroup 2 U := by
    rw [hU]
    exact isPGroup_posUnipotent σ hσ3
  have hL0 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa0) = 2 ^ 3 := by
    have h := card_orbitField_D4_orientation (ℓ := 2) Nat.prime_two (f := 1) le_rfl
      (K := K) hK (r := 1) (Or.inl rfl) (σ := σ.toRingHom)
      (fun c => by rw [pow_one]; exact hσ c) fa0
    simpa [orbit_card_fa0, pow_one] using h
  have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom fa0), s.card = 4 :=
    exists_finset_card_four (by rw [hL0]; norm_num)
  let e : C ≃* X := φ.symm
  have hUφ' : S.map φ.toMonoidHom = U.subgroupOf C := hUφ
  set Y₁ : Subgroup X := perfectCore ((P0.subgroupOf C).map e.toMonoidHom) with hY
  set X₂ : Subgroup X := (N.subgroupOf C).map e.toMonoidHom with hX2
  have hYeq : Y₁ = (perfectCore (P0.subgroupOf C)).map e.toMonoidHom := by
    rw [hY, map_perfectCore]
  have hSle : S ≤ X₂ := by
    have h : U.subgroupOf C ≤ N.subgroupOf C := Subgroup.subgroupOf_mono C hUleN
    have h' : (S.map φ.toMonoidHom).map φ.symm.toMonoidHom ≤
        (N.subgroupOf C).map e.toMonoidHom := by
      have hmap := Subgroup.map_mono (f := e.toMonoidHom) h
      rw [← hUφ'] at hmap
      exact hmap
    rw [hX2]
    rwa [map_symm_map] at h'
  have hX2card : Nat.card X₂ = 3 * Nat.card S := by
    have hNsub : Nat.card ↥(N.subgroupOf C) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv
    have hUsub : Nat.card ↥(U.subgroupOf C) = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv
    have hmapN : Nat.card X₂ = Nat.card ↥(N.subgroupOf C) := by
      rw [hX2]
      exact Subgroup.card_map_of_injective (K := N.subgroupOf C) e.injective
    have hmapU : Nat.card ↥(U.subgroupOf C) = Nat.card ↥S := by
      rw [← hUφ']
      exact Subgroup.card_map_of_injective (K := S) (f := φ.toMonoidHom) φ.injective
    rw [hmapN, hNsub, card_fixedPosWeylGroup_fa1 σ hK hσ, ← hUsub, hmapU]
  have hgen : Y₁ ⊔ X₂ = ⊤ := by
    have h := perfectCore_P0_sup_eq_top σ hK hσ
    rw [hYeq, hX2, ← Subgroup.map_sup, h, Subgroup.map_top_of_surjective _ e.surjective]
  have hB2 := fixedPosWeylGroup_fa1_subgroupOf_eq σ hK hσ
  have hpc : ⁅Y₁, Y₁⁆ = Y₁ := by
    rw [hY]
    exact perfectCore_perfect _
  have hL2 : IsL2 (Bar2 Y₁) 3 := by
    obtain ⟨g, hg, hk⟩ := exists_levi_hom_fixed (t := TwistTag.D4) σ fa0 hU2 hL4
    obtain ⟨g', hg', hk'⟩ := exists_hom_perfectCore_map (e := e) ⟨g, hg, hk⟩
    exact CFSG.Quasithin.RonanF918.lieModel_of_isPSL
      (sl2_quotient hL0 (by norm_num) g' hg' hk').1
  refine ⟨Y₁, X₂, hpc, hL2, hSle, hX2card, hgen, ?_⟩
  intro α hα
  set α' : MulAut C := e.trans (α.trans e.symm) with hα'
  have hcomp : α'.toMonoidHom.comp φ.toMonoidHom = φ.toMonoidHom.comp α.toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    change α' (φ x) = φ (α x)
    rw [hα']
    simp only [e, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hα'U : (U.subgroupOf C).map α'.toMonoidHom = U.subgroupOf C := by
    rw [← hUφ', Subgroup.map_map, hcomp, ← Subgroup.map_map, hα, hUφ']
  obtain ⟨-, hcov, -, -, -, hi0, hi1⟩ := triality_named_covers (f := 1) le_rfl σ hK hσ
  have hneq : (Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C)).relIndex
        ((QuasithinUnique.Vol2Native.L239.Lie.D4.P0 σ).subgroupOf C) ≠
      (Subgroup.normalizer ((U.subgroupOf C : Subgroup C) : Set C)).relIndex
        ((QuasithinUnique.Vol2Native.L239.Lie.D4.P1 σ).subgroupOf C) := by
    rw [hi0, hi1]
    norm_num
  obtain ⟨hP0fix, hP1fix⟩ := invariant_of_unequal_covers hcov hneq α' hα'U
  have hNfix : (N.subgroupOf C).map α'.toMonoidHom = N.subgroupOf C := by
    rw [hB2, Subgroup.map_sup, Subgroup.map_commutator, hP1fix, hα'U, ← hB2]
  constructor
  · rw [hY, map_perfectCore α.toMonoidHom ((P0.subgroupOf C).map e.toMonoidHom),
      map_comm_equiv e α (P0.subgroupOf C), ← hα', hP0fix]
  · rw [hX2, map_comm_equiv e α (N.subgroupOf C), ← hα', hNfix]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
