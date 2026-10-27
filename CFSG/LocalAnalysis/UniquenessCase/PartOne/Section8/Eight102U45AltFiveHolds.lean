module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45AltFiveModel
import CFSG.RankThree.PartTwo.KFacts.KS222U5
import CFSG.RankThree.PartTwo.KFacts.KS222U4Even
import CFSG.LocalAnalysis.UniquenessCase.UC6K332Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRankOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterCyclic
import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Out
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.Adapters.LieModelTorusRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
  (isCyclic_outer_of_lieModel_PSU4)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5 (bar2EquivOfPCore)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Excl (card_isAlt_five)
open CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag (eq_top_of_isPerfect_five)
open CFSG.RankThree.PartTwo.Sec21
  (ks222U4Even ks222U5 isSimpleGroup_projSL_two card_projSL_two)
open CFSG.RankThree.PartTwo.Sec21.Item21Early2Proof (center_projSU_four_eq_bot)
open CFSG.PGLModel (projSL projSU)

private noncomputable abbrev JOf {X : Type} [Group X] (A : Subgroup X) : Subgroup X :=
  F08.DerInf8 (⊤ ⊓ Subgroup.centralizer (A : Set X))

private theorem projSL_two_card_eq_sixty {m : ℕ} (hm : 1 ≤ m)
    (h : 2 ^ m * ((2 ^ m) ^ 2 - 1) = 60) : m = 2 := by
  have hdvd : 2 ^ m ∣ 60 := ⟨(2 ^ m) ^ 2 - 1, h.symm⟩
  have hle : 2 ^ m ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have hm6 : m < 6 := by
    by_contra hlt
    push Not at hlt
    have hpow : 2 ^ 6 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hlt
    norm_num at hpow
    omega
  interval_cases m <;> norm_num at h
  rfl

private theorem pCore_two_eq_bot_of_isSimpleGroup_of_isAlt_five {H : Type} [Group H]
    [IsSimpleGroup H] (h : IsAlt (H ⧸ CFSG.pCore 2 H) 5) : CFSG.pCore 2 H = ⊥ := by
  have hnt : ¬ Subsingleton (H ⧸ CFSG.pCore 2 H) := by
    intro hs
    have h1 : Nat.card (H ⧸ CFSG.pCore 2 H) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨1⟩⟩
    have h60 := card_isAlt_five h
    omega
  haveI : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 H) with hbot | htop
  · exact hbot
  · exact absurd (by rw [htop]; exact QuotientGroup.subsingleton_quotient_top) hnt

private theorem unique_five_of_isCyclic {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hcyc : IsCyclic ↥H) {U₁ U₂ : Subgroup G} (h1 : U₁ ≤ H) (h2 : U₂ ≤ H)
    (hc1 : Nat.card U₁ = 5) (hc2 : Nat.card U₂ = 5) : U₁ = U₂ := by
  have hsub : U₁.subgroupOf H = U₂.subgroupOf H := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h1).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h2).toEquiv, hc1, hc2]
  rw [← Subgroup.map_subgroupOf_eq_of_le h1, ← Subgroup.map_subgroupOf_eq_of_le h2, hsub]

private theorem center_eq_bot_of_isU4 {X : Type} [Group X] {n : ℕ} (h : IsU4 X n) :
    Subgroup.center X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := UCK.K332Route.nonempty_projSU_of_lieModel h
  have hn1 : 1 ≤ n := h.admissible.2.1
  have hZ : Subgroup.center (projSU 4 2 n) = ⊥ := center_projSU_four_eq_bot hn1
  have hmap := Subgroup.map_center_eq e
  rw [hZ] at hmap
  refine Subgroup.map_injective (f := (e : X →* projSU 4 2 n)) e.injective ?_
  rw [hmap, Subgroup.map_bot]

private theorem conj_injective_of_isU4 {X : Type} [Group X] {n : ℕ} (h : IsU4 X n) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  have hcenter := center_eq_bot_of_isU4 h
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxc : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hxy : x * y * x⁻¹ = y := by
      have h := congrArg (fun f : MulAut X => f y) hx
      simpa [MulAut.conj_apply] using h
    have hxy' : x * y = y * x := by
      have := congrArg (fun z : X => z * x) hxy
      simpa [mul_assoc] using this
    exact hxy'.symm
  rw [hcenter] at hxc
  exact hxc

private theorem false_of_isU5_of_isAlt_five {X : Type} [Group X] [Finite X]
    {A : Subgroup X} (hU5 : IsU5 X 2) (hA : Nat.card A = 3)
    (hAlt : IsAlt (Bar2 (JOf A)) 5) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e5⟩ := UCK.K332Route.nonempty_projSU_of_lieModel hU5
  have hJ := ks222U5 X ⊤ A ⟨Subgroup.topEquiv.trans e5⟩ le_top hA
  change Nonempty (JOf A ≃* projSL 2 (GaloisField 2 4)) ∨
    StatedClassicalModel (JOf A) .PSU 3 2 2 at hJ
  have hcardJ : Nat.card ↥(JOf A) = 60 := by
    rcases hJ with h1 | hSt
    · obtain ⟨e1⟩ := h1
      have hpc : CFSG.pCore 2 ↥(JOf A) = ⊥ := by
        haveI : IsSimpleGroup (projSL 2 (GaloisField 2 4)) :=
          isSimpleGroup_projSL_two (m := 4) (by norm_num)
        haveI : IsSimpleGroup ↥(JOf A) := e1.isSimpleGroup
        exact pCore_two_eq_bot_of_isSimpleGroup_of_isAlt_five (H := ↥(JOf A)) hAlt
      calc Nat.card ↥(JOf A) = Nat.card (Bar2 (JOf A)) :=
            (Nat.card_congr (bar2EquivOfPCore hpc).toEquiv).symm
        _ = 60 := card_isAlt_five hAlt
    · have hpc : CFSG.pCore 2 ↥(JOf A) = ⊥ := by
        have hLie : CFSG.Blueprint.LieModel ↥(JOf A) .PSU 3 2 2 :=
          Or.inl ⟨by decide, hSt⟩
        haveI : IsSimpleGroup ↥(JOf A) :=
          UC22.uc22p22r_lieModel_isSimple_classical (t := .PSU)
            (Or.inr (Or.inl rfl)) hLie
        exact pCore_two_eq_bot_of_isSimpleGroup_of_isAlt_five (H := ↥(JOf A)) hAlt
      calc Nat.card ↥(JOf A) = Nat.card (Bar2 (JOf A)) :=
            (Nat.card_congr (bar2EquivOfPCore hpc).toEquiv).symm
        _ = 60 := card_isAlt_five hAlt
  rcases hJ with h1 | hSt
  · obtain ⟨e1⟩ := h1
    have hcardSL : Nat.card (projSL 2 (GaloisField 2 4)) = 4080 := by
      rw [card_projSL_two 4 (by norm_num)]
      norm_num
    have hEq : (60 : ℕ) = 4080 := by
      rw [← hcardJ, Nat.card_congr e1.toEquiv, hcardSL]
    norm_num at hEq
  · have hcardSt : Nat.card ↥(JOf A) = 62400 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four hSt
    have hEq : (60 : ℕ) = 62400 := by rw [← hcardJ, hcardSt]
    norm_num at hEq

private theorem u4_shape_projSL_of_isAlt_five {X : Type} [Group X] [Finite X] {n : ℕ}
    {A : Subgroup X} (hU4 : IsU4 X n) (hEven : Even n)
    (hAlt : IsAlt (Bar2 (JOf A)) 5)
    (e1 : ↥(JOf A) ≃* projSL 2 (GaloisField 2 n)) :
    IsU4 X 2 ∧ n = 2 ∧ CFSG.pCore 2 ↥(JOf A) = ⊥ ∧
      Nonempty (↥(JOf A) ≃* projSL 2 (GaloisField 2 2)) := by
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hEven
    have hn1 : 1 ≤ n := hU4.admissible.2.1
    omega
  have hpc : CFSG.pCore 2 ↥(JOf A) = ⊥ := by
    haveI : IsSimpleGroup (projSL 2 (GaloisField 2 n)) :=
      isSimpleGroup_projSL_two (m := n) hn2
    haveI : IsSimpleGroup ↥(JOf A) := e1.isSimpleGroup
    exact pCore_two_eq_bot_of_isSimpleGroup_of_isAlt_five (H := ↥(JOf A)) hAlt
  have hcardJ : Nat.card ↥(JOf A) = 60 := by
    calc Nat.card ↥(JOf A) = Nat.card (Bar2 (JOf A)) :=
          (Nat.card_congr (bar2EquivOfPCore hpc).toEquiv).symm
      _ = 60 := card_isAlt_five hAlt
  have hEq : 2 ^ n * ((2 ^ n) ^ 2 - 1) = 60 := by
    calc 2 ^ n * ((2 ^ n) ^ 2 - 1) =
          Nat.card (projSL 2 (GaloisField 2 n)) := (card_projSL_two n (by omega)).symm
      _ = Nat.card ↥(JOf A) := (Nat.card_congr e1.toEquiv).symm
      _ = 60 := hcardJ
  have hn_eq : n = 2 := projSL_two_card_eq_sixty (by omega) hEq
  subst hn_eq
  exact ⟨hU4, rfl, hpc, ⟨e1⟩⟩

private theorem false_of_u4_shape_projSL_sq {X : Type} [Group X] [Finite X] {n : ℕ}
    {A : Subgroup X} (hU4 : IsU4 X n) (hEven : Even n)
    (hAlt : IsAlt (Bar2 (JOf A)) 5)
    (e2 : ↥(JOf A) ≃* projSL 2 (GaloisField 2 (2 * n))) : False := by
  have hn1 : 1 ≤ n := hU4.admissible.2.1
  have hn2 : 2 ≤ 2 * n := by omega
  have hpc : CFSG.pCore 2 ↥(JOf A) = ⊥ := by
    haveI : IsSimpleGroup (projSL 2 (GaloisField 2 (2 * n))) :=
      isSimpleGroup_projSL_two (m := 2 * n) hn2
    haveI : IsSimpleGroup ↥(JOf A) := e2.isSimpleGroup
    exact pCore_two_eq_bot_of_isSimpleGroup_of_isAlt_five (H := ↥(JOf A)) hAlt
  have hcardJ : Nat.card ↥(JOf A) = 60 := by
    calc Nat.card ↥(JOf A) = Nat.card (Bar2 (JOf A)) :=
          (Nat.card_congr (bar2EquivOfPCore hpc).toEquiv).symm
      _ = 60 := card_isAlt_five hAlt
  have hEq : 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) = 60 := by
    calc 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) =
          Nat.card (projSL 2 (GaloisField 2 (2 * n))) :=
            (card_projSL_two (2 * n) (by omega)).symm
      _ = Nat.card ↥(JOf A) := (Nat.card_congr e2.toEquiv).symm
      _ = 60 := hcardJ
  have hm : 2 * n = 2 := projSL_two_card_eq_sixty (by omega) hEq
  obtain ⟨k, hk⟩ := hEven
  omega

private theorem u4_shape_of_isAlt_five {X : Type} [Group X] [Finite X] {n : ℕ}
    {A : Subgroup X} (hU4 : IsU4 X n) (hEven : Even n) (hA : Nat.card A = 3)
    (hAlt : IsAlt (Bar2 (JOf A)) 5) :
    IsU4 X 2 ∧ n = 2 ∧ CFSG.pCore 2 ↥(JOf A) = ⊥ ∧
      Nonempty (↥(JOf A) ≃* projSL 2 (GaloisField 2 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e4⟩ := UCK.K332Route.nonempty_projSU_of_lieModel hU4
  have hJ := ks222U4Even X ⊤ A n (by have := hU4.admissible.2.1; omega) hEven
    ⟨Subgroup.topEquiv.trans e4⟩ le_top hA
  change Nonempty (JOf A ≃* projSL 2 (GaloisField 2 n)) ∨
    Nonempty (JOf A ≃* projSL 2 (GaloisField 2 (2 * n))) at hJ
  rcases hJ with h1 | h2
  · obtain ⟨e1⟩ := h1
    exact u4_shape_projSL_of_isAlt_five hU4 hEven hAlt e1
  · obtain ⟨e2⟩ := h2
    exact absurd (false_of_u4_shape_projSL_sq hU4 hEven hAlt e2) not_false

private theorem u45_shape {X : Type} [Group X] [Finite X] {n : ℕ} {A : Subgroup X}
    (hX : IsU45 X n) (hA : Nat.card A = 3)
    (hAlt : IsAlt (Bar2 (JOf A)) 5) :
    IsU4 X 2 ∧ n = 2 ∧ CFSG.pCore 2 ↥(JOf A) = ⊥ ∧
      Nonempty (↥(JOf A) ≃* projSL 2 (GaloisField 2 2)) := by
  rcases hX with ⟨hU5, rfl⟩ | ⟨hU4, hEven⟩
  · exact absurd (false_of_isU5_of_isAlt_five hU5 hA hAlt) not_false
  · exact u4_shape_of_isAlt_five hU4 hEven hA hAlt

private theorem isL2_bar2_of_shape {X : Type} [Group X] {A : Subgroup X}
    (hpCore : CFSG.pCore 2 ↥(JOf A) = ⊥)
    (eJ : ↥(JOf A) ≃* projSL 2 (GaloisField 2 2)) :
    IsL2 (Bar2 (JOf A)) 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSL 2 2 2 := by
    unfold StatedLieAdmissible
    norm_num
  have hmodels : CFSG.Models.LieModel (projSL 2 (GaloisField 2 2)) .PSL 2 2 2 :=
    CFSG.PGLModel.lieModel_projSL (n := 2) (p := 2) (e := 2) hadm
  have hblue : CFSG.Blueprint.LieModel (projSL 2 (GaloisField 2 2)) .PSL 2 2 2 :=
    CFSG.Models.LieModel.toBlueprint (t := .PSL) (n := 2) (p := 2) (f := 2)
      (by decide) hmodels
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    ((bar2EquivOfPCore hpCore).trans eJ).symm hblue

private theorem eq_bot_of_perfect_le_altFive {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (hpCore : CFSG.pCore 2 ↥(JOf A) = ⊥) (hAlt : IsAlt (Bar2 (JOf A)) 5)
    {u : X} (huNot : u ∉ Subgroup.centralizer (JOf A : Set X))
    {P : Subgroup X} (hPJ : P ≤ JOf A) (hPperf : ⁅P, P⁆ = P)
    (hPu : P ≤ Subgroup.centralizer ({u} : Set X)) : P = ⊥ := by
  obtain ⟨eBar⟩ := hAlt
  let eJ : ↥(JOf A) ≃* alternatingGroup (Fin 5) :=
    (bar2EquivOfPCore hpCore).symm.trans eBar
  let T : Subgroup ↥(JOf A) := P.subgroupOf (JOf A)
  have hTperf : Group.IsPerfect ↥T := by
    haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPJ).symm.toMonoidHom)
      (MulEquiv.surjective _)
  by_cases hTbot : T = ⊥
  · rw [show P = T.map (JOf A).subtype from
        (Subgroup.map_subgroupOf_eq_of_le hPJ).symm, hTbot, Subgroup.map_bot]
  · have hTtop : T = ⊤ := eq_top_of_isPerfect_five eJ hTperf hTbot
    have hJP : JOf A ≤ P := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hPJ]
      change JOf A ≤ T.map (JOf A).subtype
      rw [hTtop, Subgroup.map_top, Subgroup.subtype_range]
    exfalso
    apply huNot
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hjP : j ∈ P := hJP hj
    have hcomm := Subgroup.mem_centralizer_iff.mp (hPu hjP) u (Set.mem_singleton u)
    exact hcomm.symm

private noncomputable abbrev ConjPreimage {X : Type} [Group X]
    (Y : Subgroup (MulAut X)) : Subgroup X :=
  Y.comap (MulAut.conj : X →* MulAut X)

private theorem comap_conj_perfect_le_J {X : Type} [Group X] [Finite X] {A : Subgroup X}
    (h4 : IsU4 X 2) {u : X} {Y : Subgroup (MulAut X)}
    (hYinner : Y ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner X)
    (hY : ⁅Y, Y⁆ = Y) (hYA : ∀ α ∈ Y, ∀ a ∈ A, α a = a)
    (hYu : ∀ α ∈ Y, α u = u) :
    ⁅ConjPreimage Y, ConjPreimage Y⁆ = ConjPreimage Y ∧
      ConjPreimage Y ≤ JOf A ∧
      ConjPreimage Y ≤ Subgroup.centralizer ({u} : Set X) := by
  let Y' := ConjPreimage Y
  have hYmap : Y'.map (MulAut.conj : X →* MulAut X) = Y :=
    Subgroup.map_comap_eq_self hYinner
  have hY'perf : ⁅Y', Y'⁆ = Y' := by
    apply Subgroup.map_injective (conj_injective_of_isU4 h4)
    rw [Subgroup.map_commutator, hYmap, hY]
  have hY'A : Y' ≤ Subgroup.centralizer (A : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := hYA (MulAut.conj y) hy a ha
    have h' : y * a * y⁻¹ = a := by simpa [MulAut.conj_apply] using h
    have hya : y * a = a * y := by
      have := congrArg (fun z : X => z * y) h'
      simpa [mul_assoc] using this
    exact hya.symm
  have hY'u : Y' ≤ Subgroup.centralizer ({u} : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    rw [hv]
    have h := hYu (MulAut.conj y) hy
    have h' : y * u * y⁻¹ = u := by simpa [MulAut.conj_apply] using h
    have huy : y * u = u * y := by
      have := congrArg (fun z : X => z * y) h'
      simpa [mul_assoc] using this
    exact huy.symm
  have hY'J : Y' ≤ JOf A :=
    UC22.uc22p21c_le_Hinf (K := ⊤ ⊓ Subgroup.centralizer (A : Set X))
      (le_inf le_top hY'A) hY'perf
  exact ⟨hY'perf, hY'J, hY'u⟩

private theorem eq_bot_of_isPerfect_mulAut {X : Type} [Group X] [Finite X]
    {A : Subgroup X} (h4 : IsU4 X 2) (hpCore : CFSG.pCore 2 ↥(JOf A) = ⊥)
    (hAlt : IsAlt (Bar2 (JOf A)) 5) {u : X}
    (huNot : u ∉ Subgroup.centralizer (JOf A : Set X))
    (Y : Subgroup (MulAut X)) (hY : ⁅Y, Y⁆ = Y)
    (hYA : ∀ α ∈ Y, ∀ a ∈ A, α a = a)
    (hYu : ∀ α ∈ Y, α u = u) : Y = ⊥ := by
  have hcycOut : IsCyclic (Outer X) := isCyclic_outer_of_lieModel_PSU4 h4
  have hYinner : Y ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
    calc Y = ⁅Y, Y⁆ := hY.symm
      _ ≤ ⁅(⊤ : Subgroup (MulAut X)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator (MulAut X) := (_root_.commutator_def (MulAut X)).symm
      _ ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
          CFSG.LocalAnalysis.GLTheoremA.HDesc.commutator_le_inner_of_isCyclic hcycOut
  let Y' := ConjPreimage Y
  obtain ⟨hY'perf, hY'J, hY'u⟩ :=
    comap_conj_perfect_le_J h4 hYinner hY hYA hYu
  have hYmap : Y'.map (MulAut.conj : X →* MulAut X) = Y :=
    Subgroup.map_comap_eq_self hYinner
  have hY'bot : Y' = ⊥ :=
    eq_bot_of_perfect_le_altFive hpCore hAlt huNot hY'J hY'perf hY'u
  rw [← hYmap, hY'bot, Subgroup.map_bot]

theorem kU45AltFive_holds : KU45AltFive := by
  intro X _ _ n hX A hA hAlt
  obtain ⟨h4, rfl, hpCore, ⟨eJ⟩⟩ := u45_shape hX hA hAlt
  have hL2 : IsL2 (Bar2 (JOf A)) 2 := isL2_bar2_of_shape hpCore eJ
  refine ⟨?_, ?_, ?_⟩
  · intro U₁ U₂ h1 h2 hc1 hc2
    exact unique_five_of_isCyclic
      (isCyclic_centralizer_inf_centralizer_derInf8_of_isL2 h4 (by norm_num) hA hL2)
      h1 h2 hc1 hc2
  · intro u _ _ huNot Y hY hYA hYu
    exact eq_bot_of_isPerfect_mulAut h4 hpCore hAlt huNot Y hY hYA hYu
  · exact CFSG.Blueprint.LieModel.le_pRank_psu_of_dvd h4 Nat.prime_five
      (by norm_num) (by norm_num) (Or.inr (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
