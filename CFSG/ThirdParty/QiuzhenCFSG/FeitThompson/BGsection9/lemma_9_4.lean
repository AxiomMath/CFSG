module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.corollary_9_3
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 9.4 from BG Section 9

This file contains the support package and proof of Lemma 9.4 from `docs/section9.tex`.
-/

section Section9

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section9_c94_generatorRank_at_least_three_of_elementaryAbelian_card_ge_p_cubed
    {p : ℕ} [Fact p.Prime] {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian p A] (hA : p ^ 3 ≤ Nat.card A) :
    3 ≤ generatorRank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcard_dvd : Nat.card A ∣ p ^ Group.rank A := by
    simpa using card_dvd_exponent_pow_rank' (G := A) (n := p) (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (show Monoid.exponent A ∣ p by
          simpa using IsElementaryAbelian.exponent_dvd_p p A) a)
  have hcard_le : Nat.card A ≤ p ^ Group.rank A :=
    Nat.le_of_dvd (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _) hcard_dvd
  have hpow_le : p ^ 3 ≤ p ^ Group.rank A := hA.trans hcard_le
  have hrank : 3 ≤ Group.rank A :=
    (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow_le
  simpa [generatorRank_eq_group_rank] using hrank

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c94_exists_elementaryAbelian_three_le_generatorRank_of_three_le_primeRank
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hrank : 3 ≤ primeRank p R) :
    ∃ E : Subgroup R, IsElementaryAbelian p E ∧ 3 ≤ generatorRank E := by
  classical
  obtain ⟨A, hAp, hAcomm, hAgen⟩ :=
    section9_c93_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
      (p := p) (R := R) hrank
  let Ωsub : Subgroup A := omega₁ (G := A) (p := p)
  have : Fact (IsPGroup p A) := ⟨hAp⟩
  have hΩelem : IsElementaryAbelian p Ωsub := by
    let : IsMulCommutative A := hAcomm
    simpa [Ωsub] using section9_c92_omega1_isElementaryAbelian_of_commutative (p := p) A
  have hΩcard :
      Nat.card Ωsub = Nat.card (A ⧸ frattini A) := by
    let : IsMulCommutative A := hAcomm
    simpa [Ωsub] using
      section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative (p := p) A
  have hquot_rank : 3 ≤ generatorRank (A ⧸ frattini A) :=
    hAgen.trans (generatorRank_le_generatorRank_quotient_frattini (p := p) A)
  have hpow_le_quot : p ^ 3 ≤ Nat.card (A ⧸ frattini A) := by
    let : IsElementaryAbelian p (A ⧸ frattini A) :=
      isElementaryAbelian_quotient_frattini (R := A) (p := p)
    calc
      p ^ 3 ≤ p ^ generatorRank (A ⧸ frattini A) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hquot_rank
      _ ≤ Nat.card (A ⧸ frattini A) := by
        exact section9_c92_elementaryAbelian_card_ge_pow_generatorRank
          (p := p) (A ⧸ frattini A)
  have hpow_le_Ω : p ^ 3 ≤ Nat.card Ωsub := by
    rw [hΩcard]
    exact hpow_le_quot
  have hEgen : 3 ≤ generatorRank Ωsub := by
    let : IsElementaryAbelian p Ωsub := hΩelem
    exact
      section9_c94_generatorRank_at_least_three_of_elementaryAbelian_card_ge_p_cubed
        (p := p) hpow_le_Ω
  let f : A →* R := A.subtype
  let E : Subgroup R := Ωsub.map f
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext hxy
  have hEelem : IsElementaryAbelian p E := by
    let : IsElementaryAbelian p Ωsub := hΩelem
    simpa [E, f] using section9_c92_isElementaryAbelian_map_of_injective (p := p) (A := Ωsub) f
  have hEgen' : 3 ≤ generatorRank E := by
    have hgen_eq : generatorRank E = generatorRank Ωsub := by
      simpa [E, f] using section9_c92_generatorRank_map_injective_eq (A := Ωsub) f hf_inj
    simpa [hgen_eq] using hEgen
  exact ⟨E, hEelem, hEgen'⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c94_exists_maximal_elementaryAbelianSubgroup_containing
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R] {E : Subgroup R}
    (hEelem : IsElementaryAbelian p E) :
    ∃ M : Subgroup R, E ≤ M ∧ M ∈ maximalElementaryAbelianSubgroups p R := by
  classical
  let s : Set (Subgroup R) := {A | E ≤ A ∧ IsElementaryAbelian p A}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := ⟨E, le_rfl, hEelem⟩
  obtain ⟨M, hMmax⟩ := hsfin.exists_maximal hsne
  refine ⟨M, hMmax.1.1, ?_⟩
  refine ⟨hMmax.1.2, ?_⟩
  intro B hMB hBelem
  exact le_antisymm hMB (hMmax.2 ⟨hMmax.1.1.trans hMB, hBelem⟩ hMB)

omit [IsMinCE G] in
public theorem CFSG.section9_c94_primeRank_at_least_three_of_generatorRank_subgroup
    {q : ℕ} [Fact q.Prime] {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 3 ≤ generatorRank A) :
    3 ≤ primeRank q K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' := by
    exact hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  rw [primeRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
    exact hnB.trans <|
      (section9_c92_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
  · exact ⟨A', hA'p, hA'comm, by simpa [hgen_eq] using hAgen⟩

omit [IsMinCE G] in
private theorem CFSG.section9_c94_groupRank_at_least_three_of_generatorRank_subgroup
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A)
    (hAgen : 3 ≤ generatorRank A) :
    3 ≤ groupRank K := by
  let : Fact q.Prime := ⟨hq⟩
  have hqrankK : 3 ≤ primeRank q K :=
    section9_c94_primeRank_at_least_three_of_generatorRank_subgroup
      (q := q) hAK hAp hAcomm hAgen
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section9_c92_primeRank_le_natCard (p := r) K)
  · exact ⟨q, hq, hqrankK⟩

/-- Lemma 9.4. -/
public theorem CFSG.lemma_9_4
    {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hFittingRank : 3 ≤ primeRank p (fittingSubgroup M)) :
    ∀ A : Subgroup G,
      IsPGroup p A → IsMulCommutative A → 3 ≤ generatorRank A →
        A ∈ section9UniqueSubgroups G := by
  classical
  intro B hBp hBcomm hBgen
  have finish :
      ∀ S : Subgroup G, IsPGroup p S → IsMulCommutative S →
        3 ≤ generatorRank S → S ∈ section9UniqueSubgroups G →
          B ∈ section9UniqueSubgroups G := by
    intro S hSp hScomm hSgen hSunique
    have hBnoncyclic : ¬ IsCyclic B := by
      intro hBcyc
      have hle : generatorRank B ≤ 1 := generatorRank_le_one_of_isCyclic (G := B) hBcyc
      omega
    have hB_le_cent : B ≤ Subgroup.centralizer (B : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := B)).2 hBcomm
    have hcentralizerRank : 3 ≤ primeRank p (Subgroup.centralizer (B : Set G)) :=
      section9_c94_primeRank_at_least_three_of_generatorRank_subgroup
        (q := p) hB_le_cent hBp hBcomm hBgen
    exact
      corollary_9_3 (p := p) (A := S) (B := B)
        hSp hScomm hBp hBnoncyclic hSunique hSgen hcentralizerRank
  let F : Subgroup M := fittingSubgroup M
  let FG : Subgroup G := section8FittingSubgroup M
  obtain ⟨E, hEelem, hEgen⟩ :=
    section9_c94_exists_elementaryAbelian_three_le_generatorRank_of_three_le_primeRank
      (p := p) (R := F) (by simpa [F] using hFittingRank)
  have hFmap : F.map M.subtype = FG := rfl
  let eF : F ≃* FG := by
    exact
      (Subgroup.equivMapOfInjective (f := M.subtype) F M.subtype_injective).trans
        (MulEquiv.subgroupCongr hFmap)
  let E₀ : Subgroup FG := E.map eF.toMonoidHom
  have hE₀elem : IsElementaryAbelian p E₀ := by
    let : IsElementaryAbelian p E := hEelem
    simpa [E₀] using
      section9_c92_isElementaryAbelian_map_of_injective (p := p) (A := E) eF.toMonoidHom
  have hE₀gen : 3 ≤ generatorRank E₀ := by
    have hgen_eq : generatorRank E₀ = generatorRank E := by
      simpa [E₀] using
        section9_c92_generatorRank_map_injective_eq
          (A := E) eF.toMonoidHom eF.injective
    simpa [hgen_eq] using hEgen
  obtain ⟨A₀, hE₀_le_A₀, hA₀max⟩ :=
    section9_c94_exists_maximal_elementaryAbelianSubgroup_containing
      (p := p) (R := FG) (E := E₀) hE₀elem
  have hA₀elem : IsElementaryAbelian p A₀ := hA₀max.1
  have hE₀card_ge : p ^ 3 ≤ Nat.card E₀ := by
    let : IsElementaryAbelian p E₀ := hE₀elem
    calc
      p ^ 3 ≤ p ^ generatorRank E₀ := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hE₀gen
      _ ≤ Nat.card E₀ := by
        exact section9_c92_elementaryAbelian_card_ge_pow_generatorRank (p := p) E₀
  have hA₀card_ge : p ^ 3 ≤ Nat.card A₀ :=
    hE₀card_ge.trans (Subgroup.card_le_of_le hE₀_le_A₀)
  have hA₀rank : 3 ≤ generatorRank A₀ := by
    let : IsElementaryAbelian p A₀ := hA₀elem
    exact
      section9_c94_generatorRank_at_least_three_of_elementaryAbelian_card_ge_p_cubed
        (p := p) hA₀card_ge
  have hE₀nontrivial : Nontrivial E₀ := by
    by_contra hnt
    let : Subsingleton E₀ := not_nontrivial_iff_subsingleton.mp hnt
    have hcyc : IsCyclic E₀ := isCyclic_of_subsingleton (α := E₀)
    have hle : generatorRank E₀ ≤ 1 := generatorRank_le_one_of_isCyclic (G := E₀) hcyc
    omega
  have hpF : ⟨p, Fact.out⟩ ∈ subgroupPrimeSet FG := by
    let : IsElementaryAbelian p E₀ := hE₀elem
    have hdiv : p ∣ Nat.card FG :=
      section9_c93_prime_dvd_card_of_nontrivial_pSubgroup
        (G := FG) (p := p) (B := E₀)
        (IsElementaryAbelian.isPGroup p E₀) hE₀nontrivial
    dsimp [FG, subgroupPrimeSet]
    exact hdiv
  have hM8 : M ∈ section8MaximalSubgroups G := section8_maximal_of_section9_maximal hM
  by_cases hFGp : IsPGroup p FG
  · have hF_p : IsPGroup p F := by
      exact hFGp.of_equiv eF.symm
    obtain ⟨P, hF_le_P⟩ := IsPGroup.exists_le_sylow (G := M) (p := p) hF_p
    have h8 :=
      theorem_8_1 (G := G) (p := p) (M := M) hM8
        (by simpa [FG] using hpF) (A₀ := A₀) hA₀max hA₀rank P
    rcases h8.2 (by simpa [FG] using hFGp) with ⟨_hPglobal, hscn_unique⟩
    obtain ⟨X, hXp, hXcomm, hXgen⟩ :=
      section9_c93_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
        (p := p) (R := F) (by simpa [F] using hFittingRank)
    let XM : Subgroup M := X.map F.subtype
    have hXM_le_P : XM ≤ (P : Subgroup M) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact hF_le_P y.2
    have hXMp : IsPGroup p XM := by
      simpa [XM] using IsPGroup.map (p := p) (H := X) hXp F.subtype
    have hXMcomm : IsMulCommutative XM := by
      let : IsMulCommutative X := hXcomm
      simpa [XM] using (Subgroup.map_isMulCommutative (f := F.subtype) (H := X))
    have hXMgen : 3 ≤ generatorRank XM := by
      have hgen_eq : generatorRank XM = generatorRank X := by
        simpa [XM] using
          section9_c92_generatorRank_map_injective_eq
            (A := X) F.subtype F.subtype_injective
      simpa [hgen_eq] using hXgen
    have hPrank : 3 ≤ groupRank (P : Subgroup M) :=
      section9_c94_groupRank_at_least_three_of_generatorRank_subgroup
        (G := M) (q := p) (Fact.out : Nat.Prime p)
        (A := XM) (K := (P : Subgroup M)) hXM_le_P hXMp hXMcomm hXMgen
    have hBnontrivial : Nontrivial B := by
      by_contra hnt
      let : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
      have hcyc : IsCyclic B := isCyclic_of_subsingleton (α := B)
      have hle : generatorRank B ≤ 1 := generatorRank_le_one_of_isCyclic (G := B) hcyc
      omega
    have hpG : p ∣ Nat.card G :=
      section9_c93_prime_dvd_card_of_nontrivial_pSubgroup
        (G := G) (p := p) (B := B) hBp hBnontrivial
    have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
    obtain ⟨S, hSscn⟩ :=
      lemma_5_1_a (p := p) hpodd
        (R := ↥(P : Subgroup M)) P.isPGroup' hPrank
    let SG : Subgroup G := section8SylowSubgroupInAmbient M P S
    have hSGunique : SG ∈ section9UniqueSubgroups G :=
      section9_unique_of_section8_unique <| by
        simpa [SG] using (hscn_unique S hSscn).2
    have hScomm : IsMulCommutative S :=
      (scnSubgroup_normal_commutative
        (p := p) (R := ↥(P : Subgroup M)) P.isPGroup' hSscn).2
    have hSgen : 3 ≤ generatorRank S :=
      scnSubgroup_generatorRank_at_least_three
        (p := p) hpodd (R := ↥(P : Subgroup M)) P.isPGroup' hSscn
    have hSGp : IsPGroup p SG := by
      let SM : Subgroup M := S.map (P : Subgroup M).subtype
      have hSG_eq : SM.map M.subtype = SG := rfl
      have hSMp : IsPGroup p (S.map (P : Subgroup M).subtype) :=
        IsPGroup.map (p := p) (H := S) (P.isPGroup'.to_subgroup S)
          (P : Subgroup M).subtype
      rw [← hSG_eq]
      exact IsPGroup.map (p := p) (H := SM) hSMp M.subtype
    have hSGcomm : IsMulCommutative SG := by
      let SM : Subgroup M := S.map (P : Subgroup M).subtype
      have hSG_eq : SM.map M.subtype = SG := rfl
      have hSMcomm : IsMulCommutative SM := by
        let : IsMulCommutative S := hScomm
        simpa [SM] using
          (Subgroup.map_isMulCommutative (f := (P : Subgroup M).subtype) (H := S))
      let : IsMulCommutative SM := hSMcomm
      rw [← hSG_eq]
      exact Subgroup.map_isMulCommutative (f := M.subtype) (H := SM)
    have hSGgen : 3 ≤ generatorRank SG := by
      let SM : Subgroup M := S.map (P : Subgroup M).subtype
      have hSG_eq : SM.map M.subtype = SG := rfl
      have hSMgen_eq : generatorRank SM = generatorRank S := by
        simpa [SM] using
          section9_c92_generatorRank_map_injective_eq
            (A := S) (P : Subgroup M).subtype (P : Subgroup M).subtype_injective
      have hSGgen_eq : generatorRank SG = generatorRank SM := by
        rw [← hSG_eq]
        exact
          section9_c92_generatorRank_map_injective_eq
            (A := SM) M.subtype M.subtype_injective
      simpa [hSGgen_eq, hSMgen_eq] using hSgen
    exact finish SG hSGp hSGcomm hSGgen hSGunique
  · let P : Sylow p M := default
    have h8 :=
      theorem_8_1 (G := G) (p := p) (M := M) hM8
        (by simpa [FG] using hpF) (A₀ := A₀) hA₀max hA₀rank P
    let C : Subgroup G := section8CentralizerInFitting M A₀
    let A₀G : Subgroup G := A₀.map FG.subtype
    have hCunique : C ∈ section9UniqueSubgroups G :=
      section9_unique_of_section8_unique <| by
        simpa [C, FG] using h8.1 (by simpa [FG] using hFGp)
    have hA₀Gelem : IsElementaryAbelian p A₀G := by
      let : IsElementaryAbelian p A₀ := hA₀elem
      simpa [A₀G] using
        section9_c92_isElementaryAbelian_map_of_injective (p := p) (A := A₀) FG.subtype
    have hA₀Gp : IsPGroup p A₀G := by
      let : IsElementaryAbelian p A₀G := hA₀Gelem
      exact IsElementaryAbelian.isPGroup p A₀G
    have hA₀Gcomm : IsMulCommutative A₀G := by
      let : IsElementaryAbelian p A₀G := hA₀Gelem
      infer_instance
    have hA₀Ggen : 3 ≤ generatorRank A₀G := by
      have hgen_eq : generatorRank A₀G = generatorRank A₀ := by
        simpa [A₀G] using
          section9_c92_generatorRank_map_injective_eq
            (A := A₀) FG.subtype FG.subtype_injective
      simpa [hgen_eq] using hA₀rank
    have hA₀Grank : 2 ≤ groupRank A₀G :=
      section9_c93_groupRank_at_least_two_of_generatorRank_subgroup
        (G := G) (q := p) (Fact.out : Nat.Prime p)
        (A := A₀G) (K := A₀G) le_rfl hA₀Gp hA₀Gcomm
        (le_trans (by decide : 2 ≤ 3) hA₀Ggen)
    have hA₀G_le_centC : A₀G ≤ Subgroup.centralizer (C : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      have hy' : y ∈ section8CentralizerInFitting M A₀ := by
        simpa [C] using hy
      change y ∈ (Subgroup.centralizer (A₀ : Set FG)).map FG.subtype at hy'
      rcases Subgroup.mem_map.mp hy' with ⟨c, hc, hcy⟩
      have hcomm := (Subgroup.mem_centralizer_iff.mp hc) a ha
      exact by
        subst y
        simpa using congrArg Subtype.val hcomm.symm
    have hA₀Gunique : A₀G ∈ section9UniqueSubgroups G :=
      corollary_9_2 (L := C) (K := A₀G)
        hCunique hA₀G_le_centC hA₀Grank
    exact finish A₀G hA₀Gp hA₀Gcomm hA₀Ggen hA₀Gunique

end Section9
