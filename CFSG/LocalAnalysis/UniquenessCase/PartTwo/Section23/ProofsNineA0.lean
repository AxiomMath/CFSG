module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ug
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.GroupTheory.CriticalPerfect
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.GroupTheory.Frattini.NormalConjugation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem not_le_rep_ker {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (d : S23_9_A0Data D Ch c) {P : Subgroup (Bar2 D.M)} (hP : ⁅P, P⁆ = P)
    (hcomm : ⁅P, d.E⁆ ≠ ⊥) : ¬ P ≤ d.rep.ker := by
  intro hker
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  let φ : Bar2 D.M →* MulAut ↥d.E := MulAut.conjNormal (H := d.E)
  have hrep : ∀ (z : Bar2 D.M) (w : ↥d.E),
      d.rep z (Additive.ofMul (QuotientGroup.mk' (frattini ↥d.E) w)) =
        Additive.ofMul (QuotientGroup.mk' (frattini ↥d.E) (φ z w)) :=
    fun z w => CFSG.RankThree.PartOne.FixedRank36.frattiniRep_apply φ z w
  have hle : P.map φ ≤ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
      (frattini ↥d.E)).ker := by
    rintro _ ⟨x, hx, rfl⟩
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro e
    have hx1 : d.rep x = 1 := MonoidHom.mem_ker.mp (hker hx)
    have h := congrArg (fun f : Module.End (ZMod d.q)
        (Additive (↥d.E ⧸ frattini ↥d.E)) =>
        f (Additive.ofMul (QuotientGroup.mk' (frattini ↥d.E) e))) hx1
    simp only [Module.End.one_apply] at h
    rw [hrep] at h
    exact congrArg Additive.toMul h
  have hImgP : IsPGroup d.q ↥(P.map φ) :=
    ((CFSG.GroupTheory.frattini_automorphism_kernel d.hEp).2).to_le hle
  have hImgPerf : Group.IsPerfect ↥(P.map φ) :=
    isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hP])
  have hmapbot : P.map φ = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(P.map φ) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    haveI : Group.IsPerfect ↥(P.map φ) := hImgPerf
    have hsolv : Group.IsSolvable ↥(P.map φ) :=
      @IsNilpotent.to_isSolvable _ _ hImgP.isNilpotent
    exact Group.IsPerfect.not_isSolvable ↥(P.map φ) hsolv
  apply hcomm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : φ x = 1 := by
    have hmem := Subgroup.mem_map_of_mem φ hx
    rw [hmapbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h2 := congrArg (fun f : MulAut ↥d.E => (f ⟨y, hy⟩ : ↥d.E)) h1
  simp only [MulAut.one_apply] at h2
  have h3 : x * y * x⁻¹ = y := by
    have h5 := congrArg Subtype.val h2
    dsimp only [φ] at h5
    simpa [MulAut.conjNormal_apply] using h5
  have h4 : x * y = y * x := by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h3]
  exact h4.symm

private theorem exists_odd_prime_pCore_commutator {D : Data G}
    {P : Subgroup (Bar2 D.M)} (hP : ⁅P, CFSG.fittingSubgroup (Bar2 D.M)⁆ ≠ ⊥) :
    ∃ q ∈ (Nat.card (Bar2 D.M)).primeFactors, q ≠ 2 ∧
      ⁅P, CFSG.pCore q (Bar2 D.M)⁆ ≠ ⊥ := by
  obtain ⟨q, hqmem, hqcomm⟩ : ∃ q ∈ (Nat.card (Bar2 D.M)).primeFactors,
      ⁅P, CFSG.pCore q (Bar2 D.M)⁆ ≠ ⊥ := by
    by_contra h
    push_neg at h
    exact hP (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores fun p =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h p.1.1 p.1.2)))
  refine ⟨q, hqmem, ?_, hqcomm⟩
  rintro rfl
  refine hqcomm ?_
  rw [uc22p20c_pCore_quotient_pCore]
  simp

private theorem sup_pCoreOf_eq_barPreimage {D : Data G} {E : Subgroup (Bar2 D.M)} {q : ℕ}
    [Fact q.Prime] {Q : Subgroup G}
    (hQsyl : CFSG.ABGLocalTools.IsSylowOf q Q (barPreimage D.M E))
    (hQbar : barImage D.M Q = E) :
    CFSG.Open.pCoreOf 2 D.M ⊔ Q = barPreimage D.M E := by
  refine le_antisymm (sup_le (pCoreOf_le_barPreimage D.M E) hQsyl.le) ?_
  intro y hy
  obtain ⟨hyM, hyE⟩ := uc22p21c_mem_barPreimage.1 hy
  rw [← hQbar] at hyE
  obtain ⟨m, hmQ, hm⟩ := uc22p21c_mem_barImage.1 hyE
  have hzM : (m : G)⁻¹ * y ∈ D.M := D.M.mul_mem (D.M.inv_mem m.2) hyM
  have hz : (m : G)⁻¹ * y ∈ CFSG.Open.pCoreOf 2 D.M := by
    refine Subgroup.mem_map.mpr ⟨⟨_, hzM⟩, ?_, rfl⟩
    refine (QuotientGroup.eq_one_iff _).1 ?_
    change uc22p21cPi D.M (m⁻¹ * ⟨y, hyM⟩) = 1
    rw [map_mul, map_inv, hm, inv_mul_cancel]
  have hy' : y ∈ Q ⊔ CFSG.Open.pCoreOf 2 D.M := by
    rw [show y = (m : G) * ((m : G)⁻¹ * y) by group]
    exact Subgroup.mul_mem_sup hmQ hz
  rwa [sup_comm] at hy'

private theorem exists_critical_A0_subgroup {D : Data G} {Kbar : Subgroup (Bar2 D.M)} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hKbar : ⁅Kbar, Kbar⁆ = Kbar)
    (hcomm : ⁅Kbar, CFSG.pCore q (Bar2 D.M)⁆ ≠ ⊥) :
    ∃ E : Subgroup (Bar2 D.M), E.Normal ∧ IsPGroup q ↥E ∧ E ≠ ⊥ ∧
      (∀ x ∈ E, x ^ q = 1) ∧ ⁅⁅E, E⁆, E⁆ = ⊥ ∧
      IsElementaryAbelian q (↥E ⧸ frattini ↥E) ∧ ¬ IsCyclic ↥E ∧ ⁅Kbar, E⁆ ≠ ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  let Q0 : Subgroup (Bar2 D.M) := CFSG.pCore q (Bar2 D.M)
  have hQ0n : Q0.Normal := CFSG.pCore_normal
  haveI : Q0.Normal := hQ0n
  have hQ0p : IsPGroup q ↥Q0 := CFSG.pCore_isPGroup
  have hQ0ne : Q0 ≠ ⊥ := by
    intro hbot
    refine hcomm ?_
    rw [show CFSG.pCore q (Bar2 D.M) = ⊥ from hbot]
    simp
  obtain ⟨D0, hD0n, hD0p, hD0ne, hD0exp, hD0cl, hD0fix⟩ :=
    CFSG.GroupTheory.exists_critical_map_subtype (q := q) (Q := Q0) hq2 hQ0p hQ0ne
  let E : Subgroup (Bar2 D.M) := D0.map Q0.subtype
  haveI : E.Normal := hD0n
  have hEp : IsPGroup q ↥E := hD0p
  haveI : Fact (IsPGroup q ↥E) := ⟨hEp⟩
  obtain ⟨hEnc, hcommE⟩ := CFSG.GroupTheory.critical_map_noncyclic_and_commutator_ne_bot
    (q := q) (P := Kbar) (Q := Q0) (D := D0) hKbar hD0fix hcomm
  exact ⟨E, hD0n, hEp, hD0ne, hD0exp, hD0cl,
    CFSG.isElementaryAbelian_quotient_frattini, hEnc, hcommE⟩

theorem s23_9_A0_of (D : Data G) (Ch : Choice2011 G) : S23_9_A0 D Ch := by
  intro h1930 c h3 _hK _hKne hcomm
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  let Kbar : Subgroup (Bar2 D.M) := barImage D.M K
  have hcomm' : ⁅Kbar, CFSG.fittingSubgroup (Bar2 D.M)⁆ ≠ ⊥ := hcomm
  have hKM : K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hKperf : ⁅K, K⁆ = K := uc22p21c_Hinf_perfect (D.M ⊓ c.L)
  have hKbarperf : ⁅Kbar, Kbar⁆ = Kbar := by
    dsimp only [Kbar, K]
    unfold barImage
    rw [← Subgroup.map_commutator, CFSG.GroupTheory.commutator_subgroupOf_eq hKM hKM, hKperf]
  obtain ⟨q, hqmem, hq2, hqcomm⟩ := exists_odd_prime_pCore_commutator hcomm'
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E, hEnorm, hEp, hEne, hEexp, hEclass, hEel, hEnc, hcommE⟩ :=
    exists_critical_A0_subgroup hq hq2 hKbarperf hqcomm
  haveI : E.Normal := hEnorm
  haveI : Fact (IsPGroup q ↥E) := ⟨hEp⟩
  obtain ⟨Q, hQsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf q (barPreimage D.M E)
  have hQM : Q ≤ D.M := hQsyl.le.trans (uc22p21c_barPreimage_le D.M E)
  obtain ⟨hQbar, hQinf⟩ := uc22p22u_sylow_barPreimage hq hq2 hEp hQsyl
  have hprops := uc22p22u_lift_props (r := q) hQbar hQinf hQM
  have hQp : IsPGroup q ↥Q := hQsyl.isPGroup
  have hQexp : ∀ x ∈ Q, x ^ q = 1 := hprops.1 hEexp
  have hQclass : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := hprops.2.1 hEclass
  have hQnc : ¬ IsCyclic ↥Q := hprops.2.2 hEnc
  have hPre : D.M ≤ Subgroup.normalizer ((barPreimage D.M E : Subgroup G) : Set G) :=
    uc22p22u_barPreimage_normalizes (M := D.M) (D := E)
  have hsup := sup_pCoreOf_eq_barPreimage hQsyl hQbar
  have hQnorm : D.M ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 D.M ⊔ Q : Subgroup G) : Set G) := by
    rw [hsup]
    exact hPre
  let d : S23_9_A0Data D Ch c :=
    { q := q
      hq := hq
      hq2 := hq2
      Q := Q
      hQM := hQM
      hQp := hQp
      hQnc := hQnc
      hQexp := hQexp
      hQclass := hQclass
      hQnorm := hQnorm
      E := E
      hEnorm := hEnorm
      hEp := hEp
      hEne := hEne
      hEnc := hEnc
      hEexp := hEexp
      hEclass := hEclass
      hEel := hEel
      hEQ := hQbar }
  exact ⟨d, not_le_rep_ker d hKbarperf hcommE⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
