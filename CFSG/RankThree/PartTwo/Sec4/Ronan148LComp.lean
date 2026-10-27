module

public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.LocalAnalysis.GLTheoremB CFSG.RankThree.LocalRank
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (isQuasisimple_barX_iff barX_eq_iff_cov
  glaPComponent_up barX_isSubnormal_top)

open scoped commutatorElement

theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

theorem exists_ne_comm_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center Q = ⊤ :=
    (Subgroup.eq_top_iff' _).2 fun a => Subgroup.mem_center_iff.2 fun b => h b a
  have := hQ.2.toNontrivial
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (QuotientGroup.eq.2 (by rw [hc]; trivial))

theorem glaPPrimeCore_le_center {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (h3 : 3 ∣ Nat.card Q) : CFSG.Open.GLAPPrimeCore 3 Q ≤ Subgroup.center Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases normal_eq_top_or_le_center hQ (inferInstance : (CFSG.Open.GLAPPrimeCore 3 Q).Normal)
    with h | h
  · exfalso
    have hc : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 Q)) := CFSG.pPrimeCore_coprime_card
    have hc' : Nat.Coprime 3 (Nat.card Q) := by
      have h' : CFSG.pPrimeCore 3 Q = ⊤ := h
      rw [h', Subgroup.card_top] at hc
      exact hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc' h3
  · exact h

section Comp

variable {G : Type*} [Group G] [Finite G]

theorem open_isSubnormal_of_subgroupOf {X U : Subgroup G} (hUX : U ≤ X)
    (h : (U.subgroupOf X).IsSubnormal) : CFSG.Open.IsSubnormal U X :=
  (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hUX).1
    ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_top_iff_mathlib _).2 h))

theorem glaPComponent_three_self {J : Subgroup G} (hJ : CFSG.Open.IsQuasisimple ↥J)
    (h3 : 3 ∣ Nat.card J) : CFSG.Open.GLAPComponent 3 J J := by
  have hO := glaPPrimeCore_le_center hJ h3
  have hsn : CFSG.Open.IsSubnormal J J := CFSG.Open.IsSubnormal.refl J
  refine ⟨le_rfl, hsn, ⟨le_top, barX_isSubnormal_top 3 hsn, ?_⟩, ?_⟩
  · refine (isQuasisimple_barX_iff Nat.prime_three hsn).2 ?_
    have hker : (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 3 ↥J)).ker ≤ Subgroup.center ↥J := by
      rw [QuotientGroup.ker_mk']
      exact hO
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
        ((CFSG.LocalCores.quasisimple_central_quotient
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1
            ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).2 hJ))
          (CFSG.Open.GLAPPrimeCore 3 ↥J) hO).1))
  · intro J' hlt hJ'sn heq
    have hJ'J : J' ≤ J := hlt.le
    have hcov := (barX_eq_iff_cov Nat.prime_three hsn hJ'J).1 heq
    have hcomp : CFSG.Open.IsComponentOf J J := ⟨le_rfl, hsn, hJ⟩
    rcases CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_comp_le_or_comm hcomp hJ'J hJ'sn with
      h | h
    · exact hlt.ne (le_antisymm hJ'J h)
    ·
      apply (exists_ne_comm_of_isQuasisimple hJ).elim
      intro a ha
      obtain ⟨b, hb⟩ := ha
      apply hb
      have hcentral : ∀ x : ↥J, x ∈ Subgroup.center ↥J := by
        intro x
        obtain ⟨j', hj', hc⟩ := hcov x x.2
        have hj'c : (⟨j', hJ'J hj'⟩ : ↥J) ∈ Subgroup.center ↥J := by
          rw [Subgroup.mem_center_iff]
          intro y
          have hyx : ⁅(y : G), j'⁆ ∈ ⁅J, J'⁆ :=
            Subgroup.commutator_mem_commutator y.2 hj'
          rw [h, Subgroup.mem_bot] at hyx
          apply Subtype.ext
          show (y : G) * j' = j' * y
          rw [commutatorElement_eq_one_iff_mul_comm] at hyx
          exact hyx
        have hcO : (⟨j', hJ'J hj'⟩ : ↥J)⁻¹ * x ∈ CFSG.Open.GLAPPrimeCore 3 ↥J := by
          have := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff
            3 J _).1 hc
          exact this.2
        have hx : x = (⟨j', hJ'J hj'⟩ : ↥J) * ((⟨j', hJ'J hj'⟩ : ↥J)⁻¹ * x) := by group
        rw [hx]
        exact Subgroup.mul_mem _ hj'c (hO hcO)
      exact Subgroup.mem_center_iff.1 (hcentral b) a

theorem glaPComponent_three_of_isComponentOf {X J : Subgroup G}
    (hJ : CFSG.Open.IsComponentOf J X) (h3 : 3 ∣ Nat.card J) : CFSG.Open.GLAPComponent 3 X J :=
  glaPComponent_up Nat.prime_three (glaPComponent_three_self hJ.2.2 h3) hJ.1 hJ.2.1

end Comp

section Theta

variable {Q : Type*} [Group Q] [Finite Q]

theorem theta_eq_glaPPrimeCore (hQ : CFSG.Open.IsQuasisimple Q) (h3 : 3 ∣ Nat.card Q) :
    aschbacherSolvableCore 3 Q = CFSG.Open.GLAPPrimeCore 3 Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hchar, h3θ, hmax, -⟩ := solvable_prime_complement_core_characterization
    (H := Q) Nat.prime_three
  apply le_antisymm
  · haveI := hchar
    have hn : (aschbacherSolvableCore 3 Q).Normal := inferInstance
    have hc : Nat.Coprime 3 (Nat.card (aschbacherSolvableCore 3 Q)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3θ
    exact le_sSup ⟨hn, hc⟩
  · have hO := glaPPrimeCore_le_center hQ h3
    have hsol : Group.IsSolvable (CFSG.Open.GLAPPrimeCore 3 Q) :=
      Group.isSolvable_of_comm fun a b => by
        apply Subtype.ext
        show (a : Q) * b = b * a
        exact Subgroup.mem_center_iff.1 (hO b.2) (a : Q)
    have h3O : ¬ 3 ∣ Nat.card (CFSG.Open.GLAPPrimeCore 3 Q) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
    exact hmax _ inferInstance hsol h3O

noncomputable def thetaQuotEquivBarOf {G : Type*} [Group G] {J : Subgroup G} [Finite J]
    (hJ : CFSG.Open.IsQuasisimple ↥J) (h3 : 3 ∣ Nat.card J) :
    (↥J ⧸ aschbacherSolvableCore 3 ↥J) ≃* barOf 3 J :=
  QuotientGroup.quotientMulEquivOfEq (theta_eq_glaPPrimeCore hJ h3)

end Theta

section TripleCover

theorem three_dvd_card_of_isTripleCover {X Y : Type*} [Group X] [Group Y] [Finite X]
    (h : Sec4.IsTripleCover X Y) : 3 ∣ Nat.card X := by
  have := Subgroup.card_subgroup_dvd_card (Subgroup.center X)
  rw [h.1] at this
  exact this

theorem three_dvd_card_of_isTripleCover_theta {G : Type*} [Group G] {J : Subgroup G} [Finite J]
    {Y : Type*} [Group Y] (h : Sec4.IsTripleCover (↥J ⧸ aschbacherSolvableCore 3 ↥J) Y) :
    3 ∣ Nat.card J :=
  (three_dvd_card_of_isTripleCover h).trans
    (Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥J))

theorem isTripleCover_of_mulEquiv' {X X' Y : Type*} [Group X] [Group X'] [Group Y]
    (e : X ≃* X') (h : Sec4.IsTripleCover X Y) : Sec4.IsTripleCover X' Y := by
  have hZ : (Subgroup.center X).map (e : X →* X') = Subgroup.center X' := Subgroup.map_center_eq e
  refine ⟨?_, ?_⟩
  · rw [← hZ, Subgroup.card_map_of_injective e.injective, h.1]
  · obtain ⟨f⟩ := h.2
    exact ⟨(QuotientGroup.congr _ _ e hZ).symm.trans f⟩

theorem not_isTripleCover_of_lieCompData {G : Type} [Group G] {J : Subgroup G} [Finite J]
    {q : ℕ} (hJ : CFSG.Open.IsQuasisimple ↥J) (hd : LieCompData q (barOf 3 J))
    (h6 : Sec4.IsTripleCover (↥J ⧸ aschbacherSolvableCore 3 ↥J) (alternatingGroup (Fin 6))) :
    False := by
  have h3 := three_dvd_card_of_isTripleCover_theta h6
  have h6' := isTripleCover_of_mulEquiv' (thetaQuotEquivBarOf hJ h3) h6
  exact hd.centre h6'.2 (by rw [h6'.1])

end TripleCover

section At

variable {S : Type} [Group S] [Finite S]

theorem autFix_eq_fixSub (β : MulAut S) : Sec4.autFix β = Lemma510Ns.fixSub β :=
  Subgroup.ext fun _ => Iff.rfl

@[expose] def NoA6At (β : MulAut S) : Prop :=
  ∀ J : Subgroup S, J ≤ Sec4.autFix β → CFSG.IsQuasisimple ↥J →
    (J.subgroupOf (Sec4.autFix β)).IsSubnormal →
    ¬ Sec4.IsTripleCover (↥J ⧸ aschbacherSolvableCore 3 ↥J) (alternatingGroup (Fin 6))

theorem glaPComponent_of_autFix {β : MulAut S} {J : Subgroup S} (hJ : J ≤ Sec4.autFix β)
    (hq : CFSG.IsQuasisimple ↥J) (hsn : (J.subgroupOf (Sec4.autFix β)).IsSubnormal)
    (h3 : 3 ∣ Nat.card J) : CFSG.Open.GLAPComponent 3 (Lemma510Ns.fixSub β) J := by
  have hJo : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq)
  rw [autFix_eq_fixSub] at hJ hsn
  exact glaPComponent_three_of_isComponentOf ⟨hJ, open_isSubnormal_of_subgroupOf hJ hsn, hJo⟩ h3

theorem noA6At_of_data {β : MulAut S} {q : ℕ}
    (h : ∀ J : Subgroup S, CFSG.Open.GLAPComponent 3 (Lemma510Ns.fixSub β) J →
      LieCompData q (barOf 3 J)) : NoA6At β := by
  intro J hJ hq hsn h6
  have hJo : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hq)
  exact not_isTripleCover_of_lieCompData hJo
    (h J (glaPComponent_of_autFix hJ hq hsn (three_dvd_card_of_isTripleCover_theta h6))) h6

end At

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
