module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization
import CFSG.RankThree.GroupTheory.SteinbergBMFaithfulRankThreeLineKernel
import CFSG.RankThree.GroupTheory.SteinbergBKSylowTwoCentralQuotient
public import CFSG.RankThree.GroupTheory.SteinbergBKMovingTwoSubgroup
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.GroupTheory.SteinbergBK

theorem moving_two_subgroup_normal_closure_top {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {L A : Type*} [Group L] [Finite L] [Group A] [MulDistribMulAction A L]
    (hLperf : Group.IsPerfect L)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hcent : ∀ U : Subgroup L, U ≤ aschbacherSolvableCore p L → IsPGroup 2 U →
      (∀ a : A, ∀ x ∈ U, a • x ∈ U) → ∀ a : A, ∀ x ∈ U, a • x = x)
    (T : Subgroup L) (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T)
    (hTA : actionCommutator A T = T) :
    normalClosure (T : Set L) = ⊤ := by
  classical
  set N := aschbacherSolvableCore p L with hNdef
  obtain ⟨hNsolv, hNchar, hNp, hNmax, -⟩ := solvable_prime_complement_core_characterization
    (H := L) hp
  have := hNchar
  have : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  have hnc : ¬ T.map π ≤ center (L ⧸ N) := by
    intro hcen
    set TO := (T.map π).comap π with hTO
    have hTTO : T ≤ TO := le_comap_map π T
    have hOTO : N ≤ TO := by
      intro x hx
      change π x ∈ T.map π
      rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have hTmapn : (T.map π).Normal := ⟨fun x hx g => by
      rw [mem_center_iff.mp (hcen hx) g, mul_inv_cancel_right]
      exact hx⟩
    have hTOn : TO.Normal := hTmapn.comap π
    have hTOsolv : Group.IsSolvable TO := by
      let g : TO →* T.map π := (π.comp TO.subtype).codRestrict (T.map π) fun x => x.2
      let f : N.subgroupOf TO →* TO := (N.subgroupOf TO).subtype
      have hcomm : IsMulCommutative (T.map π) := ⟨⟨fun a b => Subtype.ext
        ((mem_center_iff.mp (hcen a.2) b).symm)⟩⟩
      have : Group.IsSolvable (N.subgroupOf TO) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (subgroupOfEquivOfLe hOTO).toMonoidHom) (MulEquiv.injective _)
      refine Group.isSolvable_of_ker_le_range f g fun x hx => ?_
      have hx1 : π (x : L) = 1 := congrArg Subtype.val hx
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      exact ⟨⟨x, hx1⟩, rfl⟩
    have hTOp : ¬ p ∣ Nat.card TO := by
      intro hdvd
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hπx : π (x : L) ∈ T.map π := x.2
      obtain ⟨y, hy, hyx⟩ := hπx
      obtain ⟨k, hk⟩ := hT2 ⟨y, hy⟩
      have h1 : π (x : L) ^ 2 ^ k = 1 := by
        rw [← hyx, ← map_pow]
        have := congrArg Subtype.val hk
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
        rw [this, map_one]
      have hxp := pow_orderOf_eq_one x
      rw [hx] at hxp
      have h2 : π (x : L) ^ p = 1 := by
        rw [← map_pow, ← Subgroup.coe_pow, hxp, Subgroup.coe_one, map_one]
      have hcop : Nat.Coprime (2 ^ k) p :=
        Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd))
      have h3 : π (x : L) = 1 := by
        have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
        rwa [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
      have hxp' : orderOf (⟨x, h3⟩ : N) = p :=
        (Subgroup.orderOf_coe (⟨x, h3⟩ : N)).symm.trans ((Subgroup.orderOf_coe x).trans hx)
      have hdvdN : orderOf (⟨x, h3⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
      rw [hxp'] at hdvdN
      exact hNp hdvdN
    have hTN : T ≤ N := hTTO.trans (hNmax TO hTOn hTOsolv hTOp)
    have hfix := hcent T hTN hT2 hTinv
    apply hT1
    rw [← hTA, eq_bot_iff, actionCommutator, closure_le]
    rintro _ ⟨h, hh, a, rfl⟩
    rw [hfix a h hh, inv_mul_cancel]
    exact one_mem _
  set M := normalClosure (T : Set L) with hM
  have hMn : M.Normal := normalClosure_normal
  have hTM : T ≤ M := subset_normalClosure
  have hMπ : M.map π = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (hMn.map π
      (QuotientGroup.mk'_surjective N)) with h | h
    · exact h
    · exact absurd ((map_mono hTM).trans h) hnc
  have hMN : M ⊔ N = ⊤ := by
    have h := comap_map_eq π M
    rw [hMπ, comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp N.subtype) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M q
    have hg : g ∈ ((M ⊔ N : Subgroup L) : Set L) := hMN ▸ mem_top g
    rw [normal_mul] at hg
    obtain ⟨m, hm, o, ho, rfl⟩ := hg
    refine ⟨⟨o, ho⟩, ?_⟩
    have hm1 : QuotientGroup.mk' M m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [MonoidHom.comp_apply, map_mul, hm1, one_mul]
    rfl
  have hsolv : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hsurj
  have htop : commutator (L ⧸ M) = ⊤ := by
    rw [_root_.commutator_def, ← map_top_of_surjective _ (QuotientGroup.mk'_surjective M),
      ← map_commutator, ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  have hsub : Subsingleton (L ⧸ M) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := L ⧸ M)).ne htop
  refine eq_top_iff.mpr fun g _ => ?_
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

theorem actionCommutator_top_eq_top_of_moving_two_subgroup {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) {L A : Type*} [Group L] [Finite L] [Group A] [MulDistribMulAction A L]
    (hLperf : Group.IsPerfect L)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hcent : ∀ U : Subgroup L, U ≤ aschbacherSolvableCore p L → IsPGroup 2 U →
      (∀ a : A, ∀ x ∈ U, a • x ∈ U) → ∀ a : A, ∀ x ∈ U, a • x = x)
    (T : Subgroup L) (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T)
    (hTA : actionCommutator A T = T) :
    actionCommutator A (⊤ : Subgroup L) = ⊤ := by
  have hcl := moving_two_subgroup_normal_closure_top hp hodd hLperf hLq hcent T hT1 hT2 hTinv hTA
  have : (actionCommutator A (⊤ : Subgroup L)).Normal := actionCommutator_top_normal
  have hle : normalClosure (T : Set L) ≤ actionCommutator A (⊤ : Subgroup L) := by
    apply normalClosure_le_normal
    intro x hx
    have hx' : x ∈ actionCommutator A T := by rw [hTA]; exact hx
    exact CFSG.RankThree.GroupTheory.SteinbergBM.actionCommutator_mono (A := A) le_top hx'
  rw [hcl] at hle
  exact eq_top_iff.mpr hle

theorem commutatorSubgroup_eq_actionCommutator {L A : Type*} [Group L] [Group A]
    [MulDistribMulAction A L] (H : Subgroup L) :
    commutatorSubgroup A L H = actionCommutator A H := by
  unfold commutatorSubgroup actionCommutator
  congr 1
  ext x
  constructor
  · rintro ⟨a, h, hh, rfl⟩
    exact ⟨h, hh, a, rfl⟩
  · rintro ⟨h, hh, a, rfl⟩
    exact ⟨a, h, hh, rfl⟩

theorem moving_theta_odd_core_quotient {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {L A : Type*} [Group L] [Finite L] [Group A] [Finite A] [IsElementaryAbelian p A]
    [MulDistribMulAction A L] (hLperf : Group.IsPerfect L)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hcent : ∀ U : Subgroup L, U ≤ aschbacherSolvableCore p L → IsPGroup 2 U →
      (∀ a : A, ∀ x ∈ U, a • x ∈ U) → ∀ a : A, ∀ x ∈ U, a • x = x)
    (T : Subgroup L) (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T)
    (hTA : actionCommutator A T = T) :
    actionCommutator A (⊤ : Subgroup L) = ⊤ ∧
      ⁅aschbacherSolvableCore p L, (⊤ : Subgroup L)⁆ ≤
        inSubgroup (pPrimeCore 2) (aschbacherSolvableCore p L) ∧
      IsQuasisimple (L ⧸ inSubgroup (pPrimeCore 2) (aschbacherSolvableCore p L)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hLA := actionCommutator_top_eq_top_of_moving_two_subgroup hp hodd hLperf hLq hcent T hT1
    hT2 hTinv hTA
  set N := aschbacherSolvableCore p L with hN
  obtain ⟨hNs, hNchar, hNp, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  have := hNchar
  have : N.Normal := inferInstance
  have hNinv : ∀ a : A, ∀ x ∈ N, a • x ∈ N := by
    intro a x hx
    have hc := (Subgroup.characteristic_iff_comap_eq.mp hNchar)
      (MulDistribMulAction.toMulEquiv L a)
    have : x ∈ N.comap (MulDistribMulAction.toMulEquiv L a).toMonoidHom := by
      rw [hc]; exact hx
    exact this
  have : CFSG.IsInvariant A L N := ⟨fun a g => by
    refine ⟨hNinv a g, fun h => ?_⟩
    have := hNinv a⁻¹ _ h
    rwa [inv_smul_smul] at this⟩
  obtain ⟨P, hP⟩ := CFSG.SolvableHall.exists_invariant_sylow (p := p) (A := A) (H := N) hNp 2
  have hPfix : ∀ a : A, ∀ x ∈ (P : Subgroup N), a • (x : L) = x := by
    have hU := hcent ((P : Subgroup N).map N.subtype) (Subgroup.map_subtype_le _)
      (P.isPGroup'.map _) (by
        rintro a _ ⟨y, hy, rfl⟩
        exact ⟨a • y, hP a y hy, rfl⟩)
    intro a x hx
    exact hU a x ⟨x, hx, rfl⟩
  have hBK := generated_action_centralized_sylow_two_solvable_core_central_quotient
    N hNs hNinv (by rw [commutatorSubgroup_eq_actionCommutator]; exact hLA) ⟨P, hPfix⟩
  obtain ⟨-, hcomm, -, hcen⟩ := hBK
  refine ⟨hLA, hcomm, ?_⟩
  set O := inSubgroup (pPrimeCore 2) N with hO
  have hON : O ≤ N := Subgroup.map_subtype_le _
  have : O.Normal := CFSG.RankThree.GroupTheory.SteinbergBK.inSubgroup_pPrimeCore_normal 2 N
  have hperf : Group.IsPerfect (L ⧸ O) := by
    have := hLperf
    exact Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective O)
  have hqq : IsQuasisimple ((L ⧸ O) ⧸ N.map (QuotientGroup.mk' O)) :=
    LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientQuotientEquivQuotient O N hON).symm
      hLq
  have hWn : (N.map (QuotientGroup.mk' O)).Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hcen hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hqd := LocalCores.quasisimple_central_extension_derived (N.map (QuotientGroup.mk' O)) hcen
    hqq
  have htop : IsQuasisimple ↥(⊤ : Subgroup (L ⧸ O)) := by
    rw [← hperf.commutator_eq_top]
    exact hqd
  exact LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv htop

end CFSG.RankThree.PartOne
