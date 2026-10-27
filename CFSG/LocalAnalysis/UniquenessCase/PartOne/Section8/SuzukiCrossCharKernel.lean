module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiCrossCharCriticalKernel
public import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.GroupTheory.PerfectActionCritical
public import CFSG.RepresentationTheory.FaithfulScalarNormal
public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofPGroup
public import CFSG.GroupTheory.SteinbergCBFTCritical
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofGL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open scoped commutatorElement

theorem critical_elementary_action_eq_one
    {H S E : Type} [Group H] [Finite H] [Group.IsPerfect H]
    [Group S] [Group E] [Finite E] {n p : ℕ} [Fact p.Prime]
    (π : H →* S) (hπ : Function.Surjective π)
    (hmin : ∀ J : Subgroup H, J.map π = ⊤ → J = ⊤)
    (hS : CFSG.Quasithin.IsSz n S) (hn : 3 ≤ n) (hp3 : p ≠ 3)
    (hE : CFSG.IsElementaryAbelian p E) (hcard : Nat.card E ≤ 169)
    (φ : H →* MulAut E) : φ = 1 := by
  classical
  have : CFSG.IsElementaryAbelian p E := hE
  obtain ⟨d, hd⟩ := (CFSG.IsElementaryAbelian.isPGroup p E).exists_card_eq
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (fun a b => (IsMulCommutative.is_comm (M := E)).comm a b)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p p E)) hd
  by_cases hsmall : d ≤ 1
  · have hcyc : IsCyclic E := by
      interval_cases d
      · have : Subsingleton E := Finite.card_le_one_iff_subsingleton.mp (by simp_all)
        exact isCyclic_of_subsingleton
      · exact isCyclic_of_prime_card (by simpa using hd)
    have : IsCyclic E := hcyc
    have htop : (⊤ : Subgroup H).map φ = ⊥ :=
      CFSG.GroupTheory.map_eq_bot_of_isPerfect_of_isCyclicTarget φ
        (by simpa only [← _root_.commutator_def] using Group.IsPerfect.commutator_eq_top (G := H))
    rw [Subgroup.map_top, MonoidHom.range_eq_bot_iff] at htop
    exact htop
  · apply eq_one_of_isSz_card_not_dvd hπ hmin hS φ
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e]
    by_cases hp2 : p = 2
    · subst p
      have hd7 : d ≤ 7 := by
        have h : 2 ^ d ≤ 169 := hd ▸ hcard
        by_contra hnot
        have h8 : 2 ^ 8 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at h8
        omega
      exact not_dvd_card_isSz_gl_two hn hS hd7
    · exact not_dvd_card_isSz_gl_odd hn hS (Fact.out : p.Prime) hp2 hp3
        (by omega) (hd ▸ hcard)

theorem critical_action_eq_one_of_center_quotient
    {H Q : Type} [Group H] [Finite H] [Group.IsPerfect H] [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (hQ : IsPGroup p Q) (φ : H →* MulAut Q)
    (hZ : ∀ h : H, ∀ z ∈ Subgroup.center Q, φ h z = z)
    (hbar : (CFSG.ClassicalInvolution.Disconnected.AschTight.centerQuotientAut Q).comp φ = 1) :
    φ = 1 := by
  have hrange : φ.range ≤ criticalKernelFixing Q := by
    rintro _ ⟨h, rfl⟩
    constructor
    · exact DFunLike.congr_fun hbar h
    · exact (mem_fixingSubgroup_iff _).mpr (hZ h)
  exact CFSG.RankThree.PartTwo.Sec20.Res11.eq_one_of_isPGroup_range φ
    ((isPGroup_criticalKernelFixing hQ).to_le hrange)

theorem normal_critical_subgroup_fixed
    {H S : Type} [Group H] [Finite H] [Group.IsPerfect H] [Group S]
    {n p : ℕ} [Fact p.Prime] (π : H →* S) (hπ : Function.Surjective π)
    (hmin : ∀ J : Subgroup H, J.map π = ⊤ → J = ⊤)
    (hS : CFSG.Quasithin.IsSz n S) (hn : 3 ≤ n) (hp3 : p ≠ 3)
    (Q : Subgroup H) [Q.Normal] (hQ : IsPGroup p Q)
    (hE : CFSG.IsElementaryAbelian p (Q ⧸ Subgroup.center Q))
    (hcard : Nat.card (Q ⧸ Subgroup.center Q) ≤ 169)
    (hZ : (Subgroup.center Q).map Q.subtype ≤ Subgroup.center H) :
    (MulAut.conjNormal (H := Q) : H →* MulAut Q) = 1 := by
  let φ : H →* MulAut Q := MulAut.conjNormal
  have hbar : (CFSG.ClassicalInvolution.Disconnected.AschTight.centerQuotientAut Q).comp φ = 1 :=
    critical_elementary_action_eq_one π hπ hmin hS hn hp3 hE hcard _
  apply critical_action_eq_one_of_center_quotient hQ φ _ hbar
  intro h z hz
  apply Subtype.ext
  change h * (z : H) * h⁻¹ = (z : H)
  have hzH : (z : H) ∈ Subgroup.center H := hZ (Subgroup.mem_map_of_mem Q.subtype hz)
  rw [Subgroup.mem_center_iff.mp hzH h, mul_inv_cancel_right]

theorem normal_p_subgroup_central_of_scalar_bounds
    {H S : Type} [Group H] [Finite H] [Group.IsPerfect H] [Group S]
    {n p : ℕ} [Fact p.Prime] (π : H →* S) (hπ : Function.Surjective π)
    (hmin : ∀ J : Subgroup H, J.map π = ⊤ → J = ⊤)
    (hS : CFSG.Quasithin.IsSz n S) (hn : 3 ≤ n) (hp3 : p ≠ 3)
    (hA : ∀ A : Subgroup H, A.Normal → IsMulCommutative A → A ≤ Subgroup.center H)
    (hB : ∀ Q : Subgroup H, Q ≤ π.ker → Q.Normal →
      (∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q) →
      Nat.card (Q ⧸ Subgroup.center Q) ≤ 169)
    (P : Subgroup H) [P.Normal] (hP : IsPGroup p P) (hPN : P ≤ π.ker) :
    P ≤ Subgroup.center H := by
  classical
  obtain ⟨C, hCn, ⟨hCclass, hCele⟩, hCfix, hCcomm, hCcen⟩ :=
    CFSG.GroupTheory.FT63ChII.ft_lemma_8_2 hP
  have : C.Characteristic := hCn
  let Q : Subgroup H := C.map P.subtype
  have hQn : Q.Normal := ConjAct.normal_of_characteristic_of_normal
  have : Q.Normal := hQn
  have hQP : Q ≤ P := Subgroup.map_subtype_le C
  let e : C ≃* Q := Subgroup.equivMapOfInjective C P.subtype P.subtype_injective
  have hQp : IsPGroup p Q := (hP.to_subgroup C).map P.subtype
  have hQclass : Q.lowerCentralSeries 2 = ⊥ := by
    rw [← Subgroup.map_lowerCentralSeries, hCclass, Subgroup.map_bot]
  have htclass : (⊤ : Subgroup Q).lowerCentralSeries 2 = ⊥ := by
    have h := Subgroup.top_subtype_lowerCentralSeries Q 2
    rw [hQclass] at h
    exact Subgroup.map_subtype_inj.mp (h.trans (Subgroup.map_bot (f := Q.subtype)).symm)
  have hcommQ : ∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q := by
    intro x y
    rw [Subgroup.mem_center_iff]
    intro z
    have hxyz : ⁅⁅x, y⁆, z⁆ ∈ (⊥ : Subgroup Q) := by
      rw [← htclass, Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_succ,
        Subgroup.lowerCentralSeries_zero]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
        (Subgroup.mem_top z)
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hxyz)).symm
  have hpowC : ∀ x : C, x ^ p ∈ Subgroup.center C := by
    intro x
    have hx : (QuotientGroup.mk x : C ⧸ Subgroup.center C) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hCele.exponent_dvd_p _
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hx
  have hpowQ : ∀ x : Q, x ^ p ∈ Subgroup.center Q := by
    intro x
    have h : e (e.symm x ^ p) ∈ (Subgroup.center C).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom (hpowC (e.symm x))
    have hcent : (Subgroup.center C).map e.toMonoidHom = Subgroup.center Q :=
      Subgroup.map_center_eq e
    rw [hcent, map_pow, e.apply_symm_apply] at h
    exact h
  have hQc : IsMulCommutative (Q ⧸ Subgroup.center Q) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    induction x using QuotientGroup.induction_on with | H x =>
      induction y using QuotientGroup.induction_on with | H y =>
        rw [← commutatorElement_eq_one_iff_mul_comm]
        change ⁅(QuotientGroup.mk' (Subgroup.center Q)) x,
          (QuotientGroup.mk' (Subgroup.center Q)) y⁆ = 1
        rw [← map_commutatorElement (QuotientGroup.mk' (Subgroup.center Q))]
        exact (QuotientGroup.eq_one_iff _).mpr (hcommQ x y)
  have hQexp : Monoid.exponent (Q ⧸ Subgroup.center Q) ∣ p := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    induction x using QuotientGroup.induction_on with | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hpowQ x
  have hQele : CFSG.IsElementaryAbelian p (Q ⧸ Subgroup.center Q) :=
    { toIsMulCommutative := hQc, exponent_dvd_p := hQexp }
  have hZnormal := CFSG.RepresentationTheory.normal_map_center_and_isMulCommutative Q
  have hZ : (Subgroup.center Q).map Q.subtype ≤ Subgroup.center H :=
    hA _ hZnormal.1 hZnormal.2
  have hfixQ : (MulAut.conjNormal (H := Q) : H →* MulAut Q) = 1 :=
    normal_critical_subgroup_fixed π hπ hmin hS hn hp3 Q hQp hQele
      (hB Q (hQP.trans hPN) hQn hcommQ) hZ
  let φ : H →* MulAut P := MulAut.conjNormal
  have hφfix : (⊤ : Subgroup H).map φ ≤ fixingSubgroup (MulAut P) (C : Set P) := by
    rintro _ ⟨h, _, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro c hc
    apply Subtype.ext
    have heqQ := congrArg (fun f : H →* MulAut Q => f h (e ⟨c, hc⟩)) hfixQ
    have heqH : h * P.subtype c * h⁻¹ = P.subtype c :=
      congrArg (fun q : Q => (q : H)) heqQ
    exact heqH
  have hφ : φ = 1 := by
    have h := CFSG.GroupTheory.map_eq_bot_of_isPerfect_of_le_fixingSubgroup φ C hCfix
      (by simpa only [← _root_.commutator_def] using Group.IsPerfect.commutator_eq_top (G := H)) hφfix
    rwa [Subgroup.map_top, MonoidHom.range_eq_bot_iff] at h
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro h
  have hfix := congrArg (fun f : H →* MulAut P => f h ⟨x, hx⟩) hφ
  have heq : h * x * h⁻¹ = x := congrArg Subtype.val hfix
  exact (mul_inv_eq_iff_eq_mul).mp heq

theorem minimal_suzuki_kernel_le_center_of_scalar_bounds
    {H S : Type} [Group H] [Finite H] [Group.IsPerfect H] [Group S]
    {n : ℕ} (π : H →* S) (hπ : Function.Surjective π)
    (hmin : ∀ J : Subgroup H, J.map π = ⊤ → J = ⊤)
    (hS : CFSG.Quasithin.IsSz n S) (hn : 3 ≤ n)
    (hA : ∀ A : Subgroup H, A.Normal → IsMulCommutative A → A ≤ Subgroup.center H)
    (hB : ∀ Q : Subgroup H, Q ≤ π.ker → Q.Normal →
      (∀ x y : Q, ⁅x, y⁆ ∈ Subgroup.center Q) →
      Nat.card (Q ⧸ Subgroup.center Q) ≤ 169) :
    π.ker ≤ Subgroup.center H := by
  classical
  have h3 : ¬ 3 ∣ Nat.card π.ker := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof.not_dvd_card_ker_of_minimal
      hπ hmin (three_not_dvd_card_of_isSz' hS)
  let Z : Subgroup π.ker := (Subgroup.center H).comap π.ker.subtype
  have hZtop : Z = ⊤ := CFSG.GroupTheory.WielandtProduct.eq_top_of_forall_sylow_le (by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    let P := Classical.arbitrary (Sylow p π.ker)
    let R : Subgroup H := (P : Subgroup π.ker).map π.ker.subtype
    have hRn : R.Normal :=
      CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof.sylow_normal_of_minimal hπ hmin p P
    have : R.Normal := hRn
    have hRp : IsPGroup p R := P.isPGroup'.map π.ker.subtype
    have hRN : R ≤ π.ker := Subgroup.map_subtype_le _
    have hRc : R ≤ Subgroup.center H := by
      by_cases hp3 : p = 3
      · subst p
        have hR3 : ¬ 3 ∣ Nat.card R := fun h => h3 (h.trans (Subgroup.card_dvd_of_le hRN))
        obtain ⟨k, hk⟩ := hRp.exists_card_eq
        have hk0 : k = 0 := by
          by_contra hkne
          exact hR3 (hk ▸ dvd_pow_self 3 hkne)
        have hRbot : R = ⊥ := Subgroup.eq_bot_of_card_le R (by simp [hk, hk0])
        rw [hRbot]
        exact bot_le
      · exact normal_p_subgroup_central_of_scalar_bounds π hπ hmin hS hn hp3
          hA hB R hRp hRN
    refine ⟨P, ?_⟩
    intro x hx
    exact hRc (Subgroup.mem_map_of_mem π.ker.subtype hx))
  intro x hx
  have hmem : (⟨x, hx⟩ : π.ker) ∈ Z := hZtop ▸ Subgroup.mem_top _
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
