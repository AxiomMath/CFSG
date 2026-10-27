module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S10.MovingThetaComponentQuasisimplicity
public import CFSG.RankThree.GroupTheory.SteinbergBMRelativeMinimalFrattini
import CFSG.RankThree.PartOne.S10.MovingThetaCore
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator
import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.GroupTheory.SteinbergBM CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement

theorem exists_prime_pCore_not_commuting {X : Type} [Group X] [Finite X] {L O : Subgroup X}
    (hOL : O ≤ L) (hOs : Group.IsSolvable O) (h : ⁅L, O⁆ ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ ⁅L, inSubgroup (pCore q) O⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply h
  have hF : (fittingSubgroup O).map O.subtype ≤ Subgroup.centralizer (L : Set X) := by
    rw [fitting_eq_sup_pCore O, Subgroup.map_iSup]
    refine iSup_le fun p => ?_
    have h1 := hcon p.1.1 (Nat.prime_of_mem_primeFactors p.1.2)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
    exact h1
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  have hxO : (⟨x, hx⟩ : O) ∈ Subgroup.centralizer (fittingSubgroup O : Set O) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfL := hF (Subgroup.mem_map_of_mem O.subtype hf)
    have := Subgroup.mem_centralizer_iff.mp hfL x (hOL hx)
    exact Subtype.ext this.symm
  have hxF := CFSG.RankThree.PGroups.solvable_fitting_self_centralizing O hxO
  exact hF (Subgroup.mem_map_of_mem O.subtype hxF)

theorem eq_one_of_fixing_pGroup_of_two_power {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {P : Type*} [Group P] {D : Set P} (hfix : IsPGroup q (fixingSubgroup (MulAut P) D))
    {σ : MulAut P} (hσD : ∀ d ∈ D, σ d = d) {k : ℕ} (hσ : σ ^ (2 ^ k) = 1) : σ = 1 := by
  have hmem : σ ∈ fixingSubgroup (MulAut P) D := by
    rw [mem_fixingSubgroup_iff (MulAut P)]
    exact hσD
  obtain ⟨j, hj⟩ := hfix ⟨σ, hmem⟩
  have hj' : σ ^ (q ^ j) = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (q ^ j) (2 ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hσ)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

theorem le_centralizer_of_centralizes_critical_subgroup {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {X : Type*} [Group X] {Q T : Subgroup X} (hTQ : T ≤ normalizer (Q : Set X))
    (hT : IsPGroup 2 T) (D₀ : Subgroup Q)
    (hfix : IsPGroup q (fixingSubgroup (MulAut Q) (D₀ : Set Q)))
    (hTD : T ≤ Subgroup.centralizer ((D₀.map Q.subtype : Subgroup X) : Set X)) :
    T ≤ Subgroup.centralizer (Q : Set X) := by
  intro t ht
  let _ : MulDistribMulAction T Q := conjActionOn hTQ
  have hsmul : ∀ (a : T) (k : Q), ((a • k : Q) : X) = (a : X) * k * (a : X)⁻¹ := fun _ _ => rfl
  let σ : MulAut Q := MulDistribMulAction.toMulAut T Q ⟨t, ht⟩
  have hσD : ∀ d ∈ (D₀ : Set Q), σ d = d := by
    intro d hd
    apply Subtype.ext
    show (((⟨t, ht⟩ : T) • d : Q) : X) = d
    rw [hsmul]
    have h := Subgroup.mem_centralizer_iff.mp (hTD ht) (d : X)
      (Subgroup.mem_map_of_mem Q.subtype hd)
    calc t * d * t⁻¹ = d * t * t⁻¹ := by rw [← h]
      _ = d := by group
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hσk : σ ^ (2 ^ k) = 1 := by
    rw [← map_pow (MulDistribMulAction.toMulAut T Q), hk, map_one]
  have hσ1 := eq_one_of_fixing_pGroup_of_two_power hq hq2 hfix hσD hσk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := congrArg (fun φ : MulAut Q => ((φ ⟨x, hx⟩ : Q) : X)) hσ1
  change (((⟨t, ht⟩ : T) • (⟨x, hx⟩ : Q) : Q) : X) = x at h
  rw [hsmul] at h
  calc x * t = t * x * t⁻¹ * t := by rw [h]
    _ = t * x := by group

theorem exists_odd_critical_subgroup {L : Type} [Group L] [Finite L] {O T : Subgroup L}
    [O.Characteristic] (hOs : Group.IsSolvable O) (hOodd : Odd (Nat.card O))
    (hO : ⁅(⊤ : Subgroup L), O⁆ ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTcl : normalClosure (T : Set L) = ⊤) :
    ∃ (q : ℕ) (D : Subgroup L), q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card O ∧ D.Characteristic ∧
      D ≠ ⊥ ∧ D ≤ O ∧ (∀ x ∈ D, x ^ q = 1) ∧ ⁅⁅D, D⁆, D⁆ = ⊥ ∧ ⁅T, D⁆ ≠ ⊥ := by
  obtain ⟨q, hq, hQ⟩ := exists_prime_pCore_not_commuting (le_top : O ≤ ⊤) hOs hO
  have : Fact q.Prime := ⟨hq⟩
  set Q : Subgroup L := inSubgroup (pCore q) O with hQdef
  have hQO : Q ≤ O := Subgroup.map_subtype_le _
  have hQchar : Q.Characteristic := by
    rw [hQdef, inSubgroup]
    infer_instance
  have hQq : IsPGroup q Q := (pCore_isPGroup (p := q) (G := O)).map O.subtype
  have hQ1 : Q ≠ ⊥ := fun h => hQ (by rw [h, Subgroup.commutator_bot_right])
  have hqO : q ∣ Nat.card O := by
    rcases hQq.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hQ1
    · exact h.trans (Subgroup.card_dvd_of_le hQO)
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr hqO)
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  obtain ⟨D₀, hD₀char, hD₀1, hD₀cl, hD₀exp, hD₀fix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hQq
  refine ⟨q, D₀.map Q.subtype, hq, hq2, hqO, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.characteristic_of_characteristic_of_characteristic
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective]
    exact hD₀1
  · exact (Subgroup.map_subtype_le D₀).trans hQO
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, hD₀exp y hy, Subgroup.coe_one]
  · have h1 : ⁅D₀, D₀⁆ ≤ Subgroup.centralizer (D₀ : Set Q) :=
      (Subgroup.commutator_mono le_rfl le_top).trans (hD₀cl.trans inf_le_right)
    have h2 : ⁅⁅D₀, D₀⁆, D₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, h2, Subgroup.map_bot]
  · intro h0
    have hTD : T ≤ Subgroup.centralizer ((D₀.map Q.subtype : Subgroup L) : Set L) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have hTQ : T ≤ normalizer (Q : Set L) := by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hTC := le_centralizer_of_centralizes_critical_subgroup hq hq2 hTQ hT2 D₀ hD₀fix hTD
    have hcl : normalClosure (T : Set L) ≤ Subgroup.centralizer (Q : Set L) :=
      normalClosure_le_normal hTC
    rw [hTcl] at hcl
    exact hQ (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcl)

theorem index_ker_toMulAut_eq_prime_of_relative_minimal {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A P : Type*} [Group A] [Finite A] [IsElementaryAbelian p A] [Group P] [Finite P]
    [Nontrivial P] [MulDistribMulAction A P] (hP : IsPGroup 2 P)
    (K : Subgroup P) (hKP : K < ⊤) (hKinv : ∀ a : A, ∀ x ∈ K, a • x ∈ K)
    (hPA : actionCommutator A (⊤ : Subgroup P) = ⊤)
    (hU : ∀ U : Subgroup P, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) →
      actionCommutator A U = U → U ≤ K) :
    (MulDistribMulAction.toMulAut A P).ker.index = p := by
  have hpA : IsPGroup p A := IsElementaryAbelian.isPGroup p A
  have hAodd : ¬ 2 ∣ Nat.card A := by
    obtain ⟨n, hn⟩ := hpA.exists_card_eq
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction A (P ⧸ frattini P) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := P) (frattini P)
      (CFSG.isInvariant_of_characteristic (A := A) (G := P) (frattini P))
  let : MulAction.QuotientAction A (frattini P) :=
    CFSG.quotientAction_of_isInvariant (A := A) (frattini P)
      (CFSG.isInvariant_of_characteristic (A := A) (G := P) (frattini P))
  obtain ⟨⟨a₀, v₀, hav⟩, hirr, -, -⟩ := relative_minimal_action_frattini_irreducibility
    Nat.prime_two hP hAodd K hKP hKinv hPA hU
  have : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : CommGroup (P ⧸ frattini P) := IsMulCommutative.instCommGroup
  have : Nontrivial (P ⧸ frattini P) := ⟨⟨v₀, a₀ • v₀, fun h => hav h.symm⟩⟩
  have : Nontrivial A := ⟨⟨a₀, 1, fun h => by rw [h, one_smul] at hav; exact hav rfl⟩⟩
  obtain ⟨B, hB, hBfix⟩ := SolvableHall.exists_hyperplane_acting_trivially_of_irreducible (p := p)
    (A := A) (H := P ⧸ frattini P) (fun U hU' => hirr U hU')
  have hBker : B ≤ (MulDistribMulAction.toMulAut A P).ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    set σ := MulDistribMulAction.toMulAut A P b with hσdef
    have hσ : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini P) σ
        = 1 := by
      ext v
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      have h1 := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply
        (frattini P) σ x
      have h3 : ((σ x : P) : P ⧸ frattini P) = (x : P ⧸ frattini P) := by
        have h := hBfix b hb (x : P ⧸ frattini P)
        rw [MulAction.Quotient.smul_coe (H := frattini P) b x] at h
        exact h
      exact h1.trans h3
    obtain ⟨-, hkerP⟩ := CFSG.GroupTheory.frattini_automorphism_kernel (p := 2) hP
    obtain ⟨k, hk⟩ := hkerP ⟨σ, hσ⟩
    have hk' : σ ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hbp : b ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p A) b
    have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hbp, map_one]
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσp) (orderOf_dvd_of_pow_eq_one hk')
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  have hker_ne_top : (MulDistribMulAction.toMulAut A P).ker ≠ ⊤ := by
    intro htop
    have hfix : ∀ a : A, ∀ x : P, a • x = x := fun a x => by
      have h : a ∈ (MulDistribMulAction.toMulAut A P).ker := htop ▸ mem_top a
      rw [MonoidHom.mem_ker] at h
      exact congrArg (fun φ : MulAut P => φ x) h
    have hbot : actionCommutator A (⊤ : Subgroup P) = ⊥ := by
      rw [actionCommutator, eq_bot_iff, closure_le]
      rintro _ ⟨x, -, a, rfl⟩
      rw [hfix a x, inv_mul_cancel]
      exact one_mem _
    rw [hbot] at hPA
    obtain ⟨x, hx⟩ := exists_ne (1 : P)
    have hx' : x ∈ (⊤ : Subgroup P) := mem_top x
    rw [← hPA] at hx'
    exact hx ((mem_bot).mp hx')
  have hdvd : (MulDistribMulAction.toMulAut A P).ker.index ∣ B.index :=
    Subgroup.index_dvd_of_le hBker
  rw [hB] at hdvd
  rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
  · exact absurd (Subgroup.index_eq_one.mp h) hker_ne_top
  · exact h

theorem le_normalizer_of_characteristic_subgroupOf {G : Type*} [Group G] {A L D : Subgroup G}
    (hAL : A ≤ normalizer (L : Set G)) (hDL : D ≤ L)
    (hchar : (D.subgroupOf L).Characteristic) : A ≤ normalizer (D : Set G) := by
  refine le_normalizer_of_conj_mem_forall fun a ha x hx => ?_
  let _ : MulDistribMulAction A L := conjActionOn hAL
  have hsmul : ∀ (a : A) (l : L), ((a • l : L) : G) = (a : G) * l * (a : G)⁻¹ := fun _ _ => rfl
  have h := Subgroup.characteristic_iff_le_comap.mp hchar
    (MulDistribMulAction.toMulEquiv L (⟨a, ha⟩ : A))
    (show (⟨x, hDL hx⟩ : L) ∈ D.subgroupOf L from hx)
  have h' : (((⟨a, ha⟩ : A) • (⟨x, hDL hx⟩ : L) : L) : G) ∈ D := h
  rwa [hsmul] at h'

theorem normalClosure_subgroupOf_eq_top_of_moving_two_subgroup {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hvan : AschVanishing G p) {A : Subgroup G}
    (hAe : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3) {L : Subgroup G}
    (hAL : A ≤ normalizer (L : Set G)) (hLfam : L ∈ thetaComponentFamily p A) {R : Subgroup G}
    (hRL : R ≤ L) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hAR : A ≤ normalizer (R : Set G))
    (hRA : ⁅R, A⁆ = R) :
    normalClosure ((R.subgroupOf L : Subgroup L) : Set L) = ⊤ := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hLfam
  have hperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsAt hLc
  have hLq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hLc
  have : IsElementaryAbelian p A := hAe
  let _ : MulDistribMulAction A L := conjActionOn hAL
  have hsmul : ∀ (a : A) (l : L), ((a • l : L) : G) = (a : G) * l * (a : G)⁻¹ := fun _ _ => rfl
  have hNθ : inSubgroup (aschbacherSolvableCore p) L ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)) := by
    rw [theta_eq_inf_of_mem_thetaComponentsAt hp hLc]
    exact inf_le_right
  have hcent : ∀ U : Subgroup L, U ≤ aschbacherSolvableCore p L → IsPGroup 2 U →
      (∀ a : A, ∀ x ∈ U, a • x ∈ U) → ∀ a : A, ∀ x ∈ U, a • x = x := by
    intro U hUN hU2 hUinv a x hx
    have hUθ : U.map L.subtype ≤
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({c} : Set G)) :=
      (Subgroup.map_mono hUN).trans hNθ
    have hUA : A ≤ normalizer ((U.map L.subtype : Subgroup G) : Set G) := by
      refine le_normalizer_of_conj_mem_forall fun a ha g hg => ?_
      obtain ⟨u, hu, rfl⟩ := hg
      exact Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : A) • u, hUinv ⟨a, ha⟩ u hu, rfl⟩
    have hbot := vanishing_centralizes_invariant_two_subgroups hp hvan hAe hAcard hcA hc1 hUθ
      (hU2.map _) hUA
    have hxc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot)
      (Subgroup.mem_map_of_mem L.subtype hx)
    have h : (a : G) * (x : G) = (x : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hxc (a : G) a.2
    apply Subtype.ext
    rw [hsmul]
    calc (a : G) * x * (a : G)⁻¹ = x * a * (a : G)⁻¹ := by rw [h]
      _ = x := by group
  set T := R.subgroupOf L with hT
  have hRT : T.map L.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRL
  have hT1 : T ≠ ⊥ := fun h => hR1 (by rw [← hRT, h, Subgroup.map_bot])
  have hT2 : IsPGroup 2 T := hR2.comap_subtype
  have hTinv : ∀ a : A, ∀ x ∈ T, a • x ∈ T := fun a x hx => by
    rw [hT, Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hAR a.2) x).mp hx
  have hTA : actionCommutator A T = T := by
    apply Subgroup.map_injective L.subtype_injective
    rw [SteinbergBM.map_actionCommutator_conj hAL T, hRT, hRA]
  exact moving_two_subgroup_normal_closure_top hp hp2 hperf hLq hcent T hT1 hT2 hTinv hTA

theorem relative_minimal_hypotheses_of_ambient {G : Type*} [Group G] {A' R D : Subgroup G}
    (hA'R : A' ≤ normalizer (R : Set G)) (hA'D : A' ≤ normalizer (D : Set G))
    (hRA' : ⁅R, A'⁆ = R) (hRD : ⁅R, D⁆ ≠ ⊥)
    (hmin : ∀ U : Subgroup G, U < R → A' ≤ normalizer (U : Set G) → ⁅U, A'⁆ = U →
      ⁅U, D⁆ = ⊥) :
    letI : MulDistribMulAction A' R := conjActionOn hA'R
    ∃ K : Subgroup R, K < ⊤ ∧ (∀ a : A', ∀ x ∈ K, a • x ∈ K) ∧
      actionCommutator A' (⊤ : Subgroup R) = ⊤ ∧
      ∀ U : Subgroup R, U < ⊤ → (∀ a : A', ∀ x ∈ U, a • x ∈ U) → actionCommutator A' U = U →
        U ≤ K := by
  let _ : MulDistribMulAction A' R := conjActionOn hA'R
  have hsmulR : ∀ (a : A') (r : R), ((a • r : R) : G) = (a : G) * r * (a : G)⁻¹ :=
    fun _ _ => rfl
  have hTopR : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨(Subgroup.centralizer (D : Set G)).subgroupOf R, ?_, ?_, ?_, ?_⟩
  · refine lt_top_iff_ne_top.mpr fun h => hRD ?_
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun r hr => ?_
    have : (⟨r, hr⟩ : R) ∈ (Subgroup.centralizer (D : Set G)).subgroupOf R :=
      h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  · intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmulR]
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro d hd
    have hd' : (a : G)⁻¹ * d * a ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hA'D (A'.inv_mem a.2)) d).mp hd
      simpa using this
    have h1 := hx _ hd'
    calc d * ((a : G) * x * (a : G)⁻¹)
        = (a : G) * (((a : G)⁻¹ * d * a) * x) * (a : G)⁻¹ := by group
      _ = (a : G) * (x * ((a : G)⁻¹ * d * a)) * (a : G)⁻¹ := by rw [h1]
      _ = (a : G) * x * (a : G)⁻¹ * d := by group
  · apply Subgroup.map_injective R.subtype_injective
    rw [SteinbergBM.map_actionCommutator_conj hA'R, hTopR, hRA']
  · intro U hUt hUinv hUA u hu
    set U' := U.map R.subtype with hU'
    have hU'R : U' < R := by
      have := (Subgroup.map_lt_map_iff_of_injective R.subtype_injective).mpr hUt
      rwa [hTopR] at this
    have hAU : A' ≤ normalizer (U' : Set G) := by
      refine le_normalizer_of_conj_mem_forall fun a ha g hg => ?_
      obtain ⟨u, hu, rfl⟩ := hg
      exact Subgroup.mem_map.mpr ⟨(⟨a, ha⟩ : A') • u, hUinv ⟨a, ha⟩ u hu, rfl⟩
    have hU'A : ⁅U', A'⁆ = U' := by
      rw [← SteinbergBM.map_actionCommutator_conj hA'R U, hUA]
    have hbot := hmin U' hU'R hAU hU'A
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      (Subgroup.mem_map_of_mem R.subtype hu)
    exact Subgroup.mem_subgroupOf.mpr this

theorem subgroupOf_inf_centralizer_eq_ker {G : Type*} [Group G] {A' R : Subgroup G}
    (hA'R : A' ≤ normalizer (R : Set G)) :
    letI : MulDistribMulAction A' R := conjActionOn hA'R
    (A' ⊓ Subgroup.centralizer (R : Set G)).subgroupOf A' =
      (MulDistribMulAction.toMulAut A' R).ker := by
  let _ : MulDistribMulAction A' R := conjActionOn hA'R
  have hsmulR : ∀ (a : A') (r : R), ((a • r : R) : G) = (a : G) * r * (a : G)⁻¹ :=
    fun _ _ => rfl
  ext a
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, h⟩
    refine MulEquiv.ext fun r => Subtype.ext ?_
    change ((a • r : R) : G) = r
    rw [hsmulR]
    have h1 := h r r.2
    calc (a : G) * r * (a : G)⁻¹ = (r * a) * (a : G)⁻¹ := by rw [← h1]
      _ = r := by group
  · intro h
    refine ⟨a.2, fun r hr => ?_⟩
    have h2 := congrArg (fun φ : MulAut R => ((φ ⟨r, hr⟩ : R) : G)) h
    change ((a • (⟨r, hr⟩ : R) : R) : G) = r at h2
    rw [hsmulR] at h2
    calc r * a = ((a : G) * r * (a : G)⁻¹) * a := by rw [h2]
      _ = a * r := by group

theorem pRank_le_three_of_le_centralizer_of_two_element {G : Type} [Group G] [Finite G]
    (he : evenRank G ≤ 3) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {R : Subgroup G}
    (hR : IsPGroup 2 R) {r : G} (hrR : r ∈ R) (hr1 : r ≠ 1) {E : Subgroup G}
    (hE : E ≤ Subgroup.centralizer ({r} : Set G)) : CFSG.pRank q ↥E ≤ 3 := by
  have hP : Subgroup.zpowers r ≠ ⊥ := fun h => hr1 (by
    have := Subgroup.mem_zpowers r
    rwa [h, Subgroup.mem_bot] at this)
  have hP2 : IsPGroup 2 (Subgroup.zpowers r) := hR.to_le (Subgroup.zpowers_le.mpr hrR)
  have hN : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G)) :=
    ⟨_, hP, hP2, rfl⟩
  have hEN : E ≤ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G) := by
    refine hE.trans ?_
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
    exact Subgroup.centralizer_le_normalizer _
  calc CFSG.pRank q ↥E = CFSG.Assembly.pRank q E := (assembly_pRank_eq hq E).symm
    _ ≤ CFSG.Assembly.pRank q (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G)) :=
      CFSG.SectionRank.pRank_mono hq.one_lt hEN
    _ ≤ localRank q G := CFSG.RankThree.Classical.pRank_le_localRank hq.one_lt hN
    _ ≤ evenRank G := CFSG.RankThree.OddKernel.localRank_le_evenRank hq hq2
    _ ≤ 3 := he

theorem nonquasisimple_moving_theta_component_minimal_odd_core_action_of
    (hB5 : SelectedPrimeElementsNormalizeThetaComponents) :
    NonquasisimpleMovingThetaComponentMinimalOddCoreAction := by
  intro G _ _ he p hp hp3 hvan A hAe hAcard L hL0 hnq
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hAL, -, -, -, hiff⟩ :=
    moving_theta_component_quasisimplicity_reduces_to_odd_core_centralization_of hB5 G he p hp hp3
      hvan A hAe hAcard L hL0
  have hLO : ⁅L, oddThetaCore p L⁆ ≠ ⊥ := fun h => hnq (hiff.mpr h)
  obtain ⟨hLfam, T, hTL, hT1, hT2, hAT, hTA'⟩ := hL0
  have hTA : ⁅T, A⁆ = T := hTA'.symm
  set θ : Subgroup L := aschbacherSolvableCore p L with hθ
  set O' : Subgroup L := inSubgroup (pPrimeCore 2) θ with hO'
  have hOO : oddThetaCore p L = O'.map L.subtype := oddThetaCore_eq_map L
  have hO'θ : O' ≤ θ := Subgroup.map_subtype_le _
  have hθchar : θ.Characteristic := inferInstance
  have hO'char : O'.Characteristic := by
    rw [hO', inSubgroup]
    infer_instance
  obtain ⟨hθsolv, -, hθp, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  have hO's : Group.IsSolvable O' :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hO'θ)
      (Subgroup.inclusion_injective hO'θ)
  have hO'odd : Odd (Nat.card O') := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := pPrimeCore_coprime_card (p := 2) (G := θ)
    rw [hO', inSubgroup, Subgroup.card_map_of_injective θ.subtype_injective]
    exact Nat.coprime_two_left.mp h
  have hpO' : ¬ p ∣ Nat.card O' := fun h => hθp (h.trans (Subgroup.card_dvd_of_le hO'θ))
  have hTopL : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hO'ne : ⁅(⊤ : Subgroup L), O'⁆ ≠ ⊥ := by
    intro h
    apply hLO
    have h2 := congrArg (Subgroup.map L.subtype) h
    rwa [Subgroup.map_commutator, hTopL, ← hOO, Subgroup.map_bot] at h2
  have hcl := normalClosure_subgroupOf_eq_top_of_moving_two_subgroup hp hp3 hvan hAe hAcard hAL
    hLfam hTL hT1 hT2 hAT hTA
  obtain ⟨q, D', hq, hq2, hqO', hD'char, hD'1, hD'O, hD'exp, hD'cl, hTD'⟩ :=
    exists_odd_critical_subgroup (O := O') (T := T.subgroupOf L) hO's hO'odd hO'ne
      hT2.comap_subtype hcl
  have hqp : q ≠ p := by
    rintro rfl
    exact hpO' hqO'
  set D : Subgroup G := D'.map L.subtype with hD
  have hDL : D ≤ L := Subgroup.map_subtype_le _
  have hDsub : D.subgroupOf L = D' :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective D'
  have hDchar : (D.subgroupOf L).Characteristic := by
    rw [hDsub]
    exact hD'char
  have hDO : D ≤ oddThetaCore p L := by
    rw [hOO]
    exact Subgroup.map_mono hD'O
  have hDexp : ∀ x ∈ D, x ^ q = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [Subgroup.subtype_apply, ← Subgroup.coe_pow, hD'exp y hy, Subgroup.coe_one]
  have hDcl : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    rw [hD, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hD'cl, Subgroup.map_bot]
  have hD1 : D ≠ ⊥ := by
    rw [hD, Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact hD'1
  have hTD : ⁅T, D⁆ ≠ ⊥ := by
    intro h
    apply hTD'
    have h2 : (⁅T.subgroupOf L, D'⁆).map L.subtype = ⊥ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTL, ← hD]
      exact h
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h2
  have hAD : A ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf hAL hDL hDchar
  obtain ⟨R, ⟨hRT, hAR, hRA, hRD⟩, hRmin⟩ := wellFounded_lt.has_min
    {S : Subgroup G | S ≤ T ∧ A ≤ normalizer (S : Set G) ∧ ⁅S, A⁆ = S ∧ ⁅S, D⁆ ≠ ⊥}
    ⟨T, le_rfl, hAT, hTA, hTD⟩
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  have hRL : R ≤ L := hRT.trans hTL
  have hR1 : R ≠ ⊥ := fun h => hRD (by rw [h, Subgroup.commutator_bot_left])
  have hmin : ∀ U : Subgroup G, U < R → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U →
      ⁅U, D⁆ = ⊥ := by
    intro U hUR hAU hUA
    by_contra h
    exact hRmin U ⟨hUR.le.trans hRT, hAU, hUA, h⟩ hUR
  have hrel : (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A = p := by
    have : IsElementaryAbelian p A := hAe
    let _ : MulDistribMulAction A R := conjActionOn hAR
    have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
    obtain ⟨K, hKP, hKinv, hPA, hU⟩ :=
      relative_minimal_hypotheses_of_ambient hAR hAD hRA hRD hmin
    have hidx := index_ker_toMulAut_eq_prime_of_relative_minimal (p := p) hp2 (A := A) (P := R)
      hR2 K hKP hKinv hPA hU
    rw [Subgroup.relIndex, subgroupOf_inf_centralizer_eq_ker hAR]
    exact hidx
  have hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3 :=
    fun r hr hr1 =>
      pRank_le_three_of_le_centralizer_of_two_element he hq hq2 hR2 hr hr1 inf_le_right
  exact ⟨q, hq, hq2, hqp, D, R, hD1, hDL, hDchar, hDO, hDexp, hDcl, hR2, hRL, hAR, hRA, hR1, hRD,
    hmin, hrel, hrank⟩

end CFSG.RankThree.PartOne
