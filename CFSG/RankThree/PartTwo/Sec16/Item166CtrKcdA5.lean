module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrLB
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.GroupTheory.CoprimeActionSupport.OrderThreePairCommutator
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec16.Item166KStep
public import CFSG.RankThree.PartTwo.Sec16.Item166ThetaTripleA6
public import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS

@[expose] def Step166KcdA5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ b ∈ ({c * d, c * d ^ 2} : Set G),
    ∀ X ∈ thetaComponentsAt 3 b,
      X = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) X →
      CFSG.Open.pCoreOf 2 X = ⊥ →
      ∀ (M J P : Subgroup G) (p : ℕ), p.Prime → 3 < p →
        M ∈ scriptY2 A → J ≤ M → M ≤ Subgroup.normalizer (J : Set G) →
        J ≤ Y₀ → J ⊓ CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 J →
        Group.IsPerfect ↥J → Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) →
        A ≤ Subgroup.normalizer (J : Set G) →
        IsPGroup p P → P ≤ M → A ≤ Subgroup.normalizer (P : Set G) →
        ⁅P, J⁆ ≤ CFSG.Open.pCoreOf 2 J →
        inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G)) ≤ X →
        Nonempty (↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
          CFSG.pCore 2 ↥(inSubgroup perfectResidual (J ⊓ Subgroup.centralizer ({b} : Set G))) ≃*
          alternatingGroup (Fin 5)) →
        ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≤
          inSubgroup (aschbacherSolvableCore 3) X →
        ⁅⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆, Subgroup.zpowers d⁆ =
          ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ →
        ⁅P ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ = ⊥

@[expose] def Step166A5Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ b ∈ ({c * d, c * d ^ 2} : Set G),
    ∀ X ∈ thetaComponentsAt 3 b,
      X = lB A (Subgroup.closure {c, d}) ⊔ inSubgroup (aschbacherSolvableCore 3) X →
      CFSG.Open.pCoreOf 2 X = ⊥ →
      ∀ J : Subgroup G, J ≤ Y₀ → Group.IsPerfect ↥J →
        Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)) →
        A ≤ Subgroup.normalizer (J : Set G) →
        let I := inSubgroup perfectResidual
          (J ⊓ Subgroup.centralizer ({b} : Set G))
        I ≤ X ∧ Group.IsPerfect ↥I ∧
          Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5)) ∧
          A ≤ Subgroup.normalizer (I : Set G)

end CFSG.RankThree.PartTwo.Sec16

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec11
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private lemma commutator_zpowers_le_of_div_mem_centralizer {Q : Subgroup G} {a b : G}
    (hcomm : Commute a b) (hbN : b ∈ Subgroup.normalizer (Q : Set G))
    (hab : a / b ∈ Subgroup.centralizer (Q : Set G)) :
    ⁅Q, Subgroup.zpowers a⁆ ≤ ⁅Q, Subgroup.zpowers b⁆ := by
  rw [Subgroup.commutator_le]
  intro q hq g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hbNn : b ^ n ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpow_mem (Subgroup.normalizer (Q : Set G)) hbN n
  have hdiv : a ^ n / b ^ n ∈ Subgroup.centralizer (Q : Set G) := by
    have heq : a ^ n / b ^ n = (a / b) ^ n := by
      rw [div_eq_mul_inv, div_eq_mul_inv, hcomm.inv_right.mul_zpow, inv_zpow]
    rw [heq]
    exact Subgroup.zpow_mem (Subgroup.centralizer (Q : Set G)) hab n
  rw [KStep166.commutatorElement_eq_of_div_mem_centralizer hbNn hdiv hq]
  exact Subgroup.commutator_mem_commutator hq (Subgroup.zpow_mem_zpowers b n)

private lemma commutator_zpowers_eq_of_mul_mem_centralizer {Q : Subgroup G} {c d : G} {k : ℕ}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hcd : Commute c d)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (hdQ : d ∈ Subgroup.normalizer (Q : Set G)) (hk : k = 1 ∨ k = 2)
    (hb : c * d ^ k ∈ Subgroup.centralizer (Q : Set G)) :
    ⁅Q, Subgroup.zpowers c⁆ = ⁅Q, Subgroup.zpowers d⁆ := by
  have hdord : orderOf d = 3 := by
    have hdvd : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    have hne : orderOf d ≠ 1 := fun h => hd1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hne
    · exact h3
  have hb0N : d ^ (3 - k) ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.pow_mem _ hdQ (3 - k)
  have hcommcb : Commute c (d ^ (3 - k)) := hcd.pow_right (3 - k)
  have hb0inv : (d ^ (3 - k))⁻¹ = d ^ k := by
    have h : d ^ (3 - k) * d ^ k = 1 := by
      rw [← pow_add, show 3 - k + k = 3 by omega, hd3]
    exact inv_eq_of_mul_eq_one_right h
  have hcbC : c / d ^ (3 - k) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [div_eq_mul_inv, hb0inv]
    exact hb
  have hbcC : d ^ (3 - k) / c ∈ Subgroup.centralizer (Q : Set G) := by
    have h := Subgroup.inv_mem (Subgroup.centralizer (Q : Set G)) hcbC
    simpa [div_eq_mul_inv] using h
  have hz : Subgroup.zpowers (d ^ (3 - k)) = Subgroup.zpowers d := by
    have h := (Subgroup.zpowers_eq_zpowers_iff' d ((3 - k : ℕ) : ℤ) 1).mpr ?_
    · simpa using h
    · rcases hk with rfl | rfl <;> norm_num [hdord]
  have h1 : ⁅Q, Subgroup.zpowers c⁆ ≤ ⁅Q, Subgroup.zpowers (d ^ (3 - k))⁆ :=
    commutator_zpowers_le_of_div_mem_centralizer hcommcb hb0N hcbC
  have h2 : ⁅Q, Subgroup.zpowers (d ^ (3 - k))⁆ ≤ ⁅Q, Subgroup.zpowers c⁆ :=
    commutator_zpowers_le_of_div_mem_centralizer hcommcb.symm hcQ hbcC
  rw [← hz]
  exact le_antisymm h1 h2

private theorem inf_centralizer_le_centralizer_of_cd_of_kcdA5
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h143 : Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (hKcd : Step166KcdA5) (hData : Step166A5Data)
    {J : Subgroup G} (hJY : J ≤ Y₀) (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d) {P : Subgroup G} {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hPQ : P ∈ scriptQ A (lB A))
    {M : Subgroup G} (hMY : M ∈ scriptY2 A) (hJM : J ≤ M)
    (hMJ : M ≤ Subgroup.normalizer (J : Set G)) (hPM : P ≤ M)
    (hPJ : ⁅P, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hJQ : J ⊓ CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 J)
    {k : ℕ} (hk : k = 1 ∨ k = 2) :
    P ⊓ Subgroup.centralizer ({c * d ^ k} : Set G) ≤
      Subgroup.centralizer ({c} : Set G) := by
  classical
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hcA : c ∈ A := hD13.mem_A
  have hcd : Commute c d := hD13.commute hcA hdA
  have hcd3 : d ^ 3 = 1 := hA.1.2 d hdA
  have hbA : c * d ^ k ∈ A := A.mul_mem hcA (A.pow_mem hdA k)
  have hbmem : c * d ^ k ∈ ({c * d, c * d ^ 2} : Set G) := by
    rcases hk with rfl | rfl
    · simpa using Set.mem_insert (c * d) ({c * d ^ 2} : Set G)
    · simpa using Set.mem_insert_of_mem (c * d) (Set.mem_singleton (c * d ^ 2))
  obtain ⟨X, hX, hΔ, hXL, hA6⟩ :=
    exists_thetaComponent_at_cd h hJ h143 h134 h48 h1514 hMeets hdA hd1 hdc hk
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    Proof17Res10.omegaA_eq_of_j2 h (h1514 G A c L Y₀ h) (hMeets G A c L Y₀ h)
      hD13.zpowers_mem_omegaA hD13.mem_lA hJ
  obtain ⟨-, hb1, -, -, -⟩ := b_facts h hJ hΩ hdA hd1 hdc hk
  let O : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer ({c * d ^ k} : Set G))
  let U₀ : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  let θX : Subgroup G := inSubgroup (aschbacherSolvableCore 3) X
  obtain ⟨L0, hL0⟩ : ∃ L0 : Subgroup G, L0 = lB A (Subgroup.closure {c, d}) := ⟨_, rfl⟩
  have hXLlB : X = lB A (Subgroup.closure {c, d}) ⊔
      inSubgroup (aschbacherSolvableCore 3) X := hXL
  rw [← hL0] at hXL
  let W : Subgroup G := U₀ ⊔ L0
  let Q : Subgroup G := P ⊓ Subgroup.centralizer ({c * d ^ k} : Set G)
  let U : Subgroup G := ⁅Q, Subgroup.zpowers c⁆
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := (mem_scriptQ_iff.mp hPQ).2.1
  have hAb : A ≤ Subgroup.centralizer ({c * d ^ k} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hD13.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨c * d ^ k, hbA⟩))
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    (le_inf hAP (hAb.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hPΔ : Q ≤ delta A (lB A) (Subgroup.centralizer ({c * d ^ k} : Set G)) := by
    simpa [Q] using inf_centralizer_le_delta hPQ hbA (fun x hx y hy => hD13.commute hx hy)
  have hX' : X ∈ thetaComponentsIn (Subgroup.centralizer ({c * d ^ k} : Set G)) := by
    rw [← thetaComponentsAt_eq_thetaComponentsIn]
    exact hX
  have hXO : X ⊓ O = θX := by
    have := ThetaCompY.inf_pPrimeCoreOf_eq hX' hA6
    simpa [O, θX, inSubgroup] using this
  have hθX_le_O : θX ≤ O := by rw [← hXO]; exact inf_le_right
  have hOX : O ≤ Subgroup.normalizer (X : Set G) :=
    KStep166.pPrimeCoreOf_le_normalizer_of_thetaComponentsIn hX' hA6
  have hHnorm : Subgroup.centralizer ({c * d ^ k} : Set G) ≤
      Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 _
  have hcH : c ∈ Subgroup.centralizer ({c * d ^ k} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.refl c).mul_right (hcd.pow_right k)).eq
  have hdH : d ∈ Subgroup.centralizer ({c * d ^ k} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcd.symm.mul_right ((Commute.refl d).pow_right k)
  have hcO : c ∈ Subgroup.normalizer (O : Set G) := hHnorm hcH
  have hdO : d ∈ Subgroup.normalizer (O : Set G) := hHnorm hdH
  have hcB : c ∈ Subgroup.closure {c, d} :=
    Subgroup.subset_closure (Set.mem_insert c (Set.singleton d))
  have hbB : c * d ^ k ∈ Subgroup.closure {c, d} := by
    refine Subgroup.mul_mem _ hcB (Subgroup.pow_mem _ ?_ k)
    exact Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  have hWc : W ≤ Subgroup.centralizer ({c} : Set G) := by
    simpa [W, hL0] using KStep166.sup_pPrimeCoreOf_lB_le_centralizer hcA hcB
  have hWH : W ≤ Subgroup.centralizer ({c * d ^ k} : Set G) := by
    simpa [W, hL0] using KStep166.sup_pPrimeCoreOf_lB_le_centralizer hbA hbB
  have hWO : W ≤ Subgroup.normalizer (O : Set G) := hWH.trans hHnorm
  have hXLd : X = L0 ⊔ θX := by
    simpa [θX] using hXL
  have hQX : Q ≤ (U₀ ⊔ L0) ⊔ O := by
    calc Q ≤ delta A (lB A) (Subgroup.centralizer ({c * d ^ k} : Set G)) := hPΔ
      _ = O ⊔ U₀ ⊔ X := hΔ
      _ = O ⊔ U₀ ⊔ (L0 ⊔ θX) := by rw [hXLd]
      _ ≤ O ⊔ U₀ ⊔ (L0 ⊔ O) :=
        sup_le_sup_left (sup_le_sup_left hθX_le_O L0) (O ⊔ U₀)
      _ = (U₀ ⊔ L0) ⊔ O := by ac_rfl
  have hmemLd : d ∈ inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    mem_ld_of_threeCentral h hJ hdA hd1 hdc
  have hLdle : L0 ≤ X := by
    rw [hXLd]
    exact le_sup_left
  have hdX : d ∈ X := by
    have hL0Eq : L0 = inSubgroup perfectResidual
        (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
      rw [hL0]
      exact lB_closure_eq_residual h hJ hdA hd1 hdc
    exact hLdle (hL0Eq ▸ hmemLd)
  have hcomm_le := KStep166.commutator_commutator_le (P := P) (Q := Q) (O := O) (W := W)
    (X := X) (c := c) (d := d) inf_le_left (hAP hcA) (hAP hdA) hcO hdO hWO hWc hQX hOX hdX
  have hQdN : d ∈ Subgroup.normalizer (Q : Set G) := hAQ hdA
  have hQcN : c ∈ Subgroup.normalizer (Q : Set G) := hAQ hcA
  have hQb : c * d ^ k ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun q hq => Subgroup.mem_centralizer_singleton_iff.mp hq.2
  have hUeqd : U = ⁅Q, Subgroup.zpowers d⁆ := by
    simpa [U] using commutator_zpowers_eq_of_mul_mem_centralizer hcd3 hd1 hcd hQcN hQdN hk hQb
  have hUidem : ⁅U, Subgroup.zpowers d⁆ = U := by
    rw [hUeqd]
    refine CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3
      Nat.prime_three (Subgroup.zpowers d) Q ?_ ?_ ?_
    · exact Sec6.isPGroup_zpowers_of_pow_three hcd3
    · exact Subgroup.zpowers_le.mpr hQdN
    · have hdord : orderOf d = 3 := by
        have hdvd : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hcd3
        have hne : orderOf d ≠ 1 := fun h => hd1 (orderOf_eq_one_iff.mp h)
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact absurd h1 hne
        · exact h3
      have hcardd : Nat.card (Subgroup.zpowers d) = 3 := by
        rw [Nat.card_zpowers, hdord]
      have hcop := IsPGroup.coprime_card_of_ne 3 p (Ne.symm hp3) (Subgroup.zpowers d) Q
        (Sec6.isPGroup_zpowers_of_pow_three hcd3) (hP.to_le inf_le_left)
      simpa [hcardd] using hcop
  have hUθ : U ≤ θX := by
    have hUU : U = ⁅⁅Q, Subgroup.zpowers c⁆, Subgroup.zpowers d⁆ := by
      rw [show ⁅⁅Q, Subgroup.zpowers c⁆, Subgroup.zpowers d⁆ = ⁅U, Subgroup.zpowers d⁆
        from rfl, hUidem]
    rw [hUU]
    refine hcomm_le.trans ?_
    rw [hXO]
    exact inf_le_right
  have hPJN : P ≤ Subgroup.normalizer (J : Set G) := hPM.trans hMJ
  have hQI : Q ≤ Subgroup.normalizer
      ((inSubgroup perfectResidual
        (J ⊓ Subgroup.centralizer ({c * d ^ k} : Set G)) : Subgroup G) : Set G) := by
    have hQJ : Q ≤ Subgroup.normalizer (J : Set G) := inf_le_left.trans hPJN
    have hQbN : Q ≤ Subgroup.normalizer
        (Subgroup.centralizer ({c * d ^ k} : Set G) : Set G) :=
      inf_le_right.trans Subgroup.le_normalizer
    refine (le_inf hQJ hQbN).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf.trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _)
  have hUQ : U ≤ Q :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hQcN)
  have hUUI : U ≤ Subgroup.normalizer
      ((inSubgroup perfectResidual
        (J ⊓ Subgroup.centralizer ({c * d ^ k} : Set G)) : Subgroup G) : Set G) :=
    hUQ.trans hQI
  have hAcN : A ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hD13.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
    have h : Subgroup.centralizer ({c} : Set G) =
        Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact (h ▸ hAc).trans (Subgroup.centralizer_le_normalizer _)
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    simpa [U] using Sec14.le_normalizer_commutator hAQ hAcN
  have h3p : 3 < p := by
    have hp2' := (Fact.out : Nat.Prime p).two_le
    omega
  have hPU : IsPGroup p U := hP.to_le (hUQ.trans inf_le_left)
  have hUbot : U = ⊥ := by
    by_cases hO2 : CFSG.Open.pCoreOf 2 X = ⊥
    · obtain ⟨hIX, -, hIA5, -⟩ :=
        hData G A c L Y₀ h hJ d hdA hd1 hdc (c * d ^ k) hbmem X hX hXLlB hO2
          J hJY hJperf hJA5 hAJ
      exact hKcd G A c L Y₀ h hJ d hdA hd1 hdc (c * d ^ k) hbmem X hX hXLlB hO2
        M J P p (Fact.out) h3p hMY hJM hMJ hJY hJQ hJperf hJA5 hAJ hP hPM hAP hPJ
        hIX hIA5 hUθ hUidem
    · have hXtop : X ≠ ⊤ := by
        intro htop
        have hXC : X ≤ Subgroup.centralizer ({c * d ^ k} : Set G) :=
          Sec14.le_centralizer_of_mem_thetaComponentsAt hX
        exact Sec14.centralizer_singleton_ne_top hD13.isSimpleGroup hD13.nonabelian
          hb1 (top_le_iff.mp (htop ▸ hXC))
      have hS4 : SectionFourHyp ↥X := hD13.toTheoremFourHyp.sectionFourHyp hXtop
      have hperf : Group.IsPerfect ↥X := Sec6.isPerfect_of_mem_thetaComponentsAt hX
      haveI : Group.IsPerfect ↥X := hperf
      have hO2' : CFSG.pCore 2 ↥X ≠ ⊥ := by
        intro hbot
        exact hO2 (by rw [CFSG.Open.pCoreOf, hbot, Subgroup.map_bot])
      have heq := ThetaTripleA6.aschbacherSolvableCore_eq_pCore_two hS4 hA6 hO2'
      have hEq : θX = CFSG.Open.pCoreOf 2 X := by
        unfold θX inSubgroup CFSG.Open.pCoreOf
        rw [heq]
      have hUO2 : U ≤ CFSG.Open.pCoreOf 2 X := hUθ.trans (le_of_eq hEq)
      have hdisj := IsPGroup.disjoint_of_ne p 2 hp2 U (CFSG.Open.pCoreOf 2 X) hPU
        ((CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map X.subtype)
      have hinf : U ⊓ CFSG.Open.pCoreOf 2 X = ⊥ := hdisj.eq_bot
      rwa [inf_eq_left.mpr hUO2] at hinf
  have hQc : Q ≤ Subgroup.centralizer ({c} : Set G) := by
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUbot
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  simpa [Q] using hQc

theorem commutator_zpowers_le_centralizer_d_of_kcdA5 (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h143 : Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8) (h1514 : Item1514S17)
    (hMeets : Claim1715Meets) (hKcd : Step166KcdA5)
    (hData : Step166A5Data) {J : Subgroup G} (hJY : J ≤ Y₀) (hJperf : Group.IsPerfect ↥J)
    (hJA5 : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* alternatingGroup (Fin 5)))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdc : IsThreeCentralIn L d) {P : Subgroup G} {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hPQ : P ∈ scriptQ A (lB A))
    {M : Subgroup G} (hMY : M ∈ scriptY2 A)
    (hJM : J ≤ M) (hMJ : M ≤ Subgroup.normalizer (J : Set G)) (hPM : P ≤ M)
    (hPJ : ⁅P, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hJQ : J ⊓ CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 J) :
    ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) := by
  classical
  have hD13 : Sec13Data G A c L := h.toSec13Data
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hcA : c ∈ A := hD13.mem_A
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := (mem_scriptQ_iff.mp hPQ).2.1
  have h1 : P ⊓ Subgroup.centralizer ({c * d} : Set G) ≤
      Subgroup.centralizer ({c} : Set G) := by
    simpa using inf_centralizer_le_centralizer_of_cd_of_kcdA5 h hJ h143 h134 h48 h1514
      hMeets hKcd hData hJY hJperf hJA5 hAJ hdA hd1 hdc hP hp2 hp3 hPQ
      hMY hJM hMJ hPM hPJ hJQ (Or.inl rfl)
  have h2 : P ⊓ Subgroup.centralizer ({c * d ^ 2} : Set G) ≤
      Subgroup.centralizer ({c} : Set G) :=
    inf_centralizer_le_centralizer_of_cd_of_kcdA5 h hJ h143 h134 h48 h1514 hMeets hKcd hData
      hJY hJperf hJA5 hAJ hdA hd1 hdc hP hp2 hp3 hPQ hMY hJM hMJ hPM hPJ hJQ (Or.inr rfl)
  exact GroupTheory.CoprimeActionSupport.OrderThreePairCommutator.commutator_zpowers_le_centralizer
    hP hp3 (hA.1.2 c hcA) (hA.1.2 d hdA) (hD13.commute hcA hdA) (hAP hcA) (hAP hdA) h1 h2

end CFSG.RankThree.PartTwo.Sec16.Ctr166
