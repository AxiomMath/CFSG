module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseII2
public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseII
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Tools

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83_partOne_false
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S) : False := by
  classical
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  set m : ℕ := 2 ^ CFSG.pRank 2 S with hm
  have hm2 : 2 ≤ 2 * a + 1 := by omega
  have hq1 : 1 ≤ q := by
    have h : 0 < q := by rw [hq]; positivity
    omega
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqpos : 0 < q := by omega
  have hB1 : VSzBig L1 ∨ VU3Big L1 := Or.inl ⟨a, ha, hSz⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, hm2, hL2⟩))
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hL2sup : IsL2Quot (2 * a + 1) (oTwoQuot ↥(L2 ⊔ S)) := by
    have hsupQ : L2 ⊔ S = L2 ⊔ Q1 L2 L1 S := by
      rw [hsup2]
      simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hsupQ]
    obtain ⟨eL⟩ := hL2
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL⟩
  have hJ' : jAtLeast m q S ≤ Q1 L1 L2 S := by
    rw [hm, hq]
    exact hJ
  have hJQ1 : jAtLeast m q (Q1 L1 L2 S) = jAtLeast m q S :=
    jAtLeast_eq_of_le hJ' hQ1S
  set W : Subgroup G := omegaOneCenterOf (jAtLeast m q S) with hW
  set Wt : Subgroup G := omegaOneCenterOf (jAtLeast m q (Q2 L1 L2 S)) with hWt
  have hWe : IsElemAbelian 2 W := by
    rw [hW]
    exact SmithC27.isElemAbelian_omegaOneCenterOf _
  have hWte : IsElemAbelian 2 Wt := by
    rw [hWt]
    exact SmithC27.isElemAbelian_omegaOneCenterOf _
  have hWS : W ≤ S := by
    rw [hW]
    exact (A4.omegaOneCenterOf_le _).trans (jAtLeast_le m q S)
  have hWtQ2 : Wt ≤ Q2 L1 L2 S := by
    rw [hWt]
    exact (A4.omegaOneCenterOf_le _).trans (jAtLeast_le m q (Q2 L1 L2 S))
  have hWcJ : W ≤ Subgroup.centralizer (jAtLeast m q S : Set G) := by
    rw [hW]
    exact (A4.omegaOneCenterOf_le_centerOf _).trans (A4.centerOf_le_centralizer _)
  have hWtcJ2 : Wt ≤ Subgroup.centralizer (jAtLeast m q (Q2 L1 L2 S) : Set G) := by
    rw [hWt]
    exact (A4.omegaOneCenterOf_le_centerOf _).trans (A4.centerOf_le_centralizer _)
  have hWP1 : P1 L1 L2 S ≤ Subgroup.normalizer (W : Set G) := by
    rw [hW, ← hJQ1]
    exact (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
      ((normalizer_le_normalizer_jAtLeast m q (Q1 L1 L2 S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf _))
  have hWtP2 : P2 L1 L2 S ≤ Subgroup.normalizer (Wt : Set G) := by
    rw [hWt]
    exact (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      ((normalizer_le_normalizer_jAtLeast m q (Q2 L1 L2 S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf _))
  have hSNW : S ≤ Subgroup.normalizer (W : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans hWP1
  have hBNW : bigB L1 L2 S ≤ Subgroup.normalizer (W : Set G) := by
    rw [hW]
    exact hB.trans ((normalizer_le_normalizer_jAtLeast m q S).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _))
  have hL2P2 : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hWtN : L2 ⊔ S ≤ Subgroup.normalizer (Wt : Set G) := hL2P2.trans hWtP2
  have hWleA : ∀ A : Subgroup G, IsMaxElemAbelian S A → W ≤ A := by
    intro A hA
    have hcardA : Nat.card A = m := by
      have h := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
      rw [pow_zero, mul_one] at h
      rw [hm, CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two S]
      exact h
    have hAJ : A ≤ jAtLeast m q S :=
      le_jAtLeast hA.1 hA.2.1 (by rw [hcardA]; exact Nat.le_mul_of_pos_left _ hqpos)
    have hZcA : W ≤ Subgroup.centralizer (A : Set G) :=
      hWcJ.trans (Subgroup.centralizer_le hAJ)
    have hsup : IsElemAbelian 2 (W ⊔ A) :=
      IsElemAbelian.sup_of_commute hWe hA.2.1
        (fun z hz a ha' => (Subgroup.mem_centralizer_iff.mp (hZcA hz) a ha').symm)
    have hcard : Nat.card ↥(W ⊔ A) ≤ Nat.card A :=
      hA.2.2 (W ⊔ A) (sup_le hWS hA.1) hsup
    have hZA : A = W ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
    rw [hZA]
    exact le_sup_left
  have hAinfJ : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      A ⊓ Q2 L1 L2 S ≤ jAtLeast m q (Q2 L1 L2 S) := by
    intro A hA
    have hcardA : Nat.card A = m := by
      have h := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
      rw [pow_zero, mul_one] at h
      rw [hm, CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two S]
      exact h
    have hrel : (A ⊓ Q2 L1 L2 S).relIndex A ≤ q := by
      have h := relIndex_inf_pCoreOf_le_two_pow hm2 hL2sup
        (hA.1.trans le_sup_right) hA.2.1
      rwa [hpCore2] at h
    have hmul : m ≤ q * Nat.card ↥(A ⊓ Q2 L1 L2 S) := by
      have hcard := Subgroup.relIndex_mul_card (A ⊓ Q2 L1 L2 S) A
      rw [inf_comm (A ⊓ Q2 L1 L2 S) A,
        inf_eq_right.mpr (inf_le_left : A ⊓ Q2 L1 L2 S ≤ A)] at hcard
      calc m = Nat.card A := hcardA.symm
        _ = (A ⊓ Q2 L1 L2 S).relIndex A * Nat.card ↥(A ⊓ Q2 L1 L2 S) := hcard.symm
        _ ≤ q * Nat.card ↥(A ⊓ Q2 L1 L2 S) := Nat.mul_le_mul_right _ hrel
    exact le_jAtLeast inf_le_right (IsElemAbelian.mono hA.2.1 inf_le_left) hmul
  have hWcapWt : W ⊓ Q2 L1 L2 S ≤ Wt := by
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
    intro x hx
    obtain ⟨hxW, hxQ2⟩ := Subgroup.mem_inf.mp hx
    have hxJ2 : x ∈ jAtLeast m q (Q2 L1 L2 S) :=
      hAinfJ A₀ hA₀ ⟨hWleA A₀ hA₀ hxW, hxQ2⟩
    rw [hWt]
    exact mem_omegaOneCenterOf hxJ2 (fun z hz => Subgroup.mem_centralizer_iff.mp
      (hWcJ hxW) z (jAtLeast_mono hQ2S hz)) (hWe.2 x hxW)
  have hZ1J : Z1 L1 L2 S ≤ jAtLeast m q S := by
    have hth : thompsonJ S ≤ jAtLeast m q S := by
      rw [hm, CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two S]
      exact thompsonJ_le_jAtLeast hq1 S
    exact (z1_le_omegaOneCenterOf_thompsonJ_of_caseII hF hB hB1 hII).trans
      ((A4.omegaOneCenterOf_le (thompsonJ S)).trans hth)
  have hZ1W : Z1 L1 L2 S ≤ W := by
    intro z hz
    rw [hW]
    refine mem_omegaOneCenterOf (hZ1J hz) (fun y hy => ?_)
      ((SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).2 z hz)
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.le_centralizer_iff.mp (Q1_le_centralizer_Z1 L1 L2 S) hz) y (hJ' hy)
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    intro hbot
    have hle := omegaOneCenterOf_S_le_caseII hF.1 hS1 hS2
    have hzero : omegaOneCenterOf S ≤ ⊥ := by
      refine hle.trans ?_
      rw [hbot, bot_inf_eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1 (le_bot_iff.mp hzero)
  obtain ⟨A, hA, hAnQ2⟩ : ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q2 L1 L2 S := by
    by_contra hcon
    push Not at hcon
    exact not_thompsonJ_le_Q2_of_caseII hF hB hB1 hII (iSup₂_le fun B hB' => hcon B hB')
  have hAH : A ≤ L2 ⊔ S := hA.1.trans le_sup_right
  have hAnR : ¬ A ≤ pCoreOf 2 (L2 ⊔ S) := by
    rw [hpCore2]
    exact hAnQ2
  have hcommTR : ⁅Wt, A ⊓ Q2 L1 L2 S⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (hWtcJ2 hw) a (hAinfJ A hA ha)
  obtain ⟨hTR1, hTR2, hTReq⟩ := thompsonReplacement hQ2S hWtQ2 hWte hA hcommTR
  have hbound : (Wt ⊓ Subgroup.centralizer (A : Set G)).relIndex Wt ≤
      (A ⊓ pCoreOf 2 (L2 ⊔ S)).relIndex A := by
    rw [hpCore2]
    exact hTR1.trans hTR2
  obtain ⟨c, hser⟩ : ∃ c : ℕ, IsChiefSeriesFrom (L2 ⊔ S) Wt Wt c :=
    D15Proof.exists_isChiefSeriesFrom Wt
      ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hWtN hg) x).mp hx⟩
  have hc1 : c ≤ 1 :=
    lemmaFF2_c_le_one hm2 hL2sup hWte (hWtQ2.trans (hQ2S.trans le_sup_right)) hA.2.1 hAH
      hAnR hbound hser
  interval_cases c
  ·
    have hzero : ⁅Wt, oTwoUpper (L2 ⊔ S)⁆ = ⊥ := lemmaFF2_zero hWte hser rfl
    have hO2Wt : oTwoUpper (L2 ⊔ S) ≤ Subgroup.centralizer (Wt : Set G) := by
      rw [Subgroup.commutator_comm] at hzero
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero
    by_cases hWQ2 : W ≤ Q2 L1 L2 S
    ·
      have hWWt : W ≤ Wt := (le_inf le_rfl hWQ2).trans hWcapWt
      have hO2W : oTwoUpper (L2 ⊔ S) ≤ Subgroup.centralizer (W : Set G) :=
        hO2Wt.trans (Subgroup.centralizer_le hWWt)
      have hL2SNW : L2 ⊔ S ≤ Subgroup.normalizer (W : Set G) := by
        rw [eq_oTwoUpper_sup_of_isSylowTwoOf (isSylowTwoOf_sup_Q2 hF.1 hS2)]
        exact sup_le (hO2W.trans (Subgroup.centralizer_le_normalizer (W : Set G))) hSNW
      have hP2NW : P2 L1 L2 S ≤ Subgroup.normalizer (W : Set G) :=
        sup_le (le_sup_left.trans hL2SNW) hBNW
      have hG0NW : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (W : Set G) := by
        rw [← F1.parabolic_sup_parabolic L1 L2 S]
        exact sup_le hWP1 hP2NW
      have hWleO : W ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
        le_pCoreOf_of_le_normalizer 2 (hWS.trans le_sup_right) hG0NW
          (hF.1.h1.pgroup.to_le hWS)
      rw [hF.1.o2] at hWleO
      exact hZ1ne (le_bot_iff.mp (hZ1W.trans hWleO))
    ·
      obtain ⟨s, hsW, hsQ⟩ : ∃ s : G, s ∈ W ∧ s ∉ Q2 L1 L2 S := by
        by_contra hcon
        push Not at hcon
        exact hWQ2 fun x hx => hcon x hx
      have hsS : s ∈ S := hWS hsW
      have hsP2 : s ∈ P2 L1 L2 S := hL2P2 ((le_sup_right : S ≤ L2 ⊔ S) hsS)
      have hNQ2 : s ∈ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
        le_normalizer_pCoreOf 2 (P2 L1 L2 S) hsP2
      have hc : ∀ x ∈ Q2 L1 L2 S, x * s * x⁻¹ * s⁻¹ ∈ Wt := by
        intro x hx
        have hconjW : x * s * x⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hSNW (hQ2S hx)) s).mp hsW
        have hcomW : x * s * x⁻¹ * s⁻¹ ∈ W := W.mul_mem hconjW (W.inv_mem hsW)
        have hconjQ : s * x * s⁻¹ ∈ Q2 L1 L2 S :=
          (Subgroup.mem_normalizer_iff.mp hNQ2 x).mp hx
        have hmul : s * x * s⁻¹ * x⁻¹ ∈ Q2 L1 L2 S :=
          (Q2 L1 L2 S).mul_mem hconjQ ((Q2 L1 L2 S).inv_mem hx)
        have heq : x * s * x⁻¹ * s⁻¹ = (s * x * s⁻¹ * x⁻¹)⁻¹ := by group
        have hcomQ : x * s * x⁻¹ * s⁻¹ ∈ Q2 L1 L2 S := by
          rw [heq]
          exact (Q2 L1 L2 S).inv_mem hmul
        exact hWcapWt (Subgroup.mem_inf.mpr ⟨hcomW, hcomQ⟩)
      exact false_of_commutator_le_of_isL2 hF.1 hS2 hm2 hL2 hWtQ2 hWtN hzero hsS hsQ hc
  ·
    obtain ⟨_, _, _, _, hAeq, hVeq, _⟩ :=
      lemmaFF2_one_numeric hm2 hL2sup hWte (hWtQ2.trans (hQ2S.trans le_sup_right)) hA.2.1
        hAH hAnR hbound hser
    have hAeqQ : (A ⊓ Q2 L1 L2 S).relIndex A = q := by
      rw [hq, ← hAeq, hpCore2]
    have hVeqQ : (Wt ⊓ Subgroup.centralizer (A : Set G)).relIndex Wt = q := by
      rw [hq, ← hVeq]
    have hWtAq : (Wt ⊓ A).relIndex Wt = q := by
      refine le_antisymm ?_ ?_
      · exact hTR2.trans (le_of_eq hAeqQ)
      · exact (le_of_eq hVeqQ.symm).trans hTR1
    have hAstar : IsMaxElemAbelian S (Wt ⊔ (A ⊓ Q2 L1 L2 S)) :=
      hTReq.mp (hWtAq.trans hAeqQ.symm)
    have hZ1Q2 : Z1 L1 L2 S ≤ Q2 L1 L2 S :=
      (Z1_le_maxElemAbelian_of_caseII hF hB hB1 hII hAstar).trans
        (sup_le hWtQ2 inf_le_right)
    set U : Subgroup G := conjClosure (Z1 L1 L2 S) (L2 ⊔ S) with hU
    have hUleWt : U ≤ Wt := by
      rw [hU]
      exact conjClosure_le fun g hg z hz =>
        (Subgroup.mem_normalizer_iff.mp (hWtN hg) z).mp (hWcapWt ⟨hZ1W hz, hZ1Q2 hz⟩)
    have hUtS : U ≤ S := hUleWt.trans (hWtQ2.trans hQ2S)
    have hU2 : IsPGroup 2 U := hF.1.h1.pgroup.to_le hUtS
    have hUH : U ≤ L2 ⊔ S := by
      rw [hU]
      exact conjClosure_le fun g hg z hz =>
        (L2 ⊔ S).mul_mem ((L2 ⊔ S).mul_mem hg ((le_sup_right : S ≤ L2 ⊔ S) (hQ2S (hZ1Q2 hz))))
          ((L2 ⊔ S).inv_mem hg)
    have hUN : L2 ⊔ S ≤ Subgroup.normalizer (U : Set G) := by
      rw [hU]
      exact le_normalizer_conjClosure _ _
    obtain ⟨c', hser'⟩ : ∃ c' : ℕ, IsChiefSeriesFrom (L2 ⊔ S) U U c' :=
      D15Proof.exists_isChiefSeriesFrom U
        ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hUN hg) x).mp hx⟩
    obtain ⟨t, htA, htQ⟩ : ∃ t : G, t ∈ A ∧ t ∉ Q2 L1 L2 S := by
      by_contra hcon
      push Not at hcon
      exact hAnQ2 fun x hx => hcon x hx
    have htH : t ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) (hA.1 htA)
    have ht2 : t * t ∈ pCoreOf 2 (L2 ⊔ S) := by
      have hsq : t * t = 1 := by
        rw [← pow_two]
        exact hA.2.1.2 t htA
      rw [hpCore2, hsq]
      exact (Q2 L1 L2 S).one_mem
    have htO : t ∉ pCoreOf 2 (L2 ⊔ S) := by
      rw [hpCore2]
      exact htQ
    have hM6 := l2_pow_sq_le_relIndex_centralizer hm2 hL2sup hU2 hUH hser' htH ht2 htO
    have hmono1 : (U ⊓ Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex U ≤
        (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U :=
      Subgroup.relIndex_le_of_le_left
        (inf_le_inf_left _ (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr htA)))
        (D15Proof.relIndex_ne_zero _ _)
    have hmono2 : (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U ≤
        (Wt ⊓ Subgroup.centralizer (A : Set G)).relIndex Wt := by
      rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]
      exact Subgroup.relIndex_le_of_le_right hUleWt Subgroup.index_ne_zero_of_finite
    have hboundU : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        U ≤ q := by
      rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G)) U, inf_comm]
      exact hmono1.trans (hmono2.trans (le_of_eq hVeqQ))
    have hc'1 : c' ≤ 1 := by
      have hmain : (2 ^ (2 * a + 1)) ^ c' ≤ 2 ^ (2 * a + 1) := by
        rw [hq] at hboundU
        exact hM6.trans hboundU
      by_contra hcon
      have h2 : 2 ≤ c' := by omega
      have hle : (2 ^ (2 * a + 1)) ^ 2 ≤ (2 ^ (2 * a + 1)) ^ c' :=
        Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num)) h2
      have hlt : 2 ^ (2 * a + 1) < (2 ^ (2 * a + 1)) ^ 2 := by
        calc 2 ^ (2 * a + 1) = (2 ^ (2 * a + 1)) ^ 1 := (pow_one _).symm
          _ < (2 ^ (2 * a + 1)) ^ 2 :=
              Nat.pow_lt_pow_right (by rw [← hq]; omega) (by norm_num)
      exact absurd (hle.trans hmain) (not_le.mpr hlt)
    rw [hU] at hser'
    exact no_chiefSeries_le_one_U_of_caseII hF hB ha hSz hL2 hII hZ1Q2 hZ2 hser' hc'1

end CFSG.Quasithin.Stroth

end
