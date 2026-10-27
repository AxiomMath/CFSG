module

public import CFSG.Quasithin.Recognition.Stroth.BenderQrcHyp
public import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
public import CFSG.Quasithin.Background.Harris.R1.Q8Ker
public import CFSG.Quasithin.H13.A5W1618g
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeC2Z
public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.Stroth.BenderOmega
public import CFSG.Quasithin.Recognition.Stroth.BenderSylow

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {m : ℕ}

theorem sup_eq_of_S_eq {L1 L2 S : Subgroup G}
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
  have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := congrArg (fun X => L1 ⊔ X) hS1
  rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]

theorem sup_eq_of_S_eq_right {L1 L2 S : Subgroup G}
    (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S) : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
  have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
  rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]

theorem exists_isSzU3Quot_sup_of_bender
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1) :
    ∃ q, IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) q := by
  obtain ⟨q, hq⟩ := exists_isSzU3Quot hB1
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  refine ⟨q, ?_⟩
  rw [sup_eq_of_S_eq hS1]
  exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF.1) hq

theorem le_normalizer_thompsonJ_of_not_le_centralizer
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hsyl : IsSylowTwoOf S (L1 ⊔ Q1 L1 L2 S) := isSylowTwoOf_sup_pCoreOf hF.1 hS1
  obtain ⟨q, hq⟩ := exists_isSzU3Quot_sup_of_bender hF hB hB1
  have hq' : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S)) q := hsup1 ▸ hq
  have hX : (∃ a : ℕ, 1 ≤ a ∧ Nonempty (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃* Sz a)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = (2 ^ n) ^ 2 ∧
        (Nonempty (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃* StatedSU 3 (2 ^ n) F) ∨
          Nonempty (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃*
            StatedProj (StatedSU 3 (2 ^ n) F)))) := by
    rcases hq' with ⟨a, ha, -, he⟩ | ⟨n, hn, -, F, hFld, hFin, hcard, he⟩
    · exact Or.inl ⟨a, ha, he⟩
    · exact Or.inr ⟨n, hn, F, hFld, hFin, hcard, he⟩
  have hdich := le_centralizer_or_le_normalizer_thompsonJ hX hsyl
  rw [pCoreOf_sup_pCoreOf hF.1] at hdich
  exact hdich.resolve_left (by simpa [Z1] using hII)

theorem isSimpleGroup_oTwoQuot_sup_right_of_isL2Quot
    (hF : Hyp111 L1 L2 S) (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S) {m : ℕ} (hm : 2 ≤ m)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2)) :
    IsSimpleGroup (oTwoQuot ↥(L2 ⊔ S)) := by
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hQ12 : L2 ⊔ Q1 L2 L1 S = L2 ⊔ Q2 L1 L2 S := by
    rw [Q1, Q2, P1, P2, bigB_comm]
  have hL2sup : IsL2Quot m (oTwoQuot ↥(L2 ⊔ S)) := by
    obtain ⟨eL2⟩ := hL2
    rw [hsup2, ← hQ12]
    exact ⟨(oTwoQuotSupEquiv hF.symm).trans eL2⟩
  exact CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot hm hL2sup

theorem inf_centralizer_pCoreOf_left_of_hyp111 (hF : Hyp111 L1 L2 S) :
    (L1 ⊔ S) ⊓ Subgroup.centralizer (Q1 L1 L2 S : Set G) ≤ Q1 L1 L2 S := by
  have hchar : CharTwo (P1 L1 L2 S) := by
    rw [P1, F1.parabolic_eq]
    exact hF.h1.charTwo
  have hHle : L1 ⊔ S ≤ P1 L1 L2 S := by
    rw [P1, bigB]
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  exact (inf_le_inf_right (Subgroup.centralizer (Q1 L1 L2 S : Set G)) hHle).trans hchar

theorem inf_centralizer_pCoreOf_right_of_hyp111 (hF : Hyp111 L1 L2 S) :
    (L2 ⊔ S) ⊓ Subgroup.centralizer (Q2 L1 L2 S : Set G) ≤ Q2 L1 L2 S := by
  have hchar : CharTwo (P2 L1 L2 S) := by
    rw [P2, ← bigB_comm L1 L2 S, F1.parabolic_eq]
    exact hF.h2.charTwo
  have hHle : L2 ⊔ S ≤ P2 L1 L2 S := by
    rw [P2, bigB]
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  exact (inf_le_inf_right (Subgroup.centralizer (Q2 L1 L2 S : Set G)) hHle).trans hchar

theorem thompsonJ_le_Q1_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    thompsonJ S ≤ Q1 L1 L2 S := by
  have hN : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    le_normalizer_thompsonJ_of_not_le_centralizer hF hB hB1 hII
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    sup_le ((le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S).trans hN)
      (hB.trans (normalizer_le_normalizer_thompsonJ S))
  exact le_pCoreOf_of_le_normalizer 2
    ((thompsonJ_le_self S).trans
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) hP1N
    (hF.1.h1.pgroup.to_le (thompsonJ_le_self S))

theorem not_thompsonJ_le_Q2_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    ¬ thompsonJ S ≤ Q2 L1 L2 S := by
  have hJQ1 : thompsonJ S ≤ Q1 L1 L2 S := thompsonJ_le_Q1_of_caseII hF hB hB1 hII
  intro hJQ2
  have hQ2S : Q2 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le
      (F112W.isSylowTwoOf_parabolic' (Hyp111R.of_hyp111 rankOneListedFacts hF.1))
  have hJeq : thompsonJ S = thompsonJ (Q2 L1 L2 S) := by
    simpa using (thompsonJ_eq_of_le (S := S) (R := Q2 L1 L2 S) hJQ2 hQ2S)
  have hJ2 : IsPGroup 2 (thompsonJ S) := hF.1.h1.pgroup.to_le (thompsonJ_le_self S)
  have hN : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    le_normalizer_thompsonJ_of_not_le_centralizer hF hB hB1 hII
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    sup_le ((le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S).trans hN)
      (hB.trans (normalizer_le_normalizer_thompsonJ S))
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    have hchar : ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)).Characteristic :=
      CFSG.QuasithinUnique.Setup.characteristic_thompsonJ (Q2 L1 L2 S)
    have hmap : ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)).map
        (Q2 L1 L2 S).subtype = thompsonJ S := by
      rw [Subgroup.map_subgroupOf_eq_of_le (thompsonJ_le_self (Q2 L1 L2 S))]
      exact hJeq.symm
    have h := (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (normalizer_le_normalizer_map_of_characteristic
        ((thompsonJ (Q2 L1 L2 S)).subgroupOf (Q2 L1 L2 S)))
    rwa [hmap] at h
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (thompsonJ S : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le hP1N hP2N
  have hJleO : thompsonJ S ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 ((thompsonJ_le_self S).trans le_sup_right) hG0N hJ2
  rw [hF.1.o2] at hJleO
  have hSne : S ≠ ⊥ := by
    intro hS
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
      (le_bot_iff.mp (by simpa [hS] using omegaOneCenterOf_le S))
  exact CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hF.1.h1.pgroup hSne
    (le_bot_iff.mp hJleO)

theorem Z1_le_centralizer_Q1 (L1 L2 S : Subgroup G) :
    Z1 L1 L2 S ≤ Subgroup.centralizer (Q1 L1 L2 S : Set G) :=
  (A4.omegaOneCenterOf_le_centerOf (Q1 L1 L2 S)).trans
    (A4.centerOf_le_centralizer (Q1 L1 L2 S))

theorem Q1_le_centralizer_Z1 (L1 L2 S : Subgroup G) :
    Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  simpa [Z1, omegaOneCenterOf_eq] using
    CFSG.Quasithin.H13.A5.T_le_centralizer_omegaOneCenter (Q1 L1 L2 S)

theorem Z1_le_maxElemAbelian_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) : Z1 L1 L2 S ≤ A := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hJQ1 : thompsonJ S ≤ Q1 L1 L2 S := thompsonJ_le_Q1_of_caseII hF hB hB1 hII
  have hAQ1 : A ≤ Q1 L1 L2 S := (le_iSup₂_of_le A hA le_rfl).trans hJQ1
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZ1S : Z1 L1 L2 S ≤ S := (omegaOneCenterOf_le (Q1 L1 L2 S)).trans hQ1S
  have hZ1ea : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hcomm : ∀ z ∈ Z1 L1 L2 S, ∀ a ∈ A, z * a = a * z := by
    intro z hz a ha'
    exact (Subgroup.mem_centralizer_iff.mp (Z1_le_centralizer_Q1 L1 L2 S hz) a
      (hAQ1 ha')).symm
  have hsup_ea : IsElemAbelian 2 (Z1 L1 L2 S ⊔ A) :=
    IsElemAbelian.sup_of_commute hZ1ea hA.2.1 hcomm
  have hsupS : Z1 L1 L2 S ⊔ A ≤ S := sup_le hZ1S hA.1
  have hcard : Nat.card (Z1 L1 L2 S ⊔ A : Subgroup G) ≤ Nat.card (A : Subgroup G) :=
    hA.2.2 (B := Z1 L1 L2 S ⊔ A) hsupS hsup_ea
  have hsup_eq : A = Z1 L1 L2 S ⊔ A :=
    Subgroup.eq_of_le_of_card_ge le_sup_right hcard
  rw [hsup_eq]
  exact le_sup_left

theorem z1_le_omegaOneCenterOf_thompsonJ_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S ≤ omegaOneCenterOf (thompsonJ S) := by
  have hJQ1 : thompsonJ S ≤ Q1 L1 L2 S := thompsonJ_le_Q1_of_caseII hF hB hB1 hII
  have hJcent : thompsonJ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
    rw [thompsonJ]
    refine iSup₂_le fun A hA => ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzQ1 : z ∈ Q1 L1 L2 S := omegaOneCenterOf_le (Q1 L1 L2 S) hz
    have hzC : z ∈ Subgroup.centralizer (Q1 L1 L2 S : Set G) :=
      Z1_le_centralizer_Q1 L1 L2 S hz
    have haQ1 : a ∈ Q1 L1 L2 S :=
      hJQ1 ((le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ S) ha)
    exact (Subgroup.mem_centralizer_iff.mp hzC a haQ1).symm
  have hZ1CJ : Z1 L1 L2 S ≤ Subgroup.centralizer (thompsonJ S : Set G) :=
    Subgroup.le_centralizer_iff.mpr hJcent
  have hZ1J : Z1 L1 L2 S ≤ thompsonJ S := by
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
    exact (Z1_le_maxElemAbelian_of_caseII hF hB hB1 hII hA₀).trans
      (le_iSup₂_of_le A₀ hA₀ le_rfl)
  intro z hz
  have hzJ : z ∈ thompsonJ S := hZ1J hz
  have hz2 : z ^ 2 = 1 := (SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)).2 z hz
  exact Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hzJ, hZ1CJ hz⟩, hz2⟩

theorem omegaOneCenterOf_S_le_caseII (hF : Hyp111 L1 L2 S)
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S)
    (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S) :
    omegaOneCenterOf S ≤ Z1 L1 L2 S ⊓ Z2 L1 L2 S := by
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  refine le_inf ?_ ?_
  · rw [omegaOneCenterOf]
    refine Subgroup.closure_mono ?_
    rintro x ⟨hxZ, hx2⟩
    have hxS : x ∈ S := (Subgroup.mem_inf.mp hxZ).1
    have hxC : x ∈ Subgroup.centralizer (S : Set G) := (Subgroup.mem_inf.mp hxZ).2
    have hxCQ1 : x ∈ Subgroup.centralizer (Q1 L1 L2 S : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro q hq
      exact hxC q (hQ1S hq)
    have hxH1 : x ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) hxS
    have hxQ1 : x ∈ Q1 L1 L2 S :=
      inf_centralizer_pCoreOf_left_of_hyp111 hF ⟨hxH1, hxCQ1⟩
    exact ⟨Subgroup.mem_inf.mpr ⟨hxQ1, hxCQ1⟩, hx2⟩
  · rw [omegaOneCenterOf]
    refine Subgroup.closure_mono ?_
    rintro x ⟨hxZ, hx2⟩
    have hxS : x ∈ S := (Subgroup.mem_inf.mp hxZ).1
    have hxC : x ∈ Subgroup.centralizer (S : Set G) := (Subgroup.mem_inf.mp hxZ).2
    have hxCQ2 : x ∈ Subgroup.centralizer (Q2 L1 L2 S : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro q hq
      exact hxC q (hQ2S hq)
    have hxP2 : x ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) hxS
    have hxQ2 : x ∈ Q2 L1 L2 S :=
      inf_centralizer_pCoreOf_right_of_hyp111 hF ⟨hxP2, hxCQ2⟩
    exact ⟨Subgroup.mem_inf.mpr ⟨hxQ2, hxCQ2⟩, hx2⟩

theorem inf_centralizer_z1_eq_q1_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hsup : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  obtain ⟨q, hq⟩ := exists_isSzU3Quot_sup_of_bender hF hB hB1
  have hq' : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S)) q := hsup ▸ hq
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hSle : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hS1
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  set H : Subgroup G := L1 ⊔ Q1 L1 L2 S with hH
  set K : Subgroup G := H ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) with hK
  have hKH : K ≤ H := inf_le_left
  have hQ1K : Q1 L1 L2 S ≤ K :=
    le_inf le_sup_right (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S))
  have hHP1 : H ≤ P1 L1 L2 S := sup_le le_sup_left (pCoreOf_le 2 (P1 L1 L2 S))
  have hHnormZ1 : H ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hHP1.trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S))
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
      ((F7.normalizer_le_normalizer_centralizer (Z1 L1 L2 S)) (hHnormZ1 hx))
  have hpCoreH : pCoreOf 2 H = Q1 L1 L2 S := by
    rw [hH]
    exact pCoreOf_sup_pCoreOf hF.1
  rcases eq_or_mem_pCoreOf_of_normal hq' hKH hKn (by rw [hpCoreH]; exact hQ1K) with
    htop | h2el
  · exfalso
    refine hII ?_
    have hHC : H ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := htop.symm ▸ inf_le_right
    exact hH.symm ▸ hHC
  · refine le_antisymm ?_ (le_inf hQ1S
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S)))
    intro x hx
    have hxS : x ∈ S := (Subgroup.mem_inf.mp hx).1
    have hxC : x ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxK : x ∈ K := Subgroup.mem_inf.mpr ⟨hSle hxS, hxC⟩
    obtain ⟨n, hn⟩ := hF.1.h1.pgroup ⟨x, hxS⟩
    have hxQ : x ∈ pCoreOf 2 H := h2el x hxK ⟨n, by simpa using congrArg Subtype.val hn⟩
    rwa [hpCoreH] at hxQ

theorem baum_le_Q1_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    baum S ≤ Q1 L1 L2 S := by
  have hZ1W : Z1 L1 L2 S ≤ omegaOneCenterOf (thompsonJ S) :=
    z1_le_omegaOneCenterOf_thompsonJ_of_caseII hF hB hB1 hII
  have hC : Subgroup.centralizer (omegaOneCenterOf (thompsonJ S) : Set G) ≤
      Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    Subgroup.centralizer_le hZ1W
  calc baum S = S ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJ S) : Set G) := rfl
    _ ≤ S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) := inf_le_inf_left S hC
    _ = Q1 L1 L2 S := inf_centralizer_z1_eq_q1_of_caseII hF hB hB1 hII

theorem P1_le_normalizer_baum_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    P1 L1 L2 S ≤ Subgroup.normalizer (baum S : Set G) := by
  have hbaum : baum S ≤ Q1 L1 L2 S := baum_le_Q1_of_caseII hF hB hB1 hII
  have hN : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    le_normalizer_thompsonJ_of_not_le_centralizer hF hB hB1 hII
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    sup_le ((le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S).trans hN)
      (hB.trans (normalizer_le_normalizer_thompsonJ S))
  have hP1W : P1 L1 L2 S ≤
      Subgroup.normalizer (omegaOneCenterOf (thompsonJ S) : Set G) :=
    hP1N.trans (A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ S))
  have hP1C : P1 L1 L2 S ≤ Subgroup.normalizer
      (Subgroup.centralizer (omegaOneCenterOf (thompsonJ S) : Set G) : Set G) :=
    hP1W.trans (F7.normalizer_le_normalizer_centralizer (omegaOneCenterOf (thompsonJ S)))
  have hP1Q1 : P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P1 L1 L2 S)
  have hQ1S : Q1 L1 L2 S ≤ S := by
    have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hbaumEq : baum S =
      Q1 L1 L2 S ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJ S) : Set G) := by
    rw [baum]
    refine le_antisymm (le_inf hbaum inf_le_right) (inf_le_inf hQ1S le_rfl)
  rw [hbaumEq]
  intro x hx
  exact A4.mem_normalizer_inf (hP1Q1 hx) (hP1C hx)

theorem isTwoReducedIn_z1_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    IsTwoReducedIn (L1 ⊔ S) (Z1 L1 L2 S) := by
  classical
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZ1S : Z1 L1 L2 S ≤ S := (omegaOneCenterOf_le (Q1 L1 L2 S)).trans hQ1S
  have hZ1ea : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hHnorm : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hHleP1.trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S))
  obtain ⟨q, hq⟩ := exists_isSzU3Quot_sup_of_bender hF hB hB1
  refine ⟨hZ1S.trans le_sup_right, hHnorm, hZ1ea, ?_⟩
  intro D hDH hDN hD
  set C : Subgroup G := (L1 ⊔ S) ⊓
    Subgroup.centralizer (Z1 L1 L2 S : Set G) with hC
  have hCH : C ≤ L1 ⊔ S := inf_le_left
  have hCn : L1 ⊔ S ≤ Subgroup.normalizer (C : Set G) := by
    intro x hx
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
      ((F7.normalizer_le_normalizer_centralizer (Z1 L1 L2 S)) (hHnorm hx))
  have hQ1C : Q1 L1 L2 S ≤ C :=
    le_inf (hQ1S.trans le_sup_right)
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S))
  set K : Subgroup G := D ⊔ C with hK
  have hKH : K ≤ L1 ⊔ S := sup_le hDH hCH
  have hQ1K : Q1 L1 L2 S ≤ K := hQ1C.trans le_sup_right
  have hKn : L1 ⊔ S ≤ Subgroup.normalizer (K : Set G) := by
    rw [hK]
    exact F1.le_normalizer_sup hDN hCn
  have hD' : ∀ d ∈ D, ∃ n : ℕ, d ^ (2 ^ n) ∈ C := by
    intro d hd
    obtain ⟨m, hm⟩ := hD d hd
    refine ⟨m, ?_⟩
    rw [hC]
    exact Subgroup.mem_inf.mpr ⟨hDH (D.pow_mem hd _), hm⟩
  rcases eq_or_mem_pCoreOf_of_normal hq hKH hKn
    (by rw [hpCore1]; exact hQ1K) with htop | h2el
  · exfalso
    have h2 : ∀ x ∈ L1 ⊔ S, ∃ m : ℕ, x ^ (2 ^ m) ∈ C :=
      exists_pow_mem_of_sup_eq_of_normalizes hCH hCn hDN htop hD'
    have hCe : C = L1 ⊔ S :=
      eq_of_forall_pow_mem hq hCH hCn (by rw [hpCore1]; exact hQ1C) h2
    apply hII
    rw [← hsup1, ← hCe]
    exact inf_le_right
  · intro d hd
    obtain ⟨b, a, rfl, hbodd, ⟨k, hak⟩, hbz, haz⟩ :=
      CFSG.Quasithin.H13.exists_odd_two_decomp d
    have haD : a ∈ D := Subgroup.zpowers_le.mpr hd haz
    have hbD : b ∈ D := Subgroup.zpowers_le.mpr hd hbz
    have haK : a ∈ K := Subgroup.mem_sup_left haD
    have haQ : a ∈ Q1 L1 L2 S := by
      have := h2el a haK ⟨k, hak⟩
      rwa [hpCore1] at this
    have haC : a ∈ C := hQ1C haQ
    obtain ⟨j, hj⟩ := hD (b * a) hd
    have hdj : (b * a) ^ (2 ^ j) ∈ C := by
      rw [hC]
      exact Subgroup.mem_inf.mpr ⟨hDH (D.pow_mem hd _), hj⟩
    set d : G := b * a with hd
    have hbz' : b ∈ Subgroup.zpowers d := by simpa [hd] using hbz
    have haz' : a ∈ Subgroup.zpowers d := by simpa [hd] using haz
    have hcomm : Commute b a := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hbz'
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp haz'
      rw [← hi, ← hl]
      exact Commute.zpow_zpow_self d i l
    have hpow : (b * a) ^ (2 ^ j) = b ^ (2 ^ j) * a ^ (2 ^ j) :=
      hcomm.mul_pow (2 ^ j)
    have hapowC : a ^ (2 ^ j) ∈ C := C.pow_mem haC _
    have hbj : b ^ (2 ^ j) ∈ C := by
      have h1 : b ^ (2 ^ j) = (b * a) ^ (2 ^ j) * (a ^ (2 ^ j))⁻¹ := by
        rw [hpow]
        group
      rw [h1]
      exact C.mul_mem hdj (C.inv_mem hapowC)
    have hbC : b ∈ C := B2F.mem_of_odd_orderOf_of_pow_mem hbodd hbj
    exact (inf_le_right : C ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
      (C.mul_mem hbC haC)

theorem no_normal_d11Hyp
    (hF : F112HypW L1 L2 S) {N : Subgroup G} (hN : N ≤ pCoreOf 2 (L1 ⊔ S))
    (hNn : (N.subgroupOf ((L1 ⊔ S) ⊔ (L2 ⊔ S))).Normal) : N = ⊥ := by
  have hNH : N ≤ L1 ⊔ S := hN.trans (pCoreOf_le 2 (L1 ⊔ S))
  have hNG : N ≤ (L1 ⊔ S) ⊔ (L2 ⊔ S) := hNH.trans le_sup_left
  have hNGn : (L1 ⊔ S) ⊔ (L2 ⊔ S) ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNG).mp hNn
  have hNp : IsPGroup 2 N := (pCoreOf_isPGroup 2 (L1 ⊔ S)).to_le hN
  have hNle : N ≤ pCoreOf 2 ((L1 ⊔ S) ⊔ (L2 ⊔ S)) :=
    le_pCoreOf_of_le_normalizer 2 hNG hNGn hNp
  rw [show (L1 ⊔ S) ⊔ (L2 ⊔ S) = L1 ⊔ L2 ⊔ S by ac_rfl, hF.1.o2] at hNle
  exact le_bot_iff.mp hNle

theorem isSylowTwoOf_sup_Q2
    (hF : Hyp111 L1 L2 S) (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S) :
    IsSylowTwoOf S (L2 ⊔ S) := by
  rw [sup_eq_of_S_eq_right hS2]
  have hS2' : S = (S ⊓ L2) ⊔ Q1 L2 L1 S := by
    simpa [Q1, Q2, P1, P2, bigB_comm] using hS2
  have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.symm hS2'
  simpa [Q1, Q2, P1, P2, bigB_comm] using h

private theorem Z1_ne_bot_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S ≠ ⊥ := by
  intro hbot
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hle := omegaOneCenterOf_S_le_caseII hF.1 hS1 hS2
  have hinf : Z1 L1 L2 S ⊓ Z2 L1 L2 S = ⊥ := by rw [hbot, bot_inf_eq]
  exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
    (le_bot_iff.mp (hle.trans (le_of_eq hinf)))

theorem d11Hyp_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hm : 2 ≤ m)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    D11Hyp (L1 ⊔ S) (L2 ⊔ S) S (Z1 L1 L2 S) (borelOf L2 S ⊔ S) := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hsylow1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  exact
    { sylow₁ := hsylow1
      sylow₂ := isSylowTwoOf_sup_Q2 hF.1 hS2
      reduced := isTwoReducedIn_z1_of_caseII hF hB hB1 hII
      nontrivial := Z1_ne_bot_of_caseII hF hB hB1 hS2 hII
      unique_max := CFSG.Quasithin.H13.A5.isUniqueMaxOver_borelOf_sup
        (L := L2) (T := S) (Hyp111R.of_hyp111 rankOneListedFacts hF.1).r2
        hF.1.h2.normalizes
      centralizer := by
        rw [hpCore1]
        exact (inf_centralizer_z1_eq_q1_of_caseII hF hB hB1 hII).symm
      no_normal := fun N hN hNn => no_normal_d11Hyp hF hN hNn }

private theorem caseII_le_centralizer_of_commutator
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hm : 2 ≤ m)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hcomm : ⁅Z2 L1 L2 S, thompsonJ S⁆ = ⊥) :
    L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hpCoreH : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hHZ2 : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) := by
    refine ((sup_le le_sup_left
      ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right) :
        L2 ⊔ S ≤ P2 L1 L2 S)).trans ?_
    exact (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hKnorm : L2 ⊔ S ≤ Subgroup.normalizer
      (((L2 ⊔ S) ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) : Subgroup G) : Set G) := by
    intro x hx
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hx)
      ((hHZ2.trans (F7.normalizer_le_normalizer_centralizer (Z2 L1 L2 S))) hx)
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hQK : pCoreOf 2 (L2 ⊔ S) ≤
      (L2 ⊔ S) ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    rw [hpCoreH]
    exact le_inf (hQ2S.trans le_sup_right) hQ2C
  have hJK : thompsonJ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hJQ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S :=
    not_thompsonJ_le_Q2_of_caseII hF hB hB1 hII
  have hsimple : IsSimpleGroup (oTwoQuot ↥(L2 ⊔ S)) :=
    isSimpleGroup_oTwoQuot_sup_right_of_isL2Quot hF.1 hS2 hm hL2
  have hKH : (L2 ⊔ S) ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) ≤ L2 ⊔ S := inf_le_left
  have hKJ : thompsonJ S ≤
      (L2 ⊔ S) ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    le_inf ((thompsonJ_le_self S).trans le_sup_right) hJK
  have hKn : ∀ h ∈ L2 ⊔ S,
      ∀ x ∈ (L2 ⊔ S) ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G),
        h * x * h⁻¹ ∈ (L2 ⊔ S) ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    intro h hh x hx
    exact (Subgroup.mem_normalizer_iff.mp (hKnorm hh) x).mp hx
  have hKH_eq : (L2 ⊔ S) ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = L2 ⊔ S := by
    rcases CFSG.Quasithin.Background.Harris.R1.normal_eq_pCore_or_top hsimple hKH hKn
      (by simpa [hpCoreH] using hQK) with hK | hH
    · exfalso
      rw [hpCoreH] at hK
      exact hJQ2 (hK ▸ hKJ)
    · exact le_antisymm hKH hH
  calc L2 ⊔ Q2 L1 L2 S = L2 ⊔ S := hsup2.symm
    _ ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
        rw [← hKH_eq]
        exact inf_le_right

theorem caseII_split
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB1 : VSzBig L1 ∨ VU3Big L1)
    (hL2 : IsL2Quot m (oTwoQuot ↥L2)) (hm : 2 ≤ m)
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    ⁅Z2 L1 L2 S, thompsonJ S⁆ = ⊥ ↔
      L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
  constructor
  · intro hcomm
    exact caseII_le_centralizer_of_commutator hF hB hB1 hL2 hm hII hcomm
  · intro hH
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨m, hm, hL2⟩))
    have hSle : S ≤ L2 ⊔ Q2 L1 L2 S := by
      calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
        _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
    have hJH : thompsonJ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
      (thompsonJ_le_self S).trans (hSle.trans hH)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hJH

end CFSG.Quasithin.Stroth

end
