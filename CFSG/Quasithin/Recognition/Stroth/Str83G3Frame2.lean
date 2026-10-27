module

public import CFSG.Quasithin.Recognition.Stroth.Str83G3Frame
public import CFSG.Quasithin.Recognition.Stroth.BenderRleQ
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexM6
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

private theorem sup_eq_of_S_eq {L1 L2 S : Subgroup G}
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
  have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) :=
    congrArg (fun X => L1 ⊔ X) hS1
  rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]

theorem relIndex_inf_q1_le {L1 L2 S : Subgroup G} {q : ℕ}
    (hF : Hyp111 L1 L2 S) (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S)
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) {A : Subgroup G} (hAS : A ≤ S)
    (hA : ∀ a ∈ A, a ^ 2 ∈ Q1 L1 L2 S) :
    (A ⊓ Q1 L1 L2 S).relIndex A ≤ q := by
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF
  have hbender1 : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) q := by
    rw [hsup1]
    exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF) hq
  have hsylow : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF hS1
  have hle := relIndex_inf_pCoreOf_le hbender1 hsylow hAS
    (fun a ha => by rw [hpCore1]; exact hA a ha)
  rwa [hpCore1] at hle

theorem inf_le_jAtLeast_of_not_le_q1 {L1 L2 S : Subgroup G} {q : ℕ}
    (hF : Hyp111 L1 L2 S) (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S)
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    A ⊓ Q1 L1 L2 S ≤ jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S) := by
  have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 S := by
    have := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
    simpa using this
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAsq : ∀ a ∈ A, a ^ 2 ∈ Q1 L1 L2 S := by
    intro a ha
    rw [hAe.2 a ha]
    exact (Q1 L1 L2 S).one_mem
  have hrel : (A ⊓ Q1 L1 L2 S).relIndex A ≤ q :=
    relIndex_inf_q1_le hF hS1 hq hA.1 hAsq
  have hcard := Subgroup.relIndex_mul_card (A ⊓ Q1 L1 L2 S) A
  rw [inf_comm (A ⊓ Q1 L1 L2 S) A,
    inf_eq_right.mpr (inf_le_left : A ⊓ Q1 L1 L2 S ≤ A)] at hcard
  have hm : 2 ^ CFSG.Open.pRank 2 S ≤ q * Nat.card ↥(A ⊓ Q1 L1 L2 S) := by
    calc 2 ^ CFSG.Open.pRank 2 S = Nat.card A := hcardA.symm
      _ = (A ⊓ Q1 L1 L2 S).relIndex A * Nat.card ↥(A ⊓ Q1 L1 L2 S) := hcard.symm
      _ = Nat.card ↥(A ⊓ Q1 L1 L2 S) * (A ⊓ Q1 L1 L2 S).relIndex A := Nat.mul_comm _ _
      _ ≤ Nat.card ↥(A ⊓ Q1 L1 L2 S) * q := Nat.mul_le_mul_left _ hrel
      _ = q * Nat.card ↥(A ⊓ Q1 L1 L2 S) := Nat.mul_comm _ _
  exact le_jAtLeast inf_le_right (IsElemAbelian.mono hAe inf_le_left) hm

private theorem relIndex_centralizer_zTilde_le_q_of_not_le_q1
    {L1 L2 S : Subgroup G} {q : ℕ} (hF : Hyp111 L1 L2 S)
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) (hq : IsSzU3Quot (oTwoQuot ↥L1) q)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) {t : G} (htA : t ∈ A)
    (htQ : t ∉ Q1 L1 L2 S) :
    (zTilde L1 L2 S q ⊓ Subgroup.centralizer ({t} : Set G)).relIndex
      (zTilde L1 L2 S q) ≤ q := by
  have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 S := by
    have := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
    simpa using this
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZe : IsElemAbelian 2 (zTilde L1 L2 S q) :=
    SmithC27.isElemAbelian_omegaOneCenterOf _
  have hZS : zTilde L1 L2 S q ≤ S := (zTilde_le_pCoreOf L1 L2 S q).trans hQ1S
  have hZc : zTilde L1 L2 S q ≤
      Subgroup.centralizer (jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S) : Set G) :=
    (A4.omegaOneCenterOf_le_centerOf _).trans (A4.centerOf_le_centralizer _)
  have hAQ1J : A ⊓ Q1 L1 L2 S ≤ jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S) :=
    inf_le_jAtLeast_of_not_le_q1 hF hS1 hq hA
  have hCA : A ⊓ Q1 L1 L2 S ≤
      A ⊓ Subgroup.centralizer (zTilde L1 L2 S q : Set G) := by
    refine le_inf inf_le_left ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZc hz) x (hAQ1J hx)).symm
  have hR := relIndex_centralizer_le_mul (S := S) (V := zTilde L1 L2 S q)
    (F := A) (k := 1) hZe hZS hAe hA.1 (by rw [hcardA]; simp)
  have hR' : (zTilde L1 L2 S q ⊓ Subgroup.centralizer (A : Set G)).relIndex
      (zTilde L1 L2 S q) ≤
      1 * (A ⊓ Subgroup.centralizer (zTilde L1 L2 S q : Set G)).relIndex A := by
    rw [← Subgroup.inf_relIndex_left (H := zTilde L1 L2 S q)
        (K := Subgroup.centralizer (A : Set G)),
      ← Subgroup.inf_relIndex_left (H := A)
        (K := Subgroup.centralizer (zTilde L1 L2 S q : Set G))] at hR
    exact hR
  have hCArel : (A ⊓ Subgroup.centralizer (zTilde L1 L2 S q : Set G)).relIndex A ≤
      (A ⊓ Q1 L1 L2 S).relIndex A :=
    Subgroup.relIndex_le_of_le_left hCA (D15Proof.relIndex_ne_zero _ _)
  have hAsq : ∀ a ∈ A, a ^ 2 ∈ Q1 L1 L2 S := by
    intro a ha
    rw [hAe.2 a ha]
    exact (Q1 L1 L2 S).one_mem
  have hArel : (A ⊓ Q1 L1 L2 S).relIndex A ≤ q :=
    relIndex_inf_q1_le hF hS1 hq hA.1 hAsq
  have h1 : (zTilde L1 L2 S q ⊓ Subgroup.centralizer (A : Set G)).relIndex
      (zTilde L1 L2 S q) ≤ q := by
    calc (zTilde L1 L2 S q ⊓ Subgroup.centralizer (A : Set G)).relIndex
          (zTilde L1 L2 S q)
        ≤ 1 * (A ⊓ Subgroup.centralizer (zTilde L1 L2 S q : Set G)).relIndex A := hR'
      _ = (A ⊓ Subgroup.centralizer (zTilde L1 L2 S q : Set G)).relIndex A := one_mul _
      _ ≤ (A ⊓ Q1 L1 L2 S).relIndex A := hCArel
      _ ≤ q := hArel
  have hmono : (zTilde L1 L2 S q ⊓ Subgroup.centralizer ({t} : Set G)).relIndex
      (zTilde L1 L2 S q) ≤
      (zTilde L1 L2 S q ⊓ Subgroup.centralizer (A : Set G)).relIndex
        (zTilde L1 L2 S q) := by
    refine Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htA))
  exact hmono.trans h1

private theorem exists_maxElemAbelian_not_le_pCoreOf {L1 L2 S : Subgroup G}
    (hJ : ¬ thompsonJ S ≤ Q1 L1 L2 S) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q1 L1 L2 S := by
  by_contra hcon
  push Not at hcon
  exact hJ (by
    rw [thompsonJ]
    exact iSup₂_le fun A hA => hcon A hA)

theorem commutator_zTilde_oTwoUpper_of_not_le_q1
    {L1 L2 S : Subgroup G} {q : ℕ} (hF : Hyp111 L1 L2 S)
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S) (hq : IsSzU3Quot (oTwoQuot ↥L1) q)
    (hJ : ¬ thompsonJ S ≤ Q1 L1 L2 S) :
    ⁅zTilde L1 L2 S q, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
  classical
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF
  have hbender1 : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) q := by
    rw [hsup1]
    exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF) hq
  set H : Subgroup G := L1 ⊔ S with hH
  set Zt : Subgroup G := zTilde L1 L2 S q with hZt
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZe : IsElemAbelian 2 Zt := SmithC27.isElemAbelian_omegaOneCenterOf _
  have hHV : H ≤ Subgroup.normalizer (Zt : Set G) := by
    rw [hH, hZt]
    exact (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (normalizer_zTilde L1 L2 S q)
  have hq2 : 2 ≤ q := by
    have := IsSzU3Quot.four_le hq
    omega
  have hle : H ≤ (H ⊓ Subgroup.centralizer (Zt : Set G)) ⊔ Q1 L1 L2 S := by
    by_contra hnot
    obtain ⟨A, hA, hAQ1⟩ := exists_maxElemAbelian_not_le_pCoreOf hJ
    obtain ⟨t, htA, htQ⟩ : ∃ t, t ∈ A ∧ t ∉ Q1 L1 L2 S := by
      by_contra hcon
      push Not at hcon
      exact hAQ1 (fun x hx => hcon x hx)
    have ht2 : t * t = 1 := by simpa [pow_two] using hA.2.1.2 t htA
    have htH : t ∈ H := by
      rw [hH]
      exact (le_sup_right : S ≤ L1 ⊔ S) (hA.1 htA)
    have htO : t ∉ pCoreOf 2 H := by
      rw [hpCore1]
      exact htQ
    have hnot' : ¬ H ≤ (H ⊓ Subgroup.centralizer (Zt : Set G)) ⊔ pCoreOf 2 H := by
      rwa [hpCore1]
    have hbig := sq_le_relIndex_centralizer (H := H) (V := Zt) (q := q)
      hbender1 (fun v hv => by simpa [pow_two] using hZe.2 v hv) hHV hnot'
      htH ht2 htO
    have hsmall := relIndex_centralizer_zTilde_le_q_of_not_le_q1 hF hS1 hq hA htA htQ
    have hqq : q * q ≤ q * 1 := by
      simpa [pow_two, mul_one] using hbig.trans hsmall
    have hqle : q ≤ 1 := Nat.le_of_mul_le_mul_left hqq (by omega)
    omega
  have hQ1P1 : Q1 L1 L2 S ≤ P1 L1 L2 S := pCoreOf_le 2 (P1 L1 L2 S)
  have hQ1H : Q1 L1 L2 S ≤ H := by
    rw [hH]
    exact hQ1S.trans le_sup_right
  have hQ1N : Q1 L1 L2 S ≤
      Subgroup.normalizer ((H ⊓ Subgroup.centralizer (Zt : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxNZ : x ∈ Subgroup.normalizer (Zt : Set G) :=
      (hQ1P1.trans (by rw [hZt]; exact normalizer_zTilde L1 L2 S q)) hx
    have hxNC : x ∈ Subgroup.normalizer
        (Subgroup.centralizer (Zt : Set G) : Set G) :=
      (F7.normalizer_le_normalizer_centralizer Zt) hxNZ
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer (hQ1H hx)) hxNC
  have hO2 : oTwoUpper H ≤ H ⊓ Subgroup.centralizer (Zt : Set G) :=
    CFSG.Quasithin.Vol2.Ch11.SecD.oTwoUpper_le_of_le_sup' hle
      (pCoreOf_isPGroup 2 (P1 L1 L2 S)) hQ1N
  have hO2C : oTwoUpper H ≤ Subgroup.centralizer (Zt : Set G) := hO2.trans inf_le_right
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hO2C

theorem not_jAtLeast_le_of_not_le_q1
    {L1 L2 S : Subgroup G} {q : ℕ} (hF : Hyp111 L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S)
    (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S)
    (hq : IsSzU3Quot (oTwoQuot ↥L1) q) (hJ : ¬ thompsonJ S ≤ Q1 L1 L2 S) :
    ¬ jAtLeast (2 ^ CFSG.Open.pRank 2 S) q S ≤ Q2 L1 L2 S := by
  classical
  intro hJs
  set m : ℕ := 2 ^ CFSG.Open.pRank 2 S with hm
  set Z : Subgroup G := omegaOneCenterOf (jAtLeast m q S) with hZ
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF
  have hbender1 : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) q := by
    rw [hsup1]
    exact IsSzU3Quot.of_mulEquiv (oTwoQuotSupEquiv hF) hq
  have hq1 : 1 ≤ q := by
    have := IsSzU3Quot.four_le hq
    omega
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hJeq : jAtLeast m q (Q2 L1 L2 S) = jAtLeast m q S :=
    jAtLeast_eq_of_le (m := m) (q := q) hJs hQ2S
  have hBNZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZ]
    exact (hB.trans (normalizer_le_normalizer_jAtLeast m q S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hSNZ : S ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZ]
    exact (Subgroup.le_normalizer : S ≤ Subgroup.normalizer (S : Set G)).trans
      ((normalizer_le_normalizer_jAtLeast m q S).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf (jAtLeast m q S)))
  have hP2NZ : P2 L1 L2 S ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZ]
    have h : P2 L1 L2 S ≤ Subgroup.normalizer (jAtLeast m q S : Set G) := by
      have h' := (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
        (normalizer_le_normalizer_jAtLeast m q (Q2 L1 L2 S))
      rwa [hJeq] at h'
    exact h.trans (A4.normalizer_le_normalizer_omegaOneCenterOf (jAtLeast m q S))
  have hJne : thompsonJ S ≠ ⊥ := fun hbot => hJ (hbot ▸ bot_le)
  have hJstarP : IsPGroup 2 (jAtLeast m q S) :=
    hF.h1.pgroup.to_le (jAtLeast_le m q S)
  have hJstarNe' : jAtLeast m q S ≠ ⊥ := fun hbot =>
    hJne (le_bot_iff.mp ((thompsonJ_le_jAtLeast hq1 S).trans (le_of_eq hbot)))
  have hJstarNe : jAtLeast m q S ≠ ⊥ := by
    rwa [hm]
  have hZne : Z ≠ ⊥ := by
    rw [hZ]
    exact Setup.omegaOneCenterOf_ne_bot hJstarP hJstarNe
  have hZe : IsElemAbelian 2 Z := SmithC27.isElemAbelian_omegaOneCenterOf _
  have hZS : Z ≤ S := by
    rw [hZ]
    exact (A4.omegaOneCenterOf_le _).trans (jAtLeast_le m q S)
  have hZcJ : Z ≤ Subgroup.centralizer (jAtLeast m q S : Set G) := by
    rw [hZ]
    exact (A4.omegaOneCenterOf_le_centerOf _).trans (A4.centerOf_le_centralizer _)
  have hZleA : ∀ A : Subgroup G, IsMaxElemAbelian S A → Z ≤ A := by
    intro A hA
    have hcardA : Nat.card A = m := by
      have := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
      rw [hm]
      simpa using this
    have hAJ : A ≤ jAtLeast m q S :=
      le_jAtLeast hA.1 hA.2.1 (by rw [hcardA]; exact Nat.le_mul_of_pos_left _ (by omega))
    have hZcA : Z ≤ Subgroup.centralizer (A : Set G) :=
      hZcJ.trans (Subgroup.centralizer_le hAJ)
    have hsup : IsElemAbelian 2 (Z ⊔ A) :=
      IsElemAbelian.sup_of_commute hZe hA.2.1
        (fun z hz a ha => (Subgroup.mem_centralizer_iff.mp (hZcA hz) a ha).symm)
    have hcard : Nat.card ↥(Z ⊔ A) ≤ Nat.card A :=
      hA.2.2 (Z ⊔ A) (sup_le hZS hA.1) hsup
    have hZA : A = Z ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_right hcard
    rw [hZA]
    exact le_sup_left
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hZQ1 : Z ⊓ Q1 L1 L2 S ≤ zTilde L1 L2 S q := by
    intro x hx
    obtain ⟨hxZ, hxQ1⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian S
    have hxAQ1 : x ∈ A ⊓ Q1 L1 L2 S := ⟨hZleA A hA hxZ, hxQ1⟩
    have hxJ : x ∈ jAtLeast m q (Q1 L1 L2 S) :=
      inf_le_jAtLeast_of_not_le_q1 hF hS1 hq hA hxAQ1
    have hZcQ1 : Z ≤ Subgroup.centralizer (jAtLeast m q (Q1 L1 L2 S) : Set G) :=
      hZcJ.trans (Subgroup.centralizer_le (jAtLeast_mono (m := m) (q := q) hQ1S))
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨hxJ, hZcQ1 hxZ⟩, hZe.2 x hxZ⟩
  by_cases hZQ1le : Z ≤ Q1 L1 L2 S
  · have hZeq : Z ⊓ Q1 L1 L2 S = Z := inf_eq_left.mpr hZQ1le
    have hZleZt : Z ≤ zTilde L1 L2 S q := by
      simpa [hZeq] using hZQ1
    have hYc : ⁅zTilde L1 L2 S q, oTwoUpper (L1 ⊔ S)⁆ = ⊥ :=
      commutator_zTilde_oTwoUpper_of_not_le_q1 hF hS1 hq hJ
    have hO2Zt : oTwoUpper (L1 ⊔ S) ≤ Subgroup.centralizer (zTilde L1 L2 S q : Set G) := by
      rw [Subgroup.commutator_comm] at hYc
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYc
    have hO2Z : oTwoUpper (L1 ⊔ S) ≤ Subgroup.centralizer (Z : Set G) :=
      hO2Zt.trans (Subgroup.centralizer_le hZleZt)
    have hHS : L1 ⊔ S = oTwoUpper (L1 ⊔ S) ⊔ S :=
      CFSG.Quasithin.H13.eq_oTwoUpper_sup_of_isSylowTwoOf
        (by rw [hsup1]; exact isSylowTwoOf_sup_pCoreOf hF hS1)
    have hHNZ : L1 ⊔ S ≤ Subgroup.normalizer (Z : Set G) := by
      rw [hHS]
      exact sup_le (hO2Z.trans (Subgroup.centralizer_le_normalizer (Z : Set G))) hSNZ
    have hP1NZ : P1 L1 L2 S ≤ Subgroup.normalizer (Z : Set G) :=
      sup_le (le_sup_left.trans hHNZ) hBNZ
    have hG0NZ : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (Z : Set G) := by
      rw [← F1.parabolic_sup_parabolic L1 L2 S]
      exact sup_le hP1NZ hP2NZ
    have hZleO : Z ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 (hZS.trans le_sup_right) hG0NZ
        (hF.h1.pgroup.to_le hZS)
    rw [hF.o2] at hZleO
    exact hZne (le_bot_iff.mp hZleO)
  · obtain ⟨z', hz'Z, hz'Q1⟩ : ∃ z', z' ∈ Z ∧ z' ∉ Q1 L1 L2 S := by
      by_contra hcon
      push Not at hcon
      exact hZQ1le (fun x hx => hcon x hx)
    have hz'S : z' ∈ S := hZS hz'Z
    have hz'P1 : z' ∈ P1 L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
        ((le_sup_right : S ≤ bigB L1 L2 S) hz'S)
    have hYn : L1 ⊔ S ≤ Subgroup.normalizer (zTilde L1 L2 S q : Set G) :=
      (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
        (normalizer_zTilde L1 L2 S q)
    have hc : ∀ x ∈ Q1 L1 L2 S, x * z' * x⁻¹ * z'⁻¹ ∈ zTilde L1 L2 S q := by
      intro x hx
      have hxS : x ∈ S := hQ1S hx
      have hxNZ : x ∈ Subgroup.normalizer (Z : Set G) := hSNZ hxS
      have hconjZ : x * z' * x⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp hxNZ z').mp hz'Z
      have hcomZ : x * z' * x⁻¹ * z'⁻¹ ∈ Z := Z.mul_mem hconjZ (Z.inv_mem hz'Z)
      have hconjQ : z' * x * z'⁻¹ ∈ Q1 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp
          ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)) hz'P1) x).mp hx
      have hcomQ : x * z' * x⁻¹ * z'⁻¹ ∈ Q1 L1 L2 S := by
        have hmul : z' * x * z'⁻¹ * x⁻¹ ∈ Q1 L1 L2 S :=
          (Q1 L1 L2 S).mul_mem hconjQ ((Q1 L1 L2 S).inv_mem hx)
        have heq : x * z' * x⁻¹ * z'⁻¹ = (z' * x * z'⁻¹ * x⁻¹)⁻¹ := by group
        rw [heq]
        exact (Q1 L1 L2 S).inv_mem hmul
      exact hZQ1 ⟨hcomZ, hcomQ⟩
    exact false_of_commutator_le_of_bender hF hB hS1 hq (zTilde_le_pCoreOf L1 L2 S q)
      hYn (commutator_zTilde_oTwoUpper_of_not_le_q1 hF hS1 hq hJ) hz'S hz'Q1 hc

theorem str83_not_jAtLeast_le_of_caseIa
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112Hyp L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hJ2 : thompsonJ S ≤ Q2 L1 L2 S) (hJ1 : ¬ thompsonJ S ≤ Q1 L1 L2 S) :
    ¬ jAtLeast (2 ^ CFSG.Open.pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q2 L1 L2 S := by
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ (2 * a + 1)) := by
    obtain ⟨e⟩ := hSz
    exact Or.inl ⟨a, ha, rfl, ⟨e⟩⟩
  exact not_jAtLeast_le_of_not_le_q1 hF.1 hB hS1 hS2 hq hJ1

theorem card_chiefSeries_z2_le_two
    {L1 L2 S : Subgroup G} {a c : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hJ1 : ¬ thompsonJ S ≤ Q1 L1 L2 S)
    (hser : IsChiefSeriesFrom (L2 ⊔ S) (Z2 L1 L2 S) (Z2 L1 L2 S) c) :
    c ≤ 2 := by
  let q : ℕ := 2 ^ (2 * a + 1)
  have hq4 : 4 ≤ q := by
    have h : 4 ≤ 2 ^ (2 * a + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [q] using h
  have hq1 : 1 < q := by omega
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hq : IsSzU3Quot (oTwoQuot ↥L1) q := by
    obtain ⟨e⟩ := hSz
    exact Or.inl ⟨a, ha, rfl, ⟨e⟩⟩
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
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
  have hnotJ : ¬ jAtLeast (2 ^ CFSG.Open.pRank 2 S) q S ≤ Q2 L1 L2 S :=
    not_jAtLeast_le_of_not_le_q1 hF.1 hB hS1 hS2 hq hJ1
  obtain ⟨E, hES, hEe, hmE, hEQ2⟩ := exists_not_le_of_not_jAtLeast_le hnotJ
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf _
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hZ2H : Z2 L1 L2 S ≤ L2 ⊔ S := hZ2S.trans le_sup_right
  have hZ2p : IsPGroup 2 (Z2 L1 L2 S) := hF.1.h2.pgroup.to_le hZ2S
  have hR := relIndex_centralizer_le_mul (S := S) (V := Z2 L1 L2 S) (F := E) (k := q)
    hZ2e hZ2S hEe hES hmE
  have hErel : (E ⊓ Q2 L1 L2 S).relIndex E ≤ q := by
    rw [Subgroup.inf_relIndex_left]
    calc (Q2 L1 L2 S).relIndex E ≤ (Q2 L1 L2 S).relIndex S :=
          Subgroup.relIndex_le_of_le_right hES (D15Proof.relIndex_ne_zero _ _)
      _ = q := by
          have h := str86_relIndex_q2_s (n := 2 * a + 1) hF hB (by omega) hL2
          simpa [q] using h
  have hCV' : (E ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E ≤
      (E ⊓ Q2 L1 L2 S).relIndex E := by
    refine Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)
    refine le_inf inf_le_left ?_
    intro x hx
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hx.2
  have hCV : (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E ≤
      (E ⊓ Q2 L1 L2 S).relIndex E := by
    rwa [Subgroup.inf_relIndex_left] at hCV'
  have hdispE : (Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S) ≤ q * q :=
    hR.trans (Nat.mul_le_mul_left q (hCV.trans hErel))
  obtain ⟨e, heE, heQ2⟩ : ∃ e, e ∈ E ∧ e ∉ Q2 L1 L2 S := by
    by_contra hcon
    push Not at hcon
    exact hEQ2 (fun x hx => hcon x hx)
  have heH : e ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) (hES heE)
  have he2 : e * e ∈ pCoreOf 2 (L2 ⊔ S) := by
    rw [hpCore2]
    rw [show e * e = 1 from by rw [← pow_two]; exact hEe.2 e heE]
    exact (Q2 L1 L2 S).one_mem
  have heO : e ∉ pCoreOf 2 (L2 ⊔ S) := by
    rwa [hpCore2]
  have hM6 := l2_pow_sq_le_relIndex_centralizer (H := L2 ⊔ S) (U := Z2 L1 L2 S)
    (m := 2 * a + 1) (c := c) (hm2 := by omega) (hL2 := hL2sup)
    hZ2p hZ2H hser heH he2 heO
  have hcent : Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) =
      Subgroup.centralizer ({e} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hmono : (Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G)).relIndex
      (Z2 L1 L2 S) ≤ (Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S) := by
    rw [hcent]
    exact Subgroup.relIndex_le_of_le_left
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heE))
      (D15Proof.relIndex_ne_zero _ _)
  have hin : q ^ c ≤ q ^ 2 := by
    calc q ^ c ≤ (Subgroup.centralizer
          ((Subgroup.zpowers e : Subgroup G) : Set G)).relIndex (Z2 L1 L2 S) := hM6
      _ ≤ (Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S) := hmono
      _ ≤ q * q := hdispE
      _ = q ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_right hq1).mp hin


theorem z2_inf_centralizer_sup_eq_bot_of_caseI
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z2 L1 L2 S ⊓ Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨-, -, hZ2bot, -, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  rwa [hsup2]

theorem not_isCentralStep_bot_of_caseI
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {Y : Subgroup G} (hstep : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ Y) :
    ¬ IsCentralStep (L2 ⊔ S) ⊥ Y := by
  intro hcent
  have hZ2bot := z2_inf_centralizer_sup_eq_bot_of_caseI hF hB ha hSz hL2 hZI
  have hYleC : Y ≤ Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 : g * x * g⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := hcent g hg x hx
    have h2 : g * x * g⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h1
    have h3 : g * x * g⁻¹ = x := by
      have := congrArg (fun y => y * x) h2
      simpa [mul_assoc] using this
    have h4 : g * x = x * g := by
      have := congrArg (fun y => y * g) h3
      simpa [mul_assoc] using this
    exact h4
  have hYle : Y ≤ Z2 L1 L2 S ⊓ Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) :=
    le_inf hstep.1.1 hYleC
  have hYbot : Y = ⊥ := le_bot_iff.mp (hYle.trans (le_of_eq hZ2bot))
  exact (ne_of_gt hstep.2.2.1) hYbot

theorem one_le_chiefSeries_z2_of_caseI
    {L1 L2 S : Subgroup G} {a c : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hser : IsChiefSeriesFrom (L2 ⊔ S) (Z2 L1 L2 S) (Z2 L1 L2 S) c) :
    1 ≤ c := by
  by_contra hc
  have hc0 : c = 0 := by omega
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hZ2ne : Z2 L1 L2 S ≠ ⊥ := by
    intro hbot
    have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
      have hZ1eq := (str83_caseI_basics hF hB ha hSz hL2 hZI).1
      rw [hZ1eq]
      exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
    exact hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq hbot)))
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hZ2p : IsPGroup 2 (Z2 L1 L2 S) := hF.1.h2.pgroup.to_le hZ2S
  have hcomm := D14.commutator_eq_bot_of_zero hZ2p hser hc0
  have hH : L2 ⊔ S = oTwoUpper (L2 ⊔ S) ⊔ Q2 L1 L2 S := by
    have h := str86_u3H_eq_oTwoUpper_sup_q2 (n := 2 * a + 1) hF (by omega) hL2
    change L2 ⊔ Q2 L1 L2 S = oTwoUpper (L2 ⊔ Q2 L1 L2 S) ⊔ Q2 L1 L2 S at h
    rw [← hsup2] at h
    exact h
  have hO2C : oTwoUpper (L2 ⊔ S) ≤
      Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hC : (L2 ⊔ S : Subgroup G) ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    rw [hH]
    exact sup_le hO2C (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S))
  have hZ2le : Z2 L1 L2 S ≤ Z2 L1 L2 S ⊓
      Subgroup.centralizer ((L2 ⊔ S : Subgroup G) : Set G) := by
    refine le_inf le_rfl ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hC hg) z hz).symm
  have hZ2bot := z2_inf_centralizer_sup_eq_bot_of_caseI hF hB ha hSz hL2 hZI
  exact hZ2ne (le_bot_iff.mp (hZ2le.trans (le_of_eq hZ2bot)))

theorem centralizer_eq_q2_of_caseI
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112Hyp L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {Y : Subgroup G} (hYn : L2 ⊔ S ≤ Subgroup.normalizer (Y : Set G))
    (hYZ : Y ≤ Z2 L1 L2 S) (hYne : Y ≠ ⊥) :
    (L2 ⊔ S) ⊓ Subgroup.centralizer (Y : Set G) = Q2 L1 L2 S := by
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  set H : Subgroup G := L2 ⊔ S with hH
  set K : Subgroup G := H ⊓ Subgroup.centralizer (Y : Set G) with hK
  have hKH : K ≤ H := by rw [hK]; exact inf_le_left
  have hQ2H : Q2 L1 L2 S ≤ H := hQ2S.trans le_sup_right
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Y : Set G) :=
    (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)).trans
      (Subgroup.centralizer_le hYZ)
  have hQ2K : Q2 L1 L2 S ≤ K := le_inf hQ2H hQ2C
  have hHnC : H ≤ Subgroup.normalizer
      (Subgroup.centralizer (Y : Set G) : Set G) :=
    hYn.trans (F7.normalizer_le_normalizer_centralizer Y)
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    rw [hK]
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hx) (hHnC hx)
  have hKn' : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (K : Set G) := by
    rwa [← hsup2]
  have hKH' : K ≤ L2 ⊔ Q2 L1 L2 S := by
    rwa [← hsup2]
  rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW (by omega : 2 ≤ 2 * a + 1) hL2
      hKH' hKn' hQ2K with hQ | hTop
  · rw [hK] at hQ
    exact hQ
  · exfalso
    have hKtop : K = H := by rw [hTop, hsup2]
    have hHleC : H ≤ Subgroup.centralizer (Y : Set G) := by
      have := hKtop
      rw [hK] at this
      exact inf_eq_left.mp this
    have hYleC : Y ≤ Subgroup.centralizer (H : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_iff.mp (hHleC hg) y hy).symm
    have hYle : Y ≤ Z2 L1 L2 S ⊓ Subgroup.centralizer (H : Set G) := le_inf hYZ hYleC
    rw [hH] at hYle
    have hZ2bot := z2_inf_centralizer_sup_eq_bot_of_caseI hF.toW hB ha hSz hL2 hZI
    exact hYne (le_bot_iff.mp (hYle.trans (le_of_eq hZ2bot)))


end CFSG.Quasithin.Stroth

end
