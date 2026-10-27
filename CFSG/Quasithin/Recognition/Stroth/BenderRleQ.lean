module

public import CFSG.Quasithin.Recognition.Stroth.BenderJn
public import CFSG.Quasithin.Recognition.Stroth.BenderOriented
public import CFSG.Quasithin.Background.D15Chief

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev zTilde (L1 L2 S : Subgroup G) (q : ℕ) : Subgroup G :=
  omegaOneCenterOf (jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S))

theorem normalizer_zTilde (L1 L2 S : Subgroup G) (q : ℕ) :
    P1 L1 L2 S ≤ Subgroup.normalizer (zTilde L1 L2 S q : Set G) :=
  (le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans <|
    (normalizer_le_normalizer_jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S)).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf
        (jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S)))

theorem zTilde_le_pCoreOf (L1 L2 S : Subgroup G) (q : ℕ) :
    zTilde L1 L2 S q ≤ Q1 L1 L2 S :=
  (A4.omegaOneCenterOf_le (jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S))).trans
    (jAtLeast_le (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S))

namespace OrientedBenderPair

variable {L1 L2 S : Subgroup G} {q r : ℕ}

theorem inf_le_jAtLeast
    (h : OrientedBenderPair L1 L2 S q r) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) :
    A ⊓ Q1 L1 L2 S ≤ jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S) := by
  have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 S := by
    have := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
    simpa using this
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hAsq : ∀ a ∈ A, a ^ 2 ∈ Q1 L1 L2 S := by
    intro a ha
    rw [hAe.2 a ha]
    exact (Q1 L1 L2 S).one_mem
  have hrel : (A ⊓ Q1 L1 L2 S).relIndex A ≤ q := h.relIndex_le_q hA.1 hAsq
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

private theorem relIndex_centralizer_zTilde_le_q
    (h : OrientedBenderPair L1 L2 S q r) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) {t : G} (htA : t ∈ A) (htQ : t ∉ Q1 L1 L2 S) :
    (zTilde L1 L2 S q ⊓ Subgroup.centralizer ({t} : Set G)).relIndex
      (zTilde L1 L2 S q) ≤ q := by
  have hcardA : Nat.card A = 2 ^ CFSG.Open.pRank 2 S := by
    have := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
    simpa using this
  have hAe : IsElemAbelian 2 A := hA.2.1
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [h.s1]
    exact le_sup_right
  have hZe : IsElemAbelian 2 (zTilde L1 L2 S q) :=
    SmithC27.isElemAbelian_omegaOneCenterOf _
  have hZS : zTilde L1 L2 S q ≤ S := (zTilde_le_pCoreOf L1 L2 S q).trans hQ1S
  have hZc : zTilde L1 L2 S q ≤
      Subgroup.centralizer (jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S) : Set G) :=
    (A4.omegaOneCenterOf_le_centerOf _).trans (A4.centerOf_le_centralizer _)
  have hAQ1J : A ⊓ Q1 L1 L2 S ≤ jAtLeast (2 ^ CFSG.Open.pRank 2 S) q (Q1 L1 L2 S) :=
    h.inf_le_jAtLeast hA
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
  have hArel : (A ⊓ Q1 L1 L2 S).relIndex A ≤ q := h.relIndex_le_q hA.1 hAsq
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

private theorem exists_maxElemAbelian_not_le_pCoreOf
    (h : OrientedBenderPair L1 L2 S q r) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ Q1 L1 L2 S := by
  by_contra hcon
  push Not at hcon
  exact h.j_not_le (by
    rw [thompsonJ]
    exact iSup₂_le fun A hA => hcon A hA)

theorem commutator_zTilde_oTwoUpper
    (h : OrientedBenderPair L1 L2 S q r) :
    ⁅zTilde L1 L2 S q, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
  classical
  set H : Subgroup G := L1 ⊔ S with hH
  set Zt : Subgroup G := zTilde L1 L2 S q with hZt
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [h.s1]
    exact le_sup_right
  have hZe : IsElemAbelian 2 Zt := SmithC27.isElemAbelian_omegaOneCenterOf _
  have hHV : H ≤ Subgroup.normalizer (Zt : Set G) := by
    rw [hH, hZt]
    exact (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans
      (normalizer_zTilde L1 L2 S q)
  have hq2 : 2 ≤ q := by
    have := IsSzU3Quot.four_le h.bender1
    omega
  have hle : H ≤ (H ⊓ Subgroup.centralizer (Zt : Set G)) ⊔ Q1 L1 L2 S := by
    by_contra hnot
    obtain ⟨A, hA, hAQ1⟩ := exists_maxElemAbelian_not_le_pCoreOf h
    obtain ⟨t, htA, htQ⟩ : ∃ t, t ∈ A ∧ t ∉ Q1 L1 L2 S := by
      by_contra hcon
      push Not at hcon
      exact hAQ1 (fun x hx => hcon x hx)
    have ht2 : t * t = 1 := by simpa [pow_two] using hA.2.1.2 t htA
    have htH : t ∈ H := by
      rw [hH]
      exact (le_sup_right : S ≤ L1 ⊔ S) (hA.1 htA)
    have htO : t ∉ pCoreOf 2 H := by
      rw [pCoreOf_sup₁ h]
      exact htQ
    have hnot' : ¬ H ≤ (H ⊓ Subgroup.centralizer (Zt : Set G)) ⊔ pCoreOf 2 H := by
      rwa [pCoreOf_sup₁ h]
    have hbig := sq_le_relIndex_centralizer (H := H) (V := Zt) (q := q)
      h.bender_sup₁ (fun v hv => by simpa [pow_two] using hZe.2 v hv) hHV hnot'
      htH ht2 htO
    have hsmall := relIndex_centralizer_zTilde_le_q h hA htA htQ
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

theorem not_jAtLeast_le
    (h : OrientedBenderPair L1 L2 S q r) :
    ¬ jAtLeast (2 ^ CFSG.Open.pRank 2 S) q S ≤ Q2 L1 L2 S := by
  classical
  intro hJ
  set m : ℕ := 2 ^ CFSG.Open.pRank 2 S with hm
  set Z : Subgroup G := omegaOneCenterOf (jAtLeast m q S) with hZ
  have hq1 : 1 ≤ q := by
    have := IsSzU3Quot.four_le h.bender1
    omega
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [h.s2]
    exact le_sup_right
  have hJeq : jAtLeast m q (Q2 L1 L2 S) = jAtLeast m q S :=
    jAtLeast_eq_of_le (m := m) (q := q) hJ hQ2S
  have hBNZ : bigB L1 L2 S ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZ]
    exact (h.sB.trans (normalizer_le_normalizer_jAtLeast m q S)).trans
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
  have hJne : thompsonJ S ≠ ⊥ := fun hbot => h.j_not_le (hbot ▸ bot_le)
  have hJstarP : IsPGroup 2 (jAtLeast m q S) :=
    h.hyp.h1.pgroup.to_le (jAtLeast_le m q S)
  have hJstarNe' : jAtLeast (2 ^ CFSG.Open.pRank 2 S) q S ≠ ⊥ := fun hbot =>
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
    conv_rhs => rw [h.s1]
    exact le_sup_right
  have hZQ1 : Z ⊓ Q1 L1 L2 S ≤ zTilde L1 L2 S q := by
    intro x hx
    obtain ⟨hxZ, hxQ1⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian S
    have hxAQ1 : x ∈ A ⊓ Q1 L1 L2 S := ⟨hZleA A hA hxZ, hxQ1⟩
    have hxJ : x ∈ jAtLeast m q (Q1 L1 L2 S) := (h.inf_le_jAtLeast hA) hxAQ1
    have hZcQ1 : Z ≤ Subgroup.centralizer (jAtLeast m q (Q1 L1 L2 S) : Set G) :=
      hZcJ.trans (Subgroup.centralizer_le (jAtLeast_mono (m := m) (q := q) hQ1S))
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨hxJ, hZcQ1 hxZ⟩, hZe.2 x hxZ⟩
  by_cases hZQ1le : Z ≤ Q1 L1 L2 S
  · have hZeq : Z ⊓ Q1 L1 L2 S = Z := inf_eq_left.mpr hZQ1le
    have hZleZt : Z ≤ zTilde L1 L2 S q := by
      simpa [hZeq] using hZQ1
    have hYc : ⁅zTilde L1 L2 S q, oTwoUpper (L1 ⊔ S)⁆ = ⊥ :=
      h.commutator_zTilde_oTwoUpper
    have hO2Zt : oTwoUpper (L1 ⊔ S) ≤ Subgroup.centralizer (zTilde L1 L2 S q : Set G) := by
      rw [Subgroup.commutator_comm] at hYc
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hYc
    have hO2Z : oTwoUpper (L1 ⊔ S) ≤ Subgroup.centralizer (Z : Set G) :=
      hO2Zt.trans (Subgroup.centralizer_le hZleZt)
    have hHS : L1 ⊔ S = oTwoUpper (L1 ⊔ S) ⊔ S :=
      CFSG.Quasithin.H13.eq_oTwoUpper_sup_of_isSylowTwoOf (h.isSylowTwoOf₁)
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
        (h.hyp.h1.pgroup.to_le hZS)
    rw [h.hyp.o2] at hZleO
    exact hZne (le_bot_iff.mp hZleO)
  · obtain ⟨z', hz'Z, hz'Q1⟩ : ∃ z', z' ∈ Z ∧ z' ∉ Q1 L1 L2 S := by
      by_contra hcon
      push Not at hcon
      exact hZQ1le (fun x hx => hcon x hx)
    have hz'S : z' ∈ S := hZS hz'Z
    have hz'P1 : z' ∈ P1 L1 L2 S :=
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
        ((le_sup_right : S ≤ bigB L1 L2 S) hz'S)
    have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
      sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    have hYn : L1 ⊔ S ≤ Subgroup.normalizer (zTilde L1 L2 S q : Set G) :=
      hHleP1.trans (normalizer_zTilde L1 L2 S q)
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
    exact h.false_of_commutator_le (zTilde_le_pCoreOf L1 L2 S q) hYn
      h.commutator_zTilde_oTwoUpper hz'S hz'Q1 hc

theorem r_le_q
    (h : OrientedBenderPair L1 L2 S q r) : r ≤ q := by
  classical
  obtain ⟨F, hFS, hFe, hmF, hFQ2⟩ :=
    exists_not_le_of_not_jAtLeast_le h.not_jAtLeast_le
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) := SmithC27.isElemAbelian_omegaOneCenterOf _
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [h.s2]
    exact le_sup_right
  have hZ2S : Z2 L1 L2 S ≤ S :=
    (A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hFsq : ∀ a ∈ F, a ^ 2 ∈ Q2 L1 L2 S := by
    intro a ha
    rw [hFe.2 a ha]
    exact (Q2 L1 L2 S).one_mem
  have hFQ : (F ⊓ Q2 L1 L2 S).relIndex F ≤ r := h.relIndex_le_r hFS hFsq
  have hR := relIndex_centralizer_le_mul (S := S) (V := Z2 L1 L2 S)
    (F := F) (k := q) hZ2e hZ2S hFe hFS hmF
  have hCV' : (F ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex F ≤
      (F ⊓ Q2 L1 L2 S).relIndex F := by
    refine Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)
    refine le_inf inf_le_left ?_
    intro x hx
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hx.2
  have hCV : (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex F ≤
      (F ⊓ Q2 L1 L2 S).relIndex F := by
    rwa [Subgroup.inf_relIndex_left] at hCV'
  have hdispF : (Subgroup.centralizer (F : Set G)).relIndex (Z2 L1 L2 S) ≤ q * r :=
    hR.trans (Nat.mul_le_mul_left q (hCV.trans hFQ))
  obtain ⟨f, hfF, hfQ2⟩ : ∃ f, f ∈ F ∧ f ∉ Q2 L1 L2 S := by
    by_contra hcon
    push Not at hcon
    exact hFQ2 (fun x hx => hcon x hx)
  have hfS : f ∈ S := hFS hfF
  have hf2 : f * f = 1 := by simpa [pow_two] using hFe.2 f hfF
  have hv : r ^ 2 ≤ (Z2 L1 L2 S ⊓ Subgroup.centralizer ({f} : Set G)).relIndex
      (Z2 L1 L2 S) :=
    h.v2b hfS (by rw [hf2]; exact (Q2 L1 L2 S).one_mem) hfQ2
  have hmono : (Z2 L1 L2 S ⊓ Subgroup.centralizer ({f} : Set G)).relIndex
      (Z2 L1 L2 S) ≤
      (Subgroup.centralizer (F : Set G)).relIndex (Z2 L1 L2 S) := by
    have hle : Z2 L1 L2 S ⊓ Subgroup.centralizer (F : Set G) ≤
        Z2 L1 L2 S ⊓ Subgroup.centralizer ({f} : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hfF))
    have h := Subgroup.relIndex_le_of_le_left (L := Z2 L1 L2 S) hle
      (D15Proof.relIndex_ne_zero _ _)
    have h' : (Z2 L1 L2 S ⊓ Subgroup.centralizer (F : Set G)).relIndex (Z2 L1 L2 S) =
        (Subgroup.centralizer (F : Set G)).relIndex (Z2 L1 L2 S) :=
      Subgroup.inf_relIndex_left (H := Z2 L1 L2 S)
        (K := Subgroup.centralizer (F : Set G))
    rw [← h']
    exact h
  have hfin : r ^ 2 ≤ q * r := hv.trans (hmono.trans hdispF)
  have hrpos : 0 < r := by
    have := IsSzU3Quot.four_le h.bender2
    omega
  have hrr : r * r ≤ r * q := by
    calc r * r = r ^ 2 := by ring
      _ ≤ q * r := hfin
      _ = r * q := by ring
  exact Nat.le_of_mul_le_mul_left hrr hrpos

end OrientedBenderPair

end CFSG.Quasithin.Stroth

end
