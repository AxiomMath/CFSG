module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrStar
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private theorem commutator_zpowers_le_of_forall {K N : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (N : Set G))
    (h : ∀ x ∈ K, ⁅x, d⁆ ∈ N) :
    ⁅K, Subgroup.zpowers d⁆ ≤ N := by
  have key : ∀ t ∈ Subgroup.zpowers d, t ∈ Subgroup.normalizer (N : Set G) ∧
      ∀ x ∈ K, ⁅x, t⁆ ∈ N := by
    intro t ht
    rw [Subgroup.zpowers_eq_closure] at ht
    induction ht using Subgroup.closure_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact ⟨hdN, h⟩
    | one =>
        exact ⟨Subgroup.one_mem _, fun x _ => by
          rw [commutatorElement_one_right]
          exact N.one_mem⟩
    | mul a b ha hb iha ihb =>
        refine ⟨Subgroup.mul_mem _ iha.1 ihb.1, fun x hx => ?_⟩
        rw [commutatorElement_mul_right_eq_mul_conj,
          show ⁅x, a⁆ * a * ⁅x, b⁆ * a⁻¹ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) by group]
        exact N.mul_mem (iha.2 x hx)
          ((Subgroup.mem_normalizer_iff.mp iha.1 ⁅x, b⁆).mp (ihb.2 x hx))
    | inv a ha iha =>
        refine ⟨Subgroup.inv_mem _ iha.1, fun x hx => ?_⟩
        have hxa : ⁅a, x⁆ ∈ N := by
          have h1 := N.inv_mem (iha.2 x hx)
          rwa [commutatorElement_inv] at h1
        rw [commutatorElement_inv_right]
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ iha.1) ⁅a, x⁆).mp hxa
  rw [Subgroup.commutator_le]
  exact fun x hx t ht => (key t ht).2 x hx

private theorem le_normalizer_y0_of_mem_scriptQ (h : Sec17Std G A c L Y₀) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSQ : S ∈ scriptQ A (lB A)) :
    S ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hmem : S ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hSQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩
  exact HeadProof.le_M_of_mem_scriptQPi_two h hmem

private theorem commutatorElement_mem_of_mem_sup (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) {S : Subgroup G} (hcS : c ∈ Subgroup.normalizer (S : Set G))
    (hQ0S : CFSG.Open.pCoreOf 2 Y₀ ≤ S) (hSY : S ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ∀ x ∈ Y₀ ⊔ S, ⁅x, c⁆ ∈ S := by
  intro x hx
  have hx' : x ∈ (S : Set G) * (Y₀ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S Y₀ hSY]
    exact (sup_comm Y₀ S) ▸ hx
  obtain ⟨s, hs, y, hy, rfl⟩ := hx'
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅s, c⁆ ∈ S := by
    have hc : c * s⁻¹ * c⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hcS s⁻¹).mp (S.inv_mem hs)
    rw [commutatorElement_def, show s * c * s⁻¹ * c⁻¹ = s * (c * s⁻¹ * c⁻¹) by group]
    exact S.mul_mem hs hc
  have h2 : ⁅y, c⁆ ∈ S := hQ0S (commutatorElement_mem_pCoreOf_y0 h hJ h1523 y hy)
  have h3 : s * ⁅y, c⁆ * s⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) ⁅y, c⁆).mp h2
  exact S.mul_mem h3 h1

private theorem inf_pCoreOf_sup_le {J Q W : Subgroup G} (hJW : J ≤ W)
    (hWNQ : W ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q) :
    J ⊓ (CFSG.Open.pCoreOf 2 J ⊔ Q) ≤ CFSG.Open.pCoreOf 2 J := by
  have hJNQ : J ≤ Subgroup.normalizer (Q : Set G) := hJW.trans hWNQ
  have hJQ : Q ⊓ J ≤ CFSG.Open.pCoreOf 2 J :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      ((le_inf hJNQ Subgroup.le_normalizer).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := Q) (K := J)))
      (hQ2.to_le inf_le_left)
  intro x hx
  obtain ⟨hxJ, hxOQ⟩ := Subgroup.mem_inf.mp hx
  have hOQ : CFSG.Open.pCoreOf 2 J ≤ Subgroup.normalizer (Q : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJW).trans hWNQ
  have hx' : x ∈ (CFSG.Open.pCoreOf 2 J : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (CFSG.Open.pCoreOf 2 J) Q hOQ]
    exact hxOQ
  obtain ⟨t, htO, q, hqQ, rfl⟩ := hx'
  have hqJ : q ∈ J := by
    have h1 : t⁻¹ * (t * q) ∈ J :=
      J.mul_mem (J.inv_mem ((CFSG.LieType.BorelTits.pCoreOf_le 2 J) htO)) hxJ
    simpa using h1
  exact (CFSG.Open.pCoreOf 2 J).mul_mem htO (hJQ ⟨hqQ, hqJ⟩)

private theorem commutator_le_pCoreOf_of_le_sup {S J U Q : Subgroup G}
    (hJY : J ≤ Y₀) (hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 J) (hQ2 : IsPGroup 2 Q)
    (hNQ : Y₀ ⊔ S ≤ Subgroup.normalizer (Q : Set G))
    (hUQS : U ≤ Q ⊔ S) (hUNJ : U ≤ Subgroup.normalizer (J : Set G)) :
    ⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  have hSNQ : S ≤ Subgroup.normalizer (Q : Set G) := le_sup_right.trans hNQ
  have hJNQ : J ≤ Subgroup.normalizer (Q : Set G) := (hJY.trans le_sup_left).trans hNQ
  have hkey := inf_pCoreOf_sup_le (hJW := hJY.trans le_sup_left) hNQ hQ2
  rw [Subgroup.commutator_le]
  intro x hx j hj
  have hxQS : x ∈ (Q : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q S hSNQ]
    exact hUQS hx
  obtain ⟨q, hqQ, s, hsS, rfl⟩ := hxQS
  have ht : ⁅s, j⁆ ∈ CFSG.Open.pCoreOf 2 J :=
    hSJ (Subgroup.commutator_mem_commutator hsS hj)
  have htW : ⁅s, j⁆ ∈ Y₀ ⊔ S :=
    Subgroup.mem_sup_left (((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJY) ht)
  have hconj : q * ⁅s, j⁆ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 J ⊔ Q := by
    have hid : q * ⁅s, j⁆ * q⁻¹ = ⁅s, j⁆ * ⁅⁅s, j⁆⁻¹, q⁆ := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    refine (CFSG.Open.pCoreOf 2 J ⊔ Q).mul_mem (Subgroup.mem_sup_left ht)
      (Subgroup.mem_sup_right ?_)
    have h1 : ⁅s, j⁆⁻¹ * q * (⁅s, j⁆⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hNQ (Subgroup.inv_mem (Y₀ ⊔ S) htW)) q).mp hqQ
    rw [commutatorElement_def,
      show ⁅s, j⁆⁻¹ * q * (⁅s, j⁆⁻¹)⁻¹ * q⁻¹ =
        (⁅s, j⁆⁻¹ * q * (⁅s, j⁆⁻¹)⁻¹) * q⁻¹ by group]
    exact Q.mul_mem h1 (Q.inv_mem hqQ)
  have hqj : ⁅q, j⁆ ∈ Q := by
    have h1 : j * q⁻¹ * j⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hJNQ hj) q⁻¹).mp (Q.inv_mem hqQ)
    rw [commutatorElement_def, show q * j * q⁻¹ * j⁻¹ = q * (j * q⁻¹ * j⁻¹) by group]
    exact Q.mul_mem hqQ h1
  have hmemJ : q * ⁅s, j⁆ * q⁻¹ * ⁅q, j⁆ ∈ J := by
    have h1 : q * s * j * (q * s)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hUNJ hx) j).mp hj
    have h2 : ⁅q * s, j⁆ ∈ J := by
      rw [commutatorElement_def]
      exact J.mul_mem h1 (J.inv_mem hj)
    rwa [commutatorElement_mul_left_eq_conj_mul] at h2
  have hmemO : q * ⁅s, j⁆ * q⁻¹ * ⁅q, j⁆ ∈ CFSG.Open.pCoreOf 2 J ⊔ Q :=
    (CFSG.Open.pCoreOf 2 J ⊔ Q).mul_mem hconj (Subgroup.mem_sup_right hqj)
  rw [commutatorElement_mul_left_eq_conj_mul]
  exact hkey ⟨hmemJ, hmemO⟩

private theorem commutator_le_pCoreOf_of_le_inf {J Q₀ U : Subgroup G}
    (hUQ : U ≤ Q₀) (hUNJ : U ≤ Subgroup.normalizer (J : Set G))
    (hJNQ : J ≤ Subgroup.normalizer (Q₀ : Set G)) (hQ2 : IsPGroup 2 Q₀) :
    ⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J := by
  have hJQ : J ⊓ Q₀ ≤ CFSG.Open.pCoreOf 2 J :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer hJNQ).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := J) (K := Q₀)))
      (hQ2.to_le inf_le_right)
  refine (Subgroup.commutator_le.mpr ?_).trans hJQ
  intro u hu j hj
  refine ⟨?_, ?_⟩
  · have h1 : u * j * u⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hUNJ hu) j).mp hj
    rw [commutatorElement_def]
    exact J.mul_mem h1 (J.inv_mem hj)
  · have h2 : j * u⁻¹ * j⁻¹ ∈ Q₀ :=
      (Subgroup.mem_normalizer_iff.mp (hJNQ hj) u⁻¹).mp (Q₀.inv_mem (hUQ hu))
    rw [commutatorElement_def, show u * j * u⁻¹ * j⁻¹ = u * (j * u⁻¹ * j⁻¹) by group]
    exact Q₀.mul_mem (hUQ hu) h2

private theorem le_of_inf_normalizer_le {Q₀ S U : Subgroup G}
    (hU : U = Q₀ ⊓ Subgroup.normalizer (S : Set G)) (hUS : U ≤ S)
    (hS2 : IsPGroup 2 S) (hQ2 : IsPGroup 2 Q₀)
    (hSQ : S ≤ Subgroup.normalizer (Q₀ : Set G)) :
    Q₀ ≤ S := by
  by_contra hQS
  have hS2P : IsPGroup 2 (Q₀ ⊔ S : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hQ2 hS2 hSQ
  have hlt : S < Q₀ ⊔ S :=
    lt_of_le_of_ne le_sup_right fun heq => hQS (heq.symm ▸ le_sup_left)
  have hmod : (Q₀ ⊔ S) ⊓ Subgroup.normalizer (S : Set G) ≤ S := by
    intro x hx
    obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ (Q₀ : Set G) * (S : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q₀ S hSQ]
      exact hxP
    obtain ⟨q, hqQ, s, hsS, rfl⟩ := hx'
    have hqN : q ∈ Subgroup.normalizer (S : Set G) := by
      have h1 : q * s * s⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
        (Subgroup.normalizer (S : Set G)).mul_mem hxN
          (Subgroup.inv_mem _ (Subgroup.le_normalizer hsS))
      simpa using h1
    have hqU : q ∈ U := by
      rw [hU]
      exact Subgroup.mem_inf.mpr ⟨hqQ, hqN⟩
    exact S.mul_mem (hUS hqU) hsS
  have hcontra : S < (Q₀ ⊔ S) ⊓ Subgroup.normalizer (S : Set G) :=
    CFSG.GroupTheory.FT63ChII.lt_inf_normalizer_of_lt hS2P hlt
  exact absurd hcontra (not_lt_of_ge hmod)

theorem pCoreOf_y0_le_of_spade (h : Sec17Std G A c L Y₀) (hQ0 : Claim17Q0) {S J : Subgroup G}
    (hJY : J ≤ Y₀) (hS2 : IsPGroup 2 S) (hSQ : S ∈ scriptQ A (lB A))
    (hspade : ∀ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) → U ∈ scriptQ A (lB A) →
      IsPGroup 2 U → U ≤ Subgroup.normalizer (J : Set G) ∧
        (⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J → U ≤ S)) :
    CFSG.Open.pCoreOf 2 Y₀ ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q₀ : Subgroup G := CFSG.Open.pCoreOf 2 Y₀ with hQ₀
  set P : Subgroup G := Q₀ ⊔ S
  have hQ0mem : Q₀ ∈ scriptQ A (lB A) := by rw [hQ₀]; exact hQ0 G A c L Y₀ h
  have hAQ₀ : A ≤ Subgroup.normalizer (Q₀ : Set G) := (mem_scriptQ_iff.mp hQ0mem).2.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := (mem_scriptQ_iff.mp hSQ).2.1
  have hSY : S ≤ Subgroup.normalizer (Y₀ : Set G) := le_normalizer_y0_of_mem_scriptQ h hS2 hSQ
  have hSJ0 : S ≤ Subgroup.normalizer (Q₀ : Set G) :=
    hSY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀)
  have hQ₀2 : IsPGroup 2 Q₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀
  have hP2 : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hQ₀2 hS2 hSJ0
  set U : Subgroup G := Q₀ ⊓ Subgroup.normalizer (S : Set G)
  have hUQ : U ≤ Q₀ := inf_le_left
  have hUNS : U ≤ Subgroup.normalizer (S : Set G) := inf_le_right
  have hU2 : IsPGroup 2 U := hP2.to_le (hUQ.trans le_sup_left)
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    (le_inf hAQ₀ (hAS.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Q₀)
        (K := Subgroup.normalizer (S : Set G)))
  have hUmem : U ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ0mem hUQ hAU
  obtain ⟨hUNJ, hspadeU⟩ := hspade U hUNS hUmem hU2
  have hUJ : ⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J :=
    commutator_le_pCoreOf_of_le_inf hUQ hUNJ
      (hJY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)) hQ₀2
  exact le_of_inf_normalizer_le rfl (hspadeU hUJ) hS2 hQ₀2 hSJ0

private theorem mem_scriptQ_of_le_centralizer (h : Sec17Std G A c L Y₀) (h142 : Concl142S14)
    {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUz : U ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G))
    (hAU : A ≤ Subgroup.normalizer (U : Set G)) :
    U ∈ scriptQ A (lB A) := by
  have h3U : ¬ 3 ∣ Nat.card U :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hU2 Nat.prime_three (by norm_num)
  exact mem_scriptQ_of_concl142 (h142 G A c L h.toSec14Std) h.zpowers_mem_omegaA
    ⟨hUz.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers c : Set G)),
      (isPiSubgroup_piCompl_iff Nat.prime_three U).mpr h3U, hAU⟩

private theorem exists_centralizer_of_not_le (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (hQ0 : Claim17Q0) {S J : Subgroup G}
    (hJY : J ≤ Y₀) (hS2 : IsPGroup 2 S) (hSQ : S ∈ scriptQ A (lB A))
    (hspade : ∀ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) → U ∈ scriptQ A (lB A) →
      IsPGroup 2 U → U ≤ Subgroup.normalizer (J : Set G) ∧
        (⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J → U ≤ S))
    (hQS : ¬ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ≤ S) :
    ∃ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) ∧
      U ≤ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ⊔ S ∧ IsPGroup 2 U ∧
      U ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) ∧
      A ≤ Subgroup.normalizer (U : Set G) ∧ ¬ U ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W : Subgroup G := Y₀ ⊔ S with hW
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 W
  have hAY : A ≤ Subgroup.normalizer (Y₀ : Set G) := h.mem_y0Star.prop.1.1.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := (mem_scriptQ_iff.mp hSQ).2.1
  have hSY : S ≤ Subgroup.normalizer (Y₀ : Set G) := le_normalizer_y0_of_mem_scriptQ h hS2 hSQ
  have hSW : S ≤ W := by rw [hW]; exact le_sup_right
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) W
  have hQleW : Q ≤ W := CFSG.LieType.BorelTits.pCoreOf_le 2 W
  have hWQ : W ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 W
  have hAW : A ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf hAY hAS).trans (Subgroup.inf_normalizer_le_normalizer_sup Y₀ S)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    hAW.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hcS : c ∈ Subgroup.normalizer (S : Set G) := hAS hcA
  have hQ0S : CFSG.Open.pCoreOf 2 Y₀ ≤ S := pCoreOf_y0_le_of_spade h hQ0 hJY hS2 hSQ hspade
  have hS2Q : IsPGroup 2 (Q ⊔ S : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hQ2 hS2 (hSW.trans hWQ)
  have hlt : S < Q ⊔ S :=
    lt_of_le_of_ne le_sup_right fun heq => hQS (heq.symm ▸ le_sup_left)
  set K : Subgroup G := (Q ⊔ S) ⊓ Subgroup.normalizer (S : Set G)
  have hSK : S ≤ K := le_inf le_sup_right Subgroup.le_normalizer
  have hSKlt : S < K := CFSG.GroupTheory.FT63ChII.lt_inf_normalizer_of_lt hS2Q hlt
  have hKW : K ≤ W := inf_le_left.trans (sup_le hQleW hSW)
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := by
    have hcQ : c ∈ Subgroup.normalizer (Q : Set G) := hAQ hcA
    have h1 : c ∈ Subgroup.normalizer (Q ⊔ S : Subgroup G) :=
      (Subgroup.inf_normalizer_le_normalizer_sup Q S) ⟨hcQ, hcS⟩
    have h2 : c ∈ Subgroup.normalizer (Subgroup.normalizer (S : Set G) : Set G) :=
      Subgroup.le_normalizer hcS
    exact (Subgroup.inf_normalizer_le_normalizer_inf (H := Q ⊔ S)
      (K := Subgroup.normalizer (S : Set G))) ⟨h1, h2⟩
  have hcommK : ⁅K, Subgroup.zpowers c⁆ ≤ S :=
    commutator_zpowers_le_of_forall hcS fun x hx =>
      commutatorElement_mem_of_mem_sup h hJ h1523 hcS hQ0S hSY x (hKW hx)
  have hR3 : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1)
      (by simpa using (zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).2.1)
  have h3S : ¬ 3 ∣ Nat.card S :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hS2 Nat.prime_three (by norm_num)
  have hdec : K ⊓ Subgroup.centralizer (Subgroup.zpowers c : Set G) ⊔ S = K :=
    CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le (p := 3) (X := K) (N := S)
      (R := Subgroup.zpowers c) hSK (Subgroup.zpowers_le.mpr hcK)
      (Subgroup.zpowers_le.mpr hcS) hR3 h3S hcommK
  let U : Subgroup G := K ⊓ Subgroup.centralizer (Subgroup.zpowers c : Set G)
  have hUK : U ≤ K := inf_le_left
  have hUQS : U ≤ Q ⊔ S := hUK.trans inf_le_left
  have hUNS : U ≤ Subgroup.normalizer (S : Set G) := hUK.trans inf_le_right
  have hU2 : IsPGroup 2 U := hS2Q.to_le hUQS
  have hUSne : ¬ U ≤ S := by
    intro hle
    have hKS : K ≤ S := by
      rw [← hdec]
      exact sup_le hle le_rfl
    exact absurd hSKlt (not_lt_of_ge hKS)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    have h1 : A ≤ Subgroup.normalizer (Q ⊔ S : Subgroup G) :=
      (le_inf hAQ hAS).trans (Subgroup.inf_normalizer_le_normalizer_sup Q S)
    have h2 : A ≤ Subgroup.normalizer (Subgroup.normalizer (S : Set G) : Set G) :=
      hAS.trans Subgroup.le_normalizer
    exact (le_inf h1 h2).trans (Subgroup.inf_normalizer_le_normalizer_inf
      (H := Q ⊔ S) (K := Subgroup.normalizer (S : Set G)))
  have hAc : A ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr h.isE27.1.1).trans
      (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hcA))
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    (le_inf hAK (hAc.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := K)
        (K := Subgroup.centralizer (Subgroup.zpowers c : Set G)))
  exact ⟨U, hUNS, hUQS, hU2,
    (inf_le_right : U ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G)), hAU, hUSne⟩

private theorem exists_spade_counterexample (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (h142 : Concl142S14) (hQ0 : Claim17Q0) {S J : Subgroup G}
    (hJY : J ≤ Y₀) (hS2 : IsPGroup 2 S) (hSQ : S ∈ scriptQ A (lB A))
    (hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hspade : ∀ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) → U ∈ scriptQ A (lB A) →
      IsPGroup 2 U → U ≤ Subgroup.normalizer (J : Set G) ∧
        (⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J → U ≤ S))
    (hQS : ¬ CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ≤ S) :
    ∃ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) ∧ U ∈ scriptQ A (lB A) ∧
      IsPGroup 2 U ∧ ⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J ∧ ¬ U ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 (Y₀ ⊔ S)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (Y₀ ⊔ S)
  have hNQ : Y₀ ⊔ S ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y₀ ⊔ S)
  obtain ⟨U, hUNS, hUQS, hU2, hUz, hAU, hUSne⟩ :=
    exists_centralizer_of_not_le h hJ h1523 hQ0 hJY hS2 hSQ hspade hQS
  have hUmem : U ∈ scriptQ A (lB A) := mem_scriptQ_of_le_centralizer h h142 hU2 hUz hAU
  obtain ⟨hUNJ, -⟩ := hspade U hUNS hUmem hU2
  exact ⟨U, hUNS, hUmem, hU2,
    commutator_le_pCoreOf_of_le_sup hJY hSJ hQ2 hNQ hUQS hUNJ, hUSne⟩

theorem pCoreOf_sup_le_of_spade (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h1523 : Item1523R) (h142 : Concl142S14) (hQ0 : Claim17Q0) {S J : Subgroup G}
    (hJY : J ≤ Y₀) (hS2 : IsPGroup 2 S) (hSQ : S ∈ scriptQ A (lB A))
    (hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 J)
    (hspade : ∀ U : Subgroup G, U ≤ Subgroup.normalizer (S : Set G) → U ∈ scriptQ A (lB A) →
      IsPGroup 2 U → U ≤ Subgroup.normalizer (J : Set G) ∧
        (⁅U, J⁆ ≤ CFSG.Open.pCoreOf 2 J → U ≤ S)) :
    CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ≤ S := by
  by_contra hQS
  obtain ⟨U, hUNS, hUmem, hU2, hUJ, hUSne⟩ :=
    exists_spade_counterexample h hJ h1523 h142 hQ0 hJY hS2 hSQ hSJ hspade hQS
  exact hUSne ((hspade U hUNS hUmem hU2).2 hUJ)

end CFSG.RankThree.PartTwo.Sec16.Ctr166
