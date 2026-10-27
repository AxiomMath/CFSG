module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp

import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWChief
import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqDisp
public import CFSG.Quasithin.Background.D14Groups
public import CFSG.Quasithin.Recognition.Stroth.F112Tree
import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem str86_lhat_eq_sup_q1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) :
    L1 ⊔ S = L1 ⊔ Q1 L1 L2 S :=
  sup_eq_of_S_eq (eq_sup_pCoreOf_of_bender_left hI.hF.1 hI.hSB
    (Or.inr (Or.inl ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩)))

private theorem str86_pCoreOf_lhat_eq_q1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) :
    pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
  rw [str86_lhat_eq_sup_q1 hI]
  exact pCoreOf_sup_pCoreOf hI.hF.1

private theorem str86_z1_le_z2
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) :
    Z1 L1 L2 S ≤ Z2 L1 L2 S :=
  (str86_caseI_basics hI.hF hI.hSB
    ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩ hI.hB2 ⟨m, hI.hL2⟩
    hI.hZI).2.1

private theorem str86_z1_le_conjClosure
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) :
    Z1 L1 L2 S ≤ conjClosure (Z2 L1 L2 S) L1 :=
  (str86_z1_le_z2 hI).trans (le_conjClosure (Z2 L1 L2 S) L1)

private theorem str86_conjClosure_le_pCoreOf_lhat
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    conjClosure (Z2 L1 L2 S) L1 ≤ pCoreOf 2 (L1 ⊔ S) := by
  rw [str86_pCoreOf_lhat_eq_q1 hI]
  exact (str86_conjClosure_frame hI hZQ).1

private theorem str86_conjClosure_le_lhat
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S :=
  (str86_conjClosure_le_pCoreOf_lhat hI hZQ).trans (pCoreOf_le 2 (L1 ⊔ S))

private theorem str86_conjClosure_isPGroup
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1) := by
  have hQ1S : Q1 L1 L2 S ≤ S :=
    isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hI.hF.toW)
  exact hI.hF.1.h1.pgroup.to_le ((str86_conjClosure_frame hI hZQ).1.trans hQ1S)

private theorem str86_conjClosure_normalIn
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    IsNormalIn (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1) (conjClosure (Z2 L1 L2 S) L1) := by
  obtain ⟨-, hP1NV, -⟩ := str86_conjClosure_frame hI hZQ
  have hHnorm : L1 ⊔ S ≤
      Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    (str86_lhat_eq_sup_q1 hI).le.trans
      ((sup_le le_sup_left (pCoreOf_le 2 (P1 L1 L2 S))).trans hP1NV)
  exact ⟨le_rfl, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHnorm hg) x).mp hx⟩

private theorem str86_z1_normalIn_conjClosure
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) :
    IsNormalIn (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1) (Z1 L1 L2 S) := by
  have hHZ : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (str86_lhat_eq_sup_q1 hI).le.trans hI.hZI
  have hHN : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hHZ.trans (Subgroup.centralizer_le_normalizer _)
  exact ⟨str86_z1_le_conjClosure hI, fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHN hg) x).mp hx⟩

private theorem str86_mem_lhat_of_involution
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {t : G} (htP : t ∈ P1 L1 L2 S)
    (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1) : t ∈ L1 ⊔ S := by
  have ht1 : t ≠ 1 := fun h => htQ (h ▸ (Q1 L1 L2 S).one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hX2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  exact (str86_le_lhat_of_isPGroup hI hX2).1 (Subgroup.zpowers_le.mpr htP)
    (Subgroup.mem_zpowers t)

private theorem str86_isSzU3Quot_lhat
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) :
    IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
    Or.inr ⟨k, hI.hk, rfl, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have he : oTwoQuot ↥(L1 ⊔ S) ≃* oTwoQuot ↥L1 := by
    rw [str86_lhat_eq_sup_q1 hI]
    exact oTwoQuotSupEquiv hI.hF.1
  exact IsSzU3Quot.of_mulEquiv he hq

private theorem str86_between_z1_conjClosure_count_ne_zero
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {n : ℕ}
    (hser : F112W.IsChiefSeriesBetween (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
      (Z1 L1 L2 S) (conjClosure (Z2 L1 L2 S) L1) n) : n ≠ 0 := by
  rintro rfl
  have hUH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S := str86_conjClosure_le_lhat hI hZQ
  have hUQ : conjClosure (Z2 L1 L2 S) L1 ≤ pCoreOf 2 (L1 ⊔ S) :=
    str86_conjClosure_le_pCoreOf_lhat hI hZQ
  have hcomm : ⁅conjClosure (Z2 L1 L2 S) L1, oTwoUpper (L1 ⊔ S)⁆ ≤ Z1 L1 L2 S :=
    (F112W.isChiefSeriesBetween_zero_iff hUH hUQ (str86_z1_normalIn_conjClosure hI)
      (str86_conjClosure_normalIn hI hZQ) (str86_z1_le_conjClosure hI)).mp hser
  have hHZ : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (str86_lhat_eq_sup_q1 hI).le.trans hI.hZI
  have h6 : ⁅oTwoUpper (L1 ⊔ S), Z1 L1 L2 S⁆ ≤ ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((oTwoUpper_le (L1 ⊔ S)).trans hHZ)).le
  have h5 : ⁅oTwoUpper (L1 ⊔ S), conjClosure (Z2 L1 L2 S) L1⁆ ≤ Z1 L1 L2 S := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hbot : ⁅conjClosure (Z2 L1 L2 S) L1, oTwoUpper (L1 ⊔ S)⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_comm]
    have h := A4.commutator_le_of_oTwoUpper (A := oTwoUpper (L1 ⊔ S)) (N := ⊥)
      (B := Z1 L1 L2 S) (D := conjClosure (Z2 L1 L2 S) L1)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (str86_z1_le_conjClosure hI)
      (D14.exists_pow_mem_of_isPGroup (str86_conjClosure_isPGroup hI hZQ) le_rfl) h5 h6
    rwa [D14.oTwoUpper_oTwoUpper] at h
  apply str86_commutator_conjClosure_ne_bot hI hZQ
  exact le_bot_iff.mp hbot

private theorem str86_exists_noncentral_step_between_z1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    ∃ L' N' : Subgroup G, Z1 L1 L2 S ≤ L' ∧ N' ≤ conjClosure (Z2 L1 L2 S) L1 ∧
      IsChiefStep (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1) L' N' ∧
        ¬ IsCentralStep (L1 ⊔ S) L' N' := by
  obtain ⟨n, hser⟩ := F112W.exists_isChiefSeriesBetween (H := L1 ⊔ S)
    (U := conjClosure (Z2 L1 L2 S) L1) (W := Z1 L1 L2 S)
    (str86_z1_normalIn_conjClosure hI) (conjClosure (Z2 L1 L2 S) L1)
    (str86_conjClosure_normalIn hI hZQ) (str86_z1_le_conjClosure hI)
  have key : ∀ {N : Subgroup G} {n : ℕ},
      F112W.IsChiefSeriesBetween (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
        (Z1 L1 L2 S) N n → n ≠ 0 →
      ∃ L' N' : Subgroup G, Z1 L1 L2 S ≤ L' ∧ N' ≤ N ∧
        IsChiefStep (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1) L' N' ∧
          ¬ IsCentralStep (L1 ⊔ S) L' N' := by
    intro N n hs ha
    induction hs with
    | refl => exact absurd rfl ha
    | @central N L n hstep hc hs ih =>
        obtain ⟨L', N', hWL', hN'L, hstep', hnc⟩ := ih ha
        exact ⟨L', N', hWL', hN'L.trans hstep.2.2.1.le, hstep', hnc⟩
    | @noncentral N L n hstep hnc hs ih =>
        exact ⟨L, N, hs.le, le_rfl, hstep, hnc⟩
  exact key hser (str86_between_z1_conjClosure_count_ne_zero hI hZQ hser)

theorem str86_sq_le_relIndex_centralizerMod_z1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {t : G}
    (htP : t ∈ P1 L1 L2 S) (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1) :
    (2 ^ k) ^ 2 ≤ (centralizerMod (Z1 L1 L2 S) (conjClosure (Z2 L1 L2 S) L1)
      (Subgroup.zpowers t)).relIndex (conjClosure (Z2 L1 L2 S) L1) := by
  classical
  have hUH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S := str86_conjClosure_le_lhat hI hZQ
  have hU2 : IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1) :=
    str86_conjClosure_isPGroup hI hZQ
  have hX : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := str86_isSzU3Quot_lhat hI
  have htH : t ∈ L1 ⊔ S := str86_mem_lhat_of_involution hI htP htQ ht2
  have hAh : Subgroup.zpowers t ≤ L1 ⊔ S := Subgroup.zpowers_le.mpr htH
  have hA : ∀ a ∈ Subgroup.zpowers t, a * a ∈ pCoreOf 2 (L1 ⊔ S) := by
    intro a ha
    have ha2 : a * a = 1 := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have ht2z : t ^ (2 : ℤ) = 1 := by
        simpa [zpow_ofNat, pow_two] using ht2
      calc t ^ j * t ^ j = t ^ (j + j) := (zpow_add t j j).symm
        _ = (t ^ (2 : ℤ)) ^ j := by
            rw [show j + j = (2 : ℤ) * j by ring, zpow_mul]
        _ = 1 := by rw [ht2z, one_zpow]
    rw [ha2]
    exact (pCoreOf 2 (L1 ⊔ S)).one_mem
  have hAO : ¬ Subgroup.zpowers t ≤ pCoreOf 2 (L1 ⊔ S) := by
    intro hle
    have ht : t ∈ pCoreOf 2 (L1 ⊔ S) := hle (Subgroup.mem_zpowers t)
    rw [str86_pCoreOf_lhat_eq_q1 hI] at ht
    exact htQ ht
  obtain ⟨n, hser⟩ := F112W.exists_isChiefSeriesBetween (H := L1 ⊔ S)
    (U := conjClosure (Z2 L1 L2 S) L1) (W := Z1 L1 L2 S)
    (str86_z1_normalIn_conjClosure hI) (conjClosure (Z2 L1 L2 S) L1)
    (str86_conjClosure_normalIn hI hZQ) (str86_z1_le_conjClosure hI)
  have hn : n ≠ 0 := str86_between_z1_conjClosure_count_ne_zero hI hZQ hser
  have hper : ∀ L' N' : Subgroup G, Z1 L1 L2 S ≤ L' →
      IsChiefStep (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1) L' N' →
      ¬ IsCentralStep (L1 ⊔ S) L' N' →
      (2 ^ k) ^ 2 ≤ (centralizerMod L' N' (Subgroup.zpowers t)).relIndex N' := by
    intro L' N' _ hstep hnc
    exact sq_le_relIndex_centralizerMod_of_not_le hX hU2 hUH hstep hnc hAh hA hAO
  have hpow := pow_le_relIndex_centralizerMod_between (H := L1 ⊔ S)
    (U := conjClosure (Z2 L1 L2 S) L1) (W := Z1 L1 L2 S) (A := Subgroup.zpowers t)
    hUH hAh hper hser
  exact (le_self_pow (one_le_pow₀ (Nat.one_le_pow k 2 (by norm_num))) hn).trans hpow

theorem str86_false_of_commutator_conjClosure_le_z1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {t : G}
    (htP : t ∈ P1 L1 L2 S) (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1)
    (htV : ∀ v ∈ conjClosure (Z2 L1 L2 S) L1, t * v * t⁻¹ * v⁻¹ ∈ Z1 L1 L2 S) : False := by
  classical
  obtain ⟨L', N', hZ1L', hN'U, hstep, hnc⟩ :=
    str86_exists_noncentral_step_between_z1 hI hZQ
  have hUH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S := str86_conjClosure_le_lhat hI hZQ
  have hU2 : IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1) :=
    str86_conjClosure_isPGroup hI hZQ
  have hX : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := str86_isSzU3Quot_lhat hI
  have htH : t ∈ L1 ⊔ S := str86_mem_lhat_of_involution hI htP htQ ht2
  have hCH : centralizerMod L' (L1 ⊔ S) N' ≤ L1 ⊔ S := centralizerMod_le_left _ _ _
  have hCnorm : L1 ⊔ S ≤
      Subgroup.normalizer (centralizerMod L' (L1 ⊔ S) N' : Set G) :=
    le_normalizer_centralizerMod (D14.le_normalizer_of_isNormalIn hstep.2.1)
      Subgroup.le_normalizer (D14.le_normalizer_of_isNormalIn hstep.1)
  have hQ1C : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L' (L1 ⊔ S) N' :=
    Ch3z.pCoreOf_le_centralizerMod hUH hstep (isElemAbelian_chiefMod hstep hUH hU2)
  have htC : t ∈ centralizerMod L' (L1 ⊔ S) N' := by
    refine ⟨htH, (D14.le_normalizer_of_isNormalIn hstep.2.1) htH, fun u hu => ?_⟩
    exact hZ1L' (htV u (hN'U hu))
  have ht2pow : ∃ n : ℕ, t ^ 2 ^ n = 1 := ⟨1, by rw [pow_one, pow_two]; exact ht2⟩
  rcases eq_or_mem_pCoreOf_of_normal hX hCH hCnorm hQ1C with htop | hmem
  · apply hnc
    intro g hg x hx
    exact (mem_centralizerMod.mp (htop.symm ▸ hg)).2.2 x hx
  · apply htQ
    have ht : t ∈ pCoreOf 2 (L1 ⊔ S) := hmem t htC ht2pow
    rwa [str86_pCoreOf_lhat_eq_q1 hI] at ht

end CFSG.Quasithin.Stroth

end
