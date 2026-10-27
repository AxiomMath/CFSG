module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbEven

import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2E1
import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2F5
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth
import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans
import CFSG.Quasithin.Recognition.Stroth.L2ChiefNatural
import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexDisplacement
public import CFSG.Quasithin.Recognition.Stroth.Str86ZNotLeB2Core

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_e1_offender {L1 L2 S : Subgroup G} {k m : ℕ}
    {F : Type} [Field F] [Finite F] (hI : Str86AbHyp L1 L2 S k m F) {g : G}
    (hgZ : Z2 L1 L2 S ≤ MulAut.conj g • S) (hZg : MulAut.conj g • Z2 L1 L2 S ≤ S)
    (hnc : ¬ Z2 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S) :
    ¬ MulAut.conj g • Z2 L1 L2 S ≤ Q2 L1 L2 S ∧
      MulAut.conj g • Z2 L1 L2 S ⊔ Q2 L1 L2 S = S ∧
      Z2 L1 L2 S ⊔ MulAut.conj g • Q2 L1 L2 S = MulAut.conj g • S ∧
      IsChiefStep (L2 ⊔ Q2 L1 L2 S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      ¬ IsCentralStep (L2 ⊔ Q2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      (∀ z ∈ Z2 L1 L2 S, ∀ s ∈ S, ⁅z, s⁆ ∈ Z1 L1 L2 S) ∧
      ∃ A : Subgroup G, A ≤ S ∧ IsElemAbelian 2 A ∧
        (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ m ∧
        (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ m := by
  classical
  obtain ⟨hF, hSB, hk, hFc, hU3, hB2, hn, hL2, hZI⟩ := hI
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨m, hL2⟩
  obtain ⟨-, -, -, hSCZ2, -⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hQ2CZ : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) := SmithC27.isElemAbelian_omegaOneCenterOf _
  set W : Subgroup G := MulAut.conj g • Z2 L1 L2 S with hWdef
  set W' : Subgroup G := MulAut.conj g⁻¹ • Z2 L1 L2 S with hW'def
  have hmemW' : ∀ x, x ∈ W' ↔ g * x * g⁻¹ ∈ Z2 L1 L2 S := fun x => by
    rw [hW'def, mem_conj_smul_iff', inv_inv]
  have hWS : W ≤ S := hZg
  have hW'S : W' ≤ S := by
    intro x hx
    have h' := mem_conj_smul_iff'.mp (hgZ ((hmemW' x).mp hx))
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h'
  have hWe : IsElemAbelian 2 W := isElemAbelian_conj_smul hZ2e g
  have hW'e : IsElemAbelian 2 W' := isElemAbelian_conj_smul hZ2e g⁻¹
  have hgg : MulAut.conj g • W' = Z2 L1 L2 S := by
    rw [hW'def, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have hW'Q2 : ¬ W' ≤ Q2 L1 L2 S := by
    intro hle
    apply hnc
    intro z hz
    rw [mem_conj_smul_iff']
    refine hle ((hmemW' _).mpr ?_)
    have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rwa [e]
  have hCQ : ∀ X : Subgroup G, X ≤ S →
      X ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = X ⊓ Q2 L1 L2 S := by
    intro X hX
    rw [← hSCZ2, ← inf_assoc, inf_eq_left.mpr hX]
  have hWQ2 : ¬ W ≤ Q2 L1 L2 S := by
    intro hle
    apply hW'Q2
    have hW'C : W' ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : g * z * g⁻¹ ∈ W := by
        rw [hWdef, mem_conj_smul_iff']
        have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
        rwa [e]
      have h' := Subgroup.mem_centralizer_iff.mp (hQ2CZ (hle hz')) _ ((hmemW' x).mp hx)
      calc z * x = g⁻¹ * ((g * z * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * z * g⁻¹)) * g := by rw [h']
        _ = x * z := by group
    have h' : W' ≤ W' ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) := le_inf le_rfl hW'C
    rw [hCQ W' hW'S] at h'
    exact h'.trans inf_le_right
  have hrel1 : (Z2 L1 L2 S ⊓ Subgroup.centralizer (W : Set G)).relIndex (Z2 L1 L2 S) =
      (W' ⊓ Q2 L1 L2 S).relIndex W' := by
    have h' := Subgroup.relIndex_pointwise_smul (MulAut.conj g)
      (W' ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)) W'
    rw [conj_smul_inf_centralizer, hgg, hCQ W' hW'S] at h'
    exact h'
  have hrel2 : (Z2 L1 L2 S ⊓ Subgroup.centralizer (W' : Set G)).relIndex (Z2 L1 L2 S) =
      (W ⊓ Q2 L1 L2 S).relIndex W := by
    have h' := Subgroup.relIndex_pointwise_smul (MulAut.conj g)
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (W' : Set G)) (Z2 L1 L2 S)
    rw [conj_smul_inf_centralizer, hgg, ← hWdef, hCQ W hWS] at h'
    exact h'.symm
  have hF5 : ∃ A : Subgroup G, A ≤ S ∧ IsElemAbelian 2 A ∧
      (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ m ∧
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ m ∧
      IsChiefStep (L2 ⊔ Q2 L1 L2 S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      ¬ IsCentralStep (L2 ⊔ Q2 L1 L2 S) ⊥ (Z2 L1 L2 S) ∧
      (∀ z ∈ Z2 L1 L2 S, ∀ s ∈ S, ⁅z, s⁆ ∈ Z1 L1 L2 S) ∧
      (W ⊓ Q2 L1 L2 S).relIndex W = 2 ^ m ∧ (W' ⊓ Q2 L1 L2 S).relIndex W' = 2 ^ m := by
    by_cases hcase : (Z2 L1 L2 S ⊓ Subgroup.centralizer (W : Set G)).relIndex (Z2 L1 L2 S) ≤
        (W ⊓ Q2 L1 L2 S).relIndex W
    · obtain ⟨hk1, hz1, hst, hnc1, hq1⟩ :=
        str86_b2_f5 hF hSB hk hFc hU3 hB2 hn hL2 hZI hWS hWe hWQ2 hcase
      exact ⟨W, hWS, hWe, hk1, hz1, hst, hnc1, hq1, hk1, hrel1.symm.trans hz1⟩
    · have hcase' : (Z2 L1 L2 S ⊓ Subgroup.centralizer (W' : Set G)).relIndex (Z2 L1 L2 S) ≤
          (W' ⊓ Q2 L1 L2 S).relIndex W' := by
        rw [hrel2, ← hrel1]
        omega
      obtain ⟨hk1, hz1, hst, hnc1, hq1⟩ :=
        str86_b2_f5 hF hSB hk hFc hU3 hB2 hn hL2 hZI hW'S hW'e hW'Q2 hcase'
      exact ⟨W', hW'S, hW'e, hk1, hz1, hst, hnc1, hq1, hrel2.symm.trans hz1, hk1⟩
  obtain ⟨A, hAS, hAe, hkA, hzA, hst, hnc', hquad, hWrel, hW'rel⟩ := hF5
  have hsup : ∀ X : Subgroup G, X ≤ S → (X ⊓ Q2 L1 L2 S).relIndex X = 2 ^ m →
      X ⊔ Q2 L1 L2 S = S := by
    intro X hXS hXrel
    have hXN : X ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
      hXS.trans (le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S))
    have hle : X ⊔ Q2 L1 L2 S ≤ S := sup_le hXS hQ2S
    have hsec := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := X) (K := Q2 L1 L2 S) hXN).2
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _
      (le_sup_right : Q2 L1 L2 S ≤ X ⊔ Q2 L1 L2 S) hle
    rw [hsec, hXrel, str86_relIndex_q2_s hF.toW hSB hn hL2] at hmul
    have h1' : (X ⊔ Q2 L1 L2 S).relIndex S = 1 := by
      have h' : 2 ^ m * (X ⊔ Q2 L1 L2 S).relIndex S = 2 ^ m * 1 := by rw [hmul, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1')
  have hZQS : Z2 L1 L2 S ⊔ MulAut.conj g • Q2 L1 L2 S = MulAut.conj g • S := by
    have h' := congrArg (MulAut.conj g • ·) (hsup W' hW'S hW'rel)
    simp only [Subgroup.smul_sup, hgg] at h'
    exact h'
  exact ⟨hWQ2, hsup W hWS hWrel, hZQS, hst, hnc', hquad, A, hAS, hAe, hkA, hzA⟩

theorem str86_z2_natural_facts
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F)
    (hst : IsChiefStep (L2 ⊔ Q2 L1 L2 S) (Z2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hnc : ¬ IsCentralStep (L2 ⊔ Q2 L1 L2 S) ⊥ (Z2 L1 L2 S))
    (hq : ∀ z ∈ Z2 L1 L2 S, ∀ s ∈ S, ⁅z, s⁆ ∈ Z1 L1 L2 S)
    {A : Subgroup G} (hAS : A ≤ S) (hA : IsElemAbelian 2 A)
    (hAr : (A ⊓ Q2 L1 L2 S).relIndex A = 2 ^ m)
    (hZr : (Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G)).relIndex (Z2 L1 L2 S) = 2 ^ m) :
    Nat.card (Z2 L1 L2 S) = (2 ^ m) ^ 2 ∧ Nat.card (Z1 L1 L2 S) = 2 ^ m ∧
      (∀ x ∈ S, x ∉ Q2 L1 L2 S → ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ = Z1 L1 L2 S) ∧
      ⁅Z2 L1 L2 S, Q1 L1 L2 S⁆ = Z1 L1 L2 S := by
  classical
  obtain ⟨hF, hSB, hk, hFc, hU3, hB2, hm, hL2, hZI⟩ := hI
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨m, hL2⟩
  obtain ⟨-, hZ1Z2, -, -, hZ2CS⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hpH : pCoreOf 2 (L2 ⊔ Q2 L1 L2 S) = Q2 L1 L2 S := str86_pCoreOf_u3H hF.toW
  have hLH : IsL2Quot m (oTwoQuot ↥(L2 ⊔ Q2 L1 L2 S)) := str86_isL2Quot_u3H hF.toW hL2
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) := SmithC27.isElemAbelian_omegaOneCenterOf _
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := omegaOneCenterOf_le _
  have hZ2H : Z2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S := hZ2Q2.trans le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hQ1S : Q1 L1 L2 S ≤ S := F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hSH : S ≤ L2 ⊔ Q2 L1 L2 S := str86_s_le_u3H hF.toW hSB hm hL2
  have hHZ : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  have hQ2CZ : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hZcomm : ∀ x ∈ Z2 L1 L2 S, ∀ y ∈ Z2 L1 L2 S, x * y = y * x := fun x hx y hy =>
    A4.mul_comm_of_mem_omegaOneCenterOf hx hy
  have hnat := isNaturalChiefStep_of_eq hm hLH hZ2e hZ2H hst hnc hA (hAS.trans hSH)
    (by rw [centralizerMod_bot_eq]; exact hZr) (by rw [hpH]; exact hAr)
  have hcard := natCard_quotient_of_isNaturalChiefStep hnat
  rw [GaloisField.card 2 m (by omega)] at hcard
  have hZ2card : Nat.card (Z2 L1 L2 S) = (2 ^ m) ^ 2 := by
    rw [← Subgroup.relIndex_bot_left]
    exact hcard
  have hAN : A ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    hAS.trans (le_normalizer_q2_of_sylow (L1 := L1) (L2 := L2) (S := S))
  have hAQS : A ⊔ Q2 L1 L2 S = S := by
    have hle : A ⊔ Q2 L1 L2 S ≤ S := sup_le hAS hQ2S
    have hsec := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
      (H := A) (K := Q2 L1 L2 S) hAN).2
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _
      (le_sup_right : Q2 L1 L2 S ≤ A ⊔ Q2 L1 L2 S) hle
    rw [hsec, hAr, str86_relIndex_q2_s hF.toW hSB hm hL2] at hmul
    have h1' : (A ⊔ Q2 L1 L2 S).relIndex S = 1 := by
      have h' : 2 ^ m * (A ⊔ Q2 L1 L2 S).relIndex S = 2 ^ m * 1 := by rw [hmul, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1')
  have hCA : Z2 L1 L2 S ⊓ Subgroup.centralizer (A : Set G) = Z1 L1 L2 S := by
    rw [← hZ2CS]
    refine le_antisymm (fun z hz => ?_) (inf_le_inf_left _ (Subgroup.centralizer_le hAS))
    obtain ⟨hzZ, hzA⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨hzZ, ?_⟩
    have hle : A ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun q hq => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ((Subgroup.mem_centralizer_iff.mp hzA) a ha).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (Subgroup.mem_centralizer_iff.mp (hQ2CZ hq) y hzZ)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h' := hle (by rw [hAQS]; exact hs)
    rw [Subgroup.mem_centralizer_iff] at h'
    exact (h' z (Set.mem_singleton z)).symm
  have hZ1rel : (Z1 L1 L2 S).relIndex (Z2 L1 L2 S) = 2 ^ m := by
    rw [← hCA]
    exact hZr
  have hZ1card : Nat.card (Z1 L1 L2 S) = 2 ^ m := by
    have h' := Subgroup.relIndex_mul_card (H := Z1 L1 L2 S) (K := Z2 L1 L2 S)
    rw [hZ1rel, inf_eq_left.mpr hZ1Z2, hZ2card, pow_two] at h'
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  have hx : ∀ x ∈ S, x ∉ Q2 L1 L2 S → ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ = Z1 L1 L2 S := by
    intro x hxS hxQ
    have hxsq : x * x ∈ pCoreOf 2 (L2 ⊔ Q2 L1 L2 S) := by
      rw [hpH]
      exact str86_sq_mem_q2 hF.toW hSB hm hL2 hxS
    have hxO : x ∉ pCoreOf 2 (L2 ⊔ Q2 L1 L2 S) := by
      rwa [hpH]
    have hlow := l2ChiefSectionRep_pow_le_relIndex_centralizerMod hm hLH hZ2e.isPGroup hZ2H hst
      hnc (hSH hxS) hxsq hxO
    have hCx : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
        Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [centralizerMod_bot_eq, hCx, inf_comm, Subgroup.inf_relIndex_right] at hlow
    have hZ1C : Z1 L1 L2 S ≤ Subgroup.centralizer ({x} : Set G) ⊓ Z2 L1 L2 S := by
      rw [← hZ2CS, inf_comm]
      exact inf_le_inf_right _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxS))
    have hup : (Subgroup.centralizer ({x} : Set G)).relIndex (Z2 L1 L2 S) ≤ 2 ^ m := by
      rw [← Subgroup.inf_relIndex_right, ← hZ1rel]
      exact Subgroup.relIndex_le_of_le_left hZ1C (CFSG.Quasithin.D15Proof.relIndex_ne_zero _ _)
    have hcnt := CFSG.Quasithin.H13.A7.card_range_commutator_eq_relIndex hZcomm (hHZ (hSH hxS))
    rw [le_antisymm hup hlow] at hcnt
    have hle : ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ ≤ Z1 L1 L2 S :=
      Subgroup.commutator_le.mpr fun z hz y hy => hq z hz y (Subgroup.zpowers_le.mpr hxS hy)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hZ1card, ← hcnt]
    refine Nat.card_mono (Set.toFinite _) ?_
    rintro _ ⟨v, rfl⟩
    dsimp only
    have e : (v : G) * x * (v : G)⁻¹ * x⁻¹ = ⁅(v : G), x⁆ := (commutatorElement_def _ _).symm
    rw [e]
    exact Subgroup.commutator_mem_commutator v.2 (Subgroup.mem_zpowers x)
  have hQ1Q2 : ¬ Q1 L1 L2 S ≤ Q2 L1 L2 S := by
    intro hle
    have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
    have hchar : CharTwo (P1 L1 L2 S) := F1.parabolic_charTwo hR
    have hZC : Z2 L1 L2 S ≤ Subgroup.centralizer (Q1 L1 L2 S : Set G) :=
      Subgroup.le_centralizer_iff.mpr (hle.trans hQ2CZ)
    have hZP1 : Z2 L1 L2 S ≤ P1 L1 L2 S :=
      (hZ2Q2.trans hQ2S).trans ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
    have hZQ1 : Z2 L1 L2 S ≤ Q1 L1 L2 S := fun z hz =>
      hchar (Subgroup.mem_inf.mpr ⟨hZP1 hz, hZC hz⟩)
    have hZZ1 : Z2 L1 L2 S ≤ Z1 L1 L2 S := fun v hv =>
      Subgroup.subset_closure ⟨⟨hZQ1 hv, hZC hv⟩, hZ2e.2 v hv⟩
    have hc := Subgroup.card_le_of_le hZZ1
    rw [hZ2card, hZ1card] at hc
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    nlinarith
  obtain ⟨x, hxQ1, hxQ2⟩ := Set.not_subset.mp hQ1Q2
  refine ⟨hZ2card, hZ1card, hx, le_antisymm ?_ ?_⟩
  · exact Subgroup.commutator_le.mpr fun z hz y hy => hq z hz y (hQ1S hy)
  · rw [← hx x (hQ1S hxQ1) hxQ2]
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hxQ1)

theorem str86_e1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {g : G}
    (hgZ : Z2 L1 L2 S ≤ MulAut.conj g • S) (hZg : MulAut.conj g • Z2 L1 L2 S ≤ S)
    (hnc : ¬ Z2 L1 L2 S ≤ MulAut.conj g • Q2 L1 L2 S) :
    ¬ MulAut.conj g • Z2 L1 L2 S ≤ Q2 L1 L2 S ∧
      MulAut.conj g • Z2 L1 L2 S ⊔ Q2 L1 L2 S = S ∧
      Nat.card (Z2 L1 L2 S) = (2 ^ m) ^ 2 ∧ Nat.card (Z1 L1 L2 S) = 2 ^ m ∧
      ⁅Z2 L1 L2 S, MulAut.conj g • Z2 L1 L2 S⁆ = Z1 L1 L2 S ∧
      MulAut.conj g • Z1 L1 L2 S = Z1 L1 L2 S ∧
      MulAut.conj g • Z2 L1 L2 S ⊓ Q2 L1 L2 S = Z1 L1 L2 S ∧
      ⁅Z2 L1 L2 S, Q1 L1 L2 S⁆ = Z1 L1 L2 S := by
  classical
  obtain ⟨hWQ2, hWQS, hZQS, hst, hnc', hquad, A, hAS, hAe, hkA, hzA⟩ :=
    str86_e1_offender hI hgZ hZg hnc
  obtain ⟨hZ2card, hZ1card, hx, hZQ1⟩ :=
    str86_z2_natural_facts hI hst hnc' hquad hAS hAe hkA hzA
  obtain ⟨hF, hSB, hk, hFc, hU3, hB2, hm, hL2, hZI⟩ := hI
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have h2 : VL2 L2 := ⟨m, hL2⟩
  obtain ⟨-, hZ1Z2, -, -, hZ2CS⟩ := str86_caseI_basics hF hSB h1 hB2 h2 hZI
  have hZ2Q2 : Z2 L1 L2 S ≤ Q2 L1 L2 S := omegaOneCenterOf_le _
  have hQ2CZ : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  set W' : Subgroup G := MulAut.conj g⁻¹ • Z2 L1 L2 S with hW'def
  have hmemW' : ∀ x, x ∈ W' ↔ g * x * g⁻¹ ∈ Z2 L1 L2 S := fun x => by
    rw [hW'def, mem_conj_smul_iff', inv_inv]
  have hW'S : W' ≤ S := by
    intro x hx
    have h' := mem_conj_smul_iff'.mp (hgZ ((hmemW' x).mp hx))
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h'
  have hW'Q2 : ¬ W' ≤ Q2 L1 L2 S := by
    intro hle
    apply hnc
    intro z hz
    rw [mem_conj_smul_iff']
    refine hle ((hmemW' _).mpr ?_)
    have e : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rwa [e]
  have hgg : MulAut.conj g • W' = Z2 L1 L2 S := by
    rw [hW'def, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have hcommX : ∀ X : Subgroup G, X ≤ S → ¬ X ≤ Q2 L1 L2 S →
      ⁅Z2 L1 L2 S, X⁆ = Z1 L1 L2 S := by
    intro X hXS hXQ
    obtain ⟨w, hwX, hwQ⟩ := Set.not_subset.mp hXQ
    refine le_antisymm ?_ ?_
    · exact Subgroup.commutator_le.mpr fun z hz y hy => hquad z hz y (hXS hy)
    · rw [← hx w (hXS hwX) hwQ]
      exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hwX)
  have hZW := hcommX _ hZg hWQ2
  have hsmul : ∀ H K : Subgroup G,
      MulAut.conj g • ⁅H, K⁆ = ⁅MulAut.conj g • H, MulAut.conj g • K⁆ := fun H K =>
    Subgroup.map_commutator H K (MulDistribMulAction.toMonoidEnd (MulAut G) G (MulAut.conj g))
  have hZ1g : MulAut.conj g • Z1 L1 L2 S = Z1 L1 L2 S := by
    rw [← hcommX W' hW'S hW'Q2, hsmul, hgg, Subgroup.commutator_comm, hcommX W' hW'S hW'Q2]
    exact hZW
  have hWQ : MulAut.conj g • Z2 L1 L2 S ⊓ Q2 L1 L2 S = Z1 L1 L2 S := by
    refine le_antisymm (fun w hw => ?_) (le_inf (fun z hz => ?_) (hZ1Z2.trans hZ2Q2))
    · obtain ⟨hwW, hwQ⟩ := Subgroup.mem_inf.mp hw
      have hw' : g⁻¹ * w * g ∈ Z2 L1 L2 S := mem_conj_smul_iff'.mp hwW
      have hle : Z2 L1 L2 S ⊔ MulAut.conj g • Q2 L1 L2 S ≤
          Subgroup.centralizer ({w} : Set G) := by
        refine sup_le (fun z hz => ?_) (fun q hq => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff.mp hy]
          exact (Subgroup.mem_centralizer_iff.mp (hQ2CZ hwQ) z hz).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff.mp hy]
          have h' := Subgroup.mem_centralizer_iff.mp (hQ2CZ (mem_conj_smul_iff'.mp hq)) _ hw'
          calc w * q = g * ((g⁻¹ * w * g) * (g⁻¹ * q * g)) * g⁻¹ := by group
            _ = g * ((g⁻¹ * q * g) * (g⁻¹ * w * g)) * g⁻¹ := by rw [h']
            _ = q * w := by group
      have hwC : w ∈ Subgroup.centralizer ((MulAut.conj g • S : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        rw [← hZQS] at hs
        have h' := hle hs
        rw [Subgroup.mem_centralizer_iff] at h'
        exact (h' w (Set.mem_singleton w)).symm
      have hmem : w ∈ MulAut.conj g • (Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G)) := by
        rw [conj_smul_inf_centralizer]
        exact Subgroup.mem_inf.mpr ⟨hwW, hwC⟩
      rwa [hZ2CS, hZ1g] at hmem
    · rw [← hZ1g] at hz
      exact mem_conj_smul_iff'.mpr (hZ1Z2 (mem_conj_smul_iff'.mp hz))
  exact ⟨hWQ2, hWQS, hZ2card, hZ1card, hZW, hZ1g, hWQ, hZQ1⟩

theorem str86E1_holds :
    Str86E1 :=
  fun _ _ _ _ _ _ _ _ _ _ _ hI _ hgZ hZg hnc => str86_e1 hI hgZ hZg hnc

end CFSG.Quasithin.Stroth

end
