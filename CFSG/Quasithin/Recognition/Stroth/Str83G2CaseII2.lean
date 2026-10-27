module

public import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
public import CFSG.Quasithin.Recognition.Stroth.BenderQrc
public import CFSG.Quasithin.Recognition.Stroth.Str83G3Frame2
public import CFSG.Quasithin.SteinbergCDChiefFactorTools

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a c : ℕ}

private theorem commutator_eq_bot_of_le_centralizer_of_odd {U P : Subgroup G}
    (hUe : IsElemAbelian 2 U) (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hgen : oTwoUpper P = P)
    (hZ : ⁅U, P⁆ ≤ Subgroup.centralizer (P : Set G)) :
    ⁅U, P⁆ = ⊥ := by
  have hPUcomm : P ≤ Subgroup.centralizer (U : Set G) := by
    rw [← hgen, oTwoUpper]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxP, hxodd⟩
    change x ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hxN : x ∈ Subgroup.normalizer (U : Set G) := hPU hxP
    let B : Subgroup G := ⁅U, Subgroup.zpowers x⁆
    have hBU : B ≤ U :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hxN)
    have hBP : B ≤ ⁅U, P⁆ :=
      Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hxP)
    have hBcomm : ∀ b ∈ B, ⁅b, x⁆ = 1 := by
      intro b hb
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hZ (hBP hb)) x hxP).symm
    have hxU : ∀ v ∈ U, x * v * x⁻¹ ∈ U := fun v hv =>
      (Subgroup.mem_normalizer_iff.mp hxN v).mp hv
    have hkey : ⁅u, x⁆ = 1 :=
      CFSG.Quasithin.SteinbergCD.commutator_mem_of_odd hUe hBU hxodd hxU
        (by intro w hw; rw [Subgroup.mem_bot.mp hw]; simp)
        (fun b hb => by simpa [Subgroup.mem_bot] using hBcomm b hb)
        (Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers x))
    exact commutatorElement_eq_one_iff_mul_comm.mp hkey
  have hUP : U ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.le_centralizer_iff.mpr hPUcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hUP

theorem no_chiefSeries_le_one_of_d11Hyp
    {G₁ G₂ T V M₂ : Subgroup G} (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hndual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hZcent : G₂ ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 G₂) : Set G))
    {c : ℕ} (hc : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) c)
    (hc1 : c ≤ 1) : False := by
  set U : Subgroup G := conjClosure V G₂ with hU
  have hUR₂ : U ≤ pCoreOf 2 G₂ := by
    rw [hU]
    refine conjClosure_le fun g hg v hv => ?_
    exact (Subgroup.mem_normalizer_iff.mp ((le_normalizer_pCoreOf 2 G₂) hg) v).mp
      (hVR₂ hv)
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup 2 G₂).to_le hUR₂
  interval_cases c
  · have hbot : ⁅U, oTwoUpper G₂⁆ = ⊥ := by
      simpa using D14.commutator_eq_bot_of_zero (H := G₂) (U := U) (N := U) hU2 hc rfl
    exact D15Proof.commutator_ne_bot h (hU ▸ hbot)
  · have hconcl := D15Proof.d15Concl5 h hnff hVR₂ hc hndual
    obtain ⟨-, hUe, -, hcomm, -, -⟩ := hconcl
    have hcomm' : ⁅U, oTwoUpper G₂⁆ ≤ centerOf (pCoreOf 2 G₂) := by
      rw [F6.twoResidual_eq_oTwoUpper] at hcomm
      simpa [hU] using hcomm
    have hUP_le_Z : ⁅U, oTwoUpper G₂⁆ ≤ omegaOneCenterOf (pCoreOf 2 G₂) := by
      intro y hy
      have hyR : y ∈ pCoreOf 2 G₂ :=
        (inf_le_left : centerOf (pCoreOf 2 G₂) ≤ pCoreOf 2 G₂) (hcomm' hy)
      have hyC : y ∈ Subgroup.centralizer (pCoreOf 2 G₂ : Set G) :=
        (inf_le_right : centerOf (pCoreOf 2 G₂) ≤
          Subgroup.centralizer (pCoreOf 2 G₂ : Set G)) (hcomm' hy)
      have hyU : y ∈ U := by
        have hPU : oTwoUpper G₂ ≤ Subgroup.normalizer (U : Set G) :=
          (oTwoUpper_le G₂).trans (le_normalizer_conjClosure V G₂)
        have hle : ⁅U, oTwoUpper G₂⁆ ≤ U :=
          Subgroup.le_normalizer_iff_commutator_le_left.mp hPU
        exact hle hy
      exact mem_omegaOneCenterOf hyR
        (fun z hz => Subgroup.mem_centralizer_iff.mp hyC z hz) (hUe.2 y hyU)
    have hUP_le_CP : ⁅U, oTwoUpper G₂⁆ ≤
        Subgroup.centralizer (oTwoUpper G₂ : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hpy := Subgroup.mem_centralizer_iff.mp
        (hZcent (oTwoUpper_le G₂ hp)) y (hUP_le_Z hy)
      exact hpy.symm
    have hgen : oTwoUpper (oTwoUpper G₂) = oTwoUpper G₂ :=
      CFSG.Quasithin.EmptyFaithfulMultiple.oTwoUpper_oTwoUpper G₂
    have hPU : oTwoUpper G₂ ≤ Subgroup.normalizer (U : Set G) :=
      (oTwoUpper_le G₂).trans (le_normalizer_conjClosure V G₂)
    have hbot : ⁅U, oTwoUpper G₂⁆ = ⊥ :=
      commutator_eq_bot_of_le_centralizer_of_odd hUe hPU hgen hUP_le_CP
    exact D15Proof.commutator_ne_bot h (hU ▸ hbot)

theorem no_chiefSeries_le_one_U_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ1Q2 : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hZ2cent : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    {c : ℕ}
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (conjClosure (Z1 L1 L2 S) (L2 ⊔ S))
      (conjClosure (Z1 L1 L2 S) (L2 ⊔ S)) c)
    (hc1 : c ≤ 1) : False := by
  have hB1 : VSzBig L1 ∨ VU3Big L1 := Or.inl ⟨a, ha, hSz⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hV : IsElemAbelian 2 (Z1 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    rw [hsup1]
    refine sup_le ?_ ?_
    · exact ((le_sup_left : L1 ≤ P1 L1 L2 S).trans
        ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))))
    · exact (Q1_le_centralizer_Z1 L1 L2 S).trans
        (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hC : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S :=
    inf_centralizer_z1_eq_q1_of_caseII hF hB hB1 hII
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdisp : ∀ t ∈ S, t * t ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
      t ∉ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
      (2 ^ (2 * a + 1)) ^ 2 ≤
        (Z1 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) := by
    intro t htS ht2 htC
    have htQ1 : t ∉ Q1 L1 L2 S := fun htQ =>
      htC (Q1_le_centralizer_Z1 L1 L2 S htQ)
    have htH : t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) htS
    have ht2Q1 : t * t ∈ Q1 L1 L2 S := by
      have htSC : t * t ∈ S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        ⟨S.mul_mem htS htS, ht2⟩
      rwa [hC] at htSC
    have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
      rw [hsup1]
      exact pCoreOf_sup_pCoreOf hF.1
    have hHc : ¬ L1 ⊔ S ≤
        ((L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) ⊔ pCoreOf 2 (L1 ⊔ S) := by
      rw [hpCore1]
      intro hle
      have hQ1C : Q1 L1 L2 S ≤
          (L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        le_inf (hQ1S.trans le_sup_right) (Q1_le_centralizer_Z1 L1 L2 S)
      have hHleC : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        (hle.trans (sup_le le_rfl hQ1C)).trans inf_le_right
      exact hII (by rwa [hsup1] at hHleC)
    obtain ⟨eSz⟩ := hSz
    have hX : (∃ b : ℕ, 1 ≤ b ∧ 2 ^ (2 * a + 1) = 2 ^ (2 * b + 1) ∧
        Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* CFSG.Open.Sz b)) ∨
        (∃ n : ℕ, 2 ≤ n ∧ 2 ^ (2 * a + 1) = 2 ^ n ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
            (Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) ∨
              Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃*
                CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)))) := by
      refine Or.inl ⟨a, ha, rfl, ?_⟩
      rw [hsup1]
      exact ⟨(oTwoQuotSupEquiv hF.1).trans eSz⟩
    exact sq_le_relIndex_centralizer_of_sq_mem hX
      (fun v hv => by rw [← pow_two]; exact hV.2 v hv) hHZ1 hHc htH
      (by rwa [hpCore1]) (by rwa [hpCore1])
  have hhab : ∀ A : Subgroup G, A ≤ S →
      (∀ x ∈ A, ∀ y ∈ A,
        x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) ∧
          x * x ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G)) →
      (A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex A ≤ 2 ^ (2 * a + 1) := by
    intro A hAS hA
    have hsq : ∀ x ∈ A, x ^ 2 ∈ Q1 L1 L2 S := by
      intro x hx
      rw [pow_two]
      have hxSC : x * x ∈ S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        ⟨S.mul_mem (hAS hx) (hAS hx), (hA x hx x hx).2⟩
      rwa [hC] at hxSC
    have hqU : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ (2 * a + 1)) :=
      Or.inl ⟨a, ha, rfl, hSz⟩
    have h := relIndex_inf_q1_le hF.1 hS1 hqU hAS hsq
    have hAinf : A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = A ⊓ Q1 L1 L2 S := by
      calc A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)
          = (A ⊓ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
            rw [inf_eq_left.mpr hAS]
        _ = A ⊓ (S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) := by rw [inf_assoc]
        _ = A ⊓ Q1 L1 L2 S := by rw [hC]
    rwa [hAinf]
  have hFF := not_isFFInt_of_disp hV hHZ1 hSyl1 hq hdisp hhab
  have hD11 : D11Hyp (L1 ⊔ S) (L2 ⊔ S) S (Z1 L1 L2 S) (borelOf L2 S ⊔ S) :=
    d11Hyp_of_caseII hF hB hB1 hL2 (by omega) hII
  have hVR₂ : Z1 L1 L2 S ≤ pCoreOf 2 (L2 ⊔ S) := by
    rwa [hpCore2]
  have hZcent : L2 ⊔ S ≤
      Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (L2 ⊔ S)) : Set G) := by
    rwa [hpCore2]
  exact no_chiefSeries_le_one_of_d11Hyp hD11 hFF.1 hFF.2 hVR₂ hZcent hc hc1

end CFSG.Quasithin.Stroth

end
