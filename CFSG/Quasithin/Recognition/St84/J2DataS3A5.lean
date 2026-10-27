module

public import CFSG.Quasithin.Recognition.St84.TransferS3A5Count
public import CFSG.Quasithin.Recognition.St84.TransferS3A5Setup
public import CFSG.Quasithin.Recognition.St84.J2LocalData
public import CFSG.Quasithin.Recognition.J2RecSplit
public import CFSG.GroupTheory.FixedPointFreeCommutator
public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem f112sa_twist_right {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hT : S3A5ParabolicId L1 L2 S) (hJ : S3A5J2Hyp L1 L2 S)
    (hS : ¬ S ≤ L2) {Zs : Subgroup H} (hZQ : Zs ≤ pCoreOf 2 (f112saP2' L1 L2 S))
    (hZn : f112saP1' L1 L2 S ≤ Subgroup.normalizer (Zs : Set H))
    (hZc : centerOf (S ⊓ f112saK L1 L2 S) ≤ Zs) :
    ∃ u ∈ S, u ∉ L2 ∧ u ^ 2 = 1 ∧ ∃ v ∈ pCoreOf 2 L2, v ^ 2 = 1 ∧
      v ∉ Subgroup.centralizer (pCoreOf 2 L2 : Set H) ∧ u * v = v * u := by
  have hSP1 : S ≤ f112P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)
  have hTL2 : S ⊓ f112saK L1 L2 S ≤ L2 := hT.T_eq.ge.trans inf_le_right
  obtain ⟨d, hdL, hd3⟩ := f112sa_exists_orderThree_L1 (L2 := L2) (S := S) h1
  have hdO : d ∈ oTwoPrime (f112saP1' L1 L2 S) := hT.L1_eq.le hdL
  have hdE : d ∈ f112saP1' L1 L2 S := oTwoPrime_le _ hdO
  have hfree : ∀ e ∈ pCoreOf 2 (f112saP1' L1 L2 S), e * d = d * e → e = 1 := by
    intro e he hed
    have hc : ⁅e, d⁆ ∈ (⊥ : Subgroup H) := by
      rw [show ⁅e, d⁆ = 1 by rw [commutatorElement_def, hed]; group]
      exact Subgroup.one_mem _
    exact Subgroup.mem_bot.mp (hJ.nat_left d hdO hd3 e he hc)
  have hdN : d ∈ Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
    f112sa_P1_le_normalizer_QS hF (f112sa_P1'_le_P1 hF.toW hdE)
  obtain ⟨u, huS, huL2, hu2, hud, -⟩ := (hT.twist hS).diag
  have hw : ⁅u, d⁆⁻¹ ∈ pCoreOf 2 (f112saP1' L1 L2 S) :=
    Subgroup.inv_mem _ (hT.QS_eq ▸ hud d hdL)
  obtain ⟨s, hsQ, hs⟩ := CFSG.exists_eq_conj_mul_inv_of_fixedPointFree hdN
    (fun t ht htd => hfree t ht (by
      calc t * d = d * t * d⁻¹ * d := by rw [htd]
        _ = d * t := by group)) _ hw
  have hsT : s ∈ S ⊓ f112saK L1 L2 S := f112sa_QS_le_T hF hsQ
  have h1' : u * d * u⁻¹ = s * d * s⁻¹ := by
    have h := congrArg (·⁻¹) hs
    simp only [commutatorElement_def, inv_inv] at h
    calc u * d * u⁻¹ = (u * d * u⁻¹ * d⁻¹) * d := by group
      _ = (d * s * d⁻¹ * s⁻¹)⁻¹ * d := by rw [h]
      _ = s * d * s⁻¹ := by group
  have hu'd : s⁻¹ * u * d = d * (s⁻¹ * u) := by
    calc s⁻¹ * u * d = s⁻¹ * (u * d * u⁻¹) * u := by group
      _ = s⁻¹ * (s * d * s⁻¹) * u := by rw [h1']
      _ = d * (s⁻¹ * u) := by group
  have hu'S : s⁻¹ * u ∈ S := S.mul_mem (S.inv_mem hsT.1) huS
  have hu'L2 : s⁻¹ * u ∉ L2 := fun h =>
    huL2 (by simpa using L2.mul_mem (hTL2 hsT) h)
  have hu'2 : (s⁻¹ * u) ^ 2 = 1 := by
    have huN : u ∈ Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
      f112sa_P1_le_normalizer_QS hF (hSP1 huS)
    have hsq : (s⁻¹ * u) ^ 2 ∈ pCoreOf 2 (f112saP1' L1 L2 S) := by
      have hu2' : u ^ 2 ∈ pCoreOf 2 (f112saP1' L1 L2 S) := hT.QS_eq ▸ hu2
      have hcj : u * s⁻¹ * u⁻¹ ∈ pCoreOf 2 (f112saP1' L1 L2 S) :=
        (Subgroup.mem_normalizer_iff.mp huN _).mp (Subgroup.inv_mem _ hsQ)
      have heq : (s⁻¹ * u) ^ 2 = s⁻¹ * (u * s⁻¹ * u⁻¹) * u ^ 2 := by
        simp only [pow_two]; group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsQ) hcj) hu2'
    refine hfree _ hsq ?_
    calc (s⁻¹ * u) ^ 2 * d = (s⁻¹ * u) * (s⁻¹ * u * d) := by simp only [pow_two]; group
      _ = (s⁻¹ * u) * (d * (s⁻¹ * u)) := by rw [hu'd]
      _ = (s⁻¹ * u * d) * (s⁻¹ * u) := by group
      _ = (d * (s⁻¹ * u)) * (s⁻¹ * u) := by rw [hu'd]
      _ = d * (s⁻¹ * u) ^ 2 := by simp only [pow_two]; group
  have hQA32 : Nat.card ↥(pCoreOf 2 (f112saP2' L1 L2 S)) = 32 := hJ.q8d8_right.1
  have hZA : Nat.card ↥(centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) = 2 :=
    (isQ8D8_extraspecial_facts hJ.q8d8_right).2.1
  have hT2 : IsPGroup 2 ↥(S ⊓ f112saK L1 L2 S) := hF.1.h1.pgroup.to_le inf_le_left
  have hT1 : S ⊓ f112saK L1 L2 S ≠ ⊥ := by
    intro hbot
    have hle := f112sa_QA_le_T hF
    rw [hbot, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hQA32
    norm_num at hQA32
  obtain ⟨z, hzZ, hz2, hz1⟩ := CFSG.QuasithinUnique.Setup.exists_involution_centerOf hT2 hT1
  have hZT : centerOf (S ⊓ f112saK L1 L2 S) = centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) := by
    refine Subgroup.eq_of_le_of_card_ge (f112sa_centerOf_T_le_P2' hF.toW) ?_
    rw [hZA]
    have hne : centerOf (S ⊓ f112saK L1 L2 S) ≠ ⊥ := fun h => hz1 (by
      rw [h] at hzZ
      exact Subgroup.mem_bot.mp hzZ)
    have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
    omega
  have hZT2 : Nat.card ↥(centerOf (S ⊓ f112saK L1 L2 S)) = 2 := hZT ▸ hZA
  have hzS : ∀ x ∈ S, z * x = x * z := by
    have hSN : S ≤ Subgroup.normalizer ((S ⊓ f112saK L1 L2 S : Subgroup H) : Set H) := by
      rw [← hT.T_eq]
      exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hF.1.h2.normalizes hx⟩
    exact commute_of_mem_centerOf_of_card_two hSN hZT2 hzZ
  have hzQS : z ∈ pCoreOf 2 (f112saP1' L1 L2 S) := (f112sa_centerOf_T_le_P1' hF hzZ).1
  have hvZs : d * z * d⁻¹ ∈ Zs := (Subgroup.mem_normalizer_iff.mp (hZn hdE) z).mp (hZc hzZ)
  have hvQ : d * z * d⁻¹ ∈ pCoreOf 2 L2 := hT.QA_eq ▸ hZQ hvZs
  refine ⟨s⁻¹ * u, hu'S, hu'L2, hu'2, d * z * d⁻¹, hvQ, ?_, ?_, ?_⟩
  · rw [conj_pow, hz2, mul_one, mul_inv_cancel]
  · intro hvC
    rw [hT.QA_eq] at hvC
    have hvZ : d * z * d⁻¹ ∈ centerOf (S ⊓ f112saK L1 L2 S) := by
      rw [hZT]
      exact ⟨hT.QA_eq ▸ hvQ, hvC⟩
    have hv1 : d * z * d⁻¹ ≠ 1 := fun h => hz1 (conj_eq_one_iff.mp h)
    have hvz : d * z * d⁻¹ = z :=
      (G64.eq_one_or_eq_of_card_two hZT2 hzZ hz1 hvZ).resolve_left hv1
    exact hz1 (hfree z hzQS (by
      calc z * d = d * z * d⁻¹ * d := by rw [hvz]
        _ = d * z := by group))
  · have hu'z : s⁻¹ * u * z = z * (s⁻¹ * u) := (hzS _ hu'S).symm
    have hu'di : s⁻¹ * u * d⁻¹ = d⁻¹ * (s⁻¹ * u) := by
      calc s⁻¹ * u * d⁻¹ = d⁻¹ * (d * (s⁻¹ * u)) * d⁻¹ := by group
        _ = d⁻¹ * (s⁻¹ * u * d) * d⁻¹ := by rw [hu'd]
        _ = d⁻¹ * (s⁻¹ * u) := by group
    calc s⁻¹ * u * (d * z * d⁻¹) = (s⁻¹ * u * d) * z * d⁻¹ := by group
      _ = d * (s⁻¹ * u * z) * d⁻¹ := by rw [hu'd]; group
      _ = d * z * (s⁻¹ * u * d⁻¹) := by rw [hu'z]; group
      _ = d * z * d⁻¹ * (s⁻¹ * u) := by rw [hu'di]; group

private theorem exists_complement_of_s3a5ParabolicId
    {L1 L2 S : Subgroup H} (hF : F112Hyp L1 L2 S) (h2 : VA5 L2) (hT : S3A5ParabolicId L1 L2 S)
    (hJ : S3A5J2Hyp L1 L2 S)
    (hinv : ∃ x ∈ pCoreOf 2 (f112saP1' L1 L2 S), x ∉ pCoreOf 2 (f112saP2' L1 L2 S) ∧
      x ^ 2 = 1) :
    ∃ K : Subgroup H, K ≤ L2 ∧ K ⊓ pCoreOf 2 L2 = ⊥ ∧ Nat.card K = 60 := by
  obtain ⟨x, hxQ, hxA, hx2⟩ := hinv
  have hq8 : IsQ8D8 ↥(pCoreOf 2 L2) := hT.QA_eq ▸ hJ.q8d8_right
  have hxL2 : x ∈ L2 := (hT.T_eq.ge (f112sa_QS_le_T hF hxQ)).2
  have hquot : Nonempty (OTwoQuot L2 ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e2⟩ := h2
    obtain ⟨e⟩ := F112J2.nonempty_psl_four_equiv_alt5
    exact ⟨e2.trans e⟩
  exact exists_complement_of_involution_of_le hq8.nonempty_mulEquiv_QM hT.charTwo_right hquot
    hxL2 (by rw [← pow_two]; exact hx2) (fun h => hxA (hT.QA_eq ▸ h))

theorem j2Data_of_s3a5ParabolicId {L1 L2 S : Subgroup H}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hT : S3A5ParabolicId L1 L2 S) (hJ : S3A5J2Hyp L1 L2 S)
    (hcard : Nat.card ↥(pCoreOf 2 (f112saP1' L1 L2 S)) = 2 ^ 6)
    (hinv : ∃ x ∈ pCoreOf 2 (f112saP1' L1 L2 S), x ∉ pCoreOf 2 (f112saP2' L1 L2 S) ∧
      x ^ 2 = 1)
    (hZs : ∃ Zs : Subgroup H, Zs ≤ pCoreOf 2 (f112saP2' L1 L2 S) ∧
      f112saP1' L1 L2 S ≤ Subgroup.normalizer (Zs : Set H) ∧
      centerOf (S ⊓ f112saK L1 L2 S) ≤ Zs) :
    J2LocalData L1 L2 S ∨ AutJ2LocalData L1 L2 S := by
  have hq8 : IsQ8D8 ↥(pCoreOf 2 L2) := hT.QA_eq ▸ hJ.q8d8_right
  have hsplit := exists_complement_of_s3a5ParabolicId hF h2 hT hJ hinv
  have hcL : Nat.card ↥(pCoreOf 2 L1) = 2 ^ 6 := by rw [hT.QS_eq]; exact hcard
  by_cases hS : S ≤ L2
  · exact Or.inl ⟨hT.plain hS, hq8, hsplit, hcL⟩
  obtain ⟨Zs, hZQ, hZn, hZc⟩ := hZs
  obtain ⟨hidx, hperm, -⟩ := hT.ext hS
  refine Or.inr ⟨?_, ?_, hq8, hsplit, f112sa_twist_right hF h1 hT hJ hS hZQ hZn hZc, hcL⟩
  ·
    have h := Subgroup.relIndex_mul_card (H := S ⊓ L2) (K := S)
    rw [hidx, inf_eq_left.mpr (inf_le_left : S ⊓ L2 ≤ S), hT.T_eq,
      f112sa_card_T_eq_QS hF h1 h2, hcard] at h
    rw [← h]
    norm_num
  ·
    rw [← sup_bigB_eq_sup_of_vs3 hF h1]
    exact hperm

end CFSG.Quasithin.F112R.St84
