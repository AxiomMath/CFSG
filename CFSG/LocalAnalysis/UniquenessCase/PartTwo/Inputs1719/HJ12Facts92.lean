module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Objects
public import Certificates.Certificate17292

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Sporadic.J2.Module12 (A12 B12)
open CFSG.GF2Type.Smith1979.GammaU (vecOf)
open HJBridge (grpOf J12x hjTauM)
open HJ12 (wordR hjTauc)

theorem hjInvolution_facts :
    ∀ t ∈ hjT1, orderOf t = 2 →
      rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers t)) < 6 →
        rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers t)) = 4 ∧
          ∃ s₁ ∈ fixV (Subgroup.zpowers t), ∃ s₂ ∈ fixV (Subgroup.zpowers t),
            (∃ l ∈ hjL0, l hjV2 = s₁) ∧ (∃ l ∈ hjL0, l hjV2 = s₂) ∧
              (∃ l ∈ hjL0, l hjV2 = s₁ * s₂) := by
  classical
  have h : HJ12.hjT1Check = true := Certificates.certificate17292.2
  simp only [HJ12.hjT1Check, HJ12.gensL, Bool.and_eq_true, gensOKN_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_closedCheck,
    CFSG.GF2Type.Smith1979.GammaU.native_enumGrp,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_orbitOf] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hg1, -⟩, -⟩, hc1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    hinv⟩ := h
  intro t ht ht2 hrk6
  obtain ⟨r, hr, htr⟩ := (HJBridge.mem_grpOf_iff hg1 hc1 t).1 ht
  have hcan := canon_of_mem_enumGrp hg1 hr
  have hr1 : r ≠ CFSG.GF2Type.Smith1979.GammaU.StepA.idR := by
    rintro rfl
    have h1 : t = 1 := HJBridge.rowsOf_unique htr HJBridge.rowsOf_one
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hr2 : CFSG.GF2Type.Smith1979.GammaU.StepA.mulR r r =
      CFSG.GF2Type.Smith1979.GammaU.StepA.idR := by
    have htt : t * t = 1 := by
      have h0 := pow_orderOf_eq_one t
      rw [ht2, pow_two] at h0
      exact h0
    have h1 := HJBridge.rowsOf_mul htr htr
    rw [htt] at h1
    refine rows_eq_of_rowsOf h1 HJBridge.rowsOf_one ⟨?_, mulR_lt hcan.2⟩ ⟨rfl, by decide⟩
    rw [CFSG.GF2Type.Smith1979.GammaU.StepA.mulR, Array.size_map, hcan.1]
  have hmem : r ∈ (CFSG.GF2Type.Smith1979.GammaU.Enum.enumGrp
      (HJ12.hj_t0Words.map wordR ++ [hjTauc])).filter HJ12.isInvol := by
    rw [List.mem_filter]
    refine ⟨hr, ?_⟩
    simp only [HJ12.isInvol, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
      CFSG.GF2Type.Smith1979.GammaU.StepA.native_mulR,
      CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR]
    exact ⟨hr1, hr2⟩
  have h1 := List.all_eq_true.1 hinv r hmem
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.any_eq_true] at h1
  have hfix := HJBridge.card_fixV_zpowers htr hcan.2
  rcases h1 with h64 | ⟨h256, s₁, hs₁, ho₁, s₂, hs₂, ho₂, ho₁₂⟩
  · exfalso
    have h6 : rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers t)) = 6 :=
      rk_commSub_eq_of_card_fixV (by norm_num) (by rw [hfix]; exact h64.trans (by norm_num))
    exact (Nat.ne_of_lt hrk6) h6
  · refine ⟨rk_commSub_eq_of_card_fixV (by norm_num)
        (by rw [hfix]; exact h256.trans (by norm_num)),
      Multiplicative.ofAdd (vecOf s₁), mem_fixV_of_mem_fixCodes htr hs₁,
      Multiplicative.ofAdd (vecOf s₂), mem_fixV_of_mem_fixCodes htr hs₂,
      HJBridge.exists_of_mem_orbitOf (by norm_num) (List.contains_iff_mem.1 ho₁),
      HJBridge.exists_of_mem_orbitOf (by norm_num) (List.contains_iff_mem.1 ho₂), ?_⟩
    obtain ⟨l, hl, hlv⟩ := HJBridge.exists_of_mem_orbitOf (p := 1024) (by norm_num)
      (List.contains_iff_mem.1 ho₁₂)
    refine ⟨l, hl, ?_⟩
    rw [show hjV2 = Multiplicative.ofAdd (vecOf 1024) from rfl, hlv,
      CFSG.GF2Type.Smith1979.GammaU.vecOf_xor, ofAdd_add]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
