module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts5
public import CFSG.Quasithin.Vol2.Ch11SecEK1E
public import CFSG.Quasithin.Vol2.Ch11SecAKC4
public import CFSG.Quasithin.Vol2.Ch11G2Q8Siegel
public import CFSG.Quasithin.Vol2.Ch11SecAKC2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (pCoreOf_map_of_injective)

open EK1 in
theorem factTorusPointG2_holds : FactTorusPointG2 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU h hh u hu hu1 hhu hc
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have := finite_cayleyGroup (F := K)
  have h4 := four_le_card hn hK
  have hfix := SecA.factRadicalFixedG2_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hpt := factPointG2A_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hhU := mem_stabW_of_comm hfix hpt hc
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU1 := eq_U1_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU)
  subst hU1
  have hψ : Function.Injective (psiG hc0 hc1 π g) := psiG_injective hf hc0 hc1 g
  have hmem : h ∈ (stabQ (stdF K 1)).map (psiG hc0 hc1 π g) := by
    rw [map_stabQ_eq hf hc0 hc1 g]
    exact ⟨hh, hhU⟩
  obtain ⟨γ, hγ, rfl⟩ := hmem
  obtain ⟨a, s₁, hs₁, rfl⟩ := SecA.KC4.exists_g2T_mul_of_mem_stabQ_one hγ
  obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.mp hu
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, hf.ker] at ht
    exact hu1 (Subgroup.mem_bot.mp ht)
  have ha : a = 1 := by
    have h1 := congrArg f hhu
    rw [f_psiG hf, ht, G2Q8.g2Act_smul, g2Act_inv_apply, G2Q8.g2Act_smul, g2Act_mul_apply,
      mem_stabV0.mp hs₁, g2Act_g2T_eu, mul_one] at h1
    have h2 := congrArg (fun v => (g2Act g⁻¹ v) (.inl 0)) h1
    simp only [G2Q8.g2Act_smul, g2Act_inv_apply, Pi.smul_apply, smul_eq_mul] at h2
    simp only [eu, Pi.single_eq_same] at h2
    rw [mul_one] at h2
    exact Units.ext (by rw [Units.val_one]; exact mul_left_cancel₀ ht0 (by rw [mul_one]; exact h2))
  subst ha
  rw [show ((1 : Kˣ), (1 : Kˣ)) = 1 from rfl, map_one, one_mul] at *
  have hΓ1 := gammaW_one_eqG h4 hf hc0 hc1 g
  have hO : pCoreOf 2 (perfectCore (H ⊓ SecA.stabW
      (hf.pre (gmapG g (stdF K 1)).toAddSubgroup))) =
      (pCoreOf 2 (stabV0 K)).map (psiG hc0 hc1 π g) := by
    change pCoreOf 2 (SecS.gammaW H _) = _
    rw [hΓ1, pCoreOf_map_of_injective _ hψ]
  have hlev : ∀ s ∈ stabV0 K, levi1Mat (s₁ * s * s₁⁻¹ * s⁻¹) = 1 := by
    intro s hs
    have hk : psiG hc0 hc1 π g s ∈ perfectCore (H ⊓ SecA.stabW
        (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)) := by
      change _ ∈ SecS.gammaW H _
      rw [hΓ1]
      exact ⟨s, hs, rfl⟩
    have h1 := hc _ hk
    rw [hO] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hxe
    rw [← hψ hxe]
    exact (mem_pCoreOf_stabV0_iff.mp hx).2
  have hcen : levi1 ⟨s₁, hs₁⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro C
    obtain ⟨s, rfl⟩ := levi1_surjective C
    have h1 : levi1 (⟨s₁, hs₁⟩ * s * ⟨s₁, hs₁⟩⁻¹ * s⁻¹) = 1 :=
      Subtype.ext (by rw [levi1_apply]; exact hlev s.1 s.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hker : (⟨s₁, hs₁⟩ : ↥(stabV0 K)) ∈ (levi1 (F := K)).ker := eq_one_of_mem_center hcen
  obtain ⟨k, hk⟩ := isPGroup_ker_levi1 (F := K) ⟨_, hker⟩
  refine ⟨k, ?_⟩
  have h1 : s₁ ^ 2 ^ k = 1 := by
    have := congrArg (fun x : ↥(levi1 (F := K)).ker => ((x : ↥(stabV0 K)) : ↥(cayleyGroup K))) hk
    simpa using this
  rw [← map_pow, h1, map_one]

end CFSG.Quasithin.Vol2.Ch11.SecE
