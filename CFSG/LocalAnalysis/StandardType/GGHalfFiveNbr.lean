module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveStdSub
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveKbNb
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveNbrBasic
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveSl3Facts
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup
public import CFSG.LocalAnalysis.StandardType.GGPumpupBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

open scoped commutatorElement

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

theorem exists_nb (hL : GGLBalanceInput) :
    ∃ N : Subgroup G, GGNbr p B x (dPrime x φ₁ φ₂) (sl3four.map φ₁) (bElt φ₁ φ₂) N ∧
      sl3four.map φ₁ ≤ N ∧ sl3four.map φ₂ ≤ N := by
  have hp : p.Prime := by rw [h.nbr.2.1]; exact Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  have hpJ : p ∣ Nat.card (sl3four.map φ₁) := by
    rw [h.nbr.2.1, Subgroup.card_map_of_injective (f := φ₁) h.coords.inj₁, card_sl3four]
    norm_num
  obtain ⟨hNcomp, hLN, hxN, halt⟩ :=
    pumpup_of_stdSub (ggPumpupInput_of_lBalance hL) h.cfg.1 (stdSub_lb h) hpJ
      (rfl : dPrime x φ₁ φ₂ = Subgroup.closure {x, bElt φ₁ φ₂})
  set N : Subgroup G :=
    ggLayerClosure p (Subgroup.centralizer ({bElt φ₁ φ₂} : Set G)) (sl3four.map φ₁) with hNdef
  have hKN : sl3four.map φ₂ ≤ N := kb_le_of_pComponent h hNcomp hLN
  refine ⟨N, ?_, hLN, hKN⟩
  rcases halt with hnbr | hcore
  · exact hnbr
  ·
    exfalso
    set O : Subgroup G := LargeEvenPPrimeCoreOf p N with hOdef
    have hxne : x ≠ 1 := h.basic.2.2.2.2.1
    have hzx : Subgroup.zpowers x = Subgroup.zpowers (φ₂ (omegaBlock 5 4)) := by
      simpa using zpowers_x h
    have hxmem : x ∈ (Subgroup.zpowers (omegaBlock 5 4)).map φ₂ := by
      rw [MonoidHom.map_zpowers, ← hzx]
      exact Subgroup.mem_zpowers x
    obtain ⟨t, ht, hxt⟩ := Subgroup.mem_map.mp hxmem
    have ht1 : t ≠ 1 := by
      intro h1
      exact hxne (by rw [← hxt, h1, map_one])
    have hNO : N ≤ Subgroup.normalizer (O : Set G) := fun a ha =>
      mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer ha)
    have hOcop : Nat.Coprime 3 (Nat.card O) := by
      have hpc := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥N)
      rw [h.nbr.2.1] at hpc
      rw [hOdef, LargeEvenPPrimeCoreOf, h.nbr.2.1,
        Subgroup.card_map_of_injective (f := N.subtype) N.subtype_injective]
      simp only [LargeEvenPPrimeCore]
      exact hpc
    let Q : Subgroup (SpecialLinearGroup (Fin 6) F2) := sl3four ⊓ O.comap φ₂
    have hQs : Q ≤ sl3four := inf_le_left
    have hQmap : Q.map φ₂ ≤ O := (Subgroup.map_le_iff_le_comap).mpr inf_le_right
    have hQcop : Nat.Coprime (Nat.card Q) 3 := by
      have hdiv : Nat.card Q ∣ Nat.card O := by
        rw [← Subgroup.card_map_of_injective (f := φ₂) h.coords.inj₂]
        exact Subgroup.card_dvd_of_le hQmap
      exact (hOcop.coprime_dvd_right hdiv).symm
    have hQnorm : (Q.subgroupOf sl3four).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hQs]
      intro hh k hq hk
      change k * hh * k⁻¹ ∈ sl3four ⊓ O.comap φ₂
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · exact sl3four.mul_mem (sl3four.mul_mem hk (Subgroup.mem_inf.mp hq).1)
          (sl3four.inv_mem hk)
      · rw [Subgroup.mem_comap]
        have hkk : φ₂ k ∈ N := hKN (Subgroup.mem_map_of_mem φ₂ hk)
        have hqh : φ₂ hh ∈ O := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hq).2
        have hmem := ((Subgroup.mem_normalizer_iff.mp (hNO hkk)) (φ₂ hh)).mp hqh
        simpa only [map_mul, map_inv] using hmem
    have hQbot : Q = ⊥ := normal_coprime_eq_bot hQs hQnorm hQcop
    have hcent : ∀ s ∈ sl3four, t * s = s * t := by
      intro s hs
      have hsst : s * t * s⁻¹ * t⁻¹ ∈ Q := by
        change s * t * s⁻¹ * t⁻¹ ∈ sl3four ⊓ O.comap φ₂
        rw [Subgroup.mem_inf]
        refine ⟨?_, ?_⟩
        · have hω4 : omegaBlock 5 4 ∈ halfTorus 5 :=
            Subgroup.subset_closure
              (show omegaBlock 5 4 ∈ {t : SpecialLinearGroup (Fin 6) F2 |
                  ∃ k : Fin 5, k.val % 2 = 0 ∧ t = omegaBlock 5 k} from
                ⟨(4 : Fin 5), by norm_num, rfl⟩)
          have htT : t ∈ halfTorus 5 := Subgroup.zpowers_le.mpr hω4 ht
          have htN : sl3four.map (MulAut.conj t).toMonoidHom = sl3four :=
            map_sl3four_of_mem_halfTorus htT
          have hconj : t * s⁻¹ * t⁻¹ ∈ sl3four := by
            have hh := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom
              (sl3four.inv_mem hs)
            rw [htN] at hh
            change t * s⁻¹ * t⁻¹ ∈ sl3four
            exact hh
          simpa only [mul_assoc] using sl3four.mul_mem hs hconj
        · rw [Subgroup.mem_comap]
          have hsk : φ₂ s ∈ N := hKN (Subgroup.mem_map_of_mem φ₂ hs)
          have hcomm : ⁅φ₂ s, x⁆ ∈ (⁅N, Subgroup.zpowers x⁆ : Subgroup G) :=
            Subgroup.commutator_mem_commutator hsk (Subgroup.mem_zpowers x)
          have hcommO : ⁅φ₂ s, x⁆ ∈ O := hcore hcomm
          have heq : φ₂ (s * t * s⁻¹ * t⁻¹) = ⁅φ₂ s, x⁆ := by
            rw [commutatorElement_def]
            simp only [map_mul, map_inv, hxt]
          rwa [heq]
      have h1 : s * t * s⁻¹ * t⁻¹ = 1 := by
        rw [hQbot] at hsst
        simpa using hsst
      have h2 : s * t * s⁻¹ = t := by
        calc s * t * s⁻¹ = s * t * s⁻¹ * t⁻¹ * t := by group
          _ = 1 * t := by rw [h1]
          _ = t := one_mul t
      have hst : s * t = t * s := by
        calc s * t = s * t * s⁻¹ * s := by group
          _ = t * s := by rw [h2]
      exact hst.symm
    exact (not_centralizes_of_mem_zpowers_omega4 ht ht1) hcent

end GGHalfCtx

end CFSG.StandardType

end
