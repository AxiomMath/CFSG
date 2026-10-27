module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagCases
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Closure

variable {G : Type} [Group G]

theorem le_normalizer_iSup_map_conj (E J : Subgroup G) :
    E ≤ Subgroup.normalizer
      ((⨆ (a : G) (_ : a ∈ E), J.map (MulAut.conj a).toMonoidHom : Subgroup G) : Set G) := by
  intro b hb
  have key : ∀ c ∈ E,
      (⨆ (a : G) (_ : a ∈ E), J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj c).toMonoidHom
        ≤ ⨆ (a : G) (_ : a ∈ E), J.map (MulAut.conj a).toMonoidHom := by
    intro c hc
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun a ha => ?_
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
    have hca : (MulAut.conj c).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (c * a)).toMonoidHom := by
      ext g
      simp [MulAut.conj_apply, mul_assoc]
    rw [hca]
    exact le_iSup₂ (f := fun (a : G) (_ : a ∈ E) => J.map (MulAut.conj a).toMonoidHom) (c * a)
      (Subgroup.mul_mem _ hc ha)
  exact CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_conjSub_le (key b hb)
    (key b⁻¹ (Subgroup.inv_mem _ hb))

theorem eq_iSup_map_conj_of_isQuasisimple {K J : Subgroup G} (hK : CFSG.Assembly.IsQuasisimple ↥K)
    (hJ : CFSG.Assembly.IsQuasisimple ↥J) (hJK : J ≤ K) :
    (⨆ (a : G) (_ : a ∈ K), J.map (MulAut.conj a).toMonoidHom) = K := by
  set N := ⨆ (a : G) (_ : a ∈ K), J.map (MulAut.conj a).toMonoidHom with hN
  have hNK : N ≤ K := by
    refine iSup₂_le fun a ha => ?_
    rintro _ ⟨j, hj, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact K.mul_mem (K.mul_mem ha (hJK hj)) (K.inv_mem ha)
  have hJN : J ≤ N := by
    refine le_trans ?_ (le_iSup₂ (f := fun (a : G) (_ : a ∈ K) =>
      J.map (MulAut.conj a).toMonoidHom) 1 (Subgroup.one_mem _))
    intro j hj
    exact ⟨j, hj, by simp⟩
  rcases ggLe_center_or_eq_of_normalized hK hNK (le_normalizer_iSup_map_conj K J) with h | h
  · exfalso
    apply CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple hJ
    exact (hJN.trans h).trans (Subgroup.centralizer_le hJK)
  · exact h

end Closure

section Nbr

theorem ggSixKdNbrInput_of_prime (hpJ : GGStdSubPrimeInput) : GGSixKdNbrInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx h65 d hd hdx hDK
  have hp : p.Prime := hctx.prime
  have : Fact p.Prime := ⟨hp⟩
  have hd1 : d ≠ 1 := fun h => hdx (h ▸ Subgroup.one_mem _)
  set K := ggKd p B x L D J d with hKdef
  have hK : IsComponentOf K (Subgroup.centralizer {d}) := h65 d hd hd1
  have hJK : J ≤ K := le_ggKd p B x L D J d
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hctx.j_comp.2.2
  have hpJ' : p ∣ Nat.card J := hpJ G p B x L D J hctx.thmI hctx.stdSub
  have hpK : p ∣ Nat.card K := hpJ'.trans (Subgroup.card_dvd_of_le hJK)
  have hxD : x ∈ D := hctx.x_mem_d
  have hxB : x ∈ B := hctx.sstar.2.1
  have hD : D = Subgroup.closure {x, d} :=
    (ggClosure_pair_eq hp hctx.card_d hxD hd hctx.sstar.2.2.1 (hctx.sstar.1.1.2 x hxB) hdx).symm
  have hKO : ¬ K ≤ CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({d} : Set G)) := by
    intro hle
    have hcop : Nat.Coprime p
        (Nat.card (CFSG.Open.lBalancePrimeCore p (Subgroup.centralizer ({d} : Set G)))) := by
      rw [CFSG.ComponentClassification.LBalance.primeCore_eq_map,
        Subgroup.card_map_of_injective (Subgroup.centralizer ({d} : Set G)).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop (hpK.trans (Subgroup.card_dvd_of_le hle))
  have hA : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) K :=
    (largeEvenPComponent_iff_lBalance p _ K).mpr
      ⟨hK.1, lBalanceIsPComponent_of_isComponentOf hK hKO⟩
  have hKL : K ≤ LargeEvenPLayer p (Subgroup.centralizer ({d} : Set G)) := le_sSup hA
  have hAJ : K ≤ ⨆ (a : G) (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({d} : Set G))),
      J.map (MulAut.conj a⁻¹).toMonoidHom := by
    calc K = ⨆ (a : G) (_ : a ∈ K), J.map (MulAut.conj a).toMonoidHom :=
          (eq_iSup_map_conj_of_isQuasisimple hK.2.2 hJq hJK).symm
      _ ≤ _ := by
        refine iSup₂_le fun a ha => ?_
        have h := le_iSup₂ (f := fun (a : G)
          (_ : a ∈ LargeEvenPLayer p (Subgroup.centralizer ({d} : Set G))) =>
            J.map (MulAut.conj a⁻¹).toMonoidHom) a⁻¹ (hKL (K.inv_mem ha))
        rwa [inv_inv] at h
  have hxA : ¬ (⁅K, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
    intro h
    have hOcop : Nat.Coprime p (Nat.card (LargeEvenPPrimeCoreOf p K)) := by
      rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hxCd : x ∈ Subgroup.centralizer ({d} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hctx.d_comm x hxD d hd)
    have hxN : x ∈ Subgroup.normalizer (K : Set G) :=
      mem_normalizer_of_le_component hK hJq hJK hxCd (hctx.le_centralizer_J hxD)
    have hxK : x ∈ Subgroup.centralizer (K : Set G) :=
      mem_centralizer_of_commutator_le_coprime hp hK.2.2 hpK hOcop
        (fun k hk => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer hk)) hxN h
    have hdK : d ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hK.1 hk)
    apply hDK
    rw [hD, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hxK
    · exact hdK
  exact ggNbr_of_pComponent hctx.thmI hctx.stdSub hpJ' hD hA hJK hAJ hxA

end Nbr

section Main


theorem ggSixInnerOnKdInput_of_prime (hN : GGInndiagNormalInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hpJ : GGStdSubPrimeInput) : GGSixInnerOnKdInput :=
  ggSixInnerOnKdInput_of_nbr hN hc₀ hc₁ hc₂ (ggSixKdNbrInput_of_prime hpJ)

theorem ggSixInndiagNormalInput_of_prime (hN : GGInndiagNormalInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hpJ : GGStdSubPrimeInput) (hJ : GGSixBstarInnerDiagJInput) : GGSixInndiagNormalInput :=
  ggSixInndiagNormalInput_of_nbr hN hc₀ hc₁ hc₂ (ggSixKdNbrInput_of_prime hpJ) hJ

end Main

end CFSG.StandardType
