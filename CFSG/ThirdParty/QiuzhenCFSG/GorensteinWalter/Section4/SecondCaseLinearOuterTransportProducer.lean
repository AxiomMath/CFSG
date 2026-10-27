module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OuterInvolutionFromSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2ActionOuterImage
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOuterTransportEndpoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2ReflectedToriPairAlignment
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26Core
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The aligned outer subgroup in the linear second case

The failure of ambient-Sylow containment supplies an outer involution in the
selected maximal subgroup.  Its semilinear image and the image of the
distinguished component involution form an outer/inner pair in `PGL₂`; the
reflected-torus alignment and Theorem 2.6 product-centralizer conjugator then
produce the odd subgroup needed by the source's final contradiction.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix

universe u

/-- Produce the odd reflected subgroup in `U` from an ambient Sylow element
outside the selected component. -/
public theorem secondCase_linear_outer_transported_subgroup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (F : Subgroup G)
    (hF_eq : F = c.FU ⊓ Subgroup.centralizer
      (((SE : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G))
    (hNF : Subgroup.normalizer (F : Set G) = w.M)
    (hSnotE : ¬ (c.S : Subgroup G) ≤ d.E)
    (hm2 : 2 ≤ c.m) :
    ∃ r : w.M, ∃ R : Subgroup G,
      r ∈ (SM : Subgroup w.M) ∧
      IsInvolution (r : G) ∧
      (r : G) ∉ d.E ∧
      Commute c.t (r : G) ∧
      IsCyclic R ∧
      Odd (Nat.card R) ∧
      (Nat.card R = (Nat.card K - 1) / 2 ∨
        Nat.card R = (Nat.card K + 1) / 2) ∧
      R ≤ c.U ∧
      (∀ x : G, x ∈ R →
        (r : G) * x * (r : G)⁻¹ = x⁻¹) := by
  classical
  obtain ⟨r, hrSM, hrI, hrE, htr⟩ :=
    secondCase_psl2_aligned_outer_involution c w d K hK e SM hSMleS SE
      hSEamb F hF_eq hNF hSnotE
  obtain ⟨ad⟩ := secondCase_psl2_action_data hmin c w d K hK e
  let i : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
  have hiinj : Function.Injective i := SemidirectProduct.inl_injective
  obtain ⟨r0, hr0, hr0J⟩ :=
    secondCase_psl2_action_outer_image w d K ad r hrI hrE
  have hrMpow : r ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hrI.2
  have hr0pow : r0 ^ 2 = 1 := by
    apply hiinj
    calc
      (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) (r0 ^ 2) =
          (SemidirectProduct.inl r0) ^ 2 := by simp
      _ = (ad.f r) ^ 2 := by rw [hr0]
      _ = ad.f (r ^ 2) := by rw [map_pow]
      _ = 1 := by rw [hrMpow]; simp
      _ = (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) 1 := by simp
  have hr0ne : r0 ≠ 1 := by
    intro h
    apply hr0J
    rw [h]
    exact (commutator (PGL2 K)).one_mem
  have hr0I : IsInvolution r0 := ⟨hr0ne, hr0pow⟩
  let tE : d.E := ⟨c.t, d.t_mem_E⟩
  let tM : w.M := ⟨c.t, d.E_component.1 d.t_mem_E⟩
  let t0 : PGL2 K := secondCasePSL2ComponentPGLMap d K ad tE
  have ht0 : ad.f tM = SemidirectProduct.inl t0 := by
    simpa [t0, tE, tM] using
      secondCase_psl2_action_on_component_eq_inl w d K ad tE
  have htMne : tM ≠ 1 := by
    intro h
    apply c.t_involution.1
    exact congrArg Subtype.val h
  have htMpow : tM ^ 2 = 1 := by
    apply Subtype.ext
    simpa [tM, pow_two] using c.t_involution.2
  have ht0pow : t0 ^ 2 = 1 := by
    apply hiinj
    calc
      (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) (t0 ^ 2) =
          (SemidirectProduct.inl t0) ^ 2 := by simp
      _ = (ad.f tM) ^ 2 := by rw [ht0]
      _ = ad.f (tM ^ 2) := by rw [map_pow]
      _ = 1 := by rw [htMpow]; simp
      _ = (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) 1 := by simp
  have ht0ne : t0 ≠ 1 := by
    intro h
    have hftM : ad.f tM = 1 := by rw [ht0, h]; simp
    have htMker : tM ∈ ad.f.ker := MonoidHom.mem_ker.mpr hftM
    have htMorder : orderOf tM = 2 := orderOf_eq_prime htMpow htMne
    have hdiv : 2 ∣ Nat.card ad.f.ker := by
      simpa [htMorder] using
        (Subgroup.orderOf_dvd_natCard ad.f.ker htMker)
    exact ad.ker_odd.not_two_dvd_nat hdiv
  have htI : IsInvolution t0 := by
    exact ⟨ht0ne, ht0pow⟩
  have hrtM : Commute r tM := by
    show r * tM = tM * r
    apply Subtype.ext
    exact htr.eq.symm
  have hrt0 : Commute r0 t0 := by
    have hcomm := hrtM.map ad.f
    have hcomm' :
        (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) r0 *
            (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) t0 =
          (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) t0 *
            (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) r0 := by
      simpa [hr0, ht0] using hcomm.eq
    apply hiinj
    simpa only [map_mul] using hcomm'
  have hcard : 3 < Nat.card K :=
    secondCase_psl2_field_card_gt_three d K hK e
  have htJ : t0 ∈ commutator (PGL2 K) := by
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K ad.primePower hcard]
    change t0 ∈ Matrix.ProjectiveSpecialLinearGroup.toPGL.range
    refine ⟨ad.modelEquiv.some
      (QuotientGroup.mk' (Subgroup.center d.E) tE), ?_⟩
    exact (secondCase_psl2_componentPGLMap_apply d K ad tE).symm
  obtain ⟨P, m, eP, T, a, hrT, htT⟩ :=
    pgl2_reflected_tori_pair_alignment K hK hcard r0 t0
      hr0I htI hrt0 hr0J htJ
  have hte : c.t ≠ (r : G) := by
    intro h
    apply hrE
    rw [← h]
    exact d.t_mem_E
  obtain ⟨y, hyI, hyconj0, hyC⟩ :=
    exists_theorem26_product_centralizer_conjugator hmin c hm2
      (r : G) hrI htr hte
  have hyinv : y⁻¹ = y := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hyI.2
  have hy2 : y * y = 1 := by
    simpa [pow_two] using hyI.2
  have hyconj : y * (r : G) * y⁻¹ = c.t := by
    calc
      y * (r : G) * y⁻¹ =
          y * (y * c.t * y⁻¹) * y⁻¹ := by rw [← hyconj0]
      _ = (y * y) * c.t * (y * y) := by rw [hyinv]; group
      _ = c.t := by rw [hy2]; simp
  let CE : Subgroup G :=
    Subgroup.centralizer ({(r : G)} : Set G) ⊓ d.E
  let R0 : Subgroup G := ⁅Subgroup.zpowers c.t, CE⁆
  let Ry : Subgroup G := R0.map (MulAut.conj y).toMonoidHom
  have hEnd := secondCase_linear_outer_transport_endpoint hmin w d K ad P eP T
    r hrI hrE htr r0 t0 a hr0 ht0 hrT htT y hyconj hyC
  dsimp [CE, R0, Ry] at hEnd
  rcases hEnd with ⟨hRcyc, hRodd, hRcard, hRyU, hRyinv⟩
  have hRycard : Nat.card Ry = Nat.card R0 := by
    dsimp [Ry]
    exact Subgroup.card_map_of_injective (MulAut.conj y).injective
  let eRy : R0 ≃* Ry :=
    Subgroup.equivMapOfInjective R0 (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective
  have hRycyc : IsCyclic Ry := (MulEquiv.isCyclic eRy).mp hRcyc
  have hRyodd : Odd (Nat.card Ry) := by
    rw [hRycard]
    exact hRodd
  have hRycardT : Nat.card Ry = Nat.card T.U / 2 :=
    hRycard.trans hRcard
  have hRyhalf :
      Nat.card Ry = (Nat.card K - 1) / 2 ∨
        Nat.card Ry = (Nat.card K + 1) / 2 := by
    rcases T.U_card with hU | hU
    · left
      calc
        Nat.card Ry = Nat.card T.U / 2 := hRycardT
        _ = (Nat.card K - 1) / 2 := by rw [hU]
    · right
      calc
        Nat.card Ry = Nat.card T.U / 2 := hRycardT
        _ = (Nat.card K + 1) / 2 := by rw [hU]
  exact ⟨r, Ry, hrSM, hrI, hrE, htr, hRycyc, hRyodd, hRyhalf,
    hRyU, hRyinv⟩

end CFSG.GorensteinWalter
