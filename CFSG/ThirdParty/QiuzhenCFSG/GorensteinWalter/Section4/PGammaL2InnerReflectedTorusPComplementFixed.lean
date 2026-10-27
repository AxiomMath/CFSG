module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2ConcreteSplitTorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2SplitReflectedTorusPComplementFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusInvolutionDerived
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2SemilinearConjugationTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldSquare
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NonsplitTorusFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflectedTorusNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed-field divisibility for an inner reflected torus

This is the source-independent split/nonsplit transport used in the
semilinear Fitting argument.  A field-component element centralizing a
normal `p`-complement of an inner reflected torus forces that complement to
have the corresponding fixed-subfield half-divisor.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- Let `U` be an inner cyclic torus in `PΓL₂(K)` containing an involution,
with cardinality the even half of `q-1` or `q+1`.  If a semilinear element
with prime-order field part `σ` centralizes `U₀ ≤ U`, then `|U₀|` divides
the matching half-cardinality over the fixed field of `σ`. -/
public theorem pGammaL2_inner_reflected_torus_pComplement_fixed
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (sigma : K ≃+* K) (hsigord : orderOf sigma = p)
    (UPGL : Subgroup (PGL2 K))
    (hUPGLcyc : IsCyclic UPGL)
    (hUPGLinner : UPGL ≤ commutator (PGL2 K))
    (hUPGLeven : Even (Nat.card UPGL))
    (hUPGLcard : Nat.card UPGL = (Nat.card K - 1) / 2 ∨
      Nat.card UPGL = (Nat.card K + 1) / 2)
    (tauPGL : PGL2 K) (htauUPGL : tauPGL ∈ UPGL)
    (htauPGLinv : IsInvolution tauPGL)
    (U0 : Subgroup (PGammaL2 K))
    (hU0leU : U0 ≤ UPGL.map
      (SemidirectProduct.inl : PGL2 K →* PGammaL2 K))
    (b0 : PGammaL2 K)
    (hb0sigma : SemidirectProduct.rightHom b0 = sigma)
    (hb0fix : ∀ u : PGammaL2 K, u ∈ U0 → b0 * u * b0⁻¹ = u) :
    (Nat.card (UPGL.map
          (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)) =
        (Nat.card K - 1) / 2 ∧
      Nat.card U0 ∣
        (Nat.card (FixedPoints.subfield (Subgroup.zpowers sigma) K) - 1) / 2) ∨
    (Nat.card (UPGL.map
          (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)) =
        (Nat.card K + 1) / 2 ∧
      Nat.card U0 ∣
        (Nat.card (FixedPoints.subfield (Subgroup.zpowers sigma) K) + 1) / 2) := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  let : Fintype K := Fintype.ofFinite K
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (by
      intro e f hef
      ext x
      exact congrFun hef x)
  let : Finite (PGammaL2 K) :=
    Finite.of_injective
      (fun x : PGammaL2 K => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext
          (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  let i : PGL2 K →* PGammaL2 K := SemidirectProduct.inl
  let U : Subgroup (PGammaL2 K) := UPGL.map i
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  have hp : p.Prime := Fact.out
  obtain ⟨_hr, _hp3, hq⟩ := finiteField_primeOrder_fixedSubfield_data
    K hK sigma p hp hpodd hsigord
  have hKodd : Odd (Nat.card K) := by
    rcases hK with ⟨ell, n, hell, hellodd, hn, hKcard⟩
    rw [hKcard]
    exact hellodd.pow
  have hrOdd : Odd (Nat.card R) := by
    rcases Nat.even_or_odd (Nat.card R) with hrEven | hrOdd
    · exfalso
      have h2r : 2 ∣ Nat.card R := even_iff_two_dvd.mp hrEven
      have h2pow : 2 ∣ Nat.card R ^ p := dvd_pow h2r hp.ne_zero
      rw [← hq] at h2pow
      exact hKodd.not_two_dvd_nat h2pow
    · exact hrOdd
  have hiinj : Function.Injective i := SemidirectProduct.inl_injective
  have hUcard : Nat.card U = Nat.card UPGL :=
    Subgroup.card_map_of_injective (K := UPGL) hiinj
  let U0P : Subgroup (PGL2 K) := U0.comap i
  have hU0Pmap : U0P.map i = U0 := by
    apply le_antisymm
    · exact Subgroup.map_comap_le i U0
    · intro x hx
      have hxU : x ∈ U := hU0leU hx
      rcases Subgroup.mem_map.mp hxU with ⟨y, hy, hxy⟩
      exact Subgroup.mem_map.mpr ⟨y, by
        apply Subgroup.mem_comap.mpr
        simpa [hxy] using hx, hxy⟩
  have hU0Pcard : Nat.card U0P = Nat.card U0 := by
    rw [← hU0Pmap]
    exact (Subgroup.card_map_of_injective (K := U0P) hiinj).symm
  have hU0Ple : U0P ≤ UPGL := by
    intro x hx
    have hinlU0 : i x ∈ U0 := Subgroup.mem_comap.mp hx
    have hinlU : i x ∈ U := hU0leU hinlU0
    rcases Subgroup.mem_map.mp hinlU with ⟨y, hy, hxy⟩
    have hyx : y = x := hiinj hxy
    simpa [hyx] using hy
  have hU0Pinner : U0P ≤ commutator (PGL2 K) := hU0Ple.trans hUPGLinner
  have hsemiconj : ∀ x : PGL2 K, x ∈ U0P →
      b0.left * pgl2FieldAut K sigma x * b0.left⁻¹ = x := by
    intro x hx
    have hfix := hb0fix (i x) (Subgroup.mem_comap.mp hx)
    have hleft := congrArg SemidirectProduct.left hfix
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.inv_left, map_inv] at hleft
    have hb0right : b0.right = sigma := by simpa using hb0sigma
    rw [hb0right] at hleft
    simpa [i] using hleft
  have htauJ : tauPGL ∈ commutator (PGL2 K) := hUPGLinner htauUPGL
  have hJindex : (commutator (PGL2 K)).index = 2 := by
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  have cyclic_le_centralizer : ∀ (V : Subgroup (PGL2 K)) (s : PGL2 K),
      IsCyclic V → s ∈ V → V ≤ Subgroup.centralizer ({s} : Set (PGL2 K)) := by
    intro V s hVcyc hsV x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hVcyc with ⟨a, ha⟩
    rcases ha ⟨x, hx⟩ with ⟨m, hm⟩
    rcases ha ⟨s, hsV⟩ with ⟨n, hn⟩
    have hc : (⟨x, hx⟩ : V) * (⟨s, hsV⟩ : V) =
        (⟨s, hsV⟩ : V) * (⟨x, hx⟩ : V) := by
      calc
        (⟨x, hx⟩ : V) * (⟨s, hsV⟩ : V) = a ^ m * a ^ n := by
          simp [hm, hn]
        _ = a ^ (m + n) := by rw [zpow_add]
        _ = a ^ (n + m) := by rw [add_comm]
        _ = a ^ n * a ^ m := by rw [zpow_add]
        _ = (⟨s, hsV⟩ : V) * (⟨x, hx⟩ : V) := by
          simp [← hn, ← hm]
    simpa using congrArg Subtype.val hc
  rcases hUPGLcard with hTminus | hTplus
  · left
    refine ⟨hUcard.trans hTminus, ?_⟩
    obtain ⟨wS, hScyc, hScard, hsS, hsI, hwSnot, hwS2,
      hwSinv, hCS, _hDcard, hSnotJ⟩ :=
      pgl2_fullSplitTorus_centralizer_data K hK
    let S : Subgroup (PGL2 K) := (pGammaL2FullSplitTorus K).range
    let sS : PGL2 K := pGammaL2FullSplitTorus K (-1 : Kˣ)
    have hhalfEven : Even ((Nat.card K - 1) / 2) := by
      rw [← hTminus]
      exact hUPGLeven
    have hqsubtwo : Nat.card K - 1 = 2 * ((Nat.card K - 1) / 2) := by
      have htwo : 2 ∣ Nat.card K - 1 := by
        rcases hKodd with ⟨k, hk⟩
        use k
        omega
      rw [mul_comm]
      exact (Nat.div_mul_cancel htwo).symm
    have hsJ : sS ∈ commutator (PGL2 K) := by
      apply pgl2_torus_involution_mem_commutator hJindex S hScyc hsS
        (by simpa [pow_two] using hsI.2) hsI.1
        (m := (Nat.card K - 1) / 2)
      · change Nat.card (pGammaL2FullSplitTorus K).range =
          2 * ((Nat.card K - 1) / 2)
        exact hScard.trans hqsubtwo
      · exact hhalfEven
      · exact hSnotJ
    obtain ⟨g, _hgJ, hg⟩ := pgl2_inner_involutions_conjugate
      hK hcard htauJ htauPGLinv hsJ hsI
    let X : Subgroup (PGL2 K) := UPGL.map (MulAut.conj g).toMonoidHom
    have hXcyc : IsCyclic X := by
      let ex : UPGL ≃* X := Subgroup.equivMapOfInjective UPGL
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      exact (MulEquiv.isCyclic ex).mp hUPGLcyc
    have hsX : sS ∈ X := by
      exact Subgroup.mem_map.mpr ⟨tauPGL, htauUPGL, by
        simpa [sS, MulAut.conj_apply] using hg⟩
    have hXleS : X ≤ S :=
      cyclic_subgroup_containing_involution_le_reflected_torus
        hsI S wS hScyc hsS
        (by constructor
            · intro h1
              apply hwSnot
              rw [h1]
              exact S.one_mem
            · simpa [pow_two] using hwS2)
        hwSnot hwSinv hCS hXcyc
        (cyclic_le_centralizer X sS hXcyc hsX) hsX
    let Astd : Subgroup (PGL2 K) := U0P.map (MulAut.conj g).toMonoidHom
    have hAstdleX : Astd ≤ X :=
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hU0Ple
    have hAstdleS : Astd ≤ S := hAstdleX.trans hXleS
    have hXinner : X ≤ commutator (PGL2 K) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact (inferInstance : (commutator (PGL2 K)).Normal).conj_mem
        y (hUPGLinner hy) g
    have hAstdinner : Astd ≤ commutator (PGL2 K) := hAstdleX.trans hXinner
    let zS : PGL2 K := g * b0.left * (pgl2FieldAut K sigma g)⁻¹
    have hAstdconj : ∀ x : PGL2 K, x ∈ Astd →
        zS * pgl2FieldAut K sigma x * zS⁻¹ = x := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact pgl2_semilinear_conjugate_transport sigma g b0.left y
        (hsemiconj y hy)
    let Tsplit : Kˣ →* PGL2 K := pGammaL2FullSplitTorus K
    let B : Subgroup Kˣ := Astd.comap Tsplit
    have hBmap : B.map Tsplit = Astd := by
      apply le_antisymm
      · exact Subgroup.map_comap_le Tsplit Astd
      · intro x hx
        rcases hAstdleS hx with ⟨b, hb⟩
        exact Subgroup.mem_map.mpr ⟨b, by
          apply Subgroup.mem_comap.mpr
          simpa [Tsplit, hb] using hx, hb⟩
    have hBcard : Nat.card B = Nat.card Astd := by
      rw [← hBmap]
      exact (Subgroup.card_map_of_injective
        (K := B) (pGammaL2FullSplitTorus_injective K)).symm
    have hAstdcard : Nat.card Astd = Nat.card U0P :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hdvd := pGammaL2_splitTorus_semilinearConjugate_fixedSubfield
      hK hcard sigma p hp hpodd hsigord hhalfEven zS B
      (by intro b hb
          apply hAstdinner
          have : Tsplit b ∈ Astd := Subgroup.mem_comap.mp hb
          simpa [Tsplit] using this)
      (by intro b hb
          rw [← pGammaL2FullSplitTorus_map_field]
          apply hAstdconj
          have : Tsplit b ∈ Astd := Subgroup.mem_comap.mp hb
          simpa [Tsplit] using this)
    rw [hBcard, hAstdcard, hU0Pcard] at hdvd
    exact hdvd
  · right
    refine ⟨hUcard.trans hTplus, ?_⟩
    let : Fintype R := Fintype.ofFinite R
    have hcharR : ringChar R ≠ 2 := by
      intro hchar
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hdvd : 2 ∣ Fintype.card R :=
        (prime_dvd_char_iff_dvd_card (R := R) (p := 2)).mp (by
          simp [hchar])
      apply hrOdd.not_two_dvd_nat
      simpa [Nat.card_eq_fintype_card] using hdvd
    obtain ⟨lamR, hlamNS⟩ := FiniteField.exists_nonsquare hcharR
    let lam : K := (lamR : R)
    obtain ⟨sN, wN, hNcyc, hNcard, hsN, hsNI, hwN2, hwNnot,
      hwNinv, hCN, _hDNcard, _hNnotRange, hNnotJ⟩ :=
      pgl2_concrete_nonsplit_torus_centralizer_data K hK
        lam (fun hsquare => hlamNS
          ((fixedSubfield_isSquare_iff K sigma p hp hpodd hsigord lamR).mp
            hsquare))
    let SN : Subgroup (PGL2 K) := pgl2ConcreteNonsplitTorus K lam
    have hhalfEven : Even ((Nat.card K + 1) / 2) := by
      rw [← hTplus]
      exact hUPGLeven
    have hqaddtwo : Nat.card K + 1 = 2 * ((Nat.card K + 1) / 2) := by
      have htwo : 2 ∣ Nat.card K + 1 := by
        rcases hKodd with ⟨k, hk⟩
        use k + 1
        omega
      rw [mul_comm]
      exact (Nat.div_mul_cancel htwo).symm
    have hsNJ : sN ∈ commutator (PGL2 K) := by
      apply pgl2_torus_involution_mem_commutator hJindex SN hNcyc hsN
        (by simpa [pow_two] using hsNI.2) hsNI.1
        (m := (Nat.card K + 1) / 2)
      · change Nat.card (pgl2ConcreteNonsplitTorus K lam) =
          2 * ((Nat.card K + 1) / 2)
        exact hNcard.trans hqaddtwo
      · exact hhalfEven
      · exact hNnotJ
    obtain ⟨g, _hgJ, hg⟩ := pgl2_inner_involutions_conjugate
      hK hcard htauJ htauPGLinv hsNJ hsNI
    let X : Subgroup (PGL2 K) := UPGL.map (MulAut.conj g).toMonoidHom
    have hXcyc : IsCyclic X := by
      let ex : UPGL ≃* X := Subgroup.equivMapOfInjective UPGL
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      exact (MulEquiv.isCyclic ex).mp hUPGLcyc
    have hsX : sN ∈ X := by
      exact Subgroup.mem_map.mpr ⟨tauPGL, htauUPGL, by
        simpa [MulAut.conj_apply] using hg⟩
    have hXleN : X ≤ SN :=
      cyclic_subgroup_containing_involution_le_reflected_torus
        hsNI SN wN hNcyc hsN
        (by constructor
            · intro h1
              apply hwNnot
              rw [h1]
              exact SN.one_mem
            · simpa [pow_two] using hwN2)
        hwNnot hwNinv hCN hXcyc
        (cyclic_le_centralizer X sN hXcyc hsX) hsX
    let Astd : Subgroup (PGL2 K) := U0P.map (MulAut.conj g).toMonoidHom
    have hAstdleX : Astd ≤ X :=
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hU0Ple
    have hAstdleN : Astd ≤ SN := hAstdleX.trans hXleN
    have hXinner : X ≤ commutator (PGL2 K) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact (inferInstance : (commutator (PGL2 K)).Normal).conj_mem
        y (hUPGLinner hy) g
    have hAstdinner : Astd ≤ commutator (PGL2 K) := hAstdleX.trans hXinner
    let zN : PGL2 K := g * b0.left * (pgl2FieldAut K sigma g)⁻¹
    have hAstdconj : ∀ x : PGL2 K, x ∈ Astd →
        zN * pgl2FieldAut K sigma x * zN⁻¹ = x := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact pgl2_semilinear_conjugate_transport sigma g b0.left y
        (hsemiconj y hy)
    have hAstdcard : Nat.card Astd = Nat.card U0P :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hdvd :=
      pGammaL2_nonsplitTorus_semilinearConjugate_fixedSubfield
        hK hcard sigma p hp hpodd hsigord lam lamR.2 hlamNS zN Astd
        hAstdleN hAstdinner hAstdconj
    rw [hAstdcard, hU0Pcard] at hdvd
    exact hdvd

end CFSG.GorensteinWalter
