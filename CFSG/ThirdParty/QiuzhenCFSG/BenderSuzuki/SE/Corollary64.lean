module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4Induction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_2_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 6.4

This file follows the source proof at `docs/cfsg-vol4.tex`, Corollary 6.4.
For a non-base point fixed by `K = I_W(z)`, normalization of
`O_{p'}(O_{2'}(D))` forces that subgroup to be trivial.  Glauberman's
`ZJ` theorem then rules out normalization of `Omega_1(Z(J(R)))`, and hence
of `R`, for the indicated `p`-subgroups of the two-point stabilizer.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

private theorem normalizer_le_normalizer_map_subtype_of_characteristic
    {G : Type u} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (K.map H.subtype : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem (K.map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, g.property⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed
      (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap
        (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxComap, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

/-- Lemma 3.9 in the form used by Corollary 6.4: an involution of the base
stabilizer and an involution fixing a distinct point have an odd product, so
there is an outside involution interchanging the two points. -/
public theorem IsStronglyEmbedded.corollary64_exists_swap
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z : X}
    (hzM : z ∈ M) (hz : IsInvolution z)
    {beta : conjugateCosetSpace M}
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    ∃ t : X, IsInvolution t ∧ t ∉ M ∧
      t • (QuotientGroup.mk 1 : conjugateCosetSpace M) = beta ∧
      t • beta = (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
  rcases QuotientGroup.mk_surjective beta with ⟨g, rfl⟩
  let s : X := rightConjugateElem z g⁻¹
  have hs : IsInvolution s := isInvolution_rightConjugateElem hz
  have hsFix : s • (QuotientGroup.mk g : conjugateCosetSpace M) =
      QuotientGroup.mk g := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer]
    exact rightConjugateElem_mem_rightConjugate hzM
  have hsNotM : s ∉ M := by
    intro hsM
    have hsBase : s • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
        QuotientGroup.mk 1 := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa [baseCoset_stabilizer] using hsM
    exact hbetaNe ((hM.involution_fixed_coset_unique hs).unique hsFix hsBase)
  have hzs : z ≠ s := by
    intro h
    exact hsNotM (h ▸ hzM)
  have hodd : Odd (orderOf (z * s)) :=
    hM.orderOf_mul_odd_of_mem_not_mem hzM hz hsNotM hs
  obtain ⟨t, ht, hzt⟩ :=
    exists_involution_conjugator_of_odd_product hz hs hzs hodd
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have hst : s * t = t * z := by
    rw [← hzt]
    simp [rightConjugateElem, ht.inv_eq_self, htt, mul_assoc]
  have hzBase : z • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
      QuotientGroup.mk 1 := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa [baseCoset_stabilizer] using hzM
  have htBase : t • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
      QuotientGroup.mk g := by
    apply (hM.involution_fixed_coset_unique hs).unique
    · calc
        s • (t • (QuotientGroup.mk 1 : conjugateCosetSpace M)) =
            (s * t) • (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
              rw [smul_smul]
        _ = (t * z) • (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
              rw [hst]
        _ = t • (z • (QuotientGroup.mk 1 : conjugateCosetSpace M)) := by
              rw [smul_smul]
        _ = t • (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
              rw [hzBase]
    · exact hsFix
  have htBeta : t • (QuotientGroup.mk g : conjugateCosetSpace M) =
      QuotientGroup.mk 1 := by
    calc
      t • (QuotientGroup.mk g : conjugateCosetSpace M) =
          t • (t • (QuotientGroup.mk 1 : conjugateCosetSpace M)) := by
            rw [htBase]
      _ = (t * t) • (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
            rw [smul_smul]
      _ = QuotientGroup.mk 1 := by rw [htt]; simp
  have htM : t ∉ M := by
    intro htM
    have htFix : t • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
        QuotientGroup.mk 1 := by
      apply MulAction.mem_stabilizer_iff.mp
      simpa [baseCoset_stabilizer] using htM
    exact hbetaNe (htBase.symm.trans htFix)
  exact ⟨t, ht, htM, htBase, htBeta⟩

/-- The ambient image of `O_{2'}(D)`. -/
@[expose] public def corollary64OddCore
    {X : Type u} [Group X] (D : Subgroup X) : Subgroup X :=
  (twoPrimeCore D).map D.subtype

/-- The source notation `theta(D) = O_{p'}(O_{2'}(D))`, embedded in the
ambient group. -/
@[expose] public def corollary64Theta
    {X : Type u} [Group X] (p : ℕ) (D : Subgroup X) : Subgroup X :=
  (pPrimeCore p (corollary64OddCore D)).map
    (corollary64OddCore D).subtype

/-- The source subgroup `Omega_1(Z(J(R)))`, embedded in the ambient group. -/
@[expose] public def corollary64Z
    {X : Type u} [Group X] (p : Nat.Primes) (R : Subgroup X) : Subgroup X :=
  (omega₁ (G := thompsonCenter R) (p := p.val)).map
    (thompsonCenter R).subtype

/-- Characteristicity of `Z(J(R))` and `Omega_1` transports normalization of
`R` to normalization of the Corollary 6.4 subgroup `Z`. -/
public theorem normalizer_le_normalizer_corollary64Z
    {X : Type u} [Group X] [Finite X] {p : Nat.Primes}
    (R : Subgroup X) :
    Subgroup.normalizer (R : Set X) ≤
      Subgroup.normalizer (corollary64Z p R : Set X) := by
  have hRZJ : Subgroup.normalizer (R : Set X) ≤
      Subgroup.normalizer (thompsonCenter R : Set X) :=
    normalizer_le_normalizer_thompsonCenter R
  have hZJZ : Subgroup.normalizer (thompsonCenter R : Set X) ≤
      Subgroup.normalizer (corollary64Z p R : Set X) := by
    let J : Subgroup X := thompsonCenter R
    have hchar : (omega₁ (G := J) (p := p.val)).Characteristic :=
      omega₁_characteristic (G := J) (p := p.val)
    simpa [J, corollary64Z] using
      normalizer_le_normalizer_map_subtype_of_characteristic
        J (omega₁ (G := J) (p := p.val))
  exact hRZJ.trans hZJZ

/-- The exact Glauberman `ZJ` consequence used in Corollary 6.4.  This is the
isolated source boundary corresponding to `[IG; 25.4, 25.6]`: when the
`p'`-core of `O R` is trivial and `R` is Sylow, `O R` normalizes
`Omega_1(Z(J(R)))`. -/
public theorem corollary64_zj_normalizer
    {X : Type u} [Group X] [Finite X] {p : Nat.Primes}
    {O R : Subgroup X}
    (hOp : pPrimeCore p.val (↥(O ⊔ R)) = ⊥)
    (_hOnorm : (O.subgroupOf (O ⊔ R)).Normal)
    (hRsylow : theorem4bIsSylowSubgroupOf p.val R (O ⊔ R))
    (hHodd : Odd (Nat.card ↥(O ⊔ R))) :
    O ⊔ R ≤ Subgroup.normalizer (corollary64Z p R : Set X) := by
  classical
  let H : Subgroup X := O ⊔ R
  have hOpH : pPrimeCore p.val H = ⊥ := by simpa [H] using hOp
  letI : Fact p.val.Prime := ⟨p.2⟩
  let : Group.IsSolvable H := odd_order_theorem H (by simpa [H] using hHodd)
  obtain ⟨S, hSR⟩ := hRsylow
  have hZJH :
      (centerIn (thompsonSubgroup (S : Subgroup H)) ⊔
        pPrimeCore p.val H).Normal :=
    theorem_6_2 (G := H) (by simpa [H] using hHodd) S
  let ZJH : Subgroup H := centerIn (thompsonSubgroup (S : Subgroup H))
  have hJH : ZJH.Normal := by
    simpa [ZJH, hOpH] using hZJH
  let A : Subgroup X := section8SubgroupInAmbient (S : Subgroup H)
  have hAeq : A = R := by
    simpa [A, H, section8SubgroupInAmbient] using hSR.symm
  have himage : section8SubgroupInAmbient ZJH =
      (centerIn (thompsonSubgroup (⊤ : Subgroup A))).map A.subtype := by
    simpa [ZJH, A] using
      (section8_centerIn_thompsonSubgroup_ambient_eq_top_image S)
  have hJamb : thompsonCenter (G := X) R =
      (ZJH.map H.subtype : Subgroup X) := by
    rw [← hAeq]
    calc
      thompsonCenter (G := X) A =
          (centerIn (thompsonSubgroup (⊤ : Subgroup A))).map A.subtype := by
            exact (thompsonCenter_top_map_subtype (G := X) A).symm
      _ = section8SubgroupInAmbient ZJH := himage.symm
      _ = ZJH.map H.subtype := rfl
  have hJmap_le : (ZJH.map H.subtype : Subgroup X) ≤ H :=
    Subgroup.map_subtype_le ZJH
  have hsubeq :
      (ZJH.map H.subtype : Subgroup X).subgroupOf H = ZJH := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hJmapSubNormal :
      ((ZJH.map H.subtype : Subgroup X).subgroupOf H).Normal := by
    rw [hsubeq]
    exact hJH
  have hHnormJmap : H ≤
      Subgroup.normalizer ((ZJH.map H.subtype : Subgroup X) : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJmap_le).1
      hJmapSubNormal
  have hHnormJ : H ≤
      Subgroup.normalizer (thompsonCenter (G := X) R : Set X) := by
    rwa [hJamb]
  let J : Subgroup X := thompsonCenter (G := X) R
  have hJOmega : Subgroup.normalizer (J : Set X) ≤
      Subgroup.normalizer
        (((omega₁ (G := J) (p := p.val)).map J.subtype : Subgroup X) :
          Set X) := by
    haveI : (omega₁ (G := J) (p := p.val)).Characteristic :=
      omega₁_characteristic (G := J) (p := p.val)
    exact section8_normalizer_map_subtype_le_of_characteristic
      (H := J) (K := omega₁ (G := J) (p := p.val))
  simpa [H, J, corollary64Z] using hHnormJ.trans hJOmega

private theorem corollary64_twoPointStabilizer_eq_of_swap
    {X : Type u} [Group X] {M : Subgroup X}
    {t : X} (ht : IsInvolution t)
    {beta : conjugateCosetSpace M}
    (htBase : t • (QuotientGroup.mk 1 : conjugateCosetSpace M) = beta) :
    M ⊓ MulAction.stabilizer X beta = M ⊓ rightConjugate M t := by
  have hstab : MulAction.stabilizer X beta = rightConjugate M t := by
    rw [← htBase]
    simpa [MulAction.Quotient.smul_mk, smul_eq_mul, ht.inv_eq_self] using
      conjugateCoset_stabilizer M t
  rw [hstab]

private theorem corollary64_theta_eq_bot
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixA M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    {t : X} (ht : IsInvolution t) (htM : t ∉ M)
    (hzNorm : d.z ∈ Subgroup.normalizer
      (corollary64Theta d.p (M ⊓ rightConjugate M t) : Set X)) :
    corollary64Theta d.p (M ⊓ rightConjugate M t) = ⊥ := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let O : Subgroup X := corollary64OddCore D
  let Theta : Subgroup X := corollary64Theta d.p D
  have : (twoPrimeCore D).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := D))
  have hNormDNormO : Subgroup.normalizer (D : Set X) ≤
      Subgroup.normalizer (O : Set X) := by
    simpa [O, corollary64OddCore] using
      normalizer_le_normalizer_map_subtype_of_characteristic
        D (twoPrimeCore D)
  have hNormONormTheta : Subgroup.normalizer (O : Set X) ≤
      Subgroup.normalizer (Theta : Set X) := by
    simpa [Theta, corollary64Theta] using
      normalizer_le_normalizer_map_subtype_of_characteristic
        O (pPrimeCore d.p O)
  have hDNormTheta : D ≤ Subgroup.normalizer (Theta : Set X) :=
    Subgroup.le_normalizer.trans (hNormDNormO.trans hNormONormTheta)
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have htNormTheta : t ∈ Subgroup.normalizer (Theta : Set X) :=
    hNormONormTheta (hNormDNormO htNormD)
  have hzNormTheta : d.z ∈ Subgroup.normalizer (Theta : Set X) := by
    simpa [Theta, D] using hzNorm
  have hcommNorm :
      ⁅D, Subgroup.zpowers t⁆ ≤ Subgroup.normalizer (Theta : Set X) := by
    rw [Subgroup.commutator_le]
    intro x hxD y hyT
    have hxN : x ∈ Subgroup.normalizer (Theta : Set X) := hDNormTheta hxD
    have hyN : y ∈ Subgroup.normalizer (Theta : Set X) :=
      (Subgroup.zpowers_le.mpr htNormTheta) hyT
    exact (Subgroup.normalizer (Theta : Set X)).mul_mem
      ((Subgroup.normalizer (Theta : Set X)).mul_mem
        ((Subgroup.normalizer (Theta : Set X)).mul_mem hxN hyN)
        ((Subgroup.normalizer (Theta : Set X)).inv_mem hxN))
      ((Subgroup.normalizer (Theta : Set X)).inv_mem hyN)
  have hLle : IsStronglyEmbedded.theorem4bProposition63Subgroup M d.z t ≤
      Subgroup.normalizer (Theta : Set X) := by
    change Subgroup.zpowers d.z ⊔ Subgroup.zpowers t ⊔
      ⁅D, Subgroup.zpowers t⁆ ≤ Subgroup.normalizer (Theta : Set X)
    exact sup_le (sup_le (Subgroup.zpowers_le.mpr hzNormTheta)
      (Subgroup.zpowers_le.mpr htNormTheta)) hcommNorm
  have hLtop : IsStronglyEmbedded.theorem4bProposition63Subgroup M d.z t = ⊤ :=
    hM.theorem4bProposition63 hX d hrank hT2 hinduction ht htM
  have hNormTop : Subgroup.normalizer (Theta : Set X) = ⊤ := by
    apply top_unique
    simpa [hLtop] using hLle
  have hThetaNormal : Theta.Normal :=
    Subgroup.normalizer_eq_top_iff.mp hNormTop
  rcases (haveI := hThetaNormal; hX.eq_bot_or_eq_top_of_normal Theta) with hbot | htop
  · simpa [Theta, D] using hbot
  · exfalso
    apply hM.ne_top
    apply top_unique
    have hThetaM : Theta ≤ M := by
      intro x hx
      have hxO : x ∈ O := Subgroup.map_subtype_le _ hx
      have hxD : x ∈ D :=
        Subgroup.map_subtype_le (twoPrimeCore D) hxO
      exact hxD.1
    simpa [htop] using hThetaM

private theorem corollary64_isSylow_of_contains_oddCore_sylow
    {X : Type u} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {D R : Subgroup X} (hDodd : Odd (Nat.card D))
    (hRp : IsPGroup p R) (hRD : R ≤ D)
    (hcontains : ∃ P₀ : Sylow p (twoPrimeCore D),
      ((((P₀ : Subgroup (twoPrimeCore D)).map
        (twoPrimeCore D).subtype).map D.subtype) : Subgroup X) ≤ R) :
    theorem4bIsSylowSubgroupOf p R D := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hOtop : twoPrimeCore D = ⊤ := by
    apply top_unique
    change (⊤ : Subgroup D) ≤ pPrimeCore 2 D
    exact le_sSup ⟨inferInstance, by simpa using hDodd.coprime_two_left⟩
  obtain ⟨P₀, hP₀R⟩ := hcontains
  let PD : Subgroup D :=
    (P₀ : Subgroup (twoPrimeCore D)).map (twoPrimeCore D).subtype
  have hPDcard : Nat.card PD = p ^ (Nat.card D).factorization p := by
    calc
      Nat.card PD = Nat.card (P₀ : Subgroup (twoPrimeCore D)) := by
        exact Subgroup.card_map_of_injective
          (K := (P₀ : Subgroup (twoPrimeCore D)))
          (twoPrimeCore D).subtype_injective
      _ = p ^ (Nat.card (twoPrimeCore D)).factorization p :=
        Sylow.card_eq_multiplicity P₀
      _ = p ^ (Nat.card D).factorization p := by rw [hOtop]; simp
  let PDsyl : Sylow p D := Sylow.ofCard PD hPDcard
  let RD : Subgroup D := R.subgroupOf D
  have hRDp : IsPGroup p RD :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRD).symm
  have hPDRD : PD ≤ RD := by
    intro x hx
    exact hP₀R (Subgroup.mem_map_of_mem D.subtype hx)
  have hRDeq : RD = PD := PDsyl.is_maximal' hRDp hPDRD
  refine ⟨PDsyl, ?_⟩
  have hRmap : RD.map D.subtype = R := by
    simpa [RD, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRD]
  calc
    R = RD.map D.subtype := hRmap.symm
    _ = PD.map D.subtype := by rw [hRDeq]
    _ = (PDsyl : Subgroup D).map D.subtype := rfl

public theorem corollary64_exists_conjugate_involution_normalizing_sylow
    {X : Type u} [Group X] [Finite X]
    {D R : Subgroup X} {t : X} {p : ℕ}
    (hDodd : Odd (Nat.card D)) (ht : IsInvolution t)
    (htNormD : t ∈ Subgroup.normalizer (D : Set X))
    (hp : Nat.Prime p) (hRsyl : theorem4bIsSylowSubgroupOf p R D) :
    ∃ x : D,
      rightConjugateElem t (x : X) ∈ Subgroup.normalizer (R : Set X) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQsyl, _hbotQ, htNormQ⟩ :=
    theorem4b_exists_invariant_sylow_containing
      (D := D) (P := (⊥ : Subgroup X)) (z := t) (p := p)
      hDodd ht htNormD hp (IsPGroup.of_bot (p := p) (G := X)) bot_le (by
        apply Subgroup.mem_normalizer_fintype
        intro n hn
        have hnOne : n = 1 := by simpa using hn
        subst n
        simp)
  obtain ⟨Q₀, hQeq⟩ := hQsyl
  obtain ⟨R₀, hReq⟩ := hRsyl
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq D R₀ Q₀
  have hQconj : Q = R.conjBy (x : X) := by
    rw [hQeq, hReq, ← hx]
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rw [Subgroup.conjBy]
    change Subgroup.map D.subtype
        (Subgroup.map (MulDistribMulAction.toMonoidHom D (MulAut.conj x))
          (R₀ : Subgroup D)) =
      Subgroup.map ((MulAut.conj (x : X)).toMonoidHom)
        (Subgroup.map D.subtype (R₀ : Subgroup D))
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hconjNorm :=
    section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (Subgroup.zpowers_le.mpr htNormQ) (x : X)⁻¹
  have hconjNormR : (Subgroup.zpowers t).conjBy (x : X)⁻¹ ≤
      Subgroup.normalizer (R : Set X) := by
    simpa [hQconj, Subgroup.conjBy_inv] using hconjNorm
  refine ⟨x, hconjNormR ?_⟩
  rw [Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨t, Subgroup.mem_zpowers t, ?_⟩
  simp [rightConjugateElem]

private theorem corollary64_z_ne_bot
    {X : Type u} [Group X] [Finite X] {p : Nat.Primes}
    {R : Subgroup X} (hRp : IsPGroup p.val R) (hRne : R ≠ ⊥) :
    corollary64Z p R ≠ ⊥ := by
  classical
  letI : Fact p.val.Prime := ⟨p.2⟩
  have hJne : thompsonCenter R ≠ ⊥ :=
    section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hRp hRne
  have hJp : IsPGroup p.val (thompsonCenter R) :=
    hRp.to_le (thompsonCenter_le R)
  have hcard := IsPGroup.card_eq_or_dvd hJp
  have hpdiv : p.val ∣ Nat.card (thompsonCenter R) := by
    rcases hcard with hcard | hdiv
    · have hJone : thompsonCenter R = ⊥ := by
        apply (Subgroup.card_eq_one (H := thompsonCenter R)).mp
        exact hcard
      exact False.elim (hJne hJone)
    · exact hdiv
  simpa [corollary64Z] using
    omega₁_map_subtype_ne_bot (thompsonCenter R) p.val hpdiv

/-- Corollary 6.4.  The Sylow-containment hypothesis is the literal source
condition: `R` contains an embedded Sylow `p`-subgroup of `O_{2'}(D)`; Sylow
status in `D` is derived in the proof. -/
public theorem IsStronglyEmbedded.corollary64
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixA M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    {beta : conjugateCosetSpace M}
    (hbetaK : beta ∈ d.kFixedPoints)
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hzNormTheta : d.z ∈ Subgroup.normalizer
      (corollary64Theta d.p
        (M ⊓ MulAction.stabilizer X beta) : Set X)) :
    let D : Subgroup X := M ⊓ MulAction.stabilizer X beta
    corollary64Theta d.p D = ⊥ ∧
      ∀ (R : Subgroup X),
        IsPGroup d.p R →
        R ≤ D →
        (∃ P₀ : Sylow d.p (twoPrimeCore D),
          ((((P₀ : Subgroup (twoPrimeCore D)).map
            (twoPrimeCore D).subtype).map D.subtype) : Subgroup X) ≤ R) →
        d.z ∉ Subgroup.normalizer
          (corollary64Z ⟨d.p, d.hp⟩ R : Set X) ∧
          d.z ∉ Subgroup.normalizer (R : Set X) := by
  classical
  let D : Subgroup X := M ⊓ MulAction.stabilizer X beta
  let p' : Nat.Primes := ⟨d.p, d.hp⟩
  obtain ⟨t, ht, htM, htBase, _htBeta⟩ :=
    hM.corollary64_exists_swap d.hzM d.hz hbetaNe
  have hDeq : D = M ⊓ rightConjugate M t :=
    corollary64_twoPointStabilizer_eq_of_swap ht htBase
  have htheta : corollary64Theta d.p D = ⊥ := by
    rw [hDeq]
    apply corollary64_theta_eq_bot hM hX d hrank hT2 hinduction ht htM
    simpa [D, hDeq] using hzNormTheta
  refine ⟨by simpa [D] using htheta, ?_⟩
  intro R hRp hRD hcontains
  change R ≤ D at hRD
  change ∃ P₀ : Sylow d.p (twoPrimeCore D),
    ((((P₀ : Subgroup (twoPrimeCore D)).map
      (twoPrimeCore D).subtype).map D.subtype) : Subgroup X) ≤ R at hcontains
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.base_inf_stabilizer_card_odd hbetaNe
  have hRsyl : theorem4bIsSylowSubgroupOf d.p R D :=
    corollary64_isSylow_of_contains_oddCore_sylow
      d.hp hDodd hRp hRD hcontains
  have htNormD : t ∈ Subgroup.normalizer (D : Set X) := by
    rw [hDeq]
    exact inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  let : Fact d.p.Prime := ⟨d.hp⟩
  have hWfix : d.W ≤ MulAction.stabilizer X beta := by
    intro w hw
    exact MulAction.mem_stabilizer_iff.mpr
      (d.kFixedPoints_subset_fixedPoints hbetaK w hw)
  have hWleD : d.W ≤ D := by
    intro w hw
    exact ⟨d.hWM hw, hWfix hw⟩
  have hpW : d.p ∣ Nat.card d.W := by
    rcases IsPGroup.card_eq_or_dvd d.hWp with hcard | hdiv
    · have hWbot : d.W = ⊥ :=
        (Subgroup.card_eq_one (H := d.W)).mp hcard
      exact False.elim (d.hWne hWbot)
    · exact hdiv
  have hpD : d.p ∣ Nat.card D :=
    hpW.trans (Subgroup.card_dvd_of_le hWleD)
  have hRne : R ≠ ⊥ := by
    obtain ⟨R₀, hReq⟩ := hRsyl
    have hR₀ne : (R₀ : Subgroup D) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card R₀ hpD
    intro hRbot
    apply hR₀ne
    apply Subgroup.map_injective D.subtype_injective
    rw [← hReq, hRbot]
    simp
  let O : Subgroup X := corollary64OddCore D
  have hOtop : twoPrimeCore D = ⊤ := by
    apply top_unique
    change (⊤ : Subgroup D) ≤ pPrimeCore 2 D
    exact le_sSup ⟨inferInstance, by simpa using hDodd.coprime_two_left⟩
  have hOeqD : O = D := by
    dsimp only [O, corollary64OddCore]
    rw [hOtop]
    simpa [MonoidHom.range_eq_map] using
      (Subgroup.range_subtype (H := D))
  have hRO : R ≤ O := by simpa [hOeqD] using hRD
  have hsup : O ⊔ R = O := sup_eq_left.mpr hRO
  have hpO : pPrimeCore d.p O = ⊥ := by
    apply Subgroup.map_injective O.subtype_injective
    simpa [corollary64Theta, O] using htheta
  have hOp : pPrimeCore d.p (↥(O ⊔ R)) = ⊥ := by
    rw [hsup]
    exact hpO
  have hOnorm : (O.subgroupOf (O ⊔ R)).Normal := by
    rw [hsup, Subgroup.subgroupOf_self]
    infer_instance
  have hRsylSup : theorem4bIsSylowSubgroupOf d.p R (O ⊔ R) := by
    rw [hsup, hOeqD]
    exact hRsyl
  have hsupNormZ : O ⊔ R ≤ Subgroup.normalizer
      (corollary64Z p' R : Set X) :=
    corollary64_zj_normalizer hOp hOnorm hRsylSup (by
      rw [hsup, hOeqD]
      exact hDodd)
  have hDNormZ : D ≤ Subgroup.normalizer
      (corollary64Z p' R : Set X) := by
    intro y hy
    apply hsupNormZ
    rw [hsup, hOeqD]
    exact hy
  obtain ⟨x, htxNormR⟩ :=
    corollary64_exists_conjugate_involution_normalizing_sylow
      hDodd ht htNormD d.hp hRsyl
  have htxNormZ : rightConjugateElem t (x : X) ∈
      Subgroup.normalizer (corollary64Z p' R : Set X) :=
    normalizer_le_normalizer_corollary64Z R htxNormR
  have hzNotNormZ : d.z ∉ Subgroup.normalizer
      (corollary64Z p' R : Set X) := by
    intro hzNormZ
    let Z : Subgroup X := corollary64Z p' R
    have hxNormZ : (x : X) ∈ Subgroup.normalizer (Z : Set X) :=
      hDNormZ x.property
    have htNormZ : t ∈ Subgroup.normalizer (Z : Set X) := by
      have hprod := (Subgroup.normalizer (Z : Set X)).mul_mem
        ((Subgroup.normalizer (Z : Set X)).mul_mem hxNormZ htxNormZ)
        ((Subgroup.normalizer (Z : Set X)).inv_mem hxNormZ)
      simpa [rightConjugateElem, mul_assoc] using hprod
    have hcommNorm : ⁅D, Subgroup.zpowers t⁆ ≤
        Subgroup.normalizer (Z : Set X) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haN : a ∈ Subgroup.normalizer (Z : Set X) := hDNormZ ha
      have hbN : b ∈ Subgroup.normalizer (Z : Set X) :=
        (Subgroup.zpowers_le.mpr htNormZ) hb
      exact (Subgroup.normalizer (Z : Set X)).mul_mem
        ((Subgroup.normalizer (Z : Set X)).mul_mem
          ((Subgroup.normalizer (Z : Set X)).mul_mem haN hbN)
          ((Subgroup.normalizer (Z : Set X)).inv_mem haN))
        ((Subgroup.normalizer (Z : Set X)).inv_mem hbN)
    have hLle : IsStronglyEmbedded.theorem4bProposition63Subgroup M d.z t ≤
        Subgroup.normalizer (Z : Set X) := by
      change Subgroup.zpowers d.z ⊔ Subgroup.zpowers t ⊔
        ⁅M ⊓ rightConjugate M t, Subgroup.zpowers t⁆ ≤
          Subgroup.normalizer (Z : Set X)
      rw [← hDeq]
      exact sup_le
        (sup_le (Subgroup.zpowers_le.mpr hzNormZ)
          (Subgroup.zpowers_le.mpr htNormZ)) hcommNorm
    have hLtop : IsStronglyEmbedded.theorem4bProposition63Subgroup
        M d.z t = ⊤ :=
      hM.theorem4bProposition63 hX d hrank hT2 hinduction ht htM
    have hNormTop : Subgroup.normalizer (Z : Set X) = ⊤ := by
      apply top_unique
      simpa [hLtop] using hLle
    have hZnormal : Z.Normal :=
      Subgroup.normalizer_eq_top_iff.mp hNormTop
    have hZne : Z ≠ ⊥ := by
      simpa [Z, p'] using corollary64_z_ne_bot hRp hRne
    rcases (haveI := hZnormal; hX.eq_bot_or_eq_top_of_normal Z) with hZbot | hZtop
    · exact hZne hZbot
    · apply hM.ne_top
      apply top_unique
      have hZleR : Z ≤ R := by
        exact (Subgroup.map_subtype_le
          (omega₁ (G := thompsonCenter R) (p := d.p))).trans
            (thompsonCenter_le R)
      have hZleM : Z ≤ M := hZleR.trans (hRD.trans inf_le_left)
      simpa [hZtop] using hZleM
  refine ⟨by simpa [p'] using hzNotNormZ, ?_⟩
  intro hzNormR
  apply hzNotNormZ
  exact normalizer_le_normalizer_corollary64Z R hzNormR

end CFSG.BenderSuzuki
