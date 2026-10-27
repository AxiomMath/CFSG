module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 7.3: invariant Sylow subgroups and swapping involutions

This module proves the full normalizing-swap assertion used in Proposition 7.4,
following the two branches of the source proof.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- A Sylow subgroup of `D` that lies in an intermediate subgroup `E` is
still Sylow in `E`, in the ambient encoding used by Section 7. -/
theorem theorem4bIsSylowSubgroupOf_of_le
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P E D : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P D)
    (hPE : P ≤ E) (hED : E ≤ D) :
    theorem4bIsSylowSubgroupOf p P E := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PD, hP⟩
  let ED : Subgroup D := E.subgroupOf D
  have hPDle : (PD : Subgroup D) ≤ ED := by
    intro x hx
    change (x : X) ∈ E
    apply hPE
    rw [hP]
    exact Subgroup.mem_map_of_mem D.subtype hx
  let PED : Sylow p ED := PD.subtype hPDle
  let e : ED ≃* E := Subgroup.subgroupOfEquivOfLe hED
  let PE : Sylow p E := PED.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨PE, ?_⟩
  apply le_antisymm
  · intro x hxP
    rw [hP] at hxP
    rcases Subgroup.mem_map.mp hxP with ⟨xD, hxPD, rfl⟩
    apply Subgroup.mem_map.mpr
    let xED : ED := ⟨xD, hPDle hxPD⟩
    refine ⟨e xED, ?_, rfl⟩
    have hxPED : xED ∈ PED := by
      exact hxPD
    simpa [PE] using
      (Subgroup.mem_map_of_mem e.toMonoidHom hxPED)
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xE, hxPE, rfl⟩
    have hxPE' : xE ∈ (PED : Subgroup ED).map e.toMonoidHom := by
      simpa [PE] using hxPE
    rcases Subgroup.mem_map.mp hxPE' with ⟨xED, hxPED, hx⟩
    change (xED : D) ∈ (PD : Subgroup D) at hxPED
    rw [hP]
    apply Subgroup.mem_map.mpr
    refine ⟨(xED : D), hxPED, ?_⟩
    change (xED : X) = (xE : X)
    calc
      (xED : X) = (e xED : X) := by rfl
      _ = (xE : X) := congrArg (fun y : E => (y : X)) hx

/-- Equal-order ambient groups have the same Sylow size, so a Sylow subgroup
of one that lies in the other is Sylow in the other. -/
theorem theorem4bIsSylowSubgroupOf_of_card_eq
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P D F : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P F)
    (hPD : P ≤ D) (hcard : Nat.card D = Nat.card F) :
    theorem4bIsSylowSubgroupOf p P D := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PF, hP⟩
  have hPcard : Nat.card P = p ^ (Nat.card F).factorization p := by
    rw [hP, Subgroup.card_map_of_injective F.subtype_injective]
    exact Sylow.card_eq_multiplicity PF
  have hPDcard : Nat.card (P.subgroupOf D) =
      p ^ (Nat.card D).factorization p := by
    rw [natCard_subgroupOf_eq P D hPD, hPcard, hcard]
  let PD : Sylow p D := Sylow.ofCard (P.subgroupOf D) hPDcard
  refine ⟨PD, ?_⟩
  have hmap : (P.subgroupOf D).map D.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD]
  simpa [PD] using hmap.symm

/-- Inside a fixed ambient subgroup, Sylow status is determined by subgroup
cardinality. -/
theorem theorem4bIsSylowSubgroupOf_of_subgroup_card_eq
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {P Q E : Subgroup X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P E)
    (hQE : Q ≤ E) (hcard : Nat.card Q = Nat.card P) :
    theorem4bIsSylowSubgroupOf p Q E := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨PE, hP⟩
  have hPcard : Nat.card P = p ^ (Nat.card E).factorization p := by
    rw [hP, Subgroup.card_map_of_injective E.subtype_injective]
    exact Sylow.card_eq_multiplicity PE
  have hQEcard : Nat.card (Q.subgroupOf E) =
      p ^ (Nat.card E).factorization p := by
    rw [natCard_subgroupOf_eq Q E hQE, hcard, hPcard]
  let QE : Sylow p E := Sylow.ofCard (Q.subgroupOf E) hQEcard
  refine ⟨QE, ?_⟩
  change Q = (Q.subgroupOf E).map E.subtype
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQE]

theorem theorem4bIsSylowSubgroupOf_le
    {X : Type u} [Group X] {p : ℕ} {P E : Subgroup X}
    (h : theorem4bIsSylowSubgroupOf p P E) : P ≤ E := by
  rcases h with ⟨Q, hQ⟩
  rw [hQ]
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨q, hq, rfl⟩
  exact q.property

theorem lemma73_D_conjBy_eq_F
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z a : X} {beta : conjugateCosetSpace M}
    (ha0 : a • (QuotientGroup.mk 1 : conjugateCosetSpace M) = beta)
    (hab : a • beta = z • beta) :
    (M ⊓ MulAction.stabilizer X beta).conjBy a =
      MulAction.stabilizer X beta ⊓
        MulAction.stabilizer X (z • beta) := by
  rw [Subgroup.conjBy, Subgroup.map_inf _ _ _ (MulAut.conj a).injective]
  conv_lhs =>
    lhs
    rw [← baseCoset_stabilizer M]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [ha0, hab]

/-- Conjugating a source triple stabilizer along a triple transport gives the
original Section 7 triple stabilizer. -/
public theorem lemma73_tripleStabilizer_conjBy_eq_E
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z s g : X} {gamma delta beta : conjugateCosetSpace M}
    (hgamma : g • gamma =
      (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hdelta : g • delta = beta)
    (hsz : rightConjugateElem s g⁻¹ = z) :
    (((MulAction.stabilizer X gamma ⊓ MulAction.stabilizer X delta) ⊓
        MulAction.stabilizer X (s • delta)).conjBy g) =
      theorem4bSection7E M z beta := by
  have hgsdelta : g • (s • delta) = z • beta := by
    have hconj : g * s * g⁻¹ = z := by
      simpa [rightConjugateElem] using hsz
    calc
      g • (s • delta) = (g * s) • delta := by rw [mul_smul]
      _ = ((g * s * g⁻¹) * g) • delta := by simp
      _ = z • (g • delta) := by rw [hconj, mul_smul]
      _ = z • beta := by rw [hdelta]
  rw [theorem4bSection7E, theorem4bSection7D, Subgroup.conjBy]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [hgamma, hdelta, hgsdelta, baseCoset_stabilizer]

/-- Transport a swapping involution between two Sylow subgroups of a pointwise
pair stabilizer. -/
theorem lemma73_transport_swap_between_sylows
    {X Omega : Type u} [Group X] [Finite X] [MulAction X Omega]
    {p : ℕ} {E P Q : Subgroup X} {alpha beta : Omega} {t : X}
    (hp : Nat.Prime p)
    (hPsyl : theorem4bIsSylowSubgroupOf p P E)
    (hQsyl : theorem4bIsSylowSubgroupOf p Q E)
    (hEalpha : E ≤ MulAction.stabilizer X alpha)
    (hEbeta : E ≤ MulAction.stabilizer X beta)
    (ht : IsInvolution t)
    (htNormQ : t ∈ Subgroup.normalizer (Q : Set X))
    (htAlpha : t • alpha = beta) (htBeta : t • beta = alpha) :
    ∃ u : X,
      IsInvolution u ∧
      u ∈ Subgroup.normalizer (P : Set X) ∧
      u • alpha = beta ∧ u • beta = alpha := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨P₀, hP⟩
  rcases hQsyl with ⟨Q₀, hQ⟩
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq E P₀ Q₀
  have hQconj : Q = P.conjBy (x : X) := by
    rw [hQ, hP, ← hx]
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rw [Subgroup.conjBy]
    change Subgroup.map E.subtype
        (Subgroup.map (MulDistribMulAction.toMonoidHom E (MulAut.conj x))
          (P₀ : Subgroup E)) =
      Subgroup.map ((MulAut.conj (x : X)).toMonoidHom)
        (Subgroup.map E.subtype (P₀ : Subgroup E))
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hconjNorm :=
    section11_conjBy_le_normalizer_conjBy_of_le_normalizer
      (Subgroup.zpowers_le.mpr htNormQ) (x : X)⁻¹
  have hconjNormP : (Subgroup.zpowers t).conjBy (x : X)⁻¹ ≤
      Subgroup.normalizer (P : Set X) := by
    simpa [hQconj, Subgroup.conjBy_inv] using hconjNorm
  let u : X := rightConjugateElem t (x : X)
  have huNorm : u ∈ Subgroup.normalizer (P : Set X) := by
    apply hconjNormP
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨t, Subgroup.mem_zpowers t, ?_⟩
    simp [u, rightConjugateElem]
  have hxAlpha : (x : X) • alpha = alpha :=
    MulAction.mem_stabilizer_iff.mp (hEalpha x.property)
  have hxBeta : (x : X) • beta = beta :=
    MulAction.mem_stabilizer_iff.mp (hEbeta x.property)
  have hxInvAlpha : (x : X)⁻¹ • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X alpha).inv_mem (hEalpha x.property)
  have hxInvBeta : (x : X)⁻¹ • beta = beta := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X beta).inv_mem (hEbeta x.property)
  refine ⟨u, isInvolution_rightConjugateElem ht, huNorm, ?_, ?_⟩
  · calc
      u • alpha = (x : X)⁻¹ • (t • ((x : X) • alpha)) := by
        simp [u, rightConjugateElem, mul_smul]
      _ = (x : X)⁻¹ • (t • alpha) := by rw [hxAlpha]
      _ = (x : X)⁻¹ • beta := by rw [htAlpha]
      _ = beta := hxInvBeta
  · calc
      u • beta = (x : X)⁻¹ • (t • ((x : X) • beta)) := by
        simp [u, rightConjugateElem, mul_smul]
      _ = (x : X)⁻¹ • (t • beta) := by rw [hxBeta]
      _ = (x : X)⁻¹ • alpha := by rw [htBeta]
      _ = alpha := hxInvAlpha

private theorem isInvolution_subtype
    {G : Type u} [Group G] {H : Subgroup G} {x : G}
    (hxH : x ∈ H) (hx : IsInvolution x) :
    IsInvolution (⟨x, hxH⟩ : H) :=
  IsInvolution.subtype hx hxH

private theorem exists_involution_conjugator_mem
    {G : Type u} [Group G] [Finite G] (F : Subgroup G) {s t : G}
    (hsF : s ∈ F) (htF : t ∈ F)
    (hs : IsInvolution s) (ht : IsInvolution t)
    (hst : s ≠ t) (hodd : Odd (orderOf (s * t))) :
    ∃ r : F, IsInvolution (r : G) ∧
      rightConjugateElem s (r : G) = t := by
  let sF : F := ⟨s, hsF⟩
  let tF : F := ⟨t, htF⟩
  have hsFI : IsInvolution sF := isInvolution_subtype hsF hs
  have htFI : IsInvolution tF := isInvolution_subtype htF ht
  have hstF : sF ≠ tF := by
    intro h
    exact hst (congrArg Subtype.val h)
  have hoddF : Odd (orderOf (sF * tF)) := by
    rw [← Subgroup.orderOf_coe]
    exact hodd
  obtain ⟨r, hr, hconj⟩ :=
    exists_involution_conjugator_of_odd_product hsFI htFI hstF hoddF
  refine ⟨r, ?_, ?_⟩
  · exact IsInvolution.map_of_injective hr F.subtype Subtype.val_injective
  · exact congrArg Subtype.val hconj

/-- The Proposition 4.4/Lemma 3.2 local package: if an involution `z` in
`M` normalizes `P` but `N_X(P)` is not contained in `M`, then an outside
involution `s` in `N_X(P)` is conjugate to `z` by an involution of
`N_X(P)`. -/
theorem lemma73_normalizer_outside_involution
    {X : Type u} [Group X] [Finite X] {M P : Subgroup X} {z : X}
    (hM : IsStronglyEmbedded M) (hzM : z ∈ M) (hz : IsInvolution z)
    (hzP : z ∈ Subgroup.normalizer (P : Set X))
    (hNnot : ¬ Subgroup.normalizer (P : Set X) ≤ M) :
    ∃ s u : X,
      IsInvolution s ∧ s ∉ M ∧
      s ∈ Subgroup.normalizer (P : Set X) ∧
      IsInvolution u ∧ u ∈ Subgroup.normalizer (P : Set X) ∧
      rightConjugateElem z u = s := by
  let N : Subgroup X := Subgroup.normalizer (P : Set X)
  have hproper : M.comap N.subtype ≠ ⊤ := by
    intro htop
    apply hNnot
    intro n hn
    have hn' : (⟨n, hn⟩ : N) ∈ M.comap N.subtype := by
      rw [htop]
      exact Subgroup.mem_top (⟨n, hn⟩ : N)
    exact hn'
  have hNstrong : IsStronglyEmbedded (M.comap N.subtype) :=
    hM.comap_of_injective N.subtype Subtype.val_injective hproper
      ⟨⟨z, hzP⟩, hzM, IsInvolution.subtype hz hzP⟩
  obtain ⟨sN, hsN, hsNnot⟩ := hNstrong.exists_involution_not_mem
  have hsNX : IsInvolution (sN : X) :=
    IsInvolution.map_of_injective hsN N.subtype Subtype.val_injective
  have hzN : IsInvolution (⟨z, hzP⟩ : N) :=
    IsInvolution.subtype hz hzP
  have hsNotM : (sN : X) ∉ M := by
    intro hsM
    exact hsNnot hsM
  have hzs : z ≠ (sN : X) := by
    intro h
    apply hsNotM
    simpa [h] using hzM
  have hodd : Odd (orderOf (z * (sN : X))) := by
    change Odd (orderOf (((⟨z, hzP⟩ : N) * sN : N) : X))
    rw [Subgroup.orderOf_coe]
    exact hNstrong.orderOf_mul_odd_of_mem_not_mem
      (s := (⟨z, hzP⟩ : N)) (t := sN)
      hzM hzN hsNnot hsN
  obtain ⟨uN, huN, hconj⟩ :=
    exists_involution_conjugator_mem N
      (s := z) (t := (sN : X)) hzP sN.property hz hsNX hzs hodd
  refine ⟨(sN : X), (uN : X), hsNX, hsNotM, sN.property, huN,
    uN.property, hconj⟩

/-- The normalizer-growth consequence needed in the hard branch of Lemma 7.3.
It is independent of the involution and fixed-point data. -/
theorem lemma73_normalizer_not_le_of_not_sylow_F
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z : X} {beta : conjugateCosetSpace M} {p : ℕ} {P : Subgroup X}
    (hp : Nat.Prime p)
    (hPsylE : theorem4bIsSylowSubgroupOf p P
      (theorem4bSection7E M z beta))
    (hPnotF : ¬ theorem4bIsSylowSubgroupOf p P
      (theorem4bSection7F z beta)) :
    ¬ Subgroup.normalizer (P : Set X) ≤ M := by
  classical
  let E : Subgroup X := theorem4bSection7E M z beta
  let F : Subgroup X := theorem4bSection7F z beta
  have hFM : F ⊓ M = E := by
    simp only [F, E, theorem4bSection7F, theorem4bSection7E,
      theorem4bSection7D]
    ac_rfl
  intro hnorm
  letI : Fact p.Prime := ⟨hp⟩
  have hPsylFM : theorem4bIsSylowSubgroupOf p P (F ⊓ M) := by
    rw [hFM]
    exact hPsylE
  rcases hPsylFM with ⟨R, hPR⟩
  have hnormR :
      Subgroup.normalizer
          (section8SubgroupInAmbient
            (R : Subgroup (F ⊓ M : Subgroup X)) : Set X) ≤ M := by
    simpa [section8SubgroupInAmbient, hPR] using hnorm
  obtain ⟨R_F, hR_F⟩ :=
    section8_exists_sylow_left_eq_inf_sylow_of_normalizer_le
      (G := X) (p := p) (M := M) (N := F) R hnormR
  apply hPnotF
  refine ⟨R_F, ?_⟩
  calc
    P = section8SubgroupInAmbient
        (R : Subgroup (F ⊓ M : Subgroup X)) := by
          simpa [section8SubgroupInAmbient] using hPR
    _ = section8SubgroupInAmbient (R_F : Subgroup F) := hR_F.symm
    _ = (R_F : Subgroup F).map F.subtype := rfl

/-- Lemma 6.1 in the exact transport form needed by Lemma 7.3: double
transitivity first matches the ordered pair, and Proposition 3.6(c) adjusts
the fixed-point involution inside the resulting two-point stabilizer. -/
public theorem lemma61_triple_transport
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    {z s : X} (hzM : z ∈ M) (hz : IsInvolution z)
    (hs : IsInvolution s)
    {gamma delta beta : conjugateCosetSpace M}
    (hsGamma : s • gamma = gamma)
    (hgammaDelta : gamma ≠ delta)
    (hbetaNe : beta ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    ∃ g : X,
      g • gamma = (QuotientGroup.mk 1 : conjugateCosetSpace M) ∧
      g • delta = beta ∧
      rightConjugateElem s g⁻¹ = z := by
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  obtain ⟨x, hxGamma, hxDelta⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo)
      hgammaDelta hbetaNe.symm
  let s' : X := rightConjugateElem s x⁻¹
  have hs' : IsInvolution s' := isInvolution_rightConjugateElem hs
  have hxInvAlpha : x⁻¹ • alpha = gamma := by
    calc
      x⁻¹ • alpha = x⁻¹ • (x • gamma) := by rw [hxGamma]
      _ = gamma := inv_smul_smul x gamma
  have hs'Alpha : s' • alpha = alpha := by
    calc
      s' • alpha = x • (s • (x⁻¹ • alpha)) := by
        simp [s', rightConjugateElem, mul_smul]
      _ = x • (s • gamma) := by rw [hxInvAlpha]
      _ = x • gamma := by rw [hsGamma]
      _ = alpha := hxGamma
  have hs'M : s' ∈ M := by
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr hs'Alpha
  obtain ⟨t, ht, htM, htAlpha, _htBeta⟩ :=
    hM.corollary64_exists_swap hzM hz hbetaNe
  obtain ⟨d, hdD, hs'd⟩ :=
    hM.involutions_conjugate_by_inf_rightConjugate
      ht htM hs'M hs' hzM hz
  have hdAlpha : d • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact hdD.1
  have hstabBeta : MulAction.stabilizer X beta = rightConjugate M t := by
    rw [← htAlpha]
    simpa [MulAction.Quotient.smul_mk, smul_eq_mul, ht.inv_eq_self] using
      conjugateCoset_stabilizer M t
  have hdBeta : d • beta = beta := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [hstabBeta]
    exact hdD.2
  have hdInvAlpha : d⁻¹ • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X alpha).inv_mem
      (MulAction.mem_stabilizer_iff.mpr hdAlpha)
  have hdInvBeta : d⁻¹ • beta = beta := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X beta).inv_mem
      (MulAction.mem_stabilizer_iff.mpr hdBeta)
  let g : X := d⁻¹ * x
  refine ⟨g, ?_, ?_, ?_⟩
  · calc
      g • gamma = d⁻¹ • (x • gamma) := by simp [g, mul_smul]
      _ = d⁻¹ • alpha := by rw [hxGamma]
      _ = alpha := hdInvAlpha
  · calc
      g • delta = d⁻¹ • (x • delta) := by simp [g, mul_smul]
      _ = d⁻¹ • beta := by rw [hxDelta]
      _ = beta := hdInvBeta
  · calc
      rightConjugateElem s g⁻¹ =
          rightConjugateElem s (x⁻¹ * d) := by
            congr 1
            simp [g]
      _ = rightConjugateElem (rightConjugateElem s x⁻¹) d := by
        rw [rightConjugateElem_comp]
      _ = z := hs'd

/-- Full source-shaped Lemma 7.3, assembled in the disposable probe. -/
public theorem IsStronglyEmbedded.theorem4b_lemma73_exists_swap_normalizing
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (d : Theorem4bSixD M)
    {beta : conjugateCosetSpace M}
    (hbetaK : beta ∈ d.data.kFixedPoints)
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    {P : Subgroup X}
    (hPsyl : theorem4bIsSylowSubgroupOf d.data.p P
      (theorem4bSection7E M d.data.z beta))
    (hzP : d.data.z ∈ Subgroup.normalizer (P : Set X)) :
    ∃ t : X,
      IsInvolution t ∧
      t ∈ Subgroup.normalizer (P : Set X) ∧
      t • (QuotientGroup.mk 1 : conjugateCosetSpace M) = beta ∧
      t • beta = (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let D : Subgroup X := theorem4bSection7D M beta
  let E : Subgroup X := theorem4bSection7E M d.data.z beta
  by_cases hEasy : ∃ Q : Subgroup X,
      theorem4bIsSylowSubgroupOf d.data.p Q D ∧
      d.data.z ∈ Subgroup.normalizer (Q : Set X)
  · rcases hEasy with ⟨Q, hQsylD, hzQ⟩
    have hQD : Q ≤ D := theorem4bIsSylowSubgroupOf_le hQsylD
    have hQD' : Q ≤ M ⊓ MulAction.stabilizer X beta := by
      simpa [D, theorem4bSection7D] using hQD
    have hQE : Q ≤ E := by
      simpa [E, theorem4bSection7E, theorem4bSection7D] using
        (theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer hzQ hQD')
    have hED : E ≤ D := by
      change theorem4bSection7E M d.data.z beta ≤
        theorem4bSection7D M beta
      exact inf_le_left
    have hQsylE : theorem4bIsSylowSubgroupOf d.data.p Q E := by
      simpa [E] using
        (theorem4bIsSylowSubgroupOf_of_le d.data.hp hQsylD hQE hED)
    obtain ⟨t, ht, htNorm, htAlpha, htBeta⟩ :=
      hM.theorem4b_lemma73_exists_swap_normalizing_twoPoint_sylow
        d hbetaNe hQsylD
    have hEalpha : E ≤ MulAction.stabilizer X alpha := by
      have hDM : D ≤ M := by
        change theorem4bSection7D M beta ≤ M
        exact inf_le_left
      simpa [alpha, baseCoset_stabilizer] using hED.trans hDM
    have hEbeta : E ≤ MulAction.stabilizer X beta := by
      have hDbeta : D ≤ MulAction.stabilizer X beta := by
        change theorem4bSection7D M beta ≤ MulAction.stabilizer X beta
        exact inf_le_right
      exact hED.trans hDbeta
    exact lemma73_transport_swap_between_sylows
      d.data.hp hPsyl hQsylE hEalpha hEbeta ht htNorm htAlpha htBeta
  · have htwo : MulAction.IsMultiplyPretransitive X
        (conjugateCosetSpace M) 2 := by
      by_contra hnot2
      apply hEasy
      exact (d.lemma62 hM hbetaK hbetaNe).2
        (d.card_eq_primeShare_of_not_twoTransitive hM hT2 hnot2)
    have hzbNe : d.data.z • beta ≠ beta := by
      intro hfix
      obtain ⟨gamma, hgamma, huniq⟩ :=
        hM.involution_fixed_coset_unique d.data.hz
      have hbaseFix : d.data.z • alpha = alpha := by
        dsimp [alpha]
        have hzStab : d.data.z ∈ MulAction.stabilizer X
            (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
          rw [baseCoset_stabilizer]
          exact d.data.hzM
        exact MulAction.mem_stabilizer_iff.mp hzStab
      have hba : beta = alpha := (huniq beta hfix).trans
        (huniq alpha hbaseFix).symm
      exact hbetaNe hba
    obtain ⟨a, ha0, hab⟩ :=
      (MulAction.is_two_pretransitive_iff.mp htwo)
        hbetaNe.symm hzbNe.symm
    have hDconj : D.conjBy a = theorem4bSection7F d.data.z beta := by
      simpa [D, theorem4bSection7D, theorem4bSection7F] using
        lemma73_D_conjBy_eq_F ha0 hab
    have hcardDF : Nat.card D =
        Nat.card (theorem4bSection7F d.data.z beta) := by
      calc
        Nat.card D = Nat.card (D.conjBy a) :=
          (Subgroup.card_map_of_injective (MulAut.conj a).injective).symm
        _ = Nat.card (theorem4bSection7F d.data.z beta) := by rw [hDconj]
    have hPnotF : ¬ theorem4bIsSylowSubgroupOf d.data.p P
        (theorem4bSection7F d.data.z beta) := by
      intro hPF
      have hPE : P ≤ E := theorem4bIsSylowSubgroupOf_le hPsyl
      have hED : E ≤ D := by
        change theorem4bSection7E M d.data.z beta ≤
          theorem4bSection7D M beta
        exact inf_le_left
      have hPD := theorem4bIsSylowSubgroupOf_of_card_eq
        (D := D) (F := theorem4bSection7F d.data.z beta)
        d.data.hp hPF (hPE.trans hED) hcardDF
      apply hEasy
      exact ⟨P, by simpa [D] using hPD, hzP⟩
    have hNnot : ¬ Subgroup.normalizer (P : Set X) ≤ M :=
      lemma73_normalizer_not_le_of_not_sylow_F d.data.hp hPsyl hPnotF
    obtain ⟨s, u, hs, hsNotM, hsNorm, hu, huNorm, hzu⟩ :=
      lemma73_normalizer_outside_involution hM d.data.hzM d.data.hz
        hzP hNnot
    have hzAlpha : d.data.z • alpha = alpha := by
      dsimp [alpha]
      exact MulAction.mem_stabilizer_iff.mp (by
        rw [baseCoset_stabilizer M]
        exact d.data.hzM)
    let gamma : conjugateCosetSpace M := u • alpha
    have hsGamma : s • gamma = gamma := by
      calc
        s • gamma = rightConjugateElem d.data.z u • (u • alpha) := by
          rw [hzu]
        _ = ((u⁻¹ * d.data.z * u) * u) • alpha := by
          simp [rightConjugateElem, mul_smul]
        _ = (u⁻¹ * d.data.z) • alpha := by
          congr 1
          have huu : u * u = 1 := by
            simpa [pow_two] using hu.sq_eq_one
          calc
            (u⁻¹ * d.data.z * u) * u =
                u⁻¹ * d.data.z * (u * u) := by group
            _ = u⁻¹ * d.data.z := by rw [huu]; simp
        _ = u⁻¹ • (d.data.z • alpha) := by rw [mul_smul]
        _ = u⁻¹ • alpha := by rw [hzAlpha]
        _ = u • alpha := by rw [hu.inv_eq_self]
        _ = gamma := rfl
    have hgammaNe : gamma ≠ alpha := by
      intro hgamma
      have huFix : u •
          (QuotientGroup.mk 1 : conjugateCosetSpace M) =
          QuotientGroup.mk 1 := by
        simpa [gamma, alpha] using hgamma
      have huM : u ∈ M := by
        rw [← baseCoset_stabilizer M]
        exact MulAction.mem_stabilizer_iff.mpr huFix
      apply hsNotM
      rw [← hzu]
      exact M.mul_mem (M.mul_mem (M.inv_mem huM) d.data.hzM) huM
    have huu : u * u = 1 := by
      simpa [pow_two] using hu.sq_eq_one
    have huGamma : u • gamma = alpha := by
      change u • (u • alpha) = alpha
      rw [← mul_smul, huu, one_smul]
    have hPE : P ≤ E := theorem4bIsSylowSubgroupOf_le hPsyl
    have hED : E ≤ D := by
      change theorem4bSection7E M d.data.z beta ≤
        theorem4bSection7D M beta
      exact inf_le_left
    have hDM : D ≤ M := by
      change theorem4bSection7D M beta ≤ M
      exact inf_le_left
    have hPalpha : P ≤ MulAction.stabilizer X alpha := by
      change P ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M)
      rw [baseCoset_stabilizer M]
      exact (hPE.trans hED).trans hDM
    have hPgamma : P ≤ MulAction.stabilizer X gamma := by
      simpa [gamma] using
        theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
          huNorm hPalpha
    have hPsAlpha : P ≤ MulAction.stabilizer X (s • alpha) :=
      theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
        hsNorm hPalpha
    let T : Subgroup X :=
      (MulAction.stabilizer X gamma ⊓ MulAction.stabilizer X alpha) ⊓
        MulAction.stabilizer X (s • alpha)
    have hPT : P ≤ T := le_inf (le_inf hPgamma hPalpha) hPsAlpha
    obtain ⟨g, hgGamma, hgAlpha, hsg⟩ :=
      lemma61_triple_transport hM htwo d.data.hzM d.data.hz hs
        hsGamma hgammaNe hbetaNe
    have hTE : T.conjBy g = E := by
      simpa [T, E] using
        lemma73_tripleStabilizer_conjBy_eq_E hgGamma hgAlpha hsg
    let Q : Subgroup X := P.conjBy g
    have hQE : Q ≤ E := by
      rw [← hTE]
      exact Subgroup.map_mono hPT
    have hQcard : Nat.card Q = Nat.card P := by
      simpa [Q, Subgroup.conjBy] using
        (Subgroup.card_map_of_injective (K := P)
          (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)
    have hQsylE : theorem4bIsSylowSubgroupOf d.data.p Q E :=
      theorem4bIsSylowSubgroupOf_of_subgroup_card_eq
        d.data.hp (by simpa [E] using hPsyl) hQE hQcard
    let t : X := rightConjugateElem u g⁻¹
    have ht : IsInvolution t := isInvolution_rightConjugateElem hu
    have hconjNorm : (Subgroup.zpowers u).conjBy g ≤
        Subgroup.normalizer (Q : Set X) := by
      simpa [Q] using
        section11_conjBy_le_normalizer_conjBy_of_le_normalizer
          (Subgroup.zpowers_le.mpr huNorm) g
    have htMemConj : t ∈ (Subgroup.zpowers u).conjBy g := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨u, Subgroup.mem_zpowers u, ?_⟩
      simp [t, rightConjugateElem]
    have htNorm : t ∈ Subgroup.normalizer (Q : Set X) :=
      hconjNorm htMemConj
    have hgInvAlpha : g⁻¹ • alpha = gamma := by
      calc
        g⁻¹ • alpha = g⁻¹ • (g • gamma) := by rw [hgGamma]
        _ = gamma := inv_smul_smul g gamma
    have hgInvBeta : g⁻¹ • beta = alpha := by
      calc
        g⁻¹ • beta = g⁻¹ • (g • alpha) := by rw [hgAlpha]
        _ = alpha := inv_smul_smul g alpha
    have htAlpha : t • alpha = beta := by
      calc
        t • alpha = g • (u • (g⁻¹ • alpha)) := by
          simp [t, rightConjugateElem, mul_smul]
        _ = g • (u • gamma) := by rw [hgInvAlpha]
        _ = g • alpha := by rw [huGamma]
        _ = beta := hgAlpha
    have htBeta : t • beta = alpha := by
      calc
        t • beta = g • (u • (g⁻¹ • beta)) := by
          simp [t, rightConjugateElem, mul_smul]
        _ = g • (u • alpha) := by rw [hgInvBeta]
        _ = g • gamma := rfl
        _ = alpha := hgGamma
    have hEalpha : E ≤ MulAction.stabilizer X alpha := by
      change E ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M)
      rw [baseCoset_stabilizer M]
      exact hED.trans hDM
    have hEbeta : E ≤ MulAction.stabilizer X beta := by
      have hDbeta : D ≤ MulAction.stabilizer X beta := by
        change theorem4bSection7D M beta ≤ MulAction.stabilizer X beta
        exact inf_le_right
      exact hED.trans hDbeta
    exact lemma73_transport_swap_between_sylows
      d.data.hp hPsyl hQsylE hEalpha hEbeta ht htNorm htAlpha htBeta

end CFSG.BenderSuzuki
