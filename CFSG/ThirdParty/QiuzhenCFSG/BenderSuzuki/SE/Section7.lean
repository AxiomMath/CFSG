module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Coprime

namespace CFSG
end CFSG
open CFSG

/-!
# Section 7: the theta-chain endpoint

This file begins the source proof of Theorem 4(b) in Section 7 of
`docs/cfsg-vol4.tex`.  It packages the two- and three-point stabilizers used in
Proposition 7.2 and proves the checked endpoint of Lemmas 7.5--7.7: their two
subgroup inclusions and cardinal inequality force equality `(7B)`, hence
normalization of `theta(X_{alpha beta})`; Corollary 6.4 then makes that theta
subgroup trivial.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- The source subgroup `D = X_{alpha,beta}` in Section 7. -/
@[expose] public def theorem4bSection7D
    {X : Type u} [Group X] [Finite X] (M : Subgroup X)
    (beta : conjugateCosetSpace M) : Subgroup X :=
  M ⊓ MulAction.stabilizer X beta

/-- The source subgroup `E = X_{alpha,beta,beta^z}` in Section 7. -/
@[expose] public def theorem4bSection7E
    {X : Type u} [Group X] [Finite X] (M : Subgroup X) (z : X)
    (beta : conjugateCosetSpace M) : Subgroup X :=
  theorem4bSection7D M beta ⊓ MulAction.stabilizer X (z • beta)

/-- The source subgroup `F = X_{beta,beta^z}` in Section 7. -/
@[expose] public def theorem4bSection7F
    {X : Type u} [Group X] [Finite X] {M : Subgroup X} (z : X)
    (beta : conjugateCosetSpace M) : Subgroup X :=
  MulAction.stabilizer X beta ⊓ MulAction.stabilizer X (z • beta)

private noncomputable def theorem4bSection7ConjSubgroupEquiv
    {X : Type u} [Group X] (H : Subgroup X) (g : X) :
    H ≃* H.conjBy g := by
  exact MulEquiv.subgroupMap (MulAut.conj g) H

private theorem theorem4bSection7ConjSubgroupEquiv_coe
    {X : Type u} [Group X] (H : Subgroup X) (g : X) (x : H) :
    (((theorem4bSection7ConjSubgroupEquiv H g) x : H.conjBy g) : X) =
      g * (x : X) * g⁻¹ := by
  change ((MulAut.conj g) x : X) = g * (x : X) * g⁻¹
  rfl

/-- Taking an ambient copy of a `p'`-core commutes with conjugating the
ambient subgroup. -/
public theorem theorem4b_ambientPPrimeCore_conjBy
    {X : Type u} [Group X] (p : ℕ) (H : Subgroup X) (g : X) :
    ((pPrimeCore p H).map H.subtype).conjBy g =
      (pPrimeCore p (H.conjBy g)).map (H.conjBy g).subtype := by
  let e : H ≃* H.conjBy g := theorem4bSection7ConjSubgroupEquiv H g
  change ((pPrimeCore p H).map H.subtype).map
      (MulAut.conj g).toMonoidHom = _
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj g).toMonoidHom.comp H.subtype =
      (H.conjBy g).subtype.comp e.toMonoidHom := by
    ext x
    simpa [e, theorem4bSection7ConjSubgroupEquiv_coe,
      MulAut.conj_apply]
  rw [hcomp]
  rw [← Subgroup.map_map]
  rw [pPrimeCore_map_iso]

/-- The odd core used in Corollary 6.4 commutes with subgroup conjugation. -/
public theorem corollary64OddCore_conjBy
    {X : Type u} [Group X] (H : Subgroup X) (g : X) :
    (corollary64OddCore H).conjBy g =
      corollary64OddCore (H.conjBy g) := by
  simpa [corollary64OddCore, twoPrimeCore] using
    theorem4b_ambientPPrimeCore_conjBy 2 H g

/-- The two-stage theta core commutes with subgroup conjugation. -/
public theorem corollary64Theta_conjBy
    {X : Type u} [Group X] (p : ℕ) (H : Subgroup X) (g : X) :
    (corollary64Theta p H).conjBy g =
      corollary64Theta p (H.conjBy g) := by
  rw [corollary64Theta]
  rw [theorem4b_ambientPPrimeCore_conjBy]
  rw [corollary64OddCore_conjBy]
  rfl

/-- Conjugating the two-point stabilizer `F` by the element supplied in
Proposition 7.4(d)(4) turns it into the next base--point stabilizer `D`. -/
public theorem theorem4bSection7F_conjBy_eq_D
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z g : X} {beta beta1 : conjugateCosetSpace M}
    (hgbeta : g • beta = beta1)
    (hgzbeta : g • (z • beta) =
      (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    (theorem4bSection7F z beta).conjBy g =
      theorem4bSection7D M beta1 := by
  rw [theorem4bSection7F, theorem4bSection7D, Subgroup.conjBy]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [hgbeta, hgzbeta, baseCoset_stabilizer, inf_comm]

/-- Theta has the same cardinality on `F` and the conjugate `D` appearing in
Proposition 7.4(d)(4). -/
public theorem corollary64Theta_card_section7F_eq_D
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (p : ℕ) {z g : X} {beta beta1 : conjugateCosetSpace M}
    (hgbeta : g • beta = beta1)
    (hgzbeta : g • (z • beta) =
      (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    Nat.card (corollary64Theta p (theorem4bSection7F z beta)) =
      Nat.card (corollary64Theta p (theorem4bSection7D M beta1)) := by
  have hmap := corollary64Theta_conjBy p (theorem4bSection7F z beta) g
  rw [theorem4bSection7F_conjBy_eq_D hgbeta hgzbeta] at hmap
  calc
    Nat.card (corollary64Theta p (theorem4bSection7F z beta)) =
        Nat.card ((corollary64Theta p
          (theorem4bSection7F z beta)).conjBy g) := by
            symm
            exact Subgroup.card_map_of_injective (MulAut.conj g).injective
    _ = Nat.card (corollary64Theta p
        (theorem4bSection7D M beta1)) := by rw [hmap]

/-- Lemma 7.7 from the minimal choice of `beta`. -/
public theorem theorem4b_lemma77_of_minimal
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (p : ℕ) (Gamma : Set (conjugateCosetSpace M))
    {z g : X} {beta beta1 : conjugateCosetSpace M}
    (hminimal : ∀ gamma : conjugateCosetSpace M,
      gamma ∈ Gamma →
      gamma ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M) →
      Nat.card (corollary64Theta p (theorem4bSection7D M beta)) ≤
        Nat.card (corollary64Theta p (theorem4bSection7D M gamma)))
    (hbeta1Gamma : beta1 ∈ Gamma)
    (hbeta1Ne : beta1 ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hgbeta : g • beta = beta1)
    (hgzbeta : g • (z • beta) =
      (QuotientGroup.mk 1 : conjugateCosetSpace M)) :
    Nat.card (corollary64Theta p (theorem4bSection7D M beta)) ≤
      Nat.card (corollary64Theta p (theorem4bSection7F z beta)) := by
  rw [corollary64Theta_card_section7F_eq_D p hgbeta hgzbeta]
  exact hminimal beta1 hbeta1Gamma hbeta1Ne

/-- Proposition 7.2: some nonbase point fixed by `K` has trivial theta-core
in its two-point stabilizer. -/
@[expose] public def Theorem4bProposition72
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) : Prop :=
  ∃ beta : conjugateCosetSpace M,
    beta ∈ d.kFixedPoints ∧
      beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M) ∧
        corollary64Theta d.p (theorem4bSection7D M beta) = ⊥

/-- The finite-subgroup comparison used after Lemmas 7.5--7.7.  If
`F ≤ E ≤ D` and the order of `D` is at most the order of `F`, all three
subgroups are equal. -/
public theorem theorem4b_section7_chain_eq
    {X : Type u} [Group X] [Finite X] {D E F : Subgroup X}
    (hFE : F ≤ E) (hED : E ≤ D) (hcard : Nat.card D ≤ Nat.card F) :
    D = E ∧ E = F := by
  have hFD : F ≤ D := hFE.trans hED
  have hFDeq : F = D :=
    Subgroup.eq_of_le_of_card_ge hFD hcard
  have hDE : D = E := by
    apply le_antisymm
    · rw [← hFDeq]
      exact hFE
    · exact hED
  exact ⟨hDE, hDE.symm.trans hFDeq.symm⟩

/-- The involution `z` interchanges `beta` and `z • beta`, hence normalizes
their two-point stabilizer `F`. -/
public theorem theorem4b_mem_normalizer_section7F
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z : X} (hz : IsInvolution z) (beta : conjugateCosetSpace M) :
    z ∈ Subgroup.normalizer (theorem4bSection7F z beta : Set X) := by
  simpa [theorem4bSection7F] using
    (theorem4b_mem_normalizer_tripleStabilizer
      (M := (⊤ : Subgroup X)) (z := z) (beta := beta)
      hz (Subgroup.mem_top z))

/-- Characteristicity of the successive odd cores transports normalization
of `F` to normalization of `theta(F)`. -/
public theorem theorem4b_mem_normalizer_section7ThetaF
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    {z : X} (hz : IsInvolution z) (p : ℕ)
    (beta : conjugateCosetSpace M) :
    z ∈ Subgroup.normalizer
      (corollary64Theta p (theorem4bSection7F z beta) : Set X) := by
  let F : Subgroup X := theorem4bSection7F z beta
  let O : Subgroup X := corollary64OddCore F
  let Theta : Subgroup X := corollary64Theta p F
  haveI : (twoPrimeCore F).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := F))
  have hNormFNormO : Subgroup.normalizer (F : Set X) ≤
      Subgroup.normalizer (O : Set X) := by
    simpa [O, corollary64OddCore] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := F) (K := twoPrimeCore F))
  have hNormONormTheta : Subgroup.normalizer (O : Set X) ≤
      Subgroup.normalizer (Theta : Set X) := by
    simpa [Theta, corollary64Theta] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := O) (K := pPrimeCore p O))
  exact hNormONormTheta (hNormFNormO (by
    simpa [F] using theorem4b_mem_normalizer_section7F hz beta))

/-- A normal subgroup of `E` whose order is prime to both `2` and `p` lies
in the two-stage core `theta(E)`.  This is the core-universal-property part of
Lemma 7.5. -/
public theorem theorem4b_lemma75_le_theta_of_normal_coprime
    {X : Type u} [Group X] [Finite X] {p : ℕ}
    {T E : Subgroup X}
    (hTE : T ≤ E)
    (hTnormal : (T.subgroupOf E).Normal)
    (h2cop : Nat.Coprime 2 (Nat.card T))
    (hpcop : Nat.Coprime p (Nat.card T)) :
    T ≤ corollary64Theta p E := by
  let O : Subgroup X := corollary64OddCore E
  have hcardTE : Nat.card (T.subgroupOf E) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTE).toEquiv
  have hTEcop : Nat.Coprime 2 (Nat.card (T.subgroupOf E)) := by
    simpa [hcardTE] using h2cop
  have hTsub_le_core : T.subgroupOf E ≤ twoPrimeCore E :=
    le_sSup ⟨hTnormal, by simpa [twoPrimeCore] using hTEcop⟩
  have hTO : T ≤ O := by
    have hmap := Subgroup.map_mono (f := E.subtype) hTsub_le_core
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTE] at hmap
    simpa [O, corollary64OddCore] using hmap
  have hOE : O ≤ E := by
    simpa [O, corollary64OddCore] using
      (Subgroup.map_subtype_le (twoPrimeCore E))
  have hENormT : E ≤ Subgroup.normalizer (T : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTE).mp hTnormal
  have hTnormalO : (T.subgroupOf O).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTO).mpr
      (hOE.trans hENormT)
  have hcardTO : Nat.card (T.subgroupOf O) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTO).toEquiv
  have hTOcop : Nat.Coprime p (Nat.card (T.subgroupOf O)) := by
    simpa [hcardTO] using hpcop
  have hTsub_le_pCore : T.subgroupOf O ≤ pPrimeCore p O :=
    le_sSup ⟨hTnormalO, hTOcop⟩
  have hmap := Subgroup.map_mono (f := O.subtype) hTsub_le_pCore
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTO] at hmap
  simpa [O, corollary64Theta] using hmap

/-- Once `theta(F)` has been placed inside an intermediate subgroup
`E ≤ F`, its characteristic/core properties promote that containment to the
full Lemma 7.5 conclusion `theta(F) ≤ theta(E)`. -/
public theorem theorem4b_lemma75_theta_le_theta_of_le
    {X : Type u} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {E F : Subgroup X}
    (hEF : E ≤ F)
    (hThetaE : corollary64Theta p F ≤ E) :
    corollary64Theta p F ≤ corollary64Theta p E := by
  let O : Subgroup X := corollary64OddCore F
  let T : Subgroup X := corollary64Theta p F
  have hOF : O ≤ F := by
    simpa [O, corollary64OddCore] using
      (Subgroup.map_subtype_le (twoPrimeCore F))
  have hTO : T ≤ O := by
    simpa [T, O, corollary64Theta] using
      (Subgroup.map_subtype_le (pPrimeCore p O))
  have hTF : T ≤ F := hTO.trans hOF
  haveI : (twoPrimeCore F).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := F))
  have hNormFNormO : Subgroup.normalizer (F : Set X) ≤
      Subgroup.normalizer (O : Set X) := by
    simpa [O, corollary64OddCore] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := F) (K := twoPrimeCore F))
  have hNormONormT : Subgroup.normalizer (O : Set X) ≤
      Subgroup.normalizer (T : Set X) := by
    simpa [T, corollary64Theta] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := O) (K := pPrimeCore p O))
  have hFNormT : F ≤ Subgroup.normalizer (T : Set X) :=
    Subgroup.le_normalizer.trans (hNormFNormO.trans hNormONormT)
  have hTnormalE : (T.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (by
      simpa [T] using hThetaE)).mpr (hEF.trans hFNormT)
  have hcardT : Nat.card T = Nat.card (pPrimeCore p O) := by
    simpa [T, O, corollary64Theta] using
      (Subgroup.card_map_of_injective
        (K := pPrimeCore p O) (f := O.subtype) O.subtype_injective)
  have hpcop : Nat.Coprime p (Nat.card T) := by
    rw [hcardT]
    exact pPrimeCore_coprime_card (p := p) (G := O)
  have hcardO : Nat.card O = Nat.card (twoPrimeCore F) := by
    simpa [O, corollary64OddCore] using
      (Subgroup.card_map_of_injective
        (K := twoPrimeCore F) (f := F.subtype) F.subtype_injective)
  have h2copO : Nat.Coprime 2 (Nat.card O) := by
    rw [hcardO]
    exact pPrimeCore_coprime_card (p := 2) (G := F)
  have h2cop : Nat.Coprime 2 (Nat.card T) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hTO) h2copO
  exact theorem4b_lemma75_le_theta_of_normal_coprime
    (p := p) (T := T) (E := E) (by simpa [T] using hThetaE)
      hTnormalE h2cop hpcop

/-! ## Lemma 7.5: coprime-action generation -/

/-- Lemma 7.5.  Proposition 7.4(c) supplies the centralizer containment
`C_F(W) <= M`.  The source coprime-action theorem `[II1; 4.6]` then generates
`theta(F)` from `C_theta(F)(W)` and the `W`-conjugates of `C_theta(F)(z)`;
all of those subgroups lie in `E = F inf M`. -/
public theorem IsStronglyEmbedded.theorem4b_lemma75
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixA M)
    {beta : conjugateCosetSpace M}
    (hbetaK : beta ∈ d.kFixedPoints)
    (hCFW : subgroupCentralizerIn
      (theorem4bSection7F d.z beta) d.W <= M) :
    corollary64Theta d.p (theorem4bSection7F d.z beta) <=
      corollary64Theta d.p (theorem4bSection7E M d.z beta) := by
  letI : Fact d.p.Prime := ⟨d.hp⟩
  let F : Subgroup X := theorem4bSection7F d.z beta
  let E : Subgroup X := theorem4bSection7E M d.z beta
  let O : Subgroup X := corollary64OddCore F
  let T : Subgroup X := corollary64Theta d.p F
  have hWbeta : d.W <= MulAction.stabilizer X beta := by
    have hfix := d.kFixedPoints_subset_fixedPoints hbetaK
    intro w hw
    exact MulAction.mem_stabilizer_iff.mpr (hfix w hw)
  have hWzbeta : d.W <= MulAction.stabilizer X (d.z • beta) :=
    theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      d.hzNorm hWbeta
  have hWF : d.W <= F := le_inf hWbeta hWzbeta
  have hWE : d.W <= E :=
    le_inf (le_inf d.hWM hWbeta) hWzbeta
  have hEF : E <= F :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hOF : O <= F := by
    simpa [O, corollary64OddCore] using
      (Subgroup.map_subtype_le (twoPrimeCore F))
  have hTO : T <= O := by
    simpa [T, O, corollary64Theta] using
      (Subgroup.map_subtype_le (pPrimeCore d.p O))
  have hTF : T <= F := hTO.trans hOF
  haveI : (twoPrimeCore F).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := F))
  have hNormFNormO : Subgroup.normalizer (F : Set X) <=
      Subgroup.normalizer (O : Set X) := by
    simpa [O, corollary64OddCore] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := F) (K := twoPrimeCore F))
  have hNormONormT : Subgroup.normalizer (O : Set X) <=
      Subgroup.normalizer (T : Set X) := by
    simpa [T, corollary64Theta] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := O) (K := pPrimeCore d.p O))
  have hFNormT : F <= Subgroup.normalizer (T : Set X) :=
    Subgroup.le_normalizer.trans (hNormFNormO.trans hNormONormT)
  have hWT : d.W <= Subgroup.normalizer (T : Set X) :=
    hWF.trans hFNormT
  have hzT : d.z ∈ Subgroup.normalizer (T : Set X) := by
    simpa [T, F] using theorem4b_mem_normalizer_section7ThetaF
      d.hz d.p beta
  have hgen : Lemma75II146Conclusion T d.W d.z := by
    apply lemma75_II146_specialized d.hz d.hzNorm hWT hzT d.hcomm
    · simpa [T, F] using lemma75_theta_odd_card d.p F
    · simpa [T, F] using
        lemma75_theta_actor_card_coprime d.hp d.hWp d.hz d.hzNorm F
  have hCTW : subgroupCentralizerIn T d.W <= E := by
    intro x hx
    have hxF : x ∈ F := hTF hx.1
    have hxM : x ∈ M := hCFW ⟨by simpa [F] using hxF, hx.2⟩
    exact ⟨⟨hxM, hxF.1⟩, hxF.2⟩
  have hCTz : elementCentralizerIn T d.z <= E := by
    intro x hx
    have hxF : x ∈ F := hTF hx.1
    have hxM : x ∈ M := hM.centralizer_le d.hzM d.hz hx.2
    exact ⟨⟨hxM, hxF.1⟩, hxF.2⟩
  have hTE : T <= E :=
    lemma75_le_of_II146Conclusion hgen hCTW hCTz hWE
  exact theorem4b_lemma75_theta_le_theta_of_le
    (p := d.p) (E := E) (F := F) hEF (by simpa [T] using hTE)

/-- Checked endpoint of Proposition 7.2 for a fixed `beta`.  Lemmas 7.5,
7.6, and 7.7 provide exactly the three comparison hypotheses below.  They
force `(7B)`, after which the obvious `z`-invariance of `F` and Corollary 6.4
give `theta(D) = 1`. -/
public theorem IsStronglyEmbedded.theorem4b_proposition72_of_theta_chain
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
    (hFE : corollary64Theta d.p (theorem4bSection7F d.z beta) ≤
      corollary64Theta d.p (theorem4bSection7E M d.z beta))
    (hED : corollary64Theta d.p (theorem4bSection7E M d.z beta) ≤
      corollary64Theta d.p (theorem4bSection7D M beta))
    (hcard :
      Nat.card (corollary64Theta d.p (theorem4bSection7D M beta)) ≤
        Nat.card (corollary64Theta d.p
          (theorem4bSection7F d.z beta))) :
    corollary64Theta d.p (theorem4bSection7D M beta) = ⊥ := by
  obtain ⟨hDE, hEF⟩ := theorem4b_section7_chain_eq hFE hED hcard
  have hDF : corollary64Theta d.p (theorem4bSection7D M beta) =
      corollary64Theta d.p (theorem4bSection7F d.z beta) :=
    hDE.trans hEF
  have hzNormD : d.z ∈ Subgroup.normalizer
      (corollary64Theta d.p (theorem4bSection7D M beta) : Set X) := by
    rw [hDF]
    exact theorem4b_mem_normalizer_section7ThetaF d.hz d.p beta
  have hcor := hM.corollary64 hX d hrank hT2 hinduction hbetaK hbetaNe (by
    simpa [theorem4bSection7D] using hzNormD)
  simpa [theorem4bSection7D] using hcor.1

/-- Existential assembly of Proposition 7.2 once Proposition 7.4 and Lemmas
7.5--7.7 have supplied a point satisfying their three comparisons. -/
public theorem IsStronglyEmbedded.theorem4b_proposition72_of_exists_theta_chain
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixA M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    (hchain : ∃ beta : conjugateCosetSpace M,
      beta ∈ d.kFixedPoints ∧
      beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M) ∧
      corollary64Theta d.p (theorem4bSection7F d.z beta) ≤
        corollary64Theta d.p (theorem4bSection7E M d.z beta) ∧
      corollary64Theta d.p (theorem4bSection7E M d.z beta) ≤
        corollary64Theta d.p (theorem4bSection7D M beta) ∧
      Nat.card (corollary64Theta d.p (theorem4bSection7D M beta)) ≤
        Nat.card (corollary64Theta d.p
          (theorem4bSection7F d.z beta))) :
    Theorem4bProposition72 d := by
  obtain ⟨beta, hbetaK, hbetaNe, hFE, hED, hcard⟩ := hchain
  refine ⟨beta, hbetaK, hbetaNe, ?_⟩
  exact hM.theorem4b_proposition72_of_theta_chain hX d hrank hT2 hinduction
    hbetaK hbetaNe hFE hED hcard

/-! ## Lemma 7.6: assembly of the conjugate `W₁` -/

/-- Lemma 7.6, specialized to the actual Section 7 set
`K₁ = K^(t^z)`.  The two final hypotheses are precisely Proposition 7.4(d)(2)
and (d)(3), rewritten as the source containment `(7C)`; the proof constructs
`W₁ = ⟨K₁⟩`, proves that it is the conjugate of the `p`-group `W`, and
then applies the checked Thompson--Bender core. -/
public theorem IsStronglyEmbedded.theorem4b_lemma76
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixA M)
    {beta : conjugateCosetSpace M}
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (t : X)
    (hK1E : rightConjugateSet d.invertedSet
      (rightConjugateElem t d.z) ⊆ theorem4bSection7E M d.z beta)
    (hcent : theorem4bSection7D M beta ⊓
      Subgroup.centralizer
        (rightConjugateSet d.invertedSet (rightConjugateElem t d.z)) ≤
      theorem4bSection7E M d.z beta) :
    corollary64Theta d.p (theorem4bSection7E M d.z beta) ≤
      corollary64Theta d.p (theorem4bSection7D M beta) := by
  classical
  letI : Fact d.p.Prime := ⟨d.hp⟩
  let g : X := rightConjugateElem t d.z
  let K1 : Set X := rightConjugateSet d.invertedSet g
  let W1X : Subgroup X := rightConjugate d.W g
  have hclosureConj :
      Subgroup.closure (rightConjugateSet d.invertedSet g) =
        rightConjugate (Subgroup.closure d.invertedSet) g := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, by simpa [rightConjugateElem] using hxy.symm⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, by simpa [rightConjugateElem] using hxy.symm⟩
  have hclosureK1 : Subgroup.closure K1 = W1X := by
    calc
      Subgroup.closure K1 =
          rightConjugate (Subgroup.closure d.invertedSet) g := by
            simpa [K1] using hclosureConj
      _ = W1X := by rw [d.closure_invertedSet_eq]
  have hW1XE : W1X ≤ theorem4bSection7E M d.z beta := by
    rw [← hclosureK1, Subgroup.closure_le]
    simpa [K1, g] using hK1E
  have hED : theorem4bSection7E M d.z beta ≤
      theorem4bSection7D M beta := inf_le_left
  have hW1XD : W1X ≤ theorem4bSection7D M beta := hW1XE.trans hED
  let W1 : Subgroup (theorem4bSection7D M beta) :=
    W1X.subgroupOf (theorem4bSection7D M beta)
  have hW1Xp : IsPGroup d.p W1X := by
    change IsPGroup d.p
      (d.W.map (MulAut.conj g⁻¹).toMonoidHom)
    exact d.hWp.map (MulAut.conj g⁻¹).toMonoidHom
  have hW1p : IsPGroup d.p W1 :=
    hW1Xp.of_equiv (Subgroup.subgroupOfEquivOfLe hW1XD).symm
  have hW1E : W1 ≤
      (theorem4bSection7E M d.z beta).subgroupOf
        (theorem4bSection7D M beta) := by
    intro x hx
    have hxE : (x : X) ∈ theorem4bSection7E M d.z beta := hW1XE hx
    exact (Subgroup.mem_subgroupOf).2 hxE
  have hcentW1E : Subgroup.centralizer
      (W1 : Set (theorem4bSection7D M beta)) ≤
        (theorem4bSection7E M d.z beta).subgroupOf
          (theorem4bSection7D M beta) := by
    intro x hx
    have hxK1 : (x : X) ∈ Subgroup.centralizer K1 := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hkW1X : k ∈ W1X := by
        rw [← hclosureK1]
        exact Subgroup.subset_closure hk
      let kD : theorem4bSection7D M beta := ⟨k, hW1XD hkW1X⟩
      have hkW1 : kD ∈ W1 := by
        exact (Subgroup.mem_subgroupOf).2 hkW1X
      have hcomm := Subgroup.mem_centralizer_iff.mp hx kD hkW1
      exact congrArg Subtype.val hcomm
    have hxE : (x : X) ∈ theorem4bSection7E M d.z beta :=
      hcent ⟨x.property, by simpa [K1, g] using hxK1⟩
    exact (Subgroup.mem_subgroupOf).2 hxE
  have hpodd : d.p ≠ 2 := by
    intro hp
    have htwoOdd : Odd 2 := hp ▸ d.hpOdd
    exact htwoOdd.not_two_dvd_nat (dvd_refl 2)
  have hDodd : Odd (Nat.card (theorem4bSection7D M beta)) := by
    simpa [theorem4bSection7D] using
      hM.base_inf_stabilizer_card_odd hbetaNe
  apply theorem4b_lemma76_of_pgroup_centralizer_le_E
    hpodd hDodd hED W1 hW1p
  exact sup_le hW1E hcentW1E

/-! ## Lemma 7.3: invariant Sylow and swapping-involution helpers -/

/-- The first assertion of Lemma 7.3.  Every `z`-invariant `p`-subgroup of
the triple stabilizer is contained in a `z`-invariant Sylow `p`-subgroup of
that triple stabilizer. -/
public theorem IsStronglyEmbedded.theorem4b_lemma73_exists_invariant_sylow
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixD M)
    {beta : conjugateCosetSpace M}
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    {P : Subgroup X}
    (hPp : IsPGroup d.data.p P)
    (hPE : P ≤ theorem4bSection7E M d.data.z beta)
    (hzP : d.data.z ∈ Subgroup.normalizer (P : Set X)) :
    ∃ Q : Subgroup X,
      theorem4bIsSylowSubgroupOf d.data.p Q
        (theorem4bSection7E M d.data.z beta) ∧
      P ≤ Q ∧
      d.data.z ∈ Subgroup.normalizer (Q : Set X) := by
  let D : Subgroup X := theorem4bSection7D M beta
  let E : Subgroup X := theorem4bSection7E M d.data.z beta
  have hDodd : Odd (Nat.card D) := by
    simpa [D, theorem4bSection7D] using
      hM.base_inf_stabilizer_card_odd hbetaNe
  have hEodd : Odd (Nat.card E) := by
    have hED : E ≤ D := by
      change theorem4bSection7D M beta ⊓
        MulAction.stabilizer X (d.data.z • beta) ≤
          theorem4bSection7D M beta
      exact inf_le_left
    exact Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hED)
  have hzE : d.data.z ∈ Subgroup.normalizer (E : Set X) := by
    simpa [E, theorem4bSection7E, theorem4bSection7D] using
      theorem4b_mem_normalizer_tripleStabilizer
        (M := M) (z := d.data.z) (beta := beta)
          d.data.hz d.data.hzM
  simpa [E] using theorem4b_exists_invariant_sylow_containing
    hEodd d.data.hz hzE d.data.hp hPp (by simpa [E] using hPE) hzP

/-- The easy Sylow branch in Lemma 7.3.  If a Sylow `p`-subgroup of the
two-point stabilizer is given, a conjugate of the standard swapping
involution still swaps the two points and normalizes that Sylow subgroup. -/
public theorem IsStronglyEmbedded.theorem4b_lemma73_exists_swap_normalizing_twoPoint_sylow
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (d : Theorem4bSixD M)
    {beta : conjugateCosetSpace M}
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    {Q : Subgroup X}
    (hQsyl : theorem4bIsSylowSubgroupOf d.data.p Q
      (theorem4bSection7D M beta)) :
    ∃ t : X,
      IsInvolution t ∧
      t ∈ Subgroup.normalizer (Q : Set X) ∧
      t • (QuotientGroup.mk 1 : conjugateCosetSpace M) = beta ∧
      t • beta = (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
  obtain ⟨t0, ht0, _ht0M, ht0Base, ht0Beta⟩ :=
    hM.corollary64_exists_swap d.data.hzM d.data.hz hbetaNe
  let D : Subgroup X := theorem4bSection7D M beta
  have hDodd : Odd (Nat.card D) := by
    simpa [D, theorem4bSection7D] using
      hM.base_inf_stabilizer_card_odd hbetaNe
  have ht0NormD : t0 ∈ Subgroup.normalizer (D : Set X) := by
    have hnorm := theorem4b_mem_normalizer_tripleStabilizer
      (M := (⊤ : Subgroup X)) (z := t0)
      (beta := (QuotientGroup.mk 1 : conjugateCosetSpace M))
      ht0 (Subgroup.mem_top t0)
    simpa [D, theorem4bSection7D, baseCoset_stabilizer, ht0Base] using hnorm
  obtain ⟨x, hxNorm⟩ :=
    corollary64_exists_conjugate_involution_normalizing_sylow
      hDodd ht0 ht0NormD d.data.hp hQsyl
  let t : X := rightConjugateElem t0 (x : X)
  have ht : IsInvolution t := isInvolution_rightConjugateElem ht0
  have hxBase : (x : X) •
      (QuotientGroup.mk 1 : conjugateCosetSpace M) =
        QuotientGroup.mk 1 := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact x.property.1
  have hxBeta : (x : X) • beta = beta :=
    MulAction.mem_stabilizer_iff.mp x.property.2
  have hxInvBase : (x : X)⁻¹ •
      (QuotientGroup.mk 1 : conjugateCosetSpace M) =
        QuotientGroup.mk 1 := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact M.inv_mem x.property.1
  have hxInvBeta : (x : X)⁻¹ • beta = beta := by
    apply MulAction.mem_stabilizer_iff.mp
    exact (MulAction.stabilizer X beta).inv_mem x.property.2
  refine ⟨t, ht, by simpa [t] using hxNorm, ?_, ?_⟩
  · calc
      t • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
          (x : X)⁻¹ • (t0 • ((x : X) •
            (QuotientGroup.mk 1 : conjugateCosetSpace M))) := by
              simp [t, rightConjugateElem, mul_smul]
      _ = (x : X)⁻¹ • (t0 •
          (QuotientGroup.mk 1 : conjugateCosetSpace M)) := by rw [hxBase]
      _ = (x : X)⁻¹ • beta := by rw [ht0Base]
      _ = beta := hxInvBeta
  · calc
      t • beta = (x : X)⁻¹ • (t0 • ((x : X) • beta)) := by
        simp [t, rightConjugateElem, mul_smul]
      _ = (x : X)⁻¹ • (t0 • beta) := by rw [hxBeta]
      _ = (x : X)⁻¹ •
          (QuotientGroup.mk 1 : conjugateCosetSpace M) := by rw [ht0Beta]
      _ = QuotientGroup.mk 1 := hxInvBase

theorem theorem4bIsSylowSubgroupOf_of_le_section7
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
theorem theorem4bIsSylowSubgroupOf_of_card_eq_section7
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
theorem theorem4bIsSylowSubgroupOf_of_subgroup_card_eq_section7
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

public theorem theorem4bIsSylowSubgroupOf_le_section7
    {X : Type u} [Group X] {p : ℕ} {P E : Subgroup X}
    (h : theorem4bIsSylowSubgroupOf p P E) : P ≤ E := by
  rcases h with ⟨Q, hQ⟩
  rw [hQ]
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨q, hq, rfl⟩
  exact q.property

private theorem lemma73_D_conjBy_eq_F
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
private theorem lemma73_tripleStabilizer_conjBy_eq_E
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
private theorem lemma73_transport_swap_between_sylows
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

private theorem lemma73_isInvolution_subtype
    {G : Type u} [Group G] {H : Subgroup G} {x : G}
    (hxH : x ∈ H) (hx : IsInvolution x) :
    IsInvolution (⟨x, hxH⟩ : H) :=
  IsInvolution.subtype hx hxH

private theorem lemma73_exists_involution_conjugator_mem
    {G : Type u} [Group G] [Finite G] (F : Subgroup G) {s t : G}
    (hsF : s ∈ F) (htF : t ∈ F)
    (hs : IsInvolution s) (ht : IsInvolution t)
    (hst : s ≠ t) (hodd : Odd (orderOf (s * t))) :
    ∃ r : F, IsInvolution (r : G) ∧
      rightConjugateElem s (r : G) = t := by
  let sF : F := ⟨s, hsF⟩
  let tF : F := ⟨t, htF⟩
  have hsFI : IsInvolution sF := lemma73_isInvolution_subtype hsF hs
  have htFI : IsInvolution tF := lemma73_isInvolution_subtype htF ht
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
private theorem lemma73_normalizer_outside_involution
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
    lemma73_exists_involution_conjugator_mem N
      (s := z) (t := (sN : X)) hzP sN.property hz hsNX hzs hodd
  refine ⟨(sN : X), (uN : X), hsNX, hsNotM, sN.property, huN,
    uN.property, hconj⟩

/-- The normalizer-growth consequence needed in the hard branch of Lemma 7.3.
It is independent of the involution and fixed-point data. -/
private theorem lemma73_normalizer_not_le_of_not_sylow_F
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
public theorem lemma73_triple_transport
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

/-- Full source-shaped Lemma 7.3, with both source branches checked. -/
public theorem IsStronglyEmbedded.theorem4b_lemma73
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
    have hQD : Q ≤ D := theorem4bIsSylowSubgroupOf_le_section7 hQsylD
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
        (theorem4bIsSylowSubgroupOf_of_le_section7 d.data.hp hQsylD hQE hED)
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
      have hPE : P ≤ E := theorem4bIsSylowSubgroupOf_le_section7 hPsyl
      have hED : E ≤ D := by
        change theorem4bSection7E M d.data.z beta ≤
          theorem4bSection7D M beta
        exact inf_le_left
      have hPD := theorem4bIsSylowSubgroupOf_of_card_eq_section7
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
    have hPE : P ≤ E := theorem4bIsSylowSubgroupOf_le_section7 hPsyl
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
      lemma73_triple_transport hM htwo d.data.hzM d.data.hz hs
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
      theorem4bIsSylowSubgroupOf_of_subgroup_card_eq_section7
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

/-- In an odd two-point stabilizer, an ambient Sylow `p`-subgroup contains
the image of a Sylow `p`-subgroup of `O_{2'}(D)`.  Here the odd core is all of
`D`; this is the exact containment input required by Corollary 6.4. -/
public theorem theorem4b_section7_sylow_contains_oddCore
    {X : Type u} [Group X] [Finite X] {D R : Subgroup X}
    {p : ℕ} (hp : Nat.Prime p) (hDodd : Odd (Nat.card D))
    (hRsyl : theorem4bIsSylowSubgroupOf p R D) :
    ∃ P₀ : Sylow p (twoPrimeCore D),
      ((((P₀ : Subgroup (twoPrimeCore D)).map
        (twoPrimeCore D).subtype).map D.subtype) : Subgroup X) ≤ R := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hOtop : twoPrimeCore D = ⊤ := by
    apply top_unique
    change (⊤ : Subgroup D) ≤ pPrimeCore 2 D
    exact le_sSup ⟨inferInstance, by simpa using hDodd.coprime_two_left⟩
  obtain ⟨Q, hQeq⟩ := hRsyl
  let O : Subgroup D := twoPrimeCore D
  let QD : Subgroup D := (Q : Subgroup D)
  have hQO : QD ≤ O := by
    change QD ≤ twoPrimeCore D
    rw [hOtop]
    exact le_top
  let QO : Subgroup O := QD.subgroupOf O
  have hQOcard : Nat.card QO = p ^ (Nat.card O).factorization p := by
    rw [natCard_subgroupOf_eq QD O hQO]
    change Nat.card (Q : Subgroup D) = _
    rw [Sylow.card_eq_multiplicity Q]
    have hOcard : Nat.card O = Nat.card D := by
      change Nat.card (twoPrimeCore D) = Nat.card D
      rw [hOtop]
      simp
    rw [hOcard]
  let P₀ : Sylow p O := Sylow.ofCard QO hQOcard
  refine ⟨?_, ?_⟩
  · simpa [O] using P₀
  · have hQOmap : QO.map O.subtype = QD := by
      simpa [QO, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQO]
    change (QO.map O.subtype).map D.subtype ≤ R
    rw [hQOmap]
    simpa [QD] using hQeq.ge

/-- Proposition 7.9.  Proposition 7.2 rules out equality in `(6B)`: equality
would make `z` normalize a Sylow subgroup by Lemma 6.2, while Corollary 6.4
forbids that normalization when theta is trivial. -/
public theorem IsStronglyEmbedded.theorem4b_proposition79
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    (h72 : Theorem4bProposition72 d.data) :
    Nat.card {x : X // x ∈ d.data.invertedSet} <
      theorem4bPrimeShare M d.data.z d.data.p := by
  have hle := d.card_inverted_le_primeShare hM
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨beta, hbetaK, hbetaNe, htheta⟩ := h72
  obtain ⟨R, hRsyl, hzNormR⟩ :=
    (d.lemma62 hM hbetaK hbetaNe).2 heq
  let D : Subgroup X := theorem4bSection7D M beta
  let D0 : Subgroup X := M ⊓ MulAction.stabilizer X beta
  have hDodd : Odd (Nat.card D) := by
    simpa [D, D0, theorem4bSection7D] using
      hM.base_inf_stabilizer_card_odd hbetaNe
  have hRD : R ≤ D := by
    obtain ⟨Q, hQeq⟩ := hRsyl
    rw [hQeq]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨q, _hq, rfl⟩
    simpa [D, D0, theorem4bSection7D] using q.property
  have hRp : IsPGroup d.data.p R := by
    obtain ⟨Q, hQeq⟩ := hRsyl
    rw [hQeq]
    simpa [D, theorem4bSection7D] using
      Q.isPGroup'.map (M ⊓ MulAction.stabilizer X beta).subtype
  have hcontains := theorem4b_section7_sylow_contains_oddCore
    d.data.hp hDodd hRsyl
  have hzNormTheta : d.data.z ∈ Subgroup.normalizer
      (corollary64Theta d.data.p D : Set X) := by
    have hthetaD : corollary64Theta d.data.p D = ⊥ := by
      simpa [D, theorem4bSection7D] using htheta
    rw [hthetaD]
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hx1 : x = 1 := by simpa using hx
    subst x
    simp
  have hcor := hM.corollary64 hX d.data hrank hT2 hinduction hbetaK hbetaNe (by
    simpa [D, theorem4bSection7D] using hzNormTheta)
  exact (hcor.2 R hRp hRD hcontains).2 hzNormR

/-- The double-transitivity assertion of Proposition 7.8.  In the
non-two-transitive branch, the equality half of `(6B)` contradicts
Proposition 7.9. -/
public theorem IsStronglyEmbedded.theorem4b_proposition78
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (d : Theorem4bSixD M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ (H : Subgroup X), H ≠ ⊤ →
      ∀ (N : Subgroup H), IsStronglyEmbedded N →
        TheoremSEConclusion N)
    (h72 : Theorem4bProposition72 d.data) :
    MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2 := by
  by_contra hnot2
  have heq := d.card_eq_primeShare_of_not_twoTransitive hM hT2 hnot2
  have hlt := hM.theorem4b_proposition79 hX d hrank hT2 hinduction h72
  omega

end CFSG.BenderSuzuki
