module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.4: source-independent local algebra

This module records the two small consequences of the Lemma 10.1 and
Proposition 10.2 packages that are used before the recognized-model endpoint:
the `p'` order of `A = O_{p'}(V)`, and the nontriviality of `[A,P]`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The Lemma 10.1 subgroup `A` has order prime to the selected prime `p`. -/
public theorem lemma114_A1_coprime_card
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t) :
    Nat.Coprime d.choice.p (Nat.card d.choice.initial.A1) := by
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  rw [d.A1_eq_pPrimeCore]
  rw [Subgroup.card_map_of_injective
    (peterfalviV D t).subtype_injective]
  exact pPrimeCore_coprime_card

/-- Proposition 10.2(a,c) makes the commutator `[A,P]` nontrivial. -/
public theorem lemma114_commutator_A1_P_ne_bot
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h102 : Proposition102Conclusion M W D E t d) :
    ⁅d.choice.initial.A1, d.choice.P⁆ ≠ ⊥ := by
  rw [← h102.part_a.derived_inf_V]
  exact ne_bot_of_le_ne_bot h102.exponent.R_ne_bot
    h102.exponent.R_le_derived_inf_V

/-- The subgroup selected in Lemma 10.1 satisfies Peterfalvi's rank-one
hypothesis `(B1)`.  The rank bound is inherited from the stronger Section 10
statement that the full normalizer `N_X(P)` has 2-rank one. -/
public theorem lemma114_hypothesisB1
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t) :
    PFchapter2.HypothesisB1 X
      (peterfalviV (M ⊓ rightConjugate M t) t)
      d.choice.P d.choice.p := by
  refine
    { p_prime := d.choice.p_prime
      P_le_V := d.choice.P_le_V
      P_card := d.P_card
      centralizer_has_involution := ?_
      centralizer_has_two_rank_one := ?_ }
  · refine ⟨t, ?_, ht⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hpP
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (d.choice.P_le_V hpP).2
  · intro hcentralizerRank
    apply d.not_twoRankAtLeastTwo_normalizer hM ht htM d83
    exact hcentralizerRank.map_of_injective
      (Subgroup.inclusion (centralizer_le_normalizer d.choice.P))
      (Subgroup.inclusion_injective
        (centralizer_le_normalizer d.choice.P))

/-! The source next proves `C_V(A) ≤ A`.  The core argument only uses that
`V = AP`, with `A ◁ V`, `A ∩ P = 1`, and `P` a Sylow subgroup of prime
order.  If `C_V(A)` contained an element outside `A`, its image in `V/A`
would have order `p`; hence `C_V(A)` would contain a nontrivial `p`-subgroup.
Conjugating a Sylow overgroup into `P` and using normality of `C_V(A)` then
forces `P ≤ C_V(A)`, contradicting `[A,P] ≠ 1`. -/

/-- A normal complement with a noncentral prime-order Sylow factor contains
its fixed-point subgroup.  This is the source-independent core of the
inclusion `C_V(A) ≤ A` in Lemma 11.4. -/
public theorem lemma114_inf_centralizer_le_of_prime_complement
    {X : Type u} [Group X] [Finite X]
    {V A P : Subgroup X} {p : ℕ}
    (hp : p.Prime)
    (hAV : A ≤ V) (hPV : P ≤ V)
    (hAnormal : (A.subgroupOf V).Normal)
    (hVmul : (V : Set X) = (A : Set X) * (P : Set X))
    (hdisj : Disjoint A P)
    (hPcard : Nat.card P = p)
    (hPsylV : theorem4bIsSylowSubgroupOf p P V)
    (hcomm : ⁅A, P⁆ ≠ ⊥) :
    V ⊓ Subgroup.centralizer (A : Set X) ≤ A := by
  let AV : Subgroup V := A.subgroupOf V
  let PV : Subgroup V := P.subgroupOf V
  have hsupV : AV ⊔ PV = ⊤ := by
    calc
      AV ⊔ PV = (A ⊔ P).subgroupOf V := by
        simpa [AV, PV] using (Subgroup.subgroupOf_sup hAV hPV).symm
      _ = V.subgroupOf V := by
        rw [show A ⊔ P = V by
          apply le_antisymm
          · exact sup_le hAV hPV
          · intro x hx
            have hx' : x ∈ (A : Set X) * (P : Set X) := by
              rw [← hVmul]
              exact hx
            rcases Set.mem_mul.mp hx' with ⟨a, ha, q, hq, h⟩
            rw [← h]
            exact Subgroup.mul_mem_sup ha hq]
      _ = ⊤ := Subgroup.subgroupOf_self V
  have hdisjV : Disjoint PV AV := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxA
    have hxOne : (x : X) = 1 :=
      Subgroup.disjoint_def.mp hdisj hxA hxP
    exact Subtype.ext hxOne
  have hmulV : (PV : Set V) * (AV : Set V) = Set.univ := by
    rw [← Subgroup.mul_normal PV AV, sup_comm, hsupV]
    rfl
  have hcomp : PV.IsComplement' AV :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjV hmulV
  have hquot : Nat.card (V ⧸ AV) = p := by
    calc
      Nat.card (V ⧸ AV) = AV.index := by rw [Subgroup.index_eq_card]
      _ = Nat.card PV := hcomp.index_eq_card
      _ = Nat.card P := natCard_subgroupOf_eq P V hPV
      _ = p := hPcard
  letI : Fact p.Prime := ⟨hp⟩
  let q : V →* (V ⧸ AV) := QuotientGroup.mk' AV
  intro x hx
  by_contra hxA
  let xV : V := ⟨x, hx.1⟩
  have hxqne : q xV ≠ 1 := by
    intro hxq
    apply hxA
    have : xV ∈ AV := (QuotientGroup.eq_one_iff xV).mp hxq
    exact this
  have horderq : orderOf (q xV) = p := by
    have hdvd : orderOf (q xV) ∣ p := by
      simpa [hquot] using (orderOf_dvd_natCard (q xV))
    exact ((Nat.dvd_prime hp).mp hdvd).resolve_left
      (by intro h; exact hxqne (orderOf_eq_one_iff.mp h))
  have hporder : p ∣ orderOf xV := by
    rw [← horderq]
    exact orderOf_map_dvd q xV
  have hpC : p ∣ Nat.card ↑(V ⊓ Subgroup.centralizer (A : Set X)) := by
    let xC : ↑(V ⊓ Subgroup.centralizer (A : Set X)) := ⟨x, hx⟩
    have horderC :
        orderOf xC ∣ Nat.card ↑(V ⊓ Subgroup.centralizer (A : Set X)) :=
      orderOf_dvd_natCard _
    have horders : orderOf xV = orderOf xC := by
      rw [← Subgroup.orderOf_coe xV, ← Subgroup.orderOf_coe xC]
    exact hporder.trans (by simpa [horders] using horderC)
  let C : Subgroup X := V ⊓ Subgroup.centralizer (A : Set X)
  let CV : Subgroup V := C.subgroupOf V
  have hCVeq : CV = Subgroup.centralizer (AV : Set V) := by
    ext z
    constructor
    · intro hz
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      apply Subtype.ext
      have hzC : (z : X) ∈ C := hz
      exact (Subgroup.mem_centralizer_iff.mp hzC.2) (a : X) ha
    · intro hz
      change (z : X) ∈ C
      refine ⟨z.property, ?_⟩
      change (z : X) ∈ Subgroup.centralizer (A : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      let aV : V := ⟨a, hAV ha⟩
      have haAV : aV ∈ AV := ha
      exact congrArg Subtype.val
        ((Subgroup.mem_centralizer_iff.mp hz) aV haAV)
  have hCVnormal : CV.Normal := by
    letI : AV.Normal := hAnormal
    rw [hCVeq]
    infer_instance
  let T : Sylow p CV := default
  have hpCV : p ∣ Nat.card CV := by
    have hcardCV : Nat.card CV = Nat.card C := by
      simpa [CV] using natCard_subgroupOf_eq C V inf_le_left
    rw [hcardCV]
    simpa [C] using hpC
  have hTne : (T : Subgroup CV) ≠ ⊥ := T.ne_bot_of_dvd_card hpCV
  obtain ⟨U, hUT⟩ := T.exists_comap_subtype_eq
  rcases hPsylV with ⟨P0, hP0map⟩
  have hPVeq : PV = (P0 : Subgroup V) := by
    apply Subgroup.map_injective V.subtype_injective
    simpa [PV, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPV] using
      hP0map
  obtain ⟨v, hv⟩ := MulAction.exists_smul_eq V U P0
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
  have hzU : ((z : CV) : V) ∈ (U : Subgroup V) := by
    have hzcomap : (z : CV) ∈ U.comap CV.subtype := by
      rw [hUT]
      exact z.property
    exact hzcomap
  let y : V := v * ((z : CV) : V) * v⁻¹
  have hyP0 : y ∈ (P0 : Subgroup V) := by
    have hyconj : y ∈ (MulAut.conj v) • (U : Subgroup V) := by
      exact Subgroup.smul_mem_pointwise_smul
        ((z : CV) : V) (MulAut.conj v) (U : Subgroup V) hzU
    have heq : (MulAut.conj v) • (U : Subgroup V) =
        (P0 : Subgroup V) := by
      rw [← Sylow.coe_subgroup_smul, hv]
    rw [heq] at hyconj
    exact hyconj
  have hyCV : y ∈ CV := by
    simpa [y] using
      hCVnormal.conj_mem ((z : CV) : V) (z : CV).property v
  have hyne : y ≠ 1 := by
    intro hy
    apply hzne
    apply Subtype.ext
    apply Subtype.ext
    calc
      ((z : CV) : V) = v⁻¹ * y * v := by simp [y, mul_assoc]
      _ = 1 := by rw [hy]; simp
  have hyP : (y : X) ∈ P := by
    change y ∈ PV
    rw [hPVeq]
    exact hyP0
  have hyC : (y : X) ∈ C := hyCV
  let CP : Subgroup P := (C ⊓ P).subgroupOf P
  have hCPne : CP ≠ ⊥ := by
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    let yP : P := ⟨(y : X), hyP⟩
    let yCP : CP := ⟨yP, hyC, hyP⟩
    refine ⟨yCP, ?_⟩
    intro hyCP
    apply hyne
    apply Subtype.ext
    exact congrArg (fun w : CP => ((w : P) : X)) hyCP
  letI : Fact (Nat.card P).Prime := ⟨by simpa [hPcard] using hp⟩
  have hCPtop : CP = ⊤ :=
    (Subgroup.eq_bot_or_eq_top_of_prime_card CP).resolve_left hCPne
  have hPleC : P ≤ C := by
    intro z hzP
    let zP : P := ⟨z, hzP⟩
    have hzCP : zP ∈ CP := by
      rw [hCPtop]
      exact Subgroup.mem_top zP
    exact hzCP.1
  apply hcomm
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro z hzP
  exact ((Subgroup.mem_centralizer_iff.mp (hPleC hzP).2) a ha).symm

/-- Lemma 10.1 and Proposition 10.2 imply the fixed-point inclusion used in
the recognized-model part of Lemma 11.4. -/
public theorem lemma114_V_inf_centralizer_A1_le_A1
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h102 : Proposition102Conclusion M W D E t d) :
    peterfalviV D t ⊓
        Subgroup.centralizer (d.choice.initial.A1 : Set X) ≤
      d.choice.initial.A1 := by
  have hAV : d.choice.initial.A1 ≤ peterfalviV D t := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hPsylV : theorem4bIsSylowSubgroupOf d.choice.p d.choice.P
      (peterfalviV D t) :=
    theorem4bIsSylowSubgroupOf_of_between d.choice.p_prime d.P_sylow_D
      d.choice.P_le_V inf_le_left
  exact lemma114_inf_centralizer_le_of_prime_complement
    d.choice.p_prime hAV d.choice.P_le_V
    d.choice.initial.A1_normal_V d.V_eq_mul
    d.choice.initial.A1_disjoint_P d.P_card hPsylV
    (lemma114_commutator_A1_P_ne_bot d h102)

/-! The next helper is the second Corollary 8.5 application in the source
proof.  It is kept as a wrapper around the already checked uniform
`Lemma101ChoiceData` theorem: the callback remains exactly the recognized
model endpoint for Corollary 8.5, and no Lemma 11.4 conclusion is assumed. -/

/-- Reapply Corollary 8.5 to the selected `A₁` from Lemma 10.1, retaining
the Sylow/root data constructed in the proof. -/
public theorem lemma114_corollary85Supported_A1
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t) :
    Nonempty (Corollary85SupportedConclusion M t d83.u
      d.choice.initial.A1 d.choice.P) := by
  have hPnormA : d.choice.P ≤
      Subgroup.normalizer (d.choice.initial.A1 : Set X) := by
    exact d.choice.P_le_V.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (by rw [d.choice.initial.A1_eq]; exact inf_le_left)).mp
        d.choice.initial.A1_normal_V)
  exact d.choice.corollary85_supported_of_nontrivial_invariant
    hM ht htM d83 h84 le_rfl d.choice.initial.A1_ne_bot hPnormA

/-- Project the source-facing Corollary 8.5 conclusion for `A₁`. -/
public theorem lemma114_corollary85_A1
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t) :
    Nonempty (Corollary85Conclusion M t d83.u
      d.choice.initial.A1 d.choice.P) := by
  obtain ⟨supported⟩ := lemma114_corollary85Supported_A1
    hM ht htM d83 h84 d
  exact ⟨supported.conclusion⟩

/-- Retain the Proposition 8.4 quotient Borel and central-kernel support for
the selected subgroup `A₁`. -/
public theorem lemma114_modelSupport_A1
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (hsupport : Proposition84ModelSupportStatement M t d83.u)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t) :
    Proposition84ModelSupport M d.choice.initial.A1 := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := peterfalviV D t
  have hA1V : d.choice.initial.A1 ≤ V := by
    rw [d.choice.initial.A1_eq]
    exact inf_le_left
  have hVeq : V = D ⊓ Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [D, V, peterfalviV] using d83.centralizer_eq
  have hA1local : d.choice.initial.A1 ≤
      (M ⊓ rightConjugate M t) ⊓
        Subgroup.centralizer ({d83.u} : Set X) := by
    simpa [D, ← hVeq] using hA1V
  obtain ⟨j, hjI, hjCY, hjne⟩ := d.choice.Y_nontrivial_centralizer
  have hjJ : j ∈ d.choice.initial.J := by
    change j ∈ (d.choice.initial.J : Set X)
    rw [d.choice.initial.J_eq_centralizer]
    exact ⟨hjI, hjCY⟩
  have hjCA1 : j ∈
      Subgroup.centralizer (d.choice.initial.A1 : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a haA
    rw [d.choice.initial.A1_eq] at haA
    exact (Subgroup.mem_centralizer_iff.mp haA.2 j hjJ).symm
  have hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t d.choice.initial.A1 :=
    ⟨j, hjI, centralizer_le_normalizer _ hjCA1, hjne⟩
  exact hsupport d.choice.initial.A1 hA1local
    d.choice.initial.A1_ne_bot hI

/-- The involution `t` belongs to the embedded `2`-residual attached to
`A₁`, because `A₁ ≤ V = C_D(t)`. -/
public theorem lemma114_t_mem_residual_A1
    {X : Type u} [Group X] [Finite X]
    {D A : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hAV : A ≤ peterfalviV D t) :
    t ∈ centralizerTwoPrimeResidual A := by
  have htC : t ∈ Subgroup.centralizer (A : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hAV ha).2
  exact zpowers_le_centralizerTwoPrimeResidual_of_isInvolution
    A ht htC (Subgroup.mem_zpowers t)

/-- Elements of `A ∩ F₀` are central in `F₀`: the residual `F₀` centralizes
`A` by construction.  The center is mapped back to the ambient group, since
`Subgroup.center F₀` is a subgroup of the subtype `F₀`. -/
public theorem lemma114_A1_inf_residual_le_center
    {X : Type u} [Group X] [Finite X]
    (A : Subgroup X) :
    A ⊓ centralizerTwoPrimeResidual A ≤
      (Subgroup.center (centralizerTwoPrimeResidual A)).map
        (centralizerTwoPrimeResidual A).subtype := by
  intro x hx
  rw [Subgroup.mem_map]
  let xf : centralizerTwoPrimeResidual A := ⟨x, hx.2⟩
  refine ⟨xf, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.mp
    (centralizerTwoPrimeResidual_le_ambientCentralizer A y.property)
    x hx.1).symm

/-- If the fixed-point part of `V` in `F₀` lies in `A`, then it is central in
`F₀`; this is the ambient form of the source inclusions
`V ∩ F₀ ≤ A ∩ F₀ ≤ Z(F₀)`. -/
public theorem lemma114_V_inf_residual_le_center
    {X : Type u} [Group X] [Finite X]
    {V A : Subgroup X}
    (hCVA : V ⊓ Subgroup.centralizer (A : Set X) ≤ A) :
    V ⊓ centralizerTwoPrimeResidual A ≤
      (Subgroup.center (centralizerTwoPrimeResidual A)).map
        (centralizerTwoPrimeResidual A).subtype := by
  intro x hx
  have hxA : x ∈ A := hCVA ⟨hx.1,
    centralizerTwoPrimeResidual_le_ambientCentralizer A hx.2⟩
  exact lemma114_A1_inf_residual_le_center A ⟨hxA, hx.2⟩

/-- The preceding centrality statement restricts to the fixed points of `t`
inside `D ∩ F₀`, the exact configuration consumed by the `[II4]` endpoint. -/
public theorem lemma114_fixed_D_inf_residual_le_center
    {X : Type u} [Group X] [Finite X]
    {D A : Subgroup X} {t : X}
    (hfixed : peterfalviV D t ⊓ centralizerTwoPrimeResidual A ≤
      (Subgroup.center (centralizerTwoPrimeResidual A)).map
        (centralizerTwoPrimeResidual A).subtype) :
    (D ⊓ centralizerTwoPrimeResidual A) ⊓
        Subgroup.centralizer ({t} : Set X) ≤
      (Subgroup.center (centralizerTwoPrimeResidual A)).map
        (centralizerTwoPrimeResidual A).subtype := by
  intro x hx
  apply hfixed
  exact ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩

/-- The exact fixed-point configuration passed to the recognized-model
endpoint `[II4; 3.2(e), 2.8(a)]`. -/
public theorem lemma114_fixed_D_inf_residual_A1_le_center
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (h102 : Proposition102Conclusion M W D E t d) :
    (D ⊓ centralizerTwoPrimeResidual d.choice.initial.A1) ⊓
        Subgroup.centralizer ({t} : Set X) ≤
      (Subgroup.center (centralizerTwoPrimeResidual d.choice.initial.A1)).map
        (centralizerTwoPrimeResidual d.choice.initial.A1).subtype := by
  exact lemma114_fixed_D_inf_residual_le_center
    (lemma114_V_inf_residual_le_center
      (lemma114_V_inf_centralizer_A1_le_A1 d h102))

end CFSG.BenderSuzuki
