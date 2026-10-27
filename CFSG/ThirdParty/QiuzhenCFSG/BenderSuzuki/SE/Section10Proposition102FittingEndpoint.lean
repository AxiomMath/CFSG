module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102ExponentData
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2(d--e): source-specific Fitting endpoint

This module proves that the complementary factor in the Fitting subgroup is
trivial.  It uses the checked normal Sylow split, the uniform centralizer
statement from Lemma 10.1, and the coprime-action centralization theorem from
`Section10Proposition102Fitting`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

universe u

open PFAppendixIII PFchapter1section1
open scoped Pointwise

private lemma proposition102_subgroupOf_le_pPrimeCore_map
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K H : Subgroup G} (hKH : K ≤ H)
    [hKN : (K.subgroupOf H).Normal]
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p (↥H)).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    natCard_subgroupOf_eq K H hKH
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact hcop
  have hsub : K.subgroupOf H ≤ pPrimeCore p (↥H) :=
    le_sSup ⟨hKN, hcop'⟩
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKH] using
    (Subgroup.map_mono (f := H.subtype) hsub)

/-- An anti-fixed element in an internal direct product has anti-fixed
components.  This is the set-level companion to the inverted-cardinality
product lemma. -/
public theorem proposition102_inverted_mem_factor_of_internalDirectProduct
    {X : Type u} [Group X]
    {H A B : Subgroup X} {t : X}
    (hprod : Section2.IsInternalDirectProduct H A B)
    (htnormA : t ∈ Subgroup.normalizer (A : Set X))
    (htnormB : t ∈ Subgroup.normalizer (B : Set X))
    {x : X} (hxH : x ∈ H)
    (hxanti : t * x * t⁻¹ = x⁻¹) :
    ∃ a ∈ A, ∃ b ∈ B,
      x = a * b ∧ t * a * t⁻¹ = a⁻¹ ∧ t * b * t⁻¹ = b⁻¹ := by
  rcases hprod.mul_surjective x hxH with ⟨a, ha, b, hb, hab⟩
  have hta : t * a * t⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp htnormA a).mp ha
  have htb : t * b * t⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp htnormB b).mp hb
  have hcomp :
      (t * a * t⁻¹) * (t * b * t⁻¹) = a⁻¹ * b⁻¹ := by
    calc
      (t * a * t⁻¹) * (t * b * t⁻¹) = t * (a * b) * t⁻¹ := by group
      _ = t * x * t⁻¹ := by rw [hab]
      _ = x⁻¹ := hxanti
      _ = (a * b)⁻¹ := by rw [hab]
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = a⁻¹ * b⁻¹ := by
        exact (show Commute a b from hprod.commute a ha b hb).inv_inv.eq.symm
  let lhs : A × B :=
    (⟨t * a * t⁻¹, hta⟩, ⟨t * b * t⁻¹, htb⟩)
  let rhs : A × B := (⟨a⁻¹, A.inv_mem ha⟩, ⟨b⁻¹, B.inv_mem hb⟩)
  have hpair : lhs = rhs := by
    apply Subgroup.mul_injective_of_disjoint
      (show Disjoint A B by rw [disjoint_iff, hprod.inf_eq_bot])
    simpa [lhs, rhs] using hcomp
  refine ⟨a, ha, b, hb, hab, ?_, ?_⟩
  · exact congrArg (fun z : A × B => (z.1 : X)) hpair
  · exact congrArg (fun z : A × B => (z.2 : X)) hpair

/-- A normal subgroup disjoint from a Sylow subgroup has order prime to the
Sylow prime. -/
public theorem proposition102_coprime_card_of_normal_disjoint_sylow
    {X : Type u} [Group X] [Finite X]
    {p : ℕ} {M C P : Subgroup X}
    (hp : p.Prime)
    (hCM : C ≤ M)
    (hPM : P ≤ M)
    (hPsyl : theorem4bIsSylowSubgroupOf p P M)
    (hCnormal : (C.subgroupOf M).Normal)
    (hinf : C ⊓ P = ⊥) :
    Nat.Coprime p (Nat.card C) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases hPsyl with ⟨S, hSP⟩
  let PM : Subgroup M := P.subgroupOf M
  have hPM_eq : PM = (S : Subgroup M) := by
    apply Subgroup.map_injective M.subtype_injective
    simpa [PM, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPM] using hSP
  let CM : Subgroup M := C.subgroupOf M
  let T : Sylow p CM := default
  obtain ⟨U, hUT⟩ := T.exists_comap_subtype_eq
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M U S
  have hTbot : (T : Subgroup CM) = ⊥ := by
    apply le_antisymm
    · intro x hxT
      have hxU : ((x : CM) : M) ∈ (U : Subgroup M) := by
        have hxComap : (x : CM) ∈ U.comap CM.subtype := by
          rw [hUT]
          exact hxT
        exact hxComap
      let y : M := m * ((x : CM) : M) * m⁻¹
      have hyS : y ∈ (S : Subgroup M) := by
        have hyConj : y ∈ (MulAut.conj m) • (U : Subgroup M) := by
          exact Subgroup.smul_mem_pointwise_smul
            ((x : CM) : M) (MulAut.conj m) (U : Subgroup M) hxU
        have heq : (MulAut.conj m) • (U : Subgroup M) =
            (S : Subgroup M) := by
          rw [← Sylow.coe_subgroup_smul, hm]
        rw [heq] at hyConj
        exact hyConj
      have hxCM : ((x : CM) : M) ∈ CM := x.property
      have hyCM : y ∈ CM := by
        simpa [y] using hCnormal.conj_mem ((x : CM) : M) hxCM m
      have hyPM : y ∈ PM := by
        rw [hPM_eq]
        exact hyS
      have hyInf : ((y : M) : X) ∈ C ⊓ P := ⟨hyCM, hyPM⟩
      have hyOneX : ((y : M) : X) = 1 := by
        simpa [hinf] using hyInf
      have hyOneM : y = 1 := Subtype.ext hyOneX
      have hxOneM : ((x : CM) : M) = 1 := by
        calc
          ((x : CM) : M) = m⁻¹ * y * m := by simp [y, mul_assoc]
          _ = 1 := by rw [hyOneM]; simp
      exact Subtype.ext hxOneM
    · exact bot_le
  apply hp.coprime_iff_not_dvd.mpr
  intro hpdvdC
  have hpdvdCM : p ∣ Nat.card CM := by
    simpa [CM, natCard_subgroupOf_eq C M hCM] using hpdvdC
  exact (T.ne_bot_of_dvd_card hpdvdCM) hTbot

/-- The complementary `r'`-factor in the Fitting subgroup is trivial. -/
public theorem proposition102_fitting_complement_eq_bot
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hA : Proposition102PartAConclusion M W D E
      (peterfalviV D t) t d)
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D)
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (htnormE : t ∈ Subgroup.normalizer (E : Set X))
    (hVC : peterfalviV D t ⊓
      Subgroup.centralizer (peterfalviKSet D t) = ⊥)
    (e : Proposition102ExponentConclusion M W D E t d)
    (hHnormalD :
      (((derivedSubgroup E).map E.subtype).subgroupOf D).Normal)
    (Q : Subgroup X)
    (hprodF : Section2.IsInternalDirectProduct
      (fittingSubgroupOf (peterfalviV D t)) e.R Q)
    (hQeq : Q =
      (pPrimeCore e.r (fittingSubgroupOf (peterfalviV D t))).map
        (fittingSubgroupOf (peterfalviV D t)).subtype) :
    Q = ⊥ := by
  classical
  let H : Subgroup X := (derivedSubgroup E).map E.subtype
  let V : Subgroup X := peterfalviV D t
  let P : Subgroup X := d.choice.P
  let A1 : Subgroup X := d.choice.initial.A1
  let R : Subgroup X := e.R
  let F : Subgroup X := fittingSubgroupOf V
  let S : Subgroup X := (pCore e.r H).map H.subtype
  let S2 : Subgroup X := (pPrimeCore e.r H).map H.subtype
  let C1 : Subgroup X := subgroupCentralizerIn S R
  let Kset : Set X := peterfalviKSet D t
  letI : Fact e.r.Prime := ⟨e.r_prime⟩
  letI : Fact d.choice.p.Prime := ⟨d.choice.p_prime⟩
  have hHleD : H ≤ D :=
    (Subgroup.map_subtype_le (derivedSubgroup E)).trans hED
  have hVleD : V ≤ D := inf_le_left
  have hR_eq : R = S ⊓ V := by
    simpa [R, S, H, V] using e.R_eq
  have hRleS : R ≤ S := by rw [hR_eq]; exact inf_le_left
  have hRleV : R ≤ V := by rw [hR_eq]; exact inf_le_right
  have hRne : R ≠ ⊥ := by simpa [R] using e.R_ne_bot
  have hRleA1 : R ≤ A1 := by simpa [R, A1] using e.R_le_A1
  have hQleF : Q ≤ F := by simpa [F, V] using hprodF.right_le
  have hFleV : F ≤ V := fittingSubgroupOf_le V
  have hQleV : Q ≤ V := hQleF.trans hFleV
  have hQleD : Q ≤ D := hQleV.trans hVleD
  have hQR : ⁅Q, R⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact hprodF.commute r hr q hq
  have hcentRP : subgroupCentralizerIn R P = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxH : x ∈ subgroupCentralizerIn H P :=
      ⟨hRleS.trans (by
        simpa [S] using Subgroup.map_subtype_le (pCore e.r H)) hx.1, hx.2⟩
    have hHP : subgroupCentralizerIn H P = ⊥ := by
      simpa [H, P] using hA.centralizer_derived_P
    simpa [hHP] using hxH
  have hPQbot : P ⊓ Q = ⊥ := by
    by_contra hne
    have hcardInfDvd : Nat.card (P ⊓ Q : Subgroup X) ∣ d.choice.p := by
      rw [← d.P_card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcardInfNeOne : Nat.card (P ⊓ Q : Subgroup X) ≠ 1 :=
      ((Subgroup.one_lt_card_iff_ne_bot (P ⊓ Q : Subgroup X)).mpr hne).ne'
    have hcardInf : Nat.card (P ⊓ Q : Subgroup X) = d.choice.p :=
      (d.choice.p_prime.eq_one_or_self_of_dvd _ hcardInfDvd).resolve_left
        hcardInfNeOne
    have hPleQ : P ≤ Q := by
      have hinfP : P ⊓ Q = P :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardInf, d.P_card])
      exact inf_eq_left.mp hinfP
    have hRcentP : R ≤ Subgroup.centralizer (P : Set X) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (hprodF.commute r hr p (hPleQ hp)).symm
    have hRleBot : R ≤ ⊥ := by
      intro r hr
      have hrC : r ∈ subgroupCentralizerIn R P := ⟨hr, hRcentP hr⟩
      simpa [hcentRP] using hrC
    exact hRne (le_bot_iff.mp hRleBot)
  have hQnormalV : (Q.subgroupOf V).Normal := by
    have hFnormalV : (F.subgroupOf V).Normal := by
      rw [show F = (fittingSubgroup V).map V.subtype by rfl]
      rw [subgroupOf_map_subtype_eq]
      exact inferInstance
    have hVnormF : V ≤ Subgroup.normalizer (F : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFleV).mp hFnormalV
    have hVnormQ : V ≤ Subgroup.normalizer (Q : Set X) := by
      rw [hQeq]
      exact hVnormF.trans
        (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
          F (pPrimeCore e.r F))
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQleV).mpr hVnormQ
  have hPsylV : theorem4bIsSylowSubgroupOf d.choice.p P V := by
    exact theorem4bIsSylowSubgroupOf_of_between d.choice.p_prime
      (by simpa [P] using d.P_sylow_D)
      (by simpa [P, V] using d.choice.P_le_V) hVleD
  have hQcopP : Nat.Coprime d.choice.p (Nat.card Q) := by
    exact proposition102_coprime_card_of_normal_disjoint_sylow
      d.choice.p_prime hQleV (by simpa [P, V] using d.choice.P_le_V)
      hPsylV hQnormalV (by simpa [P, inf_comm] using hPQbot)
  have hQleA1 : Q ≤ A1 := by
    letI : (Q.subgroupOf V).Normal := hQnormalV
    rw [show A1 = (pPrimeCore d.choice.p V).map V.subtype by
      simpa [A1, V] using d.A1_eq_pPrimeCore]
    exact proposition102_subgroupOf_le_pPrimeCore_map
      (p := d.choice.p) hQleV hQcopP
  have hHnil : Group.IsNilpotent H := by
    simpa [H] using proposition102_derived_nilpotent hA
  have hprodH : Section2.IsInternalDirectProduct H S S2 := by
    simpa [S, S2] using proposition102_internalDirectProduct_map_subtype_top
      (proposition102_nilpotent_internalDirectProduct_pCore_pPrimeCore
        e.r e.r_prime hHnil)
  have htNormH : t ∈ Subgroup.normalizer (H : Set X) := by
    simpa [H] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        E (derivedSubgroup E)) htnormE
  have htNormS : t ∈ Subgroup.normalizer (S : Set X) := by
    simpa [S] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        H (pCore e.r H)) htNormH
  have htNormS2 : t ∈ Subgroup.normalizer (S2 : Set X) := by
    simpa [S2] using
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        H (pPrimeCore e.r H)) htNormH
  have htNormV : t ∈ Subgroup.normalizer (V : Set X) := by
    have htNormC := proposition102_involution_mem_normalizer_centralizer_singleton ht
    exact (Subgroup.le_normalizer_inf
      (A := Subgroup.zpowers t)
      (H := D) (K := Subgroup.centralizer ({t} : Set X))
      (Subgroup.zpowers_le.mpr htnormD)
      (Subgroup.zpowers_le.mpr htNormC)) (Subgroup.mem_zpowers t)
  have htNormR : t ∈ Subgroup.normalizer (R : Set X) := by
    rw [hR_eq]
    exact (Subgroup.le_normalizer_inf
      (A := Subgroup.zpowers t)
      (Subgroup.zpowers_le.mpr htNormS)
      (Subgroup.zpowers_le.mpr htNormV)) (Subgroup.mem_zpowers t)
  have htNormCentR : t ∈ Subgroup.normalizer
      (Subgroup.centralizer (R : Set X) : Set X) := by
    exact (le_normalizer_centralizer_of_le_normalizer
      (Subgroup.zpowers_le.mpr htNormR)) (Subgroup.mem_zpowers t)
  have htNormC1 : t ∈ Subgroup.normalizer (C1 : Set X) := by
    simpa [C1, subgroupCentralizerIn] using
      (Subgroup.le_normalizer_inf
        (A := Subgroup.zpowers t)
        (Subgroup.zpowers_le.mpr htNormS)
        (Subgroup.zpowers_le.mpr htNormCentR)) (Subgroup.mem_zpowers t)
  have hDnormH : D ≤ Subgroup.normalizer (H : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHleD).mp (by
      simpa [H] using hHnormalD)
  have hDnormS : D ≤ Subgroup.normalizer (S : Set X) :=
    hDnormH.trans
      (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
        H (pCore e.r H))
  have hQnormS : Q ≤ Subgroup.normalizer (S : Set X) :=
    hQleD.trans hDnormS
  have hPleV : P ≤ V := by
    simpa [P, V] using d.choice.P_le_V
  have hPnormS : P ≤ Subgroup.normalizer (S : Set X) := by
    exact hPleV.trans (hVleD.trans hDnormS)
  have hPnormV : P ≤ Subgroup.normalizer (V : Set X) :=
    hPleV.trans (Subgroup.le_normalizer (H := V))
  have hPnormR : P ≤ Subgroup.normalizer (R : Set X) := by
    rw [hR_eq]
    exact Subgroup.le_normalizer_inf hPnormS hPnormV
  have hsetUniform := d.centralizer_uniform R hRleA1 hRne hPnormR
  have hSleH : S ≤ H := by
    simpa [S] using Subgroup.map_subtype_le (pCore e.r H)
  have hSleD : S ≤ D := hSleH.trans hHleD
  have hC1leS : C1 ≤ S := by
    intro x hx
    exact hx.1
  have hC1odd : Odd (Nat.card C1) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le (hC1leS.trans hSleD))
  have hQCR : Q ≤ Subgroup.centralizer (C1 : Set X) := by
    have hQleCR : Q ≤ Subgroup.centralizer (R : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQR
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    obtain ⟨yz, _hyz, hyzEq⟩ :=
      (PFchapter1section1.lemma_a t C1 ht hC1odd htNormC1).1.surjOn hc
    have hyS : (yz.1 : X) ∈ S := hC1leS yz.1.property.1
    have hyV : (yz.1 : X) ∈ V :=
      ⟨hSleD hyS, yz.1.property.2⟩
    have hyR : (yz.1 : X) ∈ R := by
      rw [hR_eq]
      exact ⟨hyS, hyV⟩
    have hyq : (yz.1 : X) * q = q * (yz.1 : X) :=
      Subgroup.mem_centralizer_iff.mp (hQleCR hq) _ hyR
    have hzC1 : (yz.2 : X) ∈ C1 := yz.2.property.1
    have hzS : (yz.2 : X) ∈ S := hC1leS hzC1
    have hzK : (yz.2 : X) ∈ Kset :=
      ⟨hSleD hzS, yz.2.property.2⟩
    have hzCR : (yz.2 : X) ∈ Subgroup.centralizer (R : Set X) := hzC1.2
    have hzCA1 : (yz.2 : X) ∈ Subgroup.centralizer (A1 : Set X) := by
      have hzPair : (yz.2 : X) ∈
          {x : X | x ∈ peterfalviKSet D t ∧
            x ∈ Subgroup.centralizer (R : Set X)} := by
        simpa [Kset] using And.intro hzK hzCR
      rw [hsetUniform] at hzPair
      exact hzPair.2
    have hqz : q * (yz.2 : X) = (yz.2 : X) * q :=
      Subgroup.mem_centralizer_iff.mp hzCA1 q (hQleA1 hq)
    rw [← hyzEq]
    calc
      ((yz.1 : X) * (yz.2 : X)) * q =
          (yz.1 : X) * ((yz.2 : X) * q) := by group
      _ = (yz.1 : X) * (q * (yz.2 : X)) := by rw [hqz]
      _ = ((yz.1 : X) * q) * (yz.2 : X) := by group
      _ = (q * (yz.1 : X)) * (yz.2 : X) := by rw [hyq]
      _ = q * ((yz.1 : X) * (yz.2 : X)) := by group
  have hSr : IsPGroup e.r S := by
    simpa [S] using (pCore_isPGroup (G := H) (p := e.r)).map H.subtype
  have hQcopS : Nat.Coprime (Nat.card Q) (Nat.card S) := by
    have hQcopr : Nat.Coprime e.r (Nat.card Q) := by
      rw [hQeq, Subgroup.card_map_of_injective F.subtype_injective]
      exact pPrimeCore_coprime_card
    obtain ⟨n, hn⟩ := hSr.exists_card_eq
    rw [hn]
    exact hQcopr.symm.pow_right n
  have hQS : ⁅Q, S⁆ = ⊥ :=
    proposition102_commutator_eq_bot_of_coprime_centralizer
      hSr hRleS hQnormS hQcopS hQR hQCR
  have hKH : Kset ⊆ H := by
    intro x hx
    have hxK : x ∈ Subgroup.closure Kset := Subgroup.subset_closure hx
    have hcl : Subgroup.closure Kset ≤ lemma106H d := le_sup_left
    have hxH : x ∈ lemma106H d := hcl hxK
    simpa [Kset, H, hA.derived_eq_H] using hxH
  have hQCK : Q ≤ Subgroup.centralizer Kset := by
    have hQleCS : Q ≤ Subgroup.centralizer (S : Set X) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQS
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkH : k ∈ H := hKH hk
    have hkanti : t * k * t⁻¹ = k⁻¹ := by
      simpa [Kset, peterfalviKSet, rightConjugateElem,
        ht.inv_eq_self] using hk.2
    obtain ⟨a, haS, b, hbS2, hkab, _haanti, hbanti⟩ :=
      proposition102_inverted_mem_factor_of_internalDirectProduct
        hprodH htNormS htNormS2 hkH hkanti
    have haq : a * q = q * a :=
      Subgroup.mem_centralizer_iff.mp (hQleCS hq) a haS
    have hbH : b ∈ H := hprodH.right_le hbS2
    have hbK : b ∈ Kset := by
      refine ⟨hHleD hbH, ?_⟩
      simpa [Kset, peterfalviKSet, rightConjugateElem,
        ht.inv_eq_self] using hbanti
    have hbCR : b ∈ Subgroup.centralizer (R : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact hprodH.commute r (hRleS hr) b hbS2
    have hbCA1 : b ∈ Subgroup.centralizer (A1 : Set X) := by
      have hbPair : b ∈
          {x : X | x ∈ peterfalviKSet D t ∧
            x ∈ Subgroup.centralizer (R : Set X)} := by
        simpa [Kset] using And.intro hbK hbCR
      rw [hsetUniform] at hbPair
      exact hbPair.2
    have hqb : q * b = b * q :=
      Subgroup.mem_centralizer_iff.mp hbCA1 q (hQleA1 hq)
    rw [hkab]
    calc
      (a * b) * q = a * (b * q) := by group
      _ = a * (q * b) := by rw [hqb]
      _ = (a * q) * b := by group
      _ = (q * a) * b := by rw [haq]
      _ = q * (a * b) := by group
  apply le_antisymm
  · intro q hq
    have hqInf : q ∈ V ⊓ Subgroup.centralizer Kset :=
      ⟨hQleV hq, hQCK hq⟩
    have hqBot : q ∈ (⊥ : Subgroup X) := by
      rw [← hVC]
      simpa [V, Kset] using hqInf
    simpa using hqBot
  · exact bot_le

end CFSG.BenderSuzuki
