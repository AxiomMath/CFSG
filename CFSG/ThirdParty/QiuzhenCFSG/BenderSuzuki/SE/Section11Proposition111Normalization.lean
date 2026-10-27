module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Proposition111Transport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Final
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Lemma101

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Proposition 11.1: Fitting-subgroup normalization

This module proves the final source-independent normalization step.  A
subgroup with at least three fixed cosets is moved into a conjugate of `V`;
the Fitting subgroup `F(V)`, already known to be a Sylow subgroup, is then the
normal Sylow subgroup of the intervening centralizer and hence is normalized
by its normalizer.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- The Fitting subgroup is functorial under a group equivalence. -/
public theorem proposition111_fittingSubgroup_map_mulEquiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm
  · refine le_sSup ⟨?_, ?_⟩
    · exact (show (fittingSubgroup A).Normal from inferInstance).map
        e.toMonoidHom e.surjective
    · haveI : Group.IsNilpotent (fittingSubgroup A) := inferInstance
      exact nilpotent_of_mulEquiv (e.subgroupMap (fittingSubgroup A))
  · have hpre :
        (fittingSubgroup B).map e.symm.toMonoidHom ≤ fittingSubgroup A := by
      refine le_sSup ⟨?_, ?_⟩
      · exact (show (fittingSubgroup B).Normal from inferInstance).map
          e.symm.toMonoidHom e.symm.surjective
      · haveI : Group.IsNilpotent (fittingSubgroup B) := inferInstance
        exact nilpotent_of_mulEquiv
          (e.symm.subgroupMap (fittingSubgroup B))
    intro b hb
    refine Subgroup.mem_map.mpr ⟨e.symm b, hpre ?_, by simp⟩
    exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩

/-- Ambient Fitting subgroups commute with right conjugation. -/
public theorem proposition111_fittingSubgroupOf_rightConjugate
    {X : Type u} [Group X] [Finite X]
    (H : Subgroup X) (g : X) :
    fittingSubgroupOf (rightConjugate H g) =
      rightConjugate (fittingSubgroupOf H) g := by
  let eH : H ≃* rightConjugate H g :=
    (MulAut.conj g⁻¹).subgroupMap H
  have hmap :
      (fittingSubgroup H).map eH.toMonoidHom =
        fittingSubgroup (rightConjugate H g) :=
    proposition111_fittingSubgroup_map_mulEquiv eH
  have hmapX := congrArg
    (fun K : Subgroup (rightConjugate H g) =>
      K.map (rightConjugate H g).subtype) hmap.symm
  have hcomp :
      (rightConjugate H g).subtype.comp eH.toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  simp only [Subgroup.map_map] at hmapX
  rw [hcomp] at hmapX
  simpa [fittingSubgroupOf, rightConjugate, Subgroup.conjBy, eH,
    Subgroup.map_map] using hmapX

/-- Equal-cardinality ambient subgroups have the same Sylow size. -/
public theorem proposition111_sylow_of_card_eq
    {X : Type u} [Group X] [Finite X] {r : ℕ}
    {P D F : Subgroup X}
    (hr : r.Prime)
    (hPsyl : theorem4bIsSylowSubgroupOf r P F)
    (hPD : P ≤ D) (hcard : Nat.card D = Nat.card F) :
    theorem4bIsSylowSubgroupOf r P D := by
  letI : Fact r.Prime := ⟨hr⟩
  rcases hPsyl with ⟨PF, hP⟩
  have hPcard : Nat.card P = r ^ (Nat.card F).factorization r := by
    rw [hP, Subgroup.card_map_of_injective F.subtype_injective]
    exact Sylow.card_eq_multiplicity PF
  have hPDcard : Nat.card (P.subgroupOf D) =
      r ^ (Nat.card D).factorization r := by
    rw [natCard_subgroupOf_eq P D hPD, hPcard, hcard]
  let PD : Sylow r D := Sylow.ofCard (P.subgroupOf D) hPDcard
  refine ⟨PD, ?_⟩
  have hmap : (P.subgroupOf D).map D.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD]
  simpa [PD] using hmap.symm

/-- Inside a fixed ambient subgroup, Sylow status depends only on subgroup
cardinality. -/
public theorem proposition111_sylow_of_subgroup_card_eq
    {X : Type u} [Group X] [Finite X] {r : ℕ}
    {P Q E : Subgroup X}
    (hr : r.Prime)
    (hPsyl : theorem4bIsSylowSubgroupOf r P E)
    (hQE : Q ≤ E) (hcard : Nat.card Q = Nat.card P) :
    theorem4bIsSylowSubgroupOf r Q E := by
  letI : Fact r.Prime := ⟨hr⟩
  rcases hPsyl with ⟨PE, hP⟩
  have hPcard : Nat.card P = r ^ (Nat.card E).factorization r := by
    rw [hP, Subgroup.card_map_of_injective E.subtype_injective]
    exact Sylow.card_eq_multiplicity PE
  have hQEcard : Nat.card (Q.subgroupOf E) =
      r ^ (Nat.card E).factorization r := by
    rw [natCard_subgroupOf_eq Q E hQE, hcard, hPcard]
  let QE : Sylow r E := Sylow.ofCard (Q.subgroupOf E) hQEcard
  refine ⟨QE, ?_⟩
  change Q = (Q.subgroupOf E).map E.subtype
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQE]

/-- A normal Sylow subgroup is the unique ambiently encoded Sylow subgroup. -/
public theorem proposition111_sylow_eq_of_right_normal
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} {P Q H : Subgroup X}
    (hr : r.Prime)
    (hPsyl : theorem4bIsSylowSubgroupOf r P H)
    (hQsyl : theorem4bIsSylowSubgroupOf r Q H)
    (hQnormal : (Q.subgroupOf H).Normal) :
    P = Q := by
  letI : Fact r.Prime := ⟨hr⟩
  rcases hPsyl with ⟨PS, hP⟩
  rcases hQsyl with ⟨QS, hQ⟩
  have hQleH : Q ≤ H := by
    rw [hQ]
    exact Subgroup.map_subtype_le _
  have hQsubeq : Q.subgroupOf H = (QS : Subgroup H) := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQleH]
    exact hQ
  have hQSnormal : (QS : Subgroup H).Normal := by
    simpa [hQsubeq] using hQnormal
  letI : Unique (Sylow r H) := Sylow.unique_of_normal QS hQSnormal
  calc
    P = (PS : Subgroup H).map H.subtype := hP
    _ = (QS : Subgroup H).map H.subtype := by
      rw [Subsingleton.elim PS QS]
    _ = Q := hQ.symm

/-- If `F=F(V)` lies in a right conjugate of `V`, then it is the normal Sylow
`r`-subgroup of that conjugate as well. -/
public theorem proposition111_fitting_normal_sylow_rightConjugate
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} {F V : Subgroup X} {g : X}
    (hr : r.Prime)
    (hFeq : F = fittingSubgroupOf V)
    (hFsylV : theorem4bIsSylowSubgroupOf r F V)
    (hFleVg : F ≤ rightConjugate V g) :
    theorem4bIsSylowSubgroupOf r F (rightConjugate V g) ∧
      (F.subgroupOf (rightConjugate V g)).Normal := by
  let Vg : Subgroup X := rightConjugate V g
  let Fg : Subgroup X := rightConjugate F g
  have hcardVg : Nat.card Vg = Nat.card V := by
    simpa [Vg] using proposition102_natCard_rightConjugate V g
  have hFsylVg : theorem4bIsSylowSubgroupOf r F Vg :=
    proposition111_sylow_of_card_eq hr hFsylV hFleVg hcardVg
  have hFgLeVg : Fg ≤ Vg := by
    dsimp [Fg, Vg]
    rw [hFeq]
    exact Subgroup.map_mono (fittingSubgroupOf_le V)
  have hcardFg : Nat.card Fg = Nat.card F := by
    simpa [Fg] using proposition102_natCard_rightConjugate F g
  have hFgsylVg : theorem4bIsSylowSubgroupOf r Fg Vg :=
    proposition111_sylow_of_subgroup_card_eq
      hr hFsylVg hFgLeVg hcardFg
  have hFitVg : fittingSubgroupOf Vg = Fg := by
    calc
      fittingSubgroupOf Vg =
          rightConjugate (fittingSubgroupOf V) g := by
            simpa [Vg] using
              proposition111_fittingSubgroupOf_rightConjugate V g
      _ = Fg := by rw [← hFeq]
  have hVgNormFg : Vg ≤ Subgroup.normalizer (Fg : Set X) := by
    letI : (fittingSubgroup Vg).Characteristic :=
      fittingSubgroup_characteristic
    have hVgNormVg : Vg ≤ Subgroup.normalizer (Vg : Set X) :=
      Vg.le_normalizer
    have hNormFit : Subgroup.normalizer (Vg : Set X) ≤
        Subgroup.normalizer (fittingSubgroupOf Vg : Set X) := by
      simpa [fittingSubgroupOf] using
        (proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
          Vg (fittingSubgroup Vg))
    rw [hFitVg] at hNormFit
    exact hVgNormVg.trans hNormFit
  have hFgnormalVg : (Fg.subgroupOf Vg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFgLeVg).2 hVgNormFg
  have hFFg : F = Fg :=
    proposition111_sylow_eq_of_right_normal
      hr hFsylVg hFgsylVg hFgnormalVg
  have hFnormalVg : (F.subgroupOf Vg).Normal := by
    simpa [hFFg] using hFgnormalVg
  exact ⟨hFsylVg, hFnormalVg⟩

/-- A normal Sylow subgroup of an overgroup containing `Y` is the ambient
image of `O_r(Y)`.  Consequently every normalizer of `Y` normalizes it. -/
public theorem proposition111_normalizes_of_normal_sylow_overgroup
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} {F Y Vg N : Subgroup X}
    (hr : r.Prime)
    (hFleY : F ≤ Y) (hYleVg : Y ≤ Vg)
    (hFsylVg : theorem4bIsSylowSubgroupOf r F Vg)
    (hFnormalVg : (F.subgroupOf Vg).Normal)
    (hNnormY : N ≤ Subgroup.normalizer (Y : Set X)) :
    N ≤ Subgroup.normalizer (F : Set X) := by
  letI : Fact r.Prime := ⟨hr⟩
  have hFleVg : F ≤ Vg := hFleY.trans hYleVg
  have hVgnormF : Vg ≤ Subgroup.normalizer (F : Set X) := by
    letI : (F.subgroupOf Vg).Normal := hFnormalVg
    exact Subgroup.le_normalizer_of_normal_subgroupOf hFleVg
  have hYnormF : Y ≤ Subgroup.normalizer (F : Set X) :=
    hYleVg.trans hVgnormF
  have hFnormalY : (F.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFleY).2 hYnormF
  have hFsylY : theorem4bIsSylowSubgroupOf r F Y :=
    theorem4bIsSylowSubgroupOf_of_between hr hFsylVg hFleY hYleVg
  rcases hFsylY with ⟨S, hFS⟩
  have hFsubeq : F.subgroupOf Y = (S : Subgroup Y) := by
    apply Subgroup.map_injective Y.subtype_injective
    simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hFleY] using hFS
  have hSnormal : (S : Subgroup Y).Normal := by
    simpa [hFsubeq] using hFnormalY
  have hCore : pCore r Y = (S : Subgroup Y) :=
    proposition102_normal_sylow_eq_pCore hr S hSnormal
  have hCoreMap : (pCore r Y).map Y.subtype = F := by
    rw [hCore]
    exact hFS.symm
  letI : (pCore r Y).Characteristic := pCore_characteristic
  have hNormCore : Subgroup.normalizer (Y : Set X) ≤
      Subgroup.normalizer ((pCore r Y).map Y.subtype : Set X) :=
    proposition102_normalizer_le_normalizer_map_subtype_of_characteristic
      Y (pCore r Y)
  rw [hCoreMap] at hNormCore
  exact hNnormY.trans hNormCore

/-- Right conjugation follows the exponent convention `(H^a)^b=H^(ab)`. -/
public theorem proposition111_rightConjugate_rightConjugate
    {X : Type u} [Group X] (H : Subgroup X) (a b : X) :
    rightConjugate (rightConjugate H a) b =
      rightConjugate H (a * b) := by
  simp [rightConjugate, Subgroup.conjBy_conjBy, mul_inv_rev]

/-- Reverse a right-conjugate containment. -/
public theorem proposition111_le_rightConjugate_inv_of_rightConjugate_le
    {X : Type u} [Group X] {H K : Subgroup X} {g : X}
    (h : rightConjugate H g ≤ K) :
    H ≤ rightConjugate K g⁻¹ := by
  intro x hxH
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨rightConjugateElem x g,
    h (rightConjugateElem_mem_rightConjugate hxH), ?_⟩
  simp [rightConjugateElem, MulAut.conj_apply, mul_assoc]

/-- The final normalization step of Proposition 11.1.  If `Y ≤ M` contains
`F(V)`, has at least three fixed cosets, and is normalized by `N`, then `N`
normalizes `F(V)`. -/
public theorem proposition111_normalizes_fitting_of_fixedPoints
    {X : Type u} [Group X] [Finite X]
    {M W Y N : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (d83 : Lemma83Data M t)
    (d : Lemma101Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t))
      (peterfalviV (M ⊓ rightConjugate M t) t) t)
    (h102 : Proposition102Conclusion M W
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t d)
    (hYM : Y ≤ M)
    (hFleY : fittingSubgroupOf
      (peterfalviV (M ⊓ rightConjugate M t) t) ≤ Y)
    (hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Y))
    (hNnormY : N ≤ Subgroup.normalizer (Y : Set X)) :
    N ≤ Subgroup.normalizer
      (fittingSubgroupOf
        (peterfalviV (M ⊓ rightConjugate M t) t) : Set X) := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  let V : Subgroup X := peterfalviV D t
  let F : Subgroup X := fittingSubgroupOf V
  have hFleY' : F ≤ Y := by
    simpa [F, V, D] using hFleY
  obtain ⟨g, hYgV⟩ :=
    proposition111_exists_rightConjugate_le_lemma83V
      d83 ht htM htwo hYM hthree
  have hYleVg : Y ≤ rightConjugate V g⁻¹ :=
    proposition111_le_rightConjugate_inv_of_rightConjugate_le hYgV
  have hFleVg : F ≤ rightConjugate V g⁻¹ :=
    hFleY'.trans hYleVg
  have hFeqR : F = h102.exponent.R := by
    calc
      F = (derivedSubgroup E).map E.subtype ⊓ V := by
        simpa [F, V, E, D] using h102.fitting_eq_derived_inf
      _ = h102.exponent.R := by
        simpa [V, E, D] using h102.derived_inf_eq_exponent_R.symm
  have hFsylV : theorem4bIsSylowSubgroupOf h102.exponent.r F V := by
    rw [hFeqR]
    simpa [V, E, D] using h102.derived_inf_isSylow_V
  obtain ⟨hFsylVg, hFnormalVg⟩ :=
    proposition111_fitting_normal_sylow_rightConjugate
      h102.exponent.r_prime (by rfl) hFsylV hFleVg
  have hresult : N ≤ Subgroup.normalizer (F : Set X) :=
    proposition111_normalizes_of_normal_sylow_overgroup
      h102.exponent.r_prime hFleY' hYleVg hFsylVg hFnormalVg hNnormY
  simpa [F, V, D] using hresult

end CFSG.BenderSuzuki
