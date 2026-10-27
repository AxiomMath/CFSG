module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Action
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Coprime
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow

namespace CFSG
end CFSG
open CFSG

/-!
# Proposition 8.4: the proper-predecessor step

This file proves the checked induction step at source lines 2484--2505.  The
predecessor conclusion supplies its normal Sylow `2`-subgroup; regularity is
restricted to the `Y`-fixed points, and the odd-order coprime-action theorem
refines the resulting `N_D(Y)` factor to `N_V(Y)`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The Sylow, normality, and regularity fields inherited from the induction
conclusion at `Y₀`. -/
public theorem proposition84Proper_sylow_regular_fields
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) {t u0 : X} {Y₀ Y : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({u0} : Set X))
    (hY₀Y : Y₀ ≤ Y)
    (hY₀normal : (Y₀.subgroupOf Y).Normal)
    (h₀ : Proposition84Conclusion M t u0 Y₀) :
    ∃ S : Subgroup X,
      S ≤ normalizerIn M Y ∧
      (S.subgroupOf (normalizerIn M Y)).Normal ∧
      (∃ P : Sylow 2 ↥(centralizerTwoPrimeResidual Y ⊓ M),
        S = (P : Subgroup ↥(centralizerTwoPrimeResidual Y ⊓ M)).map
          (centralizerTwoPrimeResidual Y ⊓ M).subtype) ∧
      IsRegularOn S
        {omega : conjugateCosetSpace M |
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y ∧
            omega ≠ QuotientGroup.mk 1} := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  let F₀ : Subgroup X := centralizerTwoPrimeResidual Y₀
  let F : Subgroup X := centralizerTwoPrimeResidual Y
  have hAB₀ : Proposition84ABConclusion M t u0 Y₀ := h₀.1
  change
    IsTwoTransitiveOn F₀
        (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y₀) ∧
      ((Subgroup.normalizer (Y₀ : Set X) : Subgroup X) : Set X) =
        (F₀ : Set X) * (normalizerIn
          (D ⊓ Subgroup.centralizer ({u0} : Set X)) Y₀ : Set X) ∧
      ∃ S₀ : Subgroup X,
        S₀ ≤ normalizerIn M Y₀ ∧
        (S₀.subgroupOf (normalizerIn M Y₀)).Normal ∧
        (∃ P₀ : Sylow 2 ↥(F₀ ⊓ M),
          S₀ = (P₀ : Subgroup ↥(F₀ ⊓ M)).map
            (F₀ ⊓ M).subtype) ∧
        IsRegularOn S₀
          {omega : conjugateCosetSpace M |
            omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y₀ ∧
              omega ≠ QuotientGroup.mk 1} ∧
        (normalizerIn M Y₀ : Set X) =
          (S₀ : Set X) * (normalizerIn D Y₀ : Set X) at hAB₀
  rcases hAB₀.2.2 with
    ⟨S₀, hS₀leNMY₀, hS₀normalNMY₀, ⟨P₀, hS₀eq⟩,
      hS₀reg, _hfactor₀⟩
  have hYM : Y ≤ M := by
    intro y hy
    exact (hYV hy).1.1
  letI : (Y₀.subgroupOf Y).Normal := hY₀normal
  have hYleNormY₀ : Y ≤ Subgroup.normalizer (Y₀ : Set X) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hY₀Y
  have hYleNMY₀ : Y ≤ normalizerIn M Y₀ := by
    intro y hy
    exact ⟨hYM hy, hYleNormY₀ hy⟩
  letI : (S₀.subgroupOf (normalizerIn M Y₀)).Normal :=
    hS₀normalNMY₀
  have hYnormS₀ : Y ≤ Subgroup.normalizer (S₀ : Set X) :=
    hYleNMY₀.trans
      (Subgroup.le_normalizer_of_normal_subgroupOf hS₀leNMY₀)
  have hS₀p : IsPGroup 2 S₀ := by
    rw [hS₀eq]
    exact P₀.isPGroup'.map (F₀ ⊓ M).subtype
  have hS₀leF₀M : S₀ ≤ F₀ ⊓ M := by
    rw [hS₀eq]
    exact Subgroup.map_subtype_le (P₀ : Subgroup ↥(F₀ ⊓ M))
  have hF₀MleNMY₀ : F₀ ⊓ M ≤ normalizerIn M Y₀ := by
    intro x hx
    exact ⟨hx.2, centralizer_le_normalizer Y₀
      (centralizerTwoPrimeResidual_le_ambientCentralizer Y₀ hx.1)⟩
  have hS₀normalF₀M : (S₀.subgroupOf (F₀ ⊓ M)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hS₀leF₀M]
    exact hF₀MleNMY₀.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hS₀leNMY₀).mp
        hS₀normalNMY₀)
  have hP₀eq : (P₀ : Subgroup ↥(F₀ ⊓ M)) =
      S₀.subgroupOf (F₀ ⊓ M) := by
    ext x
    change x ∈ P₀ ↔ (x : X) ∈ S₀
    rw [hS₀eq]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := by
        apply Subtype.ext
        exact hyx
      simpa [hyx'] using hy
  have hP₀normal : (P₀ : Subgroup ↥(F₀ ⊓ M)).Normal := by
    rw [hP₀eq]
    exact hS₀normalF₀M
  have hFF₀ : F ≤ F₀ :=
    centralizerTwoPrimeResidual_mono hY₀Y
  have hFMF₀M : F ⊓ M ≤ F₀ ⊓ M :=
    inf_le_inf hFF₀ le_rfl
  obtain ⟨P, hPmap, hPnormal⟩ :=
    exists_sylow_map_eq_inf_of_normal_sylow_map
      (F₀ ⊓ M) (F ⊓ M) hFMF₀M P₀ hP₀normal
  let S : Subgroup X := S₀ ⊓ F
  have hS₀M : S₀ ≤ M :=
    hS₀leNMY₀.trans inf_le_left
  have hPmapS :
      (P : Subgroup ↥(F ⊓ M)).map (F ⊓ M).subtype = S := by
    rw [hPmap, ← hS₀eq]
    ext x
    change (x ∈ S₀ ∧ (x ∈ F ∧ x ∈ M)) ↔
      (x ∈ S₀ ∧ x ∈ F)
    constructor
    · rintro ⟨hxS₀, hxF, _hxM⟩
      exact ⟨hxS₀, hxF⟩
    · rintro ⟨hxS₀, hxF⟩
      exact ⟨hxS₀, hxF, hS₀M hxS₀⟩
  have hSleNMY : S ≤ normalizerIn M Y := by
    intro s hs
    exact ⟨hS₀M hs.1, centralizer_le_normalizer Y
      (centralizerTwoPrimeResidual_le_ambientCentralizer Y hs.2)⟩
  have hFMleNMY : F ⊓ M ≤ normalizerIn M Y := by
    intro x hx
    exact ⟨hx.2, centralizer_le_normalizer Y
      (centralizerTwoPrimeResidual_le_ambientCentralizer Y hx.1)⟩
  have hFMnormalNMY :
      ((F ⊓ M).subgroupOf (normalizerIn M Y)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hFMleNMY]
    intro f n hf hn
    refine ⟨?_, M.mul_mem (M.mul_mem hn.1 hf.2) (M.inv_mem hn.1)⟩
    have hFleNY : F ≤ Subgroup.normalizer (Y : Set X) :=
      (centralizerTwoPrimeResidual_le_ambientCentralizer Y).trans
        (centralizer_le_normalizer Y)
    have hFnormalNY : (F.subgroupOf
        (Subgroup.normalizer (Y : Set X))).Normal :=
      centralizerTwoPrimeResidual_normal_in_normalizer Y
    exact (Subgroup.normal_subgroupOf_iff hFleNY).mp hFnormalNY
      f n hf.1 hn.2
  have hPchar : (P : Subgroup ↥(F ⊓ M)).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  have hSnormalNMY : (S.subgroupOf (normalizerIn M Y)).Normal :=
    normal_subgroupOf_map_of_characteristic_of_normal
      (F ⊓ M) S (normalizerIn M Y) hFMleNMY hFMnormalNMY
      (P : Subgroup ↥(F ⊓ M)) hPchar hPmapS.symm hSleNMY
  have hSreg : IsRegularOn S
      {omega : conjugateCosetSpace M |
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y ∧
          omega ≠ QuotientGroup.mk 1} := by
    have hregC := isRegularOn_inf_centralizer_fixedPoints_of_le
      S₀ Y₀ Y (QuotientGroup.mk 1 : conjugateCosetSpace M)
      hY₀Y hS₀reg hYnormS₀
    rw [inf_centralizer_eq_inf_centralizerTwoPrimeResidual hS₀p] at hregC
    exact hregC
  exact ⟨S, hSleNMY, hSnormalNMY, ⟨P, hPmapS.symm⟩, hSreg⟩

/-- Source-faithful proper-predecessor step of Proposition 8.4. -/
public theorem IsStronglyEmbedded.proposition84ProperStep_of_source
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t) :
    Proposition84ProperStep M t d83.u := by
  dsimp [Proposition84ProperStep]
  intro Y₀ Y hYV _hY₀ne hY₀lt hY₀normal h₀ _hIY
  let D : Subgroup X := M ⊓ rightConjugate M t
  let V : Subgroup X := D ⊓ Subgroup.centralizer ({d83.u} : Set X)
  let F : Subgroup X := centralizerTwoPrimeResidual Y
  obtain ⟨S, hSle, hSnormal, ⟨P, hSmap⟩, hSreg⟩ :=
    proposition84Proper_sylow_regular_fields M hYV hY₀lt.le
      hY₀normal h₀
  have hYVt : Y ≤ D ⊓ Subgroup.centralizer ({t} : Set X) := by
    dsimp [D]
    rw [d83.centralizer_eq]
    exact hYV
  have hYD : Y ≤ D := hYVt.trans inf_le_left
  have hYM : Y ≤ M := hYD.trans inf_le_left
  have hFC : F ≤ Subgroup.centralizer (Y : Set X) := by
    dsimp [F]
    exact centralizerTwoPrimeResidual_le_ambientCentralizer Y
  have hSF : S ≤ F := by
    rw [hSmap]
    exact (Subgroup.map_subtype_le
      (P : Subgroup ↥(centralizerTwoPrimeResidual Y ⊓ M))).trans
        inf_le_left
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hSfix : S ≤ MulAction.stabilizer X alpha := by
    intro s hs
    rw [show MulAction.stabilizer X alpha = M by
      simpa [alpha] using baseCoset_stabilizer M]
    exact (hSle hs).1
  have hstable : ∀ (f : F) ⦃omega : conjugateCosetSpace M⦄,
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y →
        (f : X) • omega ∈
          fixedPointsOfSubgroup X (conjugateCosetSpace M) Y := by
    intro f omega homega
    exact smul_mem_fixedPointsOfSubgroup_of_mem_centralizer
      (hFC f.property) homega
  have halpha : alpha ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y :=
    theorem4b_baseCoset_mem_fixedPoints hYM
  have hbeta : beta ∈
      fixedPointsOfSubgroup X (conjugateCosetSpace M) Y := by
    intro y hyY
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
    exact (hYD hyY).2
  have hbetaNe : beta ≠ alpha := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h.symm
  have htC : t ∈ Subgroup.centralizer (Y : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hyY
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYVt hyY).2
  have htF : t ∈ F := by
    dsimp [F]
    exact zpowers_le_centralizerTwoPrimeResidual_of_isInvolution Y ht htC
      (Subgroup.mem_zpowers t)
  have htalpha : t • alpha = beta := by
    simp [alpha, beta, MulAction.Quotient.smul_mk]
  have htwo : IsTwoTransitiveOn F
      (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y) :=
    isTwoTransitiveOn_of_regularOn_compl_singleton
      F S (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y)
      alpha beta t hSF hSfix hstable halpha hbeta hbetaNe hSreg htF htalpha
  have hNfactorD :
      ((Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) =
        (F : Set X) * (normalizerIn D Y : Set X) := by
    exact normalizer_eq_mul_normalizerIn_of_twoTransitiveOn
      M Y F ht htM hYD hFC htwo
  have hDdecomp :
      ((normalizerIn D Y : Subgroup X) : Set X) ⊆
        (F : Set X) * (normalizerIn V Y : Set X) := by
    exact normalizerIn_le_centralizerResidual_mul_normalizerIn
      hM ht htM d83 hYV
  have hNfactorV :
      ((Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) =
        (F : Set X) * (normalizerIn V Y : Set X) := by
    apply Set.Subset.antisymm
    · intro x hxN
      have hxFactor : x ∈
          (F : Set X) * (normalizerIn D Y : Set X) := by
        rw [← hNfactorD]
        exact hxN
      rw [Set.mem_mul] at hxFactor
      rcases hxFactor with ⟨a, haF, d, hdD, had⟩
      have hdFactor := hDdecomp hdD
      rw [Set.mem_mul] at hdFactor
      rcases hdFactor with ⟨b, hbF, v, hvV, hbv⟩
      rw [Set.mem_mul]
      refine ⟨a * b, F.mul_mem haF hbF, v, hvV, ?_⟩
      rw [mul_assoc, hbv, had]
    · intro x hx
      rw [Set.mem_mul] at hx
      rcases hx with ⟨a, haF, v, hvV, hav⟩
      have hFleN : F ≤ Subgroup.normalizer (Y : Set X) :=
        hFC.trans (centralizer_le_normalizer Y)
      rw [← hav]
      exact (Subgroup.normalizer (Y : Set X)).mul_mem
        (hFleN haF) hvV.2
  have hMfactor :
      (normalizerIn M Y : Set X) =
        (S : Set X) * (normalizerIn D Y : Set X) := by
    exact normalizerIn_eq_mul_normalizerIn_of_regularOn
      M Y S ht htM hYD hSle hSreg
  dsimp [Proposition84ABConclusion]
  exact ⟨htwo, hNfactorV, S, hSle, hSnormal,
    ⟨P, hSmap⟩, hSreg, hMfactor⟩

end CFSG.BenderSuzuki
