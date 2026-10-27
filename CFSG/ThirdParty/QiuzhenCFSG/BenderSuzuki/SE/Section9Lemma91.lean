module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Lemma 9.1

For a minimal normal supplement `W` of the two-point stabilizer `D`,
disjointness from `D` makes `W` a normal complement.  A nontrivial element of
the Peterfalvi anti-fixed set has exactly two fixed cosets, so its centralizer
in `W` is trivial.  Thompson's fixed-point-free theorem gives nilpotence, and
Theorem 4(a) turns the complement factorization into regularity on the
nonbase cosets.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

set_option maxHeartbeats 1000000

private theorem section9_zpowers_mem_K
    {X : Type u} [Group X]
    {D : Subgroup X} {t x : X}
    (hx : x ∈ peterfalviKSet D t) :
    ∀ y : X, y ∈ Subgroup.zpowers x →
      y ∈ peterfalviKSet D t := by
  intro y hy
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
  refine ⟨D.zpow_mem hx.1 n, ?_⟩
  change t⁻¹ * x ^ n * t = (x ^ n)⁻¹
  have hxanti : t⁻¹ * x * t = x⁻¹ := by
    simpa [rightConjugateElem] using hx.2
  calc
    t⁻¹ * x ^ n * t = (t⁻¹ * x * t) ^ n := by
      simpa using (conj_zpow (a := t⁻¹) (b := x) (i := n)).symm
    _ = (x⁻¹) ^ n := by rw [hxanti]
    _ = (x ^ n)⁻¹ := by simp

private theorem section9_regular_of_complement
    {X : Type u} [Group X]
    {M W : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (htM : t ∉ M)
    (hW : IsNormalComplementIn M (M ⊓ rightConjugate M t) W)
    (htrans : IsTransitiveOn M
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)}) :
    IsRegularOn W
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)} := by
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hbetaNeAlpha : beta ≠ alpha := by
    intro h
    apply htM
    simpa [alpha, beta] using QuotientGroup.eq.mp h
  let WM : Subgroup M := W.subgroupOf M
  let DM : Subgroup M := (M ⊓ rightConjugate M t).subgroupOf M
  haveI : WM.Normal := by
    simpa [WM] using hW.normal_in_M
  have hdisjointM : Disjoint WM DM := by
    rw [Subgroup.disjoint_def]
    intro x hxW hxD
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hW.disjoint_D hxW hxD
  have hsupM : WM ⊔ DM = ⊤ := by
    calc
      WM ⊔ DM =
          (W ⊔ (M ⊓ rightConjugate M t)).subgroupOf M := by
        simpa [WM, DM] using
          (Subgroup.subgroupOf_sup (A := W)
            (A' := M ⊓ rightConjugate M t) (B := M)
            hW.le_M inf_le_left).symm
      _ = M.subgroupOf M := by
        simpa using congrArg (Subgroup.subgroupOf · M) hW.sup_eq
      _ = ⊤ := Subgroup.subgroupOf_self M
  have hcomp : WM.IsComplement' DM :=
    isComplement'_of_disjoint_sup_eq_top_of_normal WM DM hdisjointM hsupM
  have hWmove : ∀ omega : conjugateCosetSpace M,
      omega ≠ alpha → ∃ w : W, (w : X) • beta = omega := by
    intro omega hne
    rcases htrans hbetaNeAlpha hne with ⟨m, hm⟩
    rcases hcomp.existsUnique m with ⟨⟨w, d⟩, hwd, _huniq⟩
    let wX : W := ⟨(w : X), w.property⟩
    have hdFix : (d : X) • beta = beta := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [show MulAction.stabilizer X beta = rightConjugate M t by
        simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
      exact d.property.2
    refine ⟨wX, ?_⟩
    change (w : X) • beta = omega
    calc
      (w : X) • beta = (w : X) • ((d : X) • beta) := by rw [hdFix]
      _ = (((w : M) * (d : M) : M) : X) • beta := by
        exact (mul_smul (w : X) (d : X) beta).symm
      _ = (m : X) • beta := by
        simpa using congrArg (fun q : M => (q : X) • beta) hwd
      _ = omega := hm
  intro a b ha hb
  obtain ⟨wa, hwa⟩ := hWmove a ha
  obtain ⟨wb, hwb⟩ := hWmove b hb
  let r : W := wb * wa⁻¹
  refine ⟨r, ?_, ?_⟩
  · change ((wb : X) * (wa : X)⁻¹) • a = b
    rw [mul_smul, ← hwa, inv_smul_smul, hwb]
  · intro s hs
    have hfix : ((wb⁻¹ * s * wa : W) : X) • beta = beta := by
      change ((wb : X)⁻¹ * (s : X) * (wa : X)) • beta = beta
      rw [mul_smul, mul_smul, hwa, hs, ← hwb, inv_smul_smul]
    have hfix' : (wb⁻¹ * s * wa : W) = 1 := by
      have hmem : ((wb⁻¹ * s * wa : W) : X) ∈
          rightConjugate M t := by
        rw [← show MulAction.stabilizer X beta = rightConjugate M t by
          simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
        exact MulAction.mem_stabilizer_iff.mpr hfix
      have hmemD : ((wb⁻¹ * s * wa : W) : X) ∈
          M ⊓ rightConjugate M t :=
        ⟨hW.le_M ((wb⁻¹ * s * wa : W).property), hmem⟩
      have hmemW : ((wb⁻¹ * s * wa : W) : X) ∈ W :=
        (wb⁻¹ * s * wa : W).property
      have hbot := Subgroup.disjoint_def.mp hW.disjoint_D hmemW hmemD
      exact Subtype.ext (by simpa using hbot)
    apply Subtype.ext
    have h := congrArg (fun z : W => wb * z * wa⁻¹) hfix'
    simpa [mul_assoc] using h

/-- Lemma 9.1: a disjoint minimal normal supplement is a nilpotent normal
complement acting regularly on the nonbase conjugate cosets. -/
public theorem lemma_9_1
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hdisjoint : Disjoint W (M ⊓ rightConjugate M t))
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (htrans : IsTransitiveOn M
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)}) :
    IsNormalComplementIn M (M ⊓ rightConjugate M t) W ∧
      Group.IsNilpotent W ∧
      IsRegularOn W
        {omega : conjugateCosetSpace M |
          omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)} := by
  let D : Subgroup X := M ⊓ rightConjugate M t
  have hNC : IsNormalComplementIn M D W :=
    hW.isNormalComplementIn_of_disjoint (by simpa [D] using hdisjoint)
  obtain ⟨x, hxI, hxne⟩ := hIne
  let K : Subgroup X := Subgroup.zpowers x
  have hKleD : K ≤ D := by
    intro y hy
    exact (section9_zpowers_mem_K hxI y hy).1
  have hMnormW : M ≤ Subgroup.normalizer (W : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNC.le_M).mp
      hNC.normal_in_M
  have hKnormW : K ≤ Subgroup.normalizer (W : Set X) :=
    hKleD.trans (by simpa [D] using inf_le_left) |>.trans hMnormW
  have hKnontriv : ∃ y : X, y ∈ K ∧ y ≠ 1 :=
    ⟨x, Subgroup.mem_zpowers x, hxne⟩
  have hfixed : ∀ y : X, y ∈ K → y ≠ 1 →
      Subgroup.centralizer ({y} : Set X) ⊓ W = ⊥ := by
    intro y hyK hyne
    have hyI : y ∈ peterfalviKSet D t := by
      simpa [D] using section9_zpowers_mem_K hxI y hyK
    have hcard : Nat.card (theorem4bFixedPoints M (Subgroup.zpowers y)) = 2 :=
      d83.fixedPoints_card_eq_two hyI hyne
    let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
    let beta : conjugateCosetSpace M := QuotientGroup.mk t
    have halpha : alpha ∈ fixedPointsOfSubgroup X
        (conjugateCosetSpace M) (Subgroup.zpowers y) := by
      intro k hk
      apply MulAction.mem_stabilizer_iff.mp
      rw [baseCoset_stabilizer M]
      exact Subgroup.zpowers_le.mpr hyI.1.1 hk
    have hbeta : beta ∈ fixedPointsOfSubgroup X
        (conjugateCosetSpace M) (Subgroup.zpowers y) := by
      intro k hk
      apply MulAction.mem_stabilizer_iff.mp
      rw [conjugateCoset_stabilizer M t, ht.inv_eq_self]
      exact Subgroup.zpowers_le.mpr hyI.1.2 hk
    have hbetaNeAlpha : beta ≠ alpha := by
      intro h
      apply htM
      simpa [alpha, beta] using QuotientGroup.eq.mp h
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have hwW : w ∈ W := hw.2
    have hwcomm : w * y = y * w :=
      Subgroup.mem_centralizer_singleton_iff.mp hw.1
    have hwyFixed : (w : X) • beta ∈ fixedPointsOfSubgroup X
        (conjugateCosetSpace M) (Subgroup.zpowers y) := by
      intro k hk
      rcases Subgroup.mem_zpowers_iff.mp hk with ⟨n, rfl⟩
      have hcomm : Commute y w := by
        exact hwcomm.symm
      have hcommPow : y ^ n * w = w * y ^ n :=
        (hcomm.zpow_left n).eq
      have hyfix : y ^ n • beta = beta :=
        hbeta (y ^ n)
          ((Subgroup.zpowers y).zpow_mem (Subgroup.mem_zpowers y) n)
      calc
        y ^ n • (w • beta) = (y ^ n * w) • beta := by rw [mul_smul]
        _ = (w * y ^ n) • beta := by rw [hcommPow]
        _ = w • (y ^ n • beta) := by rw [mul_smul]
        _ = w • beta := by rw [hyfix]
    let base : theorem4bFixedPoints M (Subgroup.zpowers y) := ⟨alpha, halpha⟩
    let betap : theorem4bFixedPoints M (Subgroup.zpowers y) := ⟨beta, hbeta⟩
    let wb : theorem4bFixedPoints M (Subgroup.zpowers y) := ⟨w • beta, hwyFixed⟩
    have hwbNeBase : wb ≠ base := by
      intro h
      have hwM : w ∈ M := hNC.le_M hwW
      have hwbase : (w : X) • alpha = alpha := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [baseCoset_stabilizer M]
        exact hwM
      apply hbetaNeAlpha
      have hwbval : (w : X) • beta = alpha := by
        simpa [wb, base] using congrArg Subtype.val h
      have hwbval' := congrArg
        (fun q : conjugateCosetSpace M => (w : X)⁻¹ • q) hwbval
      have hwinvbase : (w : X)⁻¹ • alpha = alpha := by
        apply MulAction.mem_stabilizer_iff.mp
        rw [baseCoset_stabilizer M]
        exact M.inv_mem hwM
      have hwbval'' : beta = (w : X)⁻¹ • alpha := by
        simpa using hwbval'
      exact hwbval''.trans hwinvbase
    obtain ⟨gamma, hgamma, huniq⟩ :=
      (Nat.card_eq_two_iff' (⟨alpha, halpha⟩ :
        theorem4bFixedPoints M (Subgroup.zpowers y))).mp hcard
    have hwbBeta : wb = betap := by
      exact (huniq wb hwbNeBase).trans (huniq betap (by
        intro h
        exact hbetaNeAlpha (congrArg Subtype.val h))).symm
    have hwfix : (w : X) • beta = beta := congrArg Subtype.val hwbBeta
    have hwD : w ∈ D := by
      refine ⟨hNC.le_M hwW, ?_⟩
      rw [← show MulAction.stabilizer X beta = rightConjugate M t by
        simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
      exact MulAction.mem_stabilizer_iff.mpr hwfix
    have hbot := Subgroup.disjoint_def.mp hNC.disjoint_D hwW hwD
    simpa using hbot
  have hnil : Group.IsNilpotent W :=
    External.huppert_V_8_14_thompson_fixedPointFree_conjugation_nilpotent_subgroup
      W K hKnormW hKnontriv hfixed
  have hreg : IsRegularOn W
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)} :=
    section9_regular_of_complement ht htM hNC htrans
  exact ⟨hNC, hnil, hreg⟩

end CFSG.BenderSuzuki
