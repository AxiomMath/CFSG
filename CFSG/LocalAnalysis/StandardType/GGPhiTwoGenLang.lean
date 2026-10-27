module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenDefs
public import CFSG.LieType.AlgebraicGroups.KernelRootGroup
public import CFSG.LieType.AlgebraicGroups.KernelRootDescent
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

@[expose] noncomputable def kernelGroup
    {τ : Tag} {M : Type} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    (L : Type) [Field L] : Subgroup (ModGL τ L) :=
  torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ)

theorem exists_mul_eq_kernelGroup
    {τ : Tag} {M : Type} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    {K : Type} [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hrat : ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))))
    {w : WeylGroup τ} {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hnw : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∈
      kernelGroup χ (AlgebraicClosure K)) :
    ∃ h : adjointGroup τ K, ∃ d ∈ kernelGroup χ (AlgebraicClosure K),
      g0 = baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K) * d := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  rw [hfr] at hg0
  obtain ⟨z, hz, hzLang⟩ :=
    CFSG.LieType.AlgebraicGroups.lang_torus_sup_rootSpan (L := AlgebraicClosure K)
      (χ := χ) (ringChar K) (f : ℕ) f.pos
      (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) hnw
  have hz_adj : z ∈ adjointGroup τ (AlgebraicClosure K) :=
    CFSG.LieType.AlgebraicGroups.torus_sup_rootSpan_le_adjointGroup
      (S := kernelRoots χ) hz
  have h0_adj : g0 * z⁻¹ ∈ adjointGroup τ (AlgebraicClosure K) :=
    mul_mem hg0C (inv_mem hz_adj)
  have hz' : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) (f : ℕ) z =
      z * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w := by
    have h := congrArg (fun x => z * x) hzLang
    simpa [mul_assoc] using h
  have h0_fix : Units.map (entrywiseHom Fr) (g0 * z⁻¹) = g0 * z⁻¹ := by
    rw [map_mul, map_inv, hfr, hg0, hz']
    group
  have hfixX : ∀ x ∈ Subgroup.zpowers (g0 * z⁻¹),
      Units.map (entrywiseHom Fr) x = x := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [map_zpow, h0_fix]
  have hafix : entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) (f : ℕ) (g0 * z⁻¹) =
      g0 * z⁻¹ := by
    have h0_fix' := h0_fix
    rw [hfr] at h0_fix'
    exact h0_fix'
  have hfinX : Finite (Subgroup.zpowers (g0 * z⁻¹)) := by
    refine ((CFSG.LieType.AlgebraicGroups.finite_setOf_entrywiseFrobGL_eq
      (τ := τ) (k := AlgebraicClosure K) (p := ringChar K) (n := f) f.pos).subset ?_).to_subtype
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    change entrywiseFrobGL τ (AlgebraicClosure K) (ringChar K) (f : ℕ)
      ((g0 * z⁻¹) ^ n) = (g0 * z⁻¹) ^ n
    rw [map_zpow, hafix]
  have hmemz : g0 * z⁻¹ ∈ (adjointGroup τ K).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    hrat (Subgroup.zpowers (g0 * z⁻¹)) hfinX
      (Subgroup.zpowers_le.mpr h0_adj) hfixX (Subgroup.mem_zpowers _)
  obtain ⟨h, hh, hheq⟩ := hmemz
  refine ⟨⟨h, hh⟩, z, hz, ?_⟩
  rw [hheq]
  group

theorem mem_kernelGroup_conj_iff
    {τ : Tag} {M : Type} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M)
    {K : Type} [Field K] {g0 : ModGL τ (AlgebraicClosure K)} {h : adjointGroup τ K}
    {d : ModGL τ (AlgebraicClosure K)} (hd : d ∈ kernelGroup χ (AlgebraicClosure K))
    (hg0 : g0 = baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K) * d)
    (x : adjointGroup τ K) :
    g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 ∈
        kernelGroup χ (AlgebraicClosure K) ↔
      ((h⁻¹ * x * h : adjointGroup τ K) : ModGL τ K) ∈ kernelGroup χ K := by
  let y : adjointGroup τ K := h⁻¹ * x * h
  let yL : ModGL τ (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K)
  have hdM : d ∈ torusGroup τ (AlgebraicClosure K) ⊔
      rootSpan τ (AlgebraicClosure K) (kernelRoots χ) := hd
  have hleft : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 =
      d⁻¹ * yL * d := by
    have hyL : (baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K))⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K) = yL := by
      simp only [yL, y, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    calc
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g0 =
          d⁻¹ * ((baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K))⁻¹ *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL τ K)) * d := by
        rw [hg0, mul_inv_rev]
        group
      _ = d⁻¹ * yL * d := by rw [hyL]
  unfold kernelGroup
  rw [hleft]
  constructor
  · intro hmem
    have hmem' : yL ∈ torusGroup τ (AlgebraicClosure K) ⊔
        rootSpan τ (AlgebraicClosure K) (kernelRoots χ) := by
      have h := mul_mem (mul_mem hdM hmem) (inv_mem hdM)
      rwa [show d * (d⁻¹ * yL * d) * d⁻¹ = yL by group] at h
    exact CFSG.LieType.AlgebraicGroups.mem_torus_sup_rootSpan_of_baseChangeGL_mem
      (algebraMap K (AlgebraicClosure K)) χ y.2 hmem'
  · intro hmem
    have hbc : yL ∈ torusGroup τ (AlgebraicClosure K) ⊔
        rootSpan τ (AlgebraicClosure K) (kernelRoots χ) := by
      have hle : torusGroup τ K ⊔ rootSpan τ K (kernelRoots χ) ≤
          (torusGroup τ (AlgebraicClosure K) ⊔
            rootSpan τ (AlgebraicClosure K) (kernelRoots χ)).comap
            (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
        sup_le (fun t ht => Subgroup.mem_sup_left
          (CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup
            (algebraMap K (AlgebraicClosure K)) ht))
          (fun r hr => Subgroup.mem_sup_right
            (CFSG.RankThree.Classical2.baseChangeGL_mem_rootSpan
              (algebraMap K (AlgebraicClosure K)) hr))
      exact hle hmem
    exact mul_mem (mul_mem (inv_mem hdM) hbc) hdM

end CFSG.StandardType.PhiTwoRootGen

end
