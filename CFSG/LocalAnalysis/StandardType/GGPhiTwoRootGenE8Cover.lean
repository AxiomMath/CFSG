module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenE8D8
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenE8Weyl
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenStepOne
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenCover
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput
public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenAsm
public import CFSG.HardMathSupport.Malle.SeitzCube.Landing

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar (e8Neg e8Neg_smul)

theorem mem_iSup_phiTwoComp_of_mem_e8D8
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g : ModGL .E8 (AlgebraicClosure K)} (hgC : g ∈ adjointGroup .E8 (AlgebraicClosure K))
    (hg : Units.map (entrywiseHom Fr) g =
      g * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) e8Neg)
    {x : adjointGroup .E8 K}
    (hx : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * g ∈
      torusGroup .E8 (AlgebraicClosure K) ⊔
        rootSpan .E8 (AlgebraicClosure K) {γ | IsRoot .E8 γ ∧ Even (γ (e8Node 0))}) :
    x ∈ ⨆ γ : {γ : Fin Tag.E8.rank → ℤ // IsRoot .E8 γ}, phiTwoComp g γ.1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hrat : ∀ X : Subgroup (ModGL .E8 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .E8 (AlgebraicClosure K) →
      (∀ y ∈ X, Units.map (entrywiseHom Fr) y = y) →
        X ≤ (adjointGroup .E8 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X _ hXC hXF y hy =>
      CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E8
        (K := K) (L := AlgebraicClosure K) Fr hFr (hXC hy) (hXF y hy)
  obtain ⟨h, d, hd, hgd⟩ :=
    exists_mul_eq_kernelGroup (maskChar (τ := .E8) e8BitsD8) hFr hrat hgC hg
      (CFSG.LieType.AlgebraicGroups.canonicalRep_mem_torus_sup_rootSpan_kernelRoots
        e8Neg_mem_closure_rootReflection_kernelRoots_e8BitsD8)
  have hxχ : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * g ∈
      torusGroup .E8 (AlgebraicClosure K) ⊔
        rootSpan .E8 (AlgebraicClosure K)
          (kernelRoots (maskChar (τ := .E8) e8BitsD8)) := by
    rw [e8D8Roots_eq_kernelRoots] at hx
    exact hx
  have hxh0 : ((h⁻¹ * x * h : adjointGroup .E8 K) : ModGL .E8 K) ∈
      torusGroup .E8 K ⊔
        rootSpan .E8 K (kernelRoots (maskChar (τ := .E8) e8BitsD8)) :=
    (mem_kernelGroup_conj_iff (maskChar (τ := .E8) e8BitsD8) hd hgd x).1 hxχ
  have hxh : ((h⁻¹ * x * h : adjointGroup .E8 K) : ModGL .E8 K) ∈
      rootSpan .E8 K {γ : Fin Tag.E8.rank → ℤ | IsRoot .E8 γ ∧ Even (γ (e8Node 0))} := by
    rw [← e8D8Roots_eq_kernelRoots] at hxh0
    rw [sup_eq_right.mpr torusGroup_le_rootSpan_e8D8] at hxh0
    exact hxh0
  obtain ⟨Ψ, hΨinj, hΨrange⟩ := exists_e8D8Omega_injective K
  let G : Type := ↥(CFSG.RankThree.Classical2.orthDerived
    (CFSG.LieType.Universal.Spin.quadPlus 8 K))
  let Ψ' : G →* adjointGroup .E8 K := (MulAut.conj h).toMonoidHom.comp Ψ
  have hΨ'inj : Function.Injective Ψ' := fun a b hab =>
    hΨinj ((MulAut.conj h).injective hab)
  have hΨ'apply : ∀ a : G, Ψ' a = (MulAut.conj h) (Ψ a) := fun _ => rfl
  have hmem_range : ∀ y : adjointGroup .E8 K, y ∈ Ψ'.range ↔
      ((h⁻¹ * y * h : adjointGroup .E8 K) : ModGL .E8 K) ∈
        rootSpan .E8 K {γ : Fin Tag.E8.rank → ℤ | IsRoot .E8 γ ∧ Even (γ (e8Node 0))} := by
    intro y
    constructor
    · rintro ⟨a, rfl⟩
      have hmem : ((Ψ a : adjointGroup .E8 K) : ModGL .E8 K) ∈
          rootSpan .E8 K {γ : Fin Tag.E8.rank → ℤ | IsRoot .E8 γ ∧
            Even (γ (e8Node 0))} := by
        rw [← hΨrange]
        exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
      have heq : h⁻¹ * Ψ' a * h = Ψ a := by
        rw [hΨ'apply, MulAut.conj_apply]
        group
      rw [heq]
      exact hmem
    · intro hy
      have hy' : ((h⁻¹ * y * h : adjointGroup .E8 K) : ModGL .E8 K) ∈
          Ψ.range.map (adjointGroup .E8 K).subtype := by
        rw [hΨrange]
        exact hy
      rw [Subgroup.mem_map] at hy'
      obtain ⟨z, hz, hzy⟩ := hy'
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hz
      refine ⟨s, ?_⟩
      have hzy' : h⁻¹ * y * h = z := Subtype.ext hzy.symm
      rw [← hs] at hzy'
      rw [hΨ'apply, MulAut.conj_apply, ← hzy']
      group
  have hxrange : x ∈ Ψ'.range := (hmem_range x).mpr hxh
  set p := Nat.minFac (Nat.card K + 1) with hpdef
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpq : p ∣ Nat.card K + 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    have h2dvd : 2 ∣ Nat.card K + 1 := h2 ▸ hpq
    obtain ⟨fv, -, hfv⟩ := FiniteField.card K 2
    have hfK : Nat.card K = 2 ^ (fv : ℕ) := by rw [Nat.card_eq_fintype_card, hfv]
    have hfv0 : (fv : ℕ) ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hfK
      omega
    have h2q : 2 ∣ Nat.card K := by
      rw [hfK]
      exact dvd_pow_self 2 hfv0
    have h3 : 2 ∣ (Nat.card K + 1) - Nat.card K := Nat.dvd_sub h2dvd h2q
    rw [Nat.add_sub_cancel_left] at h3
    exact absurd h3 (by norm_num)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζo, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_orderOf_eq_of_dvd_add_one K
      (L := AlgebraicClosure K) (N := p) hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  obtain ⟨T, hTinj, hTcoe⟩ :=
    exists_phiTwoTorus_of_neg (n := p) hpq hFr hrat (fun γ _ => e8Neg_smul γ) hgC hg hζo hζ
  have hTmem : ∀ t : Fin Tag.E8.rank → ZMod p, T (Multiplicative.ofAdd t) ∈ Ψ'.range := by
    intro t
    refine (hmem_range _).mpr ?_
    have h1 : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((T (Multiplicative.ofAdd t) : adjointGroup .E8 K) : ModGL .E8 K) * g ∈
        torusGroup .E8 (AlgebraicClosure K) ⊔
          rootSpan .E8 (AlgebraicClosure K)
            (kernelRoots (maskChar (τ := .E8) e8BitsD8)) := by
      rw [hTcoe t]
      have heq : g⁻¹ * (g * rootDiagUnit .E8 (TableBExc.E6Three.zetaVec ζ hζ t) * g⁻¹) * g =
          rootDiagUnit .E8 (TableBExc.E6Three.zetaVec ζ hζ t) := by group
      rw [heq]
      exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
    have h2 : ((h⁻¹ * T (Multiplicative.ofAdd t) * h : adjointGroup .E8 K) : ModGL .E8 K) ∈
        torusGroup .E8 K ⊔
          rootSpan .E8 K (kernelRoots (maskChar (τ := .E8) e8BitsD8)) :=
      (mem_kernelGroup_conj_iff (maskChar (τ := .E8) e8BitsD8) hd hgd
        (T (Multiplicative.ofAdd t))).1 h1
    rw [← e8D8Roots_eq_kernelRoots] at h2
    rw [sup_eq_right.mpr torusGroup_le_rootSpan_e8D8] at h2
    exact h2
  have hTle : T.range ≤ Ψ'.range := by
    rintro - ⟨t, rfl⟩
    exact hTmem t
  have hdim : Module.finrank K (Fin 8 ⊕ Fin 8 → K) = 2 * 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hmodel : CFSG.Open.IsElemAbelian p (T.range.comap Ψ') →
      (∀ g : G, (∀ y ∈ T.range.comap Ψ', g * y = y * g) → g ^ p = 1 →
        g ∈ T.range.comap Ψ') →
      GGTorusModelAt p (T.range.comap Ψ') :=
    fun hE hsc =>
      CFSG.StandardType.OmNsRootGen.ggTorusModelAt_of_selfCentralizing
        (F := K) (V := Fin 8 ⊕ Fin 8 → K)
        (Q := CFSG.LieType.Universal.Spin.quadPlus 8 K) (p := p) (ℓ := 8)
        (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus (n := 8) (K := K))
        hp hp2 hpq hK4 hdim (by norm_num) hE hsc
  exact range_le_iSup_phiTwoComp_of_ggTorusModelAt (Or.inr (Or.inr (Or.inl rfl)))
    hp2 hζo hζ hgC hTinj hTcoe hΨ'inj hTle hmodel hxrange

theorem iSup_phiTwoComp_eq_top_E8
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup .E8} (hneg : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ → w • γ = -γ)
    {g0 : ModGL .E8 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup .E8 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w) :
    (⨆ γ : {γ : Fin Tag.E8.rank → ℤ // IsRoot .E8 γ}, phiTwoComp g0 γ.1) = ⊤ := by
  have hw : w = e8Neg := by
    refine ext_single fun i => ?_
    rw [hneg _ (IsRoot.basis i), e8Neg_smul]
  subst w
  refine iSup_phiTwoComp_eq_top_of_kernelRoots_cover e8D4Char hFr
    (fun x hx hfix =>
      CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E8
        (K := K) (L := AlgebraicClosure K) Fr hFr hx hfix)
    (fun v => ext_single fun i => by
      rw [mul_smul, mul_smul, e8Neg_smul, e8Neg_smul, smul_neg])
    e8Neg_mem_closure_rootReflection_kernelRoots_e8D4Char
    (Φ₁ := {γ : Fin Tag.E8.rank → ℤ | IsRoot .E8 γ ∧ Even (γ (e8Node 0))})
    (fun g hgC hgFr x hx => mem_iSup_phiTwoComp_of_mem_e8D8 hK4 hFr hgC hgFr hx)
    (fun γ hγ => ?_) hg0C hg0
  obtain ⟨v, S, hγS, hDS, hS⟩ := exists_D8_cover_E8 hγ
  exact ⟨v, S, hγS, hDS, fun δ hδ => ⟨(hS δ hδ).1, IsRoot.smul (hS δ hδ).1 v⁻¹,
    (hS δ hδ).2⟩⟩

theorem phiTwoGenAt_E8 :
    PhiTwoGenAt .E8 := by
  intro K _ _ _ hK4 w Fr g0 hw hFr hg0C hg0
  have hrev : ReversesSigns w := fun α hα hpos =>
    (IsRoot.height_neg_iff (IsRoot.smul hα w)).2 fun j =>
      hw α hα ((IsRoot.height_pos_iff hα).1 hpos) j
  have hrev' : ReversesSigns e8Neg := fun α _ hpos => by
    rw [e8Neg_smul, height_neg]
    omega
  exact iSup_phiTwoComp_eq_top_E8 hK4 hFr
    (fun γ _ => by rw [ReversesSigns.eq hrev hrev', e8Neg_smul]) hg0C hg0

end CFSG.StandardType.PhiTwoRootGen

end
