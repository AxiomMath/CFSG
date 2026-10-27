module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenF4Rat
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenLayer
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Even
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenStepOne
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE7
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Multiplicative
open CFSG.HardMathSupport.Lang.AnisoF4 CFSG.ClassicalGroups.Symplectic


private theorem inv_mul_conj_mul {G : Type*} [Group G] (a x : G) :
    a⁻¹ * (a * x * a⁻¹) * a = x := by group

private theorem exists_psi_injective_of_card
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hfK : Nat.card K = 2 ^ f)
    (hK4 : 4 ≤ Nat.card K) :
    ∃ Ψ : CFSG.Open.StatedSp 4 K →* adjointGroup .F4 K, Function.Injective Ψ ∧
      Ψ.range.map (adjointGroup .F4 K).subtype = phiTwoB4Subgroup K := by
  classical
  obtain ⟨Ψ, hΨker, hΨrange, -, -⟩ :=
    exists_psi_B4_F4_frame_even (K := K) (f := f) hfK hK4
  have hΨinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [← center_statedSp_eq_bot_of_charP_two (m := 4) (by norm_num)]
    exact hΨker hs
  refine ⟨Ψ, hΨinj, ?_⟩
  rw [hΨrange, CFSG.ComponentClassification.CatLeafProof.map_subtype_iSup_b4Chain,
    ← phiTwoB4Roots_eq_kernelRoots, ← phiTwoB4Subgroup_eq_rootSpan]

theorem mem_iSup_phiTwoComp_of_mem_phiTwoB4
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {w : WeylGroup .F4} (hneg : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot .F4 γ → w • γ = -γ)
    {g0 : ModGL .F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup .F4 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem .F4) (AlgebraicClosure K) w)
    {x : adjointGroup .F4 K}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .F4 K) * g0 ∈
      phiTwoB4Subgroup (AlgebraicClosure K)) :
    x ∈ ⨆ γ : {γ : Fin Tag.F4.rank → ℤ // IsRoot .F4 γ}, phiTwoComp g0 γ.1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨h, d, hd, hg0d⟩ := exists_mul_eq_phiTwoB4 hFr hneg hg0C hg0
  have hxh : ((h⁻¹ * x * h : adjointGroup .F4 K) : ModGL .F4 K) ∈ phiTwoB4Subgroup K :=
    (mem_phiTwoB4_iff hd hg0d x).1 hx
  obtain ⟨fv, -, hfv⟩ := FiniteField.card K 2
  have hfK : Nat.card K = 2 ^ (fv : ℕ) := by rw [Nat.card_eq_fintype_card, hfv]
  obtain ⟨Ψ, hΨinj, hDrange⟩ := exists_psi_injective_of_card hfK hK4
  obtain ⟨sp, hsp⟩ : ∃ s : CFSG.Open.StatedSp 4 K, Ψ s = h⁻¹ * x * h := by
    have h1 : ((h⁻¹ * x * h : adjointGroup .F4 K) : ModGL .F4 K) ∈
        Ψ.range.map (adjointGroup .F4 K).subtype := by rw [hDrange]; exact hxh
    rw [Subgroup.mem_map] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    obtain ⟨e, he⟩ := hy
    exact ⟨e, Subtype.ext (by rw [he]; exact hyx)⟩
  have hxs : x = h * Ψ sp * h⁻¹ := by
    rw [show Ψ sp = h⁻¹ * x * h from hsp]
    group
  let Ψ' : CFSG.ClassicalGroups.Alternating.Gsp (spForm 4 K) →* adjointGroup .F4 K :=
    ((MulAut.conj h).toMonoidHom.comp Ψ).comp (spEquiv (m := 4) (K := K)).symm.toMonoidHom
  have hΨ'inj : Function.Injective Ψ' := by
    intro a b hab
    have h1 : Ψ ((spEquiv (m := 4) (K := K)).symm a) =
        Ψ ((spEquiv (m := 4) (K := K)).symm b) := (MulAut.conj h).injective hab
    exact (spEquiv (m := 4) (K := K)).symm.injective (hΨinj h1)
  have hΨ'apply : ∀ a : CFSG.ClassicalGroups.Alternating.Gsp (spForm 4 K),
      Ψ' a = (MulAut.conj h) (Ψ ((spEquiv (m := 4) (K := K)).symm a)) := fun a => rfl
  have hxeq : x = Ψ' ((spEquiv (m := 4) (K := K)) sp) := by
    rw [hxs, hΨ'apply, MulEquiv.symm_apply_apply, MulAut.conj_apply]
  set p := Nat.minFac (Nat.card K + 1) with hpdef
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpq : p ∣ Nat.card K + 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h2
    have h2dvd : 2 ∣ Nat.card K + 1 := h2 ▸ hpq
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
  have hrat : ∀ X : Subgroup (ModGL .F4 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .F4 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
        X ≤ (adjointGroup .F4 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    fun X _ hXC hXF y hy =>
      mem_map_adjointGroup_F4_of_frobenius_fixed Fr hFr (hXC hy) (hXF y hy)
  obtain ⟨T, hTinj, hTcoe⟩ :=
    exists_phiTwoTorus_of_neg (n := p) hpq hFr hrat hneg hg0C hg0 hζo hζ
  have hmem_range : ∀ y : adjointGroup .F4 K, y ∈ Ψ'.range ↔
      ((h⁻¹ * y * h : adjointGroup .F4 K) : ModGL .F4 K) ∈ phiTwoB4Subgroup K := by
    intro y
    constructor
    · rintro ⟨a, rfl⟩
      have hmem : ((Ψ ((spEquiv (m := 4) (K := K)).symm a) : adjointGroup .F4 K) :
          ModGL .F4 K) ∈ Ψ.range.map (adjointGroup .F4 K).subtype :=
        Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      rw [hDrange] at hmem
      convert hmem using 2
      rw [hΨ'apply, MulAut.conj_apply]
      group
    · intro hy
      have hy' : ((h⁻¹ * y * h : adjointGroup .F4 K) : ModGL .F4 K) ∈
          Ψ.range.map (adjointGroup .F4 K).subtype := by rw [hDrange]; exact hy
      rw [Subgroup.mem_map] at hy'
      obtain ⟨z, hz, hzy⟩ := hy'
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hz
      refine ⟨(spEquiv (m := 4) (K := K)) s, ?_⟩
      have hzy' : h⁻¹ * y * h = z := Subtype.ext hzy.symm
      rw [← hs] at hzy'
      rw [hΨ'apply, MulEquiv.symm_apply_apply, MulAut.conj_apply, ← hzy']
      group
  have hTmem : ∀ t : Fin 4 → ZMod p, T (ofAdd t) ∈ Ψ'.range := by
    intro t
    refine (hmem_range _).mpr ((mem_phiTwoB4_iff hd hg0d (T (ofAdd t))).mp ?_)
    rw [hTcoe t]
    rw [inv_mul_conj_mul g0 (rootDiagUnit .F4 (TableBExc.E6Three.zetaVec ζ hζ t))]
    exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
  have hTle : T.range ≤ Ψ'.range := by
    rintro - ⟨t, rfl⟩
    exact hTmem t
  have hdim : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := finrank_spSpace
  have hmodel : CFSG.Open.IsElemAbelian p (T.range.comap Ψ') →
      (∀ g : CFSG.ClassicalGroups.Alternating.Gsp (spForm 4 K),
        (∀ x ∈ T.range.comap Ψ', g * x = x * g) → g ^ p = 1 → g ∈ T.range.comap Ψ') →
        GGTorusModelAt p (T.range.comap Ψ') :=
    fun hE hsc =>
      CFSG.StandardType.SpNsRootGen.ggTorusModelAt_gsp (B := spForm 4 K) spForm_isAlt
        spForm_nondegenerate hp hp2 hpq hK4 hdim (by norm_num) hE hsc
  have hxrange : x ∈ Ψ'.range := by
    rw [hxeq]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  exact range_le_iSup_phiTwoComp_of_ggTorusModelAt (τ := .F4) (Or.inr (Or.inr (Or.inr rfl)))
    hp2 hζo hζ hg0C hTinj hTcoe hΨ'inj hTle hmodel hxrange

end CFSG.StandardType.PhiTwoRootGen

end
