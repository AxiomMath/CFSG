module

public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamF4Shapes
import CFSG.LocalAnalysis.StandardType.GGFamF4Orbit
import CFSG.LocalAnalysis.StandardType.GGFamF4Tame
import CFSG.LocalAnalysis.StandardType.GGFamInnerCover
import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Gamma
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LowRankModelsPart2
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Inner
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2SmallJ
import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem l10lH3_ggCompFieldAt_of_spCover
    {G : Type} [Group G] {X : Subgroup G}
    {K : Type} [Field K] [Finite K] {k : ℕ}
    (hk : Nat.card K = 2 ^ k) (hK4 : 4 ≤ Nat.card K)
    (hq : CFSG.Open.IsQuasisimple ↥X)
    (g : ↥(CFSG.Open.StatedSp 2 K) →* ↥X) (hgsurj : Function.Surjective g)
    (hgker : g.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp 2 K)) :
    CFSG.StandardType.GGCompFieldAt (2 ^ k) X := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hqs := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num)
    (Or.inl (Or.inr hK4))
  have hperf : commutator ↥(CFSG.Open.StatedSp 2 K) = ⊤ :=
    Group.isPerfect_def.mp hqs.1
  obtain ⟨e_quot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hgsurj hgker
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk; omega
    · exact h
  have hadm : StatedLieAdmissible .PSp 2 2 k := by
    refine ⟨Nat.prime_two, hk1, le_rfl, ?_⟩
    intro hcon
    have h4 : 4 ≤ 2 ^ k := by rw [← hk]; exact hK4
    have h2 : 2 ^ k = 2 := congrArg Prod.snd hcon
    omega
  have hclassSp : StatedClassicalModel
      (↥(CFSG.Open.StatedSp 2 K) ⧸ Subgroup.center ↥(CFSG.Open.StatedSp 2 K)) .PSp 2 2 k :=
    CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient
      (n := 2) (F := K) hadm hk
  obtain ⟨-, K', _, hfinK', hcardK', ⟨φ⟩⟩ := hclassSp
  have hclass : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp 2 2 k :=
    ⟨hadm, K', inferInstance, hfinK', hcardK', ⟨e_quot.symm.trans φ⟩⟩
  exact ggCompFieldAt_of_lieModel hq (Or.inl ⟨by decide, hclass⟩)
    ⟨by decide, by decide, by decide⟩

theorem famF4_b2_cover
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hB2 : FamF4B2Shape (componentRoots (famCharHom a) i)) :
    ∃ (E : Subfield L) (_ : Finite ↥E) (κ : ↥(CFSG.Open.StatedSp 2 ↥E) →* ModGL Tag.F4 L),
      Nat.card ↥E = S.D.q ∧ κ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp 2 ↥E) ∧
      rationalComponentM S.ρ S.Γ (famCharHom a) i ≤ κ.range ∧
      κ.range ≤ rationalSpanM S.ρ S.Γ (famCharHom a) i := by
  classical
  have hL2 : CharP L 2 := inferInstance
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  obtain ⟨v, hshape⟩ := hB2
  obtain ⟨horb, hlen⟩ := famF4_orbit S hp hp2 hT hap i
  have hs1 : componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 := hlen
  have hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]) := by
    rw [hs1, Function.iterate_one]
    exact CFSG.StandardType.F4ExplicitPos.B2Inner.b2_component_rho_twistInner
      (D := S.D) S.frob i hshape horb
  obtain ⟨σ, hfin, hcard, f, hf1, hker, -, hf4⟩ :=
    fam_exists_inner_cover_le S hρ i hinner
  obtain ⟨r, e, -, hchar, he, hqpow⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq L hchar hL2
  clear hchar
  have hqe : ∃ f : ℕ, 1 ≤ f ∧ S.D.q = 2 ^ f := ⟨e, he, by rw [hqpow, hr2]⟩
  have hΓ : S.Γ = S.D.model :=
    CFSG.StandardType.LieCore.ggLieF4_gamma_eq_model (L := L) S.D S.finite hqe
  let E := fixSubfield σ
  have : Finite ↥E := hfin
  have : CharP ↥E 2 := @Subfield.charP L _ E 2 hL2
  have hmodel := CFSG.StandardType.F4ExplicitPos.LowRankModels.b2Model (Ω := L) E v hshape
  have eC : ↥(CFSG.Open.StatedSp 2 ↥E) ≃* ↥(componentRootSpan E (famCharHom a) i) :=
    hmodel.trans ((MulEquiv.subgroupCongr
      (CFSG.StandardType.F4ExplicitPos.B2Finite.rootSpanOver_eq_map_rootSpan
        (Ω := L) E (componentRoots (famCharHom a) i))).trans
      ((Subgroup.equivMapOfInjective (rootSpan Tag.F4 ↥E (componentRoots (famCharHom a) i))
        (CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL E.subtype)
        (CFSG.StandardType.F4ExplicitPos.BaseChange.bcGL_injective E.subtype
          E.subtype.injective)).symm))
  let κ : ↥(CFSG.Open.StatedSp 2 ↥E) →* ModGL Tag.F4 L := f.comp eC.toMonoidHom
  have hκrange : κ.range = f.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨eC y, rfl⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨y, rfl⟩ := eC.surjective c
      exact ⟨y, rfl⟩
  have hκker : κ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp 2 ↥E) := by
    intro c hc
    have h1 : eC c ∈ f.ker := MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hc)
    have h2 := Subgroup.mem_center_iff.mp (hker h1)
    rw [Subgroup.mem_center_iff]
    intro c'
    apply eC.injective
    rw [map_mul, map_mul]
    exact h2 (eC c')
  have hNS : f.range ≤ rationalSpanM S.ρ S.Γ (famCharHom a) i := by
    unfold rationalSpanM
    refine le_inf (hf4.trans inf_le_left) ?_
    rw [hΓ]
    exact hf4.trans inf_le_right
  refine ⟨E, hfin, κ, ?_, hκker, ?_, ?_⟩
  · rw [hcard, hs1, pow_one]
  · rw [hκrange]
    exact hf1
  · rw [hκrange]
    exact hNS

theorem famF4_b2_two_equivAlt6
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hB2 : FamF4B2Shape (componentRoots (famCharHom a) i)) (hq2 : S.D.q = 2) :
    CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ∧
      Subgroup.center ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) = ⊥ ∧
      Nonempty (↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ≃* alternatingGroup (Fin 6)) := by
  classical
  obtain ⟨E, hfin, κ, hcard, hκker, hRle, hκle⟩ :=
    famF4_b2_cover S hp hp2 hT hap i hB2
  have : Finite ↥E := hfin
  have : CharP ↥E 2 := @Subfield.charP L _ E 2 (inferInstance : CharP L 2)
  have hE2 : Nat.card ↥E = 2 := by rw [hcard, hq2]
  have hcen : Subgroup.center ↥(CFSG.Open.StatedSp 2 ↥E) = ⊥ :=
    (CFSG.LieType.Universal.Symplectic.center_eq 2 ↥E).trans
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := 2))
  have hκinj : Function.Injective κ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact eq_bot_iff.mpr (hκker.trans hcen.le)
  have hD : ⁅κ.range, κ.range⁆ ≤ rationalComponentM S.ρ S.Γ (famCharHom a) i :=
    Subgroup.commutator_mono hκle hκle
  have hDq : CFSG.IsQuasisimple ↥⁅κ.range, κ.range⁆ :=
    CFSG.StandardType.F4ExplicitPos.B2SmallJ.isQuasisimple_derivedRange_sp4_two hE2 hκinj rfl
  have hns : ¬ Group.IsSolvable ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) := fun _ =>
    CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hDq
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hD))
  have hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
    (langFamTame_F4 S hp hp2 hT hap h1 i).resolve_right hns
  have hR : rationalComponentM S.ρ S.Γ (famCharHom a) i = ⁅κ.range, κ.range⁆ :=
    le_antisymm ((Subgroup.isPerfect_iff.mp hq.1).symm.le.trans
      (Subgroup.commutator_mono hRle hRle)) hD
  let eR : ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.subgroupCongr hR).trans
      (CFSG.StandardType.F4ExplicitPos.B2SmallJ.derivedRangeEquivAlt6 hE2 hκinj rfl)
  have hZ : Subgroup.center ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (f := eR.toMonoidHom) _ eR.injective).mp
      ((Subgroup.map_center_eq eR).trans (alternatingGroup.center_eq_bot (α := Fin 6) (by simp)))
  exact ⟨hq, hZ, ⟨eR⟩⟩

theorem famF4_laneB2
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit Tag.F4 (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hB2 : FamF4B2Shape (componentRoots (famCharHom a) i))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAt
        (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
        (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
      (S.D.q = 2 ∧ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 ∧
        Nat.card ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) = 360 ∧
        Nat.card (↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) = 360) := by
  classical
  have hL2 : CharP L 2 := inferInstance
  obtain ⟨-, hlen⟩ := famF4_orbit S hp hp2 hT hap i
  have hs1 : componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 := hlen
  by_cases hq2 : S.D.q = 2
  · obtain ⟨-, hZ, ⟨eR⟩⟩ := famF4_b2_two_equivAlt6 S hp hp2 hT hap h1 i hB2 hq2
    have hcard360 : Nat.card ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) = 360 := by
      rw [Nat.card_congr eR.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    refine Or.inr ⟨hq2, hs1, hcard360, ?_⟩
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv]
    exact hcard360
  · obtain ⟨E, hfin, κ, hcard, hκker, hRle, hκle⟩ :=
      famF4_b2_cover S hp hp2 hT hap i hB2
    have : Finite ↥E := hfin
    obtain ⟨r, e, -, hchar, he, hqpow⟩ := exists_char_pow S
    have hr2 : r = 2 := CharP.eq L hchar hL2
    have he2 : 2 ≤ e := by
      by_contra! hlt
      obtain rfl : e = 1 := by omega
      exact hq2 (by rw [hqpow, hr2, pow_one])
    have hk : Nat.card ↥E =
        2 ^ (e * componentOrbitLength S.ρ (componentRoots (famCharHom a) i)) := by
      rw [hcard, hqpow, hr2, hs1, mul_one]
    have h4 : 4 ≤ Nat.card ↥E := by
      rw [hcard, hqpow, hr2]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
    have hperfSp : Group.IsPerfect ↥(CFSG.Open.StatedSp 2 ↥E) :=
      (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 ↥E (by norm_num)
        (Or.inl (Or.inr h4))).1
    have hperfRange : Group.IsPerfect ↥κ.range :=
      Group.IsPerfect.ofSurjective (f := κ.rangeRestrict) κ.rangeRestrict_surjective
    have hcomm : ⁅κ.range, κ.range⁆ = κ.range :=
      (Subgroup.isPerfect_iff (H := κ.range)).mp hperfRange
    have hR : κ.range = rationalComponentM S.ρ S.Γ (famCharHom a) i := by
      refine le_antisymm ?_ hRle
      calc κ.range = ⁅κ.range, κ.range⁆ := hcomm.symm
        _ ≤ ⁅rationalSpanM S.ρ S.Γ (famCharHom a) i,
              rationalSpanM S.ρ S.Γ (famCharHom a) i⁆ :=
            Subgroup.commutator_mono hκle hκle
        _ = rationalComponentM S.ρ S.Γ (famCharHom a) i := rfl
    let g' : ↥(CFSG.Open.StatedSp 2 ↥E) →*
        ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
      κ.codRestrict _ (fun x => hR ▸ ⟨x, rfl⟩)
    have hg'surj : Function.Surjective g' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ : y ∈ κ.range := hR.symm ▸ hy
      exact ⟨x, Subtype.ext hx⟩
    have hg'ker : g'.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp 2 ↥E) := by
      intro c hc
      apply hκker
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    have hq' : CFSG.Open.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
      ggStrongRecog_open_isQuasisimple hq
    have hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) =
        2 ^ (e * componentOrbitLength S.ρ (componentRoots (famCharHom a) i)) := by
      rw [hqpow, hr2, pow_mul]
    refine Or.inl ?_
    rw [hQ]
    exact l10lH3_ggCompFieldAt_of_spCover hk h4 hq' g' hg'surj hg'ker

end CFSG.StandardType.TableCRes
