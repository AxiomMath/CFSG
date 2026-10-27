module

public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch3xD15

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.D15Proof
open scoped commutatorElement

@[expose] def B69One : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X : Subgroup (MulAut V)) (S M : Subgroup ↥X),
      (∃ (H : Type) (_ : Group H) (_ : Finite H), SQTKTauCeti.StronglyQuasithin H ∧
        SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f) →
      MinParabolic (⊤ : Subgroup ↥X) S M → pCoreOf 2 (⊤ : Subgroup ↥X) = ⊥ →
        ¬ IsStrongFFModule X

section D125

variable {G : Type} [Group G] [Finite G]

theorem centralizerMod_le_kerIn {G₂ T M₂ U L N : Subgroup G} (hmp : MinParabolic G₂ T M₂)
    (hUT : U ≤ T) (hstep : IsChiefStep G₂ U L N) (hnc : ¬ IsCentralStep G₂ L N) :
    centralizerMod L G₂ N ≤ kerIn M₂ G₂ := by
  have hTG₂ : T ≤ G₂ := hmp.isSylow.1
  have hG₂L : G₂ ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hG₂N : G₂ ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  set C := centralizerMod L G₂ N with hCdef
  have hconj : ∀ g ∈ G₂, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    refine ⟨G₂.mul_mem (G₂.mul_mem hg hc.1) (G₂.inv_mem hg),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hG₂L hg) hc.2.1) (Subgroup.inv_mem _ (hG₂L hg)),
      fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ N := (Subgroup.mem_normalizer_iff''.mp (hG₂N hg) u).mp hu
    have h1 := (Subgroup.mem_normalizer_iff.mp (hG₂L hg) _).mp (hc.2.2 _ hu')
    have e : g * c * g⁻¹ * u * (g * c * g⁻¹)⁻¹ * u⁻¹ =
        g * (c * (g⁻¹ * u * g) * c⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1
  have hCn : G₂ ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    B6.mem_normalizer_of_forall_mem (hconj g hg) fun c hc => by
      simpa using hconj g⁻¹ (G₂.inv_mem hg) c hc
  have hK : ¬ twoResidual G₂ ≤ C := by
    intro hle
    apply hnc
    refine isCentralStep_of_commutator_le hmp.isSylow (hUT.trans hTG₂) (hstep.1.1.trans hUT)
      hstep ?_
    rw [Subgroup.commutator_le]
    intro n hn p hp
    have hpC : p ∈ C := hle ((F6.twoResidual_eq_oTwoUpper G₂).symm ▸ hp)
    have h2 := L.inv_mem (hpC.2.2 n hn)
    rwa [show (p * n * p⁻¹ * n⁻¹)⁻¹ = ⁅n, p⁆ by rw [commutatorElement_def]; group] at h2
  exact hmp.le_kerIn_of_not_twoResidual_le (centralizerMod_le_left L G₂ N) hCn hK

theorem d125_of_b69One (hB : B69One) {G₂ T M₂ U : Subgroup G} (hmp : MinParabolic G₂ T M₂)
    (hsqtk : IsSQTKSub G₂) (hUT : U ≤ T) (hUe : IsElemAbelian 2 U) :
    D125 G₂ T U := by
  have hTG₂ : T ≤ G₂ := hmp.isSylow.1
  have hUG₂ : U ≤ G₂ := hUT.trans hTG₂
  intro L N hstep hnc A hAT hAe _
  have hG₂L : G₂ ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hG₂N : G₂ ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNU : N ≤ U := hstep.1.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hNU.trans hUG₂).trans hG₂L
  have hAG₂ : A ≤ G₂ := hAT.trans hTG₂
  have hE := isElemAbelian_secImg_of_le (L := L) hUe hNU
  by_contra hlt
  push Not at hlt
  have hnt : ¬ ∀ b ∈ A, ∀ e ∈ N, b * e * b⁻¹ * e⁻¹ ∈ L := by
    intro hall
    have hCA : centralizerMod L A N = A := le_antisymm (centralizerMod_le_left _ _ _)
      fun b hb => ⟨hb, hG₂L (hAG₂ hb), hall b hb⟩
    rw [hCA, Subgroup.relIndex_self] at hlt
    exact absurd hlt (not_lt.mpr (Nat.one_le_iff_ne_zero.mpr (relIndex_ne_zero _ _)))
  have hStrong := isStrongFFModule_autOn_secImg hE hNL hG₂L hG₂N hAG₂ hAe hnt hlt
  set A_ := Subgroup.normalizer (L : Set G) with hAdef
  set E := secImg A_ L N with hEdef
  set X := autOn (secImg A_ L G₂) E with hXdef
  let _ : CommGroup ↥E := commGroupOfElemAbelian hE
  have hsq' : ∀ v : ↥E, v ^ 2 = 1 := fun v => Subtype.ext (hE.2 v v.2)
  have hmemE : ∀ g : ↥G₂, secMk A_ L (Subgroup.inclusion hG₂L g) ∈
      Subgroup.normalizer (E : Set (SecQuot A_ L)) := fun g =>
    secMk_mem_normalizer_secImg (hG₂N g.2)
  let β : ↥G₂ →* ↥(Subgroup.normalizer (E : Set (SecQuot A_ L))) :=
    ((secMk A_ L).comp (Subgroup.inclusion hG₂L)).codRestrict _ hmemE
  let ψ : ↥G₂ →* MulAut ↥E := (conjAct E).comp β
  have hψX : ∀ g : ↥G₂, ψ g ∈ X := fun g =>
    Subgroup.mem_map.mpr ⟨β g, Subgroup.mem_subgroupOf.mpr
      (secMk_mem_secImg (A := A_) (B := L) (X := G₂) (x := Subgroup.inclusion hG₂L g) g.2), rfl⟩
  let φ : ↥G₂ →* ↥X := ψ.codRestrict X hψX
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a, haG, hay⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hy)
    refine ⟨⟨a, haG⟩, Subtype.ext ?_⟩
    show conjAct E (β ⟨a, haG⟩) = conjAct E y
    congr 1
    exact Subtype.ext hay
  have hker : φ.ker ≤ M₂.subgroupOf G₂ := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hψ1 : ψ g = 1 := congrArg Subtype.val hg
    have hcent : ((β g : ↥(Subgroup.normalizer (E : Set (SecQuot A_ L)))) : SecQuot A_ L) ∈
        Subgroup.centralizer (E : Set (SecQuot A_ L)) := A4.conjAct_eq_one_iff.mp hψ1
    have hgC : (g : G) ∈ centralizerMod L G₂ N := by
      refine ⟨g.2, hG₂L g.2, fun n hn => ?_⟩
      have hnE : secMk A_ L ⟨n, hNL hn⟩ ∈ E := secMk_mem_secImg (A := A_) (B := L) (X := N) hn
      have hcomm := Subgroup.mem_centralizer_iff.mp hcent _ hnE
      have h1 : secMk A_ L (⟨g, hG₂L g.2⟩ * ⟨n, hNL hn⟩ * ⟨g, hG₂L g.2⟩⁻¹ * ⟨n, hNL hn⟩⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        have hc : secMk A_ L ⟨n, hNL hn⟩ * secMk A_ L ⟨g, hG₂L g.2⟩ =
            secMk A_ L ⟨g, hG₂L g.2⟩ * secMk A_ L ⟨n, hNL hn⟩ := hcomm
        rw [← hc]
        group
      exact secMk_eq_one_iff.mp h1
    have hk := centralizerMod_le_kerIn hmp hUT hstep hnc hgC
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk 1 G₂.one_mem)
  have hmpX := MinParabolic.map_of_surjective hmp.subgroupOf hφsurj hker
  have hO2 : pCoreOf 2 (⊤ : Subgroup ↥X) = ⊥ := by
    set Q : Subgroup ↥X := pCoreOf 2 (⊤ : Subgroup ↥X) with hQdef
    have hQn : Q.Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥X)))
    have hQ := normal_two_eq_bot hUG₂ hstep hE (Q.map X.subtype) (Subgroup.map_subtype_le Q)
      (by
        have e : (Q.map X.subtype).subgroupOf X = Q :=
          Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q
        rw [e]
        exact hQn)
      ((pCoreOf_isPGroup 2 (⊤ : Subgroup ↥X)).map X.subtype)
    exact (Subgroup.map_eq_bot_iff_of_injective Q X.subtype_injective).mp hQ
  exact hB E hsq' X _ _ ⟨↥G₂, inferInstance, inferInstance, hsqtk.2, hsqtk.1, φ, hφsurj⟩ hmpX hO2 hStrong

end D125

theorem d125NonsolvableSQTK_of_b69One (hB : B69One) : D125NonsolvableSQTK := by
  intro G _ _ G₁ G₂ T V M₂ h hsq _ hq1 hVR₂ hUe
  have hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1 := fun hff =>
    hq1 ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₂ : Subgroup G) : Set G) :=
    le_normalizer_pCoreOf 2 G₂
  have hUT : conjClosure V G₂ ≤ T :=
    (conjClosure_le fun g hg v hv =>
      (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂)
  exact d125_of_b69One hB (h.minParabolic hnff) hsq hUT hUe

end CFSG.Quasithin
