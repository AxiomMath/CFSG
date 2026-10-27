module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6Defs
import CFSG.LocalAnalysis.StandardType.GGQ2CoverComponents
import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.StandardType.GGQ2SpRealization
import CFSG.Walter.W67.Section6.Util
import CFSG.GroupTheory.PerfectCentralQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConjBase
import CFSG.RankThree.PartOne.FIS.VRelation

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.CoverComponents


private noncomputable def eqCov_rho_equiv {G : Type} [Group G] {E : Subgroup G}
    {M : Type} [Group M] (ρ : ↥E →* M) (hρ : Function.Injective ρ) :
    ↥E ≃* ↥ρ.range :=
  MonoidHom.ofInjective (f := ρ) hρ

private theorem eqCov_rho_equiv_apply {G : Type} [Group G] {E : Subgroup G}
    {M : Type} [Group M] (ρ : ↥E →* M) (hρ : Function.Injective ρ) (a : ↥E) :
    ((eqCov_rho_equiv ρ hρ a : ↥ρ.range) : M) = ρ a := by
  change ((MonoidHom.ofInjective hρ a : ↥ρ.range) : M) = ρ a
  rfl

private noncomputable def eqCov_coord {G : Type} [Group G] {E : Subgroup G}
    {M : Type} [Group M] {R : RawFrameData} {H' : Subgroup M} (ρ : ↥E →* M)
    (hρ : Function.Injective ρ) (mf' : ModelFrame H' ρ.range R) : Additive ↥E ≃+ R.V :=
  (MulEquiv.toAdditive (eqCov_rho_equiv ρ hρ)).trans mf'.coord

private theorem eqCov_coord_ofMul {G : Type} [Group G] {E : Subgroup G}
    {M : Type} [Group M] {R : RawFrameData} {H' : Subgroup M} (ρ : ↥E →* M)
    (hρ : Function.Injective ρ) (mf' : ModelFrame H' ρ.range R) (a : ↥E) :
    eqCov_coord ρ hρ mf' (Additive.ofMul a) =
      mf'.coord (Additive.ofMul (eqCov_rho_equiv ρ hρ a)) := rfl

private theorem eqCov_mulAut_congr_apply {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (φ : MulAut X) (y : Y) : (MulAut.congr e φ) y = e (φ (e.symm y)) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]

private theorem eqCov_mulAut_congr_symm {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (ψ : MulAut Y) (x : X) : ((MulAut.congr e).symm ψ) x = e.symm (ψ (e x)) := by
  have h := congrArg (fun f : MulAut Y => f (e x)) (MulEquiv.apply_symm_apply (MulAut.congr e) ψ)
  rw [eqCov_mulAut_congr_apply] at h
  rw [← h]
  simp

private theorem eqCov_ggLin_coord {G : Type} [Group G] {E : Subgroup G} {M : Type} [Group M]
    {R : RawFrameData} {H' : Subgroup M} (ρ : ↥E →* M) (hρ : Function.Injective ρ)
    (mf' : ModelFrame H' ρ.range R) (φ : MulAut ↥E) :
    ggLin (p := 3) (eqCov_coord ρ hρ mf') φ =
      ggLin (p := 3) mf'.coord
        (MulAut.congr (eqCov_rho_equiv ρ hρ) φ) := by
  have h := ggLin_mulEquiv_congr (p := 3) (eqCov_rho_equiv ρ hρ).symm mf'.coord
    (MulAut.congr (eqCov_rho_equiv ρ hρ) φ)
  rw [MulEquiv.symm_symm] at h
  rw [show MulAut.congr (eqCov_rho_equiv ρ hρ).symm
      (MulAut.congr (eqCov_rho_equiv ρ hρ) φ) = φ from ?_] at h
  · exact h
  · ext a
    rw [eqCov_mulAut_congr_apply, eqCov_mulAut_congr_apply]
    simp

private theorem eqCov_ggLin_coord_comp {G : Type} [Group G] {E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} {H' : Subgroup M} (ρ : ↥E →* M)
    (hρ : Function.Injective ρ) (mf' : ModelFrame H' ρ.range R) :
    ggLin (p := 3) (eqCov_coord ρ hρ mf') =
      (ggLin (p := 3) mf'.coord).comp
        (MulAut.congr (eqCov_rho_equiv ρ hρ)).toMonoidHom :=
  MonoidHom.ext fun φ => eqCov_ggLin_coord ρ hρ mf' φ

private theorem eqCov_range_comp_inclusion {G : Type} [Group G] {E : Subgroup G}
    {M : Type} [Group M] (ρ : ↥E →* M) {A : Subgroup G} (hAE : A ≤ E) :
    (ρ.comp (Subgroup.inclusion hAE)).range = (A.subgroupOf E).map ρ := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

private theorem eqCov_mem_subgroupOf_map {G : Type} [Group G] {E : Subgroup G} {M : Type}
    [Group M] (ρ : ↥E →* M) (hρ : Function.Injective ρ) {A : Subgroup G} (hAE : A ≤ E)
    (a : ↥E) :
    (a : G) ∈ A ↔
      ((eqCov_rho_equiv ρ hρ a : ↥ρ.range) : M) ∈ (A.subgroupOf E).map ρ := by
  constructor
  · intro ha
    rw [eqCov_rho_equiv_apply]
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr ha)
  · intro ha
    obtain ⟨x, hx, hxρ⟩ := Subgroup.mem_map.mp ha
    have heq : eqCov_rho_equiv ρ hρ ⟨(x : G), hAE (Subgroup.mem_subgroupOf.mp hx)⟩ =
        eqCov_rho_equiv ρ hρ a := by
      apply Subtype.ext
      rw [eqCov_rho_equiv_apply, eqCov_rho_equiv_apply]
      exact hxρ
    have hxa : (⟨(x : G), hAE (Subgroup.mem_subgroupOf.mp hx)⟩ : ↥E) = a :=
      (eqCov_rho_equiv ρ hρ).injective heq
    rw [← hxa]
    exact Subgroup.mem_subgroupOf.mp hx

private theorem eqCov_ggLinImage_eq {G : Type} [Group G] {E : Subgroup G} {M : Type} [Group M]
    {R : RawFrameData} {H' : Subgroup M} (ρ : ↥E →* M) (hρ : Function.Injective ρ)
    (mf' : ModelFrame H' ρ.range R) {A : Subgroup G} (hAE : A ≤ E) :
    ggLinImage (p := 3) (eqCov_coord ρ hρ mf') A =
      ggLinImage (p := 3) mf'.coord ((A.subgroupOf E).map ρ) := by
  ext v
  obtain ⟨a, rfl⟩ : ∃ a : ↥E, eqCov_coord ρ hρ mf' (Additive.ofMul a) = v :=
    ⟨Additive.toMul ((eqCov_coord ρ hρ mf').symm v), by simp⟩
  rw [ofMul_mem_ggLinImage, eqCov_coord_ofMul, ofMul_mem_ggLinImage]
  exact eqCov_mem_subgroupOf_map ρ hρ hAE a

private theorem eqCov_ggLinImage_eq_range {G : Type} [Group G] {E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} {H' : Subgroup M} (ρ : ↥E →* M)
    (hρ : Function.Injective ρ) (mf' : ModelFrame H' ρ.range R) {A : Subgroup G} (hAE : A ≤ E) :
    ggLinImage (p := 3) (eqCov_coord ρ hρ mf') A =
      ggLinImage (p := 3) mf'.coord (ρ.comp (Subgroup.inclusion hAE)).range := by
  rw [eqCov_range_comp_inclusion ρ hAE]
  exact eqCov_ggLinImage_eq ρ hρ mf' hAE


private noncomputable def eqCov_restrict {G : Type} [Group G] {E : Subgroup G} {M : Type}
    [Group M] (ρ : ↥E →* M) {A : Subgroup G} (hAE : A ≤ E) : ↥A →* M :=
  ρ.comp (Subgroup.inclusion hAE)

private theorem eqCov_equivariant_restrict {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M) (ρ : ↥E →* M)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {A : Subgroup G} (hAE : A ≤ E) :
    Equivariant (hAE.trans hEN) π (eqCov_restrict ρ hAE) := by
  intro a h
  exact hEq (Subgroup.inclusion hAE a) h

private theorem eqCov_derived_comap_perfect {X R : Type*} [Group X] [Group R] (π : X →* R)
    (hker : π.ker ≤ Subgroup.center X) {Y : Subgroup R} (hYle : Y ≤ π.range)
    (hY : ⁅Y, Y⁆ = Y) :
    (⁅Y.comap π, Y.comap π⁆).map π = Y ∧
      ⁅⁅Y.comap π, Y.comap π⁆, ⁅Y.comap π, Y.comap π⁆⁆ = ⁅Y.comap π, Y.comap π⁆ := by
  have hmap : (⁅Y.comap π, Y.comap π⁆).map π = Y := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hYle, hY]
  refine ⟨hmap, le_antisymm ?_ ?_⟩
  · refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · have hlift : ∀ g ∈ Y.comap π, ∃ d ∈ ⁅Y.comap π, Y.comap π⁆,
        d⁻¹ * g ∈ Subgroup.center X := by
      intro g hg
      have hg' : π g ∈ (⁅Y.comap π, Y.comap π⁆).map π := by
        rw [hmap]
        exact hg
      obtain ⟨d, hd, hdg⟩ := Subgroup.mem_map.mp hg'
      refine ⟨d, hd, hker ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdg, inv_mul_cancel]
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨d₁, hd₁, hz₁⟩ := hlift g₁ hg₁
    obtain ⟨d₂, hd₂, hz₂⟩ := hlift g₂ hg₂
    have hc := CFSG.GroupTheory.commutatorElement_mul_center (x := d₁) (y := d₂) hz₁ hz₂
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at hc
    rw [hc]
    exact Subgroup.commutator_mem_commutator hd₁ hd₂

private theorem eqCov_mapCentralizerEq {G : Type} [Group G] [Finite G] {H E A : Subgroup G}
    {M : Type} [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (hAE : A ≤ E)
    (π : ↥H →* M) (ρ : ↥E →* M) (hA : IsPGroup 3 ↥A)
    (_hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹) :
    ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H).map π =
      π.range ⊓ Subgroup.centralizer (((eqCov_restrict ρ hAE).range : Subgroup M) : Set M) := by
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨h, hh, rfl⟩ := hy
    refine Subgroup.mem_inf.mpr ⟨MonoidHom.mem_range.mpr ⟨h, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨a, rfl⟩ := hr
    have hhA : (h : G) ∈ Subgroup.centralizer (A : Set G) :=
      (Subgroup.mem_subgroupOf.mp hh).2
    have hacomm : (a : G) * (h : G) = (h : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hhA a a.2
    have hconj : H.normalizerMonoidHom ⟨(a : G), (hAE.trans hEN) a.2⟩ h = h := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe, hacomm]
      group
    have h1 : π (H.normalizerMonoidHom ⟨(a : G), (hAE.trans hEN) a.2⟩ h) =
        ρ (Subgroup.inclusion hAE a) * π h * (ρ (Subgroup.inclusion hAE a))⁻¹ :=
      hEq (Subgroup.inclusion hAE a) h
    rw [hconj] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1.symm
  · intro y hy
    obtain ⟨hyπ, hyC⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨h₀, hh₀⟩ := hyπ
    let fiber := {h : ↥H // π h = y}
    let φ : ↥A →* MulAut ↥H := H.normalizerMonoidHom.comp (Subgroup.inclusion (hAE.trans hEN))
    have hφ_apply : ∀ (a : ↥A) (h : ↥H),
        φ a h = H.normalizerMonoidHom ⟨(a : G), (hAE.trans hEN) a.2⟩ h := fun _ _ => rfl
    have hφ_coe : ∀ (a : ↥A) (h : ↥H),
        ((φ a h : ↥H) : G) = (a : G) * (h : G) * (a : G)⁻¹ := by
      intro a h
      rw [hφ_apply a h, normalizerMonoidHom_coe]
    have hramem : ∀ a : ↥A, (eqCov_restrict ρ hAE) a ∈ (eqCov_restrict ρ hAE).range := by
      intro a
      rw [MonoidHom.range_eq_map]
      exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_top a, rfl⟩
    have hact_mem : ∀ (a : ↥A) {h : ↥H}, π h = y → π (φ a h) = y := by
      intro a h hh
      have h1 : π (φ a h) =
          (eqCov_restrict ρ hAE) a * π h * ((eqCov_restrict ρ hAE) a)⁻¹ :=
        hEq (Subgroup.inclusion hAE a) h
      rw [h1, hh]
      have hyc : (eqCov_restrict ρ hAE) a * y = y * (eqCov_restrict ρ hAE) a :=
        Subgroup.mem_centralizer_iff.mp hyC ((eqCov_restrict ρ hAE) a) (hramem a)
      rw [hyc]; group
    let : MulAction ↥A fiber :=
      { smul := fun a h => ⟨φ a h.1, hact_mem a h.2⟩
        one_smul := by
          intro h
          apply Subtype.ext
          show φ 1 h.1 = h.1
          rw [map_one]
          rfl
        mul_smul := by
          intro a b h
          apply Subtype.ext
          show φ (a * b) h.1 = φ a (φ b h.1)
          rw [map_mul]
          rfl }
    have hcard : Nat.card fiber = Nat.card π.ker := by
      refine Nat.card_congr ?_
      refine
        { toFun := fun h => ⟨h₀⁻¹ * h.1, ?_⟩
          invFun := fun k => ⟨h₀ * k.1, ?_⟩
          left_inv := ?_
          right_inv := ?_ }
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hh₀, h.2]
        group
      · rw [map_mul, hh₀, MonoidHom.mem_ker.mp k.2, mul_one]
      · intro h
        apply Subtype.ext
        show h₀ * (h₀⁻¹ * h.1) = h.1
        group
      · intro k
        apply Subtype.ext
        show h₀⁻¹ * (h₀ * k.1) = k.1
        group
    have hcard3 : ¬ 3 ∣ Nat.card fiber := by rw [hcard]; exact hker3
    obtain ⟨h, hhfix⟩ :=
      IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hA fiber hcard3
    refine Subgroup.mem_map.mpr ⟨h.1, ?_, h.2⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨h.1.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro g hg
    let a : ↥A := ⟨g, hg⟩
    have hfixa : φ a h.1 = h.1 := congrArg Subtype.val (hhfix a)
    have hcoe : (a : G) * (h.1 : G) = (h.1 : G) * (a : G) := by
      have hc := hφ_coe a h.1
      rw [hfixa] at hc
      exact mul_inv_eq_iff_eq_mul.mp hc.symm
    simpa using hcoe

private theorem eqCov_mulAut_fixes_comap_commutator {G : Type} [Group G]
    {H E A : Subgroup G} {M : Type} [Group M]
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (hAE : A ≤ E) (π : ↥H →* M) (ρ : ↥E →* M)
    (hker : π.ker ≤ Subgroup.center ↥H)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {Y : Subgroup M} (hYle : Y ≤ Subgroup.centralizer
      (((eqCov_restrict ρ hAE).range : Subgroup M) : Set M))
    (a : ↥A) {z : ↥H} (hz : z ∈ ⁅Y.comap π, Y.comap π⁆) :
    H.normalizerMonoidHom ⟨(a : G), (hAE.trans hEN) a.2⟩ z = z := by
  refine mulAut_fixes_commutator (H.normalizerMonoidHom ⟨(a : G), (hAE.trans hEN) a.2⟩)
    (Y.comap π) ?_ z hz
  intro q hq
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  have hramem : (eqCov_restrict ρ hAE) a ∈ (eqCov_restrict ρ hAE).range := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.mem_map.mpr ⟨a, Subgroup.mem_top a, rfl⟩
  have hqY : π q ∈ Y := Subgroup.mem_comap.mp hq
  have hc := Subgroup.mem_centralizer_iff.mp (hYle hqY) ((eqCov_restrict ρ hAE) a) hramem
  have hφq : π (H.normalizerMonoidHom ⟨(a : G), (hAE.trans hEN) a.2⟩ q) = π q := by
    have h1 : π (H.normalizerMonoidHom ⟨(a : G), (hAE.trans hEN) a.2⟩ q) =
        (eqCov_restrict ρ hAE) a * π q * ((eqCov_restrict ρ hAE) a)⁻¹ :=
      hEq (Subgroup.inclusion hAE a) q
    rw [h1, hc]
    group
  rw [hφq, mul_inv_cancel]

private theorem eqCov_exists_component_of_isComponentOf {G : Type} [Group G] [Finite G]
    {H E A : Subgroup G} {M : Type} [Group M]
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (hAE : A ≤ E) (π : ↥H →* M) (ρ : ↥E →* M)
    (hA : IsPGroup 3 ↥A) (hker : π.ker ≤ Subgroup.center ↥H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {X : Subgroup G} (hX : IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G))) :
    ∃ Y : Subgroup M,
      IsComponentOf Y (π.range ⊓ Subgroup.centralizer
        (((eqCov_restrict ρ hAE).range : Subgroup M) : Set M)) ∧
        X = (⁅Y.comap π, Y.comap π⁆).map H.subtype := by
  obtain ⟨hXle, hXsub, hXq⟩ := hX
  have hXH : X ≤ H := hXle.trans inf_le_left
  let X' : Subgroup ↥H := X.subgroupOf H
  let Y : Subgroup M := X'.map π
  have hmapC : ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H).map π
      = π.range ⊓ Subgroup.centralizer
        (((eqCov_restrict ρ hAE).range : Subgroup M) : Set M) :=
    eqCov_mapCentralizerEq hEN hAE π ρ hA hker hker3 hEq
  have hXnat : CFSG.IsQuasisimple ↥X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥X).mp hXq
  have hX'nat : CFSG.IsQuasisimple ↥X' :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hXH)).mpr hXnat
  have : Group.IsPerfect ↥X' := hX'nat.1
  have hX'le : X' ≤ Y.comap π := Subgroup.map_le_iff_le_comap.mp le_rfl
  have hZeq : ⁅Y.comap π, Y.comap π⁆ = X' := by
    rw [commutator_comap_eq π hker (le_rfl : Y ≤ X'.map π),
      inf_eq_right.mpr hX'le, Subgroup.commutator_eq_self]
  refine ⟨Y, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← hmapC]
    exact Subgroup.map_mono (fun x hx => by
      rw [Subgroup.mem_subgroupOf]; exact hXle hx)
  · have hsub' : IsSubnormal X'
        ((H ⊓ Subgroup.centralizer (A : Set G)).subgroupOf H) := by
      simpa only [X', Subgroup.comap_subtype] using
        IsSubnormal.comap H.subtype hXsub
    have h := IsSubnormal.map π hsub'
    rwa [hmapC] at h
  · have hnot : ¬ X' ≤ π.ker := by
      intro hle
      have : Nontrivial (↥X' ⧸ Subgroup.center ↥X') := hX'nat.2.1.toNontrivial
      have : Nontrivial ↥X' := (QuotientGroup.mk'_surjective (Subgroup.center ↥X')).nontrivial
      have : IsMulCommutative ↥X' :=
        IsMulCommutative.of_comm fun (a b : ↥X') =>
          Subtype.ext_iff.mpr (by
            rw [Subgroup.coe_mul, Subgroup.coe_mul]
            exact (Subgroup.mem_center_iff.mp (hker (hle a.2)) (b : ↥H)).symm)
      exact Group.IsPerfect.not_isMulCommutative (G := ↥X') inferInstance
    have hYnat : CFSG.IsQuasisimple ↥Y :=
      CFSG.LocalCores.isQuasisimple_map hX'nat π hnot
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Y).mpr hYnat
  · rw [hZeq, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show X ≤ H from hXH)]

private theorem eqCov_isComponentOf_commutator_comap {G : Type} [Group G] [Finite G]
    {H E A : Subgroup G} {M : Type} [Group M]
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (hAE : A ≤ E) (π : ↥H →* M) (ρ : ↥E →* M)
    (hA : IsPGroup 3 ↥A) (hker : π.ker ≤ Subgroup.center ↥H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {Y : Subgroup M}
    (hY : IsComponentOf Y (π.range ⊓ Subgroup.centralizer
      (((eqCov_restrict ρ hAE).range : Subgroup M) : Set M))) :
    IsComponentOf ((⁅Y.comap π, Y.comap π⁆).map H.subtype)
      (H ⊓ Subgroup.centralizer (A : Set G)) := by
  obtain ⟨hYle, hYsub, hYq⟩ := hY
  have hYnat : CFSG.IsQuasisimple ↥Y :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Y).mp hYq
  let C : Subgroup G := H ⊓ Subgroup.centralizer (A : Set G)
  let C' : Subgroup ↥H := C.subgroupOf H
  have hC'map : C'.map π = π.range ⊓ Subgroup.centralizer
      (((eqCov_restrict ρ hAE).range : Subgroup M) : Set M) :=
    eqCov_mapCentralizerEq hEN hAE π ρ hA hker hker3 hEq
  have hYC' : Y ≤ C'.map π := by rw [hC'map]; exact hYle
  let Z : Subgroup ↥H := ⁅Y.comap π, Y.comap π⁆
  have hZeq : Z = ⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆ :=
    commutator_comap_eq π hker hYC'
  have hZnat : CFSG.IsQuasisimple ↥Z := by
    rw [hZeq]
    exact isQuasisimple_commutator_comap π hker hYC' hYnat
  have hZsub' : IsSubnormal (⁅Y.comap π ⊓ C', Y.comap π ⊓ C'⁆) C' :=
    isSubnormal_commutator_comap π hker hC'map hYle hYsub
  have hZsub : IsSubnormal Z C' := by rw [hZeq]; exact hZsub'
  have hXsub : IsSubnormal (Z.map H.subtype) C := by
    have h := IsSubnormal.map H.subtype hZsub
    rwa [Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (show C ≤ H from inf_le_left)] at h
  have hXle : Z.map H.subtype ≤ C := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨z.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro g hg
    let a : ↥A := ⟨g, hg⟩
    have hfix := eqCov_mulAut_fixes_comap_commutator hEN hAE π ρ hker hEq
      (hYle.trans inf_le_right) a hz
    have hc : ((H.normalizerMonoidHom ⟨(a : G), (hAE.trans hEN) a.2⟩ z : ↥H) : G)
        = (a : G) * (z : G) * (a : G)⁻¹ := by
      rw [normalizerMonoidHom_coe]
    have hcoe : (a : G) * (z : G) * (a : G)⁻¹ = (z : G) := by rw [← hc, hfix]
    exact mul_inv_eq_iff_eq_mul.mp hcoe
  have hXq : CFSG.Open.IsQuasisimple ↥(Z.map H.subtype) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      ↥(Z.map H.subtype)).mpr
      (isQuasisimple_map_injective H.subtype H.subtype_injective hZnat)
  exact ⟨hXle, hXsub, hXq⟩

private theorem eqCov_isComponentOfCoverIff {G : Type} [Group G] [Finite G]
    {H E A : Subgroup G} {M : Type} [Group M]
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (hAE : A ≤ E) (π : ↥H →* M) (ρ : ↥E →* M)
    (hA : IsPGroup 3 ↥A) (hker : π.ker ≤ Subgroup.center ↥H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    (X : Subgroup G) :
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ Y : Subgroup M, IsComponentOf Y (π.range ⊓ Subgroup.centralizer
        (((eqCov_restrict ρ hAE).range : Subgroup M) : Set M)) ∧
        X = (⁅Y.comap π, Y.comap π⁆).map H.subtype := by
  constructor
  · intro hX
    exact eqCov_exists_component_of_isComponentOf hEN hAE π ρ hA hker hker3 hEq hX
  · rintro ⟨Y, hY, rfl⟩
    exact eqCov_isComponentOf_commutator_comap hEN hAE π ρ hA hker hker3 hEq hY

private theorem eqCov_memDerivedComapIff {H R : Type*} [Group H] [Group R] (π : H →* R)
    (hker : π.ker ≤ Subgroup.center H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    {Y : Subgroup R} (hYle : Y ≤ π.range) (hYperf : ⁅Y, Y⁆ = Y)
    (e : H) (he3 : e ^ 3 = 1) :
    e ∈ ⁅Y.comap π, Y.comap π⁆ ↔ π e ∈ Y := by
  constructor
  · intro he
    have hmem : π e ∈ (⁅Y.comap π, Y.comap π⁆).map π := Subgroup.mem_map_of_mem π he
    rwa [Subgroup.map_commutator, Subgroup.map_comap_eq_self hYle, hYperf] at hmem
  · intro hpe
    set Z : Subgroup H := ⁅Y.comap π, Y.comap π⁆ with hZdef
    have hZmap : Z.map π = Y := by
      rw [hZdef, Subgroup.map_commutator, Subgroup.map_comap_eq_self hYle, hYperf]
    have hpeZ : π e ∈ Z.map π := by rw [hZmap]; exact hpe
    obtain ⟨x, hxZ, hxπ⟩ := Subgroup.mem_map.mp hpeZ
    have hzker : x⁻¹ * e ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxπ, inv_mul_cancel]
    have hzcent : x⁻¹ * e ∈ Subgroup.center H := hker hzker
    have hcommxz : Commute x (x⁻¹ * e) := Subgroup.mem_center_iff.mp hzcent x
    have hzpow : (x⁻¹ * e) ^ Nat.card π.ker = 1 := by
      have hzcard : Nat.card (Subgroup.zpowers (x⁻¹ * e)) ∣ Nat.card π.ker :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzker)
      have hzord : orderOf (x⁻¹ * e) ∣ Nat.card π.ker := by
        rwa [Nat.card_zpowers] at hzcard
      exact orderOf_dvd_iff_pow_eq_one.mp hzord
    have hepow : e ^ Nat.card π.ker ∈ Z := by
      have h1 : e = x * (x⁻¹ * e) := by group
      rw [h1, hcommxz.mul_pow, hzpow, mul_one]
      exact Subgroup.pow_mem Z hxZ _
    have hcop : Nat.Coprime (Nat.card π.ker) 3 :=
      Nat.coprime_comm.mpr ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3)
    have hone : (1 : ℤ) = (Nat.card π.ker : ℤ) * ((Nat.card π.ker).gcdA 3)
        + ((3 : ℕ) : ℤ) * ((Nat.card π.ker).gcdB 3) := by
      have h := Nat.gcd_eq_gcd_ab (Nat.card π.ker) 3
      rw [hcop] at h
      simpa using h
    have hmain : e = (e ^ Nat.card π.ker) ^ ((Nat.card π.ker).gcdA 3)
        * (e ^ 3) ^ ((Nat.card π.ker).gcdB 3) := by
      calc e = e ^ (1 : ℤ) := (zpow_one e).symm
        _ = e ^ ((Nat.card π.ker : ℤ) * ((Nat.card π.ker).gcdA 3)
              + ((3 : ℕ) : ℤ) * ((Nat.card π.ker).gcdB 3)) := by rw [hone]
        _ = e ^ ((Nat.card π.ker : ℤ) * ((Nat.card π.ker).gcdA 3))
              * e ^ (((3 : ℕ) : ℤ) * ((Nat.card π.ker).gcdB 3)) := by rw [zpow_add]
        _ = (e ^ ((Nat.card π.ker : ℕ) : ℤ)) ^ ((Nat.card π.ker).gcdA 3)
              * (e ^ ((3 : ℕ) : ℤ)) ^ ((Nat.card π.ker).gcdB 3) := by
              rw [zpow_mul, zpow_mul]
        _ = (e ^ Nat.card π.ker) ^ ((Nat.card π.ker).gcdA 3)
              * (e ^ 3) ^ ((Nat.card π.ker).gcdB 3) := by
              rw [zpow_natCast, zpow_natCast]
    rw [hmain, he3, one_zpow, mul_one]
    exact Subgroup.zpow_mem Z hepow _


private theorem eqCov_mem_centralizer {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {M : Type} [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M)
    (ρ : ↥E →* M) (_hρ : Function.Injective ρ) (hker : π.ker ≤ Subgroup.center ↥H)
    (_hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {Y : Subgroup M} (hYle : Y ≤ π.range) (hYperf : ⁅Y, Y⁆ = Y) (a : ↥E) :
    (a : G) ∈ Subgroup.centralizer
        (((⁅Y.comap π, Y.comap π⁆).map H.subtype : Subgroup G) : Set G) ↔
      ρ a ∈ Subgroup.centralizer ((Y : Subgroup M) : Set M) := by
  have hmap : (⁅Y.comap π, Y.comap π⁆).map π = Y :=
    (eqCov_derived_comap_perfect π hker hYle hYperf).1
  have hXtop : commutator ↥(⁅Y.comap π, Y.comap π⁆) = ⊤ := by
    have hperf := (eqCov_derived_comap_perfect π hker hYle hYperf).2
    exact Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  have hEqFull : Equivariant hEN π ρ := fun e h => hEq e h
  have hX := commuteCoverIff_holds hEN π ρ hker hEqFull _ hXtop a
  rw [hmap] at hX
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  have h1 : (∀ x ∈ ((⁅Y.comap π, Y.comap π⁆).map H.subtype : Subgroup G),
        x * (a : G) = (a : G) * x) ↔
      ∀ x ∈ ⁅Y.comap π, Y.comap π⁆, (a : G) * (x : G) = (x : G) * (a : G) := by
    constructor
    · intro h x hx
      exact (h (x : G) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)).symm
    · intro h g hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      exact (h x hx).symm
  refine h1.trans (hX.trans ?_)
  exact ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩

private theorem eqCov_mem_component {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {M : Type} [Group M] (_hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M)
    (ρ : ↥E →* M) (_hρ : Function.Injective ρ) (hker : π.ker ≤ Subgroup.center ↥H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker) (hEab : IsElemAbelian 3 E)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    (hρinv : ∀ e : ↥E, ρ e ∈ π.range → (e : G) ∈ H)
    {Y : Subgroup M} (hYle : Y ≤ π.range) (hYperf : ⁅Y, Y⁆ = Y) (a : ↥E) :
    (a : G) ∈ ((⁅Y.comap π, Y.comap π⁆).map H.subtype : Subgroup G) ↔ ρ a ∈ Y := by
  constructor
  · intro h
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp h
    have hπx : π x ∈ Y := by
      have hmap := (eqCov_derived_comap_perfect π hker hYle hYperf).1
      rw [← hmap]
      exact Subgroup.mem_map_of_mem π hx
    have hxH : x = (⟨(a : G), hxa ▸ x.2⟩ : ↥H) := Subtype.ext hxa
    rw [hxH] at hπx
    simpa [hρπ a (hxa ▸ x.2)] using hπx
  · intro h
    have haH : (a : G) ∈ H := hρinv a (hYle h)
    let e : ↥H := ⟨(a : G), haH⟩
    have he3 : e ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hEab.2 (a : G) a.2
    have heX : e ∈ ⁅Y.comap π, Y.comap π⁆ :=
      (eqCov_memDerivedComapIff π hker hker3 hYle hYperf e he3).mpr (by
        rw [show π e = ρ a from (hρπ a haH).symm]
        exact h)
    exact Subgroup.mem_map.mpr ⟨e, heX, rfl⟩

private theorem eqCov_marked {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (π : ↥H →* M) (ρ : ↥E →* M)
    (hker : π.ker ≤ Subgroup.center ↥H)
    (mf' : ModelFrame π.range ρ.range R) (c : R.Code) (hc : R.admissible c) :
    LargeEvenMarking
      ↥(((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype : Subgroup G))
      (fun lab _ _ _ _ _ => lab = R.label c) := by
  have hYle : mf'.component c ≤ π.range := mf'.component_le c hc
  have hYperf : ⁅mf'.component c, mf'.component c⁆ = mf'.component c :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (mf'.marked c hc).1)
  obtain ⟨hmap, hperf⟩ := eqCov_derived_comap_perfect π hker hYle hYperf
  have hY : LargeEvenMarking ↥((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map π)
      (fun lab _ _ _ _ _ => lab = R.label c) := by
    rw [hmap]
    exact mf'.marked c hc
  have hX := (SCFourCover.largeEvenMarking_map_iff hker hperf
    (fun lab => lab = R.label c)).2 hY
  exact largeEvenMarking_congr
    ((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).equivMapOfInjective H.subtype
      H.subtype_injective).symm (fun _ _ _ _ _ _ h => h) hX

private theorem eqCov_cent_eq {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M)
    (ρ : ↥E →* M) (hρ : Function.Injective ρ) (hker : π.ker ≤ Subgroup.center ↥H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    (mf' : ModelFrame π.range ρ.range R) (c : R.Code) (hc : R.admissible c) :
    ggLinImage (p := 3) (eqCov_coord ρ hρ mf')
        (Subgroup.centralizer
          (((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
            Subgroup G) : Set G)) = R.cent c := by
  have hYle : mf'.component c ≤ π.range := mf'.component_le c hc
  have hYperf : ⁅mf'.component c, mf'.component c⁆ = mf'.component c :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (mf'.marked c hc).1)
  ext v
  obtain ⟨a, rfl⟩ : ∃ a : ↥E, eqCov_coord ρ hρ mf' (Additive.ofMul a) = v :=
    ⟨Additive.toMul ((eqCov_coord ρ hρ mf').symm v), by simp⟩
  rw [ofMul_mem_ggLinImage, eqCov_coord_ofMul, ← mf'.cent_eq c hc, ofMul_mem_ggLinImage]
  rw [eqCov_rho_equiv_apply]
  exact eqCov_mem_centralizer hEN π ρ hρ hker hker3 hEq hYle hYperf a

private theorem eqCov_inside_eq {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M)
    (ρ : ↥E →* M) (hρ : Function.Injective ρ) (hker : π.ker ≤ Subgroup.center ↥H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker) (hEab : IsElemAbelian 3 E)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    (hρinv : ∀ e : ↥E, ρ e ∈ π.range → (e : G) ∈ H)
    (mf' : ModelFrame π.range ρ.range R) (c : R.Code) (hc : R.admissible c) :
    ggLinImage (p := 3) (eqCov_coord ρ hρ mf')
        (((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
          Subgroup G)) = R.inside c := by
  have hYle : mf'.component c ≤ π.range := mf'.component_le c hc
  have hYperf : ⁅mf'.component c, mf'.component c⁆ = mf'.component c :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (mf'.marked c hc).1)
  ext v
  obtain ⟨a, rfl⟩ : ∃ a : ↥E, eqCov_coord ρ hρ mf' (Additive.ofMul a) = v :=
    ⟨Additive.toMul ((eqCov_coord ρ hρ mf').symm v), by simp⟩
  rw [ofMul_mem_ggLinImage, eqCov_coord_ofMul, ← mf'.inside_eq c hc, ofMul_mem_ggLinImage]
  rw [eqCov_rho_equiv_apply]
  exact eqCov_mem_component hEN π ρ hρ hker hker3 hEab hρπ hρinv hYle hYperf a

private theorem eqCov_occurs_iff {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M)
    (ρ : ↥E →* M) (hρ : Function.Injective ρ) (hker : π.ker ≤ Subgroup.center ↥H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker) (hEab : IsElemAbelian 3 E)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    (mf' : ModelFrame π.range ρ.range R) (A : Subgroup G) (hAE : A ≤ E) (X : Subgroup G) :
    IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ c : R.Code, R.admissible c ∧
        R.occurs (ggLinImage (p := 3) (eqCov_coord ρ hρ mf') A) c ∧
        X = ((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
          Subgroup G) := by
  have hp : IsPGroup 3 ↥A := fun z =>
    ⟨1, Subtype.ext (by simpa using hEab.2 (z : G) (hAE z.2))⟩
  have hA'E' : (ρ.comp (Subgroup.inclusion hAE)).range ≤ ρ.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨Subgroup.inclusion hAE a, rfl⟩
  have hcov := eqCov_isComponentOfCoverIff hEN hAE π ρ hp hker hker3 hEq X
  constructor
  · intro h
    rw [hcov] at h
    obtain ⟨Y, hY, rfl⟩ := h
    obtain ⟨c, hc, hocc, rfl⟩ := (mf'.occurs_iff _ hA'E' Y).mp hY
    exact ⟨c, hc, by rwa [eqCov_ggLinImage_eq_range ρ hρ mf' hAE], rfl⟩
  · rintro ⟨c, hc, hocc, rfl⟩
    rw [hcov]
    have hocc' : R.occurs (ggLinImage (p := 3) mf'.coord
        (eqCov_restrict ρ hAE).range) c := by
      rwa [eqCov_ggLinImage_eq_range ρ hρ mf' hAE] at hocc
    exact ⟨mf'.component c, by
      simpa only [eqCov_restrict] using
        (mf'.occurs_iff _ hA'E' (mf'.component c)).mpr ⟨c, hc, hocc', rfl⟩, rfl⟩


private noncomputable def eqCov_kernelSub {G : Type} [Group G] {H : Subgroup G} {M : Type}
    [Group M] (π : ↥H →* M) : Subgroup G :=
  π.ker.map H.subtype

private theorem eqCov_kernelSub_le {G : Type} [Group G] {H : Subgroup G} {M : Type}
    [Group M] (π : ↥H →* M) : eqCov_kernelSub π ≤ H := by
  rintro x ⟨k, _hk, rfl⟩
  exact k.2

private theorem eqCov_rho_conj {G : Type} [Group G] {H E : Subgroup G} {M : Type} [Group M]
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M) (ρ : ↥E →* M)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {x : ↥H} (hx : (x : G) ∈ Subgroup.normalizer (E : Set G)) (a : ↥E) :
    ρ ⟨(x : G) * (a : G) * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hx (a : G)).1 a.2⟩ =
      π x * ρ a * (π x)⁻¹ := by
  let e' : ↥E :=
    ⟨(x : G) * (a : G) * (x : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hx (a : G)).1 a.2⟩
  have haxH : (a : G) * (x : G) * (a : G)⁻¹ ∈ H := by
    have h := (H.normalizerMonoidHom ⟨(a : G), hEN a.2⟩ x).2
    simpa only [normalizerMonoidHom_coe] using h
  have hcommH : (x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹ ∈ H := by
    have h1 : (x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹ =
        (x : G) * ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ := by group
    rw [h1]
    exact H.mul_mem x.2 (H.inv_mem haxH)
  let c : ↥H :=
    ⟨(x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹, hcommH⟩
  have hcommE : (x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹ ∈ E :=
    E.mul_mem ((Subgroup.mem_normalizer_iff.mp hx (a : G)).1 a.2) (E.inv_mem a.2)
  have hc_eq : c = x * (⟨(a : G) * (x : G) * (a : G)⁻¹, haxH⟩ : ↥H)⁻¹ := by
    apply Subtype.ext
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hπc : π c = π x * ρ a * (π x)⁻¹ * (ρ a)⁻¹ := by
    have hπax : π (⟨(a : G) * (x : G) * (a : G)⁻¹, haxH⟩ : ↥H) =
        ρ a * π x * (ρ a)⁻¹ := hEq a x
    rw [hc_eq, map_mul, map_inv, hπax]
    group
  have he' : e' = (⟨(x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹, hcommE⟩ : ↥E) * a := by
    apply Subtype.ext
    simp only [e', Subgroup.coe_mul]
    group
  calc
    ρ e' = ρ ((⟨(x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹, hcommE⟩ : ↥E) * a) := by
      rw [he']
    _ = ρ ⟨(x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹, hcommE⟩ * ρ a := map_mul ρ _ _
    _ = π c * ρ a := by rw [hρπ _ hcommH]
    _ = (π x * ρ a * (π x)⁻¹ * (ρ a)⁻¹) * ρ a := by rw [hπc]
    _ = π x * ρ a * (π x)⁻¹ := by group

private theorem eqCov_conj_mem_range {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M) (ρ : ↥E →* M)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {x : ↥H} (hx : (x : G) ∈ Subgroup.normalizer (E : Set G)) (a : ↥E) :
    π x * ρ a * (π x)⁻¹ ∈ ρ.range :=
  ⟨⟨_, (Subgroup.mem_normalizer_iff.mp hx (a : G)).1 a.2⟩,
    eqCov_rho_conj hEN π ρ hρπ hEq hx a⟩

private theorem eqCov_map_mem_normalizer {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M) (ρ : ↥E →* M)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {x : ↥H} (hx : (x : G) ∈ Subgroup.normalizer (E : Set G)) :
    π x ∈ Subgroup.normalizer ((ρ.range : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨a, rfl⟩
    exact eqCov_conj_mem_range hEN π ρ hρπ hEq hx a
  · intro hz
    obtain ⟨a, ha⟩ : ∃ a : ↥E, ρ a = π x * z * (π x)⁻¹ := hz
    have hx' : (x : G)⁻¹ ∈ Subgroup.normalizer (E : Set G) := Subgroup.inv_mem _ hx
    have hmem := eqCov_conj_mem_range hEN π ρ hρπ hEq (x := x⁻¹) hx' a
    rw [ha] at hmem
    have hπinv : π x⁻¹ = (π x)⁻¹ := map_inv π x
    rw [hπinv] at hmem
    convert hmem using 2; group


private theorem eqCov_conj_mem_kernel {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M) (ρ : ↥E →* M)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    (e : ↥E) {x : ↥H} (hx : x ∈ π.ker) :
    H.normalizerMonoidHom ⟨(e : G), hEN e.2⟩ x ∈ π.ker := by
  rw [MonoidHom.mem_ker]
  have h1 : π (H.normalizerMonoidHom ⟨(e : G), hEN e.2⟩ x) = ρ e * π x * (ρ e)⁻¹ :=
    hEq e x
  rw [h1, MonoidHom.mem_ker.mp hx, mul_one, mul_inv_cancel]

private theorem eqCov_kernel_inf_bot {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker) (hEab : IsElemAbelian 3 E) :
    eqCov_kernelSub π ⊓ E = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxN, hxE⟩
  obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hxN
  have hx : x = (k : G) := hkx.symm
  rw [hx] at hxE
  rw [hx]
  have hk3 : k ^ 3 = 1 := by
    apply Subtype.ext
    have h3 : (k : G) ^ 3 = 1 := by simpa using hEab.2 (k : G) hxE
    simpa using h3
  have hdvd3 : orderOf k ∣ 3 := orderOf_dvd_of_pow_eq_one hk3
  have hdvdK : orderOf k ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hk
  have hcop : Nat.Coprime 3 (Nat.card π.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3
  have hone : orderOf k = 1 := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd3 hdvdK)
  have hk1 : k = 1 := orderOf_eq_one_iff.mp hone
  simp [hk1]

private theorem eqCov_kernel_normalized_by_E {G : Type} [Group G] {H E : Subgroup G}
    {M : Type} [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M)
    (ρ : ↥E →* M)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹) :
    E ≤ Subgroup.normalizer ((eqCov_kernelSub π : Subgroup G) : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    rw [← hkx]
    refine Subgroup.mem_map.mpr ⟨H.normalizerMonoidHom ⟨(e : G), hEN he⟩ k, ?_, ?_⟩
    · exact eqCov_conj_mem_kernel hEN π ρ hEq ⟨e, he⟩ hk
    · show ((H.normalizerMonoidHom ⟨(e : G), hEN he⟩ k : ↥H) : G) =
        e * (k : G) * e⁻¹
      rw [normalizerMonoidHom_coe]
  · intro hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    have hkγ := eqCov_conj_mem_kernel hEN π ρ hEq
      (⟨(e : G)⁻¹, E.inv_mem he⟩ : ↥E) hk
    have hxH : (x : G) ∈ H := by
      have h1 : ((H.normalizerMonoidHom ⟨(e : G)⁻¹, hEN (E.inv_mem he)⟩ k : ↥H) : G) ∈ H :=
        (H.normalizerMonoidHom ⟨(e : G)⁻¹, hEN (E.inv_mem he)⟩ k).2
      rw [normalizerMonoidHom_coe] at h1
      have hkG : (k : G) = e * x * e⁻¹ := hkx
      have h2 : (e : G)⁻¹ * (k : G) * (e : G) = x := by
        rw [hkG]
        group
      simpa [h2] using h1
    have hkconj : H.normalizerMonoidHom ⟨(e : G)⁻¹, hEN (E.inv_mem he)⟩ k = ⟨x, hxH⟩ := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe]
      have hkG : (k : G) = e * x * e⁻¹ := hkx
      rw [hkG]
      group
    rw [hkconj] at hkγ
    exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hkγ, rfl⟩


private theorem eqCov_conj_mem_sup {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M) (ρ : ↥E →* M)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    (hρinv : ∀ e : ↥E, ρ e ∈ π.range → (e : G) ∈ H)
    {Y : Subgroup M} {y : ↥Y} (hyN : (y : M) ∈ Subgroup.normalizer ((ρ.range : Subgroup M) : Set M))
    {x₀ : ↥H} (hx₀π : π x₀ = (y : M)) (e : ↥E) :
    (x₀ : G) * (e : G) * (x₀ : G)⁻¹ ∈ (E ⊔ eqCov_kernelSub π : Subgroup G) := by
  have hmemr : (y : M) * ρ e * (y : M)⁻¹ ∈ ρ.range :=
    (Subgroup.mem_normalizer_iff.mp hyN (ρ e)).1 ⟨e, rfl⟩
  obtain ⟨e', he'⟩ := hmemr
  have hxeH : (e : G) * (x₀ : G) * (e : G)⁻¹ ∈ H := by
    have h := (H.normalizerMonoidHom ⟨(e : G), hEN e.2⟩ x₀).2
    simpa only [normalizerMonoidHom_coe] using h
  have hcH : (x₀ : G) * (e : G) * (x₀ : G)⁻¹ * (e : G)⁻¹ ∈ H := by
    have h1 : (x₀ : G) * (e : G) * (x₀ : G)⁻¹ * (e : G)⁻¹ =
        (x₀ : G) * ((e : G) * (x₀ : G) * (e : G)⁻¹)⁻¹ := by group
    rw [h1]
    exact H.mul_mem x₀.2 (H.inv_mem hxeH)
  let c : ↥H := ⟨(x₀ : G) * (e : G) * (x₀ : G)⁻¹ * (e : G)⁻¹, hcH⟩
  have hc_eq : c = x₀ * (⟨(e : G) * (x₀ : G) * (e : G)⁻¹, hxeH⟩ : ↥H)⁻¹ := by
    apply Subtype.ext
    simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hπc : π c = (y : M) * ρ e * (y : M)⁻¹ * (ρ e)⁻¹ := by
    have hπex : π (⟨(e : G) * (x₀ : G) * (e : G)⁻¹, hxeH⟩ : ↥H) =
        ρ e * π x₀ * (ρ e)⁻¹ := hEq e x₀
    rw [hc_eq, map_mul, map_inv, hπex, hx₀π]
    group
  have he'e_mem : (e' : G) * (e : G)⁻¹ ∈ E :=
    E.mul_mem e'.2 (E.inv_mem e.2)
  have hρe'e : ρ ⟨(e' : G) * (e : G)⁻¹, he'e_mem⟩ = π c := by
    have h1 : (⟨(e' : G) * (e : G)⁻¹, he'e_mem⟩ : ↥E) = e' * e⁻¹ := rfl
    rw [h1, map_mul, map_inv, he', hπc]
  have he'e_range : ρ ⟨(e' : G) * (e : G)⁻¹, he'e_mem⟩ ∈ π.range := ⟨c, hρe'e.symm⟩
  have he'e_H : (e' : G) * (e : G)⁻¹ ∈ H := hρinv _ he'e_range
  have he'e_π : ρ ⟨(e' : G) * (e : G)⁻¹, he'e_mem⟩ =
      π ⟨(e' : G) * (e : G)⁻¹, he'e_H⟩ := hρπ _ he'e_H
  have hkH : ((e' : G) * (e : G)⁻¹)⁻¹ *
      ((x₀ : G) * (e : G) * (x₀ : G)⁻¹ * (e : G)⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem he'e_H) hcH
  let k : ↥H := ⟨((e' : G) * (e : G)⁻¹)⁻¹ *
      ((x₀ : G) * (e : G) * (x₀ : G)⁻¹ * (e : G)⁻¹), hkH⟩
  have hk_ker : k ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : π k = (π ⟨(e' : G) * (e : G)⁻¹, he'e_H⟩)⁻¹ * π c := by
      rw [show k = (⟨(e' : G) * (e : G)⁻¹, he'e_H⟩ : ↥H)⁻¹ * c from Subtype.ext (by
        simp only [k, c, Subgroup.coe_mul, Subgroup.coe_inv])]
      rw [map_mul, map_inv]
    rw [h1, ← he'e_π, hρe'e]
    group
  let n'' : ↥H := H.normalizerMonoidHom ⟨(e : G)⁻¹, hEN (E.inv_mem e.2)⟩ k
  have hn''_ker : n'' ∈ π.ker :=
    eqCov_conj_mem_kernel hEN π ρ hEq ⟨(e : G)⁻¹, E.inv_mem e.2⟩ hk_ker
  have hdecomp : (x₀ : G) * (e : G) * (x₀ : G)⁻¹ = (e' : G) * (n'' : G) := by
    have hn'' : (n'' : G) = (e : G)⁻¹ * (((e' : G) * (e : G)⁻¹)⁻¹ *
        ((x₀ : G) * (e : G) * (x₀ : G)⁻¹ * (e : G)⁻¹)) * (e : G) := by
      show ((H.normalizerMonoidHom ⟨(e : G)⁻¹, hEN (E.inv_mem e.2)⟩ k : ↥H) : G) = _
      rw [normalizerMonoidHom_coe]
      dsimp only [k, c]
      group
    rw [hn'']
    group
  rw [hdecomp]
  exact Subgroup.mul_mem_sup e'.2 (Subgroup.mem_map.mpr ⟨n'', hn''_ker, rfl⟩)

private theorem eqCov_kernel_map_conj {G : Type} [Group G] {H : Subgroup G} {M : Type}
    [Group M] (π : ↥H →* M) (x : ↥H) :
    (eqCov_kernelSub π).map (MulAut.conj (x : G)).toMonoidHom = eqCov_kernelSub π := by
  calc
    (eqCov_kernelSub π).map (MulAut.conj (x : G)).toMonoidHom
        = ((π.ker).map H.subtype).map (MulAut.conj (x : G)).toMonoidHom := rfl
    _ = (π.ker).map ((MulAut.conj (x : G)).toMonoidHom.comp H.subtype) := by
          rw [Subgroup.map_map]
    _ = (π.ker).map (H.subtype.comp (MulAut.conj x).toMonoidHom) := rfl
    _ = ((π.ker).map (MulAut.conj x).toMonoidHom).map H.subtype := by
          rw [Subgroup.map_map]
    _ = (π.ker).map H.subtype := by
          rw [CFSG.GroupTheory.ThreeTranspositions.map_conj_eq_of_normal
            (MonoidHom.normal_ker π) x]

open scoped Pointwise in
private theorem eqCov_exists_sylow_correction {G : Type} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {E N X : Subgroup G} (hE : IsPGroup p E) (hN : ¬ p ∣ Nat.card N)
    (hEN : E ≤ Subgroup.normalizer (N : Set G)) (hEX : E ≤ Subgroup.normalizer (X : Set G))
    {x₀ : G} (hx₀ : x₀ ∈ X) (hconj : ∀ e ∈ E, x₀ * e * x₀⁻¹ ∈ E ⊔ N) :
    ∃ e₁ ∈ E, ∃ n₁ ∈ N, e₁ * n₁ ∈ X ∧
      (e₁ * n₁)⁻¹ * x₀ ∈ Subgroup.normalizer (E : Set G) := by
  classical
  set P : Subgroup G := E ⊔ N with hP
  set K : Subgroup G := X ⊓ P with hK
  set Q : Subgroup G := K ⊔ E with hQ
  have hEP : E ≤ Subgroup.normalizer (P : Set G) := le_sup_left.trans Subgroup.le_normalizer
  have hEK : E ≤ Subgroup.normalizer (K : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have h1 := Subgroup.mem_normalizer_iff.mp (hEX he) k
    have h2 := Subgroup.mem_normalizer_iff.mp (hEP he) k
    simp only [hK, Subgroup.mem_inf]
    exact ⟨fun hk => ⟨h1.mp hk.1, h2.mp hk.2⟩, fun hk => ⟨h1.mpr hk.1, h2.mpr hk.2⟩⟩
  have hEN_bot : E ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgE, hgN⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨k, hk⟩ := hE ⟨g, hgE⟩
    have hk' : g ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf g ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hgN
    have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hN)
    rw [Subgroup.mem_bot, ← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hset : (P : Set G) = (E : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right E N hEN
  have hcardP : Nat.card P = Nat.card E * Nat.card N := by
    let f : ↥E × ↥N → ↥P := fun en => ⟨(en.1 : G) * en.2, by
      show (en.1 : G) * en.2 ∈ (P : Set G)
      rw [hset]
      exact Set.mul_mem_mul en.1.2 en.2.2⟩
    have hf : Function.Bijective f := by
      constructor
      · rintro ⟨e, n⟩ ⟨e', n'⟩ h
        have h' : (e : G) * n = e' * n' := congrArg Subtype.val h
        have h1 : (e' : G)⁻¹ * e = n' * (n : G)⁻¹ := by
          calc (e' : G)⁻¹ * e = (e' : G)⁻¹ * ((e : G) * n) * (n : G)⁻¹ := by group
            _ = (e' : G)⁻¹ * ((e' : G) * n') * (n : G)⁻¹ := by rw [h']
            _ = n' * (n : G)⁻¹ := by group
        have hmem : (e' : G)⁻¹ * e ∈ E ⊓ N := Subgroup.mem_inf.mpr
          ⟨E.mul_mem (E.inv_mem e'.2) e.2, h1 ▸ N.mul_mem n'.2 (N.inv_mem n.2)⟩
        rw [hEN_bot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
        have hn : (n : G) = n' := by
          rw [← hmem] at h'
          exact mul_left_cancel h'
        exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hn)
      · rintro ⟨g, hg⟩
        have hg' : g ∈ (E : Set G) * (N : Set G) := hset ▸ hg
        obtain ⟨e, he, n, hn, rfl⟩ := hg'
        exact ⟨(⟨e, he⟩, ⟨n, hn⟩), rfl⟩
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have hQP : Q ≤ P := sup_le inf_le_right le_sup_left
  have hEQ : E ≤ Q := le_sup_right
  have hcardQ : Nat.card Q ∣ Nat.card E * Nat.card N :=
    hcardP ▸ Subgroup.card_dvd_of_le hQP
  have hidx : ∀ {F : Subgroup G}, F ≤ Q → Nat.card F = Nat.card E →
      ¬ p ∣ (F.subgroupOf Q).index := by
    intro F hFQ hFcard hdvd
    have h1 : Nat.card (F.subgroupOf Q) * (F.subgroupOf Q).index = Nat.card Q :=
      Subgroup.card_mul_index _
    have h2 : Nat.card (F.subgroupOf Q) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFQ).toEquiv
    rw [h2, hFcard] at h1
    have hpos : 0 < Nat.card E := Nat.card_pos
    have h3 : (F.subgroupOf Q).index ∣ Nat.card N := by
      rw [← h1] at hcardQ
      exact Nat.dvd_of_mul_dvd_mul_left hpos hcardQ
    exact hN (hdvd.trans h3)
  let E₂ : Subgroup G := E.map (MulAut.conj x₀).toMonoidHom
  have hE₂Q : E₂ ≤ Q := by
    rintro _ ⟨e, he, rfl⟩
    change x₀ * e * x₀⁻¹ ∈ Q
    have hX : x₀ * e * x₀⁻¹ * e⁻¹ ∈ X := by
      have h1 : e * x₀⁻¹ * e⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hEX he) x₀⁻¹).mp (X.inv_mem hx₀)
      have h2 := X.mul_mem hx₀ h1
      simpa only [mul_assoc] using h2
    have hPm : x₀ * e * x₀⁻¹ * e⁻¹ ∈ P :=
      P.mul_mem (hconj e he) (P.inv_mem (Subgroup.mem_sup_left he))
    have hKm : x₀ * e * x₀⁻¹ * e⁻¹ ∈ K := Subgroup.mem_inf.mpr ⟨hX, hPm⟩
    have := Q.mul_mem (Subgroup.mem_sup_left hKm) (Subgroup.mem_sup_right he)
    simpa using this
  have hcardE₂ : Nat.card E₂ = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj x₀).injective
  have hpE₁ : IsPGroup p ↥(E.subgroupOf Q) :=
    hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEQ).symm
  have hpE₂ : IsPGroup p ↥(E₂.subgroupOf Q) :=
    (hE.map (MulAut.conj x₀).toMonoidHom).of_equiv (Subgroup.subgroupOfEquivOfLe hE₂Q).symm
  let S₁ : Sylow p Q := hpE₁.toSylow (hidx hEQ rfl)
  let S₂ : Sylow p Q := hpE₂.toSylow (hidx hE₂Q hcardE₂)
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Q S₁ S₂
  have hqmem : ∀ g : ↥Q, g ∈ (S₂ : Subgroup Q) ↔ q⁻¹ * g * q ∈ (S₁ : Subgroup Q) := by
    intro g
    have hq2 : (q • S₁ : Sylow p Q) = S₂ := hq
    have hq' : (S₂ : Subgroup Q) = MulAut.conj q • (S₁ : Subgroup Q) := by
      rw [← hq2]
      rfl
    rw [hq', Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs
    · intro h
      exact ⟨_, h, by simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]⟩
  have hS₁ : (S₁ : Subgroup Q) = E.subgroupOf Q := IsPGroup.toSylow_coe _ _
  have hS₂ : (S₂ : Subgroup Q) = E₂.subgroupOf Q := IsPGroup.toSylow_coe _ _
  have hnorm : (q : G)⁻¹ * x₀ ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hmem2 : x₀ * g * x₀⁻¹ ∈ E₂ := ⟨g, hg, rfl⟩
      let w : ↥Q := ⟨x₀ * g * x₀⁻¹, hE₂Q hmem2⟩
      have hw : w ∈ (S₂ : Subgroup Q) := by
        rw [hS₂, Subgroup.mem_subgroupOf]
        exact hmem2
      have h1 := (hqmem w).mp hw
      rw [hS₁, Subgroup.mem_subgroupOf] at h1
      have h2 : ((q : G)⁻¹ * x₀) * g * ((q : G)⁻¹ * x₀)⁻¹ = ((q⁻¹ * w * q : ↥Q) : G) := by
        simp only [w, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h2]
      exact h1
    · intro hg
      have hqE : (q : G) * (((q : G)⁻¹ * x₀) * g * ((q : G)⁻¹ * x₀)⁻¹) * (q : G)⁻¹ ∈ Q :=
        Q.mul_mem (Q.mul_mem q.2 (hEQ hg)) (Q.inv_mem q.2)
      let w : ↥Q := ⟨_, hqE⟩
      have hw1 : q⁻¹ * w * q ∈ (S₁ : Subgroup Q) := by
        rw [hS₁, Subgroup.mem_subgroupOf]
        have h3 : ((q⁻¹ * w * q : ↥Q) : G) = ((q : G)⁻¹ * x₀) * g * ((q : G)⁻¹ * x₀)⁻¹ := by
          simp only [w, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [h3]
        exact hg
      have hw2 := (hqmem w).mpr hw1
      rw [hS₂, Subgroup.mem_subgroupOf] at hw2
      obtain ⟨e', he', hee'⟩ := hw2
      have h4 : x₀ * e' * x₀⁻¹ = x₀ * g * x₀⁻¹ := by
        have h5 : ((MulAut.conj x₀).toMonoidHom e' : G) = x₀ * e' * x₀⁻¹ := rfl
        rw [← h5, hee']
        simp only [w]
        group
      have h6 : e' = g := by
        have := congrArg (fun z => x₀⁻¹ * z * x₀) h4
        simpa [mul_assoc] using this
      exact h6 ▸ he'
  have hQset : (Q : Set G) = (K : Set G) * (E : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K E hEK
  have hqKE : (q : G) ∈ (K : Set G) * (E : Set G) := hQset ▸ q.2
  obtain ⟨k, hk, e₀, he₀, hke⟩ := hqKE
  have hke' : k * e₀ = (q : G) := hke
  obtain ⟨hkX, hkP⟩ := Subgroup.mem_inf.mp hk
  have hkEN : k ∈ (E : Set G) * (N : Set G) := hset ▸ hkP
  obtain ⟨e₁, he₁, n₁, hn₁, hen⟩ := hkEN
  have hen' : e₁ * n₁ = k := hen
  refine ⟨e₁, he₁, n₁, hn₁, hen' ▸ hkX, ?_⟩
  have h7 : (e₁ * n₁)⁻¹ * x₀ = e₀ * ((q : G)⁻¹ * x₀) := by
    rw [hen', ← hke']
    group
  rw [h7]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer he₀) hnorm


private theorem eqCov_exists_matching {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {M : Type} [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M)
    (ρ : ↥E →* M)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    (hρinv : ∀ e : ↥E, ρ e ∈ π.range → (e : G) ∈ H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker) (hEab : IsElemAbelian 3 E)
    {X : Subgroup ↥H} {Y : Subgroup M} (_hXmap : X.map π = Y)
    (hXnorm : E ≤ Subgroup.normalizer ((X.map H.subtype : Subgroup G) : Set G))
    {y : ↥Y} (hyN : (y : M) ∈ Subgroup.normalizer ((ρ.range : Subgroup M) : Set M))
    {x₀ : ↥H} (hx₀X : x₀ ∈ X) (hx₀π : π x₀ = (y : M)) :
    ∃ (x : ↥H) (_hxX : x ∈ X) (hxN : (x : G) ∈ Subgroup.normalizer (E : Set G)),
      ∀ a : ↥E, ρ ⟨(x : G) * (a : G) * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hxN (a : G)).1 a.2⟩ =
        (y : M) * ρ a * (y : M)⁻¹ := by
  classical
  let Nk : Subgroup G := eqCov_kernelSub π
  let XG : Subgroup G := X.map H.subtype
  have hXGle : XG ≤ H := Subgroup.map_subtype_le X
  have hx₀XG : (x₀ : G) ∈ XG := Subgroup.mem_map.mpr ⟨x₀, hx₀X, rfl⟩
  have hN3 : ¬ 3 ∣ Nat.card Nk := by
    dsimp only [Nk, eqCov_kernelSub]
    rwa [Subgroup.card_map_of_injective H.subtype_injective]
  have hENnorm : E ≤ Subgroup.normalizer (Nk : Set G) :=
    eqCov_kernel_normalized_by_E hEN π ρ hEq
  have hE3 : IsPGroup 3 E := fun x =>
    ⟨1, Subtype.ext (by simpa using hEab.2 (x : G) x.2)⟩
  have hconj : ∀ e ∈ E, (x₀ : G) * e * (x₀ : G)⁻¹ ∈ E ⊔ Nk := by
    intro e he
    exact eqCov_conj_mem_sup hEN π ρ hρπ hEq hρinv hyN hx₀π ⟨e, he⟩
  obtain ⟨e₁, he₁, n₁, hn₁, hkX, hnorm⟩ :=
    eqCov_exists_sylow_correction (p := 3) hE3 hN3 hENnorm hXnorm hx₀XG hconj
  obtain ⟨k', hk'X, hk'G⟩ := Subgroup.mem_map.mp hkX
  let x : ↥H := k'⁻¹ * x₀
  have hxX : x ∈ X := X.mul_mem (X.inv_mem hk'X) hx₀X
  have hn₁H : (n₁ : G) ∈ H := eqCov_kernelSub_le π hn₁
  have hk'G' : (k' : G) = e₁ * n₁ := hk'G
  have he₁H : (e₁ : G) ∈ H := by
    have h1 : (e₁ : G) = (k' : G) * (n₁ : G)⁻¹ := by
      rw [hk'G']; group
    rw [h1]
    exact H.mul_mem k'.2 (H.inv_mem hn₁H)
  have hπn₁ : π ⟨n₁, hn₁H⟩ = 1 := by
    obtain ⟨k, hk, hkG⟩ := Subgroup.mem_map.mp hn₁
    have h1 : (⟨n₁, hn₁H⟩ : ↥H) = k := Subtype.ext hkG.symm
    rw [h1]
    exact MonoidHom.mem_ker.mp hk
  have hπk' : π k' = ρ ⟨e₁, he₁⟩ := by
    have h1 : k' = (⟨e₁, he₁H⟩ : ↥H) * ⟨n₁, hn₁H⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hk'G']
    rw [h1, map_mul, hπn₁, mul_one, hρπ ⟨e₁, he₁⟩ he₁H]
  have hπx : π x = (ρ ⟨e₁, he₁⟩)⁻¹ * (y : M) := by
    calc
      π x = π (k'⁻¹ * x₀) := rfl
      _ = (π k')⁻¹ * π x₀ := by rw [map_mul, map_inv]
      _ = (ρ ⟨e₁, he₁⟩)⁻¹ * (y : M) := by rw [hπk', hx₀π]
  have hxN : (x : G) ∈ Subgroup.normalizer (E : Set G) := by
    show ((k' : G)⁻¹ * (x₀ : G)) ∈ Subgroup.normalizer (E : Set G)
    rw [hk'G']
    exact hnorm
  refine ⟨x, hxX, hxN, fun a => ?_⟩
  have hconj' := eqCov_rho_conj hEN π ρ hρπ hEq hxN a
  have hcommE : ∀ u v : ↥E, u * v = v * u := fun u v => hEab.1.is_comm.comm u v
  have hcommRange : ∀ u v : ↥ρ.range, (u : M) * (v : M) = (v : M) * (u : M) := by
    intro u v
    obtain ⟨u', hu'⟩ := MonoidHom.mem_range.mp u.2
    obtain ⟨v', hv'⟩ := MonoidHom.mem_range.mp v.2
    rw [← hu', ← hv']
    change ρ u' * ρ v' = ρ v' * ρ u'
    rw [← map_mul, ← map_mul, hcommE v' u']
  have hb : ∃ b : ↥E, ρ b = (y : M) * ρ a * (y : M)⁻¹ := by
    have hmem : (y : M) * ρ a * (y : M)⁻¹ ∈ ρ.range :=
      (Subgroup.mem_normalizer_iff.mp hyN (ρ a)).1 ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hb
  set A : M := (y : M) * ρ a * (y : M)⁻¹ with hA
  have hcomm : (ρ ⟨e₁, he₁⟩) * A = A * (ρ ⟨e₁, he₁⟩) :=
    hcommRange ⟨ρ ⟨e₁, he₁⟩, ⟨⟨e₁, he₁⟩, rfl⟩⟩ ⟨A, ⟨b, hb⟩⟩
  have hcomm_inv : (ρ ⟨e₁, he₁⟩)⁻¹ * A = A * (ρ ⟨e₁, he₁⟩)⁻¹ := by
    have h1 : A = (ρ ⟨e₁, he₁⟩)⁻¹ * A * ρ ⟨e₁, he₁⟩ := by
      calc
        A = (ρ ⟨e₁, he₁⟩)⁻¹ * ((ρ ⟨e₁, he₁⟩) * A) := by group
        _ = (ρ ⟨e₁, he₁⟩)⁻¹ * (A * ρ ⟨e₁, he₁⟩) := by rw [hcomm]
        _ = (ρ ⟨e₁, he₁⟩)⁻¹ * A * ρ ⟨e₁, he₁⟩ := by group
    calc
      (ρ ⟨e₁, he₁⟩)⁻¹ * A
          = (ρ ⟨e₁, he₁⟩)⁻¹ * A * ρ ⟨e₁, he₁⟩ * (ρ ⟨e₁, he₁⟩)⁻¹ := by group
      _ = A * (ρ ⟨e₁, he₁⟩)⁻¹ := by rw [← h1]
  rw [hconj', hπx]
  calc
    (ρ ⟨e₁, he₁⟩)⁻¹ * (y : M) * ρ a * ((ρ ⟨e₁, he₁⟩)⁻¹ * (y : M))⁻¹
        = (ρ ⟨e₁, he₁⟩)⁻¹ * A * ρ ⟨e₁, he₁⟩ := by rw [hA]; group
    _ = A := by rw [hcomm_inv]; group
    _ = (y : M) * ρ a * (y : M)⁻¹ := rfl

private theorem eqCov_congr_ggConjAut {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M) (ρ : ↥E →* M)
    (hρ : Function.Injective ρ)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    {x : ↥H} (hxN : (x : G) ∈ Subgroup.normalizer (E : Set G))
    (hπxN : π x ∈ Subgroup.normalizer ((ρ.range : Subgroup M) : Set M)) :
    MulAut.congr (eqCov_rho_equiv ρ hρ) (ggConjAut E hxN) = ggConjAut ρ.range hπxN := by
  ext b
  obtain ⟨a, rfl⟩ := (eqCov_rho_equiv ρ hρ).surjective b
  rw [eqCov_mulAut_congr_apply]
  simp only [MulEquiv.symm_apply_apply]
  rw [show ((eqCov_rho_equiv ρ hρ) ((ggConjAut E hxN) a) : M) =
      ρ ((ggConjAut E hxN) a) from rfl]
  rw [show (ggConjAut E hxN) a =
      (⟨(x : G) * (a : G) * (x : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hxN (a : G)).1 a.2⟩ : ↥E) from Subtype.ext rfl]
  rw [show ((ggConjAut ρ.range hπxN) ((eqCov_rho_equiv ρ hρ) a) : M) =
      π x * ρ a * (π x)⁻¹ from by
    rw [ggConjAut_apply, eqCov_rho_equiv_apply]]
  exact eqCov_rho_conj hEN π ρ hρπ hEq hxN a

private theorem eqCov_automizer_eq {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {M : Type} [Group M] {R : RawFrameData} (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (π : ↥H →* M) (ρ : ↥E →* M) (hρ : Function.Injective ρ)
    (hker3 : ¬ 3 ∣ Nat.card π.ker) (hEab : IsElemAbelian 3 E)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    (hρπ : ∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩)
    (hρinv : ∀ e : ↥E, ρ e ∈ π.range → (e : G) ∈ H)
    (mf' : ModelFrame π.range ρ.range R) {X : Subgroup ↥H} {Y : Subgroup M}
    (hXmap : X.map π = Y)
    (hXnorm : E ≤ Subgroup.normalizer ((X.map H.subtype : Subgroup G) : Set G))
    (_hYle : Y ≤ π.range) :
    (ggAutomizer (X.map H.subtype : Subgroup G) E).map (ggLin (p := 3) (eqCov_coord ρ hρ mf')) =
      (ggAutomizer Y ρ.range).map (ggLin (p := 3) mf'.coord) := by
  classical
  apply le_antisymm
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨g, hgX, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    obtain ⟨x, hxX, hxg⟩ := Subgroup.mem_map.mp hgX
    rw [← hxg] at hgN hφg
    have hπxY : π x ∈ Y := by
      rw [← hXmap]
      exact Subgroup.mem_map_of_mem π hxX
    have hπxN : π x ∈ Subgroup.normalizer ((ρ.range : Subgroup M) : Set M) :=
      eqCov_map_mem_normalizer hEN π ρ hρπ hEq hgN
    have hcongr : MulAut.congr (eqCov_rho_equiv ρ hρ) φ = ggConjAut ρ.range hπxN := by
      ext b
      obtain ⟨a, rfl⟩ := (eqCov_rho_equiv ρ hρ).surjective b
      rw [eqCov_mulAut_congr_apply]
      simp only [MulEquiv.symm_apply_apply]
      rw [show ((eqCov_rho_equiv ρ hρ) (φ a) : M) = ρ (φ a) from rfl]
      rw [show ((ggConjAut ρ.range hπxN) ((eqCov_rho_equiv ρ hρ) a) : M) =
          π x * ρ a * (π x)⁻¹ from by
        rw [ggConjAut_apply, eqCov_rho_equiv_apply]]
      have hφa : φ a = (⟨(x : G) * (a : G) * (x : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp hgN (a : G)).1 a.2⟩ : ↥E) := by
        apply Subtype.ext
        rw [hφg a]
        rfl
      rw [hφa]
      exact eqCov_rho_conj hEN π ρ hρπ hEq hgN a
    refine Subgroup.mem_map.mpr ⟨ggConjAut ρ.range hπxN,
      mem_ggAutomizer_iff.mpr ⟨π x, hπxY, hπxN, fun b => by rw [ggConjAut_apply]⟩, ?_⟩
    rw [eqCov_ggLin_coord, hcongr]
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨y, hyY, hyN, hψg⟩ := mem_ggAutomizer_iff.mp hψ
    have hyMap : (y : M) ∈ X.map π := by rw [hXmap]; exact hyY
    obtain ⟨x₀, hx₀X, hx₀π⟩ := Subgroup.mem_map.mp hyMap
    obtain ⟨x, hxX, hxN, hact⟩ :=
      eqCov_exists_matching (Y := Y) (y := ⟨y, hyY⟩) hEN π ρ hρπ hEq hρinv hker3 hEab hXmap hXnorm
        hyN hx₀X hx₀π
    have hcongr : MulAut.congr (eqCov_rho_equiv ρ hρ) (ggConjAut E hxN) = ψ := by
      ext b
      obtain ⟨a, rfl⟩ := (eqCov_rho_equiv ρ hρ).surjective b
      rw [eqCov_mulAut_congr_apply]
      simp only [MulEquiv.symm_apply_apply]
      rw [show ((eqCov_rho_equiv ρ hρ) ((ggConjAut E hxN) a) : M) =
          ρ ((ggConjAut E hxN) a) from rfl]
      rw [show (ggConjAut E hxN) a =
          (⟨(x : G) * (a : G) * (x : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp hxN (a : G)).1 a.2⟩ : ↥E) from Subtype.ext rfl]
      rw [hact a]
      rw [hψg ((eqCov_rho_equiv ρ hρ) a), eqCov_rho_equiv_apply]
    refine Subgroup.mem_map.mpr ⟨ggConjAut E hxN,
      mem_ggAutomizer_iff.mpr ⟨(x : G), Subgroup.mem_map.mpr ⟨x, hxX, rfl⟩, hxN,
        fun b => by rw [ggConjAut_apply]⟩, ?_⟩
    rw [eqCov_ggLin_coord, hcongr]

private theorem eqCov_component_normalized {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {M : Type} [Group M] (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M)
    (ρ : ↥E →* M)
    (hEq : ∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹)
    {Y : Subgroup M} (hmfN : ∀ e : ↥E, ρ e ∈ Subgroup.normalizer (Y : Set M)) :
    E ≤ Subgroup.normalizer
      (((⁅Y.comap π, Y.comap π⁆).map H.subtype : Subgroup G) : Set G) := by
  classical
  let P : Subgroup G := (Y.comap π).map H.subtype
  have hPmap_le : ∀ e ∈ E, P.map (MulAut.conj e).toMonoidHom ≤ P := by
    intro e he
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨q0, hq0, rfl⟩ := Subgroup.mem_map.mp hq
    rw [Subgroup.mem_comap] at hq0
    refine Subgroup.mem_map.mpr ⟨H.normalizerMonoidHom ⟨e, hEN he⟩ q0, ?_, rfl⟩
    change π (ggGamma H hEN ⟨e, he⟩ q0) ∈ Y
    rw [hEq ⟨e, he⟩ q0]
    exact (Subgroup.mem_normalizer_iff.mp (hmfN ⟨e, he⟩) (π q0)).1 hq0
  have hPnorm : E ≤ Subgroup.normalizer (P : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge (hPmap_le e he)
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj e).toMonoidHom) (MulAut.conj e).injective]
  have hcomm := CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer E P P hPnorm hPnorm
  rw [Subgroup.map_commutator]
  exact hcomm
theorem modelFrameOfEquivCover_holds : ModelFrameOfEquivCover := by
  intro G _ _ H E M _ R hEN π ρ hker hker3 _hcomm hEab hρ hEq hρπ hρinv mf hmfN
  classical
  refine ⟨?_⟩
  refine
    { coord := eqCov_coord ρ hρ mf
      component := fun c => ((⁅(mf.component c).comap π, (mf.component c).comap π⁆).map H.subtype :
        Subgroup G)
      component_le := fun c _hc => Subgroup.map_subtype_le _
      marked := fun c hc => eqCov_marked π ρ hker mf c hc
      occurs_iff := eqCov_occurs_iff hEN π ρ hρ hker hker3 hEab hEq mf
      cent_eq := fun c hc => eqCov_cent_eq hEN π ρ hρ hker hker3 hEq mf c hc
      inside_eq := fun c hc => eqCov_inside_eq hEN π ρ hρ hker hker3 hEab hρπ hρinv mf c hc
      normalizer_eq := fun c hc => ?_
      ambientNormalizer_eq := ?_ }
  · have hYle : mf.component c ≤ π.range := mf.component_le c hc
    have hYperf : ⁅mf.component c, mf.component c⁆ = mf.component c :=
      Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (mf.marked c hc).1)
    have hXmap : (⁅(mf.component c).comap π, (mf.component c).comap π⁆).map π =
        mf.component c :=
      (eqCov_derived_comap_perfect π hker hYle hYperf).1
    have hXnorm : E ≤ Subgroup.normalizer
        (((⁅(mf.component c).comap π, (mf.component c).comap π⁆).map H.subtype :
          Subgroup G) : Set G) :=
      eqCov_component_normalized hEN π ρ hEq (fun e => hmfN c hc ⟨e, rfl⟩)
    have hauto := eqCov_automizer_eq hEN π ρ hρ hker3 hEab hEq hρπ hρinv mf
      hXmap hXnorm hYle
    rw [hauto, mf.normalizer_eq c hc]
  · have hXnormH :
        E ≤ Subgroup.normalizer (((⊤ : Subgroup ↥H).map H.subtype : Subgroup G) : Set G) := by
      simpa only [Subgroup.map_top, Subgroup.range_subtype] using hEN
    have hauto := eqCov_automizer_eq hEN π ρ hρ hker3 hEab hEq hρπ hρinv mf
      (X := ⊤) (Y := π.range) (Subgroup.map_top π) hXnormH le_rfl
    simp only [Subgroup.map_top, Subgroup.range_subtype] at hauto
    rw [hauto, mf.ambientNormalizer_eq]

end CFSG.StandardType.GGQ2Frame.ExcPlacement
