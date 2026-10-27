module

public import CFSG.Quasithin.Vol2.Ch3E213MG41S2
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLaughlin
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Ch3E213M.G41.Refl

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OutcomeLocal (tv tv_apply IsF2Transvection
  isF2Transvection_iff mclaughlin_transvection_groups_F2 sumZero sumZeroRep onesLine heartRep)

local notation "V₀" => Fin 4 → ZMod 2
local notation "GL₀" => LinearMap.GeneralLinearGroup (ZMod 2) (Fin 4 → ZMod 2)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)} {b : Fin 4 → Fin 4 → k}

@[expose] noncomputable def tau (b : Fin 4 → Fin 4 → k) (r : Fin 4 → k) : GL₀ :=
  tv (f0 b (pre b r)) (pre b r) (f0_self (pre b r))

theorem tau_apply (r : Fin 4 → k) (x : V₀) :
    ((tau b r : GL₀) : V₀ →ₗ[ZMod 2] V₀) x = x + f0 b (pre b r) x • pre b r := by
  rw [tau, tv_apply]

theorem emb_tau (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    {r : Fin 4 → k} (hr : r ∈ normC G₀) (x : V₀) :
    emb b (((tau b r : GL₀) : V₀ →ₗ[ZMod 2] V₀) x) = natAct (trv r 1) (emb b x) := by
  rw [tau_apply, emb_add, emb_smul, act_trv, one_mul, f0_symm]
  conv_rhs => rw [← emb_pre hF hb hli hr]
  rw [bil_emb hF hb]

@[expose] noncomputable def grp (G₀ : Subgroup (antiSp k)) (b : Fin 4 → Fin 4 → k) :
    Subgroup GL₀ :=
  Subgroup.closure {h | ∃ r ∈ normC G₀, h = tau b r}

theorem tau_mem_grp {r : Fin 4 → k} (hr : r ∈ normC G₀) : tau b r ∈ grp G₀ b :=
  Subgroup.subset_closure ⟨r, hr, rfl⟩

theorem isF2Transvection_tau (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hli : LinearIndependent k b) {r : Fin 4 → k} (hr : r ∈ normC G₀) :
    IsF2Transvection (tau b r) := by
  refine (isF2Transvection_iff _).mpr ⟨_, _, _, fun h => ?_, pre_ne_zero hF hb hli hr, rfl⟩
  exact pre_ne_zero hF hb hli hr (eq_zero_of_f0 hF hb hli fun y => LinearMap.congr_fun h y)

theorem grp_irr [Finite k] (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)))
    (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b)
    (W : Submodule (ZMod 2) V₀)
    (hW : ∀ g ∈ grp G₀ b, ∀ w ∈ W, ((g : GL₀) : V₀ →ₗ[ZMod 2] V₀) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hD : DInv G₀ (Submodule.span k (emb b '' W)) := by
    intro d hd w hw
    obtain ⟨r, hr, rfl⟩ := exists_normC_eq hd
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨w₀, hw₀, rfl⟩ := hw
      rw [← emb_tau hF hb hli hr]
      exact Submodule.subset_span ⟨_, hW _ (tau_mem_grp hr) _ hw₀, rfl⟩
    | zero =>
      rw [act_zero]
      exact Submodule.zero_mem _
    | add a c _ _ ha hc =>
      rw [act_add]
      exact Submodule.add_mem _ ha hc
    | smul a c _ hc =>
      rw [act_smul]
      exact Submodule.smul_mem _ _ hc
  rcases dInv_of_irr_closure hirr _ hD with h | h
  · refine Or.inl (eq_bot_iff.mpr fun w hw => ?_)
    have hw' : emb b w ∈ Submodule.span k (emb b '' W) := Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot, ← emb_zero (b := b)] at hw'
    exact (Submodule.mem_bot _).mpr (emb_injective hli hw')
  · refine Or.inr (by_contra fun hne => ?_)
    obtain ⟨ψ, hψ0, hψW⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
    let B := Module.Basis.mk hli (le_of_eq (span_range_eq_top hli).symm)
    let Ψ : (Fin 4 → k) →ₗ[k] k :=
      B.constr k fun j => (c2 (ψ fun l => if j = l then 1 else 0) : k)
    have hΨ : ∀ x, Ψ (emb b x) = (c2 (ψ x) : k) := by
      intro x
      rw [LinearMap.pi_apply_eq_sum_univ ψ x, map_sum, emb, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, smul_eq_mul, map_mul]
      congr 1
      have hBj : B j = b j := Module.Basis.mk_apply _ _ j
      rw [← hBj]
      exact B.constr_basis k _ j
    have hΨW : ∀ y ∈ Submodule.span k (emb b '' W), Ψ y = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨w, hw, rfl⟩ := hy
        rw [hΨ, LinearMap.mem_ker.mp (hψW hw), map_zero]
      | zero => exact map_zero Ψ
      | add a c _ _ ha hc => rw [map_add, ha, hc, add_zero]
      | smul a c _ hc => rw [map_smul, hc, smul_zero]
    refine hψ0 (LinearMap.ext fun x => c2_injective (k := k) ?_)
    rw [← hΨ, hΨW _ (by rw [h]; exact Submodule.mem_top), LinearMap.zero_apply, map_zero]

@[expose] def liftSub (G₀ : Subgroup (antiSp k)) (b : Fin 4 → Fin 4 → k) : Subgroup GL₀ where
  carrier := {h | ∃ g ∈ G₀, ∀ x, natAct g (emb b x) = emb b (((h : GL₀) : V₀ →ₗ[ZMod 2] V₀) x)}
  one_mem' := ⟨1, G₀.one_mem, fun x => by rw [natAct_one]; rfl⟩
  mul_mem' := by
    rintro h h' ⟨g, hg, hgx⟩ ⟨g', hg', hgx'⟩
    exact ⟨g * g', G₀.mul_mem hg hg', fun x => by rw [natAct_mul, hgx', hgx]; rfl⟩
  inv_mem' := by
    rintro h ⟨g, hg, hgx⟩
    refine ⟨g⁻¹, G₀.inv_mem hg, fun x => act_injective g ?_⟩
    rw [act_act_inv, hgx]
    change emb b x = emb b (((h * h⁻¹ : GL₀) : V₀ →ₗ[ZMod 2] V₀) x)
    rw [mul_inv_cancel]
    rfl

theorem grp_le_liftSub (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hli : LinearIndependent k b) : grp G₀ b ≤ liftSub G₀ b :=
  (Subgroup.closure_le _).mpr fun _ ⟨r, hr, he⟩ =>
    ⟨trv r 1, hr.2, fun x => by rw [he, emb_tau hF hb hli hr]⟩

theorem mem_normC_of_lift [Finite k] (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀)
    (hli : LinearIndependent k b) {h : GL₀} (hh : h ∈ liftSub G₀ b) (h1 : h ≠ 1) {v : V₀}
    (hv : v ≠ 0) (hv' : ∀ x, ∃ c : ZMod 2, ((h : GL₀) : V₀ →ₗ[ZMod 2] V₀) x = x + c • v) :
    emb b v ∈ normC G₀ := by
  obtain ⟨g, hg, hgx⟩ := hh
  have hev : emb b v ≠ 0 := fun h0 => hv (emb_injective hli (by rw [h0, emb_zero]))
  have hcomm : ∀ y, natAct g y - y ∈ Submodule.span k {emb b v} := by
    intro y
    have hy : y ∈ Submodule.span k (Set.range b) := by
      rw [span_range_eq_top hli]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      obtain ⟨c, hc⟩ := hv' (Pi.single j 1)
      rw [← emb_single (b := b) j, hgx, hc, emb_add, emb_smul, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    | zero =>
      rw [act_zero, sub_zero]
      exact Submodule.zero_mem _
    | add a c _ _ ha hc =>
      rw [act_add, add_sub_add_comm]
      exact Submodule.add_mem _ ha hc
    | smul a c _ hc =>
      rw [act_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hc
  obtain ⟨x₀, hx₀⟩ : ∃ x, ((h : GL₀) : V₀ →ₗ[ZMod 2] V₀) x ≠ x := by
    by_contra hall
    push Not at hall
    exact h1 (Units.ext (LinearMap.ext hall))
  have hg1 : natAct g (emb b x₀) - emb b x₀ ≠ 0 := by
    rw [hgx, sub_ne_zero]
    exact fun he => hx₀ (emb_injective hli he)
  have hle : commSpace g ≤ Submodule.span k {emb b v} := by
    rintro _ ⟨y, rfl⟩
    rw [toLin'_sub_one_apply]
    exact hcomm y
  have hgt : IsTransvection g := by
    refine ⟨fun h' => hg1 (by rw [h', natAct_one, sub_self]), ?_⟩
    have hne : commSpace g ≠ ⊥ := by
      intro h0
      apply hg1
      have hmem : natAct g (emb b x₀) - emb b x₀ ∈ commSpace g := by
        rw [← toLin'_sub_one_apply]
        exact LinearMap.mem_range_self _ _
      rwa [h0, Submodule.mem_bot] at hmem
    have hle1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hev] at hle1
    have h0 : Module.finrank k (commSpace g) ≠ 0 := by
      rwa [Ne, Submodule.finrank_eq_zero]
    omega
  obtain ⟨r, hr, rfl⟩ := exists_normC_eq ⟨hg, hgt⟩
  have hrv : r ∈ Submodule.span k {emb b v} := by
    apply hle
    rw [commSpace_trv hr.1 one_ne_zero]
    exact Submodule.mem_span_singleton_self r
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hrv
  obtain ⟨x₁, hx₁⟩ := exists_emb_eq hF hb hli hr
  have hcoord : ∀ j, μ * c2 (v j) = c2 (x₁ j) := by
    have h0 : ∑ j, (μ * c2 (v j) - c2 (x₁ j)) • b j = 0 := by
      rw [show (∑ j, (μ * c2 (v j) - c2 (x₁ j)) • b j) = μ • emb b v - emb b x₁ by
        simp only [emb, Finset.smul_sum, smul_smul, sub_smul, Finset.sum_sub_distrib]]
      rw [hμ, hx₁, sub_self]
    exact fun j => sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 j)
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  have hμ1 : μ = 1 := by
    have hcj := hcoord j
    rw [(zmod2_cases (v j)).resolve_left hj, map_one, mul_one] at hcj
    rcases c2_eq_zero_or_one (k := k) (x₁ j) with h0 | h0
    · exact absurd (by rw [← hμ, hcj, h0, zero_smul]) hr.1
    · rw [hcj, h0]
  rw [← hμ, hμ1, one_smul] at hr
  exact hr

theorem mcl_outcomes [Finite k] (hirr : IsIrreducibleSp4 (Subgroup.closure (transvSet G₀)))
    (hF : F2Vals G₀) (hb : ∀ j, b j ∈ normC G₀) (hli : LinearIndependent k b) :
    grp G₀ b = ⊤ ∨
    (∃ f : LinearMap.BilinForm (ZMod 2) V₀, f.Nondegenerate ∧ f.IsAlt ∧
      grp G₀ b = CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup f) ∨
    (∃ Q : QuadraticForm (ZMod 2) V₀, LinearMap.Nondegenerate (QuadraticMap.polarBilin Q) ∧
      grp G₀ b = (TauCeti.QuadraticMap.orthogonalGroup Q).comap
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V₀).toMonoidHom) ∨
    (∃ β : V₀ ≃ₗ[ZMod 2] sumZero 5, (grp G₀ b).map
      (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = (sumZeroRep 5).range) ∨
    (∃ β : V₀ ≃ₗ[ZMod 2] sumZero 6 ⧸ onesLine 6, (grp G₀ b).map
      (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = (heartRep 6).range) := by
  have hgen : ∃ S, (∀ t ∈ S, IsF2Transvection t) ∧ grp G₀ b = Subgroup.closure S :=
    ⟨{h | ∃ r ∈ normC G₀, h = tau b r}, fun _ ⟨r, hr, he⟩ => he ▸ isF2Transvection_tau hF hb hli hr,
      rfl⟩
  have hn : Module.finrank (ZMod 2) V₀ = 4 := Module.finrank_fin_fun _
  have h := mclaughlin_transvection_groups_F2 (by rw [hn]; norm_num) (grp G₀ b) hgen
    (grp_irr hirr hF hb hli)
  rw [hn] at h
  rcases h with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end CFSG.Quasithin.Ch3E213M.G41.Refl
