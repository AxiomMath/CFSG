module

public import CFSG.LocalAnalysis.StandardType.GGQTwoU5Cor94
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Models
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.Models.Blueprint
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU52
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCenter
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSUOuter
public import CFSG.Models.Transport

public section

namespace CFSG.StandardType.QTwo.U5

open Subgroup CFSG.Open CFSG.Models CFSG.StandardType
open CFSG.GGQ2Prime (le_twoLocalPrimeRank U52OrderThreeAutInner)

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_sup {Bs L K : Subgroup G}
    (hL : Bs ≤ normalizer (L : Set G)) (hK : Bs ≤ normalizer (K : Set G)) :
    Bs ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) :=
  (le_inf hL hK).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup L K)

theorem le_normalizer_finset_sup {Bs : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (h : ∀ K ∈ 𝒦, Bs ≤ normalizer (K : Set G)) :
    Bs ≤ normalizer ((𝒦.sup (fun K => K) : Subgroup G) : Set G) := by
  classical
  induction 𝒦 using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      intro b _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
  | insert K s hKs ih =>
      rw [Finset.sup_insert]
      exact le_normalizer_sup (h K (Finset.mem_insert_self K s))
        (ih (fun K' hK' => h K' (Finset.mem_insert_of_mem hK')))

end CFSG.StandardType.QTwo.U5

namespace CFSG.StandardType.QTwo.U5

open Subgroup CFSG.Open CFSG.Models
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.GGQ2Prime (U52OrderThreeAutInner exists_noncomm_of_simple center_eq_bot_of_noncomm model_SU
  u52_finite u52_center u52OrderThreeAutInner)

section Generic

variable {M : Type} [Group M]

theorem conj_injective_of_center (hZ : center M = ⊥) :
    Function.Injective (MulAut.conj : M →* MulAut M) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : a ∈ center M := by
    rw [mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut M => φ y) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * a = (a * y * a⁻¹) * a := by rw [this]
      _ = a * y := by group
  rwa [hZ, mem_bot] at hc

theorem centralizer_inner_eq_bot (hZ : center M = ⊥) :
    centralizer ((inner M : Subgroup (MulAut M)) : Set (MulAut M)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [mem_bot]
  ext g
  rw [MulAut.one_apply]
  have hc := mem_centralizer_iff.1 hα (MulAut.conj g) ⟨g, rfl⟩
  have h1 : ∀ z, α g * z * (α g)⁻¹ = g * z * g⁻¹ := by
    intro z
    have := congrArg (fun φ : MulAut M => φ (α.symm z)) hc
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hcen : g⁻¹ * α g ∈ center M := by
    rw [mem_center_iff]
    intro z
    have := h1 z
    calc z * (g⁻¹ * α g) = g⁻¹ * (g * z * g⁻¹) * α g := by group
      _ = g⁻¹ * (α g * z * (α g)⁻¹) * α g := by rw [this]
      _ = g⁻¹ * α g * z := by group
  rw [hZ, mem_bot] at hcen
  calc α g = g * (g⁻¹ * α g) := by group
    _ = g := by rw [hcen, mul_one]

@[expose] noncomputable def innerEquiv (hZ : center M = ⊥) : M ≃* inner M :=
  MonoidHom.ofInjective (conj_injective_of_center hZ)

theorem exists_pair_of_elemAbelian {E : Subgroup M} (hE : IsElemAbelian 3 E)
    (hc : 9 ≤ Nat.card E) :
    ∃ x y : M, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ y ∉ zpowers x := by
  obtain ⟨hcomm, h3⟩ := hE
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hx : ∃ x ∈ E, x ≠ 1 := by
    by_contra h
    push Not at h
    have : E = ⊥ := (eq_bot_iff_forall E).2 h
    rw [this, card_bot] at hc
    omega
  obtain ⟨x, hxE, hx1⟩ := hx
  have hy : ∃ y ∈ E, y ∉ zpowers x := by
    by_contra h
    push Not at h
    have hfo : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, h3 x hxE⟩
    haveI : Finite (zpowers x) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact hfo.orderOf_pos.ne')
    have hle := card_le_of_le (G := M) (H := E) (K := zpowers x) h
    rw [Nat.card_zpowers] at hle
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (h3 x hxE))
    omega
  obtain ⟨y, hyE, hyx⟩ := hy
  refine ⟨x, y, h3 x hxE, h3 y hyE, ?_, hx1, hyx⟩
  have := hcomm.is_comm.comm ⟨x, hxE⟩ ⟨y, hyE⟩
  simpa using congrArg Subtype.val this

theorem pair_of_equiv {R : Type} [Group R] (e : R ≃* M)
    (h : ∃ x y : R, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ y ∉ zpowers x) :
    ∃ x y : M, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ y ∉ zpowers x := by
  obtain ⟨x, y, hx, hy, hxy, hx1, hyx⟩ := h
  refine ⟨e x, e y, by rw [← map_pow, hx, map_one], by rw [← map_pow, hy, map_one],
    by rw [← map_mul, ← map_mul, hxy], fun h => hx1 (by simpa using h), ?_⟩
  rintro ⟨k, hk⟩
  exact hyx ⟨k, e.injective (by simpa using hk)⟩

end Generic

theorem u52MultiplierTrivial :
    U52MultiplierTrivial := by
  intro E _ _ hperf hL
  have hmod := hL.statedClassicalModel_of_ne_zero (by norm_num)
  haveI hs := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hmod
  have hQ : CFSG.IsQuasisimple E := ⟨Group.isPerfect_def.mpr hperf, hs,
    exists_noncomm_of_simple Nat.prime_two (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)⟩
  rw [CFSG.OddStandard.SmallF3.HypA2Leaves.a2l_center_eq_bot_psu52 hQ
    (CFSG.Models.LieModel.toBlueprint (by decide) hL), card_bot]

theorem u52NoncyclicPair : U52NoncyclicPair := by
  intro K _ _ hK
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel (model_SU K 5 (by norm_num) hK)
  obtain ⟨E, hE, hc⟩ := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.exists_e81_projSU_five_two
  exact pair_of_equiv e.symm (exists_pair_of_elemAbelian hE (by omega))

theorem u52AutRankInput : U52AutRankInput := by
  intro K _ _ hK E P hE h81 hP hEP
  haveI := u52_finite K hK
  have hZ := u52_center K hK
  have hmod : StatedClassicalModel (inner (StatedProj (StatedSU 5 (2 ^ 1) K))) .PSU 5 2 1 :=
    CFSG.StandardType.PRankBounds.statedClassicalModel_of_mulEquiv_psu (innerEquiv hZ).symm
      (model_SU K 5 (by norm_num) hK)
  by_contra hP1
  have hN := normalizer_eq_top (inner (StatedProj (StatedSU 5 (2 ^ 1) K)))
  exact CFSG.StandardType.PRankBounds.not_twoLocalRankFour_of_psu5
    CFSG.StandardType.ggUFiveTwoLocalInnerInput_holds
    CFSG.StandardType.ggUFiveTwoOuterCentInput_holds
    (centralizer_inner_eq_bot hZ) hmod
    ⟨E, P, fun a _ => by rw [hN]; trivial, hE, h81, fun a _ => by rw [hN]; trivial, hP1, hP, hEP⟩

end CFSG.StandardType.QTwo.U5

namespace CFSG.StandardType.QTwo.U5

open Subgroup CFSG.Open CFSG.Models CFSG.StandardType
open CFSG.GGQ2Prime (u52OrderThreeAutInner)

theorem cor_9_4_closed
    {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs) (h5 : Nat.card Bs = 3 ^ 5)
    (hL : LieModel (L ⧸ center L) .PSU 5 2 1) (G₁ : Subgroup G)
    (hG₁ : Bs ≤ normalizer (G₁ : Set G)) : Odd (Nat.card (center G₁)) :=
  cor_9_4 u52OrderThreeAutInner u52MultiplierTrivial u52NoncyclicPair u52AutRankInput
    hG hBs h5 hL G₁ hG₁

end CFSG.StandardType.QTwo.U5

end
