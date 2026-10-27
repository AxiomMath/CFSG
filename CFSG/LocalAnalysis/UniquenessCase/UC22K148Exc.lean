module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiNormalizer
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bFinal
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF Module
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open Matrix

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

namespace ExcAux

theorem isQuasisimple_of_isComponentOf {L : Subgroup G} (hL : IsComponentOf L ⊤) :
    CFSG.IsQuasisimple ↥L :=
  ((CFSG.isComponent_iff_open L).2 hL).1

theorem cq_equiv {X H : Type} [Group X] [Group H] (hXq : CFSG.IsQuasisimple X)
    (hq : CFSG.IsQuasisimple H) (ψ : X →* H) (hψ : Function.Surjective ψ) :
    Nonempty ((H ⧸ Subgroup.center H) ≃* (X ⧸ Subgroup.center X)) := by
  have hφ : ∃ k, ψ k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨k, rfl⟩ := hψ x
    obtain ⟨l, rfl⟩ := hψ y
    exact hab (by rw [hcon k, hcon l])
  exact ⟨(CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hXq hψ
    (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hXq hφ)).symm⟩

theorem center_eq_bot {X : Type} [Group X] [IsSimpleGroup X] (hXq : CFSG.IsQuasisimple X) :
    Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hXq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top x
    exact hab (by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx y])

theorem cq_equiv_of_simple {X H Y : Type} [Group X] [Group H] [Group Y] [IsSimpleGroup X]
    (hXq : CFSG.IsQuasisimple X) (hq : CFSG.IsQuasisimple H) (ψ : X →* H)
    (hψ : Function.Surjective ψ) (e : X ≃* Y) : Nonempty ((H ⧸ Subgroup.center H) ≃* Y) := by
  obtain ⟨c⟩ := cq_equiv hXq hq ψ hψ
  exact ⟨c.trans (((QuotientGroup.quotientMulEquivOfEq (center_eq_bot hXq)).trans
    QuotientGroup.quotientBot).trans e)⟩

end ExcAux

theorem commute_calP_of_noSectionOffender [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {L : Subgroup G} (hL : IsComponentOf L ⊤)
    (hex : ∀ (W : Type) [CommGroup W] [Finite W] (Lb Eb : Subgroup (MulAut W)), (∀ w : W, w * w = 1) →
      CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb → CFSG.IsQuasisimple ↥Lb → Eb ≠ ⊥ →
      CFSG.Quasithin.IsElemAbelian2 Eb → CFSG.Quasithin.IsQuadratic Eb →
      Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W)) → (∃ ψ : ↥L →* ↥Lb, Function.Surjective ψ) →
      Nat.card Eb * Nat.card (CFSG.Quasithin.fixV Eb) < Nat.card W)
    {A : Subgroup G} (hA : A ∈ UC22.Ext.calP ρ) : ⁅L, A⁆ = ⊥ := by
  by_contra hne
  have hAN := le_normalizer_of_mem_calP hρ hL hA
  have hLA := commutator_eq_self_of_mem_calP hρ hL hA hne
  have hAe := isElementaryAbelian_of_mem_calP hA
  have hbest := isBestOffenderOn_of_mem_calP hρ hA
  have hKq := ExcAux.isQuasisimple_of_isComponentOf hL
  have hLnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro hle
    have hL1 : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      apply hρ
      ext w
      simp [(hle hl).2 w Submodule.mem_top]
    haveI := hKq.2.1
    haveI : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance hL1
  obtain ⟨W', hW'1, hW'2, Lb, Eb, hsq, hirr, hq, hE0, hEel, hEq, hEN, hoff, ψ, hψ⟩ :=
    exists_irrSection ρ L A hKq hAe hAN hLA hLnt hbest
  exact absurd hoff (not_le.2 (hex W' Lb Eb hsq hirr hq hE0 hEel hEq hEN ⟨ψ, hψ⟩))

theorem noSectionOffender_l2Odd
    {X : Type} [Group X] {W : Type} [CommGroup W] [Finite W] {Lb Eb : Subgroup (MulAut W)}
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hX : IsL2Odd X p) (hXq : CFSG.IsQuasisimple X)
    (hW : ∀ w : W, w * w = 1) (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb)
    (hq : CFSG.IsQuasisimple ↥Lb) (hE : Eb ≠ ⊥) (hEe : CFSG.Quasithin.IsElemAbelian2 Eb)
    (hEN : Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (ψ : X →* ↥Lb)
    (hψ : Function.Surjective ψ) :
    Nat.card Eb * Nat.card (CFSG.Quasithin.fixV Eb) < Nat.card W := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.QuasithinUnique.Setup.Family.equiv_projectiveSL_of_model
    (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  haveI : IsSimpleGroup X := by
    haveI := CFSG.QuasithinUnique.Setup.Family.p2_isSimpleGroup (p := p) (by omega)
    exact e.isSimpleGroup
  obtain ⟨α⟩ := ExcAux.cq_equiv_of_simple hXq hq ψ hψ e
  haveI := hirr.1
  exact (CFSG.QuasithinUnique.Setup.Family.primeLinearTwoCover hp11 hW hq.1 hirr.2 α).2 Eb hEN hE hEe

theorem noSectionOffender_sz
    {X : Type} [Group X] {W : Type} [CommGroup W] [Finite W] {Lb Eb : Subgroup (MulAut W)}
    {n : ℕ} (hX : IsSz X n) (hXq : CFSG.IsQuasisimple X)
    (hW : ∀ w : W, w * w = 1) (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb)
    (hq : CFSG.IsQuasisimple ↥Lb) (hE : Eb ≠ ⊥) (hEe : CFSG.Quasithin.IsElemAbelian2 Eb)
    (hEN : Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (ψ : X →* ↥Lb)
    (hψ : Function.Surjective ψ) :
    Nat.card Eb * Nat.card (CFSG.Quasithin.fixV Eb) < Nat.card W := by
  obtain ⟨-, hSz⟩ := CFSG.Blueprint.LieModel.suzukiModel hX
  haveI : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_2b2_simplicity X 2 n hSz).2
  obtain ⟨-, a, ha, K, _, _, hn, hcard, ⟨e⟩⟩ := hSz
  obtain ⟨α⟩ := ExcAux.cq_equiv_of_simple hXq hq ψ hψ e
  haveI := hirr.1
  exact (CFSG.QuasithinUnique.Setup.Family.suzuki_irreducible_normalizer_excludes a ha (hn ▸ hcard) W
    hW Lb hq.1 hirr.2 α).2.2.2.2 Eb hE hEe hEN

theorem noSectionOffender_su3
    {X : Type} [Group X] {W : Type} [CommGroup W] [Finite W] {Lb Eb : Subgroup (MulAut W)}
    {n : ℕ} (hX : IsSU3 X n) (hXq : CFSG.IsQuasisimple X)
    (hW : ∀ w : W, w * w = 1) (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb)
    (hq : CFSG.IsQuasisimple ↥Lb) (hE : Eb ≠ ⊥) (hEe : CFSG.Quasithin.IsElemAbelian2 Eb)
    (hEN : Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (ψ : X →* ↥Lb)
    (hψ : Function.Surjective ψ) :
    Nat.card Eb * Nat.card (CFSG.Quasithin.fixV Eb) < Nat.card W := by
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX.2 (by decide)
  have hn : 2 ≤ n := by
    obtain ⟨-, h1, -, h3⟩ := hmodel.1
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact h3 (by norm_num)
  obtain ⟨c⟩ := ExcAux.cq_equiv hXq hq ψ hψ
  have hmodel0 := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv c.symm hmodel
  exact CFSG.QuasithinUnique.Setup.X5.evenUnitaryThreeNoOffender n hn W hW hirr.1 Lb Eb hq.1 hirr.2
    hmodel0 hE hEe hEN

theorem noSectionOffender_j1
    {X : Type} [Group X] {W : Type} [CommGroup W] [Finite W] {Lb Eb : Subgroup (MulAut W)}
    (hX : IsJ1 X) (hXq : CFSG.IsQuasisimple X)
    (hW : ∀ w : W, w * w = 1) (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb)
    (hq : CFSG.IsQuasisimple ↥Lb) (hE : Eb ≠ ⊥) (hEe : CFSG.Quasithin.IsElemAbelian2 Eb)
    (hEN : Eb ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (ψ : X →* ↥Lb)
    (hψ : Function.Surjective ψ) :
    Nat.card Eb * Nat.card (CFSG.Quasithin.fixV Eb) < Nat.card W := by
  obtain ⟨e⟩ := hX
  haveI := CFSG.Walter.J1Props.J1_simple
  haveI : IsSimpleGroup X := (e.trans CFSG.Walter.walterJ1EquivNative.symm).isSimpleGroup
  obtain ⟨α⟩ := ExcAux.cq_equiv_of_simple hXq hq ψ hψ e
  exact CFSG.QuasithinUnique.Setup.X1.j1ExclusionProp W hW Lb Eb hq.1 hirr ⟨α⟩ hEN hE hEe

theorem l2Odd_commute_calP [Finite G] [Finite V]
    (hρ : Function.Injective ρ) {L : Subgroup G} (hL : IsComponentOf L ⊤) {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) (hX : IsL2Odd ↥L p) {A : Subgroup G} (hA : A ∈ UC22.Ext.calP ρ) :
    ⁅L, A⁆ = ⊥ :=
  commute_calP_of_noSectionOffender hρ hL
    (fun W _ _ Lb Eb hW hirr hq hE hEe _ hEN ⟨ψ, hψ⟩ =>
      noSectionOffender_l2Odd hp hp11 hX (ExcAux.isQuasisimple_of_isComponentOf hL) hW hirr hq hE hEe
        hEN ψ hψ) hA

theorem sz_commute_calP [Finite G] [Finite V]
    (hρ : Function.Injective ρ) {L : Subgroup G} (hL : IsComponentOf L ⊤) {n : ℕ} (hX : IsSz ↥L n)
    {A : Subgroup G} (hA : A ∈ UC22.Ext.calP ρ) : ⁅L, A⁆ = ⊥ :=
  commute_calP_of_noSectionOffender hρ hL
    (fun W _ _ Lb Eb hW hirr hq hE hEe _ hEN ⟨ψ, hψ⟩ =>
      noSectionOffender_sz hX (ExcAux.isQuasisimple_of_isComponentOf hL) hW hirr hq hE hEe hEN ψ hψ) hA

theorem su3_commute_calP
    [Finite G] [Finite V]
    (hρ : Function.Injective ρ) {L : Subgroup G} (hL : IsComponentOf L ⊤) {n : ℕ} (hX : IsSU3 ↥L n)
    {A : Subgroup G} (hA : A ∈ UC22.Ext.calP ρ) : ⁅L, A⁆ = ⊥ :=
  commute_calP_of_noSectionOffender hρ hL
    (fun W _ _ Lb Eb hW hirr hq hE hEe _ hEN ⟨ψ, hψ⟩ =>
      noSectionOffender_su3 hX (ExcAux.isQuasisimple_of_isComponentOf hL) hW hirr hq hE hEe hEN ψ hψ) hA

theorem j1_commute_calP [Finite G] [Finite V]
    (hρ : Function.Injective ρ) {L : Subgroup G} (hL : IsComponentOf L ⊤) (hX : IsJ1 ↥L)
    {A : Subgroup G} (hA : A ∈ UC22.Ext.calP ρ) : ⁅L, A⁆ = ⊥ :=
  commute_calP_of_noSectionOffender hρ hL
    (fun W _ _ Lb Eb hW hirr hq hE hEe _ hEN ⟨ψ, hψ⟩ =>
      noSectionOffender_j1 hX (ExcAux.isQuasisimple_of_isComponentOf hL) hW hirr hq hE hEe hEN ψ hψ) hA

theorem commute_hP_of_forall_calP [Finite G] [Finite V] {L : Subgroup G}
    (h : ∀ A ∈ UC22.Ext.calP ρ, ⁅L, A⁆ = ⊥) : ⁅L, UC22.Ext.hP ρ⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  refine iSup₂_le fun A hA => ?_
  have h' := h A hA
  rwa [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h'

theorem excl_commute_hP
    [Finite G] [Finite V] (hρ : Function.Injective ρ) {L : Subgroup G} (hL : IsComponentOf L ⊤)
    (hshape : (∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsL2Odd ↥L p) ∨ (∃ n : ℕ, IsSz ↥L n) ∨
      (∃ n : ℕ, IsSU3 ↥L n) ∨ IsJ1 ↥L) : ⁅L, UC22.Ext.hP ρ⁆ = ⊥ := by
  refine commute_hP_of_forall_calP fun A hA => ?_
  rcases hshape with ⟨p, hp, hp11, hX⟩ | ⟨n, hX⟩ | ⟨n, hX⟩ | hX
  · exact l2Odd_commute_calP hρ hL hp hp11 hX hA
  · exact sz_commute_calP hρ hL hX hA
  · exact su3_commute_calP hρ hL hX hA
  · exact j1_commute_calP hρ hL hX hA

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
