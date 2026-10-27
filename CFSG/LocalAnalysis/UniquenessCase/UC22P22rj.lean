module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

section Image

theorem uc22p22r_pCoreOf_le_of_isSubnormal {K L : Subgroup G} (h : CFSG.Open.IsSubnormal K L) :
    CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction h with
  | refl A => exact le_rfl
  | @step A M B hAM hn _ ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hAM) ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hn).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)

theorem uc22p22r_ker_inclusion_pCore {K L : Subgroup G} (h : CFSG.Open.IsSubnormal K L) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion h.le)).ker = CFSG.pCore 2 ↥K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion h.le)).ker =
      (CFSG.pCore 2 ↥L).comap (Subgroup.inclusion h.le) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rw [hker]
  refine le_antisymm ?_ ?_
  · exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance
      (CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective h.le))
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := uc22p22r_pCoreOf_le_of_isSubnormal h ⟨x, hx, rfl⟩
    have : y = Subgroup.inclusion h.le x := Subtype.ext hyx
    show Subgroup.inclusion h.le x ∈ CFSG.pCore 2 ↥L
    rw [← this]
    exact hy

theorem uc22p22r_bar2_quasisimple_iso {L K : Subgroup G} (hK : K ∈ calC L) :
    ∃ K' : Subgroup (Bar2 L), K' = (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ∧
      (∃ e : Bar2 K ≃* ↥K', ∀ x : ↥K,
        (e (QuotientGroup.mk x) : Bar2 L) = QuotientGroup.mk (Subgroup.inclusion hK.1.le x)) ∧
      commutator ↥K' = ⊤ ∧ CFSG.Open.IsQuasisimple ↥K' ∧ CFSG.Open.IsSubnormal K' ⊤ := by
  let ψ : ↥K →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hK.1.le)
  have hker : ψ.ker = CFSG.pCore 2 ↥K := uc22p22r_ker_inclusion_pCore hK.1
  let e : Bar2 K ≃* ↥ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  have hqs : CFSG.Open.IsQuasisimple ↥ψ.range := CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hK.2.2
  have h1 : ψ.range = (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  refine ⟨ψ.range, h1, ⟨e, fun x => rfl⟩, hqs.1, hqs, ?_⟩
  rw [h1]
  exact CFSG.Open.IsSubnormal.of_mathlib (hK.1.subgroupOf.map (QuotientGroup.mk'_surjective _))

end Image

section Components

variable {X : Type} [Group X]

theorem uc22p22r_normal_of_commuting {K₁ K₂ : Subgroup X} (hsup : K₁ ⊔ K₂ = ⊤)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) : K₁.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h : b * x * b⁻¹ = x := by
      calc b * x * b⁻¹ = x * b * b⁻¹ := by rw [hcomm x hx b hb]
        _ = x := by group
    rw [h]
    exact hx
  · intro hy
    have h1 : b⁻¹ * (b * x * b⁻¹) = (b * x * b⁻¹) * b⁻¹ := (hcomm _ hy b⁻¹ (K₂.inv_mem hb)).symm
    have h2 : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = (b * x * b⁻¹) * b⁻¹ * b := by rw [h1]
        _ = b * x * b⁻¹ := by group
    rw [h2]
    exact hy

theorem uc22p22r_component_le_or_le [Finite X] {A₁ A₂ K' : Subgroup X} [A₁.Normal] [A₂.Normal]
    (hsup : A₁ ⊔ A₂ = ⊤) (hK' : CFSG.Open.IsComponentOf K' ⊤) : K' ≤ A₁ ∨ K' ≤ A₂ := by
  by_contra hcon
  rw [not_or] at hcon
  have h1 := (CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes K' A₁
    hK').resolve_left hcon.1
  have h2 := (CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes K' A₂
    hK').resolve_left hcon.2
  have hA₁ : A₁ ≤ Subgroup.centralizer (K' : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h1
  have hA₂ : A₂ ≤ Subgroup.centralizer (K' : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h2
  have htop : (⊤ : Subgroup X) ≤ Subgroup.centralizer (K' : Set X) := hsup ▸ sup_le hA₁ hA₂
  have hcen : K' ≤ Subgroup.center X := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    exact ((Subgroup.mem_centralizer_iff.1 (htop (Subgroup.mem_top g))) k hk).symm
  haveI : Group.IsPerfect ↥K' := ⟨hK'.2.2.1⟩
  haveI : Nontrivial ↥K' := CFSG.ComponentClassification.Quasisimple.nontrivial hK'.2.2
  exact (Subgroup.nontrivial_iff_ne_bot K').1 inferInstance
    (CFSG.ComponentClassification.Quasisimple.perfect_le_center_eq_bot K' hcen)

theorem uc22p22r_equiv_factor {A B : Type} [Group A] [Group B] [IsSimpleGroup A] (e : X ≃* A × B)
    {K' : Subgroup X} (hsub : K'.IsSubnormal) (hne : K' ≠ ⊥)
    (hle : K' ≤ ((MonoidHom.snd A B).comp e.toMonoidHom).ker) : Nonempty (↥K' ≃* A) := by
  let π : X →* A := (MonoidHom.fst A B).comp e.toMonoidHom
  have hπ : Function.Surjective π := fun a => ⟨e.symm (a, 1), by simp [π]⟩
  have hinj : ∀ x ∈ K', π x = 1 → x = 1 := by
    intro x hx h1
    have h2 : (e x).2 = 1 := hle hx
    refine e.injective (Prod.ext ?_ ?_)
    · simpa [π] using h1
    · simpa using h2
  have himg : K'.map π = ⊤ := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance (hsub.map hπ) with h | h
    · exfalso
      refine hne (eq_bot_iff.2 fun x hx => ?_)
      have hx' : π x ∈ K'.map π := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.2 (hinj x hx hx')
    · exact h
  refine ⟨MulEquiv.ofBijective (π.comp K'.subtype) ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  · intro a
    have ha : a ∈ K'.map π := by
      rw [himg]
      exact Subgroup.mem_top a
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, hx⟩, rfl⟩

end Components

section Transport

theorem uc22p22r_lieModel_quot_center_congr {P W : Type} [Group P] [Group W] (e : P ≃* W)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m n : ℕ} (h : LieModel (W ⧸ Subgroup.center W) t m 2 n) :
    LieModel (P ⧸ Subgroup.center P) t m 2 n :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    (QuotientGroup.congr (Subgroup.center W) (Subgroup.center P) e.symm (Subgroup.map_center_eq e.symm)) h

theorem uc22p22r_ne_bot_of_equiv {X P : Type} [Group X] [Group P] {K' : Subgroup X} (e : P ≃* ↥K')
    (hP : CFSG.Open.IsQuasisimple P) : K' ≠ ⊥ := by
  haveI : Nontrivial P := CFSG.ComponentClassification.Quasisimple.nontrivial hP
  haveI : Nontrivial ↥K' := e.symm.toEquiv.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot K').1 inferInstance

theorem uc22p22r_lieModel_of_quasisimple {X P : Type} [Group X] [Group P] {K' : Subgroup X} (e : P ≃* ↥K')
    (hP : CFSG.Open.IsQuasisimple P) (hsub : CFSG.Open.IsSubnormal K' ⊤) (hX : CFSG.Open.IsQuasisimple X)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m n : ℕ} (h : LieModel (X ⧸ Subgroup.center X) t m 2 n) :
    LieModel (P ⧸ Subgroup.center P) t m 2 n := by
  haveI : Group.IsPerfect ↥K' := ⟨(CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hP).1⟩
  have htop : K' = ⊤ :=
    (CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hX K' hsub).resolve_left
      (uc22p22r_ne_bot_of_equiv e hP)
  exact uc22p22r_lieModel_quot_center_congr (e.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)) h

theorem uc22p22r_lieModel_of_suCentralSquare {X P : Type} [Group X] [Finite X] [Group P] {K' : Subgroup X}
    (e : P ≃* ↥K') (hP : CFSG.Open.IsQuasisimple P) (hsub : CFSG.Open.IsSubnormal K' ⊤)
    (h : IsSU3CentralSquare X) : LieModel (P ⧸ Subgroup.center P) .PSU 3 2 3 := by
  obtain ⟨K₁, K₂, hsup, hcomm, hK₁, hK₂, -⟩ := h
  have hK' : CFSG.Open.IsComponentOf K' ⊤ :=
    ⟨le_top, hsub, CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hP⟩
  haveI : K₁.Normal := uc22p22r_normal_of_commuting hsup hcomm
  haveI : K₂.Normal :=
    uc22p22r_normal_of_commuting (by rwa [sup_comm]) fun a ha b hb => (hcomm b hb a ha).symm
  have hc₁ : CFSG.Open.IsComponentOf K₁ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal ‹_›), hK₁.1⟩
  have hc₂ : CFSG.Open.IsComponentOf K₂ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal ‹_›), hK₂.1⟩
  rcases uc22p22r_component_le_or_le hsup hK' with hle | hle
  · exact uc22p22r_lieModel_quot_center_congr
      (e.trans (MulEquiv.subgroupCongr
        (CFSG.ComponentClassification.LocalComponents.eq_of_le K' K₁ hK' hc₁ hle))) hK₁.2
  · exact uc22p22r_lieModel_quot_center_congr
      (e.trans (MulEquiv.subgroupCongr
        (CFSG.ComponentClassification.LocalComponents.eq_of_le K' K₂ hK' hc₂ hle))) hK₂.2

end Transport

section Shape

theorem uc22p22r_lieModel_quot_center {P X : Type} [Group P] [Group X] (e : P ≃* X)
    (hP : CFSG.Open.IsQuasisimple P) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m n : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus ∨ t = .twistedB2 ∨ t = .G2 ∨
      t = .trialityD4 ∨ t = .twistedF4)
    (h : LieModel X t m 2 n) : LieModel (P ⧸ Subgroup.center P) t m 2 n := by
  haveI : IsSimpleGroup X := uc22p22r_lieModel_isSimple ht h
  haveI : IsSimpleGroup P := e.isSimpleGroup
  have hc : Subgroup.center P = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center P) with h0 | h0
    · exact h0
    · exfalso
      have h1 : commutator P = ⊥ := (commutator_eq_bot_iff_center_eq_top P).2 h0
      rw [hP.1] at h1
      obtain ⟨a, ha⟩ := exists_ne (1 : P)
      have : a ∈ (⊤ : Subgroup P) := Subgroup.mem_top a
      rw [h1, Subgroup.mem_bot] at this
      exact ha this
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e).symm h

theorem uc22p22r_lieModel_of_subnormal {X P : Type} [Group X] [Group P] {K' : Subgroup X} (e : P ≃* ↥K')
    (hP : CFSG.Open.IsQuasisimple P) (hsub : CFSG.Open.IsSubnormal K' ⊤)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m n : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaMinus ∨ t = .twistedB2 ∨ t = .G2 ∨
      t = .trialityD4 ∨ t = .twistedF4)
    (h : LieModel X t m 2 n) : LieModel (P ⧸ Subgroup.center P) t m 2 n := by
  haveI : IsSimpleGroup X := uc22p22r_lieModel_isSimple ht h
  have htop : K' = ⊤ :=
    (CFSG.Open.IsSubnormal.eq_bot_or_top hsub).resolve_left (uc22p22r_ne_bot_of_equiv e hP)
  exact uc22p22r_lieModel_quot_center (e.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)) hP ht h

end Shape

end CFSG.LocalAnalysis.UniquenessCase.UC22
