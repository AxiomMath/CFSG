module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypes
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SolCard
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Linear
public import CFSG.Quasithin.Recognition.F112Crit.QuasisimpleInvolution
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import Certificates.Certificate43

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.F112Crit

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Solomon
  CFSG.HardMathSupport.Solomon.Coordinator

section Basics

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) V

theorem isF2Transvection_of_fixes (g : 𝔾) (hg : g ≠ 1) (w : V)
    (h : ∀ v, ∃ s : ZMod 2, v + (g : V →ₗ[ZMod 2] V) v = s • (w + (g : V →ₗ[ZMod 2] V) w)) :
    IsF2Transvection g := by
  refine ⟨hg, ?_⟩
  set u : V := w + (g : V →ₗ[ZMod 2] V) w with hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hg
    refine i285_ext fun v => ?_
    obtain ⟨s, hs⟩ := h v
    rw [h0, smul_zero] at hs
    have h2 : (g : V →ₗ[ZMod 2] V) v = -v := eq_neg_of_add_eq_zero_right hs
    calc (g : V →ₗ[ZMod 2] V) v = -v := h2
      _ = v := zmod2_neg v
      _ = ((1 : 𝔾) : V →ₗ[ZMod 2] V) v := (i285_one_apply v).symm
  have hspan : commutatorSpace g = Submodule.span (ZMod 2) {u} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      obtain ⟨s, hs⟩ := h v
      rw [LinearMap.add_apply, LinearMap.id_apply, hs]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨w, by rw [LinearMap.add_apply, LinearMap.id_apply]⟩
  rw [hspan, finrank_span_singleton hu0]

theorem conj_tv_apply (φ : Dual (ZMod 2) V) (a : V) (h : φ a = 0) (g : 𝔾) (v : V) :
    ((g * tv φ a h * g⁻¹ : 𝔾) : V →ₗ[ZMod 2] V) v =
      v + φ (((g⁻¹ : 𝔾) : V →ₗ[ZMod 2] V) v) • (g : V →ₗ[ZMod 2] V) a := by
  rw [i285_mul_apply, i285_mul_apply, tv_apply, map_add, map_smul, i285_apply_inv_apply]

theorem isF2Transvection_conj {t : 𝔾} (ht : IsF2Transvection t) (g : 𝔾) :
    IsF2Transvection (g * t * g⁻¹) := by
  obtain ⟨φ, a, h, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  have h' : (φ ∘ₗ ((g⁻¹ : 𝔾) : V →ₗ[ZMod 2] V)) ((g : V →ₗ[ZMod 2] V) a) = 0 := by
    rw [LinearMap.comp_apply, i285_inv_apply_apply]
    exact h
  rw [conj_tv g φ a h h']
  refine (isF2Transvection_iff _).2 ⟨_, _, h', ?_, ?_, rfl⟩
  · intro h0
    apply hφ
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 ((g : V →ₗ[ZMod 2] V) v)
    rwa [LinearMap.comp_apply, i285_inv_apply_apply, LinearMap.zero_apply] at this
  · intro h0
    apply ha
    have := congrArg ((g⁻¹ : 𝔾) : V →ₗ[ZMod 2] V) h0
    rwa [i285_inv_apply_apply, map_zero] at this

end Basics

section SectionAction

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) V

@[expose] def secP (X : Subgroup 𝔾) (a : V) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {v | ∃ g ∈ X, v = (g : V →ₗ[ZMod 2] V) a}

@[expose] def secQ (X : Subgroup 𝔾) (φ : Dual (ZMod 2) V) : Submodule (ZMod 2) V where
  carrier := {v | ∀ g ∈ X, φ ((g : V →ₗ[ZMod 2] V) v) = 0}
  add_mem' {u v} hu hv g hg := by rw [map_add, map_add, hu g hg, hv g hg, add_zero]
  zero_mem' g _ := by rw [map_zero, map_zero]
  smul_mem' c v hv g hg := by rw [map_smul, map_smul, hv g hg, smul_zero]

variable (X : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (φ : Dual (ZMod 2) V) (a : V)

theorem apply_mem_secP {g : 𝔾} (hg : g ∈ X) : (g : V →ₗ[ZMod 2] V) a ∈ secP X a :=
  Submodule.subset_span ⟨g, hg, rfl⟩

theorem a_mem_secP : a ∈ secP X a := apply_mem_secP X a X.one_mem

theorem X_le_stab_secP : X ≤ i285_stab (secP X a) := by
  apply i285_le_stab
  intro x hx v hv
  have : (secP X a).map (x : V →ₗ[ZMod 2] V) ≤ secP X a := by
    rw [secP, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact apply_mem_secP X a (X.mul_mem hx hg)
  exact this ⟨v, hv, rfl⟩

theorem X_le_stab_secQ : X ≤ i285_stab (secQ X φ) := by
  apply i285_le_stab
  intro x hx v hv g hg
  exact hv (g * x) (X.mul_mem hg hx)

theorem secQ_le_ker {v : V} (hv : v ∈ secQ X φ) : φ v = 0 := hv 1 X.one_mem

theorem secP_eq_of_stab {hφa : φ a = 0} (hτX : tv φ a hφa ∈ X) {T : Submodule (ZMod 2) V}
    (hT : X ≤ i285_stab T) (h1 : secP X a ⊓ secQ X φ ≤ T) (h2 : T ≤ secP X a) :
    T = secP X a ⊓ secQ X φ ∨ T = secP X a := by
  by_cases haT : a ∈ T
  · right
    refine le_antisymm h2 ?_
    rw [secP, Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    exact (hT hg _).2 haT
  · left
    refine le_antisymm (le_inf h2 ?_) h1
    intro v hv g hg
    have hgv : (g : V →ₗ[ZMod 2] V) v ∈ T := (hT hg v).2 hv
    have hτ : (tv φ a hφa : V →ₗ[ZMod 2] V) ((g : V →ₗ[ZMod 2] V) v) ∈ T :=
      (hT hτX _).2 hgv
    rcases zmod2_eq_zero_or_one (φ ((g : V →ₗ[ZMod 2] V) v)) with h | h
    · exact h
    · exfalso
      apply haT
      have := T.sub_mem hτ hgv
      rwa [tv_apply, add_sub_cancel_left, h, one_smul] at this

@[expose] noncomputable def secHom :
    ↥X →* LinearMap.GeneralLinearGroup (ZMod 2)
      (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype) :=
  i285_secHom (X_le_stab_secP X a) (X_le_stab_secQ X φ)

theorem secHom_mk (g : ↥X) (v : ↥(secP X a)) :
    ((secHom X φ a g : LinearMap.GeneralLinearGroup (ZMod 2)
        (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype)) :
        (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype) →ₗ[ZMod 2]
          (↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype))
        (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨((g : 𝔾) : V →ₗ[ZMod 2] V) v,
        (X_le_stab_secP X a g.2 v).2 v.2⟩ :=
  rfl

end SectionAction

theorem top_eq_closure_preimage {G : Type*} [Group G] {D : Set G} {X : Subgroup G}
    (hXD : X = Subgroup.closure D) :
    Subgroup.closure (Subtype.val ⁻¹' D : Set ↥X) = ⊤ := by
  subst hXD
  exact Subgroup.closure_closure_coe_preimage

theorem exists_mcLaughlin_quotient {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (X : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)) (φ : Dual (ZMod 2) V) (a : V)
    (hφa : φ a = 0) (hτX : tv φ a hφa ∈ X)
    (D : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) (hτD : tv φ a hφa ∈ D)
    (hD : ∀ d ∈ D, ∃ g ∈ X, d = g * tv φ a hφa * g⁻¹) (hXD : X = Subgroup.closure D)
    (haQ : ∃ g ∈ X, φ ((g : V →ₗ[ZMod 2] V) a) ≠ 0) :
    ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module (ZMod 2) V')
      (_ : FiniteDimensional (ZMod 2) V')
      (σ : ↥X →* LinearMap.GeneralLinearGroup (ZMod 2) V'),
      UniquenessMaximal.IsMcLaughlinGroup ↥σ.range := by
  classical
  obtain ⟨g₀, hg₀X, hg₀⟩ := haQ
  have haQs : a ∉ secQ X φ := fun h => hg₀ (h g₀ hg₀X)
  have hZker : (secQ X φ).comap (secP X a).subtype ≤
      LinearMap.ker (φ ∘ₗ (secP X a).subtype) := by
    intro v hv
    rw [LinearMap.mem_ker]
    exact secQ_le_ker X φ hv
  refine ⟨↥(secP X a) ⧸ (secQ X φ).comap (secP X a).subtype, inferInstance, inferInstance,
    inferInstance, secHom X φ a, ?_⟩
  set P := secP X a with hP
  set Qs := secQ X φ with hQ
  set Zq : Submodule (ZMod 2) ↥P := Qs.comap P.subtype with hZq
  set σ := secHom X φ a with hσ
  let abar : ↥P ⧸ Zq := Submodule.Quotient.mk ⟨a, a_mem_secP X a⟩
  let φ' : Dual (ZMod 2) (↥P ⧸ Zq) := Zq.liftQ (φ ∘ₗ P.subtype) hZker
  have hφ'mk : ∀ v : ↥P, φ' (Submodule.Quotient.mk v) = φ v := fun v => rfl
  have hφ'a : φ' abar = 0 := hφa
  have hφ'ne : φ' ≠ 0 := by
    intro h0
    apply hg₀
    have := hφ'mk ⟨(g₀ : V →ₗ[ZMod 2] V) a, apply_mem_secP X a hg₀X⟩
    rw [h0] at this
    exact this.symm
  have hane : abar ≠ 0 := by
    intro h0
    rw [Submodule.Quotient.mk_eq_zero] at h0
    exact haQs h0
  have hστ : σ ⟨tv φ a hφa, hτX⟩ = tv φ' abar hφ'a := by
    refine tv_ext fun w => ?_
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective Zq w
    rw [tv_apply, hφ'mk, hσ, secHom_mk, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_add]
    congr 1
  have hτ': IsF2Transvection (σ ⟨tv φ a hφa, hτX⟩) := by
    rw [hστ]
    exact (isF2Transvection_iff _).2 ⟨φ', abar, hφ'a, hφ'ne, hane, rfl⟩
  have hrange : σ.range = Subgroup.closure (σ '' (Subtype.val ⁻¹' D)) := by
    rw [MonoidHom.range_eq_map, ← MonoidHom.map_closure, top_eq_closure_preimage hXD]
  have hSt : ∀ s ∈ σ '' (Subtype.val ⁻¹' D), IsF2Transvection s := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, hxg⟩ := hD x.1 hx
    have : x = ⟨g, hg⟩ * ⟨tv φ a hφa, hτX⟩ * (⟨g, hg⟩ : ↥X)⁻¹ := Subtype.ext hxg
    rw [this, map_mul, map_mul, map_inv]
    exact isF2Transvection_conj hτ' _
  have hirr : ∀ U : Submodule (ZMod 2) (↥P ⧸ Zq),
      (∀ g ∈ σ.range, ∀ w ∈ U,
        (g : (↥P ⧸ Zq) →ₗ[ZMod 2] (↥P ⧸ Zq)) w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    let T' : Submodule (ZMod 2) V := (U.comap Zq.mkQ).map P.subtype
    have hmemT' : ∀ v : ↥P, (v : V) ∈ T' ↔ Submodule.Quotient.mk v ∈ U := by
      intro v
      constructor
      · rintro ⟨y, hy, hyv⟩
        have : y = v := Subtype.ext hyv
        rw [← this]
        exact hy
      · intro h
        exact ⟨v, h, rfl⟩
    have hT'P : T' ≤ P := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hX : ∀ h ∈ X, ∀ v ∈ T', (h : V →ₗ[ZMod 2] V) v ∈ T' := by
      rintro h hh _ ⟨y, hy, rfl⟩
      have hy' : Submodule.Quotient.mk y ∈ U := hy
      have := hU _ ⟨⟨h, hh⟩, rfl⟩ _ hy'
      rw [hσ, secHom_mk] at this
      exact (hmemT' _).2 this
    have hTstab : X ≤ i285_stab T' := i285_le_stab hX
    have hPQ : P ⊓ Qs ≤ T' := by
      intro v hv
      refine (hmemT' ⟨v, hv.1⟩).2 ?_
      rw [(Submodule.Quotient.mk_eq_zero Zq).2 hv.2]
      exact U.zero_mem
    rcases secP_eq_of_stab X φ a hτX hTstab hPQ hT'P with hT | hT
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Zq w
      have hv := (hmemT' v).2 hw
      rw [hT] at hv
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact hv.2
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Zq w
      refine (hmemT' v).1 ?_
      rw [hT]
      exact v.2
  exact CFSG.HardMathSupport.Solomon.Coordinator.mcLaughlinTypes_holds _ σ.range
    ⟨σ '' (Subtype.val ⁻¹' D), ⟨_, ⟨⟨tv φ a hφa, hτX⟩, hτD, rfl⟩⟩, hSt, hrange⟩ hirr

@[expose] def NoMcLaughlinCover (Q : Type) [Group Q] : Prop :=
  ∀ (W : Type) [Group W], UniquenessMaximal.IsMcLaughlinGroup W →
    ∀ f : Q →* W, f.ker ≤ Subgroup.center Q → f.range.Normal → f.range.index ≤ 2 → False

theorem commute_of_normalizing_transvection {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (hno : NoMcLaughlinCover Q) (κ : Q →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    (hκ : Function.Injective κ) {t : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ht : IsF2Transvection t) (hnorm : ∀ q : Q, t * κ q * t⁻¹ ∈ κ.range) :
    ∀ q : Q, κ q * t = t * κ q := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V →ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V →ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
  haveI : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    Finite.of_injective (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V)) fun g h hgh => Units.ext hgh
  obtain ⟨φ, a, hφa, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  set τ := tv φ a hφa with hτ
  have ht2 : τ * τ = 1 := tv_mul_self φ a hφa
  have hτi : τ⁻¹ = τ := tv_inv φ a hφa
  set K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) := κ.range with hK
  have hKq : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr (MonoidHom.ofInjective hκ)).mp hq
  have hnorm' : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K := by
    rintro _ ⟨q, rfl⟩
    exact hnorm q
  have hnc' : ∃ k ∈ K, k * τ ≠ τ * k := by
    obtain ⟨q, hq'⟩ := hcon
    exact ⟨κ q, ⟨q, rfl⟩, hq'⟩
  set X : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) := conjGen K τ with hX
  have hKX : K ≤ X := le_conjGen hKq ht2 hnorm' hnc'
  have hτX : τ ∈ X := self_mem_conjGen
  have hτN : τ ∈ Subgroup.normalizer (K : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm' h hh, fun hh => ?_⟩
    have := hnorm' _ hh
    have e : τ * (τ * h * τ⁻¹) * τ⁻¹ = h := by
      rw [show τ * (τ * h * τ⁻¹) * τ⁻¹ = (τ * τ) * h * (τ * τ)⁻¹ by group, ht2]
      group
    rwa [e] at this
  have hXnorm : X ≤ Subgroup.normalizer (K : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hk) hτN)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hk))
  obtain ⟨k₁, hk₁, k₂, hk₂, hne⟩ := exists_not_commute hKq ht2 hnorm' hnc'
  have haQ : ∃ g ∈ X, φ ((g : V →ₗ[ZMod 2] V) a) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hcomm : ∀ x ∈ X, ∀ y ∈ X, (x * τ * x⁻¹) * (y * τ * y⁻¹) = (y * τ * y⁻¹) * (x * τ * x⁻¹) := by
      intro x hx y hy
      refine i285_comm_of_fix
        (f := fun v => φ (((x⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v))
        (f' := fun v => φ (((y⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v))
        (α := (x : V →ₗ[ZMod 2] V) a) (β := (y : V →ₗ[ZMod 2] V) a)
        (conj_tv_apply φ a hφa x) (conj_tv_apply φ a hφa y) ?_ ?_
      · rw [conj_tv_apply φ a hφa x]
        have : φ (((x⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
            ((y : V →ₗ[ZMod 2] V) a)) = 0 := hall (x⁻¹ * y) (X.mul_mem (X.inv_mem hx) hy)
        rw [this, zero_smul, add_zero]
      · rw [conj_tv_apply φ a hφa y]
        have : φ (((y⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
            ((x : V →ₗ[ZMod 2] V) a)) = 0 := hall (y⁻¹ * x) (X.mul_mem (X.inv_mem hy) hx)
        rw [this, zero_smul, add_zero]
    apply hne
    rw [hτi]
    have h1 := hcomm k₁ (hKX hk₁) k₂ (hKX hk₂)
    have h2 := hcomm k₁ (hKX hk₁) 1 X.one_mem
    have h3 := hcomm k₂ (hKX hk₂) 1 X.one_mem
    simp only [inv_one, one_mul, mul_one] at h2 h3
    exact ((Commute.mul_left (show Commute (k₁ * τ * k₁⁻¹) (k₂ * τ * k₂⁻¹) from h1)
      (show Commute τ (k₂ * τ * k₂⁻¹) from h3.symm)).mul_right
      (Commute.mul_left (show Commute (k₁ * τ * k₁⁻¹) τ from h2) (Commute.refl τ)))
  obtain ⟨V', _, _, _, σ, hσ⟩ := exists_mcLaughlin_quotient X φ a hφa hτX
    {x | ∃ k ∈ K, x = k * τ * k⁻¹} ⟨1, K.one_mem, by rw [hτ]; group⟩
    (by rintro _ ⟨k, hk, rfl⟩; exact ⟨k, hKX hk, rfl⟩) rfl haQ
  let κX : Q →* ↥X := κ.codRestrict X fun q => hKX ⟨q, rfl⟩
  let Φ : Q →* LinearMap.GeneralLinearGroup (ZMod 2) V' := σ.comp κX
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
      (MonoidHom.normal_ker Φ) with htop | hcen
  ·
    have h1 : ∀ q : Q, σ (κX q) = 1 := fun q => by
      have : q ∈ Φ.ker := by rw [htop]; exact Subgroup.mem_top q
      exact this
    have h2 : ∀ w ∈ σ.range, w = 1 ∨ w = σ ⟨τ, hτX⟩ := by
      rintro _ ⟨x, rfl⟩
      rcases conjGen_subset ht2 hnorm' x.1 x.2 with hx | ⟨k, hk, hx⟩
      · left
        obtain ⟨q, hq'⟩ := hx
        have : x = κX q := Subtype.ext hq'.symm
        rw [this]
        exact h1 q
      · right
        obtain ⟨q, rfl⟩ := hk
        have : x = κX q * ⟨τ, hτX⟩ := Subtype.ext hx
        rw [this, map_mul, h1 q, one_mul]
    have hcommW : ∀ u v : ↥σ.range, u * v = v * u := by
      intro u v
      apply Subtype.ext
      rcases h2 u.1 u.2 with hu | hu <;> rcases h2 v.1 v.2 with hv | hv <;> simp [hu, hv]
    have hsolv : Group.IsSolvable ↥σ.range := isSolvable_of_comm hcommW
    have hcard : Nat.card ↥σ.range ≤ 2 := by
      have hsurj : Function.Surjective (fun b : Bool =>
          (if b then (1 : ↥σ.range) else ⟨σ ⟨τ, hτX⟩, ⟨_, rfl⟩⟩)) := by
        intro w
        rcases h2 w.1 w.2 with h | h
        · exact ⟨true, Subtype.ext (by simp [h])⟩
        · exact ⟨false, Subtype.ext (by simp [h])⟩
      calc Nat.card ↥σ.range ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
        _ = 2 := by simp
    rcases mcl_solvable_card hσ hsolv with h | h <;> omega
  ·
    let σ' : ↥X →* ↥σ.range := σ.rangeRestrict
    have hσ' : Function.Surjective σ' := σ.rangeRestrict_surjective
    let f : Q →* ↥σ.range := σ'.comp κX
    have hfker : f.ker ≤ Subgroup.center Q := by
      intro q hq'
      apply hcen
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hq')
      exact MonoidHom.mem_ker.mpr this
    have hfrange : f.range = (K.subgroupOf X).map σ' := by
      ext w
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨κX q, Subgroup.mem_subgroupOf.mpr ⟨q, rfl⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨q, hq'⟩ := Subgroup.mem_subgroupOf.mp hx
        have : κX q = x := Subtype.ext hq'
        exact ⟨q, by simp [f, this]⟩
    have hnormal : f.range.Normal := by
      rw [hfrange]
      exact Subgroup.Normal.map ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hXnorm) σ' hσ'
    have hindex : f.range.index ≤ 2 := by
      rw [hfrange]
      have hdvd := Subgroup.index_map_dvd (H := K.subgroupOf X) hσ'
      have hle := index_subgroupOf_conjGen_le_two (K := K) ht2 hnorm'
      have hpos : (K.subgroupOf X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd).trans hle
    exact hno _ hσ f hfker hnormal hindex

end CFSG.Quasithin.F112Crit
