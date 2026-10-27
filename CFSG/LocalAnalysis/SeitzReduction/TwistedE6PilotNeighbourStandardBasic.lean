module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalKernel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section General

variable {M : Type*} [Group M]

theorem centralizer_subgroupOf {A C : Subgroup M} (hAC : A ≤ C) :
    centralizer (A.subgroupOf C : Set C) = (centralizer (A : Set M)).subgroupOf C := by
  ext x
  rw [mem_subgroupOf, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (h ⟨a, hAC ha⟩ (mem_subgroupOf.2 ha))
  · intro h a ha
    exact Subtype.ext (h a (mem_subgroupOf.1 ha))

theorem centralizer_subgroupOf_eq_sup {A Y D C : Subgroup M} (hAC : A ≤ C) (hYC : Y ≤ C)
    (hDC : D ≤ C) (h : centralizer (A : Set M) ⊓ C = Y ⊔ D) :
    centralizer (A.subgroupOf C : Set C) = Y.subgroupOf C ⊔ D.subgroupOf C := by
  rw [centralizer_subgroupOf hAC, ← inf_subgroupOf_right, h, subgroupOf_sup hYC hDC]

theorem centralizer_map_conj_inf {C A : Subgroup M} {n : M} (hn : n ∈ C) :
    centralizer ((A.map (MulAut.conj n).toMonoidHom : Subgroup M) : Set M) ⊓ C =
      (centralizer (A : Set M) ⊓ C).map (MulAut.conj n).toMonoidHom := by
  ext x
  constructor
  · intro hxx
    obtain ⟨hx, hxC⟩ := mem_inf.1 hxx
    refine ⟨n⁻¹ * x * n, mem_inf.2 ⟨mem_centralizer_iff.2 fun a ha => ?_,
      mul_mem (mul_mem (inv_mem hn) hxC) hn⟩, ?_⟩
    · have h1 := mem_centralizer_iff.1 hx (n * a * n⁻¹) ⟨a, ha, rfl⟩
      calc a * (n⁻¹ * x * n) = n⁻¹ * (n * a * n⁻¹ * x) * n := by group
        _ = n⁻¹ * (x * (n * a * n⁻¹)) * n := by rw [h1]
        _ = n⁻¹ * x * n * a := by group
    · change n * (n⁻¹ * x * n) * n⁻¹ = x
      group
  · rintro ⟨y, hyy, rfl⟩
    obtain ⟨hy, hyC⟩ := mem_inf.1 hyy
    refine mem_inf.2 ⟨mem_centralizer_iff.2 ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      change n * a * n⁻¹ * (n * y * n⁻¹) = n * y * n⁻¹ * (n * a * n⁻¹)
      have h1 := mem_centralizer_iff.1 hy a ha
      calc n * a * n⁻¹ * (n * y * n⁻¹) = n * (a * y) * n⁻¹ := by group
        _ = n * (y * a) * n⁻¹ := by rw [h1]
        _ = n * y * n⁻¹ * (n * a * n⁻¹) := by group
    · change n * y * n⁻¹ ∈ C
      exact mul_mem (mul_mem hn hyC) (inv_mem hn)

theorem map_conj_le {A C : Subgroup M} (hAC : A ≤ C) {n : M} (hn : n ∈ C) :
    A.map (MulAut.conj n).toMonoidHom ≤ C := by
  rintro _ ⟨a, ha, rfl⟩
  change n * a * n⁻¹ ∈ C
  exact mul_mem (mul_mem hn (hAC ha)) (inv_mem hn)

theorem map_conj_le_centralizer_map_conj {Y D : Subgroup M} (h : Y ≤ centralizer (D : Set M))
    (n : M) : Y.map (MulAut.conj n).toMonoidHom ≤
      centralizer ((D.map (MulAut.conj n).toMonoidHom : Subgroup M) : Set M) :=
  F4Pilot.map_le_centralizer_map _ h

theorem isQuasisimple_subgroupOf {D C : Subgroup M} (hDC : D ≤ C) [IsSimpleGroup D]
    [Group.IsPerfect D] : CFSG.IsQuasisimple (D.subgroupOf C) := by
  have hnc : ∃ a b : D, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative D ⟨⟨fun a b => h a b⟩⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hDC).symm
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1

theorem mul_mul_inv_mul_inv_mem_of_mem_sup {Y D : Subgroup M}
    (hYD : Y ≤ centralizer (D : Set M)) (hYc : Y ≤ centralizer (Y : Set M)) {g h : M}
    (hg : g ∈ Y ⊔ D) (hh : h ∈ Y ⊔ D) : g * h * g⁻¹ * h⁻¹ ∈ D := by
  have hYN : Y ≤ normalizer (D : Set M) := hYD.trans (Subgroup.centralizer_le_normalizer _)
  have hg' : g ∈ ((Y ⊔ D : Subgroup M) : Set M) := hg
  have hh' : h ∈ ((Y ⊔ D : Subgroup M) : Set M) := hh
  rw [coe_mul_of_left_le_normalizer_right _ _ hYN] at hg' hh'
  obtain ⟨y₁, hy₁, d₁, hd₁, rfl⟩ := Set.mem_mul.1 hg'
  obtain ⟨y₂, hy₂, d₂, hd₂, rfl⟩ := Set.mem_mul.1 hh'
  have hc : ∀ {y d : M}, y ∈ Y → d ∈ D → y * d = d * y := fun hy hd =>
    (mem_centralizer_iff.1 (hYD hy) _ hd).symm
  have e1 : y₁ * d₁ * (y₂ * d₂) = y₁ * y₂ * (d₁ * d₂) :=
    calc y₁ * d₁ * (y₂ * d₂) = y₁ * (d₁ * y₂) * d₂ := by group
      _ = y₁ * (y₂ * d₁) * d₂ := by rw [← hc hy₂ hd₁]
      _ = y₁ * y₂ * (d₁ * d₂) := by group
  have e2 : y₂ * d₂ * (y₁ * d₁) = y₁ * y₂ * (d₂ * d₁) :=
    calc y₂ * d₂ * (y₁ * d₁) = y₂ * (d₂ * y₁) * d₁ := by group
      _ = y₂ * (y₁ * d₂) * d₁ := by rw [← hc hy₁ hd₂]
      _ = y₂ * y₁ * (d₂ * d₁) := by group
      _ = y₁ * y₂ * (d₂ * d₁) := by rw [mem_centralizer_iff.1 (hYc hy₁) y₂ hy₂]
  have hu : d₁ * d₂ * (d₂ * d₁)⁻¹ ∈ D :=
    mul_mem (mul_mem hd₁ hd₂) (inv_mem (mul_mem hd₂ hd₁))
  have hw : y₁ * y₂ ∈ Y := mul_mem hy₁ hy₂
  have key : y₁ * d₁ * (y₂ * d₂) * (y₁ * d₁)⁻¹ * (y₂ * d₂)⁻¹ = d₁ * d₂ * (d₂ * d₁)⁻¹ :=
    calc y₁ * d₁ * (y₂ * d₂) * (y₁ * d₁)⁻¹ * (y₂ * d₂)⁻¹
        = (y₁ * d₁ * (y₂ * d₂)) * (y₂ * d₂ * (y₁ * d₁))⁻¹ := by group
      _ = (y₁ * y₂) * (d₁ * d₂ * (d₂ * d₁)⁻¹) * (y₁ * y₂)⁻¹ := by rw [e1, e2]; group
      _ = (d₁ * d₂ * (d₂ * d₁)⁻¹) * (y₁ * y₂) * (y₁ * y₂)⁻¹ := by rw [hc hw hu]
      _ = d₁ * d₂ * (d₂ * d₁)⁻¹ := by group
  rw [key]
  exact hu

end General

section Kernel


theorem lieModel_quotient_center_twistedE6 {L : Type} [Group L] (hZ : center L = ⊥) {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) :
    LieModel (L ⧸ center L) .twistedE6 0 2 f := by
  have := finite_of_card hK
  obtain ⟨e'⟩ := RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv TwistTag.E6
    Nat.prime_two hf K hK σ hσ
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hf, rfl⟩, K, inferInstance,
    inferInstance, hK, σ, hσ, ⟨(quotientCenterMulEquiv hZ).trans (e.trans e'.symm)⟩⟩)


theorem inf_centralizer_eq_zpowers_twistedE6 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_exceptional exceptionalHypothesisOne hset.standardSetting
    hset.center_eq_bot (Or.inr (Or.inr (Or.inl rfl)))
    (lieModel_quotient_center_twistedE6 hset.center_eq_bot hf hK hσ e) htC ht

end Kernel

section Generic

variable {G : Type*} [Group G] {L : Subgroup G} {C : Type*} [Group C]

theorem forall_fix_eq_one_map_symm (e : L ≃* C) {A D : Subgroup C}
    (hAut : ∀ β : MulAut C, (∀ x ∈ A, β x = x) → (∀ x ∈ D, β x = x) →
      ∀ n : ℕ, β ^ 2 ^ n = 1 → β = 1) :
    ∀ β : MulAut L, (∀ a : L, (a : G) ∈ (A.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      (∀ a : L, (a : G) ∈ (D.map e.symm.toMonoidHom).map L.subtype → β a = a) →
      ∀ n : ℕ, β ^ 2 ^ n = 1 → β = 1 := by
  intro β hβX hβD n hβn
  have hmem : ∀ {B : Subgroup C} {x : C}, x ∈ B →
      ((e.symm x : L) : G) ∈ (B.map e.symm.toMonoidHom).map L.subtype :=
    fun {_ x} hx => ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
  have key : MulAut.congr e β = 1 := by
    refine hAut _ (fun x hx => ?_) (fun x hx => ?_) n ?_
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβX _ (hmem hx),
        MulEquiv.apply_symm_apply]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hβD _ (hmem hx),
        MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβn, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem isQuasisimple_map_symm (e : L ≃* C) {D : Subgroup C} (hD : CFSG.IsQuasisimple D) :
    CFSG.IsQuasisimple ((D.map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((D.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      ((D.map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)) hD

theorem neighbour_standard_of_centralizer_eq_sup_gen [Finite G]
    (hL : standardComponentIsStandard L) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (e : L ≃* C) {A Y DC : Subgroup C} (hA : centralizer (A : Set C) = Y ⊔ DC)
    (hYD : Y ≤ centralizer (DC : Set C)) (hYc : Y ≤ centralizer (Y : Set C))
    (hDq : CFSG.IsQuasisimple DC)
    (hAut : ∀ β : MulAut C, (∀ x ∈ A, β x = x) → (∀ x ∈ DC, β x = x) →
      ∀ n : ℕ, β ^ 2 ^ n = 1 → β = 1)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = (DC.map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  subst hX hDe
  have hD := F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e hA hYD hYc hDq
  have hDq' := isQuasisimple_map_symm e hDq
  exact F4Pilot.standard_inheritance_of_forall_fix_eq_one hL htC ht hK htX hD.symm
    ⟨hDq'.1.commutator_eq_top, hDq'.2.1⟩ (forall_fix_eq_one_map_symm e hAut)

end Generic

end CFSG.SeitzReduction.TwistedE6Pilot
