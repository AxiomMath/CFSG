module

public import CFSG.Sporadic.ONOddCore.OuterLocal
public import CFSG.Sporadic.ONOddCore.OuterOrder
public import CFSG.GroupTheory.LocalCores.Components

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open UnbalancedCatalog.EvenCatalog (oddCore_eq_bot_of_mulEquiv)

theorem centralizer_map_equiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (a : G) :
    (Subgroup.centralizer {a}).map φ.toMonoidHom = Subgroup.centralizer {φ a} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← map_mul, hx, map_mul]
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply, hy]

@[expose] def centralizerCongr {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (a : G) :
    Subgroup.centralizer {a} ≃* Subgroup.centralizer {φ a} :=
  (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr (centralizer_map_equiv φ a))

theorem centralizer_subtype_map {G : Type*} [Group G] (H : Subgroup G) (a : H) :
    (Subgroup.centralizer {a}).map H.subtype = H ⊓ Subgroup.centralizer {(a : G)} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by rw [← Subgroup.coe_mul, hx, Subgroup.coe_mul]⟩
  · rintro ⟨hy, hya⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hya, rfl⟩

@[expose] def centralizerSubtypeEquiv {G : Type*} [Group G] (H : Subgroup G) (a : H) :
    Subgroup.centralizer {a} ≃* ↥(H ⊓ Subgroup.centralizer {(a : G)}) :=
  (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (centralizer_subtype_map H a))

theorem centralizer_zP :
    Subgroup.centralizer {zP} = Mv := by
  ext x
  rw [mem_centralizer_zP_iff, mem_Mv]

theorem oddCore_centralizer_P
    {a : Pv} (ha : orderOf a = 2) :
    CFSG.oddCore (Subgroup.centralizer {a}) = ⊥ := by
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate (a : Equiv.Perm (Fin N)) a.2
    (by rw [Subgroup.orderOf_coe]; exact ha)
  set gP : Pv := ⟨g, hg⟩
  have hφa : MulAut.conj gP⁻¹ a = zP := by
    apply Subtype.ext
    show (g⁻¹ * (a : Equiv.Perm (Fin N)) * g⁻¹⁻¹) = onz
    rw [hga]
    group
  have e := centralizerCongr (MulAut.conj gP⁻¹) a
  rw [hφa, centralizer_zP] at e
  have hM : CFSG.oddCore Mv = ⊥ :=
    oddCore_eq_bot_of_mulEquiv (Subgroup.subgroupOfEquivOfLe onM_le).symm oddCore_M
  exact oddCore_eq_bot_of_mulEquiv e.symm hM

theorem pv_not_comm :
    ∃ a b : Pv, a * b ≠ b * a :=
  ⟨⟨onv, onM_le onv_mem_M⟩, ⟨onh, onM_le onh_mem⟩, fun h => onv_not_comm_h (congrArg Subtype.val h)⟩

section GenFitting

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem genFitting_normal : (CFSG.generalizedFitting X).Normal :=
  (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2

theorem not_comm_of_equiv
    {F : Type*} [Group F] (ψ : F ≃* Pv) : ∃ a b : F, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := pv_not_comm
  refine ⟨ψ.symm a, ψ.symm b, fun h => hab ?_⟩
  have := congrArg ψ h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem center_eq_bot_of_simple' {F : Type*} [Group F] [IsSimpleGroup F]
    (h : ∃ a b : F, a * b ≠ b * a) : Subgroup.center F = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h' | h'
  · exact h'
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center F := h' ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem centralizer_genFitting_bot
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (ψ : CFSG.generalizedFitting X ≃* Pv) :
    Subgroup.centralizer (CFSG.generalizedFitting X : Set X) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  have hcF := CFSG.centralizer_generalizedFitting_le X hc
  have hz : (⟨c, hcF⟩ : CFSG.generalizedFitting X) ∈
      Subgroup.center (CFSG.generalizedFitting X) :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext ((Subgroup.mem_centralizer_iff.1 hc) g g.2)
  rw [center_eq_bot_of_simple' (not_comm_of_equiv ψ), Subgroup.mem_bot] at hz
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hz

@[expose] def outerHom :
    X →* Outer (CFSG.generalizedFitting X) :=
  haveI := genFitting_normal (X := X)
  (QuotientGroup.mk' (inner (CFSG.generalizedFitting X))).comp MulAut.conjNormal

theorem ker_outerHom
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (ψ : CFSG.generalizedFitting X ≃* Pv) :
    (outerHom (X := X)).ker = CFSG.generalizedFitting X := by
  have := genFitting_normal (X := X)
  ext x
  rw [MonoidHom.mem_ker, outerHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨f, hf⟩
    have hc : (f : X)⁻¹ * x ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun α : MulAut (CFSG.generalizedFitting X) =>
        ((α ⟨y, hy⟩ : CFSG.generalizedFitting X) : X)) hf
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc y * ((f : X)⁻¹ * x) = (f : X)⁻¹ * ((f : X) * y * (f : X)⁻¹) * x := by group
        _ = (f : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
        _ = (f : X)⁻¹ * x * y := by group
    rw [centralizer_genFitting_bot hF ψ, Subgroup.mem_bot] at hc
    have : x = f := by
      calc x = (f : X) * ((f : X)⁻¹ * x) := by group
        _ = f := by rw [hc, mul_one]
    rw [this]
    exact f.2
  · intro hx
    refine ⟨⟨x, hx⟩, ?_⟩
    ext y
    simp [MulAut.conjNormal_apply]

theorem index_dvd_four
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (e : CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.ON) :
    (CFSG.generalizedFitting X).index ∣ 4 := by
  have := genFitting_normal (X := X)
  set ψ : CFSG.generalizedFitting X ≃* Pv := e.trans onEquivPv
  have h1 : Nat.card (X ⧸ (outerHom (X := X)).ker) = Nat.card (outerHom (X := X)).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  rw [ker_outerHom hF ψ] at h1
  rw [Subgroup.index_eq_card, h1]
  have h2 : Nat.card (Outer (CFSG.generalizedFitting X)) ∣ 4 := by
    have h3 : Nat.card (Outer (CFSG.generalizedFitting X)) =
        Nat.card (Outer Blueprint.NativeSporadic.ON) :=
      Nat.card_congr (OuterAutomorphisms.equivalence (G := CFSG.generalizedFitting X)
        (H := Blueprint.NativeSporadic.ON) (by exact e)).toEquiv
    rw [h3]
    exact r3e_on_outer_order_divides_four.1
  exact (Subgroup.card_subgroup_dvd_card _).trans h2

theorem quotient_isPGroup
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (e : CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.ON) :
    haveI := genFitting_normal (X := X)
    IsPGroup 2 (X ⧸ CFSG.generalizedFitting X) := by
  have := genFitting_normal (X := X)
  have h := index_dvd_four hF e
  rw [Subgroup.index_eq_card, show (4 : ℕ) = 2 ^ 2 by norm_num] at h
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact IsPGroup.of_card hm

theorem oddCore_centralizer_of_inf
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (e : CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.ON) {t : X}
    (h : CFSG.oddCore ↥(CFSG.generalizedFitting X ⊓ Subgroup.centralizer {t}) = ⊥) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have := genFitting_normal (X := X)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key := (normal_prime_power_index_prime_complement_core 2 (quotient_isPGroup hF e)).2 t
  rw [oddCore_eq_pPrimeCore] at h ⊢
  rw [h, Subgroup.map_bot] at key
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 key

end GenFitting

theorem ctu_on_full_group_inner_involution_odd_core
    {X : Type*} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hON : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.ON)) :
    (CFSG.generalizedFitting X).index ∣ 4 ∧
      ∀ t : X, t ∈ CFSG.generalizedFitting X → orderOf t = 2 →
        CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨e⟩ := hON
  refine ⟨index_dvd_four hF e, fun t ht ht2 => oddCore_centralizer_of_inf hF e ?_⟩
  set ψ : CFSG.generalizedFitting X ≃* Pv := e.trans onEquivPv
  have hord : orderOf (ψ ⟨t, ht⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact ht2
  have e1 := centralizerCongr ψ ⟨t, ht⟩
  have e2 := centralizerSubtypeEquiv (CFSG.generalizedFitting X) ⟨t, ht⟩
  exact oddCore_eq_bot_of_mulEquiv (e1.symm.trans e2) (oddCore_centralizer_P hord)

end CFSG.Sporadic.ONOddCore
