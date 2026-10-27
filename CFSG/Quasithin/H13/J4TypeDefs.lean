module

public import CFSG.Quasithin.H13.J4PlusType
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.H13.J4

open CFSG.ComponentClassification.OuterAutomorphisms

abbrev M22 : Type := ↥CFSG.Blueprint.NativeSporadic.M22

@[expose] def IsAutTripleM22 (X : Type*) [Group X] : Prop :=
  ∃ Z : Subgroup X, Z.Normal ∧ Nat.card Z = 3 ∧
    (Subgroup.centralizer (Z : Set X)).index = 2 ∧
    Group.IsPerfect (Subgroup.centralizer (Z : Set X)) ∧
    (Subgroup.center (Subgroup.centralizer (Z : Set X))).map
      (Subgroup.centralizer (Z : Set X)).subtype = Z ∧
    (∀ g : X, g ∉ Subgroup.centralizer (Z : Set X) → ∀ x ∈ Z, g * x * g⁻¹ = x⁻¹) ∧
    ∃ (ψ : Subgroup.centralizer (Z : Set X) →* M22) (θ : X →* MulAut M22),
      Function.Surjective ψ ∧ ψ.ker = Z.subgroupOf (Subgroup.centralizer (Z : Set X)) ∧
      (∀ (g : X) (d : Subgroup.centralizer (Z : Set X))
        (h : g * d * g⁻¹ ∈ Subgroup.centralizer (Z : Set X)),
          θ g (ψ d) = ψ ⟨g * d * g⁻¹, h⟩) ∧
      Function.Surjective θ ∧ θ.ker = Z ∧ (Subgroup.centralizer (Z : Set X)).map θ = inner M22

@[expose] def IsTypeJ4Core (C : Type*) [Group C] (z : C) : Prop :=
  CFSG.pCore 2 C = CFSG.generalizedFitting C ∧
    IsExtraspecialPGroup 2 (CFSG.pCore 2 C) ∧ Nat.card (CFSG.pCore 2 C) = 2 ^ 13 ∧
    (Subgroup.center (CFSG.pCore 2 C)).map (CFSG.pCore 2 C).subtype = Subgroup.zpowers z ∧
    Nonempty (CFSG.pCore 2 C ≃* D8CentralProduct 6)

@[expose] def selfC {G : Type*} [Group G] (z : G) : Subgroup.centralizer ({z} : Set G) :=
  ⟨z, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def IsTypeJ4Centralizer (G : Type*) [Group G] (z : G) : Prop :=
  Nat.card (Subgroup.centralizer ({z} : Set G)) = 21799895040 ∧
    (∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)) ∧
    IsTypeJ4Core (Subgroup.centralizer ({z} : Set G)) (selfC z) ∧
    IsAutTripleM22 (Subgroup.centralizer ({z} : Set G) ⧸
      CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G))) ∧
    ∃ g : G, g⁻¹ * z * g ∈ (CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G))).map
      (Subgroup.centralizer ({z} : Set G)).subtype ∧ g⁻¹ * z * g ≠ z

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem center_map_mulEquiv' (e : X ≃* Y) :
    (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

theorem frattini_map_mulEquiv' (e : X ≃* Y) : (frattini X).map e.toMonoidHom = frattini Y :=
  OrderIso.map_radical (MulEquiv.mapSubgroup e)

theorem isExtraspecialPGroup_of_mulEquiv' {p : ℕ} (e : X ≃* Y) (h : IsExtraspecialPGroup p X) :
    IsExtraspecialPGroup p Y := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator X).map e.toMonoidHom = commutator Y := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, center_map_mulEquiv']
  · rw [← frattini_map_mulEquiv' e, hfrat, center_map_mulEquiv']
  · rw [← center_map_mulEquiv' e, Subgroup.card_map_of_injective e.injective, hcard]

theorem map_centralizer_mulEquiv (e : X ≃* Y) (S : Set X) :
    (Subgroup.centralizer S).map e.toMonoidHom = Subgroup.centralizer (e '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    show e s * e x = e x * e s
    rw [← map_mul, ← map_mul, hx s hs]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro s hs
    have := hy (e s) ⟨s, hs, rfl⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact this

@[expose] def subgroupEquivOfMap (e : X ≃* Y) {H : Subgroup X} {H' : Subgroup Y}
    (h : H.map e.toMonoidHom = H') : H ≃* H' :=
  (e.subgroupMap H).trans (MulEquiv.subgroupCongr h)

theorem subgroupEquivOfMap_coe (e : X ≃* Y) {H : Subgroup X} {H' : Subgroup Y}
    (h : H.map e.toMonoidHom = H') (x : H) : (subgroupEquivOfMap e h x : Y) = e x := rfl

theorem map_center_subtype (e : X ≃* Y) {H : Subgroup X} {H' : Subgroup Y}
    (h : H.map e.toMonoidHom = H') :
    ((Subgroup.center H).map H.subtype).map e.toMonoidHom =
      (Subgroup.center H').map H'.subtype := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨subgroupEquivOfMap e h x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    have := hx ((subgroupEquivOfMap e h).symm g)
    apply (subgroupEquivOfMap e h).symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact this
  · rintro ⟨y', hy', rfl⟩
    refine ⟨(subgroupEquivOfMap e h).symm y', ⟨(subgroupEquivOfMap e h).symm y', ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hy'
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro g
      apply (subgroupEquivOfMap e h).injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy' _
    · show e ((subgroupEquivOfMap e h).symm y' : X) = y'
      rw [← subgroupEquivOfMap_coe e h, MulEquiv.apply_symm_apply]

theorem IsAutTripleM22.of_mulEquiv (hX : IsAutTripleM22 X) (e : X ≃* Y) : IsAutTripleM22 Y := by
  obtain ⟨Z, hZn, hZc, hidx, hperf, hcen, hinv, ψ, θ, hψs, hψk, hcomp, hθs, hθk, hθD⟩ := hX
  have hD' : (Subgroup.centralizer (Z : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ((Z.map e.toMonoidHom : Subgroup Y) : Set Y) := by
    rw [map_centralizer_mulEquiv]
    rfl
  let eD := subgroupEquivOfMap e hD'
  refine ⟨Z.map e.toMonoidHom, hZn.map _ e.surjective, ?_, ?_, ?_, ?_, ?_,
    ψ.comp eD.symm.toMonoidHom,
    θ.comp e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hZc]
  · rw [← hD', Subgroup.index_map_of_bijective e.bijective, hidx]
  · rw [Group.isPerfect_def] at hperf ⊢
    have h1 : (commutator (Subgroup.centralizer (Z : Set X))).map eD.toMonoidHom =
        commutator (Subgroup.centralizer ((Z.map e.toMonoidHom : Subgroup Y) : Set Y)) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 eD.surjective]
    rw [← h1, hperf, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 eD.surjective]
  · rw [← map_center_subtype e hD', hcen]
  · intro g hg x hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    have hg' : e.symm g ∉ Subgroup.centralizer (Z : Set X) := by
      intro h
      apply hg
      rw [← hD']
      exact ⟨e.symm g, h, by simp⟩
    have := hinv _ hg' x0 hx0
    apply e.symm.injective
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul, map_inv,
      MulEquiv.symm_apply_apply]
    exact this
  · intro m
    obtain ⟨d, rfl⟩ := hψs m
    refine ⟨eD d, ?_⟩
    show ψ (eD.symm (eD d)) = ψ d
    rw [MulEquiv.symm_apply_apply]
  · ext d'
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf]
    rw [← MonoidHom.mem_ker, hψk, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      refine ⟨_, h, ?_⟩
      show e ((eD.symm d' : Subgroup.centralizer (Z : Set X)) : X) = d'
      rw [← subgroupEquivOfMap_coe e hD', MulEquiv.apply_symm_apply]
    · rintro ⟨x, hx, hxd⟩
      have : ((eD.symm d' : Subgroup.centralizer (Z : Set X)) : X) = x := by
        apply e.injective
        rw [← subgroupEquivOfMap_coe e hD', MulEquiv.apply_symm_apply]
        exact hxd.symm
      rw [this]
      exact hx
  · intro g d' h
    show θ (e.symm g) (ψ (eD.symm d')) = ψ (eD.symm ⟨g * d' * g⁻¹, h⟩)
    have hmem : e.symm g * (eD.symm d' : X) * (e.symm g)⁻¹ ∈ Subgroup.centralizer (Z : Set X) :=
      by
      have := (eD.symm ⟨g * d' * g⁻¹, h⟩).2
      convert this using 1
      apply e.injective
      rw [← subgroupEquivOfMap_coe e hD' (eD.symm _), MulEquiv.apply_symm_apply]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← subgroupEquivOfMap_coe e hD', MulEquiv.apply_symm_apply]
    rw [hcomp _ _ hmem]
    congr 1
    apply Subtype.ext
    apply e.injective
    rw [← subgroupEquivOfMap_coe e hD' (eD.symm _), MulEquiv.apply_symm_apply]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [← subgroupEquivOfMap_coe e hD', MulEquiv.apply_symm_apply]
  · intro φ
    obtain ⟨x, rfl⟩ := hθs φ
    exact ⟨e x, by simp⟩
  · ext y
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom]
    rw [← MonoidHom.mem_ker, hθk]
    constructor
    · intro h
      exact ⟨e.symm y, h, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  · rw [← hD', Subgroup.map_map]
    rw [← hθD]
    congr 1
    ext x
    simp

theorem IsTypeJ4Core.of_mulEquiv [Finite X] {z : X} {z' : Y} (h : IsTypeJ4Core X z)
    (e : X ≃* Y) (hz : e z = z') : IsTypeJ4Core Y z' := by
  subst hz
  obtain ⟨h1, h2, h3, h4, ⟨φ⟩⟩ := h
  have : Finite Y := Finite.of_equiv _ e.toEquiv
  have hF : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : (CFSG.pCore 2 X).map e.toMonoidHom = CFSG.pCore 2 Y := CFSG.pCore_map_iso 2 e
  let eQ := subgroupEquivOfMap e hQ
  refine ⟨?_, isExtraspecialPGroup_of_mulEquiv' eQ h2, by rw [← Nat.card_congr eQ.toEquiv, h3],
    ?_, ⟨eQ.symm.trans φ⟩⟩
  · have hX : CFSG.IsCharacteristicP 2 X :=
      (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore X 2).2 h1.symm
    have hY : CFSG.IsCharacteristicP 2 Y := by
      unfold CFSG.IsCharacteristicP at hX ⊢
      have hc := map_centralizer_mulEquiv e ((CFSG.pCore 2 X : Subgroup X) : Set X)
      rw [← hQ, Subgroup.coe_map, MulEquiv.coe_toMonoidHom, ← hc]
      exact Subgroup.map_mono hX
    exact ((CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore Y 2).1 hY).symm
  · rw [← map_center_subtype e hQ, h4, MonoidHom.map_zpowers]
    rfl

@[expose] noncomputable def pCoreQuotEquiv (e : X ≃* Y) :
    X ⧸ CFSG.pCore 2 X ≃* Y ⧸ CFSG.pCore 2 Y :=
  QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)

theorem mem_pCore_of_mulEquiv {x : X} (hx : x ∈ CFSG.pCore 2 X) (e : X ≃* Y) {y : Y}
    (hy : e x = y) : y ∈ CFSG.pCore 2 Y := by
  rw [← CFSG.pCore_map_iso 2 e]
  exact ⟨x, hx, hy⟩

theorem map_centralizer_singleton (e : X ≃* Y) (z : X) :
    (Subgroup.centralizer ({z} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set Y) := by
  rw [map_centralizer_mulEquiv, Set.image_singleton]

theorem IsTypeJ4Centralizer.of_mulEquiv [Finite X] {z : X} {z' : Y}
    (h : IsTypeJ4Centralizer X z) (e : X ≃* Y) (hz : e z = z') : IsTypeJ4Centralizer Y z' := by
  subst hz
  obtain ⟨hcard, ⟨S, hS⟩, hcore, hquot, g, hg1, hg2⟩ := h
  have : Finite Y := Finite.of_equiv _ e.toEquiv
  have hF : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := map_centralizer_singleton e z
  let eC := subgroupEquivOfMap e hC
  have heC : eC (selfC z) = selfC (e z) := rfl
  have hQ : (CFSG.pCore 2 (Subgroup.centralizer ({z} : Set X))).map eC.toMonoidHom =
      CFSG.pCore 2 (Subgroup.centralizer ({e z} : Set Y)) := CFSG.pCore_map_iso 2 eC
  refine ⟨by rw [← Nat.card_congr eC.toEquiv, hcard], ?_, hcore.of_mulEquiv eC heC,
    hquot.of_mulEquiv (QuotientGroup.congr _ _ eC hQ), e g, ?_, ?_⟩
  · have hcardS : Nat.card ((S : Subgroup X).map e.toMonoidHom) =
        2 ^ (Nat.card Y).factorization 2 := by
      rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity,
        Nat.card_congr e.toEquiv]
    refine ⟨Sylow.ofCard _ hcardS, ?_⟩
    rw [Sylow.coe_ofCard, ← hC]
    exact Subgroup.map_mono hS
  · obtain ⟨q, hq, hqg⟩ := hg1
    refine ⟨eC q, ?_, ?_⟩
    · rw [← hQ]
      exact ⟨q, hq, rfl⟩
    · have hqg' : (q : X) = g⁻¹ * z * g := hqg
      show e (q : X) = (e g)⁻¹ * e z * e g
      rw [hqg', map_mul, map_mul, map_inv]
  · intro h2
    apply hg2
    apply e.injective
    rw [map_mul, map_mul, map_inv]
    exact h2

end Transport

end CFSG.Quasithin.H13.J4
