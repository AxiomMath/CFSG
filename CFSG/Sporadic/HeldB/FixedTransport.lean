module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

theorem pComponent_quasisimple_of_relIndex_two {X : Type*} [Group X] [Finite X]
    {C D : Subgroup X} (hDC : D ≤ C) (hD : CFSG.IsQuasisimple D) (hidx : D.relIndex C = 2)
    (p : ℕ) (hp : p.Prime) (L : Subgroup C) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  have : Fact p.Prime := ⟨hp⟩
  have hidx' : (D.subgroupOf C).index = 2 := hidx
  have : (D.subgroupOf C).Normal := Subgroup.normal_of_index_eq_two hidx'
  have : Group.IsSolvable (C ⧸ D.subgroupOf C) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic (C ⧸ D.subgroupOf C) := isCyclic_of_prime_card hidx'
    exact Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup).mul_comm a b
  refine CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient p
    (D.subgroupOf C) (fun J hJ => ?_) L hL
  have hN : CFSG.IsQuasisimple (D.subgroupOf C) :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hDC)).2 hD
  have hJ := CatalogueBAlternatingIsometry.pComponent_eq_top_of_quasisimple hN p J hJ
  rw [hJ]
  exact (isQuasisimple_congr Subgroup.topEquiv).2 hN

theorem oddCore_eq_pPrimeCore_two' (G : Type*) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm

theorem pComponent_quasisimple_of_oddCore_eq_bot {H : Type*} [Group H] [Finite H]
    (hcore : CFSG.oddCore H = ⊥) (L : Subgroup H) (hL : CFSG.IsPComponent 2 L) :
    CFSG.IsQuasisimple L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 L hL
  have hsub : L.IsSubnormal := hL.choose_spec.2.1
  have hL0 : CFSG.pPrimeCore 2 L = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 L hsub,
      ← oddCore_eq_pPrimeCore_two', hcore, Subgroup.bot_subgroupOf]
  exact (isQuasisimple_congr ((QuotientGroup.quotientMulEquivOfEq hL0).trans
    QuotientGroup.quotientBot)).1 hq

theorem pComponent_quasisimple_of_mulEquiv {H K : Type*} [Group H] [Group K] [Finite H]
    [Finite K] (f : H ≃* K) (p : ℕ) (hp : p.Prime)
    (hK : ∀ L : Subgroup K, CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (L : Subgroup H) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have h := (p_component_isomorphism_transport p hp f).1 L
  exact (isQuasisimple_congr (L.equivMapOfInjective f.toMonoidHom f.injective)).2
    (hK _ (h.1 hL))

theorem oddCore_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.oddCore Y = ⊥) : CFSG.oddCore X = ⊥ := by
  rw [eq_bot_iff]
  apply sSup_le
  rintro K ⟨hKn, hKodd⟩
  have hmap : K.map e.toMonoidHom ≤ CFSG.oddCore Y :=
    le_sSup ⟨hKn.map _ e.surjective, by rwa [Subgroup.card_map_of_injective e.injective]⟩
  rw [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hmap
  rw [hmap]

variable {S T : Type*} [Group S] [Group T]

open FixedCommutingProduct

theorem mem_fixedSubgroup {α : MulAut S} {s : S} : s ∈ fixedSubgroup α ↔ α s = s := Iff.rfl

theorem congr_apply' (e : S ≃* T) (α : MulAut S) (t : T) :
    MulAut.congr e α t = e (α (e.symm t)) := rfl

theorem fixedSubgroup_map_congr (e : S ≃* T) (α : MulAut S) :
    (fixedSubgroup α).map e.toMonoidHom = fixedSubgroup (MulAut.congr e α) := by
  ext t
  rw [Subgroup.mem_map, mem_fixedSubgroup, congr_apply']
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [mem_fixedSubgroup] at hs
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hs]
  · intro ht
    refine ⟨e.symm t, ?_, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩
    rw [mem_fixedSubgroup]
    apply e.injective
    rw [ht, MulEquiv.apply_symm_apply]

@[expose] def fixedSubgroupCongr (e : S ≃* T) (α : MulAut S) :
    fixedSubgroup α ≃* fixedSubgroup (MulAut.congr e α) :=
  ((fixedSubgroup α).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (fixedSubgroup_map_congr e α))

theorem congr_conj (e : S ≃* T) (s : S) : MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext t
  rw [congr_apply', MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem congr_mem_range_conj_iff (e : S ≃* T) (α : MulAut S) :
    MulAut.congr e α ∈ (MulAut.conj : T →* MulAut T).range ↔
      α ∈ (MulAut.conj : S →* MulAut S).range := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨e.symm t, ?_⟩
    apply (MulAut.congr e).injective
    rw [← ht, congr_conj, MulEquiv.apply_symm_apply]
  · rintro ⟨s, rfl⟩
    exact ⟨e s, (congr_conj e s).symm⟩

theorem orderOf_congr (e : S ≃* T) (α : MulAut S) : orderOf (MulAut.congr e α) = orderOf α :=
  orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α

theorem orderOf_mulEquiv_apply (e : S ≃* T) (s : S) : orderOf (e s) = orderOf s :=
  orderOf_injective e.toMonoidHom e.injective s

theorem fixedSubgroup_conj (s : S) :
    fixedSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set S) := by
  ext x
  rw [mem_fixedSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * s = s * x * s⁻¹ * s := by rw [h]
      _ = s * x := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

@[expose] def centralizerEquiv (e : S ≃* T) (s : S) :
    Subgroup.centralizer ({s} : Set S) ≃* Subgroup.centralizer ({e s} : Set T) :=
  ((MulEquiv.subgroupCongr (fixedSubgroup_conj s).symm).trans (fixedSubgroupCongr e _)).trans
    (MulEquiv.subgroupCongr (by rw [congr_conj, fixedSubgroup_conj]))

theorem map_conj_inf_centralizer {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H)
    (y : M) :
    (H ⊓ Subgroup.centralizer {g * y * g⁻¹}).map (MulAut.conj g⁻¹).toMonoidHom =
      H ⊓ Subgroup.centralizer {y} := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hw
    obtain ⟨hw, hwc⟩ := hw
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hw) hg, ?_⟩
    calc g⁻¹ * w * g * y = g⁻¹ * (w * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * w) * g := by rw [hwc]
      _ = y * (g⁻¹ * w * g) := by group
  · rintro ⟨hz, hzy⟩
    refine ⟨g * z * g⁻¹, Subgroup.mem_inf.2 ⟨H.mul_mem (H.mul_mem hg hz) (H.inv_mem hg), ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * z * g⁻¹ * (g * y * g⁻¹) = g * (z * y) * g⁻¹ := by group
        _ = g * (y * z) * g⁻¹ := by rw [hzy]
        _ = g * y * g⁻¹ * (g * z * g⁻¹) := by group
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

@[expose] def infCentralizerConjEquiv {M : Type*} [Group M] {H : Subgroup M} {g : M}
    (hg : g ∈ H) (y : M) :
    (H ⊓ Subgroup.centralizer {g * y * g⁻¹} : Subgroup M) ≃* (H ⊓ Subgroup.centralizer {y} :
      Subgroup M) :=
  ((H ⊓ Subgroup.centralizer {g * y * g⁻¹}).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).trans (MulEquiv.subgroupCongr (map_conj_inf_centralizer hg y))

theorem orderOf_conj_eq {M : Type*} [Group M] (g x : M) : orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

theorem conj_mem_of_conj {M : Type*} [Group M] {H : Subgroup M} {s t c : M} (hc : c ∈ H)
    (ht : ∃ d ∈ H, t = d * s * d⁻¹) : ∃ d ∈ H, c * t * c⁻¹ = d * s * d⁻¹ := by
  obtain ⟨d, hd, rfl⟩ := ht
  exact ⟨c * d, H.mul_mem hc hd, by group⟩

theorem center_eq_bot_of_mulEquiv (e : S ≃* T) (h : Subgroup.center T = ⊥) :
    Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e z ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro y
    rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz]
  rw [h, Subgroup.mem_bot] at hz'
  exact e.injective (hz'.trans (map_one e).symm)

theorem conj_injective_of_center (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  rw [← hZ, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun α : MulAut S => α g) (MonoidHom.mem_ker.1 hs)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc g * s = s * g * s⁻¹ * s := by rw [h]
    _ = s * g := by group

theorem fixed_pComponent_quasisimple_of_cases [Finite T] (hZ : Subgroup.center T = ⊥)
    (hinner : ∀ t : T, orderOf t = 2 →
      CFSG.oddCore (Subgroup.centralizer ({t} : Set T)) = ⊥)
    (houter : ∀ β : MulAut T, orderOf β = 2 → β ∉ (MulAut.conj : T →* MulAut T).range →
      ∀ L : Subgroup (fixedSubgroup β), CFSG.IsPComponent 2 L → CFSG.IsQuasisimple L)
    (θ : S ≃* T) (α : MulAut S) (hα : orderOf α = 2) (L : Subgroup (fixedSubgroup α))
    (hL : CFSG.IsPComponent 2 L) : CFSG.IsQuasisimple L := by
  have : Finite S := Finite.of_equiv _ θ.symm.toEquiv
  have hβ : orderOf (MulAut.congr θ α) = 2 := by rw [orderOf_congr, hα]
  by_cases hinn : MulAut.congr θ α ∈ (MulAut.conj : T →* MulAut T).range
  · obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZ) t, ht, hβ]
    let f : fixedSubgroup α ≃* Subgroup.centralizer ({t} : Set T) :=
      (fixedSubgroupCongr θ α).trans (MulEquiv.subgroupCongr (by rw [← ht, fixedSubgroup_conj]))
    exact pComponent_quasisimple_of_oddCore_eq_bot (oddCore_eq_bot_of_mulEquiv f (hinner t ht2))
      L hL
  · exact pComponent_quasisimple_of_mulEquiv (fixedSubgroupCongr θ α) 2 Nat.prime_two
      (houter _ hβ hinn) L hL

end CFSG.Sporadic.HeldB
