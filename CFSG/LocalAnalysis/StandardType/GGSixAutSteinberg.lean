module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Model

@[expose] def GGAutModel (S : Type*) [Group S] (R : S → Prop) : Prop :=
  ∃ I C : Subgroup (MulAut S), I.Normal ∧ (MulAut.conj : S →* MulAut S).range ≤ I ∧
    Odd ((MulAut.conj : S →* MulAut S).range.relIndex I) ∧
    (∀ σ : MulAut S, ∃ i ∈ I, ∃ c ∈ C, σ = i * c) ∧ I ⊓ C = ⊥ ∧
    ∀ r, R r → ∀ c ∈ C, c ^ 2 = 1 → c ≠ 1 → ∀ e ∈ I, GGGoodAut r (e * c * e⁻¹)

namespace AutSt

variable {S S' : Type*} [Group S] [Group S']

theorem congr_conj (Θ : S ≃* S') (y : S) :
    MulAut.congr Θ (MulAut.conj y) = MulAut.conj (Θ y) := by
  ext x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem range_conj_congr (Θ : S ≃* S') :
    (MulAut.conj : S' →* MulAut S').range =
      (MulAut.conj : S →* MulAut S).range.map (MulAut.congr Θ).toMonoidHom := by
  ext σ
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨MulAut.conj (Θ.symm x), ⟨_, rfl⟩, ?_⟩
    change MulAut.congr Θ (MulAut.conj (Θ.symm x)) = MulAut.conj x
    rw [congr_conj, MulEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨Θ y, (congr_conj Θ y).symm⟩

end AutSt

open AutSt in
theorem GGAutModel.congr {S S' : Type*} [Group S] [Group S'] {R : S → Prop} (Θ : S ≃* S')
    (h : GGAutModel S R) : GGAutModel S' (fun r' => R (Θ.symm r')) := by
  obtain ⟨I, C, hI, hKI, hodd, hIC, hIC', hgood⟩ := h
  set φ := MulAut.congr Θ
  have hφ : Function.Injective φ.toMonoidHom := φ.injective
  refine ⟨I.map φ.toMonoidHom, C.map φ.toMonoidHom, hI.map _ φ.surjective, ?_, ?_, ?_, ?_, ?_⟩
  · rw [range_conj_congr Θ]
    exact Subgroup.map_mono hKI
  · rw [range_conj_congr Θ, Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact hodd
  · intro σ
    obtain ⟨i, hi, c, hc, h⟩ := hIC (φ.symm σ)
    refine ⟨φ i, ⟨i, hi, rfl⟩, φ c, ⟨c, hc, rfl⟩, ?_⟩
    rw [← map_mul, ← h, MulEquiv.apply_symm_apply]
  · rw [← Subgroup.map_inf_eq _ _ _ hφ, hIC', Subgroup.map_bot]
  · rintro r' hr' _ ⟨c, hc, rfl⟩ hc2 hc1 _ ⟨e, he, rfl⟩
    have hc2' : c ^ 2 = 1 := φ.injective (by
      rw [map_pow, map_one]
      exact hc2)
    have hc1' : c ≠ 1 := by
      rintro rfl
      exact hc1 (map_one φ.toMonoidHom)
    have h := (hgood _ hr' c hc hc2' hc1' e he).congr Θ
    rw [MulEquiv.apply_symm_apply] at h
    change GGGoodAut r' (φ e * φ c * (φ e)⁻¹)
    rwa [← map_inv, ← map_mul, ← map_mul]

theorem GGAutModel.mono {S : Type*} [Group S] {R R' : S → Prop} (h : GGAutModel S R)
    (hR : ∀ r, R' r → R r) : GGAutModel S R' := by
  obtain ⟨I, C, hI, hKI, hodd, hIC, hIC', hgood⟩ := h
  exact ⟨I, C, hI, hKI, hodd, hIC, hIC', fun r hr => hgood r (hR r hr)⟩

end Model

namespace AutSt

variable {S : Type*} [Group S]

theorem autModel_of_hom {Q : Type*} [Group Q] {R : S → Prop} (Θ : MulAut S →* Q)
    (C : Subgroup (MulAut S)) (hInn : (MulAut.conj : S →* MulAut S).range ≤ Θ.ker)
    (hodd : Odd ((MulAut.conj : S →* MulAut S).range.relIndex Θ.ker))
    (hC : ∀ σ : MulAut S, ∃ c ∈ C, Θ c = Θ σ) (hCinj : ∀ c ∈ C, Θ c = 1 → c = 1)
    (hgood : ∀ r, R r → ∀ c ∈ C, c ^ 2 = 1 → c ≠ 1 → ∀ e ∈ Θ.ker, GGGoodAut r (e * c * e⁻¹)) :
    GGAutModel S R := by
  refine ⟨Θ.ker, C, Θ.normal_ker, hInn, hodd, fun σ => ?_, ?_, hgood⟩
  · obtain ⟨c, hc, hΘ⟩ := hC σ
    refine ⟨σ * c⁻¹, ?_, c, hc, by rw [inv_mul_cancel_right]⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΘ, mul_inv_cancel]
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact hCinj x hx.2 hx.1

abbrev fixSub (c : MulAut S) : Subgroup S :=
  c.toMonoidHom.eqLocus (MonoidHom.id S)

theorem mem_fixSub {c : MulAut S} {x : S} : x ∈ fixSub c ↔ c x = x :=
  Iff.rfl

theorem eq_one_of_odd_of_mem {Q : Subgroup S} (hQ : IsPGroup 2 Q) {a : S} (ha : a ∈ Q)
    (hao : Odd (orderOf a)) : a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨a, ha⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hao
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hao) ((Nat.even_pow' hk0).mpr even_two)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem eq_bot_of_fixed_simple {c : MulAut S} (hJ : IsSimpleGroup (fixSub c)) {a : S}
    (ha : c a = a) (ha1 : a ≠ 1) (hao : Odd (orderOf a)) (Q : Subgroup S)
    (hfix : ∀ q ∈ Q, c q = q) (hQ : IsPGroup 2 Q)
    (hnorm : ∀ y : S, c y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) : Q = ⊥ := by
  have hQJ : Q ≤ fixSub c := fun q hq => hfix q hq
  have hN : (Q.subgroupOf (fixSub c)).Normal := by
    refine ⟨fun q hq y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hq ⊢
    exact hnorm y y.2 q hq
  rcases hN.eq_bot_or_eq_top with h | h
  · rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    have hq' : (⟨q, hQJ hq⟩ : fixSub c) ∈ Q.subgroupOf (fixSub c) := hq
    rw [h, Subgroup.mem_bot] at hq'
    exact congrArg Subtype.val hq'
  · exfalso
    have haQ : (⟨a, ha⟩ : fixSub c) ∈ Q.subgroupOf (fixSub c) := by
      rw [h]
      exact Subgroup.mem_top _
    exact ha1 (eq_one_of_odd_of_mem hQ haQ hao)

theorem goodAut_of_fixed_simple {r : S} {c : MulAut S} (hJ : IsSimpleGroup (fixSub c)) (g : S)
    (hg : c (g * r * g⁻¹) = g * r * g⁻¹) (a : S) (ha : c a = a)
    (har : a * (g * r * g⁻¹) = g * r * g⁻¹ * a) (ha1 : a ≠ 1) (hao : Odd (orderOf a)) :
    GGGoodAut r c :=
  ⟨fun Q hfix hQ hnorm => eq_bot_of_fixed_simple hJ ha ha1 hao Q hfix hQ hnorm,
    g, hg, a, ha, har, ha1, hao⟩

theorem goodAut_conj_inner {r : S} {c : MulAut S} (h : GGGoodAut r c) {e : MulAut S}
    (he : e ∈ (MulAut.conj : S →* MulAut S).range) : GGGoodAut r (e * c * e⁻¹) := by
  obtain ⟨k, rfl⟩ := he
  exact h.conj _ ⟨k, rfl⟩

end AutSt

section Isogeny

variable {U C : Type*} [Group U] [Group C]

@[expose] def GGModelRoot (Δ : UniversalRootDatum U) (t : StatedLieTag) (π : U →* C) (r : C) :
    Prop :=
  orderOf r = 2 ∧ ∃ γ, GGRootClass Δ t γ ∧ ∃ u z : U, z ∈ Δ.rootGroup γ ∧ r = π (u * z * u⁻¹)

theorem AutSt.ker_eq_center {G : Type*} [Group G] {ψ : U →* G}
    (hker : ψ.ker ≤ Subgroup.center U) (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ψ.ker = Subgroup.center U := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker]
  have hcent : ψ z ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
  rw [hC, Subgroup.mem_bot] at hcent
  exact hcent

@[expose] noncomputable def AutSt.modelEquiv {G : Type*} [Group G] (ψ : U →* G) (π : U →* C)
    (hπ : Function.Surjective π) (hker : π.ker = ψ.ker) : C ≃* ψ.range :=
  (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange ψ))

theorem AutSt.modelEquiv_apply {G : Type*} [Group G] (ψ : U →* G) (π : U →* C)
    (hπ : Function.Surjective π) (hker : π.ker = ψ.ker) (y : U) :
    ((AutSt.modelEquiv ψ π hπ hker (π y) : ψ.range) : G) = ψ y := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π y) = (y : U ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [AutSt.modelEquiv, MulEquiv.trans_apply, e]
  rfl

end Isogeny

section Inputs

@[expose] def GGAutModelAt (t : StatedLieTag) : Prop :=
  ∀ n f : ℕ, StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank → ¬ (t = .F4 ∧ Odd f) →
    ∃ (C : Type) (_ : Group C) (π : (ggU t n f).K →* C), Function.Surjective π ∧
      π.ker = Subgroup.center (ggU t n f).K ∧ GGAutModel C (GGModelRoot (ggU t n f).D t π)

theorem ggAutStructureAt_of_autModelAt {t : StatedLieTag} (h : GGAutModelAt t) :
    GGAutStructureAt t := by
  intro G _ _ n f ψ G₀ hadm hrank hrange hker _ _ hC _ hF r hr
  obtain ⟨C, _, π, hπ, hπker, hM⟩ := h n f hadm hrank hF
  have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hψ := AutSt.ker_eq_center hker hC'
  set Θ : C ≃* G₀ := (AutSt.modelEquiv ψ π hπ (hπker.trans hψ.symm)).trans
    (MulEquiv.subgroupCongr hrange)
  have hΘ : ∀ y, ((Θ (π y) : G₀) : G) = ψ y := fun y =>
    AutSt.modelEquiv_apply ψ π hπ (hπker.trans hψ.symm) y
  obtain ⟨I, C', h1, h2, h3, h4, h5, h6⟩ := hM.congr Θ
  refine ⟨I, C', h1, h2, h3, h4, h5, fun c hc hc2 hc1 e he => ?_⟩
  rw [ggGoodOuterAut_iff]
  refine h6 r ?_ c hc hc2 hc1 e he
  obtain ⟨hr2, γ, hγ, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, hzr⟩ := hru
  have hr' : r = Θ (π (u * z * u⁻¹)) := by
    apply Subtype.ext
    rw [hΘ, ← hzr]
    rfl
  refine ⟨?_, γ, hγ, u, z, hz, by rw [hr', MulEquiv.symm_apply_apply]⟩
  rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact hr2

end Inputs

end CFSG.StandardType
