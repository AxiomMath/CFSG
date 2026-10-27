module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityOuter
public import CFSG.OddTranspositions.PartFour.Thirteen

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld.Bridge CFSG.LocalAnalysis.WeakClosure81 CFSG.Open

namespace ExtSetting

variable {G : Type} [Group G] {t : G} {M : Subgroup G} [M.Normal]

theorem ne_bot (h : ExtSetting G t M) : M ≠ ⊥ :=
  h.minimal.2.1

theorem not_isMulCommutative [Finite G] (h : ExtSetting G t M) : ¬ IsMulCommutative M :=
  not_isMulCommutative_of_ne_bot h.rad h.ne_bot

theorem center_sup_zpowers_eq_bot (h : ExtSetting G t M) :
    Subgroup.center ↥(M ⊔ Subgroup.zpowers t) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : (z : G) ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz ⟨m, Subgroup.mem_sup_left hm⟩)
  rw [h.centralizer, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.mpr (Subtype.ext hc)

theorem derivedSeries_sup_zpowers_one [Finite G] (h : ExtSetting G t M) :
    derivedSeries ↥(M ⊔ Subgroup.zpowers t) 1 = M.subgroupOf (M ⊔ Subgroup.zpowers t) := by
  have e := Subgroup.subgroupOfEquivOfLe (le_sup_left : M ≤ M ⊔ Subgroup.zpowers t)
  have := h.simple
  have : (M.subgroupOf (M ⊔ Subgroup.zpowers t)).Normal := Subgroup.normal_subgroupOf
  have hMna := h.not_isMulCommutative
  have hM'na : ¬ IsMulCommutative ↥(M.subgroupOf (M ⊔ Subgroup.zpowers t)) := by
    rintro ⟨⟨hc⟩⟩
    exact hMna ⟨⟨fun a b => by simpa using congrArg e (hc (e.symm a) (e.symm b))⟩⟩
  have hperf := commutator_self_eq_of_isSimpleGroup e.isSimpleGroup hM'na
  have := Subgroup.zpowers_isMulCommutative t
  exact (derivedSeries_one_eq_two_of_sup_eq_top hperf
    (Subgroup.subgroupOf_isMulCommutative (H := Subgroup.zpowers t) (K := M ⊔ Subgroup.zpowers t))
    (sup_subgroupOf_sup_eq_top M (Subgroup.zpowers t))).1

theorem relIndex_sup_zpowers (h : ExtSetting G t M) :
    M.relIndex (M ⊔ Subgroup.zpowers t) = 2 := by
  rw [Subgroup.relIndex_sup_left]
  have ht2 : orderOf t = 2 := h.setup.oddT.1 t (IsConj.refl t)
  have hdvd : M.relIndex (Subgroup.zpowers t) ∣ 2 := by
    rw [← ht2, ← Nat.card_zpowers]
    exact Subgroup.relIndex_dvd_card M (Subgroup.zpowers t)
  have hne : M.relIndex (Subgroup.zpowers t) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one, Subgroup.zpowers_le]
    exact h.not_mem
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd h1 hne
  · exact h2

variable {H : Type*} [Group H]

theorem map_derivedSeries_one [Finite G] (h : ExtSetting G t M)
    (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) :
    (derivedSeries H 1).map φ.toMonoidHom = M.subgroupOf (M ⊔ Subgroup.zpowers t) := by
  rw [map_derivedSeries_eq (f := φ.toMonoidHom) φ.surjective, h.derivedSeries_sup_zpowers_one]

theorem mem_derivedSeries_one_iff [Finite G] (h : ExtSetting G t M)
    (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) {x : H} :
    x ∈ derivedSeries H 1 ↔ ((φ x : ↥(M ⊔ Subgroup.zpowers t)) : G) ∈ M := by
  rw [← Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective, h.map_derivedSeries_one φ,
    Subgroup.mem_subgroupOf]
  rfl

theorem index_derivedSeries_one [Finite G] (h : ExtSetting G t M)
    (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) : (derivedSeries H 1).index = 2 := by
  rw [← Subgroup.index_map_equiv (derivedSeries H 1) φ]
  change ((derivedSeries H 1).map φ.toMonoidHom).index = 2
  rw [h.map_derivedSeries_one φ]
  exact h.relIndex_sup_zpowers

@[expose] noncomputable def derivedEquiv [Finite G] (h : ExtSetting G t M)
    (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) : ↥(derivedSeries H 1) ≃* ↥M :=
  ((derivedSeries H 1).equivMapOfInjective φ.toMonoidHom φ.injective).trans
    ((MulEquiv.subgroupCongr (h.map_derivedSeries_one φ)).trans
      (Subgroup.subgroupOfEquivOfLe le_sup_left))

theorem coe_derivedEquiv_apply [Finite G] (h : ExtSetting G t M)
    (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) (x : ↥(derivedSeries H 1)) :
    ((h.derivedEquiv φ x : ↥M) : G) = ((φ x : ↥(M ⊔ Subgroup.zpowers t)) : G) :=
  rfl

theorem coe_derivedEquiv_conj [Finite G] (h : ExtSetting G t M)
    (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) (x : H) (m : ↥(derivedSeries H 1)) :
    ((h.derivedEquiv φ ⟨x * m * x⁻¹, (derivedSeries_normal H 1).conj_mem _ m.2 x⟩ : ↥M) : G) =
      ((φ x : ↥(M ⊔ Subgroup.zpowers t)) : G) * ((h.derivedEquiv φ m : ↥M) : G) *
        ((φ x : ↥(M ⊔ Subgroup.zpowers t)) : G)⁻¹ := by
  simp only [coe_derivedEquiv_apply, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem isSimpleGroup_derivedSeries_one [Finite G] (h : ExtSetting G t M)
    (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) : IsSimpleGroup ↥(derivedSeries H 1) :=
  haveI := h.simple
  (h.derivedEquiv φ).isSimpleGroup

theorem not_isMulCommutative_derivedSeries_one [Finite G] (h : ExtSetting G t M)
    (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) : ¬ IsMulCommutative ↥(derivedSeries H 1) := by
  rintro ⟨⟨hc⟩⟩
  apply h.not_isMulCommutative
  refine ⟨⟨fun a b => ?_⟩⟩
  have := congrArg (h.derivedEquiv φ)
    (hc ((h.derivedEquiv φ).symm a) ((h.derivedEquiv φ).symm b))
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

theorem center_eq_bot (h : ExtSetting G t M) (φ : H ≃* ↥(M ⊔ Subgroup.zpowers t)) :
    Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hφz : φ z ∈ Subgroup.center ↥(M ⊔ Subgroup.zpowers t) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨y, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, hz y]
  rw [h.center_sup_zpowers_eq_bot, Subgroup.mem_bot] at hφz
  exact Subgroup.mem_bot.mpr (φ.injective (hφz.trans φ.map_one.symm))

end ExtSetting

end CFSG.OddTranspositions.PartFour
