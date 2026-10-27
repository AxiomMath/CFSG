module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFourGroup
public import CFSG.GroupTheory.LocalCores.PrimeSetCoreIsomorphism
import CFSG.Adapters.WholeGroupLayer
public import CFSG.Assembly.Defs

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup

variable {M : Type*} [Group M]

structure AutModel (P R : Subgroup M) : Prop where
  le : P ≤ R
  conj_mem : ∀ x ∈ R, ∀ p ∈ P, x * p * x⁻¹ ∈ P
  surj : ∀ α : MulAut P, ∃ x ∈ R, ∀ p : P, ((α p : P) : M) = x * p * x⁻¹
  inj : ∀ x ∈ R, (∀ p ∈ P, x * p = p * x) → x = 1

namespace AutModel

variable {P R : Subgroup M} (h : AutModel P R)
include h

theorem eq_of_conj {x y : M} (hx : x ∈ R) (hy : y ∈ R)
    (hxy : ∀ p ∈ P, x * p * x⁻¹ = y * p * y⁻¹) : x = y := by
  have h1 := h.inj (y⁻¹ * x) (R.mul_mem (R.inv_mem hy) hx) fun p hp => by
    have e := hxy p hp
    calc y⁻¹ * x * p = y⁻¹ * (x * p * x⁻¹) * x := by group
      _ = y⁻¹ * (y * p * y⁻¹) * x := by rw [e]
      _ = p * (y⁻¹ * x) := by group
  rw [inv_mul_eq_one] at h1
  exact h1.symm

@[expose] noncomputable def elt (α : MulAut P) : M := Classical.choose (h.surj α)

theorem elt_mem (α : MulAut P) : h.elt α ∈ R := (Classical.choose_spec (h.surj α)).1

theorem elt_spec (α : MulAut P) (p : P) : ((α p : P) : M) = h.elt α * p * (h.elt α)⁻¹ :=
  (Classical.choose_spec (h.surj α)).2 p

theorem elt_eq {α : MulAut P} {x : M} (hx : x ∈ R) (hα : ∀ p : P, ((α p : P) : M) = x * p * x⁻¹) :
    h.elt α = x :=
  h.eq_of_conj (h.elt_mem α) hx fun p hp => by
    rw [← h.elt_spec α ⟨p, hp⟩, hα ⟨p, hp⟩]

@[expose] noncomputable def hom : MulAut P →* M where
  toFun := h.elt
  map_one' := h.elt_eq R.one_mem fun p => by simp
  map_mul' α β := h.elt_eq (R.mul_mem (h.elt_mem α) (h.elt_mem β)) fun p => by
    rw [MulAut.mul_apply, h.elt_spec α, h.elt_spec β]
    group

theorem hom_apply (α : MulAut P) : h.hom α = h.elt α := rfl

theorem hom_injective : Function.Injective h.hom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker, hom_apply] at hα
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun p => Subtype.ext ?_
  rw [h.elt_spec α, hα]
  simp

end AutModel

section Embed

variable {P R : Subgroup M} (h : AutModel P R) {X : Type*} [Group X] (S : Subgroup X) [S.Normal]
  (θ : S ≃* P)

@[expose] noncomputable def transportAut : X →* MulAut P :=
  (MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal

theorem transportAut_apply (x : X) (p : P) :
    transportAut S θ x p = θ (MulAut.conjNormal x (θ.symm p)) := rfl

@[expose] noncomputable def AutModel.embed : X →* M := h.hom.comp (transportAut S θ)

theorem AutModel.embed_mem (x : X) : h.embed S θ x ∈ R := h.elt_mem _

theorem AutModel.embed_coe (s : S) : h.embed S θ s = θ s := by
  refine h.elt_eq (h.le (θ s).2) fun p => ?_
  rw [transportAut_apply]
  have e : MulAut.conjNormal (s : X) (θ.symm p) = s * θ.symm p * s⁻¹ :=
    Subtype.ext (MulAut.conjNormal_apply _ _)
  rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem AutModel.embed_injective (hC : centralizer (S : Set X) = ⊥) :
    Function.Injective (h.embed S θ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, AutModel.embed, MonoidHom.comp_apply, ← map_one h.hom] at hx
  have h1 := h.hom_injective hx
  rw [← hC]
  rw [mem_centralizer_iff]
  intro s hs
  have h2 := congrArg (fun α : MulAut P => (α (θ ⟨s, hs⟩) : P)) h1
  simp only [transportAut_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
  have h3 := congrArg Subtype.val (θ.injective h2)
  rw [MulAut.conjNormal_apply] at h3
  calc s * x = x * s * x⁻¹ * x := by rw [h3]
    _ = x * s := by group

theorem AutModel.mem_centralizer_iff (hC : centralizer (S : Set X) = ⊥) (t : X) (s : S) :
    (s : X) ∈ centralizer ({t} : Set X) ↔
      ((θ s : P) : M) ∈ centralizer ({h.embed S θ t} : Set M) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← h.embed_coe S θ s,
    ← map_mul, ← map_mul]
  exact (h.embed_injective S θ hC).eq_iff.symm

@[expose] noncomputable def AutModel.centralizerEquiv (hC : centralizer (S : Set X) = ⊥) (t : X) :
    ↥(S ⊓ centralizer ({t} : Set X)) ≃* ↥(P ⊓ centralizer ({h.embed S θ t} : Set M)) where
  toFun s := ⟨θ ⟨s, (mem_inf.mp s.2).1⟩, (θ ⟨s, (mem_inf.mp s.2).1⟩).2,
    (h.mem_centralizer_iff S θ hC t ⟨s, (mem_inf.mp s.2).1⟩).1 (mem_inf.mp s.2).2⟩
  invFun p := ⟨θ.symm ⟨p, (mem_inf.mp p.2).1⟩, (θ.symm ⟨p, (mem_inf.mp p.2).1⟩).2,
    (h.mem_centralizer_iff S θ hC t (θ.symm ⟨p, (mem_inf.mp p.2).1⟩)).2 (by
      rw [MulEquiv.apply_symm_apply]; exact (mem_inf.mp p.2).2)⟩
  left_inv s := by simp
  right_inv p := by simp
  map_mul' s s' := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [show (⟨(s * s' : X), _⟩ : S) = ⟨s, (mem_inf.mp s.2).1⟩ * ⟨s', (mem_inf.mp s'.2).1⟩ from
      rfl, map_mul]
    rfl

end Embed

theorem odd_card_map_le_of_index_le_two {X : Type*} [Group X] [Finite X] (S : Subgroup X)
    [S.Normal] (hX : Nat.card X ≤ 2 * Nat.card S) {N : Subgroup X} (hN : Odd (Nat.card N)) :
    N ≤ S := by
  have hdvd1 : Nat.card (N.map (QuotientGroup.mk' S)) ∣ Nat.card N := card_map_dvd _ _
  have hdvd2 : Nat.card (N.map (QuotientGroup.mk' S)) ∣ Nat.card (X ⧸ S) :=
    card_subgroup_dvd_card _
  have hidx : Nat.card (X ⧸ S) ≤ 2 := by
    have h := S.card_eq_card_quotient_mul_card_subgroup
    have hS : 0 < Nat.card S := Nat.card_pos
    by_contra hc
    have hc' : 3 ≤ Nat.card (X ⧸ S) := by omega
    have : 3 * Nat.card S ≤ Nat.card (X ⧸ S) * Nat.card S := Nat.mul_le_mul_right _ hc'
    omega
  have h1 : Nat.card (N.map (QuotientGroup.mk' S)) = 1 := by
    have hpos : 0 < Nat.card (N.map (QuotientGroup.mk' S)) := Nat.card_pos
    have hle : Nat.card (N.map (QuotientGroup.mk' S)) ≤ 2 :=
      (Nat.le_of_dvd (Nat.card_pos) hdvd2).trans hidx
    have hodd : Odd (Nat.card (N.map (QuotientGroup.mk' S))) := Odd.of_dvd_nat hN hdvd1
    interval_cases h : Nat.card (N.map (QuotientGroup.mk' S))
    · rfl
    · exact absurd hodd (by decide)
  rw [card_eq_one, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
  exact h1

theorem oddCore_centralizer_eq_bot {P R : Subgroup M} [Finite M] (h : AutModel P R)
    (hidx : Nat.card R ≤ 2 * Nat.card P)
    (hodd : ∀ τ ∈ R, orderOf τ = 2 → CFSG.oddCore ↥(P ⊓ centralizer ({τ} : Set M)) = ⊥)
    {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal] (θ : S ≃* P)
    (hC : centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := by
  have hinj := h.embed_injective S θ hC
  have hτ : orderOf (h.embed S θ t) = 2 := by rw [orderOf_injective _ hinj, ht]
  have hCS : CFSG.oddCore ↥(S ⊓ centralizer ({t} : Set X)) = ⊥ := by
    have e := h.centralizerEquiv S θ hC t
    have h1 := hodd _ (h.embed_mem S θ t) hτ
    rw [CFSG.oddCore_eq_piCore] at h1 ⊢
    rw [← CFSG.LocalCores.prime_set_core_isomorphism e.symm, h1, Subgroup.map_bot]
  have hX : Nat.card X ≤ 2 * Nat.card S := by
    have h1 : Nat.card X = Nat.card (h.embed S θ).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have h2 : (h.embed S θ).range ≤ R := by
      rintro _ ⟨x, rfl⟩
      exact h.embed_mem S θ x
    rw [h1, Nat.card_congr θ.toEquiv]
    exact (Subgroup.card_le_of_le h2).trans hidx
  set C := centralizer ({t} : Set X)
  set N := (CFSG.oddCore C).map C.subtype
  have hNodd : Odd (Nat.card N) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact CFSG.ComponentClassification.SmallLocal.odd_card_oddCore
  have hNS : N ≤ S := odd_card_map_le_of_index_le_two S hX hNodd
  have hNC : N ≤ C := map_subtype_le _
  let N' : Subgroup ↥(S ⊓ C) := N.subgroupOf (S ⊓ C)
  have hN'n : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨m, hm, hmn⟩ := mem_map.mp hn
    have hgC : (g : X) ∈ C := (mem_inf.mp g.2).2
    have := (CFSG.oddCore_normal (G := C)).conj_mem m hm ⟨g, hgC⟩
    refine mem_map.mpr ⟨_, this, ?_⟩
    have hmn' : (m : X) = n := hmn
    simp [hmn']
  have hN'card : Nat.card N' = Nat.card N := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (le_inf hNS hNC)).toEquiv]
  have hN'bot : N' = ⊥ := by
    have := CFSG.ComponentClassification.SmallLocal.le_oddCore_of_normal_odd hN'n
      (hN'card ▸ hNodd)
    rw [hCS, le_bot_iff] at this
    exact this
  have hNbot : N = ⊥ := by
    rw [← Subgroup.card_eq_one, ← hN'card, hN'bot, Subgroup.card_bot]
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hNbot

theorem centralizer_generalizedFitting_eq_bot {X : Type*} [Group X] [Finite X]
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) :
    centralizer (CFSG.generalizedFitting X : Set X) = ⊥ :=
  CFSG.Adapters.centralizer_generalizedFitting_eq_bot_of_isSimpleGroup X hF hnab

end CFSG.Sporadic.SmallOddCore
