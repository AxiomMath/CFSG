module

public import CFSG.RankThree.Transfer.YoshidaCore
public import Mathlib.GroupTheory.Focal

public section

namespace CFSG.RankThree.Transfer

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G)

local notation "N" => Subgroup.normalizer (((P : Sylow p G) : Subgroup G) : Set G)

omit [Finite G] hp in
theorem mem_of_mem_sylow_subtype {x : N}
    (hx : x ∈ ((P.subtype Subgroup.le_normalizer : Sylow p N) : Subgroup N)) :
    (x : G) ∈ (P : Subgroup G) := by
  rwa [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hx

theorem surjective_transfer_transferFocal
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))) :
    Function.Surjective
      ((P.subtype Subgroup.le_normalizer : Sylow p N) : Subgroup N).transferFocal.transfer := by
  set PN : Sylow p N := P.subtype Subgroup.le_normalizer with hPN
  set ρ := (PN : Subgroup N).transferFocal with hρ
  by_contra hsurj
  have hrange : ρ.transfer.range ≠ ⊤ := fun h => hsurj (MonoidHom.range_eq_top.mp h)
  have hA : IsPGroup p (↥(PN : Subgroup N) ⧸ (PN : Subgroup N).focalSubgroupOf) :=
    PN.isPGroup'.to_quotient _
  obtain ⟨χ, hχs, hχ⟩ := exists_surjective_zmod_of_ne_top hA hrange
  have hμ : ∃ u : (P : Subgroup G),
      (χ.comp ρ) (Subgroup.inclusion Subgroup.le_normalizer u) ≠ 1 := by
    obtain ⟨a, ha⟩ := hχs (Multiplicative.ofAdd 1)
    obtain ⟨y, hy⟩ := Subgroup.focalSubgroupOf.pow_index_surjective PN a
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    have hwP : (((w : N) : G)) ∈ (P : Subgroup G) := mem_of_mem_sylow_subtype P w.2
    have hy' : (w : ↥(PN : Subgroup N) ⧸ (PN : Subgroup N).focalSubgroupOf) ^
        (PN : Subgroup N).index = a := hy
    refine ⟨⟨_, hwP⟩, ?_⟩
    have hincl : Subgroup.inclusion Subgroup.le_normalizer (⟨_, hwP⟩ : (P : Subgroup G)) =
        (w : N) := Subtype.ext rfl
    rw [MonoidHom.coe_comp, Function.comp_apply, hincl, hρ, Subgroup.transferFocal_eq_pow]
    change χ ((w : ↥(PN : Subgroup N) ⧸ (PN : Subgroup N).focalSubgroupOf) ^
      (PN : Subgroup N).index) ≠ 1
    rw [hy', ha]
    exact fun h => one_ne_zero (ofAdd_eq_one.mp h)
  have hV : ∀ g : G, (χ.comp ρ).transfer g = 1 := by
    intro g
    rw [transfer_comp, MonoidHom.coe_comp, Function.comp_apply]
    exact MonoidHom.mem_ker.mp (hχ ⟨g, rfl⟩)
  obtain ⟨Ψ, hΨ⟩ := exists_surjective_regularWreathProduct_of_transfer_eq_one P (χ.comp ρ) hμ hV
  exact (hW Ψ.ker).false (QuotientGroup.quotientKerEquivOfSurjective Ψ hΨ)

theorem card_focalSubgroupOf_subtype :
    Nat.card ((P.subtype Subgroup.le_normalizer : Sylow p N) : Subgroup N).focalSubgroupOf =
      Nat.card ↥((P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N)) := by
  set PN : Sylow p N := P.subtype Subgroup.le_normalizer with hPN
  have h1 : ((PN : Subgroup N).focalSubgroupOf).map (PN : Subgroup N).subtype =
      commutator N ⊓ (PN : Subgroup N) := by
    rw [Subgroup.map_focalSubgroupOf, Subgroup.commutator_inf_eq_focalSubgroup]
  have h2 : (commutator N ⊓ (PN : Subgroup N)).map (Subgroup.subtype N) =
      (P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N) := by
    rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective N), hPN, Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer, inf_comm]
  rw [← h2, Subgroup.card_map_of_injective (Subgroup.subtype_injective N), ← h1,
    Subgroup.card_map_of_injective (PN : Subgroup N).subtype_injective]

omit [Finite G] hp in
theorem card_sylow_subtype :
    Nat.card ((P.subtype Subgroup.le_normalizer : Sylow p N) : Subgroup N) =
      Nat.card (P : Subgroup G) := by
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective N), Sylow.coe_subtype,
    Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer]

theorem inf_commutator_eq_inf_map_commutator_normalizer
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal],
      IsEmpty ((↥(P : Subgroup G) ⧸ K) ≃* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)))) :
    (P : Subgroup G) ⊓ commutator G =
      (P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N) := by
  set PN : Sylow p N := P.subtype Subgroup.le_normalizer with hPN
  set A := ↥(PN : Subgroup N) ⧸ (PN : Subgroup N).focalSubgroupOf
  set V : G →* A := (PN : Subgroup N).transferFocal.transfer with hVdef
  have hV : Function.Surjective V := surjective_transfer_transferFocal P hW
  have hA : IsPGroup p A := PN.isPGroup'.to_quotient _
  have hVP : (P : Subgroup G).map V = ⊤ := by
    obtain ⟨k, hk⟩ := hA.index ((P : Subgroup G).map V)
    have hdvd := Subgroup.index_map_dvd (P : Subgroup G) hV
    rw [hk] at hdvd
    have hk0 : k = 0 := by
      by_contra hk0
      exact P.not_dvd_index ((dvd_pow_self p hk0).trans hdvd)
    rw [hk0, pow_zero] at hk
    exact Subgroup.index_eq_one.mp hk
  set K : Subgroup (P : Subgroup G) := (commutator G).subgroupOf P with hKdef
  have hK : K ≤ (V.comp (P : Subgroup G).subtype).ker := fun x hx =>
    Abelianization.commutator_subset_ker V (Subgroup.mem_subgroupOf.mp hx)
  have hlift : Function.Surjective (QuotientGroup.lift K _ hK) := by
    intro a
    have ha : a ∈ (P : Subgroup G).map V := hVP ▸ Subgroup.mem_top a
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨((⟨x, hx⟩ : (P : Subgroup G)) : ↥(P : Subgroup G) ⧸ K), rfl⟩
  have hcardA : Nat.card A ≤ K.index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_le_card_of_surjective _ hlift
  have hKcard : Nat.card K = Nat.card ↥((P : Subgroup G) ⊓ commutator G) := by
    rw [← Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective, hKdef,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hK1 := K.card_mul_index
  have hF1 := ((PN : Subgroup N).focalSubgroupOf).card_mul_index
  rw [card_focalSubgroupOf_subtype, card_sylow_subtype] at hF1
  rw [hKcard] at hK1
  have hAcard : Nat.card A = ((PN : Subgroup N).focalSubgroupOf).index :=
    (Subgroup.index_eq_card _).symm
  rw [hAcard] at hcardA
  have hle : (P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N) ≤
      (P : Subgroup G) ⊓ commutator G := by
    refine inf_le_inf_left _ ?_
    rw [Subgroup.map_subtype_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hPpos : 0 < Nat.card (P : Subgroup G) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have := Nat.mul_lt_mul_of_lt_of_le hlt hcardA hpos
  omega

theorem inf_map_commutator_normalizer_eq_commutator :
    (P : Subgroup G) ⊓ (commutator N).map (Subgroup.subtype N) = ⁅(P : Subgroup G), N⁆ := by
  rw [Subgroup.map_subtype_commutator]
  apply le_antisymm
  · set PN : Sylow p N := P.subtype Subgroup.le_normalizer with hPN
    have hmap : (commutator N ⊓ (PN : Subgroup N)).map (Subgroup.subtype N) =
        (P : Subgroup G) ⊓ ⁅N, N⁆ := by
      rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective N),
        Subgroup.map_subtype_commutator, hPN, Sylow.coe_subtype,
        Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer, inf_comm]
    rw [← hmap, Subgroup.commutator_inf_eq_focalSubgroup, Subgroup.focalSubgroup_def,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨-, x, hx, n, rfl⟩, rfl⟩
    have hxP : ((x : N) : G) ∈ (P : Subgroup G) := mem_of_mem_sylow_subtype P hx
    exact Subgroup.commutator_mem_commutator hxP n.2
  · apply le_inf
    · rw [Subgroup.commutator_le]
      intro x hx n hn
      have h := (Subgroup.mem_normalizer_iff.mp hn x⁻¹).mp (inv_mem hx)
      rw [commutatorElement_def]
      simpa [mul_assoc] using mul_mem hx h
    · exact Subgroup.commutator_mono Subgroup.le_normalizer le_rfl

theorem le_commutator_of_forall_isPGroup_quotient
    (h : ∀ (K : Subgroup G) [K.Normal], IsPGroup p (G ⧸ K) → K = ⊤) :
    (P : Subgroup G) ≤ commutator G := by
  have hker := h (P : Subgroup G).transferFocal.ker
    ((P.isPGroup'.to_quotient _).of_equiv
      (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf P).symm)
  have htriv : (P : Subgroup G).focalSubgroupOf = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy⟩ := Subgroup.transferFocal_surjective P
      (x : ↥(P : Subgroup G) ⧸ (P : Subgroup G).focalSubgroupOf)
    have hy1 : y ∈ (P : Subgroup G).transferFocal.ker := by
      rw [hker]
      exact Subgroup.mem_top y
    rw [MonoidHom.mem_ker.mp hy1] at hy
    exact (QuotientGroup.eq_one_iff x).mp hy.symm
  rw [Subgroup.focalSubgroupOf_def, Subgroup.subgroupOf_eq_top] at htriv
  exact htriv.trans (Subgroup.focalSubgroup_le_commutator _)

end CFSG.RankThree.Transfer

end
