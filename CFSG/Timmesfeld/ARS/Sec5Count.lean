module

public import CFSG.Timmesfeld.ARS.Sec5Lines
public import CFSG.Timmesfeld.ARS.Sec3Plane

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

@[simp] theorem gen_empty : gen (∅ : Set (Subgroup G)) = ⊥ := by
  simp [gen]

theorem gen_insert (E : Subgroup G) (S : Set (Subgroup G)) : gen (insert E S) = E ⊔ gen S := by
  simp only [gen, iSup_insert]

section Count

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem inf_gen_eq_bot (hΔ : IsWeakTI R Δ) {S : Set (Subgroup G)} (hS : S ⊆ Δ)
    {E : Subgroup G} (hE : E ∈ Δ) (hle : ¬ E ≤ gen S) : E ⊓ gen S = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  by_contra hx1
  obtain ⟨T, hT, hTle, hxT⟩ := exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ hS hx.2 hx1
  apply hle
  rw [Sec3.eq_of_mem_of_mem hR hiso (hΔ.1 hE) (hΔ.1 hT) hx.1 hxT hx1]
  exact hTle

theorem exists_card_gen_finset_eq_pow (hΔ : IsWeakTI R Δ) {A : Subgroup G} (hA : A ∈ Δ)
    (s : Finset (Subgroup G)) (hs : (s : Set (Subgroup G)) ⊆ Δ) :
    ∃ m : ℕ, Nat.card ↥(gen (s : Set (Subgroup G))) = Nat.card A ^ m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert E s hEs ih =>
    rw [Finset.coe_insert] at hs ⊢
    have hs' : (s : Set (Subgroup G)) ⊆ Δ := (Set.subset_insert _ _).trans hs
    obtain ⟨m, hm⟩ := ih hs'
    have hEΔ : E ∈ Δ := hs (Set.mem_insert _ _)
    rw [gen_insert]
    by_cases hle : E ≤ gen (s : Set (Subgroup G))
    · exact ⟨m, by rw [sup_of_le_right hle, hm]⟩
    have hinf := inf_gen_eq_bot hR hiso hnd hΩ hΔ hs' hEΔ hle
    have hcomm : Commuting E (gen (s : Set (Subgroup G))) :=
      (commuting_gen_of_isWeakTI_of hR hiso hnd hΔ).mono (le_gen hEΔ) (gen_mono hs')
    refine ⟨m + 1, ?_⟩
    rw [le_antisymm (card_sup_le_of_commuting hcomm) (card_mul_card_le_card_sup hinf), hm,
      hR.card_eq (hΔ.1 hEΔ) (hΔ.1 hA), pow_succ, mul_comm]

theorem exists_card_gen_eq_pow (hΔ : IsWeakTI R Δ) {A : Subgroup G} (hA : A ∈ Δ) :
    ∃ m : ℕ, Nat.card ↥(gen Δ) = Nat.card A ^ m := by
  have hfin := Set.toFinite Δ
  obtain ⟨m, hm⟩ := exists_card_gen_finset_eq_pow hR hiso hnd hΩ hΔ hA hfin.toFinset (by simp)
  rw [Set.Finite.coe_toFinset] at hm
  exact ⟨m, hm⟩

theorem card_mul_card_sub_one (hΔ : IsWeakTI R Δ) {A : Subgroup G} (hA : A ∈ Δ) :
    Nat.card Δ * (Nat.card A - 1) = Nat.card ↥(gen Δ) - 1 := by
  classical
  let f : (Σ D : Δ, {x : G // x ∈ D.1 ∧ x ≠ 1}) → {x : G // x ∈ gen Δ ∧ x ≠ 1} :=
    fun p => ⟨p.2.1, le_gen p.1.2 p.2.2.1, p.2.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨D, x, hx, hx1⟩ ⟨D', x', hx', hx'1⟩ h
      have hxx : x = x' := congrArg Subtype.val h
      subst hxx
      have hDD : D = D' :=
        Subtype.ext (Sec3.eq_of_mem_of_mem hR hiso (hΔ.1 D.2) (hΔ.1 D'.2) hx hx' hx1)
      subst hDD
      rfl
    · rintro ⟨x, hx, hx1⟩
      obtain ⟨T, hT, -, hxT⟩ := exists_mem_le_of_mem_gen hR hiso hnd hΩ hΔ subset_rfl hx hx1
      exact ⟨⟨⟨T, hT⟩, x, hxT, hx1⟩, rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  have : Fintype Δ := Fintype.ofFinite Δ
  rw [Nat.card_sigma, Plane.card_subtype_mem_ne_one] at hcard
  rw [← hcard]
  calc Nat.card Δ * (Nat.card A - 1) = ∑ _D : Δ, (Nat.card A - 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
    _ = ∑ D : Δ, Nat.card {x : G // x ∈ D.1 ∧ x ≠ 1} :=
        Finset.sum_congr rfl fun D _ => by
          rw [Plane.card_subtype_mem_ne_one, hR.card_eq (hΔ.1 D.2) (hΔ.1 hA)]

end Count

end Sec5

end CFSG.Timmesfeld.ARS
