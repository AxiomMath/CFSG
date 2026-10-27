module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Localization.Module

public section

namespace CFSG.StandardType.RCKRP

theorem rckSU3_exists_span_basis {n r : ℕ} (Ψ : Set (Fin n → ℤ))
    (hr : Module.finrank ℚ (Submodule.span ℚ ((fun γ (i : Fin n) => (γ i : ℚ)) '' Ψ)) ≤ r) :
    ∃ β : Fin r → (Fin n → ℤ), ∀ γ ∈ Ψ, γ ∈ Submodule.span ℤ (Set.range β) := by
  classical
  let Λ : Submodule ℤ (Fin n → ℤ) := Submodule.span ℤ Ψ
  let S : Submodule ℚ (Fin n → ℚ) := Submodule.span ℚ ((fun γ (i : Fin n) => (γ i : ℚ)) '' Ψ)
  obtain ⟨m, bΛ⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) Λ
  have hm : m ≤ r := by
    let castMap : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) := LinearMap.piMap (fun _ => Algebra.linearMap ℤ ℚ)
    have h_ind_Z : LinearIndependent ℤ (fun i : Fin m => ((bΛ i : Λ) : Fin n → ℤ)) := by
      exact bΛ.linearIndependent.map' (Submodule.subtype Λ)
        (LinearMap.ker_eq_bot_of_injective (f := Submodule.subtype Λ) Subtype.val_injective)
    have h_ind_Q_Z : LinearIndependent ℤ (fun i : Fin m => castMap ((bΛ i : Λ) : Fin n → ℤ)) := by
      apply LinearIndependent.map'
      · exact h_ind_Z
      · apply LinearMap.ker_eq_bot_of_injective
        intro v w h
        ext i
        have hcast : (v i : ℚ) = (w i : ℚ) := by simpa [castMap] using congrFun h i
        exact Int.cast_injective hcast
    have h_ind_Q : LinearIndependent ℚ (fun i : Fin m => castMap ((bΛ i : Λ) : Fin n → ℤ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).1 h_ind_Q_Z
    have h_mem_S : ∀ i : Fin m, castMap ((bΛ i : Λ) : Fin n → ℤ) ∈ S := by
      intro i
      have hΛ_le_S : ∀ v ∈ Λ, castMap v ∈ S := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem γ hγ => exact Submodule.subset_span ⟨γ, hγ, rfl⟩
        | zero => change (0 : Fin n → ℚ) ∈ S; exact S.zero_mem
        | add x y hx hy hxS hyS => rw [map_add]; exact S.add_mem hxS hyS
        | smul c x hx hxS =>
            have : c • castMap x = (c : ℚ) • castMap x := by rw [Int.cast_smul_eq_zsmul]
            rw [map_smul, this]
            exact S.smul_mem (c : ℚ) hxS
      exact hΛ_le_S _ (bΛ i).2
    have h_ind_S : LinearIndependent ℚ
        (fun i : Fin m => (⟨castMap ((bΛ i : Λ) : Fin n → ℤ), h_mem_S i⟩ : S)) := by
      exact LinearIndependent.of_comp S.subtype h_ind_Q
    have h_card : Fintype.card (Fin m) ≤ Module.finrank ℚ S := by
      exact LinearIndependent.fintype_card_le_finrank h_ind_S
    calc
      m = Fintype.card (Fin m) := by simp
      _ ≤ Module.finrank ℚ S := h_card
      _ ≤ r := hr
  let β : Fin r → (Fin n → ℤ) := fun j =>
    if h : j.val < m then ((bΛ ⟨j.val, h⟩ : Λ) : Fin n → ℤ) else 0
  refine ⟨β, fun γ hγ => ?_⟩
  have hγΛ : γ ∈ Λ := Submodule.subset_span hγ
  have h_mem_span_Λ : (⟨γ, hγΛ⟩ : Λ) ∈ Submodule.span ℤ (Set.range bΛ) := bΛ.mem_span ⟨γ, hγΛ⟩
  have h_image_mem : γ ∈ (Submodule.subtype Λ) '' (Submodule.span ℤ (Set.range bΛ)) :=
    Submodule.mem_map_of_mem h_mem_span_Λ
  have hγ_span_b : γ ∈ Submodule.span ℤ ((Submodule.subtype Λ) '' Set.range bΛ) :=
    Submodule.image_span_subset_span (Submodule.subtype Λ) (Set.range bΛ) h_image_mem
  have h_subset_image : (Submodule.subtype Λ) '' Set.range bΛ ⊆
      Set.range (fun i => ((bΛ i : Λ) : Fin n → ℤ)) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := hy
    exact ⟨i, rfl⟩
  have hγ_span_b' : γ ∈ Submodule.span ℤ (Set.range (fun i => ((bΛ i : Λ) : Fin n → ℤ))) :=
    Submodule.span_mono h_subset_image hγ_span_b
  have h_subset : Set.range (fun i : Fin m => ((bΛ i : Λ) : Fin n → ℤ)) ⊆ Set.range β := by
    rintro x ⟨i, rfl⟩
    refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
    simp [β, i.isLt]
  exact Submodule.span_mono h_subset hγ_span_b'

theorem rckSU3_char_trivial_of_span {n r : ℕ} {M : Type*} [Group M] {Ψ : Set (Fin n → ℤ)}
    {β : Fin r → (Fin n → ℤ)} (hβ : ∀ γ ∈ Ψ, γ ∈ Submodule.span ℤ (Set.range β))
    (χ : Multiplicative (Fin n → ℤ) →* M)
    (h : ∀ j, χ (Multiplicative.ofAdd (β j)) = 1) :
    ∀ γ ∈ Ψ, χ (Multiplicative.ofAdd γ) = 1 := by
  intro γ hγ
  have hspan : ∀ v ∈ Submodule.span ℤ (Set.range β), χ (Multiplicative.ofAdd v) = 1 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact h j
    | zero =>
        simp
    | add x y hx hy hxS hyS =>
        rw [ofAdd_add, map_mul, hxS, hyS, one_mul]
    | smul c x hx hxS =>
        rw [ofAdd_zsmul, map_zpow, hxS]
        simp
  exact hspan γ (hβ γ hγ)

theorem rckSU3_pow_eq_one {F : Type*} [Field F] {p : ℕ} (hp : 0 < p) :
    Finite {u : Fˣ // u ^ p = 1} ∧ Nat.card {u : Fˣ // u ^ p = 1} ≤ p := by
  haveI : NeZero p := NeZero.of_pos hp
  let e : {u : Fˣ // u ^ p = 1} ≃ rootsOfUnity p F := {
    toFun := fun u => ⟨u.1, (mem_rootsOfUnity p u.1).2 u.2⟩,
    invFun := fun u => ⟨u.1, (mem_rootsOfUnity p u.1).1 u.2⟩,
    left_inv := fun _ => rfl,
    right_inv := fun _ => rfl }
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  calc
    Nat.card {u : Fˣ // u ^ p = 1} = Nat.card (rootsOfUnity p F) := Nat.card_congr e
    _ ≤ p := card_rootsOfUnity F p

theorem rckSU3_card_le_mul {X : Type*} [Group X] [Finite X] (B H : Subgroup X) (hHB : H ≤ B)
    {S : Type*} [Finite S] (f : ↥B → S)
    (hf : ∀ b b' : ↥B, f b = f b' → ((b⁻¹ * b' : ↥B) : X) ∈ H) :
    Nat.card ↥B ≤ Nat.card ↥H * Nat.card S := by
  let H' : Subgroup ↥B := H.subgroupOf B
  have hH' : Nat.card ↥H' = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHB).toEquiv
  let g : (↥B ⧸ H') → S := fun c => f c.out
  have hg : Function.Injective g := by
    intro c c' h
    have hmem : (((c.out)⁻¹ * c'.out : ↥B) : X) ∈ H := hf c.out c'.out h
    have hmem' : (c.out)⁻¹ * c'.out ∈ H' := by
      rw [Subgroup.mem_subgroupOf]
      exact hmem
    have heq : (c.out : ↥B ⧸ H') = (c'.out : ↥B ⧸ H') := QuotientGroup.eq.2 hmem'
    simpa [Quotient.out_eq'] using heq
  have h1 : Nat.card (↥B ⧸ H') ≤ Nat.card S := Nat.card_le_card_of_injective g hg
  have h2 : Nat.card ↥B = Nat.card ↥H' * H'.index :=
    (Subgroup.card_mul_index H').symm
  have h3 : H'.index = Nat.card (↥B ⧸ H') := rfl
  calc
    Nat.card ↥B = Nat.card ↥H' * H'.index := h2
    _ = Nat.card ↥H * Nat.card (↥B ⧸ H') := by rw [hH', h3]
    _ ≤ Nat.card ↥H * Nat.card S := Nat.mul_le_mul_left _ h1

end CFSG.StandardType.RCKRP

end
