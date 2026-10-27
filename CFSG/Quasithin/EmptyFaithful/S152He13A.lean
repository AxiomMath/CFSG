module

public import CFSG.Quasithin.Background.E2Seventeen
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace He13

variable {G : Type} [Group G]

theorem card_le_two_of_central_of_extraspecial_s3 [Finite G] {Y D K : Subgroup G} (hDY : D ≤ Y)
    (hD : E2.IsExtraspecialPlus 2 D) (φ : ↥Y →* Equiv.Perm (Fin 3)) (hφs : Function.Surjective φ)
    (hφk : φ.ker = D.subgroupOf Y) (hKY : K ≤ Y) (hK : ∀ k ∈ K, ∀ y ∈ Y, k * y = y * k) :
    Nat.card K ≤ 2 := by
  have key : ∀ ρ : Equiv.Perm (Fin 3), (∀ σ : Equiv.Perm (Fin 3), ρ * σ = σ * ρ) → ρ = 1 := by
    decide
  have hKD : K ≤ D := by
    intro k hk
    have hcen : ∀ σ : Equiv.Perm (Fin 3), φ ⟨k, hKY hk⟩ * σ = σ * φ ⟨k, hKY hk⟩ := by
      intro σ
      obtain ⟨y, rfl⟩ := hφs σ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hK k hk y y.2)
    have h1 : φ ⟨k, hKY hk⟩ = 1 := key _ hcen
    have h2 : (⟨k, hKY hk⟩ : ↥Y) ∈ φ.ker := h1
    rw [hφk] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hle : K.subgroupOf D ≤ Subgroup.center ↥D := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    exact (hK x hxK g (hDY g.2)).symm
  have : CFSG.IsExtraspecial 2 ↥D := hD.1
  have hc : Nat.card (Subgroup.center ↥D) = 2 := CFSG.IsExtraspecial.center_order_p 2 ↥D
  calc Nat.card K = Nat.card (K.subgroupOf D) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKD).toEquiv).symm
    _ ≤ Nat.card (Subgroup.center ↥D) := Subgroup.card_le_of_le hle
    _ = 2 := hc

theorem comm_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem centralizes_conjClosure {U V K H Mc : Subgroup G} (hU : IsElemAbelian 2 U)
    (hVU : V ≤ U) (hKU : K ≤ U) (hHMc : H ≤ Mc) (hKN : Mc ≤ Subgroup.normalizer (K : Set G)) :
    ∀ k ∈ K, ∀ y ∈ conjClosure V H, k * y = y * k := by
  have hle : conjClosure V H ≤ Subgroup.centralizer (K : Set G) := by
    refine conjClosure_le fun h hh v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hhN : h⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ (hKN (hHMc hh))
    have hk' : h⁻¹ * k * h ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp hhN k).mp hk
    have hcomm := comm_of_isElemAbelian hU (hKU hk') (hVU hv)
    calc k * (h * v * h⁻¹) = h * ((h⁻¹ * k * h) * v) * h⁻¹ := by group
      _ = h * (v * (h⁻¹ * k * h)) * h⁻¹ := by rw [hcomm]
      _ = h * v * h⁻¹ * k := by group
  intro k hk y hy
  exact ((Subgroup.mem_centralizer_iff.mp (hle hy)) k hk)

theorem eq_one_or_eq_of_card_le_two [Finite G] {A : Subgroup G} (hA : Nat.card A ≤ 2) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {x : G} (hx : x ∈ A) : x = 1 ∨ x = a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hxa⟩ := hcon
  have h3 : ({1, a, x} : Set G).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, a, x, Ne.symm ha1, Ne.symm hx1, Ne.symm hxa, rfl⟩
  have hsub : ({1, a, x} : Set G) ⊆ (A : Set G) := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact A.one_mem
    · exact ha
    · exact hx
  have hle : ({1, a, x} : Set G).ncard ≤ (A : Set G).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hA' : (A : Set G).ncard = Nat.card A := (Nat.card_coe_set_eq (A : Set G)).symm
  omega

end He13

end CFSG.Quasithin
