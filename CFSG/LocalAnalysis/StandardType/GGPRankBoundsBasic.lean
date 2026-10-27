module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.StandardType

namespace PRankBounds

open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

section Comap

variable {G H : Type*} [Group G] [Group H]

theorem isElemAbelian_comap_of_inj {p : ℕ} (ψ : H →* G) (hψ : Function.Injective ψ)
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsElemAbelian p (E.comap ψ) := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hψ
    have h := congrArg Subtype.val ((isMulCommutative_iff.mp hE.1)
      (⟨ψ (a : H), a.2⟩ : E) ⟨ψ (b : H), b.2⟩)
    change ψ ((a : H) * b) = ψ ((b : H) * a)
    rw [map_mul, map_mul]
    exact h
  · apply hψ
    rw [map_pow, map_one]
    exact hE.2 _ hx

theorem comap_le_normalizer_comap (ψ : H →* G) {E T : Subgroup G}
    (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    E.comap ψ ≤ Subgroup.normalizer ((T.comap ψ : Subgroup H) : Set H) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro t
  have h := Subgroup.mem_normalizer_iff.mp (hET he) (ψ t)
  simp only [Subgroup.mem_comap, map_mul, map_inv] at h ⊢
  exact h

end Comap

section Conj

variable {G : Type*} [Group G]

theorem conj_mem_of_mem_normalizer {H : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H) : m * x * m⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hm x).mp hx

@[expose] def normConj (H : Subgroup G) : Subgroup.normalizer (H : Set G) →* MulAut H where
  toFun m :=
    { toFun := fun x => ⟨(m : G) * x * (m : G)⁻¹, conj_mem_of_mem_normalizer m.2 x.2⟩
      invFun := fun x => ⟨(m : G)⁻¹ * x * (m : G)⁻¹⁻¹,
        conj_mem_of_mem_normalizer (inv_mem m.2) x.2⟩
      left_inv := fun x => Subtype.ext (by
        change (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * (m : G)⁻¹⁻¹ = x
        group)
      right_inv := fun x => Subtype.ext (by
        change (m : G) * ((m : G)⁻¹ * x * (m : G)⁻¹⁻¹) * (m : G)⁻¹ = x
        group)
      map_mul' := fun x y => Subtype.ext (by
        change (m : G) * ((x : G) * y) * (m : G)⁻¹ =
          (m : G) * x * (m : G)⁻¹ * ((m : G) * y * (m : G)⁻¹)
        group) }
  map_one' := by
    ext x
    change ((1 : G) * x * (1 : G)⁻¹) = x
    group
  map_mul' := fun a b => by
    ext x
    change ((a : G) * b) * x * ((a : G) * b)⁻¹ = (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
    group

theorem normConj_apply (H : Subgroup G) (m : Subgroup.normalizer (H : Set G)) (x : H) :
    ((normConj H m x : H) : G) = (m : G) * x * (m : G)⁻¹ :=
  rfl

theorem mem_of_normConj_mem_inner {H : Subgroup G}
    (hC : Subgroup.centralizer (H : Set G) = ⊥) {m : Subgroup.normalizer (H : Set G)}
    (h : normConj H m ∈ inner H) : (m : G) ∈ H := by
  obtain ⟨x₀, hx₀⟩ := h
  have hcent : (x₀ : G)⁻¹ * m ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut H => ((φ ⟨x, hx⟩ : H) : G)) hx₀
    simp only [MulAut.conj_apply, normConj_apply] at h1
    change (x₀ : G) * x * (x₀ : G)⁻¹ = (m : G) * x * (m : G)⁻¹ at h1
    calc x * ((x₀ : G)⁻¹ * m) = (x₀ : G)⁻¹ * ((x₀ : G) * x * (x₀ : G)⁻¹) * m := by group
      _ = (x₀ : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * m := by rw [h1]
      _ = (x₀ : G)⁻¹ * m * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  rw [← hcent]
  exact x₀.2

end Conj

end PRankBounds

end CFSG.StandardType
