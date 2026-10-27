module

public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.RankThree.PartOne

@[expose] def CompGoodAt (p : ℕ) {T : Type} [Group T] (b : T) : Prop :=
  ∀ E : Subgroup T, IsComponentOf (Subgroup.centralizer ({b} : Set T)) E →
    E ⊓ Subgroup.centralizer (E : Set T) = ⊥ ∧ p ∣ Nat.card E

theorem compGoodAt_of_mulEquiv {p : ℕ} {T T' : Type} [Group T] [Group T'] (φ : T ≃* T') {b : T}
    (h : CompGoodAt p (φ b)) : CompGoodAt p b := by
  intro E hE
  have hE' := isComponentOf_map_mulEquiv φ hE
  rw [map_centralizer_singleton_mulEquiv_good φ b] at hE'
  obtain ⟨hZ, hp⟩ := h _ hE'
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzE, hzC⟩ := Subgroup.mem_inf.1 hz
    have h1 : φ z ∈ E.map φ.toMonoidHom ⊓ Subgroup.centralizer (E.map φ.toMonoidHom : Set T') := by
      refine Subgroup.mem_inf.2 ⟨⟨z, hzE, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hzC y hy
      change φ y * φ z = φ z * φ y
      rw [← map_mul, ← map_mul, this]
    rw [hZ, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact φ.injective (h1.trans (map_one φ).symm)
  · rwa [Subgroup.card_map_of_injective φ.injective] at hp

theorem compGoodAt_conj {p : ℕ} {T : Type} [Group T] {b : T} (g : T)
    (h : CompGoodAt p (g * b * g⁻¹)) : CompGoodAt p b :=
  compGoodAt_of_mulEquiv (MulAut.conj g) (by simpa [MulAut.conj_apply] using h)

end CFSG.RankThree.PartOne.FOCD
