module

public import CFSG.Quasithin.EmptyFaithful.S153QSL1
public import CFSG.Quasithin.EmptyFaithful.S153QPD5

public section

namespace CFSG.Quasithin.QP

open Matrix CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Conj

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_conj_unitriangular_normalizes (hn : 1 ≤ n)
    {Ū X : Subgroup (SpecialLinearGroup (Fin n) F)} (hŪ : IsSylowTwoOf Ū ⊤)
    (hN : Ū ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin n) F))) :
    ∃ c : SpecialLinearGroup (Fin n) F ≃* SpecialLinearGroup (Fin n) F,
      unitriangular n F ≤ Subgroup.normalizer ((X.map c.toMonoidHom : Subgroup _) :
        Set (SpecialLinearGroup (Fin n) F)) := by
  obtain ⟨g, hg⟩ := exists_conj_unitriangular hn hŪ
  let c : SpecialLinearGroup (Fin n) F ≃* SpecialLinearGroup (Fin n) F := MulAut.conj g⁻¹
  refine ⟨c, ?_⟩
  intro u hu
  rw [← Subgroup.map_equiv_normalizer_eq X c]
  refine ⟨g * u * g⁻¹, hN (hg ▸ ⟨u, hu, rfl⟩), ?_⟩
  simp [c, mul_assoc]

end Conj

section Main

variable {F : Type} [Field F] [Finite F]

theorem false_of_sylow_solv2 (hF : Nat.card F = 2) {d : ℕ} (hd : d = 4 ∨ d = 5)
    {S X : Subgroup (SpecialLinearGroup (Fin d) F)} (hS : IsSylowTwoOf S ⊤)
    (hN : S ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin d) F)))
    (hX : IsPGroup 2 ↥⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆)
    {g : SpecialLinearGroup (Fin d) F} (hgX : g ∈ X) (hg : orderOf g = 5) : False := by
  have : CharP F 2 := by
    let _ := Fintype.ofFinite F
    exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  obtain ⟨c, hc⟩ := exists_conj_unitriangular_normalizes (by rcases hd with h | h <;> omega) hS hN
  let ε : ↥X ≃* ↥(X.map c.toMonoidHom) := X.equivMapOfInjective c.toMonoidHom c.injective
  have hX₀ : IsPGroup 2 ↥⁅(⊤ : Subgroup ↥(X.map c.toMonoidHom)),
      (⊤ : Subgroup ↥(X.map c.toMonoidHom))⁆ :=
    solv2_of_surjective ε.toMonoidHom ε.surjective hX
  have hg₀X : c g ∈ X.map c.toMonoidHom := ⟨g, hgX, rfl⟩
  have hg₀5 : orderOf (c g) = 5 := by rw [MulEquiv.orderOf_eq]; exact hg
  have h5 : (c g) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (c g)
    rwa [hg₀5] at this
  have h1 : c g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg₀5
    omega
  rcases hd with rfl | rfl
  · exact false_of_solv2_normalizes_sl4 hF hc hX₀ hg₀X h5 h1
  · exact false_of_solv2_normalizes_sl5 hF hc hX₀ hg₀X h5 h1

end Main

end CFSG.Quasithin.QP
