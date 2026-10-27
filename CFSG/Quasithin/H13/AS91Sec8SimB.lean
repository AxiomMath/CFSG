module

public import CFSG.Quasithin.H13.AS91Sec8Defs

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction
open scoped Pointwise

universe u v

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]

private theorem autPres_of_factor {H : Type*} [Group H] (A B : Subgroup H)
    {φ₀ φ₁ φ₂ : ↥A ≃* ↥A} (h₀ : autPres A B φ₀) (h₂ : autFix A B φ₂)
    (hfac : ∀ a : ↥A, ((φ₀ a : ↥A) : H) = ((φ₁ (φ₂ a) : ↥A) : H)) :
    autPres A B φ₁ := by
  intro a
  constructor
  · intro ha
    have hφa : ((φ₀ a : ↥A) : H) = ((φ₁ a : ↥A) : H) := by
      rw [hfac a, Subtype.ext (h₂ a ha)]
    rw [← hφa]
    exact (h₀ a).mp ha
  · intro ha
    obtain ⟨w, hw⟩ : ∃ w : ↥A, φ₂ w = a := ⟨φ₂.symm a, φ₂.apply_symm_apply a⟩
    have hφw : ((φ₀ w : ↥A) : H) = ((φ₁ a : ↥A) : H) := by
      rw [hfac w, hw]
    have hφ0B : ((φ₀ w : ↥A) : H) ∈ B := by
      rw [hφw]
      exact ha
    have hwB : ((w : ↥A) : H) ∈ B := (h₀ w).mpr hφ0B
    have hfix : ((φ₂ w : ↥A) : H) = w := h₂ w hwB
    rw [hw] at hfix
    rw [hfix]
    exact hwB

theorem exists_phi_psi {I : Subgroup G} {x y : X} (hV : HypV I x y)
    (θ : ↥(I ⊓ stabilizer G x) ≃* ↥(I ⊓ stabilizer G x)) :
    ∃ (φ : ↥I ≃* ↥I) (ψ : ↥(stabilizer G x) ≃* ↥(stabilizer G x)),
      autPres I (I ⊓ stabilizer G x) φ ∧ autPres (stabilizer G x) (I ⊓ stabilizer G x) ψ ∧
      (∀ b : ↥(I ⊓ stabilizer G x),
        ((θ b : ↥(I ⊓ stabilizer G x)) : G) = totFun φ (totFun ψ (b : G))) ∧
      (∀ d : ↥I, (d : G) ∈ dblSet I x y ↔ ((φ d : ↥I) : G) ∈ dblSet I x y) ∧
      (∀ i ∈ I ⊓ stabilizer G x, ∃ j ∈ I ⊓ stabilizer G x,
        autImage ψ.symm (conjSub i (stabilizer G x ⊓ stabilizer G y)) =
          conjSub j (stabilizer G x ⊓ stabilizer G y)) := by
  obtain ⟨φ₀, ψ₀, hφ₀, hψ₀, hθ⟩ := hV.v1 θ
  obtain ⟨ψ₁, ψ₂, _, hψ₁B, hψ₂, hψ⟩ := hV.v2 ψ₀ hψ₀
  obtain ⟨φ₁, φ₂, hD₁, hφ₂, hφ⟩ := hV.v3 φ₀ hφ₀
  have hφ₁ : autPres I (I ⊓ stabilizer G x) φ₁ := autPres_of_factor _ _ hφ₀ hφ₂ hφ
  have hψ₁ : autPres (stabilizer G x) (I ⊓ stabilizer G x) ψ₁ :=
    autPres_of_factor _ _ hψ₀ hψ₂ hψ
  refine ⟨φ₁, ψ₁, hφ₁, hψ₁, ?_, hD₁, hψ₁B⟩
  intro b
  have hbS : (b : G) ∈ stabilizer G x := (Subgroup.mem_inf.mp b.2).2
  have hψb : totFun ψ₀ (b : G) = totFun ψ₁ (b : G) := by
    have h2 : ψ₂ ⟨(b : G), hbS⟩ = ⟨(b : G), hbS⟩ := Subtype.ext (hψ₂ ⟨(b : G), hbS⟩ b.2)
    have h3 := hψ ⟨(b : G), hbS⟩
    rw [h2] at h3
    rw [totFun_of_mem ψ₀ hbS, totFun_of_mem ψ₁ hbS]
    exact h3
  have hwI : totFun ψ₁ (b : G) ∈ I ⊓ stabilizer G x := by
    rw [totFun_of_mem ψ₁ hbS]
    exact (hψ₁ ⟨(b : G), hbS⟩).mp b.2
  have hφw : ∀ w : G, w ∈ I ⊓ stabilizer G x → totFun φ₀ w = totFun φ₁ w := by
    intro w hw
    have hwI' : w ∈ I := (Subgroup.mem_inf.mp hw).1
    have h2 : φ₂ ⟨w, hwI'⟩ = ⟨w, hwI'⟩ := Subtype.ext (hφ₂ ⟨w, hwI'⟩ hw)
    have h3 := hφ ⟨w, hwI'⟩
    rw [h2] at h3
    rw [totFun_of_mem φ₀ hwI', totFun_of_mem φ₁ hwI']
    exact h3
  rw [hθ b, hψb]
  exact hφw _ hwI

end CFSG.Quasithin.H13.AS91
