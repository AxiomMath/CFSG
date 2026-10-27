module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

variable {U : Type} [CommGroup U] [Finite U]

@[expose] def s15_semiBot_D (x : MulAut U) : U →* U :=
  x.toMonoidHom * (MonoidHom.id U)⁻¹

theorem s15_semiBot_D_apply (x : MulAut U) (u : U) :
    s15_semiBot_D x u = x u * u⁻¹ := rfl

theorem s15_semiBot_conj_eq (x y : U) : x * y * x⁻¹ = y := by
  rw [mul_assoc, mul_comm y x⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

theorem s15_semiBot_mul_comm_mul (x y z : U) : x * y * z = x * z * y := by
  rw [mul_assoc, mul_comm y z, ← mul_assoc]

theorem s15_semiBot_mul_mul_inv_self (x y : U) : x * (x * y)⁻¹ = y⁻¹ := by
  rw [mul_inv_rev, ← mul_assoc, mul_comm x y⁻¹, mul_assoc, mul_inv_cancel, mul_one]

theorem s15_semiBot_mul_mul_inv (x y z : U) : (x * z) * (x * y)⁻¹ = z * y⁻¹ := by
  rw [mul_comm x z, mul_assoc, s15_semiBot_mul_mul_inv_self x y]

theorem s15_semiBot_epsilon_trivial (hU : ∀ u : U, u ^ 2 = 1) {A B : Subgroup (MulAut U)}
    (hAB : ⁅A, B⁆ = ⊥) (hUA : commSub ⊤ A = ⊤) {t : MulAut U} {c : U}
    (hc1 : c ≠ 1) (hN : ∀ u, t u = u ∨ t u = u * c) (htc : t c = c) (htt : t * t = 1)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hBc : ∀ b ∈ B, b c = c) :
    ∀ b ∈ B, ∀ u, s15_semiBot_D t u * s15_semiBot_D t (b⁻¹ u) = 1 := by
  have hbA : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have hmem : ⁅a, b⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
    rwa [hAB, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcc : c * c = 1 := by rw [← pow_two]; exact hU c
  let N : U →* U := s15_semiBot_D t
  have hN_apply : ∀ u, N u = t u * u⁻¹ := fun u => s15_semiBot_D_apply t u
  have hN01 : ∀ u, N u = 1 ∨ N u = c := by
    intro u
    rcases hN u with h | h
    · left; rw [hN_apply, h, mul_inv_cancel]
    · right; rw [hN_apply, h, s15_semiBot_conj_eq u c]
  have htN : ∀ w : U, t w = w * N w := by
    intro w
    rw [hN_apply w, ← mul_assoc, s15_semiBot_conj_eq]
  intro b hb
  let ε : U →* U := N * N.comp (b⁻¹).toMonoidHom
  have hε_apply : ∀ u, ε u = N u * N (b⁻¹ u) := by intro u; simp [ε]
  have hε01 : ∀ u, ε u = 1 ∨ ε u = c := by
    intro u
    rw [hε_apply u]
    rcases hN01 u with h | h <;> rcases hN01 (b⁻¹ u) with h' | h'
    · rw [h, h', mul_one]; exact Or.inl rfl
    · rw [h, h', one_mul]; exact Or.inr rfl
    · rw [h, h', mul_one]; exact Or.inr rfl
    · rw [h, h']; exact Or.inl hcc
  let θ : MulAut U := t * b * t * b⁻¹
  have hθ_apply : ∀ u, θ u = u * ε u := by
    intro u
    have hv : b (b⁻¹ u) = u := MulAut.apply_inv_self U b u
    have hbNv : b (N (b⁻¹ u)) = N (b⁻¹ u) := by
      rcases hN01 (b⁻¹ u) with h | h
      · rw [h, map_one]
      · rw [h]; exact hBc b hb
    have htNv : t (N (b⁻¹ u)) = N (b⁻¹ u) := by
      rcases hN01 (b⁻¹ u) with h | h
      · rw [h, map_one]
      · rw [h]; exact htc
    show t (b (t (b⁻¹ u))) = u * ε u
    rw [htN (b⁻¹ u), map_mul, hv, hbNv, map_mul, htNv, htN u, hε_apply u]
    group
  have hθinv : θ⁻¹ = b * t * b⁻¹ * t := by
    have h : θ⁻¹ = b * t⁻¹ * b⁻¹ * t⁻¹ := by
      rw [show θ = t * b * t * b⁻¹ from rfl]
      group
    rw [h, ht']
  have hθcomm : ∀ a ∈ A, θ * a * θ⁻¹ = a := by
    intro a ha
    have hta : t * a * t ∈ A := by
      have := htA a ha
      rwa [ht'] at this
    have hbab : b⁻¹ * a * b = a := by
      rw [← hbA a ha b⁻¹ (B.inv_mem hb), mul_assoc, inv_mul_cancel, mul_one]
    have hbxb : b * (t * a * t) * b⁻¹ = t * a * t := by
      rw [← hbA (t * a * t) hta b hb, mul_assoc, mul_inv_cancel, mul_one]
    calc θ * a * θ⁻¹
        = t * b * t * (b⁻¹ * a * b) * t * b⁻¹ * t := by
          rw [hθinv, show θ = t * b * t * b⁻¹ from rfl]
          group
      _ = t * b * t * a * t * b⁻¹ * t := by rw [hbab]
      _ = t * (b * (t * a * t) * b⁻¹) * t := by group
      _ = t * (t * a * t) * t := by rw [hbxb]
      _ = a := by
            have h1 : t * (t * a * t) * t = (t * t) * a * (t * t) := by group
            rw [h1, htt, one_mul, mul_one]
  have hθcomm' : ∀ a ∈ A, θ * a = a * θ := by
    intro a ha
    calc θ * a = θ * a * θ⁻¹ * θ := by group
      _ = a * θ := by rw [hθcomm a ha]
  have hθcomm_pt : ∀ a ∈ A, ∀ u, θ (a u) = a (θ u) := by
    intro a ha u
    calc θ (a u) = (θ * a) u := rfl
      _ = (a * θ) u := by rw [hθcomm' a ha]
      _ = a (θ u) := rfl
  have hε_eq : ∀ a ∈ A, ∀ u, ε (a u) = a (ε u) := by
    intro a ha u
    have h := hθcomm_pt a ha u
    rw [hθ_apply, hθ_apply, map_mul] at h
    exact mul_left_cancel h
  have hεtop : ∀ u, ε u = 1 := by
    by_contra hne
    obtain ⟨u₀, hu₀⟩ : ∃ u, ε u = c := by
      by_contra h
      exact hne (fun u => by
        rcases hε01 u with h1 | h1
        · exact h1
        · exact absurd ⟨u, h1⟩ h)
    have hac : ∀ a ∈ A, a c = c := by
      intro a ha
      have h := hε_eq a ha u₀
      rw [hu₀] at h
      rcases hε01 (a u₀) with h1 | h1
      · rw [h1] at h
        exact absurd h.symm (fun hcon => hc1 (a.injective (by rw [hcon, map_one a])))
      · rw [h1] at h; exact h.symm
    have hconst : ∀ a ∈ A, ∀ u, ε (a u) = ε u := by
      intro a ha u
      rw [hε_eq a ha u]
      rcases hε01 u with h1 | h1
      · rw [h1, map_one]
      · rw [h1]; exact hac a ha
    have hker : commSub (⊤ : Subgroup U) A ≤ ε.ker := by
      rw [commSub, Subgroup.closure_le]
      rintro z ⟨a, ha, u, -, rfl⟩
      exact MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hconst a ha u, mul_inv_cancel])
    have hεu₀ : ε u₀ = 1 := by
      have hmem : u₀ ∈ ε.ker := hker (by rw [hUA]; exact Subgroup.mem_top u₀)
      exact MonoidHom.mem_ker.1 hmem
    rw [hu₀] at hεu₀
    exact hc1 hεu₀
  intro u
  have h := hεtop u
  rwa [hε_apply u] at h

end Abstract

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
