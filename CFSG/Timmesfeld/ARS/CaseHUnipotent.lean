module

public import CFSG.Timmesfeld.ARS.CaseHPositive

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

section Unipotent

variable (h : Hyp G R) (hH : SigmaEqLambda R)
include h hH

omit hH in
theorem conjSub_K {A P' : Subgroup G} (hA : A ∈ R) (hP' : P' ∈ R) {g : G}
    (hgA : conjSub A g = A) (hgP' : conjSub P' g = P') :
    conjSub (M R A ⊓ M R P') g = M R A ⊓ M R P' := by
  have := h.finite
  change Subgroup.map _ (_ ⊓ _) = _
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective]
  exact congrArg₂ (· ⊓ ·) ((isPGroup_M h.root hA).2.2 g (conjSub_eq_self_iff.1 hgA))
    ((isPGroup_M h.root hP').2.2 g (conjSub_eq_self_iff.1 hgP'))

theorem eq_one_of_mem_U5_of_mem_M (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') {y : G}
    (hy : y ∈ shortRoot R P' ⁅A₀, P⁆ A) (hyM : y ∈ M R P') : y = 1 := by
  have := h.finite
  have hP'R : P' ∈ R := hP'.2.1
  obtain ⟨-, -, -, -, -, ⟨hsAQ, -⟩, -, -, -, hQΩ⟩ := apartment h hH hA hA₀ hP hP' hPP'
  have hAs' : A ∈ lambdaStar R P' ⁅A₀, P⁆ := ⟨mem_lambdaSet_comm hA hP'.1, hA, hsAQ.symm⟩
  have hLP' : (linesThrough R P').ncard = (linesThrough R A).ncard :=
    ncard_linesThrough_eq h hA hP'R
  obtain ⟨-, -, hreg⟩ := shortRoot_moufang_of h hH hT hP'R hQΩ hAs'
  obtain ⟨W, hW, hWA⟩ : ∃ W ∈ linesThrough R P', ¬ A ≤ W := by
    by_contra hno
    push Not at hno
    have hsub : linesThrough R P' ⊆ {P' ⊔ A} := fun W hW =>
      eq_sup_of_le h hP'R hAs'.1 hW (hno W hW)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton, hLP'] at this
    omega
  obtain ⟨D, hD, rfl⟩ := (mem_linesThrough_iff h hP'R).1 hW
  have hyW : conjSub (P' ⊔ D) y = P' ⊔ D := conjSub_sup_eq_of_mem_M h hP'R hD hyM
  obtain ⟨u₀, -, huniq⟩ := hreg (P' ⊔ D) hW (P' ⊔ D) hW hWA hWA
  exact congrArg Subtype.val ((huniq ⟨y, hy⟩ hyW).trans (huniq 1 (conjSub_one _)).symm)

theorem existsUnique_comp (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') {g : G}
    (hg : g ∈ M R A ⊓ Subgroup.normalizer (P' : Set G)) :
    ∃! y, y ∈ shortRoot R P' ⁅A₀, P⁆ A ∧ g * y⁻¹ ∈ M R A ⊓ M R P' := by
  have := h.finite
  have hR := h.root
  have hP'R : P' ∈ R := hP'.2.1
  have hUK : shortRoot R P' ⁅A₀, P⁆ A ≤ Subgroup.normalizer ((M R A ⊓ M R P' : Subgroup G) :
      Set G) := fun y hy => conjSub_eq_self_iff.1 (conjSub_K h hA hP'R
        (conjSub_of_forall_commute fun x hx => commuting_shortRoot_mid h hA y hy x hx)
        (conjSub_of_forall_commute fun x hx => commuting_shortRoot_left P' _ A y hy x hx))
  have hle := M_inf_normalizer_le h hH hT hA h3 hA₀ hP hP' hPP' hg
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hUK] at hle
  obtain ⟨k, hk, y, hy, rfl⟩ := hle
  refine ⟨y, ⟨hy, by rwa [mul_inv_cancel_right]⟩, fun y' ⟨hy', hky'⟩ => ?_⟩
  have h1 : y * y'⁻¹ ∈ M R A ⊓ M R P' := by
    have := (M R A ⊓ M R P').mul_mem ((M R A ⊓ M R P').inv_mem hk) hky'
    rwa [show k⁻¹ * (k * y * y'⁻¹) = y * y'⁻¹ by group] at this
  have h2 := eq_one_of_mem_U5_of_mem_M h hH hT hA h3 hA₀ hP hP' hPP'
    ((shortRoot R P' ⁅A₀, P⁆ A).mul_mem hy ((shortRoot R P' ⁅A₀, P⁆ A).inv_mem hy')) h1.2
  exact (mul_inv_eq_one.mp h2).symm

omit h hH in
theorem comp_mul {K : Subgroup G} {g₁ g₂ y₁ y₂ : G} (h₁ : g₁ * y₁⁻¹ ∈ K) (h₂ : g₂ * y₂⁻¹ ∈ K)
    (hy₁ : conjSub K y₁ = K) : g₁ * g₂ * (y₁ * y₂)⁻¹ ∈ K := by
  have h3 : y₁ * (g₂ * y₂⁻¹) * y₁⁻¹ ∈ K := by
    have := conj_mem_conjSub y₁ h₂
    rwa [hy₁] at this
  have := K.mul_mem h₁ h3
  rwa [show g₁ * y₁⁻¹ * (y₁ * (g₂ * y₂⁻¹) * y₁⁻¹) = g₁ * g₂ * (y₁ * y₂)⁻¹ by group] at this

omit h hH in
theorem comp_conj {K : Subgroup G} {g y x : G} (hg : g * y⁻¹ ∈ K) (hx : conjSub K x = K)
    (hxy : ⁅x, y⁆ ∈ K) : x * g * x⁻¹ * y⁻¹ ∈ K := by
  have h1 : x * (g * y⁻¹) * x⁻¹ ∈ K := by
    have := conj_mem_conjSub x hg
    rwa [hx] at this
  have := K.mul_mem h1 hxy
  rwa [commutatorElement_def,
    show x * (g * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) = x * g * x⁻¹ * y⁻¹ by group] at this

theorem K_eq (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') :
    M R A ⊓ M R P' = A ⊔ P' ⊔ shortRoot R P ⁅A₀, P'⁆ A := by
  have hPR : P ∈ R := hP.2.1
  obtain ⟨-, -, -, -, -, -, ⟨hsAQ', hcAQ'⟩, -, hQ'Ω, -⟩ := apartment h hH hA hA₀ hP hP' hPP'
  have hAs : A ∈ lambdaStar R P ⁅A₀, P'⁆ := ⟨mem_lambdaSet_comm hA hP.1, hA, hsAQ'.symm⟩
  have hL : 3 ≤ (linesThrough R P).ncard := (ncard_linesThrough_eq h hA hPR) ▸ h3
  have hline := M_inf_M_eq h hH hT hPR hL hQ'Ω hAs
  rwa [Subgroup.commutator_comm ⁅A₀, P'⁆ A, hcAQ'] at hline

theorem conjSub_K_of_mem_P (hT : MTransitive R) {A A₀ P P' : Subgroup G} (hA : A ∈ R)
    (h3 : 3 ≤ (linesThrough R A).ncard) (hA₀ : A₀ ∈ omegaSet R A)
    (hP : P ∈ lambdaStar R A A₀) (hP' : P' ∈ lambdaStar R A A₀) (hPP' : P ≠ P') {p : G}
    (hp : p ∈ P) : conjSub (M R A ⊓ M R P') p = M R A ⊓ M R P' := by
  have := h.finite
  have hR := h.root
  have hPR : P ∈ R := hP.2.1
  have hK := K_eq h hH hT hA h3 hA₀ hP hP' hPP'
  have key : ∀ x ∈ P, conjSub (M R A ⊓ M R P') x ≤ M R A ⊓ M R P' := by
    intro x hx
    rw [hK]
    change Subgroup.map _ (A ⊔ P' ⊔ shortRoot R P ⁅A₀, P'⁆ A) ≤ _
    rw [Subgroup.map_sup, Subgroup.map_sup]
    have hxA : conjSub A x = A := conjSub_of_forall_commute fun a ha =>
      (hP.1.1.2.2 a ha x hx).symm
    have hxU : conjSub (shortRoot R P ⁅A₀, P'⁆ A) x = shortRoot R P ⁅A₀, P'⁆ A :=
      conjSub_of_forall_commute fun u hu => (commuting_shortRoot_left P _ A u hu x hx).symm
    have hxP' : conjSub P' x ≤ A ⊔ P' := by
      rw [← conjSub_sup_eq_of_mem_M h hA hP'.1 (QD.le_M hP.1 hx)]
      exact Subgroup.map_mono le_sup_right
    change conjSub A x ⊔ conjSub P' x ⊔ conjSub (shortRoot R P ⁅A₀, P'⁆ A) x ≤ _
    rw [hxA, hxU]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) (hxP'.trans le_sup_left)) le_sup_right
  refine le_antisymm (key p hp) ?_
  have := Subgroup.map_mono (f := (MulAut.conj p).toMonoidHom) (key p⁻¹ (P.inv_mem hp))
  change conjSub (conjSub (M R A ⊓ M R P') p⁻¹) p ≤ conjSub (M R A ⊓ M R P') p at this
  rwa [Plane.conjSub_inv_conjSub] at this

end Unipotent

end CaseH

end CFSG.Timmesfeld.ARS
