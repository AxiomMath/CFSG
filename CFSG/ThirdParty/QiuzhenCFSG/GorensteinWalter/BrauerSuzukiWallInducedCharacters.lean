module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallIndexK
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunctionHelpers

namespace CFSG
end CFSG
open CFSG

/-!
# Initial induced characters in the Brauer--Suzuki--Wall argument

Bender's order calculation starts with two linear characters of `K` that
are moved by the inverting involution `s`.  Index-two induction makes them
distinct irreducible characters of `H`, both of degree two.
-/

namespace CFSG.GorensteinWalter

noncomputable section

universe u

open BenderGlauberman
open Theory.Character

attribute [local instance] Classical.propDecidable

/-- The index-two inductions of Bender's two initial linear characters are
distinct irreducible degree-two characters, with opposite values at `t`.

The non-fixed hypotheses are stated as failure of invariance under inversion.
This is proof-irrelevance-stable and is equivalent here to failure of
invariance under conjugation by `s`, since `s` inverts `K`. -/
public theorem BrauerSuzukiWallHypotheses.induced_linear_characters
    {G : Type u} [Group G] [Fintype G]
    (h : BrauerSuzukiWallHypotheses G)
    {rho sigma : ClassFunction h.K}
    (hrho : IsLinearCharacter rho)
    (hsigma : IsLinearCharacter sigma)
    (hrhoNot : ¬ ∀ x : h.K, rho x⁻¹ = rho x)
    (hsigmaNot : ¬ ∀ x : h.K, sigma x⁻¹ = sigma x)
    (hrhoT : rho ⟨h.t, h.t_mem_K⟩ = 1)
    (hsigmaT : sigma ⟨h.t, h.t_mem_K⟩ = -1) :
    let hKleH : h.K ≤ h.H := by
      rw [h.H_eq_join]
      exact le_sup_left
    let rhoH : ClassFunction h.H := inducedFromSub hKleH rho
    let sigmaH : ClassFunction h.H := inducedFromSub hKleH sigma
    IsIrreducibleCharacter rhoH ∧
      IsIrreducibleCharacter sigmaH ∧
      rhoH ≠ sigmaH ∧
      rhoH 1 = 2 ∧ sigmaH 1 = 2 ∧
      rhoH ⟨h.t, hKleH h.t_mem_K⟩ = 2 ∧
      sigmaH ⟨h.t, hKleH h.t_mem_K⟩ = -2 := by
  classical
  let hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  let rhoH : ClassFunction h.H := inducedFromSub hKleH rho
  let sigmaH : ClassFunction h.H := inducedFromSub hKleH sigma
  have hsH : h.s ∈ h.H := by
    rw [h.H_eq_join]
    exact SetLike.le_def.mp le_sup_right (Subgroup.mem_zpowers h.s)
  have hsK : ∀ x : h.K, h.s * (x : G) * h.s⁻¹ ∈ h.K := by
    intro x
    rw [h.s_inverts_K (x : G) x.2]
    exact h.K.inv_mem x.2
  have hrhoMove : ¬ ∀ x : G, (hx : x ∈ h.K) →
      (hsx : h.s * x * h.s⁻¹ ∈ h.K) →
      rho ⟨h.s * x * h.s⁻¹, hsx⟩ = rho ⟨x, hx⟩ := by
    intro hfix
    apply hrhoNot
    intro x
    have hv := hfix (x : G) x.2 (hsK x)
    have heq : (⟨h.s * (x : G) * h.s⁻¹, hsK x⟩ : h.K) = x⁻¹ := by
      apply Subtype.ext
      exact h.s_inverts_K (x : G) x.2
    simpa [heq] using hv
  have hsigmaMove : ¬ ∀ x : G, (hx : x ∈ h.K) →
      (hsx : h.s * x * h.s⁻¹ ∈ h.K) →
      sigma ⟨h.s * x * h.s⁻¹, hsx⟩ = sigma ⟨x, hx⟩ := by
    intro hfix
    apply hsigmaNot
    intro x
    have hv := hfix (x : G) x.2 (hsK x)
    have heq : (⟨h.s * (x : G) * h.s⁻¹, hsK x⟩ : h.K) = x⁻¹ := by
      apply Subtype.ext
      exact h.s_inverts_K (x : G) x.2
    simpa [heq] using hv
  have hrhoIrr : IsIrreducibleCharacter rhoH := by
    exact
      (remark_1_4 hKleH h.index_K_H hsH h.s_not_mem_K hrho.1).2
        hrhoMove
  have hsigmaIrr : IsIrreducibleCharacter sigmaH := by
    exact
      (remark_1_4 hKleH h.index_K_H hsH h.s_not_mem_K hsigma.1).2
        hsigmaMove
  have hformula (nu : ClassFunction h.K) (hnu : IsIrreducibleCharacter nu)
      (x : G) (hx : x ∈ h.K) :
      inducedFromSub hKleH nu ⟨x, hKleH hx⟩ =
        nu ⟨x, hx⟩ + nu ⟨h.s * x * h.s⁻¹, hsK ⟨x, hx⟩⟩ := by
    exact
      (remark_1_4 hKleH h.index_K_H hsH h.s_not_mem_K hnu).1
        x hx (hsK ⟨x, hx⟩)
  have htInv : h.t⁻¹ = h.t := by
    exact inv_eq_of_mul_eq_one_right (by
      simpa [pow_two] using h.t_involution.2)
  have hst : h.s * h.t * h.s⁻¹ = h.t := by
    rw [h.s_inverts_K h.t h.t_mem_K, htInv]
  have hrhoOne : rhoH 1 = 2 := by
    have hv := hformula rho hrho.1 1 h.K.one_mem
    have hKone : (⟨(1 : G), h.K.one_mem⟩ : h.K) = 1 := rfl
    have hKconjOne :
        (⟨h.s * (1 : G) * h.s⁻¹, hsK ⟨1, h.K.one_mem⟩⟩ : h.K) = 1 := by
      apply Subtype.ext
      simp
    have hv1 : rho ⟨(1 : G), h.K.one_mem⟩ = 1 :=
      (congrArg rho hKone).trans hrho.2
    have hv2 : rho ⟨h.s * (1 : G) * h.s⁻¹, hsK ⟨1, h.K.one_mem⟩⟩ = 1 :=
      (congrArg rho hKconjOne).trans hrho.2
    rw [hv1, hv2] at hv
    norm_num at hv
    have hHone : (⟨(1 : G), hKleH h.K.one_mem⟩ : h.H) = 1 := rfl
    rw [hHone] at hv
    simpa [rhoH] using hv
  have hsigmaOne : sigmaH 1 = 2 := by
    have hv := hformula sigma hsigma.1 1 h.K.one_mem
    have hKone : (⟨(1 : G), h.K.one_mem⟩ : h.K) = 1 := rfl
    have hKconjOne :
        (⟨h.s * (1 : G) * h.s⁻¹, hsK ⟨1, h.K.one_mem⟩⟩ : h.K) = 1 := by
      apply Subtype.ext
      simp
    have hv1 : sigma ⟨(1 : G), h.K.one_mem⟩ = 1 :=
      (congrArg sigma hKone).trans hsigma.2
    have hv2 : sigma ⟨h.s * (1 : G) * h.s⁻¹, hsK ⟨1, h.K.one_mem⟩⟩ = 1 :=
      (congrArg sigma hKconjOne).trans hsigma.2
    rw [hv1, hv2] at hv
    norm_num at hv
    have hHone : (⟨(1 : G), hKleH h.K.one_mem⟩ : h.H) = 1 := rfl
    rw [hHone] at hv
    simpa [sigmaH] using hv
  have hrhoT' : rhoH ⟨h.t, hKleH h.t_mem_K⟩ = 2 := by
    have hv := hformula rho hrho.1 h.t h.t_mem_K
    have hKt : (⟨h.t, h.t_mem_K⟩ : h.K) = ⟨h.t, h.t_mem_K⟩ := rfl
    have hKconjT :
        (⟨h.s * h.t * h.s⁻¹, hsK ⟨h.t, h.t_mem_K⟩⟩ : h.K) =
          ⟨h.t, h.t_mem_K⟩ := by
      apply Subtype.ext
      exact hst
    have hv1 : rho ⟨h.t, h.t_mem_K⟩ = 1 :=
      (congrArg rho hKt).trans hrhoT
    have hv2 : rho ⟨h.s * h.t * h.s⁻¹, hsK ⟨h.t, h.t_mem_K⟩⟩ = 1 :=
      (congrArg rho hKconjT).trans hrhoT
    rw [hv1, hv2] at hv
    norm_num at hv
    simpa [rhoH] using hv
  have hsigmaT' : sigmaH ⟨h.t, hKleH h.t_mem_K⟩ = -2 := by
    have hv := hformula sigma hsigma.1 h.t h.t_mem_K
    have hKt : (⟨h.t, h.t_mem_K⟩ : h.K) = ⟨h.t, h.t_mem_K⟩ := rfl
    have hKconjT :
        (⟨h.s * h.t * h.s⁻¹, hsK ⟨h.t, h.t_mem_K⟩⟩ : h.K) =
          ⟨h.t, h.t_mem_K⟩ := by
      apply Subtype.ext
      exact hst
    have hv1 : sigma ⟨h.t, h.t_mem_K⟩ = -1 :=
      (congrArg sigma hKt).trans hsigmaT
    have hv2 : sigma ⟨h.s * h.t * h.s⁻¹, hsK ⟨h.t, h.t_mem_K⟩⟩ = -1 :=
      (congrArg sigma hKconjT).trans hsigmaT
    rw [hv1, hv2] at hv
    norm_num at hv
    simpa [sigmaH] using hv
  have hne : rhoH ≠ sigmaH := by
    intro heq
    have hv := congrFun heq ⟨h.t, hKleH h.t_mem_K⟩
    rw [hrhoT', hsigmaT'] at hv
    norm_num at hv
  exact
    ⟨hrhoIrr, hsigmaIrr, hne, hrhoOne, hsigmaOne, hrhoT', hsigmaT'⟩

end

end CFSG.GorensteinWalter
