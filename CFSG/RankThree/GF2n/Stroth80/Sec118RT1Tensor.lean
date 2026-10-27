module

public import CFSG.ClassicalGroups.Symplectic.TensorNormalizer
public import CFSG.RankThree.GF2n.Stroth80.Sec118Nondeg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix
open CFSG.ClassicalGroups.Symplectic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.mem_cmComm_of_act (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {l : G} (hlH : l ∈ H0 M Z) {y : M₀.E} (hy : y ∈ cmComm M Q Z B K γ M₀ φ) :
    φ ⟨l, hlH⟩ y ∈ cmComm M Q Z B K γ M₀ φ := by
  obtain ⟨x, hx, rfl⟩ := (mem_cmComm_iff hc h φ hφπ y).mp hy
  have hxQ : x ∈ Q := commutator_le_Q hc hx
  have hlx : l * x * l⁻¹ ∈ (⁅Q, XbarPre M Q Z B⁆ : Subgroup G) :=
    (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_commXbarPre hlH.1) x).mp hx
  refine (mem_cmComm_iff hc h φ hφπ _).mpr ⟨l * x * l⁻¹, hlx, ?_⟩
  exact hφπ ⟨l, hlH⟩ x hxQ

theorem Ctx.exists_tensor_of_mem_H0 [CharP K 2] (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    {m : ℕ} (hm : 1 ≤ m) {W₁ W₂ : Submodule K M₀.E} (hdisj : W₁ ⊓ W₂ = ⊥)
    (hsup : W₁ ⊔ W₂ = cmComm M Q Z B K γ M₀ φ)
    (hW₁ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₁, φ s w ∈ W₁)
    (hW₂ : ∀ s : ↥(XbarH M Q Z B), ∀ w ∈ W₂, φ s w ∈ W₂)
    (ρ : ↥(XbarH M Q Z B) →* GL (Fin m ⊕ Fin m) K) (hρr : ρ.range = StatedSp m K)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    (he₁ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₁),
      e₁ ⟨φ s w, hW₁ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₁ w)
    (he₂ : ∀ (s : ↥(XbarH M Q Z B)) (w : W₂),
      e₂ ⟨φ s w, hW₂ s w w.2⟩ = (ρ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ e₂ w)
    {l : G} (hlH : l ∈ H0 M Z) :
    ∃ (s₀ : GL (Fin m ⊕ Fin m) K) (h₁₁ h₁₂ h₂₁ h₂₂ : K), s₀ ∈ StatedSp m K ∧
      ∀ x : Fin m ⊕ Fin m → K,
        φ ⟨l, hlH⟩ ((e₁.symm x : W₁) : M₀.E) =
          ((e₁.symm (h₁₁ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
            M₀.E) +
          ((e₂.symm (h₂₁ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
            M₀.E) ∧
        φ ⟨l, hlH⟩ ((e₂.symm x : W₂) : M₀.E) =
          ((e₁.symm (h₁₂ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) :
            M₀.E) +
          ((e₂.symm (h₂₂ • ((s₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) :
            M₀.E) := by
  have hlM : l ∈ M := hlH.1
  have hconjH : ∀ s : ↥(XbarH M Q Z B), l * ((s : ↥(H0 M Z)) : G) * l⁻¹ ∈ H0 M Z := fun s =>
    (H0 M Z).mul_mem ((H0 M Z).mul_mem hlH s.1.2) ((H0 M Z).inv_mem hlH)
  have hconjX : ∀ s : ↥(XbarH M Q Z B), l * ((s : ↥(H0 M Z)) : G) * l⁻¹ ∈ XbarPre M Q Z B := by
    intro s
    have hs : ((s : ↥(H0 M Z)) : G) ∈ XbarPre M Q Z B := (mem_XbarH_iff hc _).mp s.2
    have hN := XbarPre_normal hc hlM
    have hmem : l * ((s : ↥(H0 M Z)) : G) * l⁻¹ ∈ conjSubgroup l (XbarPre M Q Z B) :=
      ⟨_, hs, by show (MulAut.conj l) _ = _; rw [MulAut.conj_apply]⟩
    rwa [hN] at hmem
  let σ : ↥(XbarH M Q Z B) → ↥(XbarH M Q Z B) := fun s =>
    ⟨⟨l * ((s : ↥(H0 M Z)) : G) * l⁻¹, hconjH s⟩, (mem_XbarH_iff hc _).mpr (hconjX s)⟩
  refine exists_tensor_of_normalizes hm hdisj e₁ e₂ (φ.comp (XbarH M Q Z B).subtype) ρ hρr hW₁ hW₂
    he₁ he₂ (φ ⟨l, hlH⟩) ?_ σ ?_
  · intro y hy
    rw [hsup] at hy ⊢
    exact hc.mem_cmComm_of_act h φ hφπ hlH hy
  · intro s y
    have hmul : (⟨l, hlH⟩ : ↥(H0 M Z)) * ((s : ↥(H0 M Z))) =
        ((σ s : ↥(XbarH M Q Z B)) : ↥(H0 M Z)) * ⟨l, hlH⟩ := by
      apply Subtype.ext
      show l * ((s : ↥(H0 M Z)) : G) = (l * ((s : ↥(H0 M Z)) : G) * l⁻¹) * l
      group
    have := congrArg (fun u : ↥(H0 M Z) => φ u y) hmul
    simp only [map_mul, LinearEquiv.mul_apply] at this
    exact this

end CFSG.RankThree.GF2n.Stroth80
