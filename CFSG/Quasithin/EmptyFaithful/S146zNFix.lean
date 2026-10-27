module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.ThreeC

section FixInj

open Matrix CFSG.SectionRank.Ccomm CFSG.QuasithinUnique.Setup.Family

def invList3 : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![0, 0, 1; 0, 1, 0; 1, 0, 0],
    !![0, 0, 1; 1, 1, 1; 1, 0, 0],
    !![0, 1, 0; 1, 0, 0; 0, 0, 1],
    !![0, 1, 0; 1, 0, 0; 1, 1, 1],
    !![0, 1, 1; 0, 1, 0; 1, 1, 0],
    !![0, 1, 1; 1, 0, 1; 0, 0, 1],
    !![1, 0, 0; 0, 0, 1; 0, 1, 0],
    !![1, 0, 0; 0, 1, 0; 0, 1, 1],
    !![1, 0, 0; 0, 1, 0; 1, 0, 1],
    !![1, 0, 0; 0, 1, 0; 1, 1, 1],
    !![1, 0, 0; 0, 1, 1; 0, 0, 1],
    !![1, 0, 0; 1, 0, 1; 1, 1, 0],
    !![1, 0, 0; 1, 1, 0; 0, 0, 1],
    !![1, 0, 0; 1, 1, 0; 1, 0, 1],
    !![1, 0, 0; 1, 1, 1; 0, 0, 1],
    !![1, 0, 1; 0, 1, 0; 0, 0, 1],
    !![1, 0, 1; 0, 1, 1; 0, 0, 1],
    !![1, 1, 0; 0, 1, 0; 0, 0, 1],
    !![1, 1, 0; 0, 1, 0; 0, 1, 1],
    !![1, 1, 1; 0, 0, 1; 0, 1, 0],
    !![1, 1, 1; 0, 1, 0; 0, 0, 1]]

theorem mem_invList3 : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M * M = 1 → M ≠ 1 → M ∈ invList3 := by
  decide +kernel

theorem fix_pair3 : ∀ M ∈ invList3, ∀ N ∈ invList3,
    (∀ v : Fin 3 → ZMod 2, M *ᵥ v = v ↔ N *ᵥ v = v) →
    (∀ v : Fin 3 → ZMod 2, Mᵀ *ᵥ v = v ↔ Nᵀ *ᵥ v = v) → M = N := by
  decide +kernel

theorem fix_injective {W : Type*} [Group W] [Finite W]
    (hcomm : ∀ a b : W, a * b = b * a) (hsq : ∀ a : W, a ^ 2 = 1) (h8 : Nat.card W = 8)
    (σ : MulAut (MulAut W)) (hσ : ∀ g : MulAut W, σ ≠ MulAut.conj g)
    {a b : MulAut W} (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hF : ∀ w, a w = w ↔ b w = w) (hFσ : ∀ w, σ a w = w ↔ σ b w = w) : a = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₀⟩ := nonempty_mulEquiv_of_elementary (p := 2) hcomm hsq (n := 3)
    (by rw [h8]; norm_num)
  let Ψ : MulAut W ≃* GL32 := (MulAut.congr e₀).trans (mulAutEquivGL (p := 2) 3)
  have hΨ : ∀ (c : MulAut W) (w : W), ((Ψ c : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
      Multiplicative.toAdd (e₀ w) = Multiplicative.toAdd (e₀ (c w)) := by
    intro c w
    have h := mulAutEquivGL_mulVec (p := 2) 3 (MulAut.congr e₀ c) (Multiplicative.toAdd (e₀ w))
    have e : (MulAut.congr e₀ c) (Multiplicative.ofAdd (Multiplicative.toAdd (e₀ w))) =
        e₀ (c w) := by
      simp [MulAut.congr_apply]
    rw [e] at h
    exact h
  have hfix : ∀ (c d : MulAut W), (∀ w, c w = w ↔ d w = w) →
      ∀ v : Fin 3 → ZMod 2, ((Ψ c : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v ↔
        ((Ψ d : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = v := by
    intro c d hcd v
    have hv : Multiplicative.toAdd (e₀ (e₀.symm (Multiplicative.ofAdd v))) = v := by simp
    have h1 := hΨ c (e₀.symm (Multiplicative.ofAdd v))
    have h2 := hΨ d (e₀.symm (Multiplicative.ofAdd v))
    rw [hv] at h1 h2
    rw [h1, h2]
    have := hcd (e₀.symm (Multiplicative.ofAdd v))
    constructor
    · intro h
      have h' : c (e₀.symm (Multiplicative.ofAdd v)) = e₀.symm (Multiplicative.ofAdd v) := by
        apply e₀.injective
        simpa using congrArg Multiplicative.ofAdd h
      have h'' := this.mp h'
      rw [h'']; simp
    · intro h
      have h' : d (e₀.symm (Multiplicative.ofAdd v)) = e₀.symm (Multiplicative.ofAdd v) := by
        apply e₀.injective
        simpa using congrArg Multiplicative.ofAdd h
      have h'' := this.mpr h'
      rw [h'']; simp
  let σ' : MulAut GL32 := Ψ.symm.trans (σ.trans Ψ)
  have hσ'Ψ : ∀ c : MulAut W, σ' (Ψ c) = Ψ (σ c) := fun c => by
    show Ψ (σ (Ψ.symm (Ψ c))) = Ψ (σ c)
    rw [MulEquiv.symm_apply_apply]
  have hσ'out : ∀ g : GL32, σ' ≠ MulAut.conj g := by
    intro g hg
    apply hσ (Ψ.symm g)
    refine MulEquiv.ext fun c => ?_
    apply Ψ.injective
    rw [← hσ'Ψ c, hg]
    simp [MulAut.conj_apply]
  rcases aut_GL32_cases σ' with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact absurd hg (hσ'out g)
  have hσ'apply : ∀ α : GL32, ((σ' α : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((α⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
        ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro α
    have h1 : (σ' α : GL32) = g * (CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3
        (ZMod 2) α) * g⁻¹ := by
      rw [hg]; rfl
    rw [h1]
    simp only [Units.val_mul]
    rw [CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_matrix]
  set α : GL32 := Ψ a with hα
  set β : GL32 := Ψ b with hβ
  have hαα : α * α = 1 := by rw [hα, ← map_mul, ha2, map_one]
  have hββ : β * β = 1 := by rw [hβ, ← map_mul, hb2, map_one]
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hββ
  have hα1 : (α : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h => ha1 (Ψ.injective (by
    rw [map_one]; exact Units.ext h))
  have hβ1 : (β : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 1 := fun h => hb1 (Ψ.injective (by
    rw [map_one]; exact Units.ext h))
  have hMM : (α : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (α : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    have := congrArg Units.val hαα
    simp at this; exact this
  have hNN : (β : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (β : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    have := congrArg Units.val hββ
    simpa using this
  have hF' := hfix a b hF
  have hFσ' := hfix (σ a) (σ b) hFσ
  rw [← hσ'Ψ a, ← hσ'Ψ b] at hFσ'
  have hgg : ((g : Matrix (Fin 3) (Fin 3) (ZMod 2))) * ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
    simp
  have hgg' : ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * ((g : Matrix (Fin 3) (Fin 3) (ZMod 2))) = 1 := by
    simp
  have hT : ∀ u : Fin 3 → ZMod 2,
      (α : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ u = u ↔
        (β : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ u = u := by
    intro u
    have h := hFσ' ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u)
    rw [hσ'apply α, hσ'apply β, hαinv, hβinv] at h
    have e : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
        ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A * ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2))) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u) =
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ (A *ᵥ u) := by
      intro A
      have e' : ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
          ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2))) * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A := by
        rw [Matrix.mul_assoc ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A), hgg', Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e']
    have inj : ∀ x y : Fin 3 → ZMod 2,
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ y ↔ x = y := by
      intro x y
      constructor
      · intro hxy
        have := congrArg (fun z => ((g⁻¹ : GL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ z) hxy
        simpa [Matrix.mulVec_mulVec, hgg'] using this
      · intro hxy; rw [hxy]
    rw [e, e, inj, inj] at h
    exact h
  have hMem := mem_invList3 _ hMM hα1
  have hNem := mem_invList3 _ hNN hβ1
  have hEq := fix_pair3 _ hMem _ hNem hF' hT
  exact Ψ.injective (Units.ext hEq)


end FixInj

end CFSG.Quasithin.ThreeC
