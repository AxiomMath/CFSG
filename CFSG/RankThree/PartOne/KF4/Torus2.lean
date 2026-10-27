module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag}

section Torus

variable {K : Type} [Field K]

@[expose] def torus2Elt (i₁ i₂ : Fin τ.rank) (a b : Kˣ) : ModGL τ K :=
  torusElt τ K i₁ a * torusElt τ K i₂ b

theorem torus2Elt_mul (i₁ i₂ : Fin τ.rank) (a b a' b' : Kˣ) :
    torus2Elt i₁ i₂ a b * torus2Elt i₁ i₂ a' b' =
      (torus2Elt i₁ i₂ (a * a') (b * b') : ModGL τ K) := by
  simp only [torus2Elt, torusElt_mul]
  have h := torusElt_mul_comm (τ := τ) (R := K) i₂ i₁ b a'
  calc torusElt τ K i₁ a * torusElt τ K i₂ b * (torusElt τ K i₁ a' * torusElt τ K i₂ b')
      = torusElt τ K i₁ a * (torusElt τ K i₂ b * torusElt τ K i₁ a') * torusElt τ K i₂ b' := by
        group
    _ = _ := by rw [h]; group

theorem torus2Elt_one (i₁ i₂ : Fin τ.rank) : (torus2Elt i₁ i₂ 1 1 : ModGL τ K) = 1 := by
  simp only [torus2Elt, torusElt_one, mul_one]

theorem torus2Elt_inv (i₁ i₂ : Fin τ.rank) (a b : Kˣ) :
    (torus2Elt i₁ i₂ a b : ModGL τ K)⁻¹ = torus2Elt i₁ i₂ a⁻¹ b⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [torus2Elt_mul, mul_inv_cancel, mul_inv_cancel, torus2Elt_one]

theorem mem_subsystemTorus_pair (i₁ i₂ : Fin τ.rank) {g : ModGL τ K} :
    g ∈ subsystemTorus τ K ({i₁, i₂} : Set (Fin τ.rank)) ↔
      ∃ a b : Kˣ, g = torus2Elt i₁ i₂ a b := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, t, rfl⟩ := hx
      rcases hi with rfl | rfl
      · exact ⟨t, 1, by simp only [torus2Elt, torusElt_one, mul_one]⟩
      · exact ⟨1, t, by simp only [torus2Elt, torusElt_one, one_mul]⟩
    | one => exact ⟨1, 1, (torus2Elt_one i₁ i₂).symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact ⟨a * a', b * b', torus2Elt_mul i₁ i₂ a b a' b'⟩
    | inv x _ hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨a⁻¹, b⁻¹, torus2Elt_inv i₁ i₂ a b⟩
  · rintro ⟨a, b, rfl⟩
    exact mul_mem (torusElt_mem_subsystemTorus (Or.inl rfl) a)
      (torusElt_mem_subsystemTorus (Or.inr rfl) b)

end Torus

