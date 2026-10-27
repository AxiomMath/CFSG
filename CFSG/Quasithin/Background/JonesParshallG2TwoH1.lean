module

public import CFSG.Quasithin.Background.JonesParshallG2Two
public import Certificates.Certificate17028
public import Certificates.Certificate8952
public import Certificates.Certificate8953

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

theorem subG2_le : subG2 ≤ cayleyGroup (ZMod 2) := by
  rw [subG2, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact g2a.2
  · exact g2b.2

@[expose] def muK : ↥subG2 →* AddMonoid.End (Ix3 → ZMod 2) :=
  g2Act.comp (Subgroup.inclusion subG2_le)

@[expose] def gensK : Fin 2 → ↥subG2 := ![⟨g2a, ab_mem_subG2 0⟩, ⟨g2b, ab_mem_subG2 1⟩]

theorem cobK_apply (m : Ix3 → ZMod 2) (g : ↥subG2) : coboundaryA muK m g = muK g m - m := rfl

theorem eq_of_agree_K {f f' : ↥subG2 → (Ix3 → ZMod 2)} (hf : f ∈ Z1A muK)
    (hf' : f' ∈ Z1A muK) (h0 : f (gensK 0) = f' (gensK 0)) (h1 : f (gensK 1) = f' (gensK 1)) :
    f = f' := by
  have h := eq_zero_of_vanish_closure (sub_mem hf hf')
    (Subgroup.closure_closure_coe_preimage (k := ({(g2a : Amb), (g2b : Amb)} : Set Amb))) ?_
  · exact sub_eq_zero.mp h
  · rintro s (hs | hs)
    · have e : s = gensK 0 := Subtype.ext hs
      rw [e, Pi.sub_apply]
      exact sub_eq_zero.mpr h0
    · have e : s = gensK 1 := Subtype.ext hs
      rw [e, Pi.sub_apply]
      exact sub_eq_zero.mpr h1

@[expose] def matA6 : Matrix Ix3 Ix3 (ZMod 2) := matA2.submatrix embQ embQ

@[expose] def matB6 : Matrix Ix3 Ix3 (ZMod 2) := matB2.submatrix embQ embQ

theorem muK_gens0
    (w : Ix3 → ZMod 2) : muK (gensK 0) w = matA6 *ᵥ w := by
  change g2Act g2a w = matA6 *ᵥ w
  rw [g2Act_eq_mulVec, cmat_g2a]
  rfl

theorem muK_gens1
    (w : Ix3 → ZMod 2) : muK (gensK 1) w = matB6 *ᵥ w := by
  change g2Act g2b w = matB6 *ᵥ w
  rw [g2Act_eq_mulVec, cmat_g2b]
  rfl

theorem muK_gens
    (i : Fin 2) (w : Ix3 → ZMod 2) : muK (gensK i) w = ![matA6, matB6] i *ᵥ w := by
  fin_cases i
  · exact muK_gens0 w
  · exact muK_gens1 w

@[expose] def foxQ {k : ℕ} (mats : Fin k → Matrix Ix3 Ix3 (ZMod 2))
    (vals : Fin k → Ix3 → ZMod 2) : List (Fin k) → Ix3 → ZMod 2
  | [] => 0
  | i :: w => vals i + mats i *ᵥ foxQ mats vals w

theorem foxEval_K
    (vals : Fin 2 → Ix3 → ZMod 2) (w : List (Fin 2)) :
    foxEval muK gensK vals w = foxQ ![matA6, matB6] vals w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change vals i + muK (gensK i) (foxEval muK gensK vals w) =
      vals i + ![matA6, matB6] i *ᵥ foxQ ![matA6, matB6] vals w
    rw [ih, muK_gens]

theorem g2a_cube :
    g2a * (g2a * g2a) = 1 :=
  cmat_injective (by rw [map_mul, map_mul, cmat_g2a, map_one]; decide +kernel)

theorem g2b_cube :
    g2b * (g2b * g2b) = 1 :=
  cmat_injective (by rw [map_mul, map_mul, cmat_g2b, map_one]; decide +kernel)

theorem gensK_cube
    (i : Fin 2) : gensK i * (gensK i * gensK i) = 1 := by
  fin_cases i
  · have h := congrArg (fun g : ↥(cayleyGroup (ZMod 2)) => (g : Amb)) g2a_cube
    exact Subtype.ext h
  · have h := congrArg (fun g : ↥(cayleyGroup (ZMod 2)) => (g : Amb)) g2b_cube
    exact Subtype.ext h

@[expose] def wK1 : List (Fin 2) := [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]

@[expose] def wK2 : List (Fin 2) := [1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1]

theorem rel_ab
    : wordEval ![g2a, g2b] wK1 = wordEval ![g2a, g2b] wK2 := by
  apply cmat_injective
  rw [cmat_wordEval _ _ cmat_ab, cmat_wordEval _ _ cmat_ab]
  decide +kernel

theorem wordK_rel :
    wordEval gensK wK1 = wordEval gensK wK2 := by
  apply Subtype.ext
  rw [coe_wordEval_sub, coe_wordEval_sub]
  have hg : (fun i => ((gensK i : ↥subG2) : Amb)) = ![(g2a : Amb), (g2b : Amb)] := by
    funext i
    fin_cases i <;> rfl
  rw [hg, ← coe_wordEval_ab, ← coe_wordEval_ab, rel_ab]

@[expose] def cocK : ↥subG2 → Ix3 → ZMod 2 := fG ∘ Subgroup.inclusion subG2_le

theorem cocK_mem : cocK ∈ Z1A muK := Z1A_comp _ fG_mem

theorem fG_g2a :
    fG g2a = q6 1 0 1 1 0 1 := by
  have hM : cmat g2a⁻¹ = matA2 * matA2 := by
    rw [inv_eq_of_mul_eq_one_right g2a_cube, map_mul, cmat_g2a]
  simp only [fG, ellG_eq_of_cmat hM]
  decide +kernel

theorem fG_g2b :
    fG g2b = 0 := by
  have hM : cmat g2b⁻¹ = matB2 * matB2 := by
    rw [inv_eq_of_mul_eq_one_right g2b_cube, map_mul, cmat_g2b]
  simp only [fG, ellG_eq_of_cmat hM]
  decide +kernel

theorem cocK_gens0 :
    cocK (gensK 0) = q6 1 0 1 1 0 1 := fG_g2a

theorem cocK_gens1 :
    cocK (gensK 1) = 0 := fG_g2b

theorem sol_a6 : ∀ u₀ u₁ u₂ u₃ u₄ u₅ : ZMod 2,
    q6 u₀ u₁ u₂ u₃ u₄ u₅ + matA6 *ᵥ (q6 u₀ u₁ u₂ u₃ u₄ u₅ + matA6 *ᵥ q6 u₀ u₁ u₂ u₃ u₄ u₅) = 0 →
    ∃ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2,
      q6 u₀ u₁ u₂ u₃ u₄ u₅ = matA6 *ᵥ q6 x₀ x₁ x₂ x₃ x₄ x₅ - q6 x₀ x₁ x₂ x₃ x₄ x₅ := by
  decide +kernel

theorem sol_b6 : ∀ v₀ v₁ v₂ v₃ v₄ v₅ : ZMod 2,
    q6 v₀ v₁ v₂ v₃ v₄ v₅ + matB6 *ᵥ (q6 v₀ v₁ v₂ v₃ v₄ v₅ + matB6 *ᵥ q6 v₀ v₁ v₂ v₃ v₄ v₅) = 0 →
    foxQ ![matA6, matB6] ![0, q6 v₀ v₁ v₂ v₃ v₄ v₅] wK1 =
      foxQ ![matA6, matB6] ![0, q6 v₀ v₁ v₂ v₃ v₄ v₅] wK2 →
    (∃ y₀ y₁ y₂ y₃ y₄ y₅ : ZMod 2,
      matA6 *ᵥ q6 y₀ y₁ y₂ y₃ y₄ y₅ - q6 y₀ y₁ y₂ y₃ y₄ y₅ = 0 ∧
      q6 v₀ v₁ v₂ v₃ v₄ v₅ = matB6 *ᵥ q6 y₀ y₁ y₂ y₃ y₄ y₅ - q6 y₀ y₁ y₂ y₃ y₄ y₅) ∨
    (∃ y₀ y₁ y₂ y₃ y₄ y₅ : ZMod 2,
      q6 1 0 1 1 0 1 + (matA6 *ᵥ q6 y₀ y₁ y₂ y₃ y₄ y₅ - q6 y₀ y₁ y₂ y₃ y₄ y₅) = 0 ∧
      q6 v₀ v₁ v₂ v₃ v₄ v₅ =
        (0 : Ix3 → ZMod 2) + (matB6 *ᵥ q6 y₀ y₁ y₂ y₃ y₄ y₅ - q6 y₀ y₁ y₂ y₃ y₄ y₅)) := by
  decide +kernel

theorem not_cob_K : ¬∃ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2,
    q6 1 0 1 1 0 1 = matA6 *ᵥ q6 x₀ x₁ x₂ x₃ x₄ x₅ - q6 x₀ x₁ x₂ x₃ x₄ x₅ ∧
    (0 : Ix3 → ZMod 2) = matB6 *ᵥ q6 x₀ x₁ x₂ x₃ x₄ x₅ - q6 x₀ x₁ x₂ x₃ x₄ x₅ := by
  decide +kernel

theorem cocK_not_mem :
    cocK ∉ B1A muK := by
  rintro ⟨v, hv⟩
  have e0 : q6 1 0 1 1 0 1 = matA6 *ᵥ v - v := by
    rw [← cocK_gens0, ← hv, cobK_apply, muK_gens0]
  have e1 : (0 : Ix3 → ZMod 2) = matB6 *ᵥ v - v := by
    rw [← cocK_gens1, ← hv, cobK_apply, muK_gens1]
  rw [q6_eta v] at e0 e1
  exact not_cob_K ⟨_, _, _, _, _, _, e0, e1⟩

theorem cube_rel {φ : ↥subG2 → Ix3 → ZMod 2} (hφ : φ ∈ Z1A muK) {g : ↥subG2}
    (hg : g * (g * g) = 1) : φ g + muK g (φ g + muK g (φ g)) = 0 := by
  have h := hφ g (g * g)
  rw [hφ g g, hg, Z1A_one hφ] at h
  exact h.symm

theorem Z1A_K_cases
    {f : ↥subG2 → Ix3 → ZMod 2} (hf : f ∈ Z1A muK) :
    f ∈ B1A muK ∨ f - cocK ∈ B1A muK := by
  have hu := cube_rel hf (gensK_cube 0)
  rw [muK_gens0, muK_gens0, q6_eta (f (gensK 0))] at hu
  obtain ⟨x₀, x₁, x₂, x₃, x₄, x₅, hx⟩ := sol_a6 _ _ _ _ _ _ hu
  set x : Ix3 → ZMod 2 := q6 x₀ x₁ x₂ x₃ x₄ x₅
  set f' := f - coboundaryA muK x with hf'def
  have hf' : f' ∈ Z1A muK := sub_mem hf (B1A_le_Z1A _ ⟨x, rfl⟩)
  have hff : f = f' + coboundaryA muK x := by rw [hf'def, sub_add_cancel]
  have hf'a : f' (gensK 0) = 0 := by
    rw [hf'def, Pi.sub_apply, cobK_apply, muK_gens0, sub_eq_zero,
      q6_eta (f (gensK 0)), hx]
  have hv := cube_rel hf' (gensK_cube 1)
  rw [muK_gens1, muK_gens1] at hv
  have hvals : (fun i => f' (gensK i)) = ![0, f' (gensK 1)] := by
    funext i
    fin_cases i
    · exact hf'a
    · rfl
  have hw : foxQ ![matA6, matB6] ![0, f' (gensK 1)] wK1 =
      foxQ ![matA6, matB6] ![0, f' (gensK 1)] wK2 := by
    rw [← hvals, ← foxEval_K, ← foxEval_K, ← Z1A_wordEval hf', ← Z1A_wordEval hf', wordK_rel]
  rw [q6_eta (f' (gensK 1))] at hv hw
  rcases sol_b6 _ _ _ _ _ _ hv hw with
    ⟨y₀, y₁, y₂, y₃, y₄, y₅, hy₀, hy₁⟩ | ⟨y₀, y₁, y₂, y₃, y₄, y₅, hy₀, hy₁⟩
  · left
    have e : f' = coboundaryA muK (q6 y₀ y₁ y₂ y₃ y₄ y₅) := by
      refine eq_of_agree_K hf' (B1A_le_Z1A _ ⟨_, rfl⟩) ?_ ?_
      · rw [hf'a, cobK_apply, muK_gens0, hy₀]
      · rw [cobK_apply, muK_gens1, q6_eta (f' (gensK 1)), hy₁]
    rw [hff, e]
    exact add_mem ⟨_, rfl⟩ ⟨_, rfl⟩
  · right
    have e : f' = cocK + coboundaryA muK (q6 y₀ y₁ y₂ y₃ y₄ y₅) := by
      refine eq_of_agree_K hf' (add_mem cocK_mem (B1A_le_Z1A _ ⟨_, rfl⟩)) ?_ ?_
      · rw [hf'a, Pi.add_apply, cocK_gens0, cobK_apply, muK_gens0, hy₀]
      · rw [Pi.add_apply, cocK_gens1, cobK_apply, muK_gens1, q6_eta (f' (gensK 1)), hy₁]
    have e' : f - cocK = coboundaryA muK (q6 y₀ y₁ y₂ y₃ y₄ y₅) + coboundaryA muK x := by
      rw [hff, e]
      abel
    rw [e']
    exact add_mem ⟨_, rfl⟩ ⟨_, rfl⟩

theorem card_Z1A_K
    : Nat.card (Z1A muK) = 2 * Nat.card (B1A muK) := by
  let Φ : ZMod 2 × B1A muK → Z1A muK := fun p =>
    ⟨p.1.val • cocK + p.2.1, add_mem (AddSubgroup.nsmul_mem _ cocK_mem _) (B1A_le_Z1A _ p.2.2)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨c, b⟩ ⟨c', b'⟩ h
      have h' : c.val • cocK + b.1 = c'.val • cocK + b'.1 := by
        simpa [Φ] using congrArg Subtype.val h
      have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      have key : c = c' := by
        rcases hc c with rfl | rfl <;> rcases hc c' with rfl | rfl
        · rfl
        · exfalso
          apply cocK_not_mem
          have : cocK = b.1 - b'.1 := by
            simp only [ZMod.val_zero, zero_smul, zero_add, ZMod.val_one, one_smul] at h'
            rw [h']
            abel
          rw [this]
          exact sub_mem b.2 b'.2
        · exfalso
          apply cocK_not_mem
          have : cocK = b'.1 - b.1 := by
            simp only [ZMod.val_zero, zero_smul, zero_add, ZMod.val_one, one_smul] at h'
            rw [← h']
            abel
          rw [this]
          exact sub_mem b'.2 b.2
        · rfl
      subst key
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h'))
    · rintro ⟨f, hf⟩
      rcases Z1A_K_cases hf with h | h
      · exact ⟨(0, ⟨f, h⟩), Subtype.ext (by simp [Φ])⟩
      · exact ⟨(1, ⟨f - cocK, h⟩), Subtype.ext (by simp only [Φ, ZMod.val_one, one_smul]; abel)⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_zmod]

end CFSG.Quasithin.JonesParshall
