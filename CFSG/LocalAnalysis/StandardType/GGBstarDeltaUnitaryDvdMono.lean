module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryMat

public section

namespace CFSG.StandardType

namespace TableBUM

open Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] {d : ℕ}

theorem commute_of_conj_eq_smul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 4 ≤ d)
    {W : Subgroup (Fin d → Kˣ)} (hW0 : ∀ σ ∈ W, σ ⟨0, by omega⟩ = 1)
    (hWp : ∀ σ ∈ W, ∀ k, σ k ^ p = 1) (hsep : ∀ k l : Fin d, k ≠ l → ∃ σ ∈ W, σ k ≠ σ l)
    (hcard : p ^ (d - 2) ≤ Nat.card W) {B : GL (Fin d) K}
    (hB : ∀ σ ∈ W, ∃ c : Kˣ,
      B * diagHom d σ = Matrix.GeneralLinearGroup.scalar (Fin d) c * diagHom d σ * B) :
    ∀ σ ∈ W, B * diagHom d σ = diagHom d σ * B := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set o : Fin d := ⟨0, by omega⟩ with ho
  have hcol : ∀ l, ∃ k, (B : Matrix (Fin d) (Fin d) K) k l ≠ 0 := by
    intro l
    by_contra hcon
    push Not at hcon
    have h1 : ((B⁻¹ * B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) l l = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Matrix.mul_apply] at h1
    simp [hcon] at h1
  choose π hπ using hcol
  have hrel : ∀ σ : Fin d → Kˣ, ∀ c : Kˣ,
      B * diagHom d σ = Matrix.GeneralLinearGroup.scalar (Fin d) c * diagHom d σ * B →
        ∀ l, σ l = c * σ (π l) := by
    intro σ c hc l
    have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin d) K =>
      (g : Matrix (Fin d) (Fin d) K)) hc) (π l)) l
    simp only [Units.val_mul, coe_diagHom, Matrix.mul_diagonal,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul] at h1
    apply Units.ext
    rw [Units.val_mul]
    have hne := hπ l
    have h2 : ((B : Matrix (Fin d) (Fin d) K) (π l) l) * ((σ l : Kˣ) : K) =
        ((B : Matrix (Fin d) (Fin d) K) (π l) l) * (((c : Kˣ) : K) * (σ (π l) : K)) := by
      rw [h1]
      ring
    exact mul_left_cancel₀ hne h2
  have hπinj : ∀ l l', π l = π l' → l = l' := by
    intro l l' hll'
    by_contra hne
    obtain ⟨σ, hσ, hσne⟩ := hsep l l' hne
    obtain ⟨c, hc⟩ := hB σ hσ
    exact hσne (by rw [hrel σ c hc l, hrel σ c hc l', hll'])
  have hstep : ∀ σ ∈ W, ∀ l, σ (π l) = σ (π o) * σ l := by
    intro σ hσ l
    obtain ⟨c, hc⟩ := hB σ hσ
    have h0 := hrel σ c hc o
    rw [hW0 σ hσ] at h0
    have hl := hrel σ c hc l
    have hco : σ (π o) = c⁻¹ := eq_inv_of_mul_eq_one_right h0.symm
    rw [hco, hl, ← mul_assoc, inv_mul_cancel, one_mul]
  have hc1 : ∀ σ ∈ W, ∀ c : Kˣ,
      B * diagHom d σ = Matrix.GeneralLinearGroup.scalar (Fin d) c * diagHom d σ * B → c = 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨σ₁, hσ₁, c₁, hc₁, hc₁1⟩ := hcon
    have hr₁ := hrel σ₁ c₁ hc₁
    have hc₁p : c₁ ^ p = 1 := by
      have h0 := hr₁ o
      rw [hW0 σ₁ hσ₁] at h0
      have h1 : c₁ = (σ₁ (π o))⁻¹ := eq_inv_of_mul_eq_one_left h0.symm
      rw [h1, inv_pow, hWp σ₁ hσ₁, inv_one]
    have hfix : ∀ l, π l ≠ l := by
      intro l hl
      apply hc₁1
      have h1 := hr₁ l
      rw [hl] at h1
      exact (mul_eq_right.mp h1.symm)
    have h2c : ∀ l, π (π l) ≠ l := by
      intro l hl
      apply hc₁1
      have h1 := hr₁ l
      have h2 := hr₁ (π l)
      rw [hl] at h2
      have h3 : σ₁ l = c₁ ^ 2 * σ₁ l := by
        rw [sq, mul_assoc, ← h2, ← h1]
      have h4 : c₁ ^ 2 = 1 := by
        have := mul_eq_right.mp h3.symm
        exact this
      have h5 := pow_gcd_eq_one.mpr ⟨h4, hc₁p⟩
      rwa [show Nat.gcd 2 p = 1 from (Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm,
        pow_one] at h5
    set a := π o with ha
    set b := π a with hb
    have hao : a ≠ o := hfix o
    have hbo : b ≠ o := h2c o
    have hba : b ≠ a := hfix a
    obtain ⟨z, x, hzo, hzb, hza, hzx, hx⟩ : ∃ z x : Fin d, z ≠ o ∧ z ≠ b ∧ z ≠ a ∧
        π x = z ∧ (x = b ∨ (x ≠ o ∧ x ≠ b ∧ x ≠ z)) := by
      by_cases h3 : π b = o
      · obtain ⟨x, hxo, hxa, hxb⟩ : ∃ x : Fin d, x ≠ o ∧ x ≠ a ∧ x ≠ b := by
          by_contra hcon
          push Not at hcon
          have hsub : (Finset.univ : Finset (Fin d)) ⊆ {o, a, b} := fun y _ => by
            by_cases hyo : y = o
            · rw [hyo]; exact Finset.mem_insert_self _ _
            · by_cases hya : y = a
              · rw [hya]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              · rw [hcon y hyo hya]
                exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                  (Finset.mem_singleton_self _))
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_univ, Fintype.card_fin] at h1
          have h2 := Finset.card_le_three (a := o) (b := a) (c := b)
          omega
        refine ⟨π x, x, fun h' => ?_, fun h' => ?_, fun h' => ?_, rfl,
          Or.inr ⟨hxo, hxb, (hfix x).symm⟩⟩
        · exact hxb (hπinj _ _ (h'.trans h3.symm))
        · exact hxa (hπinj _ _ h')
        · exact hxo (hπinj _ _ h')
      · exact ⟨π b, b, h3, hfix b, fun h' => h2c a h', rfl, Or.inl rfl⟩
    set S := ((Finset.univ.erase o).erase b).erase z with hS
    have hmem : ∀ y, y ≠ o → y ≠ b → y ≠ z → y ∈ S := fun y h1 h2 h3 =>
      Finset.mem_erase.mpr ⟨h3, Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr
        ⟨h1, Finset.mem_univ y⟩⟩⟩
    have hScard : S.card = d - 3 := by
      have hbm : b ∈ Finset.univ.erase o := Finset.mem_erase.mpr ⟨hbo, Finset.mem_univ b⟩
      have hzm : z ∈ (Finset.univ.erase o).erase b :=
        Finset.mem_erase.mpr ⟨hzb, Finset.mem_erase.mpr ⟨hzo, Finset.mem_univ z⟩⟩
      rw [hS, Finset.card_erase_of_mem hzm, Finset.card_erase_of_mem hbm,
        Finset.card_erase_of_mem (Finset.mem_univ o), Finset.card_univ, Fintype.card_fin]
      omega
    have hinj : ∀ σ ∈ W, ∀ τ ∈ W, (∀ k ∈ S, σ k = τ k) → σ = τ := by
      intro σ hσ τ hτ hst
      have ha' : σ a = τ a := hst a (hmem a hao (Ne.symm hba) (Ne.symm hza))
      have hb' : σ b = τ b := by
        rw [hb, hstep σ hσ a, hstep τ hτ a, ha']
      have hz' : σ z = τ z := by
        rw [← hzx, hstep σ hσ x, hstep τ hτ x, ha']
        rcases hx with hxb' | ⟨hxo, hxb, hxz⟩
        · rw [hxb', hb']
        · rw [hst x (hmem x hxo hxb hxz)]
      funext y
      by_cases hyo : y = o
      · rw [hyo, hW0 σ hσ, hW0 τ hτ]
      by_cases hyb : y = b
      · rw [hyb, hb']
      by_cases hyz : y = z
      · rw [hyz, hz']
      exact hst y (hmem y hyo hyb hyz)
    have hle := card_le_of_restrict W hWp S hinj
    rw [hScard] at hle
    have : p ^ (d - 3) < p ^ (d - 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  intro σ hσ
  obtain ⟨c, hc⟩ := hB σ hσ
  rw [hc, hc1 σ hσ c hc, map_one, one_mul]

end TableBUM

end CFSG.StandardType
