module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenIrrA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
  {Δ : Fin (2 + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (2 + 1))}

theorem s168e3_seven_exists_transp (h : s16e_d3_Ctx A L 2 Δ σ) {U : Subgroup (MulAut W)}
    (hUL : U ≤ L) (hU7 : Nat.card U = 7)
    (hUA : ∀ g ∈ A, U.map (MulAut.conj g).toMonoidHom = U) {k : Fin (2 + 1)}
    (hUk : ∀ u ∈ U, u ∈ centSub (Δ k) → u = 1) {i j : Fin (2 + 1)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    ∃ s : ↥A, σ s i = j ∧ σ s k = k ∧
      (∀ u ∈ U, (s : MulAut W) * u * (s : MulAut W)⁻¹ = u) ∧
      ∀ c ∈ L ⊓ centSub (Δ k), (s : MulAut W) * c * (s : MulAut W)⁻¹ = c⁻¹ := by
  obtain ⟨s, hs2, hσ⟩ := s168e3_seven_exists_sq h i j
  have hσi : σ s i = j := by rw [hσ, Equiv.swap_apply_left]
  have hσk : σ s k = k := by
    rw [hσ, Equiv.swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)]
  have hfix := s168e3_seven_fix_of_sq h hs2 hσk
  have hsU := s168e3_seven_cent_of_fix h hUL hUA hUk hfix
  have hdec := s168e3_seven_dec h hUL hU7 hUk
  exact ⟨s, hσi, hσk, hsU, s168e3_seven_inv_line h hdec hs2 hsU hij hσk hσi⟩

private theorem s168e3_seven_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s168e3_seven_pow_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) (x : X) : x ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp

theorem s168e3_seven_irred (h : s16e_d3_Ctx A L 2 Δ σ) {U : Subgroup (MulAut W)}
    (hUL : U ≤ L) (hU7 : Nat.card U = 7)
    (hUA : ∀ g ∈ A, U.map (MulAut.conj g).toMonoidHom = U) : False := by
  have hUk : ∀ k, ∀ u ∈ U, u ∈ centSub (Δ k) → u = 1 :=
    fun k => s168e3_seven_inf_line h hUL hU7 hUA k
  obtain ⟨s, hs0, hs2, hsU, hsC⟩ :=
    s168e3_seven_exists_transp h hUL hU7 hUA (hUk 2) (i := 0) (j := 1)
      (by decide) (by decide) (by decide)
  obtain ⟨s', hs'2, hs'0, hs'U, hs'C⟩ :=
    s168e3_seven_exists_transp h hUL hU7 hUA (hUk 0) (i := 2) (j := 1)
      (by decide) (by decide) (by decide)
  have hC0 : Nat.card ↥(L ⊓ centSub (Δ 0)) = 7 := by
    have := s168e3_seven_card_line h 0
    simpa using this
  obtain ⟨c₀, hc₀, hc₀1⟩ : ∃ c₀ ∈ L ⊓ centSub (Δ 0), c₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : L ⊓ centSub (Δ 0) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hcon x hx)
    rw [this, Subgroup.card_bot] at hC0
    omega
  exact s168e3_seven_lines_false (L := L) (U := U) (C₀ := L ⊓ centSub (Δ 0))
    (C₁ := L ⊓ centSub (Δ 1)) (C₂ := L ⊓ centSub (Δ 2))
    (fun x hx y hy => by
      have := s168e3_seven_comm_of_elem h.elem ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this)
    (fun x hx => by
      have := s168e3_seven_pow_of_elem h.elem ⟨x, hx⟩
      exact congrArg Subtype.val this)
    hUL inf_le_left inf_le_left (s168e3_seven_dec h hUL hU7 (hUk 2))
    (fun x hx hx1 => hUk 1 x hx (Subgroup.mem_inf.1 hx1).2)
    (fun x hx0 hx2 => s168e3_seven_line_inf h (i := 0) (j := 2) (by decide) hx0
      (Subgroup.mem_inf.1 hx2).2)
    hc₀ hc₀1 hsU hsC (by
      have := s168e3_seven_conj_line h s hc₀
      rwa [hs0] at this)
    hs'U (hs'C c₀ hc₀) (fun c hc => by
      have := s168e3_seven_conj_line h s' hc
      rwa [hs'2] at this)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
