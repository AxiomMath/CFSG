module

public import CFSG.Quasithin.Vol2.KGFact12618a

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv

@[expose] def stab7 (p : Fin 7) : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) p

theorem mem_stab7 {p : Fin 7} {σ : Perm (Fin 7)} :
    σ ∈ stab7 p ↔ σ ∈ alternatingGroup (Fin 7) ∧ σ p = p := Iff.rfl

theorem exists_alt7_apply_eq (p q : Fin 7) : ∃ g ∈ alternatingGroup (Fin 7), g p = q := by
  by_cases hpq : p = q
  · exact ⟨1, Subgroup.one_mem _, by rw [hpq]; rfl⟩
  obtain ⟨r, hrp, hrq⟩ : ∃ r : Fin 7, r ≠ p ∧ r ≠ q := by
    revert p q
    decide
  refine ⟨swap p r * swap p q, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap (Ne.symm hrp),
      Perm.sign_swap hpq]
    decide
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hpq) (Ne.symm hrq)]

theorem card_stab7 (p : Fin 7) : Nat.card ↥(stab7 p) = 360 := by
  classical
  have hidx := MulAction.index_stabilizer ↥(alternatingGroup (Fin 7)) p
  have horb : MulAction.orbit ↥(alternatingGroup (Fin 7)) p = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨g, hg, hgq⟩ := exists_alt7_apply_eq p q
    exact ⟨⟨g, hg⟩, hgq⟩
  rw [horb, Set.ncard_univ, Nat.card_fin] at hidx
  have hc := (MulAction.stabilizer ↥(alternatingGroup (Fin 7)) p).card_mul_index
  rw [hidx, nat_card_alternatingGroup, Nat.card_fin] at hc
  have e : Nat.card ↥(MulAction.stabilizer ↥(alternatingGroup (Fin 7)) p) =
      Nat.card ↥(stab7 p) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
        invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← e]
  have : (7 : ℕ).factorial / 2 = 2520 := by decide
  omega

theorem eq_stab7 {H : Subgroup (Perm (Fin 7))} (hH : H ≤ alternatingGroup (Fin 7))
    (h360 : Nat.card ↥H = 360) {p : Fin 7} (hp : ∀ h ∈ H, h p = p) : H = stab7 p := by
  have hle : H ≤ stab7 p := fun h hh => ⟨hH hh, hp h hh⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_stab7, h360])

theorem conj_stab7 (g : Perm (Fin 7)) (p : Fin 7) :
    (stab7 p).map (MulAut.conj g).toMonoidHom = stab7 (g p) := by
  ext σ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_stab7]
  constructor
  · rintro ⟨τ, ⟨hτA, hτp⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Perm.mem_alternatingGroup] at hτA ⊢
      simp only [Perm.sign_mul, Perm.sign_inv, hτA, mul_one]
      exact Int.units_mul_self _
    · simp [Perm.mul_apply, hτp]
  · rintro ⟨hσA, hσp⟩
    refine ⟨g⁻¹ * σ * g, ⟨?_, ?_⟩, by group⟩
    · rw [Perm.mem_alternatingGroup] at hσA ⊢
      simp only [Perm.sign_mul, Perm.sign_inv, hσA, mul_one]
      exact Int.units_mul_self _
    · simp [Perm.mul_apply, hσp]

theorem eq_one_of_commute_stab7 {p : Fin 7} {σ : Perm (Fin 7)}
    (h : ∀ τ ∈ stab7 p, σ * τ = τ * σ) : σ = 1 := by
  set g : Perm (Fin 7) := swap 6 p with hg
  have hg6 : g 6 = p := swap_apply_left 6 p
  have hmem : ∀ τ ∈ stab7 6, g * τ * g⁻¹ ∈ stab7 p := by
    intro τ hτ
    have := conj_stab7 g 6
    rw [hg6] at this
    rw [← this]
    exact ⟨τ, hτ, rfl⟩
  have hc : ∀ τ ∈ stab7 6, (g⁻¹ * σ * g) * τ = τ * (g⁻¹ * σ * g) := by
    intro τ hτ
    have h1 := h _ (hmem τ hτ)
    calc (g⁻¹ * σ * g) * τ = g⁻¹ * (σ * (g * τ * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * τ * g⁻¹) * σ) * g := by rw [h1]
      _ = τ * (g⁻¹ * σ * g) := by group
  have hc₁ : swap (0 : Fin 7) 2 * swap 0 1 ∈ stab7 6 :=
    ⟨Perm.mem_alternatingGroup.2 (by decide), MulAction.mem_stabilizer_iff.2 (by decide)⟩
  have hc₂ : swap (2 : Fin 7) 4 * swap 2 3 ∈ stab7 6 :=
    ⟨Perm.mem_alternatingGroup.2 (by decide), MulAction.mem_stabilizer_iff.2 (by decide)⟩
  have hc₃ : swap (4 : Fin 7) 0 * swap 4 5 ∈ stab7 6 :=
    ⟨Perm.mem_alternatingGroup.2 (by decide), MulAction.mem_stabilizer_iff.2 (by decide)⟩
  have h1 := eq_one_of_commute_c3 (g⁻¹ * σ * g) (hc _ hc₁) (hc _ hc₂) (hc _ hc₃)
  calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

end CFSG.Quasithin.H13.KG12618
