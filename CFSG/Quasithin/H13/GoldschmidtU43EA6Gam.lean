module

public import CFSG.Quasithin.H13.GoldschmidtU43EA6Mu
public import CFSG.Quasithin.H13.GoldschmidtU43EDat4

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem Amat_word_two : Amat1 = Umat * Amat2 * Umat := by decide
theorem Amat_word_three : Amat1 = Umat * Amat3 := by decide
theorem Amat_word_four : Amat1 = Amat4 * Umat := by decide
theorem Bmat_word_one : Bmat3 = Umat * Vmat * Bmat1 := by decide
theorem Bmat_word_two : Bmat3 = Vmat * Umat * Bmat2 := by decide
theorem Bmat_word_four : Bmat3 = Vmat * Vmat * Bmat4 := by decide

theorem card_A6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem range_chiBar_eq_Lset (e : S.Nbar ≃* alternatingGroup (Fin 6)) :
    Set.range (S.chiBar r) = Lset := by
  obtain ⟨m, m', -, -, hm, hm'⟩ := S.exists_mu_pair r e
  have hmul : ∀ x ∈ Set.range (S.chiBar r), ∀ y ∈ Set.range (S.chiBar r),
      x * y ∈ Set.range (S.chiBar r) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨a * b, S.chiBar_mul r a b⟩
  have hmul' : ∀ {x y : Mat3}, x ∈ Set.range (S.chiBar r) → y ∈ Set.range (S.chiBar r) →
      x * y ∈ Set.range (S.chiBar r) := fun {x y} hx hy => hmul x hx y hy
  have h1 : (1 : Mat3) ∈ Set.range (S.chiBar r) := ⟨1, S.chiBar_one r⟩
  have hU : Umat ∈ Set.range (S.chiBar r) := ⟨S.ubar, S.chiBar_ubar r⟩
  have hV : Vmat ∈ Set.range (S.chiBar r) := ⟨S.vbar, S.chiBar_vbar r⟩
  have hA : Amat1 ∈ Set.range (S.chiBar r) := by
    rcases hm with h | h | h | h
    · rw [← h]; exact ⟨m, rfl⟩
    · rw [Amat_word_two]
      exact hmul' (hmul' hU ⟨m, h⟩) hU
    · rw [Amat_word_three]
      exact hmul' hU ⟨m, h⟩
    · rw [Amat_word_four]
      exact hmul' ⟨m, h⟩ hU
  have hB : Bmat3 ∈ Set.range (S.chiBar r) := by
    rcases hm' with h | h | h | h
    · rw [Bmat_word_one]
      exact hmul' (hmul' hU hV) ⟨m', h⟩
    · rw [Bmat_word_two]
      exact hmul' (hmul' hV hU) ⟨m', h⟩
    · rw [← h]; exact ⟨m', rfl⟩
    · rw [Bmat_word_four]
      exact hmul' (hmul' hV hV) ⟨m', h⟩
  have hsub : Lset ⊆ Set.range (S.chiBar r) := Lset_subset_of_closed hmul h1 hU hV hA hB
  have hcard : (Set.range (S.chiBar r)).ncard = 360 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective (S.chiBar_injective r),
      Nat.card_congr e.toEquiv, card_A6]
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_Lset]) (Set.finite_range _)).symm

theorem chiBar_mem_Lset (e : S.Nbar ≃* alternatingGroup (Fin 6)) (g : S.Nbar) :
    S.chiBar r g ∈ Lset := by
  rw [← S.range_chiBar_eq_Lset r e]
  exact ⟨g, rfl⟩

end JWSetup

end CFSG.Quasithin.H13.U43
