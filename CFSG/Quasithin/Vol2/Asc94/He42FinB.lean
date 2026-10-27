module

public import CFSG.Quasithin.Vol2.Asc94.He42Fin

public section

namespace CFSG.Quasithin.A94.He42Fin

open Equiv

private abbrev he42fb_a : Perm (Fin 5) := swap 1 2 * swap 3 4

private abbrev he42fb_b : Perm (Fin 5) := swap 1 3 * swap 2 4

private abbrev he42fb_c : Perm (Fin 5) := swap 1 4 * swap 2 3

private abbrev he42fb_w1 (σ : Perm (Fin 5)) : Perm (Fin 5) :=
  σ * he42fb_a * σ⁻¹ * he42fb_a * (σ * he42fb_b * σ⁻¹)

private abbrev he42fb_w2 (σ : Perm (Fin 5)) : Perm (Fin 5) :=
  σ * he42fb_a * σ⁻¹ * he42fb_b * (σ * he42fb_b * σ⁻¹)

private abbrev he42fb_w3 (σ : Perm (Fin 5)) : Perm (Fin 5) :=
  σ * he42fb_a * σ⁻¹ * he42fb_a * he42fb_b * (σ * he42fb_b * σ⁻¹)

private lemma he42fb_of_pow_four :
    ∀ g : Perm (Fin 5), g 0 = 0 → Equiv.Perm.sign g = 1 → g ^ 4 = 1 →
      g = 1 ∨ g = he42fb_a ∨ g = he42fb_b ∨ g = he42fb_c := by
  decide +kernel

private lemma he42fb_transitive :
    ∀ i j : Fin 5, i ≠ 0 → j ≠ 0 →
      ∃ h ∈ ({1, he42fb_a, he42fb_b, he42fb_c} : Finset (Perm (Fin 5))), h i = j := by
  decide +kernel

private lemma he42fb_centralizer :
    ∀ π : Perm (Fin 5), π 0 = 0 → π ^ 3 = 1 → π * he42fb_a = he42fb_a * π →
      π * he42fb_b = he42fb_b * π → π = 1 := by
  decide +kernel

private lemma he42fb_gen_A4 :
    ∀ x y : Perm (Fin 5), x 0 = 0 → Equiv.Perm.sign x = 1 → x ≠ 1 → x ≠ he42fb_a →
      x ≠ he42fb_b → x ≠ he42fb_c → y 0 = 0 → Equiv.Perm.sign y = 1 →
      ∃ v ∈ ({1, he42fb_a, he42fb_b, he42fb_c} : Finset (Perm (Fin 5))), ∃ k : Fin 3,
        y = v * x ^ (k : ℕ) := by
  decide +kernel

private lemma he42fb_word_cover :
    ∀ σ : Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ 0 ≠ 0 →
      (he42fb_w1 σ 0 = 0 ∧ he42fb_w1 σ ≠ 1 ∧ he42fb_w1 σ ≠ he42fb_a ∧
          he42fb_w1 σ ≠ he42fb_b ∧ he42fb_w1 σ ≠ he42fb_c) ∨
      (he42fb_w2 σ 0 = 0 ∧ he42fb_w2 σ ≠ 1 ∧ he42fb_w2 σ ≠ he42fb_a ∧
          he42fb_w2 σ ≠ he42fb_b ∧ he42fb_w2 σ ≠ he42fb_c) ∨
      (he42fb_w3 σ 0 = 0 ∧ he42fb_w3 σ ≠ 1 ∧ he42fb_w3 σ ≠ he42fb_a ∧
          he42fb_w3 σ ≠ he42fb_b ∧ he42fb_w3 σ ≠ he42fb_c) := by
  decide +kernel

private lemma he42fb_conj_moves_zero :
    ∀ σ : Perm (Fin 5), σ 0 ≠ 0 → (σ * he42fb_a * σ⁻¹) 0 ≠ 0 := by
  decide +kernel

private lemma he42fb_mem_iff (H : Subgroup (Perm (Fin 5))) (hH : H ≤ alternatingGroup (Fin 5))
    (hH0 : ∀ h ∈ H, h 0 = 0) (hcard : Nat.card H = 4) (h : Perm (Fin 5)) :
    h ∈ H ↔ h = 1 ∨ h = he42fb_a ∨ h = he42fb_b ∨ h = he42fb_c := by
  have hsub0 : ∀ g ∈ H, g = 1 ∨ g = he42fb_a ∨ g = he42fb_b ∨ g = he42fb_c := by
    intro g hg
    have hdvd := orderOf_dvd_natCard (⟨g, hg⟩ : H)
    rw [hcard, orderOf_dvd_iff_pow_eq_one] at hdvd
    have h4 : g ^ 4 = 1 := by
      have := congrArg (fun y : H => (y : Perm (Fin 5))) hdvd
      simpa using this
    exact he42fb_of_pow_four g (hH0 g hg) (Equiv.Perm.mem_alternatingGroup.mp (hH hg)) h4
  refine ⟨hsub0 h, fun hh => ?_⟩
  have hsub : (H : Set (Perm (Fin 5))) ⊆
      ((({1, he42fb_a, he42fb_b, he42fb_c} : Finset (Perm (Fin 5))) : Set (Perm (Fin 5)))) := by
    intro g hg
    rcases hsub0 g hg with rfl | rfl | rfl | rfl <;> simp
  have hScard : ((({1, he42fb_a, he42fb_b, he42fb_c} : Finset (Perm (Fin 5))) :
      Set (Perm (Fin 5)))).ncard = 4 := by
    rw [Set.ncard_coe_finset]; decide +kernel
  have hHcard : (H : Set (Perm (Fin 5))).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  have heq : (H : Set (Perm (Fin 5))) =
      ((({1, he42fb_a, he42fb_b, he42fb_c} : Finset (Perm (Fin 5))) : Set (Perm (Fin 5)))) :=
    Set.eq_of_subset_of_ncard_le hsub (hScard.trans hHcard.symm).le
  have hmem : h ∈ (H : Set (Perm (Fin 5))) := by
    rw [heq]
    rcases hh with rfl | rfl | rfl | rfl <;> simp
  exact hmem

theorem eq_one_of_commute_klein (H : Subgroup (Perm (Fin 5))) (hH : H ≤ alternatingGroup (Fin 5))
    (hH0 : ∀ h ∈ H, h 0 = 0) (hcard : Nat.card H = 4) (π : Perm (Fin 5)) (hπ0 : π 0 = 0)
    (hπ3 : π ^ 3 = 1) (hcomm : ∀ h ∈ H, π * h = h * π) : π = 1 := by
  have ha : he42fb_a ∈ H := (he42fb_mem_iff H hH hH0 hcard _).mpr (Or.inr (Or.inl rfl))
  have hb : he42fb_b ∈ H := (he42fb_mem_iff H hH hH0 hcard _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  exact he42fb_centralizer π hπ0 hπ3 (hcomm _ ha) (hcomm _ hb)

theorem exists_mem_klein_apply (H : Subgroup (Perm (Fin 5))) (hH : H ≤ alternatingGroup (Fin 5))
    (hH0 : ∀ h ∈ H, h 0 = 0) (hcard : Nat.card H = 4) (i j : Fin 5) (hi : i ≠ 0) (hj : j ≠ 0) :
    ∃ h ∈ H, h i = j := by
  obtain ⟨h, hhS, hhij⟩ := he42fb_transitive i j hi hj
  exact ⟨h, (he42fb_mem_iff H hH hH0 hcard h).mpr (by simpa using hhS), hhij⟩

theorem sup_conj_klein_eq_alternating (H : Subgroup (Perm (Fin 5)))
    (hH : H ≤ alternatingGroup (Fin 5)) (hH0 : ∀ h ∈ H, h 0 = 0) (hcard : Nat.card H = 4)
    (σ : Perm (Fin 5)) (hσ : σ ∈ alternatingGroup (Fin 5)) (hσ0 : σ 0 ≠ 0) :
    H ⊔ H.map (MulAut.conj σ).toMonoidHom = alternatingGroup (Fin 5) := by
  have hHa : he42fb_a ∈ H := (he42fb_mem_iff H hH hH0 hcard _).mpr (Or.inr (Or.inl rfl))
  have hHb : he42fb_b ∈ H := (he42fb_mem_iff H hH hH0 hcard _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  set K : Subgroup (Perm (Fin 5)) := H ⊔ H.map (MulAut.conj σ).toMonoidHom with hK
  have hKH : ∀ x ∈ H, x ∈ K := fun x hx => Subgroup.mem_sup_left hx
  have hKc : ∀ x ∈ H, σ * x * σ⁻¹ ∈ K := fun x hx =>
    Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hKA : K ≤ alternatingGroup (Fin 5) := by
    refine sup_le hH ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem x (hH hx) σ
  refine le_antisymm hKA ?_
  have hA4 : ∀ x ∈ K, x 0 = 0 → x ≠ 1 → x ≠ he42fb_a → x ≠ he42fb_b → x ≠ he42fb_c →
      ∀ y : Perm (Fin 5), y 0 = 0 → Equiv.Perm.sign y = 1 → y ∈ K := by
    intro x hxK hx0 h1 h2 h3 h4 y hy0 hy
    obtain ⟨v, hv, k, rfl⟩ :=
      he42fb_gen_A4 x y hx0 (Equiv.Perm.mem_alternatingGroup.mp (hKA hxK)) h1 h2 h3 h4 hy0 hy
    have hvH : v ∈ H := (he42fb_mem_iff H hH hH0 hcard v).mpr (by simpa using hv)
    exact K.mul_mem (hKH v hvH) (K.pow_mem hxK _)
  have hA4' : ∀ y : Perm (Fin 5), y 0 = 0 → Equiv.Perm.sign y = 1 → y ∈ K := by
    rcases he42fb_word_cover σ (Equiv.Perm.mem_alternatingGroup.mp hσ) hσ0 with
      ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩
    · exact hA4 (he42fb_w1 σ)
        (K.mul_mem (K.mul_mem (hKc _ hHa) (hKH _ hHa)) (hKc _ hHb)) h0 h1 h2 h3 h4
    · exact hA4 (he42fb_w2 σ)
        (K.mul_mem (K.mul_mem (hKc _ hHa) (hKH _ hHb)) (hKc _ hHb)) h0 h1 h2 h3 h4
    · exact hA4 (he42fb_w3 σ)
        (K.mul_mem (K.mul_mem (K.mul_mem (hKc _ hHa) (hKH _ hHa)) (hKH _ hHb)) (hKc _ hHb))
        h0 h1 h2 h3 h4
  intro g hg
  by_cases hg0 : g 0 = 0
  · exact hA4' g hg0 (Equiv.Perm.mem_alternatingGroup.mp hg)
  ·
    obtain ⟨h, hhS, hh⟩ := he42fb_transitive _ _ (he42fb_conj_moves_zero σ hσ0) hg0
    have hhH : h ∈ H := (he42fb_mem_iff H hH hH0 hcard h).mpr (by simpa using hhS)
    have hkK : h * (σ * he42fb_a * σ⁻¹) ∈ K := K.mul_mem (hKH h hhH) (hKc _ hHa)
    have hk0 : (h * (σ * he42fb_a * σ⁻¹)) 0 = g 0 := by
      rw [Equiv.Perm.mul_apply]; exact hh
    have hkA : h * (σ * he42fb_a * σ⁻¹) ∈ alternatingGroup (Fin 5) := hKA hkK
    have hinv0 : ((h * (σ * he42fb_a * σ⁻¹))⁻¹ * g) 0 = 0 := by
      rw [Equiv.Perm.mul_apply, ← hk0]
      exact Equiv.symm_apply_apply (h * (σ * he42fb_a * σ⁻¹)) 0
    have hinvA : (h * (σ * he42fb_a * σ⁻¹))⁻¹ * g ∈ K :=
      hA4' _ hinv0 (Equiv.Perm.mem_alternatingGroup.mp
        ((alternatingGroup (Fin 5)).mul_mem ((alternatingGroup (Fin 5)).inv_mem hkA) hg))
    have hprod := K.mul_mem hkK hinvA
    rwa [mul_inv_cancel_left] at hprod

end CFSG.Quasithin.A94.He42Fin
