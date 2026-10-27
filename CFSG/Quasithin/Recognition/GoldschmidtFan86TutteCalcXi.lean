module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcWord
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCalcAbelPset

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

namespace Xi

theorem pset_empty (r l : H) : pset r l ∅ = 1 := by
  simp [pset]

theorem pset_singleton (r l : H) (a : ℕ) : pset r l {a} = tx r l a := by
  simp [pset]

theorem symmDiff_singleton_of_notMem {a : ℕ} {U : Finset ℕ} (ha : a ∉ U) :
    symmDiff {a} U = insert a U := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  by_cases hx : x = a
  · subst hx
    simp [ha]
  · simp [hx]

theorem pset_insert (h : IsTutteSys s r l ξ Hs) {m : ℕ} (hm : m < s) (hab : Abel Hs m) {a : ℕ}
    {U : Finset ℕ} (hT : insert a U ⊆ Finset.Icc 1 m) (ha : a ∉ U) :
    pset r l (insert a U) = tx r l a * pset r l U := by
  have hU : U ⊆ Finset.Icc 1 m := (Finset.subset_insert a U).trans hT
  have ha' : ({a} : Finset ℕ) ⊆ Finset.Icc 1 m := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact hT (Finset.mem_insert_self _ _)
  have h1 := pset_mul h hm hab ha' hU
  rw [pset_singleton, symmDiff_singleton_of_notMem ha] at h1
  exact h1.symm

theorem pset_mem (h : IsTutteSys s r l ξ Hs) {m : ℕ} (hm : m ≤ s) {T : Finset ℕ}
    (hT : T ⊆ Finset.Icc 1 m) : pset r l T ∈ Hs m := by
  unfold pset
  refine Subgroup.list_prod_mem _ ?_
  intro g hg
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hg
  obtain ⟨a, haT, rfl⟩ : ∃ a ∈ T, t = a := by simpa using ht
  exact tx_mem_of_le h (Finset.mem_Icc.1 (hT haT)).2 hm

theorem image_sub_subset {i : ℕ} {T : Finset ℕ} (hT : T ⊆ Finset.Icc 1 (i - 1)) :
    T.image (fun t => i - t) ⊆ Finset.Icc 1 (i - 1) := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
  have := Finset.mem_Icc.1 (hT ht)
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

theorem phi_pset (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : 1 ≤ i) (his : i < s)
    (hab : Abel Hs (i - 1)) (φ : H →* H) (y : H)
    (hA : ∀ a : ℕ, 1 ≤ a → a ≤ i - 1 → φ (tx r l a) = y * tx r l ((i - a : ℕ) : ℤ)) :
    ∀ T : Finset ℕ, T ⊆ Finset.Icc 1 (i - 1) →
      φ (pset r l T) = (if Even T.card then 1 else y) * pset r l (T.image fun t => i - t) := by
  have hm : i - 1 < s := by omega
  have hsq : ∀ t : ℕ, 1 ≤ t → t ≤ i - 1 → tx r l t ^ 2 = 1 := fun t h1 h2 =>
    abel_sq_eq_one h hm hab h1 h2
  have hB : ∀ t : ℕ, 1 ≤ t → t ≤ i - 1 → y * tx r l t * y = tx r l t := by
    intro t h1 h2
    have ha := hA (i - t) (by omega) (by omega)
    rw [show i - (i - t) = t by omega] at ha
    have h3 : φ (tx r l ((i - t : ℕ) : ℤ)) ^ 2 = 1 := by
      rw [← map_pow, hsq (i - t) (by omega) (by omega), map_one]
    rw [ha] at h3
    have h4 : y * tx r l t * y = (tx r l t)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [pow_two, mul_assoc] using h3)
    rw [h4]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq t h1 h2)
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    simp [pset_empty]
  | insert a U ha ih =>
    intro hT
    have hU : U ⊆ Finset.Icc 1 (i - 1) := (Finset.subset_insert a U).trans hT
    have haI := Finset.mem_Icc.1 (hT (Finset.mem_insert_self a U))
    have hR : insert (i - a) (U.image fun t => i - t) ⊆ Finset.Icc 1 (i - 1) := by
      rw [← Finset.image_insert]
      exact image_sub_subset hT
    have hnot : i - a ∉ U.image fun t => i - t := by
      intro hmem
      obtain ⟨u, hu, hua⟩ := Finset.mem_image.1 hmem
      have huI := Finset.mem_Icc.1 (hU hu)
      have : u = a := by omega
      exact ha (this ▸ hu)
    rw [pset_insert h hm hab hT ha, map_mul, hA a haI.1 haI.2, ih hU, Finset.image_insert,
      pset_insert h hm hab hR hnot, Finset.card_insert_of_notMem ha]
    by_cases hev : Even U.card
    · have hodd : ¬ Even (U.card + 1) := by simpa [Nat.even_add_one] using hev
      simp only [hev, hodd, ↓reduceIte, one_mul, mul_assoc]
    · have hodd : Even (U.card + 1) := by simpa [Nat.even_add_one] using hev
      simp only [hev, hodd, ↓reduceIte, one_mul]
      have hy := hB (i - a) (by omega) (by omega)
      calc y * tx r l ((i - a : ℕ) : ℤ) * (y * pset r l (U.image fun t => i - t))
          = (y * tx r l ((i - a : ℕ) : ℤ) * y) * pset r l (U.image fun t => i - t) := by
            simp only [mul_assoc]
        _ = tx r l ((i - a : ℕ) : ℤ) * pset r l (U.image fun t => i - t) := by rw [hy]

theorem xi_conj_inv_mul (hξ : ξ * ξ = 1) (X Y : H) :
    ξ * (X⁻¹ * Y) * ξ = (ξ * X * ξ)⁻¹ * (ξ * Y * ξ) := by
  have hinv : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hξ
  have key : ∀ g : H, ξ * g * ξ = MulAut.conj ξ g := fun g => by simp [MulAut.conj_apply, hinv]
  rw [key, key, key, map_mul, map_inv]

theorem exists_phi (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : 1 ≤ i) (his : i < s)
    (hab : Abel Hs (i - 1)) :
    ∃ (φ : H →* H) (y : H), (y = (tx r l i)⁻¹ ∨ y = tx r l i) ∧ φ (tx r l i) = y ∧
      ∀ a : ℕ, 1 ≤ a → a ≤ i - 1 → φ (tx r l a) = y * tx r l ((i - a : ℕ) : ℤ) := by
  have hm : i - 1 < s := by omega
  have hinvx : ∀ t : ℕ, 1 ≤ t → t ≤ i - 1 → (tx r l t)⁻¹ = tx r l t := fun t h1 h2 =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact abel_sq_eq_one h hm hab h1 h2)
  have hξinv : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right h.xi_sq
  let φ : H →* H := (MulAut.conj ξ).toMonoidHom.comp (MulAut.conj (r ^ (i : ℤ))).toMonoidHom
  have hφ : ∀ g : H, φ g = ξ * (r ^ (i : ℤ) * g * r ^ (-(i : ℤ))) * ξ := fun g => by
    show (MulAut.conj ξ) ((MulAut.conj (r ^ (i : ℤ))) g) = _
    rw [MulAut.conj_apply, MulAut.conj_apply, hξinv, zpow_neg]
  have hbl : ∀ a : ℤ, φ (tx r l a) =
      ξ * ((tx r l (0 + -(i : ℤ)))⁻¹ * tx r l (a + -(i : ℤ))) * ξ := fun a => by
    have h1 := tx_shift r l 0 a (-(i : ℤ))
    rw [tx_zero, inv_one, one_mul, neg_neg] at h1
    rw [hφ, h1]
  have e1 : -(0 + -(i : ℤ)) = (i : ℤ) := by ring
  have e2 : -((i : ℤ) + -(i : ℤ)) = 0 := by ring
  have e3 : ∀ a : ℕ, a ≤ i → -((a : ℤ) + -(i : ℤ)) = ((i - a : ℕ) : ℤ) := fun a ha => by
    rw [Nat.cast_sub ha]
    ring
  rcases h.xi_case with h7 | h8
  · refine ⟨φ, (tx r l i)⁻¹, Or.inl rfl, ?_, ?_⟩
    · rw [hbl, xi_conj_inv_mul h.xi_sq]
      simp only [xi_tx_7 h h7, e1, e2, tx_zero, mul_one]
    · intro a h1 h2
      rw [hbl, xi_conj_inv_mul h.xi_sq]
      simp only [xi_tx_7 h h7, e1, e3 a (by omega)]
  · refine ⟨φ, tx r l i, Or.inr rfl, ?_, ?_⟩
    · rw [hbl, xi_conj_inv_mul h.xi_sq]
      simp only [xi_tx_8 h h8, e1, e2, tx_zero, inv_inv, inv_one, mul_one]
    · intro a h1 h2
      rw [hbl, xi_conj_inv_mul h.xi_sq]
      simp only [xi_tx_8 h h8, e1, e3 a (by omega), inv_inv]
      rw [hinvx (i - a) (by omega) (by omega)]

end Xi

theorem sq_support (h : IsTutteSys s r l ξ Hs) {i : ℕ} (hi : 1 ≤ i) (his : i < s)
    (hab : Abel Hs (i - 1)) :
    ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 (i - 1) ∧ tx r l i ^ 2 = pset r l T ∧ Even T.card ∧
      ∀ t ∈ T, i - t ∈ T := by
  have hm : i - 1 < s := by omega
  obtain ⟨T, hT, hTeq⟩ := exists_pset h hm hab (tx_sq_mem h hi his)
  obtain ⟨φ, y, hyx, hφi, hA⟩ := Xi.exists_phi h hi his hab
  have hclaim := Xi.phi_pset h hi his hab φ y hA T hT
  have hinv : pset r l T * pset r l T = 1 := by
    rw [pset_mul h hm hab hT hT, symmDiff_self, Finset.bot_eq_empty, Xi.pset_empty]
  have hy2 : y ^ 2 = pset r l T := by
    rcases hyx with hy | hy
    · rw [hy, inv_pow, hTeq]
      exact inv_eq_of_mul_eq_one_right hinv
    · rw [hy, hTeq]
  have hφT : φ (pset r l T) = y ^ 2 := by rw [← hTeq, map_pow, hφi]
  rw [hφT] at hclaim
  by_cases hev : Even T.card
  · refine ⟨T, hT, hTeq, hev, ?_⟩
    simp only [hev, ↓reduceIte, one_mul] at hclaim
    have hRT : T.image (fun t => i - t) = T :=
      pset_inj h hm hab (Xi.image_sub_subset hT) hT (by rw [← hclaim, hy2])
    intro t ht
    have hmem : i - t ∈ T.image (fun t => i - t) := Finset.mem_image_of_mem _ ht
    rwa [hRT] at hmem
  · exfalso
    simp only [hev, ↓reduceIte] at hclaim
    have hyP : y = pset r l (T.image fun t => i - t) :=
      mul_left_cancel (by rw [← pow_two]; exact hclaim)
    have hyK : y ∈ Hs (i - 1) := hyP ▸ Xi.pset_mem h (by omega) (Xi.image_sub_subset hT)
    apply h.x_not_mem i hi his.le
    rcases hyx with hy | hy
    · have := Subgroup.inv_mem _ hyK
      rwa [hy, inv_inv] at this
    · rwa [hy] at hyK

end CFSG.Quasithin.Fan86.Tutte
