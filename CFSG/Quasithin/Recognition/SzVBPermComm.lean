module

public import CFSG.Quasithin.Recognition.SzVBPerm

public section

namespace CFSG.Quasithin.SzVB

open scoped symmDiff

section Products

variable {Ω A : Type*} [DecidableEq Ω] [CommGroup A] {t : Ω → A} {z : A}

omit [DecidableEq Ω] in
theorem prod_mul_self_eq_one (htt : ∀ a, t a * t a = 1) (I : Finset Ω) :
    (∏ a ∈ I, t a) * ∏ a ∈ I, t a = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun a _ => htt a

theorem prod_symmDiff_eq (htt : ∀ a, t a * t a = 1) (J J' : Finset Ω) :
    ∏ a ∈ J ∆ J', t a = (∏ a ∈ J, t a) * ∏ a ∈ J', t a := by
  have h1 : J ∆ J' = (J ∪ J') \ (J ∩ J') := by
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    tauto
  have h2 := Finset.prod_sdiff (f := t) (Finset.inter_subset_union : J ∩ J' ⊆ J ∪ J')
  have h3 := Finset.prod_union_inter (f := t) (s₁ := J) (s₂ := J')
  have h4 := prod_mul_self_eq_one htt (J ∩ J')
  rw [h1, ← h3, ← h2, mul_assoc, h4, mul_one]

theorem mem_pair_mul (hzz : z * z = 1) {a b : A} (ha : a = 1 ∨ a = z) (hb : b = 1 ∨ b = z) :
    a * b = 1 ∨ a * b = z := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, hzz]

theorem mem_pair_inv (hzz : z * z = 1) {a : A} (ha : a = 1 ∨ a = z) : a⁻¹ = 1 ∨ a⁻¹ = z := by
  rcases ha with ha | ha
  · simp [ha]
  · exact Or.inr (by rw [ha]; exact inv_eq_of_mul_eq_one_right hzz)

theorem exists_phi_prod (hzz : z * z = 1) (φ : A →* A) (σ : Ω → Ω)
    (hφ : ∀ x, φ (t x) = t (σ x) * t x ∨ φ (t x) = t (σ x) * t x * z) (K : Finset Ω) :
    ∃ ε : A, (ε = 1 ∨ ε = z) ∧ φ (∏ a ∈ K, t a) = (∏ a ∈ K, (t (σ a) * t a)) * ε := by
  refine Finset.induction_on K ⟨1, Or.inl rfl, by simp⟩ ?_
  intro a K ha ih
  obtain ⟨ε, hε, hK⟩ := ih
  rw [Finset.prod_insert ha, Finset.prod_insert ha, map_mul, hK]
  rcases hφ a with h | h
  · exact ⟨ε, hε, by rw [h]; ac_rfl⟩
  · exact ⟨z * ε, mem_pair_mul hzz (Or.inr rfl) hε, by rw [h]; ac_rfl⟩

theorem disjoint_image_of_subset {σ : Ω → Ω} {R K : Finset Ω} (hR : ∀ x ∈ R, σ x ∉ R)
    (hK : K ⊆ R) : Disjoint (K.image σ) K := by
  rw [Finset.disjoint_left]
  intro a ha haK
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
  exact hR x (hK hx) (hK haK)

theorem prod_mul_image_eq {σ : Ω → Ω} (hσ : Function.Injective σ) {K : Finset Ω}
    (hdisj : Disjoint (K.image σ) K) :
    ∏ a ∈ K, (t (σ a) * t a) = ∏ a ∈ K.image σ ∪ K, t a := by
  rw [Finset.prod_union hdisj, Finset.prod_image hσ.injOn, Finset.prod_mul_distrib]

end Products

section Action

variable {X Ω A : Type*} [Group X] [MulAction X Ω] [CommGroup A] {ρ : X →* MulAut A}
  {t : Ω → A} {z : A}

theorem TData.exists_act (hT : TData ρ t z) (g : X) (a : Ω) :
    ∃ ε : A, (ε = 1 ∨ ε = z) ∧ ρ g (t a) = t (g • a) * ε := by
  rcases hT.act g a with h | h
  · exact ⟨1, Or.inl rfl, by rw [h, mul_one]⟩
  · exact ⟨z, Or.inr rfl, h⟩

theorem TData.act_eq_of_mem (hT : TData ρ t z) {ε : A} (hε : ε = 1 ∨ ε = z) (g : X) :
    ρ g ε = ε := by
  rcases hε with hε | hε
  · rw [hε, map_one]
  · rw [hε, hT.z_fix g]

theorem commMap_eq_mul_inv (ρ : X →* MulAut A) (s : X) (a : A) :
    commMap ρ s a = ρ s a * a⁻¹ := by
  simp [commMap]

theorem commMap_commMap_of_sq (ρ : X →* MulAut A) (e e' : X) {a : A} (ha : a * a = 1) :
    commMap ρ e' (commMap ρ e a) = ρ e' (ρ e a) * ρ e' a * ρ e a * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hu : (ρ e a)⁻¹ = ρ e a := by rw [← map_inv, ha']
  rw [commMap_eq_mul_inv, commMap_eq_mul_inv, ha', map_mul, mul_inv, hu, ha']
  ac_rfl

end Action

variable {X Ω A : Type*} [Group X] [MulAction X Ω] [Fintype Ω] [DecidableEq Ω] [CommGroup A]
  {ρ : X →* MulAut A} {t : Ω → A} {z : A}

theorem eq_of_phi_prod_eq (hker : KerProp t z) (hodd : Odd (Fintype.card Ω))
    (htt : ∀ a, t a * t a = 1) (hzz : z * z = 1) (φ : A →* A) (σ : Ω → Ω)
    (hσ : Function.Injective σ) (R : Finset Ω) (hR : ∀ x ∈ R, σ x ∉ R)
    (hφ : ∀ x, φ (t x) = t (σ x) * t x ∨ φ (t x) = t (σ x) * t x * z)
    {J J' : Finset Ω} (hJ : J ⊆ R) (hJ' : J' ⊆ R)
    (h : φ (∏ a ∈ J, t a) = φ (∏ a ∈ J', t a)) : J = J' := by
  have hK : J ∆ J' ⊆ R := by
    intro a ha
    rcases Finset.mem_symmDiff.1 ha with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hJ h1
    · exact hJ' h1
  have hdisj := disjoint_image_of_subset hR hK
  have h1 : φ (∏ a ∈ J ∆ J', t a) = 1 := by
    calc φ (∏ a ∈ J ∆ J', t a) = φ ((∏ a ∈ J, t a) * ∏ a ∈ J', t a) := by
          rw [prod_symmDiff_eq htt]
      _ = φ (∏ a ∈ J, t a) * φ (∏ a ∈ J', t a) := map_mul φ _ _
      _ = φ (∏ a ∈ J, t a) * φ (∏ a ∈ J, t a) := by rw [h]
      _ = φ ((∏ a ∈ J, t a) * ∏ a ∈ J, t a) := (map_mul φ _ _).symm
      _ = 1 := by rw [prod_mul_self_eq_one htt, map_one]
  obtain ⟨ε, hε, hφK⟩ := exists_phi_prod hzz φ σ hφ (J ∆ J')
  rw [hφK, prod_mul_image_eq hσ hdisj] at h1
  have h2 : (∏ a ∈ (J ∆ J').image σ ∪ J ∆ J', t a) = 1 ∨
      (∏ a ∈ (J ∆ J').image σ ∪ J ∆ J', t a) = z := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact mem_pair_inv hzz hε
  rcases hker _ h2 with h3 | h3
  · exact Finset.symmDiff_eq_empty.1 (Finset.union_eq_empty.1 h3).2
  · exfalso
    have hc := congrArg Finset.card h3
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hσ,
      Finset.card_univ] at hc
    obtain ⟨m, hm⟩ := hodd
    omega

theorem card_range_ge_of_indep [Finite A] (hker : KerProp t z) (hodd : Odd (Fintype.card Ω))
    (htt : ∀ a, t a * t a = 1) (hzz : z * z = 1) (φ : A →* A) (σ : Ω → Ω)
    (hσ : Function.Injective σ) (R : Finset Ω) (hR : ∀ x ∈ R, σ x ≠ x ∧ σ x ∉ R)
    (hφ : ∀ x, φ (t x) = t (σ x) * t x ∨ φ (t x) = t (σ x) * t x * z) :
    2 ^ R.card ≤ Nat.card φ.range := by
  let f : R.powerset → φ.range := fun J => ⟨φ (∏ a ∈ J.1, t a), MonoidHom.mem_range.2 ⟨_, rfl⟩⟩
  have hf : Function.Injective f := by
    intro J J' hJJ
    exact Subtype.ext (eq_of_phi_prod_eq hker hodd htt hzz φ σ hσ R (fun x hx => (hR x hx).2) hφ
      (Finset.mem_powerset.1 J.2) (Finset.mem_powerset.1 J'.2) (congrArg Subtype.val hJJ))
  have hcard := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powerset] at hcard

theorem orbit_le_two_of_quadratic (hT : TData ρ t z) (hker : KerProp t z)
    (hΩ : 5 ≤ Fintype.card Ω) (e e' : X) (x : Ω)
    (hq : commMap ρ e' (commMap ρ e (t x)) = 1 ∨ commMap ρ e' (commMap ρ e (t x)) = z) :
    e • x = x ∨ e' • x = x ∨ e • x = e' • x := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hzz := hT.z_sq
  have htt := hT.t_sq
  rw [commMap_commMap_of_sq ρ e e' (htt x)] at hq
  obtain ⟨ε1, hε1, hu⟩ := hT.exists_act e x
  obtain ⟨ε2, hε2, hv⟩ := hT.exists_act e' x
  obtain ⟨ε3, hε3, hw⟩ := hT.exists_act e' (e • x)
  have hρε1 : ρ e' ε1 = ε1 := hT.act_eq_of_mem hε1 e'
  have hD : ρ e' (ρ e (t x)) * ρ e' (t x) * ρ e (t x) * t x =
      (t (e' • e • x) * t (e' • x) * t (e • x) * t x) * (ε3 * ε1 * ε2 * ε1) := by
    rw [hu, map_mul, hw, hρε1, hv]
    ac_rfl
  have hε : ε3 * ε1 * ε2 * ε1 = 1 ∨ ε3 * ε1 * ε2 * ε1 = z :=
    mem_pair_mul hzz (mem_pair_mul hzz (mem_pair_mul hzz hε3 hε1) hε2) hε1
  have hPi : (t (e' • e • x) * t (e' • x) * t (e • x) * t x) = 1 ∨
      (t (e' • e • x) * t (e' • x) * t (e • x) * t x) = z := by
    have hPieq : (t (e' • e • x) * t (e' • x) * t (e • x) * t x) =
        (ρ e' (ρ e (t x)) * ρ e' (t x) * ρ e (t x) * t x) * (ε3 * ε1 * ε2 * ε1)⁻¹ := by
      rw [hD, mul_inv_cancel_right]
    rw [hPieq]
    exact mem_pair_mul hzz hq (mem_pair_inv hzz hε)
  by_cases hyx : e' • e • x = x
  · have hPix : (t (e' • e • x) * t (e' • x) * t (e • x) * t x) = t (e' • x) * t (e • x) := by
      rw [hyx]
      calc t x * t (e' • x) * t (e • x) * t x = t (e' • x) * t (e • x) * (t x * t x) := by ac_rfl
        _ = t (e' • x) * t (e • x) := by rw [htt, mul_one]
    have hdist := hT.distinct (e' • x) (e • x) (Ne.symm h3)
    rw [hPix] at hPi
    rcases hPi with h | h
    · exact hdist.1 h
    · exact hdist.2 h
  by_cases hye : e' • e • x = e • x
  · have hPie : (t (e' • e • x) * t (e' • x) * t (e • x) * t x) = t (e' • x) * t x := by
      rw [hye]
      calc t (e • x) * t (e' • x) * t (e • x) * t x
          = t (e' • x) * t x * (t (e • x) * t (e • x)) := by ac_rfl
        _ = t (e' • x) * t x := by rw [htt, mul_one]
    have hdist := hT.distinct (e' • x) x h2
    rw [hPie] at hPi
    rcases hPi with h | h
    · exact hdist.1 h
    · exact hdist.2 h
  by_cases hyx' : e' • e • x = e' • x
  · exact h1 (smul_left_cancel e' hyx')
  have hn1 : e' • e • x ∉ ({e' • x, e • x, x} : Finset Ω) := by simp [hyx', hye, hyx]
  have hn2 : e' • x ∉ ({e • x, x} : Finset Ω) := by simp [h2, Ne.symm h3]
  have hn3 : e • x ∉ ({x} : Finset Ω) := by simp [h1]
  have hprod : (∏ a ∈ ({e' • e • x, e' • x, e • x, x} : Finset Ω), t a) =
      t (e' • e • x) * t (e' • x) * t (e • x) * t x := by
    rw [Finset.prod_insert hn1, Finset.prod_insert hn2, Finset.prod_insert hn3,
      Finset.prod_singleton]
    ac_rfl
  rcases hker _ (by rw [hprod]; exact hPi) with hI | hI
  · exact Finset.insert_ne_empty _ _ hI
  · have hc := Finset.card_le_four (a := e' • e • x) (b := e' • x) (c := e • x) (d := x)
    rw [hI, Finset.card_univ] at hc
    omega

end CFSG.Quasithin.SzVB
