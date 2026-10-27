module

public import CFSG.Timmesfeld.Orders.Distinct
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

@[expose] def rOrd (c f : ℕ) : ℕ :=
  (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * (if c = 3 then (2 ^ f) ^ 3 - 1 else (2 ^ f) ^ 3 + 1)

@[expose] def phiOrd (c q : ℕ) : ℕ := if c = 3 then q ^ 2 + q + 1 else q ^ 2 - q + 1

@[expose] def zR (c f k : ℕ) : Prop :=
  k ∣ f * 2 ∨ (c = 3 ∧ k ∣ f * 3) ∨ (c ≠ 3 ∧ k ∣ 2 * (f * 3) ∧ ¬ k ∣ f * 3)

theorem rcs_profile_rOrd {c f : ℕ} (hc : c = 3 ∨ c = 6) (hf : 1 ≤ f) :
    Profile (rOrd c f) (f * 3) (zR c f) := by
  rcases hc with rfl | rfl
  · have hm : rOrd 3 f = 2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
      simp only [rOrd, ite_true]; rw [pow_mul, mul_assoc]
    refine Profile.of_eq hm ((odd_pow_sub_one hf (by norm_num)).mul
      (odd_pow_sub_one hf (by norm_num))) (fun p k hp hk => ?_)
    rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk, PrimDiv.dvd_pow_sub_one_iff hp hk]
    simp [zR]
  · have hm : rOrd 6 f = 2 ^ (f * 3) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
      simp only [rOrd, show (6 : ℕ) ≠ 3 by norm_num, ite_false]; rw [pow_mul, mul_assoc]
    refine Profile.of_eq hm ((odd_pow_sub_one hf (by norm_num)).mul
      (odd_pow_add_one hf (by norm_num))) (fun p k hp hk => ?_)
    rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk, PrimDiv.dvd_pow_add_one_iff hp hk]
    simp [zR]

theorem rcs_zR_self {c f : ℕ} (hc : c = 3 ∨ c = 6) (hf : 0 < f) : zR c f (c * f) := by
  rcases hc with rfl | rfl
  · exact Or.inr (Or.inl ⟨rfl, ⟨1, by ring⟩⟩)
  · refine Or.inr (Or.inr ⟨by norm_num, ⟨1, by ring⟩, fun h => ?_⟩)
    have := Nat.le_of_dvd (by omega) h
    omega

theorem rcs_transfer {m₁ m₂ N₁ N₂ : ℕ} {Z₁ Z₂ : ℕ → Prop} (h₁ : Profile m₁ N₁ Z₁)
    (h₂ : Profile m₂ N₂ Z₂) (hd : m₁ ∣ m₂) {k : ℕ} (hk : 2 ≤ k) (h6 : k ≠ 6) (hz : Z₁ k) :
    Z₂ k := by
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor hk h6
  exact (h₂.prim p k hp (by omega)).mp (((h₁.prim p k hp (by omega)).mpr hz).trans hd)

theorem rcs_two_le {m₁ m₂ N₁ N₂ : ℕ} {Z₁ Z₂ : ℕ → Prop} (h₁ : Profile m₁ N₁ Z₁)
    (h₂ : Profile m₂ N₂ Z₂) (hd : m₁ ∣ m₂) : N₁ ≤ N₂ := by
  obtain ⟨r₁, hr₁, e₁⟩ := h₁.two
  obtain ⟨r₂, hr₂, e₂⟩ := h₂.two
  by_contra hlt
  rw [not_le] at hlt
  have h1 : 2 ^ (N₂ + 1) ∣ m₂ :=
    ((pow_dvd_pow 2 hlt).trans (e₁ ▸ dvd_mul_right _ _)).trans hd
  rw [e₂, pow_succ] at h1
  have h2 := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ N₂)).mp h1
  exact (Nat.not_even_iff_odd.mpr hr₂) (even_iff_two_dvd.mpr h2)

theorem rcs_prelude {c f m N : ℕ} {Z : ℕ → Prop} (hc : c = 3 ∨ c = 6) (hf : 0 < f)
    (hX : Profile m N Z) (hmM : m ∣ ordTrialityD4 (2 ^ f)) (hRm : rOrd c f ∣ m) :
    f * 3 ≤ N ∧ N ≤ f * 12 ∧ (∀ k, 2 ≤ k → k ≠ 6 → Z k → zD4 f k) ∧
      (∀ k, 2 ≤ k → k ≠ 6 → zR c f k → Z k) := by
  have hM := profile_ordTrialityD4 hf
  have hR := rcs_profile_rOrd hc hf
  exact ⟨rcs_two_le hR hX hRm, rcs_two_le hX hM hmM,
    fun k hk h6 hz => rcs_transfer hX hM hmM hk h6 hz,
    fun k hk h6 hz => rcs_transfer hR hX hRm hk h6 hz⟩

theorem rcs_first_index {c f : ℕ} {Z : ℕ → Prop} (hc : c = 3 ∨ c = 6) (hf : 0 < f)
    (h6 : c * f ≠ 6) (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → Z k) : Z (c * f) := by
  refine hR (c * f) ?_ h6 (rcs_zR_self hc hf)
  rcases hc with rfl | rfl <;> omega

theorem rcs_dvd_mul {s t a x : ℕ} (hs : 0 < s) : s * t ∣ s * a * x ↔ t ∣ a * x := by
  rw [mul_assoc]; exact Nat.mul_dvd_mul_iff_left hs

theorem rcs_dvd_mul₂ {s t a x : ℕ} (hs : 0 < s) :
    s * t ∣ 2 * (s * a * x) ↔ t ∣ 2 * (a * x) := by
  rw [show 2 * (s * a * x) = s * (2 * (a * x)) by ring]; exact Nat.mul_dvd_mul_iff_left hs

theorem rcs_zD4_mul {s b t : ℕ} (hs : 0 < s) : zD4 (s * b) (s * t) ↔ zD4 b t := by
  unfold zD4
  simp only [rcs_dvd_mul hs]

theorem rcs_zR_mul {c s b t : ℕ} (hs : 0 < s) : zR c (s * b) (s * t) ↔ zR c b t := by
  unfold zR
  simp only [rcs_dvd_mul hs, rcs_dvd_mul₂ hs]

theorem rcs_zBC_mul {n s a t : ℕ} (hs : 0 < s) : zBC n (s * a) (s * t) ↔ zBC n a t := by
  unfold zBC
  simp only [rcs_dvd_mul hs]

theorem rcs_z2D_mul {n s a t : ℕ} (hs : 0 < s) : z2D n (s * a) (s * t) ↔ z2D n a t := by
  unfold z2D
  simp only [rcs_dvd_mul hs, rcs_dvd_mul₂ hs]

theorem rcs_zList_mul {L : List ℕ} {s a t : ℕ} (hs : 0 < s) :
    zList (s * a) L (s * t) ↔ zList a L t := by
  unfold zList
  simp only [rcs_dvd_mul hs]

theorem rcs_z2E6_mul {s a t : ℕ} (hs : 0 < s) : z2E6 (s * a) (s * t) ↔ z2E6 a t := by
  unfold z2E6
  simp only [rcs_dvd_mul hs, rcs_dvd_mul₂ hs]

theorem rcs_reduce {Z : ℕ → ℕ → Prop} (hom : ∀ s a t, 0 < s → (Z (s * a) (s * t) ↔ Z a t))
    {c e f g : ℕ} (hf : 0 < f) (hg : 0 < g)
    (hG : ∀ k, 2 ≤ k → k ≠ 6 → Z g k → zD4 f k)
    (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → Z g k)
    (h1 : Z g (c * f)) (h2 : f * 3 ≤ g * e) (h3 : g * e ≤ f * 12) :
    ∃ s a b, 0 < s ∧ g = s * a ∧ f = s * b ∧ Nat.Coprime a b ∧ 0 < a ∧ 0 < b ∧
      Z a (c * b) ∧ b * 3 ≤ a * e ∧ a * e ≤ b * 12 ∧
      (∀ t, 4 ≤ t → t ≠ 6 → Z a t → zD4 b t) ∧ (∀ t, 4 ≤ t → t ≠ 6 → zR c b t → Z a t) := by
  obtain ⟨s, a, b, hs, hab, hga, hfb⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left f hg)
  have hga' : g = s * a := by rw [hga, mul_comm]
  have hfb' : f = s * b := by rw [hfb, mul_comm]
  subst hga' hfb'
  have ha : 0 < a := Nat.pos_of_ne_zero (fun h => by simp [h] at hg)
  have hb : 0 < b := Nat.pos_of_ne_zero (fun h => by simp [h] at hf)
  have hk : ∀ t, 4 ≤ t → t ≠ 6 → 2 ≤ s * t ∧ s * t ≠ 6 := by
    intro t ht4 ht6
    refine ⟨le_trans (by omega) (Nat.le_mul_of_pos_left t hs), fun h => ?_⟩
    have hdvd : t ∣ 6 := ⟨s, by rw [← h]; ring⟩
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases t <;> omega
  refine ⟨s, a, b, hs, rfl, rfl, hab, ha, hb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show c * (s * b) = s * (c * b) by ring] at h1
    exact (hom s a (c * b) hs).mp h1
  · have h2' : s * (b * 3) ≤ s * (a * e) := by
      calc s * (b * 3) = s * b * 3 := by ring
        _ ≤ s * a * e := h2
        _ = s * (a * e) := by ring
    exact Nat.le_of_mul_le_mul_left h2' hs
  · have h3' : s * (a * e) ≤ s * (b * 12) := by
      calc s * (a * e) = s * a * e := by ring
        _ ≤ s * b * 12 := h3
        _ = s * (b * 12) := by ring
    exact Nat.le_of_mul_le_mul_left h3' hs
  · intro t ht4 ht6 hz
    obtain ⟨hk2, hk6⟩ := hk t ht4 ht6
    exact (rcs_zD4_mul hs).mp (hG (s * t) hk2 hk6 ((hom s a t hs).mpr hz))
  · intro t ht4 ht6 hz
    obtain ⟨hk2, hk6⟩ := hk t ht4 ht6
    exact (hom s a t hs).mp (hR (s * t) hk2 hk6 ((rcs_zR_mul hs).mpr hz))

theorem rcs_bounds {a b c I : ℕ} (hab : Nat.Coprime a b)
    (hi : ∃ i, 0 < i ∧ i ≤ I ∧ c * b ∣ a * i) : b ≤ I := by
  obtain ⟨i, hi0, hiI, hd⟩ := hi
  have h1 : b ∣ a * i := (dvd_mul_left b c).trans hd
  have h2 : b ∣ i := (Nat.Coprime.symm hab).dvd_of_dvd_mul_left h1
  exact (Nat.le_of_dvd hi0 h2).trans hiI

theorem rcs_close {Z : ℕ → ℕ → Prop} {c a b : ℕ} {Exc : Prop}
    (hG' : ∀ t, 4 ≤ t → t ≠ 6 → Z a t → zD4 b t)
    (hR' : ∀ t, 4 ≤ t → t ≠ 6 → zR c b t → Z a t)
    (htab : (∃ t ∈ Finset.Icc 4 12, t ≠ 6 ∧
      ((Z a t ∧ ¬ zD4 b t) ∨ (zR c b t ∧ ¬ Z a t))) ∨ Exc) : Exc := by
  rcases htab with ⟨t, ht, ht6, h | h⟩ | h
  · exact absurd (hG' t (Finset.mem_Icc.mp ht).1 ht6 h.1) h.2
  · exact absurd (hR' t (Finset.mem_Icc.mp ht).1 ht6 h.1) h.2
  · exact h

end CFSG.RankThree.PartOne.D4RC
