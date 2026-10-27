module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.ConjSylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem mem_zpowers_cases_of_pow_three {G : Type*} [Group G] {q y : G} (hq : q ^ 3 = 1)
    (h : y ∈ Subgroup.zpowers q) : y = 1 ∨ y = q ∨ y = q⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  have hq' : q ^ (3 : ℤ) = 1 := by exact_mod_cast hq
  have : q ^ k = q ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul, hq', one_zpow, mul_one]
  rw [this]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right
    rw [h]
    have : q ^ (2 : ℤ) * q = 1 := by
      rw [← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, hq']
    exact eq_inv_of_mul_eq_one_left this

theorem not_weaklyClosed_of_sylow_witness {S : Type} [Group S] [Finite S] (n : ℕ)
    (Q : Subgroup S) (hQ : Nat.card Q = 3 ^ n) (hS : ¬ 3 ^ (n + 1) ∣ Nat.card S)
    (hw : ∀ q ∈ Q, orderOf q = 3 → ∃ g : S, (g * q * g⁻¹) * q = q * (g * q * g⁻¹) ∧
      g * q * g⁻¹ ∉ Subgroup.zpowers q) {z : S} (hz : orderOf z = 3) :
    ¬ WeaklyClosed (Subgroup.zpowers z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hh⟩ := CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.exists_conj_mem_of_orderOf_prime_sylow
    3 n Q hQ hS hz
  have hqo : orderOf (h⁻¹ * z * h) = 3 := by
    rw [← hz]
    have := MulEquiv.orderOf_eq (MulAut.conj h⁻¹) z
    simpa using this
  obtain ⟨g, hc, hn⟩ := hw _ hh hqo
  refine not_weaklyClosed_of_commute_conj (g := h * g * h⁻¹) ?_ ?_
  · have e : ∀ w : S, h * g * h⁻¹ * z * (h * g * h⁻¹)⁻¹ = h * (g * (h⁻¹ * z * h) * g⁻¹) * h⁻¹ := by
      intro w; group
    rw [e z]
    calc h * (g * (h⁻¹ * z * h) * g⁻¹) * h⁻¹ * z
        = h * ((g * (h⁻¹ * z * h) * g⁻¹) * (h⁻¹ * z * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * z * h) * (g * (h⁻¹ * z * h) * g⁻¹)) * h⁻¹ := by rw [hc]
      _ = z * (h * (g * (h⁻¹ * z * h) * g⁻¹) * h⁻¹) := by group
  · intro hmem
    apply hn
    have e1 : h * g * h⁻¹ * z * (h * g * h⁻¹)⁻¹ = h * (g * (h⁻¹ * z * h) * g⁻¹) * h⁻¹ := by group
    rw [e1] at hmem
    have h2 : g * (h⁻¹ * z * h) * g⁻¹ ∈ Subgroup.zpowers (h⁻¹ * z * h) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have : (h⁻¹ * z * h) ^ k = h⁻¹ * z ^ k * h := by
        have := conj_zpow (a := h⁻¹) (b := z) (i := k)
        simpa using this
      rw [this]
      calc h⁻¹ * z ^ k * h = h⁻¹ * (h * (g * (h⁻¹ * z * h) * g⁻¹) * h⁻¹) * h := by rw [hk]
        _ = g * (h⁻¹ * z * h) * g⁻¹ := by group
    exact h2

theorem listRow_of_gen {S : Type} [Group S] [Finite S] {ι : Type} [Fintype ι] {x y : S}
    (f : ι → S) (σx σy : ι → ι) (hf : Function.Injective f)
    (hmem : ∀ i, f i ∈ Subgroup.closure ({x, y} : Set S)) (h1 : ∃ i, f i = 1)
    (hσx : ∀ i, f i * x = f (σx i)) (hσy : ∀ i, f i * y = f (σy i))
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hP3 : ∀ i, f i ^ 3 = 1) (n : ℕ)
    (hcard : Fintype.card ι = 3 ^ n) (hS : ¬ 3 ^ (n + 1) ∣ Nat.card S) (w : ι → S)
    (hw : ∀ i, f i ≠ 1 → (w i * f i * (w i)⁻¹) * f i = f i * (w i * f i * (w i)⁻¹) ∧
      w i * f i * (w i)⁻¹ ≠ f i ∧ w i * f i * (w i)⁻¹ ≠ (f i)⁻¹ ∧ w i * f i * (w i)⁻¹ ≠ 1) :
    ListRow S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup S := Subgroup.closure ({x, y} : Set S) with hPdef
  have hxi : x⁻¹ = x * x :=
    inv_eq_of_mul_eq_one_right (by calc x * (x * x) = x ^ 3 := (pow_three x).symm
      _ = 1 := hx3)
  have hyi : y⁻¹ = y * y :=
    inv_eq_of_mul_eq_one_right (by calc y * (y * y) = y ^ 3 := (pow_three y).symm
      _ = 1 := hy3)
  have hsurj : ∀ g ∈ P, ∃ i, f i = g := by
    intro g hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact h1
    | mul_right g hg s hs ih =>
      obtain ⟨i, rfl⟩ := ih
      rcases hs with rfl | hs
      · exact ⟨σx i, (hσx i).symm⟩
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ⟨σy i, (hσy i).symm⟩
    | mul_inv_cancel g hg s hs ih =>
      obtain ⟨i, rfl⟩ := ih
      rcases hs with rfl | hs
      · exact ⟨σx (σx i), by rw [hxi, ← mul_assoc, hσx, hσx]⟩
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact ⟨σy (σy i), by rw [hyi, ← mul_assoc, hσy, hσy]⟩
  have hP : Nat.card P = 3 ^ n := by
    have hbij : Function.Bijective fun i : ι => (⟨f i, hmem i⟩ : P) :=
      ⟨fun i j h => hf (congrArg Subtype.val h), fun g => by
        obtain ⟨i, hi⟩ := hsurj g g.2
        exact ⟨i, Subtype.ext hi⟩⟩
    have : Nat.card P = Nat.card ι := (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    rw [this, Nat.card_eq_fintype_card, hcard]
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  refine not_weaklyClosed_of_sylow_witness n P hP hS ?_ hz
  intro q hq hqo
  obtain ⟨i, rfl⟩ := hsurj q hq
  have hne : f i ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hqo
    omega
  obtain ⟨hc, hn1, hn2, hn3⟩ := hw i hne
  refine ⟨w i, hc, fun hmem' => ?_⟩
  rcases mem_zpowers_cases_of_pow_three (hP3 i) hmem' with h | h | h
  · exact hn3 h
  · exact hn1 h
  · exact hn2 h

theorem listRow_of_class_witness {S : Type} [Group S] [Finite S] {κ : Type} (r w : κ → S)
    (hcl : ∀ z : S, orderOf z = 3 → ∃ k : κ, ∃ h : S, z = h * r k * h⁻¹)
    (hr3 : ∀ k, r k ^ 3 = 1)
    (hw : ∀ k, r k ≠ 1 → (w k * r k * (w k)⁻¹) * r k = r k * (w k * r k * (w k)⁻¹) ∧
      w k * r k * (w k)⁻¹ ≠ r k ∧ w k * r k * (w k)⁻¹ ≠ (r k)⁻¹ ∧ w k * r k * (w k)⁻¹ ≠ 1) :
    ListRow S := by
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  obtain ⟨k, h, rfl⟩ := hcl z hz
  have hne : r k ≠ 1 := by
    intro h1
    rw [h1] at hz
    simp at hz
  obtain ⟨hc, hn1, hn2, hn3⟩ := hw k hne
  refine not_weaklyClosed_of_commute_conj (g := h * w k * h⁻¹) ?_ ?_
  · calc h * w k * h⁻¹ * (h * r k * h⁻¹) * (h * w k * h⁻¹)⁻¹ * (h * r k * h⁻¹)
        = h * ((w k * r k * (w k)⁻¹) * r k) * h⁻¹ := by group
      _ = h * (r k * (w k * r k * (w k)⁻¹)) * h⁻¹ := by rw [hc]
      _ = (h * r k * h⁻¹) * (h * w k * h⁻¹ * (h * r k * h⁻¹) * (h * w k * h⁻¹)⁻¹) := by group
  · intro hmem
    have e1 : h * w k * h⁻¹ * (h * r k * h⁻¹) * (h * w k * h⁻¹)⁻¹ =
        h * (w k * r k * (w k)⁻¹) * h⁻¹ := by group
    rw [e1] at hmem
    rcases mem_zpowers_cases_of_pow_three (q := h * r k * h⁻¹)
      (by rw [show (h * r k * h⁻¹) ^ 3 = h * r k ^ 3 * h⁻¹ by simp [conj_pow], hr3 k]; group)
      hmem with h' | h' | h'
    · apply hn3
      have := congrArg (fun t => h⁻¹ * t * h) h'
      simpa [mul_assoc] using this
    · apply hn1
      have := congrArg (fun t => h⁻¹ * t * h) h'
      simpa [mul_assoc] using this
    · apply hn2
      have := congrArg (fun t => h⁻¹ * t * h) h'
      simpa [mul_assoc] using this

theorem listRow_of_class_exists {S : Type} [Group S] [Finite S] {κ : Type} (r : κ → S)
    (hcl : ∀ z : S, orderOf z = 3 → ∃ k : κ, ∃ h : S, z = h * r k * h⁻¹)
    (hr3 : ∀ k, r k ^ 3 = 1)
    (hw : ∀ k, r k ≠ 1 → ∃ w : S, (w * r k * w⁻¹) * r k = r k * (w * r k * w⁻¹) ∧
      w * r k * w⁻¹ ≠ r k ∧ w * r k * w⁻¹ ≠ (r k)⁻¹ ∧ w * r k * w⁻¹ ≠ 1) : ListRow S := by
  classical
  refine listRow_of_class_witness r (fun k => if h : r k ≠ 1 then Classical.choose (hw k h) else 1)
    hcl hr3 fun k hk => ?_
  rw [dif_pos hk]
  exact Classical.choose_spec (hw k hk)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
