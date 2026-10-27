module

public import CFSG.Walter.ReeOrder.WardLocal.Hall3

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.DirectProduct
open CFSG.BlockSectionOrthogonality.Helpers

theorem six_of_count {m g t e iR iS i₁ i₂ a b : ℚ} (hm : 3 ≤ m)
    (hg : g = (3 * m ^ 2) ^ 3 * ((3 * m ^ 2) ^ 3 + 1) * (3 * m ^ 2 - 1))
    (hcov : g ≤ 1 + t + e + iR + iS + i₁ + i₂) (ht : t ≤ (3 * m ^ 2) ^ 6 - 1)
    (he : 8 * e ≤ 3 * g)
    (hiR : iR * (4 * (3 * m ^ 2 - 1)) ≤ g * (3 * m ^ 2 - 3))
    (hiS : iS * (24 * (3 * m ^ 2 + 1)) ≤ g * (3 * m ^ 2 - 3))
    (hi₁ : i₁ * ((3 * m ^ 2 + 1 - 3 * m) * a) ≤ g * (3 * m ^ 2 - 3 * m))
    (hi₂ : i₂ * ((3 * m ^ 2 + 1 + 3 * m) * b) ≤ g * (3 * m ^ 2 + 3 * m))
    (ha : 6 ≤ a) (hb : 6 ≤ b) : a = 6 ∧ b = 6 := by
  have hm2 : 27 ≤ 3 * m ^ 2 := by nlinarith
  have hq1 : 0 < 3 * m ^ 2 - 1 := by linarith
  have hqp : 0 < 3 * m ^ 2 + 1 := by linarith
  have hnm : 0 < 3 * m ^ 2 + 1 - 3 * m := by nlinarith
  have hnp : 0 < 3 * m ^ 2 + 1 + 3 * m := by nlinarith
  have hg0 : 0 < g := by rw [hg]; positivity
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have bR : iR ≤ g * (3 * m ^ 2 - 3) / (4 * (3 * m ^ 2 - 1)) := by
    rw [le_div_iff₀ (by positivity)]; exact hiR
  have bS : iS ≤ g * (3 * m ^ 2 - 3) / (24 * (3 * m ^ 2 + 1)) := by
    rw [le_div_iff₀ (by positivity)]; exact hiS
  have b₁ : i₁ ≤ g * (3 * m ^ 2 - 3 * m) / (3 * m ^ 2 + 1 - 3 * m) / a := by
    rw [le_div_iff₀ ha0, le_div_iff₀ hnm]
    calc i₁ * a * (3 * m ^ 2 + 1 - 3 * m) = i₁ * ((3 * m ^ 2 + 1 - 3 * m) * a) := by ring
      _ ≤ _ := hi₁
  have b₂ : i₂ ≤ g * (3 * m ^ 2 + 3 * m) / (3 * m ^ 2 + 1 + 3 * m) / b := by
    rw [le_div_iff₀ hb0, le_div_iff₀ hnp]
    calc i₂ * b * (3 * m ^ 2 + 1 + 3 * m) = i₂ * ((3 * m ^ 2 + 1 + 3 * m) * b) := by ring
      _ ≤ _ := hi₂
  set α := g * (3 * m ^ 2 - 3 * m) / (3 * m ^ 2 + 1 - 3 * m) with hα
  set β := g * (3 * m ^ 2 + 3 * m) / (3 * m ^ 2 + 1 + 3 * m) with hβ
  have hα0 : 0 < α := by
    rw [hα]; apply div_pos (mul_pos hg0 (by nlinarith)) hnm
  have hβ0 : 0 < β := by
    rw [hβ]; apply div_pos (mul_pos hg0 (by nlinarith)) hnp
  have hid : (3 * m ^ 2) ^ 6 + 3 * g / 8 + g * (3 * m ^ 2 - 3) / (4 * (3 * m ^ 2 - 1)) +
      g * (3 * m ^ 2 - 3) / (24 * (3 * m ^ 2 + 1)) + α / 6 + β / 6 = g := by
    rw [hα, hβ, hg]
    field_simp
    ring
  have hsum : α / 6 + β / 6 ≤ α / a + β / b := by linarith
  have hαa : α / a ≤ α / 6 := div_le_div_of_nonneg_left hα0.le (by norm_num) ha
  have hβb : β / b ≤ β / 6 := div_le_div_of_nonneg_left hβ0.le (by norm_num) hb
  have e1 : α / a = α / 6 := by linarith
  have e2 : β / b = β / 6 := by linarith
  rw [div_eq_div_iff ha0.ne' (by norm_num)] at e1
  rw [div_eq_div_iff hb0.ne' (by norm_num)] at e2
  exact ⟨(mul_left_cancel₀ hα0.ne' e1).symm, (mul_left_cancel₀ hβ0.ne' e2).symm⟩

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

include B hq hK hG hP1P hPc hPn hN1c in
theorem relIndex_eq_six (hm : q = 3 * m ^ 2) {M₁ M₂ : Subgroup G}
    (hc₁ : Nat.card M₁ = q + 1 - 3 * m) (hcomm₁ : ∀ x ∈ M₁, ∀ y ∈ M₁, x * y = y * x)
    (hcen₁ : ∀ x ∈ M₁, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M₁)
    (hc₂ : Nat.card M₂ = q + 1 + 3 * m) (hcomm₂ : ∀ x ∈ M₂, ∀ y ∈ M₂, x * y = y * x)
    (hcen₂ : ∀ x ∈ M₂, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M₂) :
    M₁.relIndex (Subgroup.normalizer (M₁ : Set G)) = 6 ∧
      M₂.relIndex (Subgroup.normalizer (M₂ : Set G)) = 6 := by
  have hq27 : 27 ≤ q := S.q_ge
  have hm1 : 1 ≤ m := by rw [m_eq hq hm]; exact Nat.one_le_pow _ _ (by norm_num)
  have hm3 : 3 ≤ m := by nlinarith
  have hlt : 3 * m < q + 1 := by rw [hm]; nlinarith
  have hle3 : 3 * m + 3 ≤ q + 1 := by rw [hm]; nlinarith
  set f : G × G → G := fun p => p.1 * p.2 * p.1⁻¹ with hf
  set IR := (Finset.univ ×ˢ ((Finset.univ.filter (· ∈ S.W.Ro.map S.κ)).erase 1)).image f
    with hIR
  set IS := (Finset.univ ×ˢ ((Finset.univ.filter (· ∈ S.W.So.map S.κ)).erase 1)).image f
    with hIS
  set I₁ := (Finset.univ ×ˢ ((Finset.univ.filter (· ∈ M₁)).erase 1)).image f with hI₁
  set I₂ := (Finset.univ ×ˢ ((Finset.univ.filter (· ∈ M₂)).erase 1)).image f with hI₂
  set T := Finset.univ.filter fun x : G => x ≠ 1 ∧ ∃ i : ℕ, orderOf x = 3 ^ i with hT
  set E := Finset.univ.filter fun x : G => Even (orderOf x) with hE
  obtain ⟨hSo4, hSoodd, -, -⟩ := So_arith hq (S := S)
  have hRo := S.W.Ro_card
  have hRo' : 2 * Nat.card S.W.Ro = q - 1 := by omega
  have hcls : ∀ x : G, x = 1 ∨ x ∈ T ∨ x ∈ E ∨ x ∈ IR ∨ x ∈ IS ∨ x ∈ I₁ ∨ x ∈ I₂ := by
    intro x
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    by_cases h₁ : ∃ p, p.Prime ∧ p ∣ q + 1 - 3 * m ∧ p ∣ orderOf x
    · obtain ⟨p, hp, hpn, hpx⟩ := h₁
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (mem_image_hall hq hG hm (Or.inl rfl) hc₁ hcen₁ hp hpn hpx))))))
    by_cases h₂ : ∃ p, p.Prime ∧ p ∣ q + 1 + 3 * m ∧ p ∣ orderOf x
    · obtain ⟨p, hp, hpn, hpx⟩ := h₂
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (mem_image_hall hq hG hm (Or.inr rfl) hc₂ hcen₂ hp hpn hpx))))))
    push Not at h₁ h₂
    by_cases he : Even (orderOf x)
    · exact Or.inr (Or.inr (Or.inl (by simp [hE, he])))
    rw [Nat.not_even_iff_odd] at he
    by_cases h3 : 3 ∣ orderOf x
    · refine Or.inr (Or.inl ?_)
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx1, B.three_elem_of_odd hq hG he h3⟩
    have ho1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr, hrx⟩ := Nat.exists_prime_and_dvd ho1
    have hr2 : r ≠ 2 := by
      rintro rfl; exact (Nat.not_even_iff_odd.mpr he) (even_iff_two_dvd.mpr hrx)
    have hr3 : r ≠ 3 := by rintro rfl; exact h3 hrx
    have hrG : r ∣ Nat.card G := hrx.trans (orderOf_dvd_natCard x)
    rw [card_G_hall hq hG hm] at hrG
    have hrq : ¬ r ∣ q := fun h => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (hr.dvd_of_dvd_pow (hq ▸ h)))
    rcases (Nat.Prime.dvd_mul hr).mp hrG with h | h
    · exact absurd hrx (h₁ r hr h)
    rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
        · exact absurd (hr.dvd_of_dvd_pow h) hrq
        · have hrR : r ∣ Nat.card S.W.Ro := by
            rw [← hRo'] at h
            exact Nat.Coprime.dvd_of_dvd_mul_left
              ((Nat.coprime_primes hr Nat.prime_two).mpr hr2) h
          exact Or.inr (Or.inr (Or.inr (Or.inl (mem_image_Ro hG he hr hrR hrx))))
      · have hrS : r ∣ Nat.card S.W.So := by
          rw [← hSo4] at h
          exact Nat.Coprime.dvd_of_dvd_mul_left
            (Nat.Coprime.pow_right 2 ((Nat.coprime_primes hr Nat.prime_two).mpr hr2))
            (by rw [show 4 = 2 ^ 2 by norm_num] at h; exact h)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (B.mem_image_So hq hK hG hP1P hPc hPn hN1c hm he hr hrS hrx)))))
    · exact absurd hrx (h₂ r hr h)
  have hcover : (Finset.univ : Finset G) ⊆ {1} ∪ T ∪ E ∪ IR ∪ IS ∪ I₁ ∪ I₂ := by
    intro x _
    rcases hcls x with h | h | h | h | h | h | h <;> simp [h]
  have hcount := Finset.card_le_card hcover
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hcount
  have hu : ({1} ∪ T ∪ E ∪ IR ∪ IS ∪ I₁ ∪ I₂ : Finset G).card ≤
      1 + T.card + E.card + IR.card + IS.card + I₁.card + I₂.card := by
    have h1 := Finset.card_union_le ({1} ∪ T ∪ E ∪ IR ∪ IS ∪ I₁) I₂
    have h2 := Finset.card_union_le ({1} ∪ T ∪ E ∪ IR ∪ IS) I₁
    have h3 := Finset.card_union_le ({1} ∪ T ∪ E ∪ IR) IS
    have h4 := Finset.card_union_le ({1} ∪ T ∪ E) IR
    have h5 := Finset.card_union_le ({1} ∪ T) E
    have h6 := Finset.card_union_le {1} T
    rw [Finset.card_singleton] at h6
    omega
  have hTb := B.card_three_le hq hK hG hP1P hPc hPn hN1c
  have hEb := card_even_le (S := S) hq
  have hIRb := card_conj_image_mul_le (S.W.Ro.map S.κ)
  have hISb := card_conj_image_mul_le (S.W.So.map S.κ)
  have hI₁b := card_conj_image_mul_le M₁
  have hI₂b := card_conj_image_mul_le M₂
  rw [Subgroup.card_map_of_injective S.κ_inj] at hIRb hISb
  have hNR := two_mul_le_card_normalizer_Ro (S := S) hq
  have hNS := six_mul_le_card_normalizer_So (S := S)
  have hN₁ := card_mul_relIndex (Subgroup.le_normalizer : M₁ ≤ Subgroup.normalizer (M₁ : Set G))
  have hN₂ := card_mul_relIndex (Subgroup.le_normalizer : M₂ ≤ Subgroup.normalizer (M₂ : Set G))
  have ha6 := six_le_relIndex hq hG hm (Or.inl rfl) hc₁ hcomm₁ hcen₁ (by omega)
  have hb6 := six_le_relIndex hq hG hm (Or.inr rfl) hc₂ hcomm₂ hcen₂ (by omega)
  set a := M₁.relIndex (Subgroup.normalizer (M₁ : Set G)) with ha
  set b := M₂.relIndex (Subgroup.normalizer (M₂ : Set G)) with hb
  rw [← hN₁, hc₁] at hI₁b
  rw [← hN₂, hc₂] at hI₂b
  have bR : IR.card * (4 * (q - 1)) ≤ Nat.card G * (q - 3) := by
    have h1 : IR.card * (2 * (q - 1)) ≤ Nat.card G * (Nat.card S.W.Ro - 1) :=
      (Nat.mul_le_mul_left _ hNR).trans hIRb
    have h2 : 2 * (Nat.card S.W.Ro - 1) = q - 3 := by omega
    calc IR.card * (4 * (q - 1)) = 2 * (IR.card * (2 * (q - 1))) := by ring
      _ ≤ 2 * (Nat.card G * (Nat.card S.W.Ro - 1)) := Nat.mul_le_mul_left _ h1
      _ = Nat.card G * (q - 3) := by rw [← h2]; ring
  have bS : IS.card * (24 * (q + 1)) ≤ Nat.card G * (q - 3) := by
    have h1 : IS.card * (6 * (q + 1)) ≤ Nat.card G * (Nat.card S.W.So - 1) :=
      (Nat.mul_le_mul_left _ hNS).trans hISb
    have h2 : 4 * (Nat.card S.W.So - 1) = q - 3 := by omega
    calc IS.card * (24 * (q + 1)) = 4 * (IS.card * (6 * (q + 1))) := by ring
      _ ≤ 4 * (Nat.card G * (Nat.card S.W.So - 1)) := Nat.mul_le_mul_left _ h1
      _ = Nat.card G * (q - 3) := by rw [← h2]; ring
  have hqQ : (q : ℚ) = 3 * (m : ℚ) ^ 2 := by rw [hm]; push_cast; ring
  have hq1 : 1 ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have key := six_of_count (m := (m : ℚ)) (g := (Nat.card G : ℚ)) (t := (T.card : ℚ))
    (e := (E.card : ℚ)) (iR := (IR.card : ℚ)) (iS := (IS.card : ℚ)) (i₁ := (I₁.card : ℚ))
    (i₂ := (I₂.card : ℚ)) (a := (a : ℚ)) (b := (b : ℚ)) (by exact_mod_cast hm3)
    (by rw [hG, ← hqQ]; push_cast [hq1]; ring)
    (by exact_mod_cast hcount.trans hu)
    (by
      have : ((T.card : ℕ) : ℚ) ≤ (((q ^ 3 + 1) * (q ^ 3 - 1) : ℕ) : ℚ) := by exact_mod_cast hTb
      rw [← hqQ]; push_cast [Nat.one_le_pow 3 q (by omega)] at this; linarith)
    (by exact_mod_cast hEb)
    (by
      have : ((IR.card * (4 * (q - 1)) : ℕ) : ℚ) ≤ ((Nat.card G * (q - 3) : ℕ) : ℚ) := by
        exact_mod_cast bR
      rw [← hqQ]; push_cast [hq1, hq3] at this; linarith)
    (by
      have : ((IS.card * (24 * (q + 1)) : ℕ) : ℚ) ≤ ((Nat.card G * (q - 3) : ℕ) : ℚ) := by
        exact_mod_cast bS
      rw [← hqQ]; push_cast [hq3] at this; linarith)
    (by
      have : ((I₁.card * ((q + 1 - 3 * m) * a) : ℕ) : ℚ) ≤
          ((Nat.card G * (q + 1 - 3 * m - 1) : ℕ) : ℚ) := by exact_mod_cast hI₁b
      rw [← hqQ]; push_cast [hlt.le, show 1 ≤ q + 1 - 3 * m by omega] at this
      have e1 : (q : ℚ) + 1 - 3 * m - 1 = (q : ℚ) - 3 * m := by ring
      rw [e1] at this; linarith)
    (by
      have : ((I₂.card * ((q + 1 + 3 * m) * b) : ℕ) : ℚ) ≤
          ((Nat.card G * (q + 1 + 3 * m - 1) : ℕ) : ℚ) := by exact_mod_cast hI₂b
      rw [← hqQ]; push_cast [show 1 ≤ q + 1 + 3 * m by omega] at this
      have e1 : (q : ℚ) + 1 + 3 * m - 1 = (q : ℚ) + 3 * m := by ring
      rw [e1] at this; linarith)
    (by exact_mod_cast ha6) (by exact_mod_cast hb6)
  exact ⟨by exact_mod_cast key.1, by exact_mod_cast key.2⟩

omit [CharP K 3] in
include S hq in
theorem exists_complement (hm : q = 3 * m ^ 2) {M : Subgroup G} {n : ℕ}
    (hn : n = q + 1 - 3 * m ∨ n = q + 1 + 3 * m) (hMc : Nat.card M = n)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hcen : ∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M)
    (h6 : M.relIndex (Subgroup.normalizer (M : Set G)) = 6) :
    ∃ W : Subgroup G, IsCyclic W ∧ Nat.card W = 6 ∧ M ⊓ W = ⊥ ∧
      Subgroup.normalizer (M : Set G) = M ⊔ W ∧
      ∀ w ∈ W, w ≠ 1 → M ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ := by
  set N := Subgroup.normalizer (M : Set G) with hN
  have hNc : Nat.card N = n * 6 := by
    rw [← hMc, ← h6]; exact (card_mul_relIndex Subgroup.le_normalizer).symm
  obtain ⟨c1, -, -, c4, -, -⟩ := hall_coprime hm (m_odd hq hm)
  have hnN : n ∣ (q + 1 - 3 * m) * (q + 1 + 3 * m) := by
    rcases hn with rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hn2 : Nat.Coprime n 2 := Nat.Coprime.coprime_dvd_left hnN c4
  have hn3 : Nat.Coprime n 3 := Nat.Coprime.coprime_dvd_right (hq ▸ dvd_pow_self 3 (by omega))
    (Nat.Coprime.coprime_dvd_left hnN c1)
  have hn6 : Nat.Coprime n 6 := by
    rw [show 6 = 2 * 3 by norm_num]; exact Nat.Coprime.mul_right hn2 hn3
  have hq27 : 27 ≤ q := S.q_ge
  have hn1 : 1 < n := by
    have hm1 : 1 ≤ m := by rw [m_eq hq hm]; exact Nat.one_le_pow _ _ (by norm_num)
    have : 3 * m + 3 ≤ q + 1 := by rw [hm]; nlinarith
    rcases hn with rfl | rfl <;> omega
  obtain ⟨x₀, hx₀M, hx₀1⟩ : ∃ x₀ ∈ M, x₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : M = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hMc
    omega
  have hCM : ∀ z : G, (∀ x ∈ M, z * x = x * z) → z ∈ M := fun z hz => by
    rw [← hcen x₀ hx₀M hx₀1, Subgroup.mem_centralizer_singleton_iff]; exact hz x₀ hx₀M
  have hconjM : ∀ s ∈ N, ∀ x ∈ M, s * x * s⁻¹ ∈ M := fun s hs x hx =>
    (Subgroup.mem_normalizer_iff.mp hs x).mp hx
  have hinv : ∀ s ∈ N, s * s = 1 → s ∉ M → ∀ x ∈ M, s * x * s⁻¹ = x⁻¹ := by
    intro s hs hss hsM x hx
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hx' : x * (s * x * s⁻¹) ∈ M := M.mul_mem hx (hconjM s hs x hx)
    have hfix : s * (x * (s * x * s⁻¹)) * s⁻¹ = x * (s * x * s⁻¹) := by
      have e : s * (x * (s * x * s⁻¹)) * s⁻¹ = (s * x * s⁻¹) * x := by
        rw [hsinv]
        calc s * (x * (s * x * s)) * s = s * x * s * x * (s * s) := by group
          _ = s * x * s * x := by rw [hss, mul_one]
      rw [e, hcomm _ (hconjM s hs x hx) x hx]
    by_contra hne
    have h1 : x * (s * x * s⁻¹) ≠ 1 := fun h => hne (by
      calc s * x * s⁻¹ = x⁻¹ * (x * (s * x * s⁻¹)) := by group
        _ = x⁻¹ := by rw [h, mul_one])
    apply hsM
    rw [← hcen _ hx' h1, Subgroup.mem_centralizer_singleton_iff]
    calc s * (x * (s * x * s⁻¹)) = s * (x * (s * x * s⁻¹)) * s⁻¹ * s := by group
      _ = x * (s * x * s⁻¹) * s := by rw [hfix]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := N) 2
    (by rw [hNc]; exact ⟨n * 3, by ring⟩)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := N) 3
    (by rw [hNc]; exact ⟨n * 2, by ring⟩)
  rw [← Subgroup.orderOf_coe] at ht₀ hu
  set t₁ : G := (t₀ : G) with ht₁
  set u₁ : G := (u : G) with hu₁
  have ht₁N : t₁ ∈ N := t₀.2
  have hu₁N : u₁ ∈ N := u.2
  have ht₁sq : t₁ * t₁ = 1 := by rw [← sq, ← ht₀, pow_orderOf_eq_one]
  have ht₁inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁sq
  have hnotM : ∀ z ∈ M, ∀ p : ℕ, p.Prime → orderOf z = p → Nat.Coprime n p → False := by
    intro z hz p hp hzp hnp
    have h := Subgroup.orderOf_dvd_natCard _ hz
    rw [hzp, hMc] at h
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hnp.symm h)
  have ht₁M : t₁ ∉ M := fun h => hnotM _ h 2 Nat.prime_two ht₀ hn2
  have hu₁M : u₁ ∉ M := fun h => hnotM _ h 3 Nat.prime_three hu hn3
  have hufpf : ∀ z ∈ M, u₁ * z * u₁⁻¹ = z → z = 1 := by
    intro z hz hzu
    by_contra hz1
    apply hu₁M
    rw [← hcen z hz hz1, Subgroup.mem_centralizer_singleton_iff]
    calc u₁ * z = u₁ * z * u₁⁻¹ * u₁ := by group
      _ = z * u₁ := by rw [hzu]
  set s₁ := u₁ * t₁ * u₁⁻¹ with hs₁
  have hs₁N : s₁ ∈ N := N.mul_mem (N.mul_mem hu₁N ht₁N) (N.inv_mem hu₁N)
  have hs₁sq : s₁ * s₁ = 1 := by
    rw [hs₁]; calc u₁ * t₁ * u₁⁻¹ * (u₁ * t₁ * u₁⁻¹) = u₁ * (t₁ * t₁) * u₁⁻¹ := by group
      _ = 1 := by rw [ht₁sq]; group
  have hs₁M : s₁ ∉ M := by
    intro h
    apply ht₁M
    have := hconjM _ (N.inv_mem hu₁N) _ h
    rwa [hs₁, show u₁⁻¹ * (u₁ * t₁ * u₁⁻¹) * u₁⁻¹⁻¹ = t₁ by group] at this
  have hx₁ : t₁⁻¹ * s₁ ∈ M := by
    apply hCM
    intro x hx
    have h1 := hinv t₁ ht₁N ht₁sq ht₁M x hx
    have h2 := hinv s₁ hs₁N hs₁sq hs₁M x hx
    have hs₁inv : s₁⁻¹ = s₁ := inv_eq_of_mul_eq_one_right hs₁sq
    have h3 : t₁⁻¹ * x⁻¹ = x * t₁⁻¹ := by rw [← h1]; group
    calc t₁⁻¹ * s₁ * x = t₁⁻¹ * (s₁ * x * s₁⁻¹) * s₁ := by group
      _ = t₁⁻¹ * x⁻¹ * s₁ := by rw [h2]
      _ = x * t₁⁻¹ * s₁ := by rw [h3]
      _ = x * (t₁⁻¹ * s₁) := by group
  let F : M → M := fun y => ⟨y * (u₁ * y * u₁⁻¹)⁻¹,
    M.mul_mem y.2 (M.inv_mem (hconjM _ hu₁N _ y.2))⟩
  have hFinj : Function.Injective F := by
    intro y y' h
    have h' : (y : G) * (u₁ * y * u₁⁻¹)⁻¹ = y' * (u₁ * y' * u₁⁻¹)⁻¹ := congrArg Subtype.val h
    have hz : (y' : G)⁻¹ * y ∈ M := M.mul_mem (M.inv_mem y'.2) y.2
    have hfix : u₁ * ((y' : G)⁻¹ * y) * u₁⁻¹ = (y' : G)⁻¹ * y := by
      have e1 : (y' : G)⁻¹ * y = (u₁ * y' * u₁⁻¹)⁻¹ * (u₁ * y * u₁⁻¹) := by
        have hc := hcomm _ (M.inv_mem (hconjM _ hu₁N _ y'.2)) _ y.2
        calc (y' : G)⁻¹ * y = (y' : G)⁻¹ * (y * (u₁ * y * u₁⁻¹)⁻¹) * (u₁ * y * u₁⁻¹) := by group
          _ = (y' : G)⁻¹ * (y' * (u₁ * y' * u₁⁻¹)⁻¹) * (u₁ * y * u₁⁻¹) := by rw [h']
          _ = (u₁ * y' * u₁⁻¹)⁻¹ * (u₁ * y * u₁⁻¹) := by group
      calc u₁ * ((y' : G)⁻¹ * y) * u₁⁻¹ = (u₁ * y' * u₁⁻¹)⁻¹ * (u₁ * y * u₁⁻¹) := by group
        _ = (y' : G)⁻¹ * y := e1.symm
    have := hufpf _ hz hfix
    exact Subtype.ext (inv_mul_eq_one.mp this).symm
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hFinj) ⟨t₁⁻¹ * s₁, hx₁⟩
  have hy' : (y : G) * (u₁ * y * u₁⁻¹)⁻¹ = t₁⁻¹ * s₁ := congrArg Subtype.val hy
  set t := t₁ * y with ht
  have htu : u₁ * t * u₁⁻¹ = t := by
    calc u₁ * t * u₁⁻¹ = s₁ * (u₁ * y * u₁⁻¹) := by rw [ht, hs₁]; group
      _ = t₁ * (t₁⁻¹ * s₁) * (u₁ * y * u₁⁻¹) := by group
      _ = t₁ * ((y : G) * (u₁ * y * u₁⁻¹)⁻¹) * (u₁ * y * u₁⁻¹) := by rw [hy']
      _ = t := by rw [ht]; group
  have htsq : t * t = 1 := by
    have h1 := hinv t₁ ht₁N ht₁sq ht₁M y y.2
    calc t * t = (t₁ * y * t₁⁻¹) * y := by rw [ht, ht₁inv]; group
      _ = 1 := by rw [h1, inv_mul_cancel]
  have ht1 : t ≠ 1 := by
    intro h
    apply ht₁M
    have : t₁ = (y : G)⁻¹ := by rw [ht] at h; exact eq_inv_of_mul_eq_one_left h
    rw [this]; exact M.inv_mem y.2
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [sq, htsq]) ht1
  have hcomm_tu : Commute t u₁ := by
    show t * u₁ = u₁ * t
    calc t * u₁ = u₁ * t * u₁⁻¹ * u₁ := by rw [htu]
      _ = u₁ * t := by group
  have hw : orderOf (t * u₁) = 6 := by
    rw [hcomm_tu.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hto, hu]; norm_num), hto, hu]
  have htN : t ∈ N := N.mul_mem ht₁N (Subgroup.le_normalizer y.2)
  have hwN : t * u₁ ∈ N := N.mul_mem htN hu₁N
  set W := Subgroup.zpowers (t * u₁) with hW
  have hWc : Nat.card W = 6 := by rw [hW, Nat.card_zpowers, hw]
  have hWN : W ≤ N := by rw [hW, Subgroup.zpowers_le]; exact hwN
  have hcop : Nat.Coprime (Nat.card M) (Nat.card W) := by rw [hMc, hWc]; exact hn6
  have hMW : M ⊓ W = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  refine ⟨W, inferInstance, hWc, hMW, (sup_eq_normalizer hWN hcop (by rw [hNc, hMc, hWc])).symm,
    fun w hw hw1 => ?_⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxM, hxw⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  apply hw1
  have hwM : w ∈ M := by
    rw [← hcen x hxM hx1, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hxw).symm
  have : w ∈ M ⊓ W := Subgroup.mem_inf.mpr ⟨hwM, hw⟩
  rw [hMW, Subgroup.mem_bot] at this
  exact this

end Block

end CFSG.Walter.WardLocal
