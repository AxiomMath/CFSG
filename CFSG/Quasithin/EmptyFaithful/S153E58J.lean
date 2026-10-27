module

public import CFSG.Quasithin.EmptyFaithful.S153E58I

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E58

open S153E57

variable {W : Type} [CommGroup W] [Finite W]

theorem abs_case_analysis (iTwo : Input15358Two) (iG93 : Input15358G93)
    (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)} (hHirr : IsIrrOn153 H ⊤)
    (hH2 : CFSG.Open.pCoreOf 2 H = ⊥) (hHsq : G64.IsQuotientOfSQTKCat ↥H)
    {a : MulAut W} (haH : a ∈ H) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hc4 : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2)
    {s : ℕ} (hs : 0 < s) (hcard : Nat.card W = 2 ^ (2 * (s + 2)))
    (F1 : ∀ h ∈ H, orderOf h = 3 →
      ∃ r ∈ commV (Subgroup.zpowers a), h r ∉ commV (Subgroup.zpowers a))
    (T' : Subgroup (MulAut W)) (hT' : IsSylowTwoOf T' H) (haT' : a ∈ T')
    (hcT' : ∀ x ∈ T', x * a = a * x) (hfix2 : Nat.card ↥(fixV T') = 2)
    (F2 : ∀ h ∈ H, orderOf h = 3 → ∃ z ∈ fixV T', h z ≠ z)
    (A : Subgroup (MulAut W)) (hAH : A ≤ H) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAsq : ∀ x ∈ A, x ^ 2 = 1) (hAcard : Nat.card ↥A = 2 ^ (s + 1)) (haA : a ∈ A)
    (D : Subgroup (MulAut W)) (hDH : D ≤ H) (hDa : ∀ d ∈ D, d * a = a * d) (haD : a ∈ ⁅D, D⁆)
    (h57 : Hyp57Two H a s) :
    ∃ (K : Subgroup (MulAut W)) (W₁ W₂ : Subgroup W) (π : ↥(StatedSL 3 (ZMod 2)) →* ↥K),
      IsMinNormalIn H K ∧ ⁅K, K⁆ = K ∧ ¬ (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) ∧
      IsIntDirect W₁ W₂ ⊤ ∧ IsIrrOn153 K W₁ ∧ IsIrrOn153 K W₂ ∧ Nat.card ↥W₁ = 2 ^ (s + 2) ∧
      Nat.card ↥W₂ = 2 ^ (s + 2) ∧ (∀ w ∈ W₁, a w ∈ W₁) ∧ (∀ w ∈ W₂, a w ∈ W₂) ∧
      Nat.card ↥(commIn153 (Subgroup.zpowers a) W₁) = 2 ∧
      Nat.card ↥(commIn153 (Subgroup.zpowers a) W₂) = 2 ∧
      (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π := by
  have : Finite (MulAut W) := finite_mulAut_of_finite W
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have F3 : ∀ h ∈ H, orderOf h = 3 → h * a ≠ a * h := by
    intro h hh h3 hch
    obtain ⟨r, hr, hnot⟩ := F1 h hh h3
    exact hnot (commV_stable_of_commute hch r hr)
  have hH1 : H ≠ ⊥ := by
    intro h
    apply ha1
    have : a ∈ (⊥ : Subgroup (MulAut W)) := h ▸ haH
    simpa using this
  obtain ⟨K, hKmin⟩ := exists_isMinNormalIn H hH1
  have hKH : K ≤ H := hKmin.1
  have hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := hKmin.2.1
  have hK1 : K ≠ ⊥ := hKmin.2.2.1
  rcases IsMinNormalIn.commutator_eq hKmin with hbot | hperf
  ·
    exfalso
    have hab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
      intro x hx y hy
      have h1 : ⁅x, y⁆ ∈ ⁅K, K⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [hbot, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    exact abelian_minNormal_false hW hKmin hab hHirr hH2 haH ha1 ha2 hc4 hs hcard F3 hDH hDa haD h57
  ·
    have hnonab : ¬ (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) := by
      intro hab
      apply hK1
      have : ⁅K, K⁆ ≤ ⊥ := Subgroup.commutator_le.2 fun x hx y hy =>
        Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hab x hx y hy))
      rw [hperf] at this
      exact le_bot_iff.1 this
    have hfix := fix_eq_one_of_normal hHirr hKn hK1
    have hoT : oTwoUpper K = K := oTwoUpper_eq_of_perfect hperf
    have hK5 : ∀ W₀ : Subgroup W, IsIrrOn153 K W₀ → 8 ≤ Nat.card W₀ := fun W₀ h =>
      eight_le_card_of_irr hW' (fun α _ hα f => eq_one_of_perfect_perm hperf α hα f) hfix h
    obtain ⟨hcomm, hdich⟩ := h57 K hKH hK1 hoT hKn hK5
    have h64 : 2 ^ 6 ≤ Nat.card W := by
      rw [hcard]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases hdich with hirr | ⟨W₁, W₂, hirr₁, hirr₂, hsup, hinf, hc₁, hc₂, hinv₁, hinv₂, hcm₁, hcm₂⟩
    ·
      exfalso
      have hcomm' : ∃ x ∈ A, ∃ k ∈ K, x * k ≠ k * x := by
        by_contra hcon
        push Not at hcon
        apply hcomm
        have : ∀ k ∈ K, k * a = a * k := fun k hk => (hcon a haA k hk).symm
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        rw [Subgroup.commutator_def] at hx
        induction hx using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨k, hk, b, hb, rfl⟩ := hx
          have hkb : k * b = b * k := by
            obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
            exact (Commute.zpow_right (show Commute k a from this k hk) m).eq
          exact commutatorElement_eq_one_iff_mul_comm.2 hkb
        | one => rfl
        | mul x y _ _ ihx ihy => rw [ihx, ihy, one_mul]
        | inv x _ ih => rw [ih, inv_one]
      exact iG93 W hW H K A a (s + 1) hHsq hH2 hHirr hKmin hnonab hirr hAH hAab hAsq hAcard
        (by rw [hcard]) hcomm' haA ha1 ha2 hc4
        h64 ⟨T', hT', haT', hcT', hfix2, F2⟩
    ·
      have h8₁ : 8 ≤ Nat.card ↥W₁ := by
        rw [hc₁]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (s + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h8₂ : 8 ≤ Nat.card ↥W₂ := by
        rw [hc₂]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (s + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmem : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
      obtain ⟨π, hπ⟩ := iTwo W hW H K a W₁ W₂ hHsq hH2 hHirr hKmin hnonab haH ha1 ha2
        ⟨T', hT', haT', hcT'⟩ ⟨hsup, hinf⟩ hirr₁ hirr₂ (hc₁.trans hc₂.symm) h8₁ h8₂ (hinv₁ a hmem)
        (hinv₂ a hmem) hcm₁ hcm₂ F1
      exact ⟨K, W₁, W₂, π, hKmin, hperf, hnonab, ⟨hsup, hinf⟩, hirr₁, hirr₂, hc₁, hc₂, hinv₁ a hmem,
        hinv₂ a hmem, hcm₁, hcm₂, hπ⟩

end S153E58

end CFSG.Quasithin
