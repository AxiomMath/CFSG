module

public import CFSG.RankThree.PartOne.AUTSL.WeightCount

public section

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical

section Sp

variable {B X ι : Type*} [CommGroup B] [CommGroup X] [Fintype ι]

theorem card_six {α : Type*} [DecidableEq α] {a b c d e g : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (hag : a ≠ g) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hbg : b ≠ g) (hcd : c ≠ d) (hce : c ≠ e) (hcg : c ≠ g) (hde : d ≠ e) (hdg : d ≠ g)
    (heg : e ≠ g) : ({a, b, c, d, e, g} : Finset α).card = 6 := by
  simp [Finset.card_insert_of_notMem, hab, hac, had, hae, hag, hbc, hbd, hbe, hbg, hcd, hce, hcg,
    hde, hdg, heg]

theorem inv_eq_pow_four {x : B →* X} (hx : x ^ 5 = 1) : x⁻¹ = x ^ 4 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx)

theorem sum_mult_eq (f : ι → (B →* X)) (s : Finset (B →* X)) :
    (Finset.univ.filter fun i => f i ∈ s).card = ∑ χ ∈ s, mult f χ := by
  unfold mult
  have h := Finset.card_eq_sum_card_fiberwise (f := f)
    (s := Finset.univ.filter fun i => f i ∈ s) (t := s)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  rw [h]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hh
    exact hh.2
  · intro hh
    exact ⟨hh ▸ hχ, hh⟩

theorem sum_six_le (f : ι → (B →* X)) {a b c d e g : B →* X} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (hag : a ≠ g) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hbg : b ≠ g) (hcd : c ≠ d) (hce : c ≠ e) (hcg : c ≠ g) (hde : d ≠ e) (hdg : d ≠ g)
    (heg : e ≠ g) : mult f a + mult f b + mult f c + mult f d + mult f e + mult f g ≤
      Fintype.card ι := by
  have h := sum_mult_le f {a, b, c, d, e, g}
  rwa [Finset.sum_insert (by simp [hab, hac, had, hae, hag]),
    Finset.sum_insert (by simp [hbc, hbd, hbe, hbg]), Finset.sum_insert (by simp [hcd, hce, hcg]),
    Finset.sum_insert (by simp [hde, hdg]), Finset.sum_pair heg, ← add_assoc, ← add_assoc,
    ← add_assoc, ← add_assoc] at h

theorem sp_weight_lemma (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B)
    (hθ : ∀ b, b * θ b * θ (θ b) = 1) (f : ι → (B →* X)) (hcard : Fintype.card ι = 6) (m : ℕ)
    (hm : ¬ 5 ∣ m) (hf1 : ∃ i, f i ≠ 1) (H1 : ∀ χ, mult f χ ≤ mult f (twist θ m χ))
    (H2 : ∀ χ, mult f χ ≤ mult f χ⁻¹) :
    Function.Injective f ∧ ∃ χ₀ : B →* X, χ₀ ≠ 1 ∧ χ₀ ∈ Set.range f ∧
      ∀ ψ ∈ Set.range f, ψ = χ₀ ∨ ψ = twist θ m χ₀ ∨ ψ = twist θ m (twist θ m χ₀) ∨
        ψ = χ₀⁻¹ ∨ ψ = (twist θ m χ₀)⁻¹ ∨ ψ = (twist θ m (twist θ m χ₀))⁻¹ := by
  obtain ⟨i₀, hi₀⟩ := hf1
  set a : B →* X := f i₀ with ha_def
  set b : B →* X := twist θ m a with hb_def
  set c : B →* X := twist θ m b with hc_def
  have hrange : ∀ χ, χ ∈ Set.range f → twist θ m χ ∈ Set.range f := fun χ hχ =>
    (mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ).2 hχ) (H1 χ))
  have hrangeinv : ∀ χ, χ ∈ Set.range f → χ⁻¹ ∈ Set.range f := fun χ hχ =>
    (mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ).2 hχ) (H2 χ))
  have haR : a ∈ Set.range f := ⟨i₀, rfl⟩
  have hbR : b ∈ Set.range f := hrange a haR
  have hcR : c ∈ Set.range f := hrange b hbR
  have hb1 : b ≠ 1 := fun h => hi₀ (twist_eq_one hB5 θ hθ m hm h)
  have hc1 : c ≠ 1 := fun h => hb1 (twist_eq_one hB5 θ hθ m hm h)
  have ha5 : a ^ 5 = 1 := chars_pow_five hB5 a
  have hb5 : b ^ 5 = 1 := chars_pow_five hB5 b
  have hc5 : c ^ 5 = 1 := chars_pow_five hB5 c
  have hai : a⁻¹ = a ^ 4 := inv_eq_pow_four ha5
  have hbi : b⁻¹ = b ^ 4 := inv_eq_pow_four hb5
  have hci : c⁻¹ = c ^ 4 := inv_eq_pow_four hc5
  have kb : ∀ l, b ≠ a ^ l := fun l => twist_ne_pow hB5 θ hθ m hm hi₀ l
  have kca : ∀ l, c ≠ a ^ l := fun l => twist_twist_ne_pow hB5 θ hθ m hm hi₀ l
  have kcb : ∀ l, c ≠ b ^ l := fun l => twist_ne_pow hB5 θ hθ m hm hb1 l
  have hab : a ≠ b := fun h => kb 1 (by rw [pow_one]; exact h.symm)
  have hac : a ≠ c := fun h => kca 1 (by rw [pow_one]; exact h.symm)
  have hbc : b ≠ c := fun h => kcb 1 (by rw [pow_one]; exact h.symm)
  have haa : a ≠ a⁻¹ := fun h => pow_ne_self hB5 hi₀ (n := 4) (by norm_num)
    (by rw [← hai]; exact h.symm)
  have hbb : b ≠ b⁻¹ := fun h => pow_ne_self hB5 hb1 (n := 4) (by norm_num)
    (by rw [← hbi]; exact h.symm)
  have hcc : c ≠ c⁻¹ := fun h => pow_ne_self hB5 hc1 (n := 4) (by norm_num)
    (by rw [← hci]; exact h.symm)
  have hab' : a ≠ b⁻¹ := fun h => kb 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hai)
  have hba' : b ≠ a⁻¹ := fun h => kb 4 (h.trans hai)
  have hac' : a ≠ c⁻¹ := fun h => kca 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hai)
  have hca' : c ≠ a⁻¹ := fun h => kca 4 (h.trans hai)
  have hbc' : b ≠ c⁻¹ := fun h => kcb 4 ((inv_eq_iff_eq_inv.1 h.symm).trans hbi)
  have hcb' : c ≠ b⁻¹ := fun h => kcb 4 (h.trans hbi)
  have hab'' : a⁻¹ ≠ b⁻¹ := fun h => hab (inv_injective h)
  have hac'' : a⁻¹ ≠ c⁻¹ := fun h => hac (inv_injective h)
  have hbc'' : b⁻¹ ≠ c⁻¹ := fun h => hbc (inv_injective h)
  have hsum := sum_six_le f hab hac haa hab' hac' hbc hba' hbb hbc' hca' hcb' hcc hab'' hac''
    hbc''
  have hpa : 0 < mult f a := (mult_pos_iff f a).2 haR
  have hpb : 0 < mult f b := (mult_pos_iff f b).2 hbR
  have hpc : 0 < mult f c := (mult_pos_iff f c).2 hcR
  have hpai : 0 < mult f a⁻¹ := (mult_pos_iff f _).2 (hrangeinv a haR)
  have hpbi : 0 < mult f b⁻¹ := (mult_pos_iff f _).2 (hrangeinv b hbR)
  have hpci : 0 < mult f c⁻¹ := (mult_pos_iff f _).2 (hrangeinv c hcR)
  rw [hcard] at hsum
  have hma : mult f a = 1 := by omega
  have hmb : mult f b = 1 := by omega
  have hmc : mult f c = 1 := by omega
  have hmai : mult f a⁻¹ = 1 := by omega
  have hmbi : mult f b⁻¹ = 1 := by omega
  have hmci : mult f c⁻¹ = 1 := by omega
  have hall : ∀ i, f i = a ∨ f i = b ∨ f i = c ∨ f i = a⁻¹ ∨ f i = b⁻¹ ∨ f i = c⁻¹ := by
    have h6 := sum_mult_eq f ({a, b, c, a⁻¹, b⁻¹, c⁻¹} : Finset (B →* X))
    have hsum6 : ∑ χ ∈ ({a, b, c, a⁻¹, b⁻¹, c⁻¹} : Finset (B →* X)), mult f χ = 6 := by
      rw [Finset.sum_insert (by simp [hab, hac, haa, hab', hac']),
        Finset.sum_insert (by simp [hbc, hba', hbb, hbc']),
        Finset.sum_insert (by simp [hca', hcb', hcc]),
        Finset.sum_insert (by simp [hab'', hac'']), Finset.sum_pair hbc'']
      omega
    have hcardF : (Finset.univ.filter fun i => f i ∈
        ({a, b, c, a⁻¹, b⁻¹, c⁻¹} : Finset (B →* X))).card = Fintype.card ι := by
      rw [h6, hsum6, hcard]
    have := Finset.eq_univ_of_card _ hcardF
    intro i
    have hi : i ∈ (Finset.univ.filter fun i => f i ∈
        ({a, b, c, a⁻¹, b⁻¹, c⁻¹} : Finset (B →* X))) := by rw [this]; exact Finset.mem_univ i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] using hi
  refine ⟨?_, a, hi₀, haR, ?_⟩
  · intro i j hij
    by_contra hne
    have h2 := two_le_mult_of_ne f hne hij
    rcases hall i with h | h | h | h | h | h <;> rw [h] at h2 <;> omega
  · rintro _ ⟨i, rfl⟩
    exact hall i

theorem sp_scalar_lemma (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B)
    (hθ : ∀ b, b * θ b * θ (θ b) = 1) (f : ι → (B →* X)) (m : ℕ) (hm : ¬ 5 ∣ m)
    {χ₀ : B →* X} (hχ₀ : χ₀ ≠ 1) (h0 : χ₀ ∈ Set.range f)
    (hall : ∀ ψ ∈ Set.range f, ψ = χ₀ ∨ ψ = twist θ m χ₀ ∨ ψ = twist θ m (twist θ m χ₀) ∨
        ψ = χ₀⁻¹ ∨ ψ = (twist θ m χ₀)⁻¹ ∨ ψ = (twist θ m (twist θ m χ₀))⁻¹)
    (m' : ℕ) (hm' : ¬ 5 ∣ m') (H' : ∀ χ, mult f χ ≤ mult f (χ ^ m')) :
    m' % 5 = 1 ∨ m' % 5 = 4 := by
  have hmem : χ₀ ^ m' ∈ Set.range f :=
    (mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ₀).2 h0) (H' χ₀))
  have h5 : χ₀ ^ 5 = 1 := chars_pow_five hB5 χ₀
  have hinv : χ₀⁻¹ = χ₀ ^ 4 := inv_eq_pow_four h5
  rcases hall _ hmem with h | h | h | h | h | h
  · left
    by_contra hne
    exact pow_ne_self hB5 hχ₀ hne h
  · exact absurd h.symm (twist_ne_pow hB5 θ hθ m hm hχ₀ m')
  · exact absurd h.symm (twist_twist_ne_pow hB5 θ hθ m hm hχ₀ m')
  · right
    by_contra hne
    have h4 : (χ₀ ^ m') ^ 4 = χ₀ := by
      rw [h, hinv, ← pow_mul, pow_eq_pow_mod (4 * 4) h5]
      norm_num
    have h4' : χ₀ ^ (m' * 4) = χ₀ := by rw [pow_mul]; exact h4
    exact pow_ne_self hB5 hχ₀ (n := m' * 4) (by omega) h4'
  · exact absurd ((inv_eq_iff_eq_inv.1 h.symm).trans
      ((inv_eq_pow_four (chars_pow_five hB5 (χ₀ ^ m'))).trans (by rw [← pow_mul])))
      (twist_ne_pow hB5 θ hθ m hm hχ₀ (m' * 4))
  · exact absurd ((inv_eq_iff_eq_inv.1 h.symm).trans
      ((inv_eq_pow_four (chars_pow_five hB5 (χ₀ ^ m'))).trans (by rw [← pow_mul])))
      (twist_twist_ne_pow hB5 θ hθ m hm hχ₀ (m' * 4))

end Sp

end CFSG.RankThree.PartOne.AUTSL
