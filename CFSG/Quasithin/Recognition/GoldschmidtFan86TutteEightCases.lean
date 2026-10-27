module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteCoreSupport
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteEightRel
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteXviiFinal

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem shift_l_conj (r l : H) (i : ℕ) (K : List ℤ) (hK : Even K.length) :
    (MulAut.conj (l ^ (i : ℤ))).toMonoidHom (nfw r l 1 K) =
      nfw r l 1 (K.map (· - (i : ℤ))) := by
  have := nfw_shift_l r l (-(i : ℤ)) K hK
  rw [neg_neg] at this
  show l ^ (i : ℤ) * nfw r l 1 K * (l ^ (i : ℤ))⁻¹ = _
  rw [← zpow_neg, this]
  simp [sub_eq_add_neg]

theorem support8 (h : IsTutteSys s r l ξ Hs) (h8 : ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹) {i : ℕ}
    (hi : 1 ≤ i) (his : 2 * i ≤ s) (hab : Abel Hs (s - i)) (L : List ℤ)
    (hL : L.Pairwise (· > ·)) (hL1 : ∀ t ∈ L, 1 ≤ t ∧ t < (s : ℤ)) (heven : Even L.length)
    (hLh : nfw r l 1 L = rho r ξ s * tx r l s) :
    ∀ b : ℤ, (i : ℤ) < b → b < s →
      (Xor (b ∈ L) ((s : ℤ) - b ∈ L) ↔ (2 * i < s ∧ b = (s : ℤ) - i)) :=
  core_support h hi his hab 1 (Or.inl rfl) (MulAut.conj (l ^ (i : ℤ))).toMonoidHom
    (shift_l_conj r l i)
    (fun e' he' N => ⟨-e', by rcases he' with rfl | rfl <;> simp, xi_nfw8 h h8 e' N⟩) L hL hL1
    (rel8 h h8 hi his hab L heven hLh)

theorem no_two_cores8 (h : IsTutteSys s r l ξ Hs) (h8 : ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹)
    (i₁ i₂ : ℕ) (h1 : 1 ≤ i₁) (h12 : i₁ < i₂) (h2 : 2 * i₂ ≤ s) (hab : Abel Hs (s - i₁)) :
    False := by
  obtain ⟨L, hL, hL1, heven, hLh⟩ := parity_h8 h h8
  have hab2 : Abel Hs (s - i₂) := fun a ha b hb =>
    hab a (Hs_mono h (by omega) (by omega) ha) b (Hs_mono h (by omega) (by omega) hb)
  have hb1 := support8 h h8 (i := i₁) h1 (by omega) hab L hL hL1 heven hLh ((s : ℤ) - i₁)
    (by omega) (by omega)
  have hb2 := support8 h h8 (i := i₂) (by omega) h2 hab2 L hL hL1 heven hLh ((s : ℤ) - i₁)
    (by omega) (by omega)
  have e1 : Xor (((s : ℤ) - i₁) ∈ L) ((s : ℤ) - ((s : ℤ) - i₁) ∈ L) :=
    hb1.mpr ⟨by omega, rfl⟩
  have := (hb2.mp e1).2
  omega

theorem not_odd_case8 (h : IsTutteSys s r l ξ Hs) (h8 : ξ * r * ξ = l⁻¹ ∧ ξ * l * ξ = r⁻¹)
    (hs : 3 ≤ s) (hodd : Odd s) : False := by
  classical
  obtain ⟨i, hsi⟩ := hodd
  have hi : 1 ≤ i := by omega
  have hsz : (s : ℤ) = 2 * i + 1 := by omega
  have hab : Abel Hs (s - i) := by
    have e : s - i = i + 1 := by omega
    rw [e]
    exact abel_of_le_two_thirds h (by omega) (by omega)
  obtain ⟨L, hL, hL1, heven, hLh⟩ := parity_h8 h h8
  have hsupp := support8 h h8 (i := i) hi (by omega) hab L hL hL1 heven hLh
  have hsym : ∀ b : ℤ, (i : ℤ) < b → b < s → b ≠ (i : ℤ) + 1 → (b ∈ L ↔ (s : ℤ) - b ∈ L) := by
    intro b hb1 hb2 hb3
    have h1 := hsupp b hb1 hb2
    have hne : ¬ (2 * i < s ∧ b = (s : ℤ) - i) := fun hh => hb3 (by omega)
    have hnx : ¬ Xor (b ∈ L) ((s : ℤ) - b ∈ L) := fun hx => hne (h1.1 hx)
    simp only [Xor, not_or, not_and, not_not] at hnx
    tauto
  have hmid : Xor ((i : ℤ) + 1 ∈ L) ((i : ℤ) ∈ L) := by
    have h1 := hsupp ((i : ℤ) + 1) (by omega) (by omega)
    have e : (s : ℤ) - ((i : ℤ) + 1) = i := by omega
    rw [e] at h1
    exact h1.2 ⟨by omega, by omega⟩
  set S : Finset ℤ := L.toFinset with hS
  have hmem : ∀ t, t ∈ S ↔ t ∈ L := fun t => List.mem_toFinset
  have hcard : S.card = L.length := List.toFinset_card_of_nodup (decr_nodup hL)
  set S' : Finset ℤ := S.filter (fun t => t ≠ (i : ℤ) ∧ t ≠ (i : ℤ) + 1) with hS'
  set S'' : Finset ℤ := S.filter (fun t => ¬ (t ≠ (i : ℤ) ∧ t ≠ (i : ℤ) + 1)) with hS''
  have hsplit : S'.card + S''.card = S.card := Finset.card_filter_add_card_filter_not _
  have hS''1 : S''.card = 1 := by
    rw [Finset.card_eq_one]
    rcases hmid with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨(i : ℤ) + 1, ?_⟩
      ext t
      simp only [hS'', Finset.mem_filter, hmem, Finset.mem_singleton]
      constructor
      · rintro ⟨ht, hne⟩
        have : t = i ∨ t = (i : ℤ) + 1 := by by_contra hc; push Not at hc; exact hne hc
        rcases this with rfl | rfl
        · exact absurd ht h2
        · rfl
      · rintro rfl
        exact ⟨h1, fun hc => hc.2 rfl⟩
    · refine ⟨(i : ℤ), ?_⟩
      ext t
      simp only [hS'', Finset.mem_filter, hmem, Finset.mem_singleton]
      constructor
      · rintro ⟨ht, hne⟩
        have : t = i ∨ t = (i : ℤ) + 1 := by by_contra hc; push Not at hc; exact hne hc
        rcases this with rfl | rfl
        · rfl
        · exact absurd ht h2
      · rintro rfl
        exact ⟨h1, fun hc => hc.1 rfl⟩
  have hS'even : ∑ _t ∈ S', (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun t _ => (s : ℤ) - t) (fun _ _ => by decide)
      (fun t _ _ => by omega) ?_ (fun t _ => sub_sub_cancel _ _)
    intro t ht
    simp only [hS', Finset.mem_filter, hmem] at ht ⊢
    obtain ⟨htL, hti, hti1⟩ := ht
    have hb := hL1 t htL
    refine ⟨?_, by omega, by omega⟩
    rcases lt_or_gt_of_ne hti with hlt | hgt
    · have hb1 : (i : ℤ) < (s : ℤ) - t := by omega
      exact (hsym ((s : ℤ) - t) hb1 (by omega) (by omega)).2 (by rw [sub_sub_cancel]; exact htL)
    · have hgt' : (i : ℤ) < t := hgt
      exact (hsym t hgt' hb.2 hti1).1 htL
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hS'even
  have hev' : Even S'.card := ZMod.natCast_eq_zero_iff_even.mp hS'even
  have hevL : Even S.card := hcard ▸ heven
  obtain ⟨a, ha⟩ := hev'
  obtain ⟨b, hb⟩ := hevL
  omega

end CFSG.Quasithin.Fan86.Tutte
