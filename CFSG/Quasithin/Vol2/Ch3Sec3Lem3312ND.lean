module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312NC
public import CFSG.Quasithin.Background.A3Structure312Nonquasi

public section

namespace CFSG.Quasithin.H13.L3312.NQ

open CFSG.Open CFSG.QuasithinUnique

variable {Q : Type} [Group Q] [Finite Q]

theorem odd_card_center (hcomm : A36Common Q) (hext : A36Extra Q) (hO1 : CFSG.oddCore Q ≠ ⊥)
    {z : Q} (hz2 : z * z = 1) (hzO : z ∉ CFSG.oddCore Q)
    (huniq : ∀ t t' : Q, t * t = 1 → t' * t' = 1 → t ∉ CFSG.oddCore Q →
      t' ∉ CFSG.oddCore Q → t'⁻¹ * t ∈ CFSG.oddCore Q) :
    Odd (Nat.card (Subgroup.center Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  have ht2 : (t : Q) * t = 1 := by
    have : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
    exact congrArg Subtype.val this
  have hOodd := odd_card_oddCore (Q := Q)
  have hO2 : ∀ x ∈ CFSG.oddCore Q, x * x = 1 → x = 1 := by
    intro x hx hxx
    have h1 : orderOf (⟨x, hx⟩ : ↥(CFSG.oddCore Q)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [pow_two] using hxx))
    have h2 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(CFSG.oddCore Q))
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1
      (Nat.coprime_two_left.mpr hOodd)) h2
    rw [orderOf_eq_one_iff] at this
    exact congrArg Subtype.val this
  have htO : (t : Q) ∉ CFSG.oddCore Q := by
    intro h
    have := hO2 _ h ht2
    have h1 : t = 1 := Subtype.ext this
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hc : ∀ g : Q, g * t = t * g := fun g => Subgroup.mem_center_iff.mp t.2 g
  have h1 := huniq z t hz2 ht2 hzO htO
  have h2 : ((t : Q)⁻¹ * z) * ((t : Q)⁻¹ * z) = 1 := by
    have : (t : Q)⁻¹ * z = z * (t : Q)⁻¹ := by
      have := hc z
      calc (t : Q)⁻¹ * z = (t : Q)⁻¹ * (z * t) * (t : Q)⁻¹ := by group
        _ = (t : Q)⁻¹ * (t * z) * (t : Q)⁻¹ := by rw [this]
        _ = z * (t : Q)⁻¹ := by group
    calc (t : Q)⁻¹ * z * ((t : Q)⁻¹ * z) = (t : Q)⁻¹ * (z * (t : Q)⁻¹) * z := by group
      _ = (t : Q)⁻¹ * ((t : Q)⁻¹ * z) * z := by rw [← this]
      _ = ((t : Q) * t)⁻¹ * (z * z) := by group
      _ = 1 := by rw [ht2, hz2]; group
  have h3 := hO2 _ h1 h2
  have hzt : z = t := by
    calc z = (t : Q) * ((t : Q)⁻¹ * z) := by group
      _ = t := by rw [h3, mul_one]
  have hF : CFSG.fittingSubgroup Q = CFSG.oddCore Q := hcomm.1
  obtain ⟨q, hq, hqO⟩ : ∃ q, q.Prime ∧ q ∣ Nat.card (CFSG.oddCore Q) := by
    apply Nat.exists_prime_and_dvd
    intro h
    exact hO1 (Subgroup.card_eq_one.mp h)
  obtain ⟨P, -, -, -, hPiff⟩ := hext q hq (hF ▸ hqO)
  apply hzO
  rw [← hF, ← hPiff z]
  intro d _
  rw [hzt, ← hc d, mul_inv_cancel_right, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem a36case_of_nonquasi {X : Type} [Group X] [Finite X] {B L : Subgroup X}
    (hNQ : A312Nonquasi B L) (hA36 : Vol2Native.A36StrongCat L) :
    A36Common ↥L ∧ (A36Case3 ↥L ∨ A36Case4 ↥L) ∧ A36Extra ↥L := by
  obtain ⟨hconc, hcomm, hextra⟩ := hA36
  have hnq := A312.not_quasisimple_of_nonquasi hNQ
  have hcase : A36Case3 ↥L ∨ A36Case4 ↥L := by
    rcases hconc with ⟨hc, -, -⟩ | ⟨hc, -, -⟩ | h3 | h4
    · exact absurd hc.1 hnq
    · exact absurd hc.1 hnq
    · exact Or.inl h3
    · exact Or.inr h4
  exact ⟨hcomm, hcase, hextra hcase⟩

theorem oddNorm_case21 {B : Subgroup Q}
    (hcomm : A36Common Q) (hcase : A36Case3 Q ∨ A36Case4 Q) (hext : A36Extra Q)
    (htype : Type3312R (ModO2 B)) (hO1 : CFSG.oddCore Q ≠ ⊥) (hBsup : B ⊔ CFSG.oddCore Q = ⊤)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hSL : IsSL2 p (Q ⧸ CFSG.oddCore Q)) :
    OddNorm Q B := by
  have : Fact p.Prime := ⟨hp⟩
  have hOodd := odd_card_oddCore (Q := Q)
  have hBO : B ⊓ CFSG.oddCore Q = ⊥ := inf_oddCore_eq_bot htype
  obtain ⟨eSL⟩ := hSL
  have e₀ : ↥B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
    (equivQuotOfCompl hBO hBsup).trans eSL
  have hp5 : 5 ≤ p := by
    have hp3 : p ≠ 3 := by
      rintro rfl
      have h1 : Nat.card ↥B = 24 := by
        rw [Nat.card_congr e₀.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
          Nat.card_zmod]
        norm_num
      have h2 : Nat.card (ModO2 B) ≤ 24 := by
        rw [← h1]
        exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      rcases htype.card with ⟨n, hn, hc⟩ | hc | hc
      · rw [hc] at h2
        have h4 := Type3312R.three_le_pow hn
        have : 4 * (4 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
          Nat.mul_le_mul h4 (Type3312R.le_sq_sub_one h4)
        omega
      · omega
      · omega
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by have := hp.two_le; omega) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · subst h
      exact absurd hp (by norm_num)
    · exact h
  obtain ⟨hperf, z, hzB, hz2, hz1, hzuniq⟩ := sl2_data hp5 e₀
  have hzO : z ∉ CFSG.oddCore Q := fun h => hz1 (by
    have : z ∈ B ⊓ CFSG.oddCore Q := ⟨hzB, h⟩
    rwa [hBO, Subgroup.mem_bot] at this)
  have huniq := fun t t' (ht : t * t = 1) (ht' : t' * t' = 1) (htO : t ∉ CFSG.oddCore Q)
    (ht'O : t' ∉ CFSG.oddCore Q) => inv_mul_mem_of_isSL2 hp2 ⟨eSL⟩ ht ht' htO ht'O
  have hZodd := odd_card_center hcomm hext hO1 hz2 hzO huniq
  have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
  have hzF : z ∉ CFSG.fittingSubgroup Q := by rw [hcomm.1]; exact hzO
  have hCz := le_centralizer_of_fitting hcomm hcase hext hzB hz2 hzF
  rw [hcomm.1] at hCz
  have hOsolv : Group.IsSolvable ↥(CFSG.oddCore Q) := by
    have : Group.IsNilpotent ↥(CFSG.fittingSubgroup Q) := inferInstance
    rw [hcomm.1] at this
    infer_instance
  exact oddNorm_of_complement hOodd hOsolv hBO hBsup hperf hzB hz2 hz1 hzuniq huniq hZodd hCz

end CFSG.Quasithin.H13.L3312.NQ
