module

public import CFSG.RankThree.PartOne.U5K.Kf.Invol
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.U5K.Kf.Frame

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def barAut (h : UnitaryFieldData 2 f K) : K ≃+* K :=
  have := h.finite
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, Finite.injective_iff_surjective.1 h.bar.injective⟩

theorem barAut_apply (c : K) : barAut h c = h.bar c := rfl

theorem zp_neg {ζ : K} (hζ : ζ ^ p = 1) (b : ZMod p) : zp ζ (-b) = (zp ζ b)⁻¹ := by
  have h1 : zp ζ b * zp ζ (-b) = 1 :=
    (zp_add hζ b (-b)).symm.trans ((congrArg (zp ζ) (add_neg_cancel b)).trans (zp_zero ζ))
  exact (inv_eq_of_mul_eq_one_right h1).symm

theorem ZetaData.barAut_ne_one (Z : ZetaData h p) : barAut h ≠ 1 := by
  intro hb
  have hζ : h.bar Z.ζ = Z.ζ := by
    rw [← barAut_apply, hb]
    rfl
  have h1 : Z.ζ ^ (2 ^ f + 1) = 1 := (Z.prim.pow_eq_one_iff_dvd _).2 Z.dvd
  rw [pow_succ, ← h.bar_apply Z.ζ, hζ] at h1
  have h2 : p ∣ 2 := (Z.prim.pow_eq_one_iff_dvd 2).1 (by rw [pow_two]; exact h1)
  have := Nat.le_of_dvd (by norm_num) h2
  have := Z.five_le
  omega

theorem ZetaData.eq_barAut (Z : ZetaData h p) {τ : K ≃+* K} (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) :
    τ = barAut h := by
  classical
  have hfin := h.finite
  obtain ⟨hcardAut, hcyc⟩ := card_ringAut_and_isCyclic h.prime K h.card
  have : Fintype K := Fintype.ofFinite K
  have hfinAut : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; have := h.one_le; omega)
  have : Fintype (RingAut K) := Fintype.ofFinite _
  have hb2 : barAut h * barAut h = 1 := by
    ext c
    simp [barAut_apply, h.bar_bar]
  by_contra hne
  have hsub : ({1, barAut h, τ} : Finset (RingAut K)) ⊆
      Finset.univ.filter fun a : RingAut K => a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow _
    · rw [pow_two]; exact hb2
    · rw [pow_two]; exact hτ2
  have hcard : ({1, barAut h, τ} : Finset (RingAut K)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using Ne.symm hne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(Z.barAut_ne_one).symm, hτ1.symm⟩
  have h1 := Finset.card_le_card hsub
  have h2 := IsCyclic.card_pow_eq_one_le (α := RingAut K) (n := 2) (by norm_num)
  rw [hcard] at h1
  omega

theorem ZetaData.barAut_zp (Z : ZetaData h p) (b : ZMod p) :
    barAut h (zp Z.ζ b) = zp Z.ζ (-b) := by
  rw [zp_neg Z.pow_eq_one, barAut_apply]
  exact (inv_eq_of_mul_eq_one_left (Z.bar_zp b)).symm

theorem ZetaData.relation_of_outer (Z : ZetaData h p) {Ã : Subgroup (VM p)}
    (s : MulAut (primeFormP h (idGram K 5))) (hs2 : s * s = 1)
    (hsD : s ∉ primeFormD h (idGram K 5))
    (hsc : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã →
      primeFormConjHom h (idGram K 5) (Z.dgU a) * s =
        s * primeFormConjHom h (idGram K 5) (Z.dgU a)) :
    ∃ M : primeFormUnitary h (idGram K 5), ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã →
      ∃ l : K, l ≠ 0 ∧ ∀ t i : Fin 5,
        ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) t i * zp Z.ζ (-(a i)) =
          l * zp Z.ζ (a t) * ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) t i := by
  have hC : IsPrimeFormGram (1 : GL (Fin 5) K) := isPrimeFormGram_idGram
  obtain ⟨⟨M, τ⟩, hs0⟩ := surjective_primeFormPsi (h := h) (n := 5) (by norm_num) Z.three_lt s
  have hs : primeFormConjHom h (idGram K 5) M * primeFormFieldHom h hC τ = s := by
    rw [← primeFormPsi_apply h hC M τ]
    exact hs0
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    apply hsD
    rw [← hs, map_one, mul_one]
    exact ⟨M, rfl⟩
  have hτ2 : τ * τ = 1 := by
    have h1 : primeFormPsi h hC ((⟨M, τ⟩ : primeFormUnitary h (idGram K 5) ⋊[primeFormFieldU h hC]
        (K ≃+* K)) * ⟨M, τ⟩) = 1 := by
      rw [map_mul, hs0, hs2]
    have := (primeFormPsi_eq_one_iff' (h := h) (n := 5) (by norm_num) Z.three_lt _).1 h1
    exact this.1
  have hτ : τ = barAut h := Z.eq_barAut hτ2 hτ1
  subst hτ
  refine ⟨M, fun a ha => ?_⟩
  set Δ := Z.dgU a with hΔ
  have h1 : primeFormConjHom h (idGram K 5)
      (M * primeFormFieldU h hC (barAut h) Δ * M⁻¹) = primeFormConjHom h (idGram K 5) Δ := by
    have e1 : s * primeFormConjHom h (idGram K 5) Δ * s⁻¹ = primeFormConjHom h (idGram K 5) Δ := by
      have hc' : primeFormConjHom h (idGram K 5) Δ * s = s * primeFormConjHom h (idGram K 5) Δ :=
        hsc a ha
      rw [← hc']
      group
    rw [← hs] at e1
    have e2 := primeFormField_conj_eq h hC (barAut h) Δ
    calc primeFormConjHom h (idGram K 5) (M * primeFormFieldU h hC (barAut h) Δ * M⁻¹)
        = primeFormConjHom h (idGram K 5) M * primeFormConjHom h (idGram K 5)
            (primeFormFieldU h hC (barAut h) Δ) * (primeFormConjHom h (idGram K 5) M)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
      _ = primeFormConjHom h (idGram K 5) M * (primeFormFieldHom h hC (barAut h) *
            primeFormConjHom h (idGram K 5) Δ * (primeFormFieldHom h hC (barAut h))⁻¹) *
            (primeFormConjHom h (idGram K 5) M)⁻¹ := by rw [e2]
      _ = (primeFormConjHom h (idGram K 5) M * primeFormFieldHom h hC (barAut h)) *
            primeFormConjHom h (idGram K 5) Δ *
            (primeFormConjHom h (idGram K 5) M * primeFormFieldHom h hC (barAut h))⁻¹ := by
          group
      _ = primeFormConjHom h (idGram K 5) Δ := e1
  have h2 : primeFormConjHom h (idGram K 5)
      (M * primeFormFieldU h hC (barAut h) Δ * M⁻¹ * Δ⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  obtain ⟨c, -, hc⟩ := (Z.conj_eq_one_iff _).1 h2
  have h3 : (M : GL (Fin 5) K) * glAut (barAut h) (Δ : GL (Fin 5) K) * (M : GL (Fin 5) K)⁻¹ *
      (Δ : GL (Fin 5) K)⁻¹ = GeneralLinearGroup.scalar (Fin 5) c := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
    exact hc
  have h4 : (M : GL (Fin 5) K) * glAut (barAut h) (Δ : GL (Fin 5) K) =
      GeneralLinearGroup.scalar (Fin 5) c * (Δ : GL (Fin 5) K) * (M : GL (Fin 5) K) := by
    have h5 : (M : GL (Fin 5) K) * glAut (barAut h) (Δ : GL (Fin 5) K) * (M : GL (Fin 5) K)⁻¹ =
        GeneralLinearGroup.scalar (Fin 5) c * (Δ : GL (Fin 5) K) := mul_inv_eq_iff_eq_mul.1 h3
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5
  refine ⟨c, Units.ne_zero c, fun t i => ?_⟩
  have h6 := congrArg (fun g : GL (Fin 5) K => ((g : Matrix (Fin 5) (Fin 5) K)) t i) h4
  simp only [Units.val_mul, coe_glAut, hΔ, ZetaData.dgU_val, diagonal_map (map_zero (barAut h)),
    Matrix.mul_diagonal, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_mul_diagonal,
    Matrix.diagonal_mul] at h6
  rw [Z.barAut_zp] at h6
  exact h6

theorem ZetaData.no_outer (Z : ZetaData h p) {Ã : Subgroup (VM p)}
    (hG : ∀ i j : Fin 5, i ≠ j → ∃ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã ∧ a i ≠ a j)
    (hcard : Nat.card Ã = p ^ 4) (s : MulAut (primeFormP h (idGram K 5))) (hs2 : s * s = 1)
    (hsD : s ∉ primeFormD h (idGram K 5))
    (hsc : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã →
      primeFormConjHom h (idGram K 5) (Z.dgU a) * s =
        s * primeFormConjHom h (idGram K 5) (Z.dgU a)) :
    False := by
  classical
  obtain ⟨M, hM⟩ := Z.relation_of_outer s hs2 hsD hsc
  set Mm : Matrix (Fin 5) (Fin 5) K := ((M : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hMm
  have hcol : ∀ i, ∃ t, Mm t i ≠ 0 := by
    intro i
    by_contra hcon
    push Not at hcon
    have h1 : (((M : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * Mm = 1 :=
      Units.inv_mul _
    have h2 := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply] at h2
    simp only [hcon, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at h2
    exact zero_ne_one h2
  have hzp : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã → ∃ l : K, l ≠ 0 ∧ ∀ t i,
      Mm t i ≠ 0 → zp Z.ζ (-(a i)) = l * zp Z.ζ (a t) := by
    intro a ha
    obtain ⟨l, hl, hrel⟩ := hM a ha
    refine ⟨l, hl, fun t i hti => ?_⟩
    have := hrel t i
    exact mul_right_cancel₀ hti (by rw [mul_comm]; exact this)
  have huniq : ∀ i t t', Mm t i ≠ 0 → Mm t' i ≠ 0 → t = t' := by
    intro i t t' ht ht'
    by_contra hne
    obtain ⟨a, ha, hat⟩ := hG t t' hne
    obtain ⟨l, hl, hz⟩ := hzp a ha
    have h1 := hz t i ht
    have h2 := hz t' i ht'
    apply hat
    exact (zp_inj Z.prim).1 (mul_left_cancel₀ hl (h1.symm.trans h2))
  choose π hπ using hcol
  have hrel : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Ã → ∀ i j,
      a (π i) + a i = a (π j) + a j := by
    intro a ha i j
    obtain ⟨l, hl, hz⟩ := hzp a ha
    have key : ∀ k, zp Z.ζ (a (π k) + a k) = l⁻¹ := by
      intro k
      have h1 := hz (π k) k (hπ k)
      rw [zp_neg Z.pow_eq_one] at h1
      rw [Z.zp_add']
      have hk0 := zp_ne_zero Z.prim (a k)
      field_simp at h1 ⊢
      linear_combination -h1
    exact (zp_inj Z.prim).1 ((key i).trans (key j).symm)
  have hinv : ∀ i, π (π i) = i := by
    intro i
    by_contra hne
    obtain ⟨a, ha, hat⟩ := hG (π (π i)) i hne
    have := hrel a ha (π i) i
    apply hat
    linear_combination this
  have hle := card_le_of_involution (Ã := Ã) Z.five_le hG π hinv hrel
  rw [hcard] at hle
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) Z.five_le
  have := Nat.pow_lt_pow_right hp1 (show 3 < 4 by norm_num)
  omega

end CFSG.RankThree.PartOne.U5K.Kf
