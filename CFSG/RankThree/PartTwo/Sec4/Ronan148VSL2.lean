module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSLTwoMain

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open Matrix

variable {F₀ : Type} [Field F₀]

theorem two_pow_mod_three_of_odd {m : ℕ} (hm : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem eq_one_of_pow_three_eq_one [Finite F₀] {m : ℕ} (hm : Odd m) (hF : Nat.card F₀ = 2 ^ m)
    {a : F₀} (ha : a ^ 3 = 1) : a = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    norm_num at ha
  have := Fintype.ofFinite F₀
  have h1 : a ^ (2 ^ m - 1) = 1 := by
    rw [← hF, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one a ha0
  have hmod := two_pow_mod_three_of_odd hm
  have hg : Nat.gcd 3 (2 ^ m - 1) = 1 := by
    have h3 : ¬ 3 ∣ 2 ^ m - 1 := by
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have : a ^ Nat.gcd 3 (2 ^ m - 1) = 1 := pow_gcd_eq_one.mpr ⟨ha, h1⟩
  rwa [hg, pow_one] at this

variable [CharP F₀ 2]

theorem mul_self_eq_one_of_mulVec_eq {s : SpecialLinearGroup (Fin 2) F₀} {v : Fin 2 → F₀}
    (hv : v ≠ 0) (hsv : (s : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v = v) : s * s = 1 := by
  have h2 : (2 : F₀) = 0 := CharP.cast_eq_zero F₀ 2
  have hdet := s.2
  rw [Matrix.det_fin_two] at hdet
  have e0 := congrFun hsv 0
  have e1 := congrFun hsv 1
  simp only [mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
  set a := (s : Matrix (Fin 2) (Fin 2) F₀) 0 0
  set b := (s : Matrix (Fin 2) (Fin 2) F₀) 0 1
  set c := (s : Matrix (Fin 2) (Fin 2) F₀) 1 0
  set d := (s : Matrix (Fin 2) (Fin 2) F₀) 1 1
  have hD0 : ((a - 1) * (d - 1) - b * c) * v 0 = 0 := by
    linear_combination (d - 1) * e0 - b * e1
  have hD1 : ((a - 1) * (d - 1) - b * c) * v 1 = 0 := by
    linear_combination (a - 1) * e1 - c * e0
  have hD : (a - 1) * (d - 1) - b * c = 0 := by
    by_contra hD
    apply hv
    funext i
    fin_cases i
    · exact (mul_eq_zero.mp hD0).resolve_left hD
    · exact (mul_eq_zero.mp hD1).resolve_left hD
  have htr : a + d = 0 := by linear_combination -hD + hdet + h2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    show a * a + b * c = 1
    linear_combination -hdet + a * htr - h2
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    show a * b + b * d = 0
    linear_combination b * htr
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    show c * a + d * c = 0
    linear_combination c * htr
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    show c * b + d * d = 1
    linear_combination -hdet + d * htr - h2

theorem eq_one_of_fixes_two {g : SpecialLinearGroup (Fin 2) F₀} {v u : Fin 2 → F₀}
    (hv : v ≠ 0) (hu : ∀ c : F₀, u ≠ c • v) (hgv : (g : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v = v)
    (hgu : (g : Matrix (Fin 2) (Fin 2) F₀) *ᵥ u = u) : g = 1 := by
  have hD : v 0 * u 1 - v 1 * u 0 ≠ 0 := by
    intro hD
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have hu0 : u 0 = 0 := by
        have : v 1 * u 0 = 0 := by rw [h0, zero_mul, zero_sub, neg_eq_zero] at hD; exact hD
        exact (mul_eq_zero.mp this).resolve_left h1
      apply hu (u 1 / v 1)
      funext i
      fin_cases i
      · simp [hu0, h0]
      · simp [div_mul_cancel₀ _ h1]
    · apply hu (u 0 / v 0)
      funext i
      fin_cases i
      · simp [div_mul_cancel₀ _ h0]
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
        field_simp
        linear_combination hD
  have e := fun i => congrFun hgv i
  have f := fun i => congrFun hgu i
  simp only [mulVec, dotProduct, Fin.sum_univ_two] at e f
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  set g00 := (g : Matrix (Fin 2) (Fin 2) F₀) 0 0
  set g01 := (g : Matrix (Fin 2) (Fin 2) F₀) 0 1
  set g10 := (g : Matrix (Fin 2) (Fin 2) F₀) 1 0
  set g11 := (g : Matrix (Fin 2) (Fin 2) F₀) 1 1
  have e0 := e 0
  have e1 := e 1
  have f0 := f 0
  have f1 := f 1
  ext i j
  fin_cases i <;> fin_cases j
  · show g00 = 1
    apply mul_right_cancel₀ hD
    linear_combination u 1 * e0 - v 1 * f0
  · show g01 = 0
    apply mul_right_cancel₀ hD
    linear_combination -(u 0) * e0 + v 0 * f0
  · show g10 = 0
    apply mul_right_cancel₀ hD
    linear_combination u 1 * e1 - v 1 * f1
  · show g11 = 1
    apply mul_right_cancel₀ hD
    linear_combination -(u 0) * e1 + v 0 * f1

variable [Finite F₀]

theorem exists_ne_zero_fixed_of_isPGroup_two {S : Subgroup (SpecialLinearGroup (Fin 2) F₀)}
    (hS : IsPGroup 2 S) :
    ∃ v : Fin 2 → F₀, v ≠ 0 ∧ ∀ g ∈ S, (g : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction S (Fin 2 → F₀) :=
    { smul := fun g v => ((g : SpecialLinearGroup (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v
      one_smul := fun v => by
        change ((1 : SpecialLinearGroup (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v = v
        rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]
      mul_smul := fun g h v => by
        change (((g * h : S) : SpecialLinearGroup (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v =
          ((g : SpecialLinearGroup (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀) *ᵥ
            (((h : SpecialLinearGroup (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v)
        rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mulVec_mulVec] }
  have h2 : 2 ∣ Nat.card (Fin 2 → F₀) := by
    rw [Nat.card_fun, Nat.card_fin]
    have := Fintype.ofFinite F₀
    obtain ⟨n, -, hcard⟩ := FiniteField.card F₀ 2
    have h2F : 2 ∣ Nat.card F₀ := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self 2 (PNat.ne_zero n)
    exact dvd_pow h2F (by norm_num)
  have h0 : (0 : Fin 2 → F₀) ∈ MulAction.fixedPoints S (Fin 2 → F₀) := fun g => by
    change ((g : SpecialLinearGroup (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀) *ᵥ 0 = 0
    exact mulVec_zero _
  obtain ⟨v, hv, hv0⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (Fin 2 → F₀) h2 h0
  exact ⟨v, fun h => hv0 h.symm, fun g hg => hv ⟨g, hg⟩⟩

theorem eq_bot_of_isPGroup_two_of_mem_normalizer {m : ℕ} (hm : Odd m) (hF : Nat.card F₀ = 2 ^ m)
    {s : SpecialLinearGroup (Fin 2) F₀} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    {S : Subgroup (SpecialLinearGroup (Fin 2) F₀)} (hS : IsPGroup 2 S)
    (hsS : s ∈ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 2) F₀))) : S = ⊥ := by
  by_contra hne
  obtain ⟨⟨g₀, hg₀S⟩, hg₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hg₀1 : g₀ ≠ 1 := fun h => hg₀1' (Subtype.ext h)
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_fixed_of_isPGroup_two hS
  have hsv : ∀ g ∈ S, (g : Matrix (Fin 2) (Fin 2) F₀) *ᵥ
      ((s : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v) = (s : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v := by
    intro g hg
    have hg' : s⁻¹ * g * s ∈ S := by
      have := (Subgroup.mem_normalizer_iff''.mp hsS g).mp hg
      exact this
    have h1 := hv _ hg'
    have e : g * s = s * (s⁻¹ * g * s) := by group
    rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, e, Matrix.SpecialLinearGroup.coe_mul,
      ← mulVec_mulVec, h1]
  obtain ⟨c, hc⟩ : ∃ c : F₀, (s : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v = c • v := by
    by_contra hcon
    push Not at hcon
    exact hg₀1 (eq_one_of_fixes_two hv0 hcon (hv g₀ hg₀S) (hsv g₀ hg₀S))
  have hc3 : c ^ 3 = 1 := by
    have h1 : ((s ^ 3 : SpecialLinearGroup (Fin 2) F₀) : Matrix (Fin 2) (Fin 2) F₀) *ᵥ v =
        c ^ 3 • v := by
      rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← mulVec_mulVec, ← mulVec_mulVec]
      simp only [hc, mulVec_smul, smul_smul]
      congr 1
      ring
    rw [hs3, Matrix.SpecialLinearGroup.coe_one, one_mulVec] at h1
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (funext hcon)
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hi (h2.symm.trans (one_mul _).symm))
  have hc1 := eq_one_of_pow_three_eq_one hm hF hc3
  rw [hc1, one_smul] at hc
  have hss := mul_self_eq_one_of_mulVec_eq hv0 hc
  apply hs1
  calc s = s ^ 3 * (s * s)⁻¹ := by group
    _ = 1 := by rw [hs3, hss, inv_one, one_mul]

theorem commute_of_odd_card {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F₀ = 2 ^ f) (H : Subgroup (SpecialLinearGroup (Fin 2) F₀))
    (hH : Odd (Nat.card H)) : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F₀)) with hφdef
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφdef, QuotientGroup.ker_mk',
      Sec14.Item148Res8.center_slTwo_eq_bot]
  set H' := H.map φ with hH'
  have hHH : Nat.card H' = Nat.card H := Subgroup.card_map_of_injective hφ
  suffices hc : IsMulCommutative H' by
    intro x hx y hy
    have := hc.is_comm.comm ⟨φ x, Subgroup.mem_map_of_mem φ hx⟩ ⟨φ y, Subgroup.mem_map_of_mem φ hy⟩
    apply hφ
    simpa using congrArg Subtype.val this
  have hodd : Odd (Nat.card H') := hHH ▸ hH
  have heven : ∀ k : ℕ, Nat.card H' = 2 * k → False := fun k hk => by
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul k)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H' with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, -, hzc, -⟩ | ⟨-, ⟨e4⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e5⟩⟩ |
      ⟨k, t, -, -, N, C, hNn, -, hNc, hCcyc, hCc, hdisj, hsup⟩ | ⟨k, hk, -, ⟨e⟩⟩ |
      ⟨k, hk, -, ⟨e⟩⟩
  · exact hEl.toIsMulCommutative
  · exact ⟨⟨fun a b => (IsCyclic.commGroup (α := H')).mul_comm a b⟩⟩
  · exact (heven z hzc).elim
  · exfalso
    apply heven 6
    rw [Nat.card_congr e4.toEquiv, nat_card_alternatingGroup]
    simp
    decide
  · exfalso
    apply heven 12
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    simp
    decide
  · exfalso
    apply heven 30
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup]
    simp
    decide
  · have hNC : Nat.card H' = 2 ^ k * t := by
      rw [← hNc, ← hCc, ← Sec14.Item148Res8.card_sup_eq_mul_of_disjoint N C hdisj, hsup,
        Subgroup.card_top]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hN1 : N = ⊥ := by
        rw [← Subgroup.card_eq_one, hNc, pow_zero]
      rw [hN1, bot_sup_eq] at hsup
      rw [hsup] at hCcyc
      have : IsCyclic H' := isCyclic_of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup H') ≃* H').toMonoidHom (MulEquiv.surjective _)
      exact ⟨⟨fun a b => (IsCyclic.commGroup (α := H')).mul_comm a b⟩⟩
    · exfalso
      apply heven (2 ^ (k - 1) * t)
      rw [hNC, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hkpos]
  · exfalso
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    apply heven (2 ^ (k - 1) * ((2 ^ k) ^ 2 - 1))
    rw [Nat.card_congr e.toEquiv, Sec14.Item148Res8.card_psl2_charTwo, GaloisField.card 2 k hk,
      ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk1]
  · exfalso
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    apply heven (2 ^ (k - 1) * ((2 ^ k) ^ 2 - 1))
    rw [Nat.card_congr e.toEquiv, CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hk,
      ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hk1, ← pow_mul, mul_comm k 2]

theorem commute_of_mem_normalizer {m : ℕ} (hm : Odd m)
    (hF : Nat.card F₀ = 2 ^ m) {s : SpecialLinearGroup (Fin 2) F₀} (hs3 : s ^ 3 = 1)
    {R : Subgroup (SpecialLinearGroup (Fin 2) F₀)} (hR3 : ¬ 3 ∣ Nat.card R)
    (hsR : s ∈ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 2) F₀))) :
    ∀ r ∈ R, r * s = s * r := by
  by_cases hs1 : s = 1
  · intro r _
    rw [hs1, mul_one, one_mul]
  have hm1 : 1 ≤ m := by
    obtain ⟨k, rfl⟩ := hm
    omega
  set A := Subgroup.zpowers s with hA
  have hAp : IsPGroup 3 A := by
    refine IsPGroup.of_card (n := 1) ?_
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_zpowers, orderOf_eq_prime hs3 hs1, pow_one]
  have hAR : A ≤ Subgroup.normalizer (R : Set (SpecialLinearGroup (Fin 2) F₀)) :=
    Subgroup.zpowers_le.mpr hsR
  set T := R ⊓ Subgroup.centralizer ({s} : Set (SpecialLinearGroup (Fin 2) F₀)) with hT
  have hTR : T ≤ R := inf_le_left
  have hpow : ∀ p : ℕ, p.Prime → p ^ (Nat.card R).factorization p ∣ Nat.card T := by
    intro p hp
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨S, hSyl, -, hAS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three hp hAp hR3 hAR bot_le IsPGroup.of_bot (by
        intro a _
        rw [Subgroup.mem_normalizer_iff]
        intro x
        simp only [Subgroup.mem_bot]
        constructor
        · rintro rfl
          group
        · intro h
          have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
          rw [this, h]
          group)
    obtain ⟨P, hP⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hSyl
    have hcardS : Nat.card S = p ^ (Nat.card R).factorization p := by
      rw [← hP, Subgroup.card_map_of_injective R.subtype_injective, P.card_eq_multiplicity]
    have hSp : IsPGroup p S := hSyl.2.1
    have hSR : S ≤ R := hSyl.1
    have hsS : s ∈ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 2) F₀)) :=
      hAS (Subgroup.mem_zpowers s)
    rw [← hcardS]
    by_cases hp2 : p = 2
    · subst hp2
      rw [eq_bot_of_isPGroup_two_of_mem_normalizer hm hF hs3 hs1 hSp hsS, Subgroup.card_bot]
      exact one_dvd _
    by_cases hp3 : p = 3
    · subst hp3
      have h0 : (Nat.card R).factorization 3 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hR3
      rw [hcardS, h0, pow_zero]
      exact one_dvd _
    have hSodd : Odd (Nat.card S) := by
      rw [hcardS]
      exact Odd.pow (hp.odd_of_ne_two hp2)
    have hprod := Sec6.card_sup_mul_card_inf (Subgroup.zpowers_le.mpr hsS)
    have hAodd : Odd (Nat.card (Subgroup.zpowers s)) := by
      rw [Nat.card_zpowers, orderOf_eq_prime hs3 hs1]
      decide
    have hHodd : Odd (Nat.card (Subgroup.zpowers s ⊔ S : Subgroup _)) := by
      have h1 : Odd (Nat.card (Subgroup.zpowers s) * Nat.card S) := hAodd.mul hSodd
      rw [← hprod] at h1
      exact (Nat.odd_mul.mp h1).1
    have hcomm := commute_of_odd_card hm1 hF _ hHodd
    have hST : S ≤ T := fun x hx => ⟨hSR hx, Subgroup.mem_centralizer_singleton_iff.mpr
      (hcomm x (Subgroup.mem_sup_right hx) s (Subgroup.mem_sup_left (Subgroup.mem_zpowers s)))⟩
    exact Subgroup.card_dvd_of_le hST
  have hRT : Nat.card R ∣ Nat.card T := by
    have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
    rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne' hT0]
    intro p
    by_cases hp : p.Prime
    · exact (hp.pow_dvd_iff_le_factorization hT0).mp (hpow p hp)
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
      exact Nat.zero_le _
  have hTeq : T = R := Subgroup.eq_of_le_of_card_ge hTR (Nat.le_of_dvd Nat.card_pos hRT)
  intro r hr
  have : r ∈ T := hTeq ▸ hr
  exact Subgroup.mem_centralizer_singleton_iff.mp this.2

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
