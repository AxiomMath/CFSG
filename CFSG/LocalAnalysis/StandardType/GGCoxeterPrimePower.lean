module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterPrimeSquare

public section

namespace CFSG.StandardType

open Module

private theorem lt_of_pow_le_of_lt_pow {p q r n : ℕ} (hle : p ^ r ≤ n) (hlt : n < q ^ r) : p < q := by
  by_contra h
  push Not at h
  exact absurd (hle.trans_lt hlt) (not_lt.mpr (Nat.pow_le_pow_left h r))

theorem ggWeylTypeData_not_pow_rank_dvd {r n c p : ℕ} [Fact p.Prime] (h : GGWeylTypeData r n c)
    (hp2 : p ≠ 2) : ¬ p ^ r ∣ n := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hfact : ∀ m k : ℕ, m ≠ 0 → m ≤ 2 * k → ¬ p ^ k ∣ m.factorial := by
    intro m k hm hmk hd
    have hk := (padicValNat_dvd_iff_le (Nat.factorial_ne_zero m)).mp hd
    have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hm
    have : 2 * padicValNat p m.factorial ≤ (p - 1) * padicValNat p m.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hcop : ∀ k j : ℕ, Nat.Coprime (p ^ k) (2 ^ j) := fun k j =>
    Nat.Coprime.pow k j ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  rcases h with ⟨hr, hn, -⟩ | ⟨hr, hn, -⟩ | ⟨hr, hn, -⟩ |
    ⟨hr, hn, -⟩ | ⟨hr, hn, -⟩ | ⟨hr, hn, -⟩ | ⟨hr, hn, -⟩ | ⟨hr, hn, -⟩
  · rw [hn]
    exact fun hd => hfact (r + 1) r (by omega) (by omega)
      (dvd_trans (pow_dvd_pow p (by omega)) hd)
  · rw [hn]
    exact fun hd => hfact r r (by omega) (by omega) ((hcop r r).dvd_of_dvd_mul_left hd)
  · rw [hn]
    exact fun hd => hfact r r (by omega) (by omega) ((hcop r (r - 1)).dvd_of_dvd_mul_left hd)
  · subst hr
    rw [hn]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h7 : p < 7 := lt_of_pow_le_of_lt_pow hle (by norm_num)
    interval_cases p <;> first | omega | (norm_num at hd) | exact absurd hp (by norm_num)
  · subst hr
    rw [hn]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h9 : p < 9 := lt_of_pow_le_of_lt_pow hle (by norm_num)
    interval_cases p <;> first | omega | (norm_num at hd) | exact absurd hp (by norm_num)
  · subst hr
    rw [hn]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h13 : p < 13 := lt_of_pow_le_of_lt_pow hle (by norm_num)
    interval_cases p <;> first | omega | (norm_num at hd) | exact absurd hp (by norm_num)
  · subst hr
    rw [hn]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h6 : p < 6 := lt_of_pow_le_of_lt_pow hle (by norm_num)
    interval_cases p <;> first | omega | (norm_num at hd) | exact absurd hp (by norm_num)
  · subst hr
    rw [hn]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have h4 : p < 4 := lt_of_pow_le_of_lt_pow hle (by norm_num)
    interval_cases p <;> first | omega | (norm_num at hd) | exact absurd hp (by norm_num)

theorem ggWeylTypeData_six_not_three_pow_five_dvd {n c : ℕ} (h : GGWeylTypeData 6 n c) :
    ¬ 3 ^ 5 ∣ n := by
  rcases h with ⟨-, hn, -⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩ |
    ⟨-, hn, -⟩ | ⟨h7, -, -⟩ | ⟨h8, -, -⟩ | ⟨h4, -, -⟩ | ⟨h2, -, -⟩
  · rw [hn]; decide
  · rw [hn]; decide
  · rw [hn]; decide
  · rw [hn]; decide
  · omega
  · omega
  · omega
  · omega

section Cartan

variable {p : ℕ} [Fact p.Prime] {E : Type} [Group E]
  {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem card_le_finrank_of_linearIndependent_mem {ι : Type*} [Fintype ι]
    [Module.Finite (ZMod p) V] {W : Submodule (ZMod p) V} (g : ι → V)
    (hg : LinearIndependent (ZMod p) g) (hW : ∀ i, g i ∈ W) :
    Fintype.card ι ≤ Module.finrank (ZMod p) W := by
  have hg' : LinearIndependent (ZMod p) (fun i => (⟨g i, hW i⟩ : W)) :=
    LinearIndependent.of_comp W.subtype (by simpa [Function.comp_def] using hg)
  exact hg'.fintype_card_le_finrank

theorem linearIndependent_coroots_E6_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {I : Type} {M : CoxeterMatrix I} {C : Matrix I I ℤ} (e : Fin 6 ≃ I)
    (hM : M = CoxeterMatrix.E₆.reindex e) (hC : GGIntCartan M C) (h : I → V)
    (α : I → Module.Dual (ZMod 3) V) (hpair : ∀ i j, α i (h j) = (C i j : ZMod 3)) :
    LinearIndependent (ZMod 3) (fun k : Fin 5 => h (e k.castSucc)) := by
  apply linearIndependent_of_det_ne_zero (fun k : Fin 5 => h (e k.castSucc))
    (fun k : Fin 5 => α (e k.castSucc))
  have hCE := ggQ2_cartan_E₆ e hM hC
  have hmat : (Matrix.of fun i j : Fin 5 => α (e i.castSucc) (h (e j.castSucc))) =
      (CartanMatrix.E 5).map (fun z : ℤ => (z : ZMod 3)) := by
    ext i j
    rw [Matrix.of_apply, hpair, hCE, Matrix.map_apply]
    congr 1
    fin_cases i <;> fin_cases j <;> rfl
  rw [hmat, ← Int.cast_det, CartanMatrix.E_det (by norm_num)]
  decide

theorem not_prime_pow_dvd_card_closure_of_span_lt
    (hp2 : p ≠ 2) (ι : Additive E ≃+ V)
    {I : Type} [Fintype I] [DecidableEq I] {M : CoxeterMatrix I} {C : Matrix I I ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    [Module.Finite (ZMod p) V] (ha : 3 ≤ Module.finrank (ZMod p) V)
    (φ : I → MulAut E) (h : I → V) (α : I → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i)
    (hspan : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) <
      Module.finrank (ZMod p) V) :
    ¬ p ^ (Module.finrank (ZMod p) V - 1) ∣ Nat.card (Subgroup.closure (Set.range φ)) := by
  classical
  intro hd
  have hp : p.Prime := Fact.out
  set a := Module.finrank (ZMod p) V with hadef
  set W := Submodule.span (ZMod p) (Set.range h) with hWdef
  have hmemW : ∀ i, h i ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hφ := isLiftable_ggLin_of_intCartan ι hC φ h α hpair hlin
  let F : M.Group →* MulAut E := M.toCoxeterSystem.lift ⟨φ, hφ⟩
  have hsimple : ∀ i, F (M.simple i) = φ i := by
    intro i
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.lift_apply_simple _ _ _
  have hrange : F.range = Subgroup.closure (Set.range φ) := by
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    apply congrArg (fun t : I → MulAut E => Subgroup.closure (Set.range t))
    funext i
    exact hsimple i
  rw [← hrange] at hd
  have hW : p ^ (a - 1) ∣ Nat.card M.Group :=
    hd.trans (Subgroup.card_dvd_of_surjective (f := F.rangeRestrict) F.rangeRestrict_surjective)
  have hdata := ggWeylTypeData_of_isWeylMatrix hM
  by_cases hdet : ((C.det : ℤ) : ZMod p) = 0
  · rcases ggRC_singular_typeA_or_E6 hp hp2 hM hC hdet with
      ⟨⟨r, e, -, hMe⟩, hpr⟩ | ⟨hp3, ⟨e, hMe⟩⟩
    · have hr : Fintype.card I = r := by simpa using (Fintype.card_congr e).symm
      rw [hr] at hpr
      have hr1 : 1 ≤ r := by
        rcases Nat.eq_zero_or_pos r with rfl | h0
        · have := Nat.le_of_dvd (by norm_num) hpr
          have := hp.two_le
          omega
        · exact h0
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      have hm : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdv
        have h1 : p ∣ m + 1 + 1 - (m + 1) := Nat.dvd_sub hpr hdv
        rw [show m + 1 + 1 - (m + 1) = 1 by omega] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      have hli := QuotMove.linearIndependent_coroots_typeA e
        (ggQ2_cartan_A e hMe hC) h α hpair hm
      have hle := card_le_finrank_of_linearIndependent_mem (W := W) _ hli
        (fun k => hmemW _)
      simp only [Fintype.card_fin] at hle
      have hcard : Nat.card M.Group = (m + 1 + 1).factorial := by
        rw [hMe, Nat.card_congr ((CoxeterMatrix.A (m + 1)).reindexGroupEquiv e).toEquiv,
          l05nK3a_card_coxeterA]
      rw [hcard] at hW
      have hk := (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp hW
      have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p
        (show m + 1 + 1 ≠ 0 by omega)
      have h2 : 2 * (a - 1) ≤ (p - 1) * padicValNat p (m + 1 + 1).factorial :=
        (Nat.mul_le_mul_left 2 hk).trans (Nat.mul_le_mul_right _ (by
          have := hp.two_le
          omega))
      omega
    · subst hp3
      have hli := linearIndependent_coroots_E6_three e hMe hC h α hpair
      have hle := card_le_finrank_of_linearIndependent_mem (W := W) _ hli (fun k => hmemW _)
      simp only [Fintype.card_fin] at hle
      have h6 : Fintype.card I = 6 := by simpa using (Fintype.card_congr e).symm
      rw [h6] at hdata
      apply ggWeylTypeData_six_not_three_pow_five_dvd hdata
      exact dvd_trans (pow_dvd_pow 3 (by omega)) hW
  · have hmatrix : (Matrix.of fun i j => α i (h j)) =
        C.map (fun z : ℤ => (z : ZMod p)) := by
      ext i j
      exact hpair i j
    have hdet' : (Matrix.of fun i j => α i (h j)).det ≠ 0 := by
      rw [hmatrix, ← Int.cast_det C]
      exact hdet
    have hind := linearIndependent_of_det_ne_zero h α hdet'
    have hle := card_le_finrank_of_linearIndependent_mem (W := W) h hind hmemW
    apply ggWeylTypeData_not_pow_rank_dvd hdata hp2
    exact dvd_trans (pow_dvd_pow p (by omega)) hW

end Cartan

end CFSG.StandardType
