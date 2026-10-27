module

public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGRCTypeADet
public import CFSG.LocalAnalysis.StandardType.GGTBWNormQuotTransvection

public section

namespace CFSG.StandardType

open Module

theorem ggWeylTypeData_card_dvd_of_rank_le_four {r n c : ℕ}
    (h : GGWeylTypeData r n c) (hr : r ≤ 4) : n ∣ 5760 := by
  rcases h with ⟨h1, hn, -⟩ | ⟨h2, hn, -⟩ | ⟨h4, hn, -⟩ |
    ⟨h6, -, -⟩ | ⟨h7, -, -⟩ | ⟨h8, -, -⟩ | ⟨-, hn, -⟩ | ⟨-, hn, -⟩
  · rw [hn]
    interval_cases r <;> norm_num
  · rw [hn]
    interval_cases r <;> norm_num
  · have : r = 4 := by omega
    subst r
    rw [hn]
    norm_num
  · omega
  · omega
  · omega
  · rw [hn]
    norm_num
  · rw [hn]
    norm_num

theorem ggWeylTypeData_not_prime_sq_dvd_of_rank_le_four {r n c p : ℕ}
    (h : GGWeylTypeData r n c) (hr : r ≤ 4) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ n := by
  intro hd
  have hd5760 : p ^ 2 ∣ 5760 := hd.trans (ggWeylTypeData_card_dvd_of_rank_le_four h hr)
  have hc2 : Nat.Coprime (p ^ 2) (2 ^ 7) :=
    Nat.coprime_pow_primes 2 7 hp Nat.prime_two (by omega)
  have hc3 : Nat.Coprime (p ^ 2) (3 ^ 2) :=
    Nat.coprime_pow_primes 2 2 hp Nat.prime_three (by omega)
  have hc : Nat.Coprime (p ^ 2) (2 ^ 7 * 3 ^ 2) := hc2.mul_right hc3
  have hd5 : p ^ 2 ∣ 5 := hc.dvd_of_dvd_mul_left (by norm_num at hd5760 ⊢; exact hd5760)
  have hle : p ^ 2 ≤ 5 := Nat.le_of_dvd (by decide) hd5
  nlinarith

section Coxeter


theorem not_prime_sq_dvd_card_coxeter_of_rank_le_four
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (h4 : Fintype.card ι ≤ 4) :
    ¬ p ^ 2 ∣ Nat.card M.Group :=
  ggWeylTypeData_not_prime_sq_dvd_of_rank_le_four
    (ggWeylTypeData_of_isWeylMatrix hM) h4 hp hp5

theorem not_prime_sq_dvd_card_range_of_small_coxeter
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (h4 : Fintype.card ι ≤ 4)
    {Γ : Type*} [Group Γ] (f : M.Group →* Γ) :
    ¬ p ^ 2 ∣ Nat.card f.range := by
  intro hd
  exact not_prime_sq_dvd_card_coxeter_of_rank_le_four hp hp5 hM h4
    (hd.trans (Subgroup.card_dvd_of_surjective (f := f.rangeRestrict)
      f.rangeRestrict_surjective))

theorem not_prime_sq_dvd_card_closure_of_small_coxeter
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) (h4 : Fintype.card ι ≤ 4)
    {Γ : Type*} [Group Γ] (φ : ι → Γ) (hφ : M.IsLiftable φ) :
    ¬ p ^ 2 ∣ Nat.card (Subgroup.closure (Set.range φ)) := by
  let F : M.Group →* Γ := M.toCoxeterSystem.lift ⟨φ, hφ⟩
  have hsimple : ∀ i, F (M.simple i) = φ i := by
    intro i
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.lift_apply_simple _ _ _
  have hrange : F.range = Subgroup.closure (Set.range φ) := by
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    apply congrArg (fun t : ι → Γ => Subgroup.closure (Set.range t))
    funext i
    exact hsimple i
  rw [← hrange]
  exact not_prime_sq_dvd_card_range_of_small_coxeter hp hp5 hM h4 F

section Cartan

variable {p : ℕ} [Fact p.Prime] {E : Type} [Group E]
  {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem cartan_rank_le_four_of_finrank_le_four
    (hp5 : 5 ≤ p) {I : Type} [Fintype I] [DecidableEq I]
    {M : CoxeterMatrix I} {C : Matrix I I ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    [Module.Finite (ZMod p) V] (h : I → V) (α : I → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hdim : Module.finrank (ZMod p) V ≤ 4) : Fintype.card I ≤ 4 := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  by_contra hcard
  have hdet : ((C.det : ℤ) : ZMod p) = 0 := by
    by_contra hdet
    have hmatrix : (Matrix.of fun i j => α i (h j)) =
        C.map (fun z : ℤ => (z : ZMod p)) := by
      ext i j
      exact hpair i j
    have hdet' : (Matrix.of fun i j => α i (h j)).det ≠ 0 := by
      rw [hmatrix, ← Int.cast_det C]
      exact hdet
    have hind := linearIndependent_of_det_ne_zero h α hdet'
    have hle := hind.fintype_card_le_finrank
    omega
  rcases ggRC_singular_typeA_or_E6 hp hp2 hM hC hdet with
    ⟨⟨r, e, -, hMe⟩, hpr⟩ | ⟨hp3, -⟩
  · have hr : Fintype.card I = r := by simpa using (Fintype.card_congr e).symm
    rw [hr] at hpr
    have hr5 : 5 ≤ r := by omega
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hm : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have h1 : p ∣ m + 1 + 1 - (m + 1) := Nat.dvd_sub hpr hd
      rw [show m + 1 + 1 - (m + 1) = 1 by omega] at h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    have hli := QuotMove.linearIndependent_coroots_typeA e
      (ggQ2_cartan_A e hMe hC) h α hpair hm
    have hle := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hle
    have hm4 : m = 4 := by omega
    rw [hm4] at hpr
    have hd : p ∣ 2 * 3 := by norm_num at hpr ⊢; exact hpr
    rcases hp.dvd_mul.mp hd with h2 | h3
    · have := Nat.le_of_dvd (by decide : 0 < 2) h2
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
  · omega

theorem isLiftable_ggLin_of_intCartan
    (ι : Additive E ≃+ V) {I : Type} {M : CoxeterMatrix I} {C : Matrix I I ℤ}
    (hC : GGIntCartan M C) (φ : I → MulAut E) (h : I → V)
    (α : I → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) :
    M.IsLiftable φ := by
  have hα : ∀ i, α i (h i) = 2 := by
    intro i
    rw [hpair, hC.1 i]
    norm_num
  have heq : ∀ i, ggLin (p := p) ι (φ i) = reflection (hα i) := by
    intro i
    apply LinearEquiv.ext
    intro v
    exact hlin i v
  have hL := isLiftable_reflection_of_intCartan hC h α hα hpair
  intro i j
  apply (ggLin_injective (p := p) ι)
  rw [map_pow, map_mul, map_one, heq i, heq j]
  exact hL i j

theorem not_prime_sq_dvd_card_closure_of_small_cartan
    (hp5 : 5 ≤ p) (ι : Additive E ≃+ V)
    {I : Type} [Fintype I] [DecidableEq I] {M : CoxeterMatrix I} {C : Matrix I I ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) (h4 : Fintype.card I ≤ 4)
    (φ : I → MulAut E) (h : I → V) (α : I → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) :
    ¬ p ^ 2 ∣ Nat.card (Subgroup.closure (Set.range φ)) :=
  not_prime_sq_dvd_card_closure_of_small_coxeter (Fact.out : p.Prime) hp5 hM h4 φ
    (isLiftable_ggLin_of_intCartan ι hC φ h α hpair hlin)

theorem not_prime_sq_dvd_card_closure_of_cartan_finrank_le_four
    (hp5 : 5 ≤ p) (ι : Additive E ≃+ V)
    {I : Type} [Fintype I] [DecidableEq I] {M : CoxeterMatrix I} {C : Matrix I I ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    [Module.Finite (ZMod p) V] (hdim : Module.finrank (ZMod p) V ≤ 4)
    (φ : I → MulAut E) (h : I → V) (α : I → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i v, ggLin (p := p) ι (φ i) v = v - α i v • h i) :
    ¬ p ^ 2 ∣ Nat.card (Subgroup.closure (Set.range φ)) :=
  not_prime_sq_dvd_card_closure_of_small_cartan hp5 ι hM hC
    (cartan_rank_le_four_of_finrank_le_four hp5 hM hC h α hpair hdim)
    φ h α hpair hlin

end Cartan

end Coxeter

end CFSG.StandardType
