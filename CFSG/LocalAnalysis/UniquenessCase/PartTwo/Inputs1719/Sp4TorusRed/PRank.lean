module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem eq_one_of_lam_zero_mul_lam_one {a b : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : (lam (k := K) (r := 2) 0) a * (lam (k := K) (r := 2) 1) b = 1) :
    a = 1 ∧ b = 1 := by
  classical
  let M0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    (((lam (k := K) (r := 2) 0 a : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  let M1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    (((lam (k := K) (r := 2) 1 b : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  have hsupp0 : IsSupp ({Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 2)} :
      Set (Fin 2 ⊕ Fin 2)) M0 := isSupp_lam 0 a
  have hsupp1 : IsSupp ({Sum.inl (1 : Fin 2), Sum.inr (1 : Fin 2)} :
      Set (Fin 2 ⊕ Fin 2)) M1 := isSupp_lam 1 b
  have hdisj : Disjoint ({Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 2)} : Set (Fin 2 ⊕ Fin 2))
      {Sum.inl (1 : Fin 2), Sum.inr (1 : Fin 2)} := by
    rw [Set.disjoint_left]
    rintro (x | x) hx hx' <;> simp at hx hx' <;> omega
  have hmat : M0 * M1 = 1 := by
    have h' := congrArg (fun z : StatedSp 2 K =>
      (((z : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) h
    simpa [M0, M1] using h'
  have hrow : ∀ x ∈ ({Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 2)} : Set (Fin 2 ⊕ Fin 2)),
      ∀ y, M0 x y = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y := by
    intro x hx y
    have hm := IsSupp.mul_apply_of_mem hsupp0 hsupp1 hdisj (x := x) hx y
    rw [hmat] at hm
    exact hm.symm
  have hM0 : M0 = 1 := by
    ext x y
    by_cases hx : x ∈ ({Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 2)} : Set (Fin 2 ⊕ Fin 2))
    · exact hrow x hx y
    · exact hsupp0 x y (Or.inl hx)
  have ha : a = 1 := by
    refine lam_injective (k := K) (r := 2) (i := (0 : Fin 2)) ?_
    simpa using statedSp_ext hM0
  have hM1 : (lam (k := K) (r := 2) 1) b = 1 := by
    simpa [ha] using h
  have hb : b = 1 := by
    refine lam_injective (k := K) (r := 2) (i := (1 : Fin 2)) ?_
    simpa using hM1
  exact ⟨ha, hb⟩

theorem two_le_pRank_of_lam_range_le {n p : ℕ} (hq : Nat.card K = 2 ^ n) (hp : p.Prime)
    (hpd : p ∣ 2 ^ n + 1) {H : Subgroup (StatedSp 2 K)}
    (h0 : (lam 0 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ≤ H)
    (h1 : (lam 1 : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K).range ≤ H) :
    2 ≤ CFSG.Open.pRank p H := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    (CFSG.Open.StatedAPI.card_statedSL 2 K).symm.trans
      (CFSG.Open.StatedAPI.card_statedSL_two K)
  have hdvdSL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [hcardSL, hq]
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [sq]
      exact mul_self_tsub_one _
    exact dvd_mul_of_dvd_right (hpd.trans ⟨2 ^ n - 1, hfac⟩) (2 ^ n)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvdSL
  let A := ↥(Subgroup.zpowers g) × ↥(Subgroup.zpowers g)
  have hcardA : Nat.card A = p ^ 2 := by
    change Nat.card (↥(Subgroup.zpowers g) × ↥(Subgroup.zpowers g)) = p ^ 2
    simp [hg, pow_two]
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => mul_comm' a b
  have hpow : ∀ a : A, a ^ p = 1 := by
    have hsingle : ∀ x : ↥(Subgroup.zpowers g), x ^ p = 1 := by
      intro x
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      rw [← Subgroup.orderOf_coe x]
      simpa [hg] using orderOf_dvd_of_mem_zpowers x.2
    rintro ⟨x, y⟩
    exact Prod.ext (hsingle x) (hsingle y)
  let f : A →* StatedSp 2 K := MonoidHom.noncommCoprod
    ((lam (k := K) (r := 2) 0).comp (Subgroup.zpowers g).subtype)
    ((lam (k := K) (r := 2) 1).comp (Subgroup.zpowers g).subtype)
    (fun x y => commute_lam_lam (k := K) (r := 2) (i := (0 : Fin 2)) (j := (1 : Fin 2))
      (by decide) (x : Matrix.SpecialLinearGroup (Fin 2) K)
      (y : Matrix.SpecialLinearGroup (Fin 2) K))
  have hker : ∀ a : A, f a = 1 → a = 1 := by
    rintro ⟨x, y⟩ h
    change (lam (k := K) (r := 2) 0) (x : Matrix.SpecialLinearGroup (Fin 2) K) *
      (lam (k := K) (r := 2) 1) (y : Matrix.SpecialLinearGroup (Fin 2) K) = 1 at h
    obtain ⟨hx, hy⟩ := eq_one_of_lam_zero_mul_lam_one h
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : a * b⁻¹ = 1 := by
      apply hker
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    calc a = a * b⁻¹ * b := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = 1 * b := by rw [h1]
      _ = b := one_mul b
  have hrange : f.range ≤ H := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change (lam (k := K) (r := 2) 0) (x : Matrix.SpecialLinearGroup (Fin 2) K) *
      (lam (k := K) (r := 2) 1) (y : Matrix.SpecialLinearGroup (Fin 2) K) ∈ H
    exact mul_mem (h0 ⟨(x : Matrix.SpecialLinearGroup (Fin 2) K), rfl⟩)
      (h1 ⟨(y : Matrix.SpecialLinearGroup (Fin 2) K), rfl⟩)
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hcardA f hf hrange

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
