module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessCore
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148B

open Matrix CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

variable {p : ℕ} [hp : Fact p.Prime]

theorem eq_or_eq_sq_of_root {F : Type*} [Field F] {ω t : F} (hω : ω ^ 2 + ω + 1 = 0)
    (ht : t ^ 2 + t + 1 = 0) : t = ω ∨ t = ω ^ 2 := by
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have : (t - ω) * (t - ω ^ 2) = 0 := by
    linear_combination ht - t * hω + h3
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h)

theorem exists_root_zmod (hp1 : p % 3 = 1) : ∃ a : ZMod p, a ^ 2 + a + 1 = 0 := by
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have h3 : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [hcard]
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 h3
  refine ⟨(u : ZMod p), ?_⟩
  have hu3 : (u : ZMod p) ^ 3 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hu1 : (u : ZMod p) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    omega
  have : ((u : ZMod p) - 1) * ((u : ZMod p) ^ 2 + (u : ZMod p) + 1) = 0 := by
    linear_combination hu3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hu1)

theorem hessPhi_mem_hessH_linear {F : Type} [Field F] [CharP F p]
    (hp23 : 23 ≤ p) (hp1 : p % 3 = 1) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ hessH hω h3 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of hp2
  obtain ⟨a, ha⟩ := exists_root_zmod hp1
  set ψ : ZMod p →+* F := ZMod.castHom (dvd_refl p) F with hψdef
  have hψa : (ψ a) ^ 2 + ψ a + 1 = 0 := by
    have := congrArg ψ ha
    simpa using this
  obtain ⟨ω₀, hω₀, hψ⟩ : ∃ ω₀ : ZMod p, ω₀ ^ 2 + ω₀ + 1 = 0 ∧ ψ ω₀ = ω := by
    rcases eq_or_eq_sq_of_root hω hψa with h | h
    · exact ⟨a, ha, h⟩
    · refine ⟨a ^ 2, ?_, ?_⟩
      · have ha3 : a ^ 3 = 1 := by linear_combination (a - 1) * ha
        have ha4 : a ^ 4 = a := by
          calc a ^ 4 = a ^ 3 * a := by ring
            _ = a := by rw [ha3, one_mul]
        linear_combination ha4 + ha
      · rw [map_pow, h]
        have h3' : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
        calc (ω ^ 2) ^ 2 = ω ^ 3 * ω := by ring
          _ = ω := by rw [h3', one_mul]
  have hne : ∀ q : ℕ, q.Prime → p ≠ q → (q : ZMod p) ≠ 0 := fun q hq hpq =>
    prime_ne_zero_of (k := ZMod p) hq hpq
  have h2₀ : (2 : ZMod p) ≠ 0 := by exact_mod_cast hne 2 Nat.prime_two hp2
  have h3₀ : (3 : ZMod p) ≠ 0 := by exact_mod_cast hne 3 Nat.prime_three hp3
  have h5₀ : (5 : ZMod p) ≠ 0 := by exact_mod_cast hne 5 Nat.prime_five (by omega)
  have h13₀ : (13 : ZMod p) ≠ 0 := by exact_mod_cast hne 13 (by norm_num) (by omega)
  have hk : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hG : Nat.card (⊤ : Subgroup SL(2, ZMod p)) ≤ p * (p ^ 2 - 1) := by
    rw [Subgroup.card_top, card_sl2_field, Nat.card_zmod]
  obtain ⟨r, hr, hz⟩ := exists_rot_z2_mem_closure hω hk hp23 ψ hω₀ h2₀ h3₀ h5₀ h13₀ ⊤ hG
    (Subgroup.mem_top _) (Subgroup.mem_top _) (Subgroup.mem_top _) (Subgroup.mem_top _)
    (Subgroup.mem_top _)
  exact hessPhi_mem_hessH_of_z hω h2 h3 ψ hω₀ hψ h2₀ hr
    (hessC_mem_hessH hω hp2 hp3 (by omega) (by omega) (by omega)) hz

noncomputable abbrev hessPoly (p : ℕ) [Fact p.Prime] : Polynomial (ZMod p) :=
  Polynomial.X ^ 2 + Polynomial.X + 1

theorem hessPoly_natDegree : (hessPoly p).natDegree = 2 := by
  rw [hessPoly]
  compute_degree!

theorem hessPoly_irreducible (hp2 : p % 3 = 2) : Irreducible (hessPoly p) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [hessPoly_natDegree]
    simp
  · intro a ha
    simp only [Polynomial.IsRoot, hessPoly, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one] at ha
    have ha0 : a ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    have ha3 : a ^ 3 = 1 := by linear_combination (a - 1) * ha
    have ha1 : a ≠ 1 := by
      intro h
      rw [h] at ha
      have h3 : ((3 : ℕ) : ZMod p) = 0 := by
        rw [← ha]
        norm_num
      rw [CharP.cast_eq_zero_iff (ZMod p) p] at h3
      have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp h3
      omega
    have hord : orderOf a = 3 := orderOf_eq_prime_iff.mpr ⟨ha3, ha1⟩
    have hdvd := ZMod.orderOf_dvd_card_sub_one ha0
    rw [hord] at hdvd
    omega

theorem hessPhi_mem_hessH_unitary {F : Type} [Field F] [CharP F p]
    (hp23 : 23 ≤ p) (hp2' : p % 3 = 2) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ hessH hω h3 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of hp2
  haveI hirr : Fact (Irreducible (hessPoly p)) := ⟨hessPoly_irreducible hp2'⟩
  have hne0 : hessPoly p ≠ 0 := hirr.out.ne_zero
  let pb := AdjoinRoot.powerBasis hne0
  haveI : Module.Finite (ZMod p) (AdjoinRoot (hessPoly p)) := pb.finite
  haveI : Finite (AdjoinRoot (hessPoly p)) := Module.finite_of_finite (ZMod p)
  haveI : CharP (AdjoinRoot (hessPoly p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (AdjoinRoot (hessPoly p))).injective p
  have hk : Nat.card (AdjoinRoot (hessPoly p)) = (p ^ 1) ^ 2 := by
    rw [← FiniteField.pow_finrank_eq_natCard p, pb.finrank, AdjoinRoot.powerBasis_dim,
      hessPoly_natDegree, pow_one]
  have hk' : Nat.card (AdjoinRoot (hessPoly p)) = p ^ 2 := by rw [hk, pow_one]
  set ω₀ : AdjoinRoot (hessPoly p) := AdjoinRoot.root (hessPoly p) with hω₀def
  have hω₀ : ω₀ ^ 2 + ω₀ + 1 = 0 := by
    have := AdjoinRoot.eval₂_root (hessPoly p)
    simpa [hessPoly] using this
  have hψroot : (hessPoly p).eval₂ (ZMod.castHom (dvd_refl p) F) ω = 0 := by
    simp [hessPoly, hω]
  set ψ : AdjoinRoot (hessPoly p) →+* F := AdjoinRoot.lift (ZMod.castHom (dvd_refl p) F) ω hψroot
  have hψ : ψ ω₀ = ω := AdjoinRoot.lift_root hψroot
  have hne : ∀ q : ℕ, q.Prime → p ≠ q → (q : AdjoinRoot (hessPoly p)) ≠ 0 := fun q hq hpq =>
    prime_ne_zero_of hq hpq
  have h2₀ : (2 : AdjoinRoot (hessPoly p)) ≠ 0 := by exact_mod_cast hne 2 Nat.prime_two hp2
  have h3₀ : (3 : AdjoinRoot (hessPoly p)) ≠ 0 := by exact_mod_cast hne 3 Nat.prime_three hp3
  have h5₀ : (5 : AdjoinRoot (hessPoly p)) ≠ 0 := by
    exact_mod_cast hne 5 Nat.prime_five (by omega)
  have h13₀ : (13 : AdjoinRoot (hessPoly p)) ≠ 0 := by
    exact_mod_cast hne 13 (by norm_num) (by omega)
  have hfrob : ∀ x : AdjoinRoot (hessPoly p), x ^ (p ^ 1) = frobenius _ p x := by
    intro x
    rw [pow_one, frobenius_def]
  have hω₀p : frobenius (AdjoinRoot (hessPoly p)) p ω₀ = ω₀ ^ 2 := by
    rw [frobenius_def]
    have h3' : ω₀ ^ 3 = 1 := by linear_combination (ω₀ - 1) * hω₀
    obtain ⟨t, ht⟩ : ∃ t, p = 3 * t + 2 := ⟨p / 3, by omega⟩
    have hpow : ω₀ ^ p = ω₀ ^ (3 * t + 2) := congrArg (ω₀ ^ ·) ht
    rw [hpow, pow_add, pow_mul, h3', one_pow, one_mul]
  set G := (CFSG.Open.StatedSU 2 (p ^ 1) (AdjoinRoot (hessPoly p))).comap
    (Matrix.SpecialLinearGroup.toGL : SL(2, AdjoinRoot (hessPoly p)) →* _) with hGdef
  have hG : Nat.card G ≤ p * (p ^ 2 - 1) := by
    have h1 := Subgroup.card_comap_dvd_of_injective
      (CFSG.Open.StatedSU 2 (p ^ 1) (AdjoinRoot (hessPoly p))) _
      Matrix.SpecialLinearGroup.toGL_injective
    have h2' := card_statedSU_two (K := AdjoinRoot (hessPoly p)) (r := p) (f := 1) hk
    rw [h2', show p ^ 1 * ((p ^ 1) ^ 2 - 1) = p * (p ^ 2 - 1) by rw [pow_one]] at h1
    exact Nat.le_of_dvd (Nat.mul_pos hp.out.pos (by
      have : 1 < p ^ 2 := by nlinarith
      omega)) h1
  have hmem : ∀ A : SL(2, AdjoinRoot (hessPoly p)),
      ((A : Matrix (Fin 2) (Fin 2) (AdjoinRoot (hessPoly p))).map (frobenius _ p))ᵀ *
        (A : Matrix (Fin 2) (Fin 2) (AdjoinRoot (hessPoly p))) = 1 → A ∈ G := by
    intro A hA
    show Matrix.SpecialLinearGroup.toGL A ∈ CFSG.Open.StatedSU 2 (p ^ 1) (AdjoinRoot (hessPoly p))
    unfold CFSG.Open.StatedSU
    refine Subgroup.subset_closure ⟨A.2, ?_⟩
    have hmap : (A : Matrix (Fin 2) (Fin 2) (AdjoinRoot (hessPoly p))).map (· ^ (p ^ 1)) =
        (A : Matrix (Fin 2) (Fin 2) (AdjoinRoot (hessPoly p))).map (frobenius _ p) := by
      ext i j
      exact hfrob _
    change ((A : Matrix (Fin 2) (Fin 2) (AdjoinRoot (hessPoly p))).map (· ^ (p ^ 1)))ᵀ *
      (A : Matrix (Fin 2) (Fin 2) (AdjoinRoot (hessPoly p))) = 1
    rw [hmap]
    exact hA
  have hrot : ∀ {c s : AdjoinRoot (hessPoly p)} (h : c ^ 2 + s ^ 2 = 1),
      frobenius _ p c = c → frobenius _ p s = s → rot2 h ∈ G := by
    intro c s h hc hs
    apply hmem
    rw [coe_rot2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hc, hs, map_neg] <;>
      first | ring1 | linear_combination h
  have hAG : rotA h5₀ ∈ G := hrot (rotA_sq h5₀)
    (by simp only [map_div₀, map_neg, map_ofNat]) (by simp only [map_div₀, map_ofNat])
  have hBG : rotB h13₀ ∈ G := hrot (rotB_sq h13₀)
    (by simp only [map_div₀, map_neg, map_ofNat]) (by simp only [map_div₀, map_ofNat])
  have hδG : delta2 hω₀ ∈ G := by
    apply hmem
    rw [coe_delta2]
    have h3' : ω₀ ^ 3 = 1 := by linear_combination (ω₀ - 1) * hω₀
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hω₀p, map_pow] <;>
      grind
  have hnG : (-1 : SL(2, AdjoinRoot (hessPoly p))) ∈ G := by
    apply hmem
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, map_neg]
  have hzG : z2 hω₀ h2₀ ∈ G := by
    apply hmem
    rw [coe_z2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, map_div₀, map_neg, map_add, map_mul, map_ofNat,
        hω₀p] <;>
      field_simp <;>
      grind
  obtain ⟨r, hr, hz⟩ := exists_rot_z2_mem_closure hω hk' hp23 ψ hω₀ h2₀ h3₀ h5₀ h13₀ G hG
    hAG hBG hδG hnG hzG
  exact hessPhi_mem_hessH_of_z hω h2 h3 ψ hω₀ hψ h2₀ hr
    (hessC_mem_hessH hω hp2 hp3 (by omega) (by omega) (by omega)) hz

theorem hessPhi_mem_hessH_large {F : Type} [Field F] [CharP F p]
    (hp23 : 23 ≤ p) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0) :
    hessPhi hω h3 ∈ hessH hω h3 := by
  have h3' : p % 3 ≠ 0 := by
    intro h
    have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp this
    omega
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h1 | h2
  · exact hessPhi_mem_hessH_linear hp23 h1 hω h3
  · exact hessPhi_mem_hessH_unitary hp23 h2 hω h3

@[expose] def HessPhiMemClosureSmall : Prop :=
  ∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p],
    (p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) →
    ∀ (ω : F) (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0),
      hessPhi hω h3 ∈ Subgroup.closure
        (Set.range (hessT (F := F)) ∪
          Set.range fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹)

theorem hessPhiMemClosure_of_small (h : HessPhiMemClosureSmall) :
    HessPhiMemClosure := by
  intro F _ p _ _ hp5 ω hω h3
  by_cases hsmall : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19
  · exact h F p hsmall ω hω h3
  · have hp23 : 23 ≤ p := by
      have hpr : p.Prime := Fact.out
      by_contra hlt
      push Not at hlt
      interval_cases p <;> simp_all (config := { decide := true })
    exact hessPhi_mem_hessH_large hp23 hω h3

end CFSG.RankThree.PartTwo.Sec4.Ronan148B
