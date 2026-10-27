module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
import CFSG.LocalAnalysis.UniquenessCase.UC22S218L3
import CFSG.RankThree.PartTwo.Sec4.Item413AutL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Quasithin.H13.KG4413 (dg3 coe_dg3)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot autCenterQuot_injective_of_perfect)
open CFSG.RankThree.PartTwo.Sec4
  (card_le_27_of_mulAut_projectiveSL_three card_le_of_mulEquiv_mulAut pRank_three_le_of_card_le
    three_ne_zero_of_card)

section Cover

variable {K : Type} [Field K]

private theorem dg3_mem_center_aux {t : Kˣ × Kˣ}
    (h : dg3 t ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) :
    t.1 = t.2 ∧ t.1 ^ 3 = 1 := by
  obtain ⟨c, hc, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have h0 : c = (t.1 : K) := by
    simpa [coe_dg3, Matrix.scalar_apply] using congrFun (congrFun hA 0) 0
  have h1 : c = (t.2 : K) := by
    simpa [coe_dg3, Matrix.scalar_apply] using congrFun (congrFun hA 1) 1
  refine ⟨Units.ext (h0.symm.trans h1), Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, ← h0]
  simpa using hc

theorem uc22s218_l3_cover_pair_data {X : Type} [Group X] [Finite K]
    (α : Matrix.SpecialLinearGroup (Fin 3) K →* X) (hα : Function.Surjective α)
    (hker : α.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))
    {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hrK : r ∣ Nat.card K - 1) (h3K : 3 ∣ Nat.card K - 1) :
    ∃ (E₀ : Subgroup X) (y : X), IsElemAbelian r E₀ ∧ Nat.card E₀ = r ^ 2 ∧ orderOf y = 3 ∧
      (∀ e ∈ E₀, y * e = e * y) ∧ ∃ w : X, w * y ≠ y * w := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
    (by rw [Nat.card_units]; exact hrK)
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [Nat.card_units]; exact h3K)
  have hcard : Nat.card (Subgroup.zpowers ζ) = r := by rw [Nat.card_zpowers, hζ]
  have hpow : ∀ x : Subgroup.zpowers ζ, x ^ r = 1 := fun x => by
    rw [← hcard]
    exact pow_card_eq_one'
  let f : Subgroup.zpowers ζ × Subgroup.zpowers ζ →* X :=
    α.comp (dg3.comp ((Subgroup.zpowers ζ).subtype.prodMap (Subgroup.zpowers ζ).subtype))
  have hf : ∀ a b : Subgroup.zpowers ζ, f (a, b) = α (dg3 ((a : Kˣ), (b : Kˣ))) := fun _ _ => rfl
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [hf] at hab
    obtain ⟨hab1, hab2⟩ := dg3_mem_center_aux (hker (MonoidHom.mem_ker.2 hab))
    have ha : (a : Kˣ) = 1 := by
      have hr' : (a : Kˣ) ^ r = 1 := by simpa using congrArg Subtype.val (hpow a)
      have hd : orderOf (a : Kˣ) ∣ Nat.gcd r 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hr') (orderOf_dvd_of_pow_eq_one hab2)
      rw [((Nat.coprime_primes hr Nat.prime_three).2 hr3).gcd_eq_one] at hd
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
    exact Prod.ext (Subtype.ext ha) (Subtype.ext (hab1.symm.trans ha))
  have hP : IsElemAbelian r (⊤ : Subgroup (Subgroup.zpowers ζ × Subgroup.zpowers ζ)) :=
    ⟨inferInstance, fun x _ => Prod.ext (hpow x.1) (hpow x.2)⟩
  have hω3 : ω ^ 3 = 1 := by simpa [hω] using pow_orderOf_eq_one ω
  have hy3 : α (dg3 (ω, 1)) ^ 3 = 1 := by
    have h : ((ω, 1) : Kˣ × Kˣ) ^ 3 = 1 := Prod.ext hω3 (one_pow 3)
    rw [← map_pow, ← map_pow, h, map_one, map_one]
  have hycen : α (dg3 (ω, 1)) ∉ Subgroup.center X := by
    intro hyc
    have hmem : dg3 (ω, 1) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      rw [← CFSG.LocalCores.comap_center_eq_of_perfect
        (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)) α hα hker]
      exact hyc
    have h1 : orderOf ω = 1 := orderOf_eq_one_iff.2 (dg3_mem_center_aux hmem).1
    rw [hω] at h1
    exact absurd h1 (by norm_num)
  refine ⟨f.range, α (dg3 (ω, 1)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact hP.map f
  · rw [Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv.symm, Nat.card_prod, hcard, sq]
  · refine (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hy3) |>.resolve_left ?_
    intro h1
    exact hycen (orderOf_eq_one_iff.1 h1 ▸ one_mem _)
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    rw [hf, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      mul_comm ((ω, 1) : Kˣ × Kˣ) ((a : Kˣ), (b : Kˣ))]
  · by_contra h
    exact hycen (Subgroup.mem_center_iff.2 fun w => by_contra fun hw => h ⟨w, hw⟩)

end Cover

theorem uc22s218_l3_pRank_mulAut_le_three_of_quasisimple {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hX : IsL3 (X ⧸ Subgroup.center X) n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ 3 := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := uc22s218_l3_exists_model hX
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card Nat.prime_two (by norm_num) hK
  have : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine pRank_three_le_of_card_le fun B hB => ?_
  have h := card_le_of_mulEquiv_mulAut e
    (fun B' hB' => card_le_27_of_mulAut_projectiveSL_three h3 B' hB')
    (B.map (autCenterQuot X)) (hB.map _)
  rwa [Subgroup.card_map_of_injective (autCenterQuot_injective_of_perfect hq.1)] at h

end CFSG.LocalAnalysis.UniquenessCase.UC22
