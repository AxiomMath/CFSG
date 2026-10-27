module

public import CFSG.RankThree.PartOne.U5K.Pkg.Fix
public import CFSG.RankThree.PartOne.S13K.KFLiftRows
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartTwo.Sec21.Item22L2

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSU projSL)

theorem exists_orderOf_of_model_psl_two {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (h : StatedClassicalModel X .PSL 2 2 f) : ∃ y : X, orderOf y = 2 ^ f - 1 := by
  obtain ⟨e⟩ := projSL_of_statedClassicalModel h
  have hch : CharP (GaloisField 2 f) 2 := inferInstance
  obtain ⟨t, ht⟩ := CTP.exists_sl2_orderOf_eq (L := GaloisField 2 f)
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨((e.trans (CFSG.RankThree.PartTwo.Sec21.projSLTwoEquivSL (GaloisField 2 f))).symm) t,
    ?_⟩
  rw [MulEquiv.orderOf_eq, ht, hcard]

theorem U5Act_mem_inndiag_of_centralizes {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    (hf5 : 5 ∣ 2 ^ f + 1) {I : Subgroup G} (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)
    {K : Subgroup G} (hKI : K ≤ I) (hK : StatedClassicalModel ↥K .PSL 2 2 f) {x : G}
    (hx : x ∈ Subgroup.normalizer (I : Set G)) (hxK : ∀ k ∈ K, x * k = k * x)
    (hx5 : x ^ 5 = 1) : U5Act I e ⟨x, hx⟩ ∈ U5Inndiag f := by
  obtain ⟨y, hy⟩ := exists_orderOf_of_model_psl_two hf hK
  have hZ : Subgroup.center ↥K = ⊥ := (S13K.isQuasisimple_and_center_of_model_psl_two hK).2
  let ρ : ↥K →* projSU 5 2 f := e.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center ↥I)).comp (Subgroup.inclusion hKI))
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : (QuotientGroup.mk (Subgroup.inclusion hKI k) : ↥I ⧸ Subgroup.center ↥I) = 1 := by
      apply e.injective
      rw [map_one]
      exact hk
    have h2 : Subgroup.inclusion hKI k ∈ Subgroup.center ↥I := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := Subgroup.mem_center_iff.1 h2 (Subgroup.inclusion hKI z)
      exact Subgroup.inclusion_injective hKI (by rw [map_mul, map_mul]; exact this)
    rw [hZ] at h3
    exact Subgroup.mem_bot.1 h3
  have hordρ : orderOf (ρ y) = 2 ^ f - 1 := by rw [orderOf_injective ρ hρ y, hy]
  have hα5 : (U5Act I e ⟨x, hx⟩) ^ 5 = 1 := by
    have : (⟨x, hx⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ 5 = 1 := Subtype.ext hx5
    rw [← map_pow, this, map_one]
  have hαy : (U5Act I e ⟨x, hx⟩) (ρ y) = ρ y := by
    have h1 := U5Act_apply I e ⟨x, hx⟩ (Subgroup.inclusion hKI y)
    have h2 : (I.normalizerMonoidHom ⟨x, hx⟩) (Subgroup.inclusion hKI y) =
        Subgroup.inclusion hKI y := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact mul_inv_eq_iff_eq_mul.mpr (hxK y y.2)
    rw [h2] at h1
    exact h1
  exact u5_inndiag_of_fix hf hf5 hα5 hordρ hαy

end CFSG.RankThree.PartOne.U5K.Pkg
