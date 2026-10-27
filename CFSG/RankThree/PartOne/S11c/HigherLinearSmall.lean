module

public import CFSG.RankThree.PartOne.S11c.CentralWitness
public import CFSG.RankThree.GroupTheory.SteinbergCELinearDefiningWitness
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.GroupTheory CFSG.RankThree.Classical
open CFSG.Assembly.RankThreeEven (localRank)

section Linear

theorem linear_model_cover {Y : Type} [Group Y] {n ℓ f : ℕ}
    (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n ℓ f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = ℓ ^ f ∧
      ∃ φ : Y →* LinearFlag.projectiveSL n K, Function.Surjective φ ∧
        φ.ker ≤ Subgroup.center Y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  let e' : (Y ⧸ Subgroup.center Y) ≃* LinearFlag.projectiveSL n K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  refine ⟨K, inferInstance, inferInstance, hK, e'.toMonoidHom.comp (QuotientGroup.mk' _),
    e'.surjective.comp (QuotientGroup.mk'_surjective _), fun x hx => ?_⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact hx

theorem exists_linear_rect_data {k : Type} [Field k] [Finite k] {p f n : ℕ} (hp : p.Prime)
    (hk : Nat.card k = p ^ f) (hp2 : p ≠ 2) {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m) (hmn : m < n) :
    ∃ (U : Subgroup (LinearFlag.projectiveSL n k)) (z : LinearFlag.projectiveSL n k),
      IsElementaryAbelian p U ∧ Nat.card U = p ^ (f * (m ^ 2 / 4 + (n - m) ^ 2 / 4)) ∧
        z ^ 2 = 1 ∧ z ≠ 1 ∧ ∀ x ∈ U, z * x = x * z := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite k
  have : CharP k p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  set h := m / 2 with hh
  set c := m + (n - m) / 2 with hc
  have hhm : h ≤ m := Nat.div_le_self m 2
  have hmc : m ≤ c := Nat.le_add_right m _
  have hcn : c ≤ n := by omega
  set R := twoBlockRect (n := n) h m c
  have hIJ := disjoint_blockRows_blockCols (n := n) hhm hmc
  have hR := twoBlockRect_subset (n := n) h m c
  have hRcard : R.card = m ^ 2 / 4 + (n - m) ^ 2 / 4 := by
    rw [card_twoBlockRect hhm hmc hcn]
    obtain ⟨j, rfl⟩ := hm
    have h1 : (j + j) / 2 = j := by omega
    have h2 : (j + j) ^ 2 / 4 = j * j := by
      rw [show (j + j) ^ 2 = 4 * (j * j) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h1] at hh
    rw [hh, h2, show j + j - j = j by omega, show c - (j + j) = (n - (j + j)) / 2 by omega,
      show n - c = n - (j + j) - (n - (j + j)) / 2 by omega, half_mul_sub_half]
  have hpv : ∀ v : R → k, p • v = 0 := fun v => funext fun α => by
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hcard : Nat.card (rectUnipotent k hIJ hR) = p ^ (f * R.card) := by
    rw [rectUnipotent,
      ← Nat.card_congr (MonoidHom.ofInjective (proj_comp_rectHom_injective hIJ hR)).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hk, Nat.card_eq_fintype_card,
      Fintype.card_coe, ← pow_mul]
  have hel : IsElemAbelian p (rectUnipotent k hIJ hR) :=
    isElemAbelian_range hpv ((LinearFlag.proj n k).comp (rectHom k hIJ hR))
  have hdet := det_blockSign (k := k) hm hmn.le
  set z₀ : Matrix.SpecialLinearGroup (Fin n) k := ⟨blockSign n m k, hdet⟩
  set z := LinearFlag.proj n k z₀
  have hneg : (-1 : k) ≠ 1 := by
    intro h1
    have h2 : (2 : k) = 0 := by linear_combination -h1
    have h3 : ((2 : ℕ) : k) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff k p] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at h1
    obtain ⟨u, -, hu⟩ := h1
    have h0 := congrFun (congrFun hu ⟨0, by omega⟩) ⟨0, by omega⟩
    have hl := congrFun (congrFun hu ⟨n - 1, by omega⟩) ⟨n - 1, by omega⟩
    simp only [z₀, blockSign, Matrix.diagonal_apply_eq, Matrix.scalar_apply] at h0 hl
    rw [ite_eq_left (show (0 : ℕ) < m by omega)] at h0
    rw [ite_eq_right (show ¬(n - 1 < m) by omega)] at hl
    exact hneg (h0.trans hl.symm)
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have : z₀ * z₀ = 1 := Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact blockSign_mul_self m)
    rw [this, map_one]
  have hzD : ∀ x ∈ rectUnipotent k hIJ hR, Commute z x := by
    rintro _ ⟨c', rfl⟩
    have hcomm : z₀ * rectHom k hIJ hR c' = rectHom k hIJ hR c' * z₀ := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      change blockSign n m k * (1 + rectSum R c'.toAdd) = (1 + rectSum R c'.toAdd) * _
      refine blockSign_mul_rect (fun ij hij => ?_) _
      simp only [R, twoBlockRect, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      omega
    change z * LinearFlag.proj n k (rectHom k hIJ hR c') =
      LinearFlag.proj n k (rectHom k hIJ hR c') * z
    rw [← map_mul, ← map_mul, hcomm]
  refine ⟨rectUnipotent k hIJ hR, z, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).2
    hel, by rw [hcard, hRcard], hz2, hz1, fun x hx => (hzD x hx).eq⟩

theorem linear_witness_absurd {X : Type} [Group X] [Finite X] {Y : Subgroup X} {n ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (φ : Y →* LinearFlag.projectiveSL n K) (hφ : Function.Surjective φ)
    (hZ : φ.ker ≤ Subgroup.center Y) (hrank : localRank ℓ X ≤ 3) {m : ℕ} (hm : Even m)
    (hm2 : 2 ≤ m) (hmn : m < n) (h6 : 6 ≤ f * (m ^ 2 / 4 + (n - m) ^ 2 / 4)) : False := by
  obtain ⟨U, z, hUel, hUcard, hz2, hz1, hzU⟩ := exists_linear_rect_data hℓ hK hℓ2 hm hm2 hmn
  obtain ⟨z', hz'2, hz'1, V, hV, hVel, r, hr, hVcard⟩ :=
    exists_rank_four_of_central_witness φ hφ hZ hℓ hℓ2 hUel hUcard h6 hz1 hz2 hzU
  have := le_localRank_of_rank_four_witness (G := X) (Y := Y) hℓ.one_lt
    ⟨z', hz'2, hz'1, V, hV, hVel, r, hr, hVcard⟩
  omega

theorem linear_small_parameters {X : Type} [Group X] [Finite X] {Y : Subgroup X} {n ℓ f : ℕ}
    (hn : 3 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : StatedClassicalModel (↥Y ⧸ Subgroup.center ↥Y) .PSL n ℓ f)
    (hrank : localRank ℓ X ≤ 3) :
    (n ≤ 4 ∨ (ℓ = 3 ∧ f = 1 ∧ (n = 5 ∨ n = 6))) ∧
      (f ≤ 3 ∨ (ℓ = 3 ∧ n = 3 ∧ (f = 4 ∨ f = 5))) := by
  obtain ⟨K, _, _, hK, φ, hφ, hZ⟩ := linear_model_cover hmod
  have hf : 1 ≤ f := hmod.1.2.1
  rcases Nat.lt_or_ge 3 ℓ with h3 | h3
  ·
    have hw : ∀ m : ℕ, Even m → 2 ≤ m → m < n →
        f * (m ^ 2 / 4 + (n - m) ^ 2 / 4) ≤ 3 := fun m hm hm2 hmn => by
      obtain ⟨-, -, -, -, -, -, -, hr⟩ :=
        linear_defining_prime_central_cover_two_local_rank_witness (G := X) Y hℓ h3 hK φ hφ hZ hm
          hm2 hmn
      exact hr.trans hrank
    refine ⟨Or.inl ?_, Or.inl ?_⟩
    · by_contra hn4
      have := hw 4 (by decide) (by norm_num) (by omega)
      have h4 : 4 ≤ f * (4 ^ 2 / 4 + (n - 4) ^ 2 / 4) :=
        calc 4 = 1 * 4 := by norm_num
          _ ≤ f * (4 ^ 2 / 4 + (n - 4) ^ 2 / 4) :=
            Nat.mul_le_mul hf (by norm_num [Nat.add_div])
      omega
    · by_contra hf3
      have := hw 2 (by decide) le_rfl (by omega)
      have h4 : 4 ≤ f * (2 ^ 2 / 4 + (n - 2) ^ 2 / 4) :=
        calc 4 ≤ f * 1 := by omega
          _ ≤ f * (2 ^ 2 / 4 + (n - 2) ^ 2 / 4) := Nat.mul_le_mul le_rfl (by omega)
      omega
  ·
    have hℓ3 : ℓ = 3 := by
      have := hℓ.two_le
      omega
    subst hℓ3
    have habs := fun (m : ℕ) (hm : Even m) (hm2 : 2 ≤ m) (hmn : m < n)
      (h6 : 6 ≤ f * (m ^ 2 / 4 + (n - m) ^ 2 / 4)) =>
      linear_witness_absurd hℓ hℓ2 hK φ hφ hZ hrank hm hm2 hmn h6
    have h7 : 7 ≤ n → False := fun h7 => by
      refine habs 4 (by decide) (by norm_num) (by omega) ?_
      have h1 : 2 ≤ (n - 4) ^ 2 / 4 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        nlinarith [Nat.sub_add_cancel (show 4 ≤ n by omega)]
      calc 6 = 1 * 6 := by norm_num
        _ ≤ f * (4 ^ 2 / 4 + (n - 4) ^ 2 / 4) := Nat.mul_le_mul hf (by norm_num; omega)
    have h56 : 5 ≤ n → 2 ≤ f → False := fun h5 hf2 => by
      refine habs 4 (by decide) (by norm_num) (by omega) ?_
      calc 6 ≤ 2 * 4 := by norm_num
        _ ≤ f * (4 ^ 2 / 4 + (n - 4) ^ 2 / 4) := Nat.mul_le_mul hf2 (by norm_num [Nat.add_div])
    have h4f : n = 4 → 3 ≤ f → False := fun h4 hf3 => by
      subst h4
      refine habs 2 (by decide) le_rfl (by norm_num) ?_
      calc 6 = 3 * 2 := by norm_num
        _ ≤ f * (2 ^ 2 / 4 + (4 - 2) ^ 2 / 4) := Nat.mul_le_mul hf3 (by norm_num)
    have hf6 : 6 ≤ f → False := fun hf6 => by
      refine habs 2 (by decide) le_rfl (by omega) ?_
      calc 6 ≤ f * 1 := by omega
        _ ≤ f * (2 ^ 2 / 4 + (n - 2) ^ 2 / 4) := Nat.mul_le_mul le_rfl (by omega)
    refine ⟨?_, ?_⟩
    · by_cases hn4 : n ≤ 4
      · exact Or.inl hn4
      · refine Or.inr ⟨rfl, ?_, ?_⟩
        · by_contra hne
          exact h56 (by omega) (by omega)
        · by_contra hne
          exact h7 (by omega)
    · by_cases hf3 : f ≤ 3
      · exact Or.inl hf3
      · refine Or.inr ⟨rfl, ?_, ?_⟩
        · by_contra hne
          have h5 : f ≤ 5 := by
            by_contra h
            exact hf6 (by omega)
          by_cases hn4 : n = 4
          · exact h4f hn4 (by omega)
          · have : 5 ≤ n := by omega
            exact h56 this (by omega)
        · by_contra hne
          have h5 : f ≤ 5 := by
            by_contra h
            exact hf6 (by omega)
          omega

end Linear

end CFSG.RankThree.PartOne
