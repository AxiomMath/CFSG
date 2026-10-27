module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModelMinus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModel
public import CFSG.RankThree.PartOne.LIT.RankMatrix

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped Matrix

namespace OrthRest

section Outer

variable {G : Type*} [Group G]

theorem mem_range_conj_of_pow {N p : ℕ} (hpN : Nat.Coprime p N)
    (h : ∀ α : MulAut G, ∃ ι ∈ (MulAut.conj : G →* MulAut G).range, ∃ c : MulAut G,
      c ^ N = 1 ∧ α = ι * c)
    {α : MulAut G} (hα : α ^ p = 1) : α ∈ (MulAut.conj : G →* MulAut G).range := by
  obtain ⟨ι, hι, c, hc, rfl⟩ := h α
  set Inn := (MulAut.conj : G →* MulAut G).range with hInn
  have hq : ((ι * c : MulAut G) : MulAut G ⧸ Inn) = (c : MulAut G ⧸ Inn) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff ι).mpr hι, one_mul]
  have h1 : ((ι * c : MulAut G) : MulAut G ⧸ Inn) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have h2 : ((ι * c : MulAut G) : MulAut G ⧸ Inn) ^ N = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, hc, QuotientGroup.mk_one]
  have h3 : orderOf ((ι * c : MulAut G) : MulAut G ⧸ Inn) = 1 :=
    Nat.eq_one_of_dvd_coprimes hpN (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem mem_range_conj_of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) {p : ℕ}
    (h : ∀ β : MulAut H, β ^ p = 1 → β ∈ (MulAut.conj : H →* MulAut H).range)
    {α : MulAut G} (hα : α ^ p = 1) : α ∈ (MulAut.conj : G →* MulAut G).range := by
  have hβ : (MulAut.congr e α) ^ p = 1 := by rw [← map_pow, hα, map_one]
  obtain ⟨g, hg⟩ := h _ hβ
  refine ⟨e.symm g, ?_⟩
  apply (MulAut.congr e).injective
  rw [← hg]
  ext x
  change e (e.symm g * e.symm x * (e.symm g)⁻¹) = g * x * g⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end Outer

section Rank

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem card_le_of_isometry (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (GL ι K)) (hiso : ∀ g ∈ E, ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ p = 1) :
    Nat.card E ≤ p ^ (Fintype.card ι / 2) := by
  have : Finite (GL ι K) :=
    Finite.of_injective (fun u : GL ι K => (u : Matrix ι ι K)) Units.val_injective
  set B := QuadraticMap.polarBilin Q with hB
  set J := LinearMap.BilinForm.toMatrix' B with hJ
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have hJB : ∀ v w : ι → K, v ⬝ᵥ (J *ᵥ w) = B v w := by
    intro v w
    rw [← Matrix.toBilin'_apply', hJ, Matrix.toBilin'_toMatrix']
  refine CFSG.RankThree.PartOne.LIT.card_le_pow_half_of_form_gl hp hpK J ?_ ?_ E hcomm hexp ?_
  · have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Pi.basisFun K ι)).mp hQ
    rwa [LinearMap.BilinForm.toMatrix_basisFun] at h
  · intro v
    rw [hJB, hB, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  · intro g hg
    have hcomp : LinearMap.BilinForm.comp B (Matrix.toLin' (g : Matrix ι ι K))
        (Matrix.toLin' (g : Matrix ι ι K)) = B := by
      refine LinearMap.ext₂ fun v w => ?_
      rw [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hB,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
        QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hiso g hg, hiso g hg,
        hiso g hg]
    have h := LinearMap.BilinForm.toMatrix'_comp B (Matrix.toLin' (g : Matrix ι ι K))
      (Matrix.toLin' (g : Matrix ι ι K))
    rw [hcomp, LinearMap.toMatrix'_toLin'] at h
    exact h.symm

theorem card_le_of_proj (Q : QuadraticForm K (ι → K)) {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hsc : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q₀) = ⊥) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (E : Subgroup (LargeEvenProj (LargeEvenOmega Q₀))) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (Fintype.card ι / 2) := by
  set f : LargeEvenProj (LargeEvenOmega Q₀) →* GL ι K :=
    (LargeEvenOmega Q₀).subtype.comp (TableBOrth.projMkEquiv hsc).symm.toMonoidHom with hf
  have hfi : Function.Injective f :=
    (LargeEvenOmega Q₀).subtype_injective.comp (TableBOrth.projMkEquiv hsc).symm.injective
  rw [← Subgroup.card_map_of_injective hfi]
  refine card_le_of_isometry Q hQ hp hp2 _ ?_ ?_ ?_
  · rintro _ ⟨r, -, rfl⟩ v
    have h := TableBOrth.isometry_of_mem_orthGroup
      (TableBOrth.omega_le_orth Q₀ ((TableBOrth.projMkEquiv hsc).symm r).2) v
    rw [hQ₀]
    exact h
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

end Rank

section Vacuous

variable {p r : ℕ} {R : Type} [Group R]

theorem conj_injective (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgZ : g ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut R => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  rw [hZ, Subgroup.mem_bot] at hgZ
  exact hgZ

theorem ggBstarBoundInnR_of_inner (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hinn : ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ (MulAut.conj : R →* MulAut R).range)
    (hcard : ∀ E : Subgroup R, IsElemAbelian p E → Nat.card E ≤ p ^ (r + 1))
    (I : Set (MulAut R)) : GGBstarBoundInnR p r R I := by
  intro Eb Eh _ _ hr _ _ _ hEh hcardh
  exfalso
  have hinj := conj_injective hZ
  have hsub : Eh ≤ (MulAut.conj : R →* MulAut R).range := fun φ hφ => hinn φ (hEh.2 φ hφ)
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hcE : Nat.card E = Nat.card Eh := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hsub]
    rw [Subgroup.card_map_of_injective hinj]
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · show MulAut.conj ((a : R) * b) = MulAut.conj ((b : R) * a)
      rw [map_mul, map_mul, TableB.IsElemAbelian.comm hEh a.2 b.2]
    · rw [map_pow, hEh.2 _ hx, map_one]
  have h1 := hcard E hEab
  have h2 : p ^ (r + 2) ≤ Nat.card Eh := by
    calc p ^ (r + 2) = p ^ 2 * p ^ r := by ring
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcardh
  have h3 : p ^ (r + 1) < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

end Vacuous

section Recipes

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m n p : ℕ}

theorem mem_range_conj_minus {b c : K} (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2 ^ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    {φ : MulAut (RMinus K m b c)} (hφ : φ ^ p = 1) :
    φ ∈ (MulAut.conj : RMinus K m b c →* MulAut (RMinus K m b c)).range := by
  have hn4 : 4 ≤ m + 1 := by omega
  refine mem_range_conj_of_mulEquiv (RecipeFieldOmega.minusEquiv hn4 b c) (fun β hβ => ?_) hφ
  refine mem_range_conj_of_pow (N := 2 * n) (Nat.Coprime.mul_right
    ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn))
    (fun α => ?_) hβ
  obtain ⟨ι, hι, k, rfl⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hK α
  refine ⟨ι, hι, _, ?_, rfl⟩
  rw [← pow_mul, pow_mul', AutOm.frobAut_pow_two_mul hn4 hirr hK, one_pow]

omit [CharP K 2] in
theorem eq_zero_or_eq_one_of_card_two (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have h2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have hx : x ^ 2 = x := by
    have := FiniteField.pow_card x
    rwa [h2] at this
  have h0 : x * (x - 1) = 0 := by
    rw [mul_sub, mul_one, ← sq, hx, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem mem_range_conj_plus_two (hm : 5 ≤ m) (hK : Nat.card K = 2)
    {φ : MulAut (RPlus K m)} (hφ : φ ^ 3 = 1) :
    φ ∈ (MulAut.conj : RPlus K m →* MulAut (RPlus K m)).range := by
  refine mem_range_conj_of_mulEquiv (RecipeFieldOmega.plusEquiv (K := K) (by omega : 1 ≤ m))
    (fun β hβ => ?_) hφ
  refine mem_range_conj_of_pow (N := 2) (by norm_num) (fun α => ?_) hβ
  obtain ⟨ι, hι, c, hc, rfl⟩ := AutOm.exists_inner_mul_plusCompl hm α
  refine ⟨ι, hι, c, ?_, rfl⟩
  have hσ : ∀ σ : K ≃+* K, σ = 1 := fun σ => RingEquiv.ext fun x => by
    rcases eq_zero_or_eq_one_of_card_two hK x with rfl | rfl
    · rw [map_zero]
      rfl
    · rw [map_one]
      rfl
  obtain ⟨σ, rfl | rfl⟩ := hc
  · rw [hσ σ, map_one, one_pow]
  · rw [hσ σ, map_one, mul_one, sq, AutOm.plusRefl_mul_self]

theorem card_le_minus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime)
    (hp2 : p ≠ 2) (E : Subgroup (RMinus K m b c)) (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (m + 1) := by
  have h := card_le_of_proj (TableBOrth.qMinusForm K m b c) (TableBOrth.coe_qMinusForm m b c)
    (TableBOrth.nondegenerate_qMinusForm m hirr)
    (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot b c) hp hp2 E hE
  have hc : Fintype.card (LargeEvenMinusIdx m) / 2 = m + 1 := by
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    omega
  rwa [hc] at h

theorem card_le_plus (hm : 1 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (E : Subgroup (RPlus K m))
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ m := by
  have h := card_le_of_proj (TableBOrth.qPlusForm K m) (TableBOrth.coe_qPlusForm m)
    (TableBOrth.nondegenerate_qPlusForm m) (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot hm)
    hp hp2 E hE
  have hc : Fintype.card (Fin m ⊕ Fin m) / 2 = m := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rwa [hc] at h

end Recipes

end OrthRest

@[expose] def GGOrthRestBstarRestInput : Prop :=
  (∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 3 ≤ m →
    p.Prime → p ∣ 2 ^ n + 1 → p ∣ n → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      GGBstarBoundInnR p m (OrthRest.RMinus K m b c) (LargeEvenInnSet _)) ∧
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGBstarBoundInnR 3 3 (OrthRest.RPlus K 4) (LargeEvenInnSet _)

theorem ggOrthRestBstarInput_of_rest (hZ : GGOrthRestCenterInput)
    (h : GGOrthRestBstarRestInput) : GGOrthRestBstarInput := by
  refine ⟨fun K _ _ n m p b c hK hm hp hpn hbc => ?_, fun K _ _ m hK hm => ?_⟩
  · by_cases hpd : p ∣ n
    · exact h.1 K n m p b c hK hm hp hpn hpd hbc
    · have hn : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · have h1 : 1 < Nat.card K := Finite.one_lt_card
          rw [hK, h0, pow_zero] at h1
          omega
        · exact h0
      have : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
          hn hK
      have hp2 : p ≠ 2 := by
        rintro rfl
        have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
        omega
      exact OrthRest.ggBstarBoundInnR_of_inner hp (hZ.1 K n m p b c hK hm hp hpn hbc).1
        (fun _ hφ => OrthRest.mem_range_conj_minus hm hbc hK hp hp2 hpd hφ)
        (fun E hE => OrthRest.card_le_minus hbc hp hp2 E hE) _
  · rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | hm5
    · exact h.2 K hK
    · have : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
          le_rfl (hK.trans (pow_one 2).symm)
      exact OrthRest.ggBstarBoundInnR_of_inner Nat.prime_three (hZ.2 K m hK hm).1
        (fun _ hφ => OrthRest.mem_range_conj_plus_two hm5 hK hφ)
        (fun E hE => by
          have h1 := OrthRest.card_le_plus (by omega) Nat.prime_three (by norm_num) E hE
          rwa [show m - 1 + 1 = m by omega]) _

end CFSG.StandardType
