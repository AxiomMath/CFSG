module

public import CFSG.Quasithin.H13.A6S13821z

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_mem_normalizer_sq_ne_one {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (P : Sylow 2 (SpecialLinearGroup (Fin 2) F)) :
    ∃ d : SpecialLinearGroup (Fin 2) F, d ∈ Subgroup.normalizer
      ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) : Set (SpecialLinearGroup (Fin 2) F)) ∧
      d ^ 2 ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl0, hl1⟩ : ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, Set.ncard_pair (zero_ne_one)] at h1
    omega
  have hdet : (!![l, 0; 0, l⁻¹] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [det_fin_two, hl0]
  let d₀ : SpecialLinearGroup (Fin 2) F := ⟨!![l, 0; 0, l⁻¹], hdet⟩
  have hd₀ : (d₀ : Matrix (Fin 2) (Fin 2) F) = !![l, 0; 0, l⁻¹] := rfl
  have hd₀inv : ((d₀⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![l⁻¹, 0; 0, l] := by
    simp only [Matrix.SpecialLinearGroup.coe_inv, hd₀, adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hconjU : ∀ u ∈ unitriangular 2 F, d₀ * u * d₀⁻¹ ∈ unitriangular 2 F := by
    intro u hu
    obtain ⟨hlow, hdiag⟩ := hu
    have h10 := hlow 1 0 (by decide)
    have h00 := hdiag 0
    have h11 := hdiag 1
    have hprod : ((d₀ * u * d₀⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![l, 0; 0, l⁻¹] * (u : Matrix (Fin 2) (Fin 2) F) * !![l⁻¹, 0; 0, l] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hd₀, hd₀inv]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hi : i = 1 := by omega
      have hj : j = 0 := by omega
      subst hi hj
      rw [hprod]
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h10]
    · rw [hprod]
      fin_cases i <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h10, h00, h11, hl0]
  have hd₀2 : d₀ ^ 2 ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    have hsq : ((d₀ ^ 2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![l, 0; 0, l⁻¹] * !![l, 0; 0, l⁻¹] := by
      rw [sq, Matrix.SpecialLinearGroup.coe_mul, hd₀]
    simp only [hsq, Matrix.SpecialLinearGroup.coe_one] at h1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h1
    have h3 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h2 : (l + 1) * (l + 1) = 0 := by
      linear_combination h1 + l * h3 + h3
    have h4 : l + 1 = 0 := mul_self_eq_zero.mp h2
    apply hl1
    linear_combination h4 - h3
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := 2) (by norm_num)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) F) P₀ P
  refine ⟨h * d₀ * h⁻¹, ?_, ?_⟩
  · have hmem : ∀ x, x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ↔
        h⁻¹ * x * h ∈ unitriangular 2 F := by
      intro x
      rw [← hh, Sylow.coe_subgroup_smul, ← hP₀, Subgroup.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have e1 : h⁻¹ * ((MulAut.conj h) • y) * h = y := by
          rw [MulAut.smul_def, MulAut.conj_apply]; group
        rw [e1]; exact hy
      · intro hx
        refine ⟨h⁻¹ * x * h, hx, ?_⟩
        rw [MulAut.smul_def, MulAut.conj_apply]; group
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe] at hx ⊢
    rw [hmem] at hx ⊢
    have e : h⁻¹ * (h * d₀ * h⁻¹ * x * (h * d₀ * h⁻¹)⁻¹) * h = d₀ * (h⁻¹ * x * h) * d₀⁻¹ := by
      group
    rw [e]
    exact hconjU _ hx
  · intro h2
    apply hd₀2
    have e : (h * d₀ * h⁻¹) ^ 2 = h * d₀ ^ 2 * h⁻¹ := by
      rw [conj_pow]
    rw [e] at h2
    have h3 := congrArg (fun x => h⁻¹ * x * h) h2
    simpa [mul_assoc] using h3

theorem exists_borel_sq_ne_one {G : Type} [Group G] [Finite G] {K T₀ : Subgroup G}
    (hsyl : IsSylowTwoOf T₀ K) {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F] [Finite F]
    (hFn : Nat.card F = 2 ^ n)
    (eK : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* SpecialLinearGroup (Fin 2) F) :
    ∃ k : ↥K, (k : G) ∈ Subgroup.normalizer (T₀ : Set G) ∧
      (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 2 ≠ 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hFn])
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hsyl' : IsSylowTwoOf (T₀.subgroupOf K) (⊤ : Subgroup ↥K) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hsyl.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hsyl.1).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hsyl.1).injective
    · have e : ((T₀.subgroupOf K).subgroupOf (⊤ : Subgroup ↥K)).index =
          (T₀.subgroupOf K).index :=
        Subgroup.index_comap_of_surjective (T₀.subgroupOf K) (f := (⊤ : Subgroup ↥K).subtype)
          (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
      rw [e]
      exact hsyl.2.2
  have hsurj : Function.Surjective (eK.toMonoidHom.comp π) := fun y => by
    obtain ⟨x, hx⟩ := hπs (eK.symm y)
    exact ⟨x, by simp [hx]⟩
  have hP := isSylowTwoOf_map_top hsurj hsyl'
  · set P := (T₀.subgroupOf K).map (eK.toMonoidHom.comp π) with hPdef
    have hidx : ¬ 2 ∣ P.index := by
      have h2 : ¬ 2 ∣ P.relIndex ⊤ := hP.2.2
      rwa [Subgroup.relIndex_top_right] at h2
    obtain ⟨d, hdN, hd2⟩ := exists_mem_normalizer_sq_ne_one hF4 (hP.2.1.toSylow hidx)
    obtain ⟨k, hk⟩ := hπs (eK.symm d)
    have hOT : CFSG.pCore 2 ↥K ≤ T₀.subgroupOf K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hx' : (x : G) ∈ pCoreOf 2 K := by
        refine ⟨x, ?_, rfl⟩
        assumption
      exact F7.isSylowTwoOf_pCoreOf_le hsyl hx'
    refine ⟨k, ?_, ?_⟩
    · refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      have htK : t ∈ K := hsyl.1 ht
      have h1 : (eK.toMonoidHom.comp π) (k * ⟨t, htK⟩ * k⁻¹) ∈ P := by
        rw [map_mul, map_mul, map_inv]
        have hk' : (eK.toMonoidHom.comp π) k = d := by
          show eK (π k) = d
          rw [hk, MulEquiv.apply_symm_apply]
        rw [hk']
        have hdN' := hdN
        rw [Subgroup.mem_normalizer_iff] at hdN'
        exact (hdN' _).mp ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      obtain ⟨y, hy, hyeq⟩ := h1
      have hyeq' : π y = π (k * ⟨t, htK⟩ * k⁻¹) := eK.injective hyeq
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyeq'
      have h2 : y * (y⁻¹ * (k * ⟨t, htK⟩ * k⁻¹)) ∈ T₀.subgroupOf K :=
        (T₀.subgroupOf K).mul_mem hy (hOT hyeq')
      rw [mul_inv_cancel_left, Subgroup.mem_subgroupOf] at h2
      simpa using h2
    · intro h
      apply hd2
      have h1 : eK.symm d ^ 2 = 1 := by rw [← hk]; exact h
      have h2 := congrArg eK h1
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at h2

end CFSG.Quasithin.H13.A6.A6S20
