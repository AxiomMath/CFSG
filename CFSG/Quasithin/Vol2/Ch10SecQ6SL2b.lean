module

public import CFSG.Quasithin.Vol2.Ch10SecQ6SL2a

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix CFSG.RankThree.PartOne.KCRootAxis CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
noncomputable abbrev innSL : Subgroup (MulAut (SpecialLinearGroup (Fin 2) K)) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner (SpecialLinearGroup (Fin 2) K)

theorem eq_one_of_sq_eq_one_char_two {c : K} (h : c ^ 2 = 1) : c = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)

theorem conj_sl2_injective :
    Function.Injective (MulAut.conj : SpecialLinearGroup (Fin 2) K →* MulAut _) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro M hM
  rw [MonoidHom.mem_ker] at hM
  have hc : M ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro N
    have h1 := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin 2) K) => φ N) hM
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc N * M = M * N * M⁻¹ * M := by rw [h1]
      _ = M * N := by group
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center] at hc
  obtain ⟨c, hc2, hcM⟩ := hc
  have h1 : (c : K) = 1 := eq_one_of_sq_eq_one_char_two (by
    rw [← Units.val_pow_eq_pow_val, hc2, Units.val_one])
  rw [Subgroup.mem_bot]
  ext i j
  rw [hcM, h1]
  simp [scalar_apply, one_apply]

theorem conj_apply_aut {G : Type*} [Group G] (φ : MulAut G) (M : G) :
    MulAut.conj (φ M) = φ * MulAut.conj M * φ⁻¹ := by
  ext N
  simp [MulAut.conj_apply, MulAut.mul_apply]

omit [CharP K 2] in
theorem card_le_of_isPGroup [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {D : Subgroup (SpecialLinearGroup (Fin 2) K)} (hD : IsPGroup 2 D) :
    Nat.card D ≤ Nat.card K := by
  obtain ⟨g, hg⟩ := exists_conj_mem_uSub hK hn hD
  rw [← card_uSub (K := K)]
  refine Nat.card_le_card_of_injective (fun d : D => (⟨g * d * g⁻¹, hg d d.2⟩ : uSub K))
    fun a b h => Subtype.ext ?_
  have h1 := congrArg Subtype.val h
  simpa using h1

theorem card_le_half [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {φ : MulAut (SpecialLinearGroup (Fin 2) K)} (hφ : φ ∉ innSL K)
    {D : Subgroup (SpecialLinearGroup (Fin 2) K)} (hD : IsPGroup 2 D) (hD1 : D ≠ ⊥)
    (hfix : ∀ M ∈ D, φ M = M) : 2 * Nat.card D ≤ Nat.card K := by
  obtain ⟨g, hg⟩ := exists_conj_mem_uSub hK hn hD
  set φ' := MulAut.conj g * φ * MulAut.conj g⁻¹ with hφ'def
  have hφ' : φ' ∉ innSL K := by
    intro h
    apply hφ
    obtain ⟨N, hN⟩ := h
    refine ⟨g⁻¹ * N * g, ?_⟩
    rw [map_mul, map_mul, hN, hφ'def, map_inv]
    group
  have hfix' : ∀ d ∈ D, φ' (g * d * g⁻¹) = g * d * g⁻¹ := by
    intro d hd
    rw [hφ'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group, hfix d hd]
  obtain ⟨M, σ, hMσ⟩ := exists_conj_mul_slFieldAut φ'
  have hσ : σ ≠ 1 := by
    rintro rfl
    apply hφ'
    rw [hMσ, map_one, mul_one]
    exact ⟨M, rfl⟩
  have hφ'ut : ∀ t, φ' (ut t) = M * ut (σ t) * M⁻¹ := by
    intro t
    rw [hMσ, MulAut.mul_apply, slFieldAut_ut, MulAut.conj_apply]
  obtain ⟨⟨d0, hd0⟩, hd01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hD1
  obtain ⟨t0, ht0⟩ := hg d0 hd0
  have ht00 : t0 ≠ 0 := by
    rintro rfl
    apply hd01
    rw [ut_zero] at ht0
    have h1 : d0 = 1 := by
      calc d0 = g⁻¹ * (g * d0 * g⁻¹) * g := by group
        _ = 1 := by rw [ht0, mul_one, inv_mul_cancel]
    exact Subtype.ext h1
  have hM10 : (M : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have h1 := hfix' d0 hd0
    rw [ht0, hφ'ut] at h1
    have h2 : ((M * ut (σ t0) * M⁻¹ : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 1 0 = (ut t0 : SpecialLinearGroup (Fin 2) K).1 1 0 :=
      congrArg (fun x : SpecialLinearGroup (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K) 1 0) h1
    rw [conj_ut_entry] at h2
    have h3 : (ut t0 : SpecialLinearGroup (Fin 2) K).1 1 0 = 0 := by simp [ut]
    have hσt0 : σ t0 ≠ 0 := fun h => ht00 (σ.injective (h.trans (map_zero σ).symm))
    have h4 : ((M : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 = 0 := by
      have h5 : -((M : Matrix (Fin 2) (Fin 2) K) 1 0) ^ 2 * σ t0 = 0 := h2.trans h3
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact neg_eq_zero.mp h6
      · exact absurd h6 hσt0
    exact pow_eq_zero_iff (by norm_num) |>.mp h4
  set a := (M : Matrix (Fin 2) (Fin 2) K) 0 0 with ha
  let Fx : AddSubgroup K :=
    { carrier := {t | a ^ 2 * σ t = t}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, map_add, mul_add] at hx hy ⊢
        rw [hx, hy]
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq, map_neg, mul_neg] at hx ⊢
        rw [hx] }
  have hFx : Fx ≠ ⊤ := by
    intro h
    have h1 : (1 : K) ∈ Fx := h ▸ AddSubgroup.mem_top 1
    have ha2 : a ^ 2 = 1 := by
      have h3 : a ^ 2 * σ 1 = 1 := h1
      rwa [map_one, mul_one] at h3
    apply hσ
    ext t
    have h2 : t ∈ Fx := h ▸ AddSubgroup.mem_top t
    have h3 : a ^ 2 * σ t = t := h2
    rw [ha2, one_mul] at h3
    exact h3
  have hmem : ∀ d ∈ D, ((g * d * g⁻¹ : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 1 ∈ Fx := by
    intro d hd
    obtain ⟨t, ht⟩ := hg d hd
    have h1 := hfix' d hd
    rw [ht, hφ'ut, conj_ut_of hM10] at h1
    rw [ht]
    exact ut_injective h1
  have hinj : Function.Injective fun d : D => (⟨_, hmem d d.2⟩ : Fx) := by
    intro d d' h
    have h1 := congrArg Subtype.val h
    obtain ⟨t, ht⟩ := hg d d.2
    obtain ⟨t', ht'⟩ := hg d' d'.2
    simp only at h1
    rw [ht, ht'] at h1
    have h2 : t = t' := by simpa [ut] using h1
    apply Subtype.ext
    have h3 : g * (d : SpecialLinearGroup (Fin 2) K) * g⁻¹ = g * d' * g⁻¹ := by
      rw [ht, ht', h2]
    simpa using h3
  have hcard := Nat.card_le_card_of_injective _ hinj
  have hidx := Fx.card_mul_index
  have hidx2 : 2 ≤ Fx.index := by
    rcases Nat.lt_or_ge Fx.index 2 with h | h
    · exfalso
      interval_cases h1 : Fx.index
      · exact Fx.index_ne_zero_of_finite h1
      · exact hFx (AddSubgroup.index_eq_one.mp h1)
    · exact h
  calc 2 * Nat.card D ≤ 2 * Nat.card Fx := by omega
    _ ≤ Fx.index * Nat.card Fx := Nat.mul_le_mul_right _ hidx2
    _ = Nat.card K := by rw [mul_comm]; exact hidx

theorem card_le_of_elem_aut [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {F : Subgroup (MulAut (SpecialLinearGroup (Fin 2) K))}
    (hc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (h2 : ∀ a ∈ F, a * a = 1) :
    Nat.card F ≤ Nat.card K := by
  let D : Subgroup (SpecialLinearGroup (Fin 2) K) := F.comap MulAut.conj
  have hD2 : IsPGroup 2 D := fun M => ⟨1, by
    rw [pow_one, sq]
    apply Subtype.ext
    apply conj_sl2_injective
    change MulAut.conj ((M : SpecialLinearGroup (Fin 2) K) * M) = MulAut.conj 1
    rw [map_mul, map_one]
    exact h2 _ M.2⟩
  have hDq : Nat.card D ≤ Nat.card K := card_le_of_isPGroup hK hn hD2
  let f : F →* Outer (SpecialLinearGroup (Fin 2) K) :=
    (QuotientGroup.mk' (innSL K)).comp F.subtype
  have hF : Nat.card F = Nat.card f.range * Nat.card f.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hker : Nat.card f.ker ≤ Nat.card D := by
    refine Nat.card_le_card_of_surjective
      (fun M : D => (⟨⟨MulAut.conj (M : SpecialLinearGroup (Fin 2) K), M.2⟩,
        (QuotientGroup.eq_one_iff _).mpr ⟨M, rfl⟩⟩ : f.ker)) ?_
    rintro ⟨φ, hφ⟩
    obtain ⟨M, hM⟩ := (QuotientGroup.eq_one_iff
      ((φ : F) : MulAut (SpecialLinearGroup (Fin 2) K))).mp (MonoidHom.mem_ker.mp hφ)
    have hMD : M ∈ D := by
      change MulAut.conj M ∈ F
      rw [hM]
      exact φ.2
    exact ⟨⟨M, hMD⟩, Subtype.ext (Subtype.ext hM)⟩
  have hrange : Nat.card f.range ≤ 2 := by
    have : IsCyclic (Outer (SpecialLinearGroup (Fin 2) K)) := out_sl2_isCyclic
    obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := f.range)
    have hx2 : x ^ 2 = 1 := by
      obtain ⟨_, φ, rfl⟩ := x
      apply Subtype.ext
      change (f φ) ^ 2 = 1
      rw [← map_pow, sq, show φ * φ = 1 from Subtype.ext (h2 _ φ.2), map_one]
    rw [← orderOf_eq_card_of_forall_mem_zpowers hx]
    exact orderOf_le_of_pow_eq_one (by norm_num) hx2
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rcases (by omega : Nat.card f.range ≤ 1 ∨ Nat.card f.range = 2) with h1 | h1
  · rw [hF]
    calc Nat.card f.range * Nat.card f.ker ≤ 1 * Nat.card f.ker := Nat.mul_le_mul_right _ h1
      _ ≤ Nat.card K := by omega
  · obtain ⟨φ0, hφ0F, hφ0⟩ : ∃ φ0 ∈ F, φ0 ∉ innSL K := by
      by_contra hno
      push Not at hno
      have hbot : f.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨φ, rfl⟩
        rw [Subgroup.mem_bot]
        exact (QuotientGroup.eq_one_iff _).mpr (hno φ φ.2)
      rw [hbot, Subgroup.card_bot] at h1
      omega
    by_cases hDb : D = ⊥
    · have hD1 : Nat.card D = 1 := by rw [hDb, Subgroup.card_bot]
      rw [hF, h1]
      omega
    · have hfixD : ∀ M ∈ D, φ0 M = M := fun M hM => by
        apply conj_sl2_injective
        rw [conj_apply_aut, hc φ0 hφ0F _ hM, mul_assoc, mul_inv_cancel, mul_one]
      have hhalf := card_le_half hK hn hφ0 hD2 hDb hfixD
      rw [hF, h1]
      omega

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
