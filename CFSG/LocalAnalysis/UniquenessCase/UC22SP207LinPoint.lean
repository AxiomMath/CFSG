module

public import CFSG.LieType.SteinbergBRParabolicResidualImage
public import CFSG.LieType.SteinbergBRBlockParabolicDInf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.SP207Lin

open Subgroup Matrix

variable {K : Type*} [Field K] {b : Type*} [Fintype b] [DecidableEq b]

theorem det_eq_one_of_pow_eq_one [Finite K] {p k : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card K - 1) {D : GL b K} (hD : D ^ p ^ k = 1) :
    GeneralLinearGroup.det D = 1 := by
  have h1 : GeneralLinearGroup.det D ^ p ^ k = 1 := by rw [← map_pow, hD, map_one]
  have h2 : orderOf (GeneralLinearGroup.det D) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (GeneralLinearGroup.det D) ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard _
  have h4 : Nat.Coprime (p ^ k) (Nat.card K - 1) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq).pow_left k
  rw [← orderOf_eq_one_iff]
  exact ((h4.coprime_dvd_left h2).eq_one_of_dvd h3)

theorem exists_radical_levi_of_hom {G : Type*} [Group G] [Finite K] [Nonempty b]
    (Q : Subgroup G) [Finite Q] (χ : Q →* GL b K) (ι : SpecialLinearGroup b K →* G)
    (hιQ : ∀ D, ι D ∈ Q) (hι : ∀ D, χ ⟨ι D, hιQ D⟩ = SpecialLinearGroup.toGL D)
    (h2 : IsPGroup 2 χ.ker) (hZ : ι.range ⊓ center G = ⊥) :
    ∃ R L₁ : Subgroup G, R ≤ Q ∧ (R.subgroupOf Q).Normal ∧ IsPGroup 2 R ∧ L₁ ≤ Q ∧
      L₁ ⊓ center G = ⊥ ∧ Nonempty (↥L₁ ≃* SpecialLinearGroup b K) ∧
      ∀ {p : ℕ}, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K - 1 →
        (p ∣ Nat.card Q → p ∣ Nat.card (SpecialLinearGroup b K)) ∧
        ∀ x ∈ Q, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ R ⊔ L₁ := by
  have hinj : Function.Injective ι := fun D E h =>
    SpecialLinearGroup.toGL_injective (by
      rw [← hι D, ← hι E]
      exact congrArg χ (Subtype.ext h))
  have hrad : (χ.ker.map Q.subtype).subgroupOf Q = χ.ker :=
    comap_map_eq_self_of_injective Q.subtype_injective _
  refine ⟨χ.ker.map Q.subtype, ι.range, map_subtype_le _, ?_, h2.map _, ?_, hZ,
    ⟨(MonoidHom.ofInjective hinj).symm⟩, fun {p} hp hp2 hpq => ⟨fun hpQ => ?_, fun x hx hxp => ?_⟩⟩
  · rw [hrad]
    exact χ.normal_ker
  · rintro _ ⟨D, rfl⟩
    exact hιQ D
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).1 h2
    have hcard : Nat.card χ.ker * Nat.card χ.range = Nat.card Q := card_ker_mul_card_range χ
    rw [← hcard, hj] at hpQ
    have hpr : p ∣ Nat.card χ.range := by
      rcases hp.dvd_mul.1 hpQ with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)) hp2
      · exact h
    have hGL : Nat.card χ.range ∣ Nat.card (GL b K) := card_subgroup_dvd_card _
    rw [← Matrix.card_SL_mul_card_units, Nat.card_units] at hGL
    rcases hp.dvd_mul.1 (hpr.trans hGL) with h | h
    · exact h
    · exact absurd h hpq
  · obtain ⟨k, hk⟩ := hxp
    have hD : (χ ⟨x, hx⟩) ^ p ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : Q) ^ p ^ k = 1 := Subtype.ext hk
      rw [this, map_one]
    have hdet := det_eq_one_of_pow_eq_one hp hpq hD
    have hmem : χ ⟨x, hx⟩ ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup b K →* GL b K).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hdet
    obtain ⟨D, hDe⟩ := hmem
    have hker : (⟨x, hx⟩ : Q) * ⟨ι D, hιQ D⟩⁻¹ ∈ χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hι, hDe, mul_inv_cancel]
    have : x = x * (ι D)⁻¹ * ι D := by group
    rw [this]
    exact mul_mem_sup ⟨_, hker, rfl⟩ ⟨D, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.SP207Lin

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix CFSG.LieType.SteinbergBR.BlockPar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag SP207Lin

namespace SP207Lin

variable {K : Type*} [Field K] {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
  [DecidableEq b]

theorem sq_eq_one_of_toBlocks [CharP K 2] {M : SpecialLinearGroup (a ⊕ b) K} (hM : M ∈ parQ)
    (h11 : M.val.toBlocks₁₁ = 1) (h22 : M.val.toBlocks₂₂ = 1) : M ^ 2 = 1 := by
  have hMv := eq_fromBlocks_of_mem_parQ hM
  rw [h11, h22] at hMv
  have hX : M.val.toBlocks₁₂ + M.val.toBlocks₁₂ = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  refine Subtype.ext ?_
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hMv,
    fromBlocks_multiply]
  simp [hX, fromBlocks_one]

theorem eq_one_of_det_eq_one_of_unique {c : Type*} [Fintype c] [DecidableEq c] [Unique c]
    {M : Matrix c c K} (h : M.det = 1) : M = 1 := by
  rw [Matrix.det_unique] at h
  ext i j
  rw [Subsingleton.elim i default, Subsingleton.elim j default]
  simpa using h

end SP207Lin

private theorem exists_flagPoint_one {m : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] :
    ∃ R L₁ : Subgroup (SpecialLinearGroup (Fin m) K),
      R ≤ stabilizer (flagSpace m K 1) ∧ (R.subgroupOf (stabilizer (flagSpace m K 1))).Normal ∧
      IsPGroup 2 R ∧ L₁ ≤ stabilizer (flagSpace m K 1) ∧
      L₁ ⊓ center (SpecialLinearGroup (Fin m) K) = ⊥ ∧
      Nonempty (↥L₁ ≃* SpecialLinearGroup (Fin (m - 1)) K) ∧
      ∀ {p : ℕ}, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K - 1 →
        (p ∣ Nat.card (stabilizer (flagSpace m K 1)) →
          p ∣ Nat.card (SpecialLinearGroup (Fin (m - 1)) K)) ∧
        ∀ x ∈ stabilizer (flagSpace m K 1), (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ R ⊔ L₁ := by
  have h : 1 + (m - 1) = m := by omega
  have hs : (flagSpace m K 1).map (mulVecLin (1 : SpecialLinearGroup (Fin m) K).val) =
      flagSpace m K 1 := by simp
  have : Nonempty (Fin (m - 1)) := ⟨⟨0, by omega⟩⟩
  let e := parQEquiv h hs
  have hιQ : ∀ D : SpecialLinearGroup (Fin (m - 1)) K,
      transportSL K h 1 (levR K (Fin 1) D) ∈ stabilizer (flagSpace m K 1) := fun D =>
    (mem_parQ_iff_transport h hs _).1 (parJR_le_parQ (levR_mem_parJR D))
  refine exists_radical_levi_of_hom (stabilizer (flagSpace m K 1))
    ((chiR K (Fin 1) (Fin (m - 1))).comp e.symm.toMonoidHom)
    ((transportSL K h 1).toMonoidHom.comp (levR K (Fin 1))) hιQ (fun D => ?_) ?_ ?_
  · have he : e.symm ⟨transportSL K h 1 (levR K (Fin 1) D), hιQ D⟩ =
        ⟨levR K (Fin 1) D, parJR_le_parQ (levR_mem_parJR D)⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    change chiR K (Fin 1) (Fin (m - 1)) (e.symm ⟨transportSL K h 1 (levR K (Fin 1) D), hιQ D⟩) = _
    rw [he]
    refine Units.ext ?_
    change (levR K (Fin 1) D).val.toBlocks₂₂ = D.val
    rw [levR_val, toBlocks_fromBlocks₂₂]
  · intro x
    refine ⟨1, ?_⟩
    have hM : e.symm x.1 ∈ (chiR K (Fin 1) (Fin (m - 1))).ker :=
      MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)
    rw [ker_chiR, Subgroup.mem_subgroupOf, mem_parJL] at hM
    have hdet := det_eq_of_mem_parQ hM.1
    rw [hM.2, det_one, mul_one] at hdet
    have hsq := sq_eq_one_of_toBlocks hM.1 (eq_one_of_det_eq_one_of_unique hdet) hM.2
    have h1 : (x.1 : stabilizer (flagSpace m K 1)) ^ 2 = 1 := by
      refine e.symm.injective ?_
      rw [map_pow, map_one]
      exact Subtype.ext hsq
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact h1
  · rw [← scalars_eq_center m K, MonoidHom.range_comp]
    refine map_inf_scalars_eq_bot_left h 1 fun g hg => ?_
    obtain ⟨D, rfl⟩ := hg
    rw [levR_val, toBlocks_fromBlocks₁₁]

private theorem exists_flagPoint_last {m : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] :
    ∃ R L₁ : Subgroup (SpecialLinearGroup (Fin m) K),
      R ≤ stabilizer (flagSpace m K (m - 1)) ∧
      (R.subgroupOf (stabilizer (flagSpace m K (m - 1)))).Normal ∧
      IsPGroup 2 R ∧ L₁ ≤ stabilizer (flagSpace m K (m - 1)) ∧
      L₁ ⊓ center (SpecialLinearGroup (Fin m) K) = ⊥ ∧
      Nonempty (↥L₁ ≃* SpecialLinearGroup (Fin (m - 1)) K) ∧
      ∀ {p : ℕ}, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K - 1 →
        (p ∣ Nat.card (stabilizer (flagSpace m K (m - 1))) →
          p ∣ Nat.card (SpecialLinearGroup (Fin (m - 1)) K)) ∧
        ∀ x ∈ stabilizer (flagSpace m K (m - 1)), (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ R ⊔ L₁ := by
  have h : m - 1 + 1 = m := by omega
  have hs : (flagSpace m K (m - 1)).map (mulVecLin (1 : SpecialLinearGroup (Fin m) K).val) =
      flagSpace m K (m - 1) := by simp
  have : Nonempty (Fin (m - 1)) := ⟨⟨0, by omega⟩⟩
  let e := parQEquiv h hs
  have hιQ : ∀ D : SpecialLinearGroup (Fin (m - 1)) K,
      transportSL K h 1 (levL K (Fin 1) D) ∈ stabilizer (flagSpace m K (m - 1)) := fun D =>
    (mem_parQ_iff_transport h hs _).1 (parJL_le_parQ (levL_mem_parJL D))
  refine exists_radical_levi_of_hom (stabilizer (flagSpace m K (m - 1)))
    ((chiL K (Fin (m - 1)) (Fin 1)).comp e.symm.toMonoidHom)
    ((transportSL K h 1).toMonoidHom.comp (levL K (Fin 1))) hιQ (fun D => ?_) ?_ ?_
  · have he : e.symm ⟨transportSL K h 1 (levL K (Fin 1) D), hιQ D⟩ =
        ⟨levL K (Fin 1) D, parJL_le_parQ (levL_mem_parJL D)⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    change chiL K (Fin (m - 1)) (Fin 1) (e.symm ⟨transportSL K h 1 (levL K (Fin 1) D), hιQ D⟩) = _
    rw [he]
    refine Units.ext ?_
    change (levL K (Fin 1) D).val.toBlocks₁₁ = D.val
    rw [levL_val, toBlocks_fromBlocks₁₁]
  · intro x
    refine ⟨1, ?_⟩
    have hM : e.symm x.1 ∈ (chiL K (Fin (m - 1)) (Fin 1)).ker :=
      MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)
    rw [ker_chiL, Subgroup.mem_subgroupOf, mem_parJR] at hM
    have hdet := det_eq_of_mem_parQ hM.1
    rw [hM.2, det_one, one_mul] at hdet
    have hsq := sq_eq_one_of_toBlocks hM.1 hM.2 (eq_one_of_det_eq_one_of_unique hdet)
    have h1 : (x.1 : stabilizer (flagSpace m K (m - 1))) ^ 2 = 1 := by
      refine e.symm.injective ?_
      rw [map_pow, map_one]
      exact Subtype.ext hsq
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact h1
  · rw [← scalars_eq_center m K, MonoidHom.range_comp]
    refine map_inf_scalars_eq_bot_right h 1 fun g hg => ?_
    obtain ⟨D, rfl⟩ := hg
    rw [levL_val, toBlocks_fromBlocks₂₂]

theorem uc22sp207_flagPoint_structure {m d : ℕ} (hm : 3 ≤ m) (hd : d = 1 ∨ d = m - 1)
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ R L₁ : Subgroup (SpecialLinearGroup (Fin m) K),
      R ≤ LinearFlag.stabilizer (LinearFlag.flagSpace m K d) ∧
      (R.subgroupOf (LinearFlag.stabilizer (LinearFlag.flagSpace m K d))).Normal ∧
      IsPGroup 2 R ∧ L₁ ≤ LinearFlag.stabilizer (LinearFlag.flagSpace m K d) ∧
      L₁ ⊓ center (SpecialLinearGroup (Fin m) K) = ⊥ ∧
      Nonempty (↥L₁ ≃* SpecialLinearGroup (Fin (m - 1)) K) ∧
      ∀ {p : ℕ}, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K - 1 →
        (p ∣ Nat.card (LinearFlag.stabilizer (LinearFlag.flagSpace m K d)) →
          p ∣ Nat.card (SpecialLinearGroup (Fin (m - 1)) K)) ∧
        ∀ x ∈ LinearFlag.stabilizer (LinearFlag.flagSpace m K d), (∃ k : ℕ, x ^ p ^ k = 1) →
          x ∈ R ⊔ L₁ := by
  rcases hd with rfl | rfl
  · exact exists_flagPoint_one hm
  · exact exists_flagPoint_last hm

end CFSG.LocalAnalysis.UniquenessCase.UC22
