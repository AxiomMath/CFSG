module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSevenE
import CFSG.RankThree.PartTwo.Sec18.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res4

open CFSG CFSG.RankThree.PartTwo.Sec20
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {n : ℕ}

theorem one_add_one_galois : (1 : GaloisField 2 n) + 1 = 0 := by
  rw [one_add_one_eq_two]
  exact CharTwo.two_eq_zero

@[expose] noncomputable def matOne : Matrix (Fin 3) (Fin 3) (GaloisField 2 n) :=
  !![1, 0, 0; 0, 0, 1; 0, 1, 1]

@[expose] noncomputable def matTwo : Matrix (Fin 3) (Fin 3) (GaloisField 2 n) :=
  !![0, 1, 0; 1, 1, 0; 0, 0, 1]

theorem det_matOne : (matOne (n := n)).det = 1 := by
  have h := one_add_one_galois (n := n)
  simp [matOne, Matrix.det_fin_three]
  linear_combination (-1 : GaloisField 2 n) * h

theorem det_matTwo : (matTwo (n := n)).det = 1 := by
  have h := one_add_one_galois (n := n)
  simp [matTwo, Matrix.det_fin_three]
  linear_combination (-1 : GaloisField 2 n) * h

@[expose] noncomputable def slOne : SpecialLinearGroup (Fin 3) (GaloisField 2 n) :=
  ⟨matOne, det_matOne⟩

@[expose] noncomputable def slTwo : SpecialLinearGroup (Fin 3) (GaloisField 2 n) :=
  ⟨matTwo, det_matTwo⟩

theorem slOne_pow_three : (slOne (n := n)) ^ 3 = 1 := by
  have h := one_add_one_galois (n := n)
  apply Subtype.ext
  change (matOne : Matrix (Fin 3) (Fin 3) (GaloisField 2 n)) ^ 3 = 1
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matOne, Matrix.mul_apply, Fin.sum_univ_three, h]

theorem slTwo_pow_three : (slTwo (n := n)) ^ 3 = 1 := by
  have h := one_add_one_galois (n := n)
  apply Subtype.ext
  change (matTwo : Matrix (Fin 3) (Fin 3) (GaloisField 2 n)) ^ 3 = 1
  rw [pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matTwo, Matrix.mul_apply, Fin.sum_univ_three, h]

theorem slOne_ne_one : (slOne (n := n)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SpecialLinearGroup (Fin 3) (GaloisField 2 n) =>
    (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 n)) 1 1) h
  simp [slOne, matOne] at this

theorem slTwo_ne_one : (slTwo (n := n)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SpecialLinearGroup (Fin 3) (GaloisField 2 n) =>
    (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 n)) 0 0) h
  simp [slTwo, matTwo] at this

theorem slOne_mem_stabilizer :
    slOne (n := n) ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) 1) := by
  apply LinearFlag.mem_stabilizer_of_map_le
  rintro _ ⟨v, hv, rfl⟩
  have hv' := LinearFlag.mem_flagSpace.mp hv
  refine LinearFlag.mem_flagSpace.mpr fun j hj => ?_
  have h1 : v 1 = 0 := hv' 1 (by simp)
  have h2 : v 2 = 0 := hv' 2 (by simp)
  fin_cases j
  · simp at hj
  · simp [slOne, matOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2]
  · simp [slOne, matOne, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]

theorem slTwo_mem_stabilizer :
    slTwo (n := n) ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) 2) := by
  apply LinearFlag.mem_stabilizer_of_map_le
  rintro _ ⟨v, hv, rfl⟩
  have hv' := LinearFlag.mem_flagSpace.mp hv
  refine LinearFlag.mem_flagSpace.mpr fun j hj => ?_
  have h2 : v 2 = 0 := hv' 2 (by simp)
  fin_cases j
  · simp at hj
  · simp at hj
  · simp [slTwo, matTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2]

theorem normalizer_le_of_isMaxParabolic
    {P : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))}
    (hP : Sec18.IsMaxParabolicRankTwo P)
    (U : Sylow 2 (SpecialLinearGroup (Fin 3) (GaloisField 2 n)))
    (hUP : (U : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ≤ P) :
    Subgroup.normalizer ((U : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) :
      Set (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, T₀, hT₀⟩ := hP
  have hsyl : ∀ R : Sylow 2 (SpecialLinearGroup (Fin 3) (GaloisField 2 n)),
      (R : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 2
        (R : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) P := by
    intro R hRP
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hRP, R.isPGroup', fun h => R.not_dvd_index (h.trans
      (Subgroup.relIndex_dvd_index_of_le hRP))⟩
  have hT₀P : (T₀ : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ≤ P :=
    Subgroup.le_normalizer.trans hT₀
  obtain ⟨p₀, hp₀, hU₀⟩ := Sec18.exists_map_conj_eq_of_isSylowOf (hsyl T₀ hT₀P) (hsyl U hUP)
  rw [hU₀, ← Subgroup.map_equiv_normalizer_eq]
  intro x hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact P.mul_mem (P.mul_mem hp₀ (hT₀ hw)) (P.inv_mem hp₀)

theorem exists_and_not_mem_of_borel (hn : Odd n)
    {P X : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))}
    (hP : Sec18.IsMaxParabolicRankTwo P)
    (U : Sylow 2 (SpecialLinearGroup (Fin 3) (GaloisField 2 n)))
    (hUP : (U : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ≤ P)
    (hXN : Subgroup.normalizer ((U : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) :
      Set (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ≤
        Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 3) (GaloisField 2 n))))
    (hXP : ¬ X ≤ P) (hXtop : X ≠ ⊤) :
    (∃ x ∈ X, x ^ 3 = 1 ∧ x ≠ 1) ∧ (∀ x ∈ X, x ^ 3 = 1 → x ≠ 1 → x ∉ P) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n hn.pos.ne']
    exact two_pow_mod_three_of_odd hn
  have hNUP := normalizer_le_of_isMaxParabolic hP U hUP
  obtain ⟨hPc, -, -⟩ := hP
  obtain ⟨Ut, hUt⟩ := LinearFlag.exists_sylow_unitriangular (K := GaloisField 2 n) 2 (n := 3)
    (by norm_num)
  have hsylTop : ∀ R : Sylow 2 (SpecialLinearGroup (Fin 3) (GaloisField 2 n)),
      CFSG.ABGLocalTools.IsSylowOf 2
        (R : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ⊤ := by
    intro R
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, R.isPGroup', R.not_dvd_index⟩
  obtain ⟨g, -, hg⟩ := Sec18.exists_map_conj_eq_of_isSylowOf (hsylTop U) (hsylTop Ut)
  rw [hUt] at hg
  set φ := MulAut.conj g with hφ
  have hB : LinearFlag.upperTriangular 3 (GaloisField 2 n) =
      (Subgroup.normalizer ((U : Subgroup (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) :
        Set (SpecialLinearGroup (Fin 3) (GaloisField 2 n)))).map φ.toMonoidHom := by
    rw [← LinearFlag.normalizer_unitriangular, hg, Subgroup.map_equiv_normalizer_eq]
  set B := LinearFlag.upperTriangular 3 (GaloisField 2 n) with hBdef
  have hP₁ : IsCoatom (P.map φ.toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup φ) P).mpr hPc
  have hBP₁ : B ≤ P.map φ.toMonoidHom := by
    rw [hB]
    exact Subgroup.map_mono hNUP
  set X₁ := X.map φ.toMonoidHom with hX₁def
  have hBX₁ :
      B ≤ Subgroup.normalizer (X₁ : Set (SpecialLinearGroup (Fin 3) (GaloisField 2 n))) := by
    rw [hB, hX₁def, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hXN
  have hmemX₁ : ∀ x : SpecialLinearGroup (Fin 3) (GaloisField 2 n), φ x ∈ X₁ ↔ x ∈ X := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← φ.injective hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hmemP₁ : ∀ x : SpecialLinearGroup (Fin 3) (GaloisField 2 n),
      φ x ∈ P.map φ.toMonoidHom ↔ x ∈ P := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← φ.injective hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  obtain ⟨hPI, -⟩ := LinearFlag.borel_overgroups (P.map φ.toMonoidHom) hBP₁
  obtain ⟨d, hdmem⟩ : (LinearFlag.borelOvergroupCuts (P.map φ.toMonoidHom)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    apply hP₁.1
    rw [hPI, h, LinearFlag.flagStabilizer_empty]
  obtain ⟨hd, hdn, -⟩ := id hdmem
  have hPd : P.map φ.toMonoidHom =
      LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) d) := by
    have hle : P.map φ.toMonoidHom ≤
        LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) d) := by
      intro y hy
      rw [hPI] at hy
      exact LinearFlag.mem_flagStabilizer.mp hy d hdmem
    rcases hP₁.le_iff.mp hle with h | h
    · exact absurd h (LinearFlag.stabilizer_flagSpace_ne_top hd hdn)
    · exact h.symm
  obtain ⟨hAI, -⟩ := LinearFlag.borel_overgroups (X₁ ⊔ B) le_sup_right
  have hdA : d ∉ LinearFlag.borelOvergroupCuts (X₁ ⊔ B) := by
    intro hdA
    apply hXP
    intro x hx
    have hxA : φ x ∈ X₁ ⊔ B := Subgroup.mem_sup_left ((hmemX₁ x).mpr hx)
    rw [hAI] at hxA
    have hxd := LinearFlag.mem_flagStabilizer.mp hxA d hdA
    rw [← hPd] at hxd
    exact (hmemP₁ x).mp hxd
  have hIne : (LinearFlag.borelOvergroupCuts (X₁ ⊔ B)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hI
    have hAtop : X₁ ⊔ B = ⊤ := by rw [hAI, hI, LinearFlag.flagStabilizer_empty]
    have hX₁n : X₁.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hAtop]
      exact sup_le Subgroup.le_normalizer hBX₁
    have := isSimpleGroup_sl3_of_odd hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X₁ with h | h
    · apply hXP
      intro x hx
      have h1 : φ x ∈ X₁ := (hmemX₁ x).mpr hx
      rw [h, Subgroup.mem_bot] at h1
      have h2 : x = 1 := φ.injective (h1.trans (map_one φ).symm)
      rw [h2]
      exact P.one_mem
    · apply hXtop
      rw [eq_top_iff]
      intro x _
      have h1 : φ x ∈ X₁ := by rw [h]; exact Subgroup.mem_top _
      exact (hmemX₁ x).mp h1
  obtain ⟨e, he⟩ := hIne
  obtain ⟨he1, hen, -⟩ := id he
  have hIe : LinearFlag.borelOvergroupCuts (X₁ ⊔ B) = {e} := by
    ext i
    constructor
    · intro hi
      obtain ⟨hi1, hin, -⟩ := id hi
      have hid : i ≠ d := fun h => hdA (h ▸ hi)
      have hed : e ≠ d := fun h => hdA (h ▸ he)
      rw [Set.mem_singleton_iff]
      omega
    · intro hi
      rw [Set.mem_singleton_iff] at hi
      rw [hi]
      exact he
  have hAe : X₁ ⊔ B = LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) e) := by
    rw [hAI, hIe, LinearFlag.flagStabilizer_singleton]
  have hed : e ≠ d := fun h => hdA (h ▸ he)
  have hinter : ∀ y, y ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) d) →
      y ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) e) → y ∈ B := by
    intro y hyd hye
    have h12 : (d = 1 ∧ e = 2) ∨ (d = 2 ∧ e = 1) := by omega
    rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact mem_upperTriangular_of_mem_stabilizer hyd hye
    · exact mem_upperTriangular_of_mem_stabilizer hye hyd
  obtain ⟨y₀, hy₀A, hy₀3, hy₀1⟩ : ∃ y ∈ X₁ ⊔ B, y ^ 3 = 1 ∧ y ≠ 1 := by
    rw [hAe]
    have : e = 1 ∨ e = 2 := by omega
    rcases this with rfl | rfl
    · exact ⟨slOne, slOne_mem_stabilizer, slOne_pow_three, slOne_ne_one⟩
    · exact ⟨slTwo, slTwo_mem_stabilizer, slTwo_pow_three, slTwo_ne_one⟩
  have hB3 : ¬ 3 ∣ Nat.card B := by
    intro h3
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hb3 : (b : SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ^ 3 = 1 := by
      have h1 := pow_orderOf_eq_one b
      rw [hb] at h1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hb1 := eq_one_of_mem_upperTriangular_of_pow_three hq b.2 hb3
    have : b = 1 := Subtype.ext hb1
    rw [this, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have hX3 : 3 ∣ Nat.card X₁ := by
    by_contra hX3
    have hdA3 : 3 ∣ Nat.card ↥(X₁ ⊔ B) := by
      have h1 := orderOf_dvd_natCard (⟨y₀, hy₀A⟩ : ↥(X₁ ⊔ B))
      rwa [Subgroup.orderOf_mk, orderOf_eq_prime hy₀3 hy₀1] at h1
    have hrel : X₁.relIndex (B ⊔ X₁) = X₁.relIndex B := by
      have := Subgroup.normal_subgroupOf_of_le_normalizer hBX₁
      have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBX₁
      exact Nat.card_congr
        (QuotientGroup.quotientInfEquivProdNormalizerQuotient B X₁ hBX₁).toEquiv.symm
    have hmul := Subgroup.relIndex_mul_card X₁ (B ⊔ X₁)
    rw [inf_eq_left.mpr le_sup_right, hrel] at hmul
    have hdvd : Nat.card ↥(X₁ ⊔ B) ∣ Nat.card B * Nat.card X₁ := by
      rw [sup_comm, ← hmul]
      exact Nat.mul_dvd_mul_right (Subgroup.relIndex_dvd_card X₁ B) _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (hdA3.trans hdvd) with h | h
    · exact hB3 h
    · exact hX3 h
  refine ⟨?_, fun x hx hx3 hx1 hxP => ?_⟩
  · obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' 3 hX3
    obtain ⟨x, hx, hxx⟩ := x₁.2
    have hx3 : x ^ 3 = 1 := by
      apply φ.injective
      have : (φ x) ^ 3 = 1 := by
        change (φ.toMonoidHom x) ^ 3 = 1
        have h1 := pow_orderOf_eq_one x₁
        rw [hx₁] at h1
        rw [hxx, ← Subgroup.coe_pow, h1, Subgroup.coe_one]
      rw [map_pow, this, map_one]
    refine ⟨x, hx, hx3, fun h1 => ?_⟩
    have : x₁ = 1 := Subtype.ext (by rw [← hxx, h1]; exact map_one _)
    rw [this, orderOf_one] at hx₁
    exact absurd hx₁ (by norm_num)
  ·
    have h1 : φ x ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) d) := by
      rw [← hPd]
      exact (hmemP₁ x).mpr hxP
    have h2 : φ x ∈ LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) e) := by
      rw [← hAe]
      exact Subgroup.mem_sup_left ((hmemX₁ x).mpr hx)
    have h3 := eq_one_of_mem_upperTriangular_of_pow_three hq (hinter _ h1 h2)
      (by rw [← map_pow, hx3, map_one])
    exact hx1 (φ.injective (h3.trans (map_one φ).symm))

end CFSG.RankThree.PartTwo.Sec20.Res4
