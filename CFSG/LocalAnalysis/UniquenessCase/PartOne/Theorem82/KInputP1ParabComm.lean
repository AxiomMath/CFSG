module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitRadical
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LinearThreeKit
open scoped commutatorElement

section Generic

variable {K : Type*} [Field K] {n : ℕ}

theorem commutator_mem_elationGenerators (L : Submodule K (Fin n → K))
    {g k : Matrix.SpecialLinearGroup (Fin n) K} (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hgL : ∀ w ∈ L, (g : Matrix (Fin n) (Fin n) K) *ᵥ w = a • w)
    (hgV : ∀ v, (g : Matrix (Fin n) (Fin n) K) *ᵥ v - b • v ∈ L)
    (hk : k ∈ stabilizer L) : ⁅g, k⁆ ∈ elationGenerators L := by
  have hmaps : ∀ x ∈ stabilizer L, ∀ w ∈ L, (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ L :=
    fun x hx w hw => (mem_stabilizer.mp hx) ▸ ⟨w, hw, rfl⟩
  have hkL := hmaps k hk
  have hk'L := hmaps k⁻¹ (inv_mem hk)
  have hgL' : ∀ w ∈ L, (g : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ L := fun w hw => by
    rw [hgL w hw]
    exact L.smul_mem a hw
  have hgi : ∀ w ∈ L,
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w =
        a⁻¹ • w := fun w hw => by
    have h1 : (g : Matrix (Fin n) (Fin n) K) *ᵥ (a⁻¹ • w) = w := by
      rw [Matrix.mulVec_smul, hgL w hw, smul_smul, inv_mul_cancel₀ ha, one_smul]
    conv_lhs => rw [← h1]
    exact inv_mulVec_mulVec g _
  have hgiV : ∀ z, ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z -
      b⁻¹ • z ∈ L := fun z => by
    have h := L.smul_mem (-b⁻¹) (hgV (((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ z))
    rw [mulVec_inv_mulVec] at h
    convert h using 1
    rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hb, neg_smul, neg_smul, one_smul]
    abel
  have hc : ∀ v, ((⁅g, k⁆ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      (g : Matrix (Fin n) (Fin n) K) *ᵥ ((k : Matrix (Fin n) (Fin n) K) *ᵥ
        (((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (((k⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v))) :=
    fun v => by
      rw [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [mem_elationGenerators_iff]
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [hc]
    set y := ((k⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v
    set u := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y
    have hky : (k : Matrix (Fin n) (Fin n) K) *ᵥ y = v := mulVec_inv_mulVec k v
    have h2 : (k : Matrix (Fin n) (Fin n) K) *ᵥ u - b⁻¹ • v ∈ L := by
      have := hkL _ (hgiV y)
      rwa [Matrix.mulVec_sub, Matrix.mulVec_smul, hky] at this
    have h3 : (g : Matrix (Fin n) (Fin n) K) *ᵥ ((k : Matrix (Fin n) (Fin n) K) *ᵥ u) -
        b⁻¹ • ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) ∈ L := by
      have := hgL' _ h2
      rwa [Matrix.mulVec_sub, Matrix.mulVec_smul] at this
    have h5 := L.add_mem h3 (L.smul_mem b⁻¹ (hgV v))
    convert h5 using 1
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hb, one_smul]
    abel
  · rw [hc, hgi _ (hk'L v hv), Matrix.mulVec_smul, mulVec_inv_mulVec, Matrix.mulVec_smul,
      hgL v hv, smul_smul, inv_mul_cancel₀ ha, one_smul]

end Generic

section Levi

variable {K : Type*} [Field K]

@[expose] def leviAlpha (d : ℕ) (c : Kˣ) : Kˣ := if d = 1 then c⁻¹ ^ 2 else c

@[expose] def leviBeta (d : ℕ) (c : Kˣ) : Kˣ := if d = 1 then c else c⁻¹ ^ 2

@[expose] def leviMatrix (d : ℕ) (c : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal fun j => if (j : ℕ) < d then ((leviAlpha d c : Kˣ) : K)
    else ((leviBeta d c : Kˣ) : K)

theorem det_leviMatrix {d : ℕ} (hd : d = 1 ∨ d = 2) (c : Kˣ) : (leviMatrix d c).det = 1 := by
  have hc : (c : K) ≠ 0 := c.ne_zero
  rw [leviMatrix, Matrix.det_diagonal, Fin.prod_univ_three]
  rcases hd with rfl | rfl <;> simp [leviAlpha, leviBeta] <;> field_simp

@[expose] def leviCentral {d : ℕ} (hd : d = 1 ∨ d = 2) (c : Kˣ) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨leviMatrix d c, det_leviMatrix hd c⟩

theorem leviCentral_acts {d : ℕ} (hd : d = 1 ∨ d = 2) (c : Kˣ) :
    leviCentral hd c ∈ stabilizer (flagSpace 3 K d) ∧
    (∀ w ∈ flagSpace 3 K d, ((leviCentral hd c : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ w = ((leviAlpha d c : Kˣ) : K) • w) ∧
    (∀ v, ((leviCentral hd c : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v - ((leviBeta d c : Kˣ) : K) • v ∈ flagSpace 3 K d) := by
  have hcoe : ((leviCentral hd c : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = leviMatrix d c := rfl
  have hv : ∀ (v : Fin 3 → K) (j : Fin 3), (leviMatrix d c *ᵥ v) j =
      (if (j : ℕ) < d then ((leviAlpha d c : Kˣ) : K) else ((leviBeta d c : Kˣ) : K)) * v j :=
    fun v j => by rw [leviMatrix, Matrix.mulVec_diagonal]
  have hL : ∀ w ∈ flagSpace 3 K d,
      leviMatrix d c *ᵥ w = ((leviAlpha d c : Kˣ) : K) • w := fun w hw => by
    funext j
    rw [hv, Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · rfl
    · rw [mem_flagSpace.mp hw j (not_lt.mp h), mul_zero, mul_zero]
  refine ⟨?_, fun w hw => by rw [hcoe]; exact hL w hw, fun v => ?_⟩
  · rw [mem_stabilizer, hcoe]
    refine le_antisymm ?_ fun w hw =>
      ⟨((leviAlpha d c)⁻¹ : Kˣ).val • w, Submodule.smul_mem _ _ hw, ?_⟩
    · rintro _ ⟨v, hv', rfl⟩
      rw [mulVecLin_apply, hL v hv']
      exact Submodule.smul_mem _ _ hv'
    · rw [mulVecLin_apply, hL _ (Submodule.smul_mem _ _ hw), smul_smul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, one_smul]
  · rw [hcoe, mem_flagSpace]
    intro j hj
    rw [Pi.sub_apply, hv, Pi.smul_apply, smul_eq_mul, if_neg (not_lt.mpr hj), sub_self]

theorem leviCentral_commutator_mem {d : ℕ} (hd : d = 1 ∨ d = 2) (c : Kˣ)
    {k : Matrix.SpecialLinearGroup (Fin 3) K} (hk : k ∈ stabilizer (flagSpace 3 K d)) :
    ⁅leviCentral hd c, k⁆ ∈ elationSubgroup (flagSpace 3 K d) := by
  obtain ⟨-, hL, hV⟩ := leviCentral_acts (K := K) hd c
  exact mem_elationSubgroup_of_mem (commutator_mem_elationGenerators _ _ _
    (leviAlpha d c).ne_zero (leviBeta d c).ne_zero hL hV hk)

theorem orderOf_proj_leviCentral {d : ℕ} (hd : d = 1 ∨ d = 2) {c : Kˣ} {r : ℕ} (hr : r.Prime)
    (h5 : 5 ≤ r) (hc : orderOf c = r) : orderOf (proj 3 K (leviCentral hd c)) = r := by
  have hcr : c ^ r = 1 := hc ▸ pow_orderOf_eq_one c
  have hinv : (c⁻¹ ^ 2) ^ r = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, inv_pow, hcr, inv_one, one_pow]
  have hα : leviAlpha d c ^ r = 1 := by
    unfold leviAlpha
    split_ifs
    exacts [hinv, hcr]
  have hβ : leviBeta d c ^ r = 1 := by
    unfold leviBeta
    split_ifs
    exacts [hcr, hinv]
  have hpow : leviCentral hd c ^ r = 1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    change leviMatrix d c ^ r = 1
    rw [leviMatrix, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext j
    simp only [Pi.pow_apply, Pi.one_apply]
    split_ifs
    · rw [← Units.val_pow_eq_pow_val, hα, Units.val_one]
    · rw [← Units.val_pow_eq_pow_val, hβ, Units.val_one]
  have hdvd : orderOf (proj 3 K (leviCentral hd c)) ∣ r :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow, map_one])
  refine (Nat.dvd_prime hr).mp hdvd |>.resolve_left fun h1 => ?_
  rw [orderOf_eq_one_iff, proj_eq_one_iff] at h1
  obtain ⟨c', -, hg⟩ := h1
  have hg' : leviMatrix d c = scalar (Fin 3) (c' : K) := hg
  have e : ∀ i : Fin 3, leviMatrix d c i i = c' := fun i => by
    rw [hg']
    simp [Matrix.scalar_apply]
  have hab : leviAlpha d c = leviBeta d c := by
    apply Units.ext
    rcases hd with rfl | rfl
    · have h0 := e 0
      have h1 := e 1
      simp only [leviMatrix, Matrix.diagonal_apply_eq] at h0 h1
      simpa using h0.trans h1.symm
    · have h0 := e 0
      have h2 := e 2
      simp only [leviMatrix, Matrix.diagonal_apply_eq] at h0 h2
      simpa using h0.trans h2.symm
  have hab' : c⁻¹ ^ 2 = c := by
    unfold leviAlpha leviBeta at hab
    rcases hd with rfl | rfl
    · simpa using hab
    · simpa using hab.symm
  have h3 : c ^ 3 = 1 := by
    calc c ^ 3 = c ^ 2 * c := pow_succ c 2
      _ = c ^ 2 * c⁻¹ ^ 2 := by rw [hab']
      _ = 1 := by rw [← mul_pow, mul_inv_cancel, one_pow]
  have := Nat.le_of_dvd (by norm_num) (hc ▸ orderOf_dvd_of_pow_eq_one h3)
  omega

end Levi

section Parabolic

variable {K : Type} [Field K] [Finite K]

theorem map_elationSubgroup_le_pCoreOf [CharP K 2] {d : ℕ} :
    (elationSubgroup (flagSpace 3 K d)).map (proj 3 K) ≤
      CFSG.Open.pCoreOf 2 (projStabilizer (flagSpace 3 K d)) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.map_mono (elationSubgroup_le_stabilizer _))
    ((Subgroup.map_mono (stabilizer_le_normalizer_elationSubgroup _)).trans
      (Subgroup.le_normalizer_map _))
    ((isPGroup_elationSubgroup 2 _).map _)

theorem exists_levi_central [CharP K 2] {d : ℕ} (hd : d = 1 ∨ d = 2) {r : ℕ} (hr : r.Prime)
    (h5 : 5 ≤ r) (hrK : r ∣ Nat.card K - 1) :
    ∃ g ∈ projStabilizer (flagSpace 3 K d), orderOf g = r ∧
      ∀ k ∈ projStabilizer (flagSpace 3 K d),
        g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (projStabilizer (flagSpace 3 K d)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r (by rwa [Nat.card_units])
  refine ⟨proj 3 K (leviCentral hd c), Subgroup.mem_map_of_mem _ (leviCentral_acts hd c).1,
    orderOf_proj_leviCentral hd hr h5 hc, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hcomm : proj 3 K (leviCentral hd c) * proj 3 K k * (proj 3 K (leviCentral hd c))⁻¹ *
      (proj 3 K k)⁻¹ = proj 3 K ⁅leviCentral hd c, k⁆ := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [hcomm]
  exact map_elationSubgroup_le_pCoreOf
    (Subgroup.mem_map_of_mem _ (leviCentral_commutator_mem hd c hk))

end Parabolic

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
