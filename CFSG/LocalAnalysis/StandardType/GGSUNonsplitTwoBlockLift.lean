module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockFrame
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSU
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization

public section

namespace CFSG.StandardType

namespace SUTB

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

variable {f n : ℕ} {K : Type} [Field K]

theorem isBlockOn_compl_of_commute_blockSU (h : UnitaryFieldData 2 f K) {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ f + 1) {S : Finset (Fin n)} (hS : 2 ≤ S.card) {N : ↥(unitarySU 2 f K n)}
    (hNp : N ^ p = 1) (hN : ∀ s ∈ TableBUE.blockSU (K := K) (n := f) S, N * s = s * N) :
    TableBUE.IsBlockOn Sᶜ (mx N) := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  set Nm : Matrix (Fin n) (Fin n) K := ((N : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hNm
  have hq1 : 2 ^ f + 1 ≠ 1 := by have := pow_pos (by norm_num : (0 : ℕ) < 2) f; omega
  have hrp : (Nat.minFac (2 ^ f + 1)).Prime := Nat.minFac_prime hq1
  have hr2 : Nat.minFac (2 ^ f + 1) ≠ 2 := by
    intro h2
    have h3 : 2 ∣ 2 ^ f + 1 := by
      have := Nat.minFac_dvd (2 ^ f + 1)
      rwa [h2] at this
    have h4 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by have := h.one_le; omega)
    omega
  obtain ⟨ζ, hζo, hζq⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one h hrp (Nat.minFac_dvd (2 ^ f + 1))
  have hζ1 : ζ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hζo
    exact hrp.one_lt.ne' hζo.symm
  have hζ2 : ζ ≠ ζ⁻¹ := by
    intro he
    have h1 : ζ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [he]; exact mul_inv_cancel ζ
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hζo] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp this)
  have hNGL : ∀ s ∈ TableBUE.blockSU (K := K) (n := f) S,
      (N : GL (Fin n) K) * (s : GL (Fin n) K) = (s : GL (Fin n) K) * (N : GL (Fin n) K) :=
    fun s hs => congrArg Subtype.val (hN s hs)
  have hoff : ∀ i ∈ S, ∀ j, j ≠ i → Nm i j = 0 ∧ Nm j i = 0 := by
    intro i hi j hji
    obtain ⟨k, hk, hki⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) i
    set t : Fin n → Kˣ := Pi.mulSingle i ζ * Pi.mulSingle k ζ⁻¹ with ht
    have hti : t i = ζ := by simp [ht, hki.symm]
    have htk : t k = ζ⁻¹ := by simp [ht, hki]
    have hto : ∀ l, l ≠ i → l ≠ k → t l = 1 := fun l hli hlk => by simp [ht, hli, hlk]
    have hD : diagHom n t ∈ unitarySU 2 f K n := by
      refine TableBUE.diagHom_mem_unitarySU h (fun l => ?_) ?_
      · simp only [ht, Pi.mul_apply, Pi.mulSingle_apply]
        split_ifs <;> simp [hζq, inv_pow]
      · simp only [ht, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
        exact mul_inv_cancel ζ
    have hDS : (⟨diagHom n t, hD⟩ : ↥(unitarySU 2 f K n)) ∈
        TableBUE.blockSU (K := K) (n := f) S := by
      intro a b hab
      change (diagHom n t : Matrix (Fin n) (Fin n) K) a b = _
      rw [coe_diagHom, Matrix.diagonal_apply, Matrix.one_apply]
      by_cases hba : a = b
      · subst hba
        have ha : a ∉ S := by tauto
        rw [ite_eq_left rfl, ite_eq_left rfl, hto a (fun h1 => ha (h1 ▸ hi))
          (fun h1 => ha (h1 ▸ hk)), Units.val_one]
      · rw [ite_eq_right hba, ite_eq_right hba]
    have hcomm := hNGL _ hDS
    have htj : t j ≠ t i := by
      rw [hti]
      by_cases hjk : j = k
      · rw [hjk, htk]
        exact fun h1 => hζ2 h1.symm
      · rw [hto j hji hjk]
        exact fun h1 => hζ1 h1.symm
    exact ⟨TableBUE.entry_eq_zero_of_commute hcomm htj.symm,
      TableBUE.entry_eq_zero_of_commute hcomm htj⟩
  have hdiag : ∀ i ∈ S, ∀ k ∈ S, Nm i i = Nm k k := by
    intro i hi k hk
    have hP := hNGL ⟨_, TableBUE.permGL_swap_mem h i k⟩ (TableBUE.isBlockOn_permGL_swap hi hk)
    have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
      hP) i) k
    have e1 : (Nm * ((CFSG.RankThree.Classical.permGL (Equiv.swap i k) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) i k = Nm i i := by
      simp [Matrix.mul_apply, Equiv.swap_apply_eq_iff]
    have e2 : (((CFSG.RankThree.Classical.permGL (Equiv.swap i k) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * Nm) i k = Nm k k := by
      simp [Matrix.mul_apply]
    simp only [Units.val_mul] at h1
    rw [← e1, ← e2]
    exact h1
  have hone : ∀ i ∈ S, Nm i i = 1 := by
    intro i hi
    have hcol : Nm *ᵥ Pi.single i 1 = Nm i i • Pi.single i 1 := by
      funext l
      have h1 : (Nm *ᵥ Pi.single i 1) l = Nm l i := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [h1, Pi.smul_apply, smul_eq_mul]
      by_cases hli : l = i
      · subst hli
        rw [Pi.single_eq_same, mul_one]
      · rw [Pi.single_eq_of_ne hli, mul_zero, (hoff i hi l hli).2]
    have hpow : ∀ m : ℕ, Nm ^ m *ᵥ Pi.single i 1 = Nm i i ^ m • Pi.single i 1 := by
      intro m
      induction m with
      | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
      | succ m ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_smul, ih, smul_smul,
          ← pow_succ']
    have hlp : Nm i i ^ p = 1 := by
      have h1 := hpow p
      have hNp' : Nm ^ p = 1 := by rw [hNm, ← mx, ← mx_pow, hNp, mx_one]
      rw [hNp', Matrix.one_mulVec] at h1
      have h2 := congrFun h1 i
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] at h2
      exact h2.symm
    have hlq : Nm i i ^ (2 ^ f + 1) = 1 := by
      obtain ⟨-, hu⟩ := (mem_unitarySU_iff h).mp N.2
      have h1 := congrFun (congrFun hu i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun l _ hli => by
        rw [Matrix.transpose_apply, Matrix.map_apply]
        change h.bar (Nm l i) * Nm l i = 0
        rw [(hoff i hi l hli).2, map_zero, zero_mul])
        (by simp), Matrix.transpose_apply, Matrix.map_apply, Matrix.one_apply_eq,
        UnitaryFieldData.bar_apply] at h1
      rw [pow_succ]
      exact h1
    have hcop : p.gcd (2 ^ f + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
    have h5 := pow_gcd_eq_one.mpr ⟨hlp, hlq⟩
    rwa [hcop, pow_one] at h5
  change TableBUE.IsBlockOn Sᶜ Nm
  intro a b hab
  rw [Matrix.one_apply]
  rcases hab with ha | hb
  · have ha' : a ∈ S := by simpa using ha
    by_cases hba : a = b
    · subst hba
      rw [ite_eq_left rfl, hone a ha']
    · rw [ite_eq_right hba, (hoff a ha' b (Ne.symm hba)).1]
  · have hb' : b ∈ S := by simpa using hb
    by_cases hba : a = b
    · subst hba
      rw [ite_eq_left rfl, hone a hb']
    · rw [ite_eq_right hba, (hoff b hb' a hba).2]

theorem scalar_mem_primeFormUnitary_idGram (h : UnitaryFieldData 2 f K) {c : Kˣ}
    (hc : (c : K) ^ (2 ^ f + 1) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ primeFormUnitary h (idGram K n) := by
  rw [mem_primeFormUnitary, Matrix.GeneralLinearGroup.coe_scalar,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.scalar_barTranspose_mul_mul,
    UnitaryFieldData.norm_eq_pow, hc, one_smul]

theorem isometry_of_mem_primeFormUnitary (h : UnitaryFieldData 2 f K) {X : GL (Fin n) K}
    (hX : X ∈ primeFormUnitary h (idGram K n)) (v w : Fin n → K) :
    stdHermForm h n ((X : Matrix (Fin n) (Fin n) K) *ᵥ v) ((X : Matrix (Fin n) (Fin n) K) *ᵥ w) =
      stdHermForm h n v w := by
  have h1 := mem_primeFormUnitary.mp hX
  rw [idGram, Units.val_one] at h1
  rw [stdHermForm_eq_gramForm]
  exact (gramForm_isometry_iff h 1 (X : Matrix (Fin n) (Fin n) K)).mpr h1 v w

theorem exists_lift (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hnq : (n, 2 ^ f) ≠ (3, 2))
    {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ f + 1) {G : Type} [Group G]
    {ψ₁ : ↥(unitarySU 2 f K n) →* G} (hker : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    (hC : Subgroup.centralizer (ψ₁.range : Set G) = ⊥) {b : G} (hbp : b ^ p = 1)
    {B' : GL (Fin n) K} (hB'U : B' ∈ primeFormUnitary h (idGram K n))
    (hB' : (b, B') ∈ SUTorus.suPairs ψ₁) : ∃ X : ↥(unitarySU 2 f K n), X ^ p = 1 ∧ ψ₁ X = b := by
  classical
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have hq1 : 2 ^ f + 1 ≠ 1 := by have := pow_pos (by norm_num : (0 : ℕ) < 2) f; omega
  have h1 : ((1 : G), B' ^ p) ∈ SUTorus.suPairs ψ₁ := by
    have := (SUTorus.suPairs ψ₁).pow_mem hB' p
    rwa [Prod.pow_mk, hbp] at this
  obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one h hn hnq (Nat.minFac_prime hq1)
    (Nat.minFac_dvd _) hker h1
  have hcn : (c : K) ^ (2 ^ f + 1) = 1 := by
    have h2 := mem_primeFormUnitary.mp ((primeFormUnitary h (idGram K n)).pow_mem hB'U p)
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.scalar_barTranspose_mul_mul, idGram,
      Units.val_one, UnitaryFieldData.norm_eq_pow] at h2
    have h3 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h3
  have hcu : c ^ (2 ^ f + 1) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hcn, Units.val_one])
  have hcop : p.Coprime (2 ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (by have := pow_pos (by norm_num : (0 : ℕ) < 2) f; omega)
  set μ : Kˣ := c ^ k with hμ
  have hμp : μ ^ p = c := by
    rw [hμ, ← pow_mul, mul_comm, ← Nat.mod_add_div (p * k) (2 ^ f + 1), hk, pow_add, pow_mul,
      hcu, one_pow, mul_one, pow_one]
  have hμn : ((μ⁻¹ : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hμ, ← pow_mul, mul_comm, pow_mul, hcu, one_pow,
      inv_one, Units.val_one]
  set X₀ : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * B' with hX₀
  have hX₀p : X₀ ^ p = 1 := by
    rw [hX₀, (commute_scalar μ⁻¹ B').symm.mul_pow, ← map_pow, hc, ← map_mul, inv_pow, hμp,
      inv_mul_cancel, map_one]
  have hX₀U : X₀ ∈ primeFormUnitary h (idGram K n) :=
    (primeFormUnitary h _).mul_mem (scalar_mem_primeFormUnitary_idGram h hμn) hB'U
  have hiso := isometry_of_mem_primeFormUnitary h hX₀U
  have hX₀m : (X₀ : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hX₀p, Units.val_one]
  have hdet := det_eq_one_of_isometry h hp hpq hiso hX₀m
  set X : ↥(unitarySU 2 f K n) := ⟨X₀, (mem_unitarySU_iff_isometry h).mpr ⟨hdet, hiso⟩⟩ with hX
  have hbX : (b, X₀) ∈ SUTorus.suPairs ψ₁ := by
    have := (SUTorus.suPairs ψ₁).mul_mem (SUTorus.one_scalar_mem_suPairs ψ₁ μ⁻¹) hB'
    rwa [Prod.mk_mul_mk, one_mul] at this
  refine ⟨X, Subtype.ext hX₀p, ?_⟩
  have hmem : (ψ₁ X)⁻¹ * b ∈ Subgroup.centralizer (ψ₁.range : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    have h2 := hbX.2 u (X * u * X⁻¹) rfl
    rw [map_mul, map_mul, map_inv] at h2
    calc ψ₁ u * ((ψ₁ X)⁻¹ * b) = (ψ₁ X)⁻¹ * (ψ₁ X * ψ₁ u * (ψ₁ X)⁻¹) * b := by group
      _ = (ψ₁ X)⁻¹ * (b * ψ₁ u * b⁻¹) * b := by rw [h2]
      _ = (ψ₁ X)⁻¹ * b * ψ₁ u := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem

end SUTB

end CFSG.StandardType
