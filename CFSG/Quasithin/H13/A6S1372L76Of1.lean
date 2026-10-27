module

public import CFSG.Quasithin.H13.A6S1372L76Od2

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular
  exists_sylow_unitriangular)
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Of

variable {F : Type} [Field F] [Finite F]

theorem exists_frobenius_pow [CharP F 2] (σ : F →+* F) : ∃ k : ℕ, ∀ x, σ x = x ^ 2 ^ k := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let _ : Algebra (ZMod 2) F := ZMod.algebra _ _
  let σ' : F →ₐ[ZMod 2] F :=
    { σ with
      commutes' := fun r => by
        have h := RingHom.ext_zmod (σ.comp (algebraMap (ZMod 2) F)) (algebraMap (ZMod 2) F)
        exact congrArg (fun f : ZMod 2 →+* F => f r) h }
  obtain ⟨k, hk⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod 2) F).2 σ'
  refine ⟨k.1, fun x => ?_⟩
  have h1 := congrArg (fun f : F →ₐ[ZMod 2] F => f x) hk
  simp only at h1
  show σ' x = _
  rw [← h1, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]

theorem ringHom_iterate_eq [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (σ : F →+* F) (x : F) :
    (⇑σ)^[n] x = x := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨k, hk⟩ := exists_frobenius_pow σ
  have hσ : ⇑σ = fun y => y ^ 2 ^ k := funext hk
  have hq : x ^ 2 ^ n = x := by
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hF] at h
  have key : ∀ m : ℕ, x ^ (2 ^ n) ^ m = x := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hq]
  rw [hσ, pow_iterate]
  show x ^ (2 ^ k) ^ n = x
  rw [← pow_mul, mul_comm, pow_mul]
  exact key k

theorem ringHom_comm [CharP F 2] (σ τ : F →+* F) (x : F) : σ (τ x) = τ (σ x) := by
  obtain ⟨k, hk⟩ := exists_frobenius_pow σ
  obtain ⟨j, hj⟩ := exists_frobenius_pow τ
  rw [hk, hj, hj, hk, ← pow_mul, ← pow_mul, mul_comm]

theorem ringHom_eq_id_of_iterate [CharP F 2] {n : ℕ} (hF : Nat.card F = 2 ^ n) (σ : F →+* F)
    {N : ℕ} (hN : ∀ x, (⇑σ)^[N] x = x) (hcop : Nat.Coprime N n) (x : F) : σ x = x := by
  have h1 : Function.IsPeriodicPt σ N x := hN x
  have h2 : Function.IsPeriodicPt σ n x := ringHom_iterate_eq hF σ x
  have h3 := h1.gcd h2
  rw [hcop] at h3
  exact h3

omit [Finite F] in
theorem exists_ringHom_of_smul {E : Type*} [AddCommGroup E] [Module F E] (f : E →+ E) {x₀ : E}
    (hx₀ : f x₀ ≠ 0) (hc : ∀ μ : F, ∃ c : F, ∀ x, f (μ • x) = c • f x) :
    ∃ σ : F →+* F, ∀ (μ : F) (x : E), f (μ • x) = σ μ • f x := by
  choose c hc using hc
  have hinj : Function.Injective fun d : F => d • f x₀ := smul_left_injective F hx₀
  refine ⟨{ toFun := c
            map_one' := hinj (show c 1 • f x₀ = (1 : F) • f x₀ by
              rw [← hc 1 x₀, one_smul, one_smul])
            map_mul' := fun μ ν => hinj (show c (μ * ν) • f x₀ = (c μ * c ν) • f x₀ by
              rw [← hc (μ * ν) x₀, mul_smul μ ν x₀, hc μ (ν • x₀), hc ν x₀,
                mul_smul (c μ) (c ν) (f x₀)])
            map_zero' := hinj (show c 0 • f x₀ = (0 : F) • f x₀ by
              rw [← hc 0 x₀, zero_smul F x₀, map_zero, zero_smul F (f x₀)])
            map_add' := fun μ ν => hinj (show c (μ + ν) • f x₀ = (c μ + c ν) • f x₀ by
              rw [← hc (μ + ν) x₀, add_smul μ ν x₀, map_add, hc μ x₀, hc ν x₀,
                add_smul (c μ) (c ν) (f x₀)]) }, hc⟩

theorem mul_self_ne_one_add [CharP F 2] {n : ℕ} (hn : Odd n) (hF : Nat.card F = 2 ^ n) (l : F) :
    l * l ≠ 1 + l := by
  classical
  have : Fintype F := Fintype.ofFinite F
  intro h
  have h0 : l ≠ 0 := by
    rintro rfl
    simp at h
  have h3 : l ^ 3 = 1 := by
    calc l ^ 3 = l * (l * l) := by ring
      _ = l * (1 + l) := by rw [h]
      _ = l + l * l := by ring
      _ = 1 + (l + l) := by rw [h]; ring
      _ = 1 := by rw [CharTwo.add_self_eq_zero, add_zero]
  have hq : l ^ (2 ^ n - 1) = 1 := by
    have h1 := FiniteField.pow_card_sub_one_eq_one l h0
    rwa [← Nat.card_eq_fintype_card, hF] at h1
  have hcop : Nat.Coprime 3 (2 ^ n - 1) :=
    Nat.Coprime.coprime_dvd_left (by norm_num) (A6L76Od.coprime_two_pow_sub_one hn 0)
  have h1 : l = 1 := by
    have h2 := pow_gcd_eq_one.2 ⟨h3, hq⟩
    rwa [hcop, pow_one] at h2
  rw [h1, mul_one, CharTwo.add_self_eq_zero] at h
  exact one_ne_zero h

theorem exists_conj_unitriangular [CharP F 2] {P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hP : IsPGroup 2 ↥P) (hodd : ¬ 2 ∣ P.index) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) F, ∀ x, x ∈ P ↔ g * x * g⁻¹ ∈ unitriangular 3 F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 3) F)
    (hP.toSylow hodd) Q
  have hmem : ∀ y, y ∈ (Q : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) ↔
      g⁻¹ * y * g ∈ P := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      IsPGroup.toSylow_coe]
    rfl
  refine ⟨g, fun x => ?_⟩
  rw [← hQ, hmem, show g⁻¹ * (g * x * g⁻¹) * g = x by group]

theorem exists_conj_unitriangular_stated [CharP F 2]
    {P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hP : IsPGroup 2 ↥P)
    (hodd : ¬ 2 ∣ P.index) :
    ∃ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F), ∀ x ∈ unitriangular 3 F,
      g⁻¹ * CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F x * g ∈ P := by
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F with he
  have hP₀ : IsPGroup 2 ↥(P.comap e.toMonoidHom) := hP.comap_of_injective _ e.injective
  have hodd₀ : ¬ 2 ∣ (P.comap e.toMonoidHom).index := by
    rwa [Subgroup.index_comap_of_surjective _ e.surjective]
  obtain ⟨g₀, hg₀⟩ := exists_conj_unitriangular hP₀ hodd₀
  refine ⟨e g₀, fun x hx => ?_⟩
  have h1 : g₀⁻¹ * x * g₀ ∈ P.comap e.toMonoidHom := by
    rw [hg₀, show g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ = x by group]
    exact hx
  have h2 : e (g₀⁻¹ * x * g₀) = (e g₀)⁻¹ * e x * e g₀ := by
    rw [map_mul, map_mul, map_inv]
  rw [← h2]
  exact h1

omit [Finite F] in
theorem transvection_mem_unitriangular {i j : Fin 3} (hij : i < j) (c : F) :
    Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) c ∈ unitriangular 3 F := by
  rw [mem_unitriangular]
  refine ⟨fun k l hkl => ?_, fun k => ?_⟩
  · rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      Matrix.one_apply_ne (ne_of_gt hkl), Matrix.single_apply]
    have : ¬ (i = k ∧ j = l) := fun ⟨h1, h2⟩ => by
      subst h1 h2
      exact absurd hij (not_lt.2 (le_of_lt hkl))
    simp [this]
  · rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
      Matrix.one_apply_eq, Matrix.single_apply]
    have : ¬ (i = k ∧ j = k) := fun ⟨h1, h2⟩ => by
      subst h1
      exact ne_of_lt hij h2.symm
    simp [this]

omit [Finite F] in
theorem transvection_mulVec (i j : Fin 3) (c : F) (v : Fin 3 → F) :
    (1 + Matrix.single i j c) *ᵥ v = v + Pi.single i (c * v j) := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  congr 1

omit [Finite F] in
theorem unitriangular_fix {v : Fin 3 → F}
    (hv : ∀ u ∈ unitriangular 3 F, (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) :
    v 1 = 0 ∧ v 2 = 0 := by
  have h1 := hv _ (transvection_mem_unitriangular (show (0 : Fin 3) < 1 by decide) 1)
  have h2 := hv _ (transvection_mem_unitriangular (show (1 : Fin 3) < 2 by decide) 1)
  rw [Matrix.SpecialLinearGroup.transvection_coe, transvection_mulVec] at h1 h2
  have e1 := congrFun h1 0
  have e2 := congrFun h2 1
  simp at e1 e2
  exact ⟨e1, e2⟩

theorem unitriangular_comm (hq : 2 < Nat.card F) {w v : Fin 3 → F} (hw : w ≠ 0)
    (hw12 : w 1 = 0 ∧ w 2 = 0)
    (hv : ∀ u ∈ unitriangular 3 F,
      (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v = 0 ∨ (u : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v = w) :
    v 1 = 0 ∧ v 2 = 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hw0 : w 0 ≠ 0 := by
    intro h0
    apply hw
    funext i
    fin_cases i
    · exact h0
    · exact hw12.1
    · exact hw12.2
  have hT : ∀ (i j : Fin 3) (hij : i < j) (c : F), Pi.single i (c * v j) = (0 : Fin 3 → F) ∨
      Pi.single i (c * v j) = w := by
    intro i j hij c
    have h := hv _ (transvection_mem_unitriangular hij c)
    rwa [Matrix.SpecialLinearGroup.transvection_coe, transvection_mulVec, add_sub_cancel_left]
      at h
  refine ⟨?_, ?_⟩
  ·
    by_contra h1
    obtain ⟨c, hc0, hc1⟩ : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun c _ => by
        by_cases h : c = 0
        · simp [h]
        · simp [hcon c h]
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
      have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
      omega
    have hA := hT 0 1 (by decide) 1
    have hB := hT 0 1 (by decide) c
    rw [one_mul] at hA
    rcases hA with hA | hA
    · exact h1 (by simpa using congrFun hA 0)
    · rcases hB with hB | hB
      · have := congrFun hB 0
        simp only [Pi.single_eq_same, Pi.zero_apply] at this
        exact (mul_ne_zero hc0 h1) this
      · have e1 := congrFun hA 0
        have e2 := congrFun hB 0
        simp only [Pi.single_eq_same] at e1 e2
        apply hc1
        have : c * v 1 = 1 * v 1 := by
          rw [one_mul]
          exact e2.trans e1.symm
        exact mul_right_cancel₀ h1 this
  · have hB := hT 1 2 (by decide) 1
    rw [one_mul] at hB
    rcases hB with hB | hB
    · simpa using congrFun hB 1
    · exfalso
      apply hw0
      rw [← hB]
      simp

end A6L76Of

end CFSG.Quasithin.H13.A6
