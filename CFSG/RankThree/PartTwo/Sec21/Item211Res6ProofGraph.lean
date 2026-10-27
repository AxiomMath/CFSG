module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofGraphConj
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofOrthFrame
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofTriv

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section Graph

variable {K : Type} [Field K]

theorem exists_graph_form [Finite K] {x : MulAut (projectiveSL 3 K)}
    (hx : x ∉ semilinearAutGroup 3 K) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K), x = conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K := by
  obtain ⟨σ, A, ε, hε, rfl⟩ := ProjectivePlane.exists_standard_form K 3 (le_refl 3) x
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · exfalso
    apply hx
    rw [pow_zero, mul_one]
    exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
      (fieldAut_mem_semilinearAutGroup _)
  · exact ⟨A, σ, by rw [pow_one]⟩

theorem conjAut_mul_fieldAut_mem (A : GL (Fin 3) K) (σ : K ≃+* K) :
    conjAut 3 K A * fieldAut 3 K σ ∈ semilinearAutGroup 3 K :=
  mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
    (fieldAut_mem_semilinearAutGroup _)

theorem mul_inv_mem_semilinear [Finite K] {t t' : MulAut (projectiveSL 3 K)}
    (ht : t ∉ semilinearAutGroup 3 K) (ht' : t' ∉ semilinearAutGroup 3 K) :
    t * t'⁻¹ ∈ semilinearAutGroup 3 K := by
  obtain ⟨A, σ, rfl⟩ := exists_graph_form ht
  obtain ⟨B, τ, rfl⟩ := exists_graph_form ht'
  have e : conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K *
      (conjAut 3 K B * fieldAut 3 K τ * dualAut 3 K)⁻¹ =
      (conjAut 3 K A * fieldAut 3 K σ) * (conjAut 3 K B * fieldAut 3 K τ)⁻¹ := by group
  rw [e]
  exact mul_mem (conjAut_mul_fieldAut_mem A σ) (inv_mem (conjAut_mul_fieldAut_mem B τ))

theorem conj_mem_semilinear [Finite K] (x : MulAut (projectiveSL 3 K))
    {s : MulAut (projectiveSL 3 K)} (hs : s ∈ semilinearAutGroup 3 K) :
    x * s * x⁻¹ ∈ semilinearAutGroup 3 K := by
  by_cases hx : x ∈ semilinearAutGroup 3 K
  · exact mul_mem (mul_mem hx hs) (inv_mem hx)
  obtain ⟨A, σ, rfl⟩ := exists_graph_form hx
  obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.mp hs
  have hδ : dualAut 3 K * (conjAut 3 K B * fieldAut 3 K τ) * (dualAut 3 K)⁻¹ =
      conjAut 3 K (Matrix.GeneralLinearGroup.inverseTranspose B) * fieldAut 3 K τ := by
    rw [← mul_assoc, dualAut_mul_conjAut]
    simp only [mul_assoc]
    rw [← mul_assoc (dualAut 3 K) (fieldAut 3 K τ), dualAut_mul_fieldAut]
    group
  have e : conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K * (conjAut 3 K B * fieldAut 3 K τ) *
      (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K)⁻¹ =
      (conjAut 3 K A * fieldAut 3 K σ) *
        (dualAut 3 K * (conjAut 3 K B * fieldAut 3 K τ) * (dualAut 3 K)⁻¹) *
          (conjAut 3 K A * fieldAut 3 K σ)⁻¹ := by group
  rw [e, hδ]
  exact mul_mem (mul_mem (conjAut_mul_fieldAut_mem A σ) (conjAut_mul_fieldAut_mem _ τ))
    (inv_mem (conjAut_mul_fieldAut_mem A σ))

theorem map_tauOne (σ : K ≃+* K) :
    ((tauOne : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map σ = (tauOne : SL(3, K)) :=
  map_mOne σ

theorem map_tauTwo (σ : K ≃+* K) :
    ((tauTwo : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map σ = (tauTwo : SL(3, K)) :=
  map_mTwo σ

theorem tauOne_jZero : ((tauOne : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * jZero *
    ((tauOne : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ = jZero :=
  mOne_jZero

theorem tauTwo_jZero : ((tauTwo : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * jZero *
    ((tauTwo : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)ᵀ = jZero :=
  mTwo_jZero

theorem conj_fix_frame {P : GL (Fin 3) K}
    (hP : (P : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K)ᵀ = -jZero)
    (hPσ : ∀ σ : K ≃+* K, Matrix.GeneralLinearGroup.map (σ : K →+* K) P = P) {τ : SL(3, K)}
    (hτσ : ∀ σ : K ≃+* K, (τ : Matrix (Fin 3) (Fin 3) K).map σ = τ)
    (hτ : (τ : Matrix (Fin 3) (Fin 3) K) * jZero * (τ : Matrix (Fin 3) (Fin 3) K)ᵀ = jZero)
    (N : GL (Fin 3) K) (θ : K ≃+* K) (ε : ℕ) :
    (conjAut 3 K N * (fieldAut 3 K θ * dualAut 3 K ^ ε) * (conjAut 3 K N)⁻¹)
        (conjAut 3 K (N * P⁻¹) (proj 3 K τ)) = conjAut 3 K (N * P⁻¹) (proj 3 K τ) := by
  have hfix := fieldAut_dualAut_pow_frame hP hPσ hτσ hτ θ ε
  rw [map_mul]
  change conjAut 3 K N ((fieldAut 3 K θ * dualAut 3 K ^ ε) ((conjAut 3 K N)⁻¹
    (conjAut 3 K N (conjAut 3 K P⁻¹ (proj 3 K τ))))) =
      conjAut 3 K N (conjAut 3 K P⁻¹ (proj 3 K τ))
  rw [MulAut.inv_apply, MulEquiv.symm_apply_apply, hfix]

theorem eq_one_of_semilinear [Finite K] {T : Subgroup (MulAut (projectiveSL 3 K))}
    (hT2 : IsPGroup 2 T) (hR : T ⊓ innP K = ⊥) {t : MulAut (projectiveSL 3 K)} (ht : t ∈ T)
    (htS : t ∈ semilinearAutGroup 3 K)
    (h1 : ProjectivePlane.linearFieldPart K (le_refl 3) t = 1) : t = 1 := by
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp htS
  have hσ : σ = 1 := by
    have := ProjectivePlane.linearFieldPart_eq (K := K) (le_refl 3) (A := A) (σ := σ)
      (Nat.zero_le 1)
    rw [pow_zero, mul_one] at this
    rw [← this]
    exact h1
  subst hσ
  exact eq_one_of_mem_linearAutGroup hT2 hR ht (by rw [map_one, mul_one])

theorem exists_semilinear_gen [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {T : Subgroup (MulAut (projectiveSL 3 K))} (hT2 : IsPGroup 2 T) (hR : T ⊓ innP K = ⊥) :
    ∃ s ∈ T, s ∈ semilinearAutGroup 3 K ∧
      (∃ (H : GL (Fin 3) K) (ρ : K ≃+* K),
        s = conjAut 3 K H * fieldAut 3 K ρ * (conjAut 3 K H)⁻¹) ∧
      ∀ t ∈ T, t ∈ semilinearAutGroup 3 K → ∃ j : ℤ, t = s ^ j := by
  classical
  set S := semilinearAutGroup 3 K with hSdef
  set φ := ProjectivePlane.linearFieldPart K (le_refl 3) with hφ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf⟩ := FiniteField.card K p
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic (Fact.out : p.Prime) K
    (by rw [Nat.card_eq_fintype_card, hf.2])).2
  obtain ⟨⟨σ₁, hσ₁⟩, hgen⟩ := IsCyclic.exists_generator (α := (T ⊓ S).map φ)
  obtain ⟨s, ⟨hsT, hsS⟩, rfl⟩ := hσ₁
  refine ⟨s, hsT, hsS, ?_, fun t ht htS => ?_⟩
  · obtain ⟨B, ρ, hsB⟩ := mem_semilinearAutGroup_iff.mp hsS
    have hφs : φ s = ρ := by
      rw [hsB]
      have := ProjectivePlane.linearFieldPart_eq (K := K) (le_refl 3) (A := B) (σ := ρ)
        (Nat.zero_le 1)
      rwa [pow_zero, mul_one] at this
    have : Finite (K ≃+* K) := CFSG.GH74.GLS.IVK.instFiniteRingEquiv K
    have hρh : ρ ^ orderOf ρ = 1 := pow_orderOf_eq_one ρ
    have hsh : s ^ orderOf ρ = 1 := eq_one_of_semilinear hT2 hR (T.pow_mem hsT _)
      (S.pow_mem hsS _) (by rw [map_pow, hφs, hρh])
    rw [hsB, ProjectivePlane.conjAut_mul_fieldAut_pow, hρh, map_one, mul_one] at hsh
    obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq (hsh.trans (map_one _).symm)
    rw [mul_one] at hc
    obtain ⟨H, d, hHd⟩ := CFSG.StandardType.OrdPRest.exists_hilbert90 (n := 3) (by norm_num) rfl
      B hc
    exact ⟨H, ρ, by rw [hsB, CFSG.StandardType.OrdPRest.conjAut_mul_fieldAut_eq_conj' B H ρ d hHd]⟩
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨φ t, ⟨t, ⟨ht, htS⟩, rfl⟩⟩)
    refine ⟨j, ?_⟩
    have h1 : φ s ^ j = φ t := by simpa using congrArg Subtype.val hj
    have h2 := eq_one_of_semilinear hT2 hR (T.mul_mem (T.inv_mem (T.zpow_mem hsT j)) ht)
      (S.mul_mem (S.inv_mem (S.zpow_mem hsS j)) htS)
      (by rw [map_mul, map_inv, map_zpow, h1, inv_mul_cancel])
    calc t = s ^ j * ((s ^ j)⁻¹ * t) := by group
      _ = s ^ j := by rw [h2, mul_one]

theorem exists_conj_fieldAut_dualAut [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {T : Subgroup (MulAut (projectiveSL 3 K))} (hT2 : IsPGroup 2 T)
    (hR : T ⊓ innP K = ⊥) {t₀ : MulAut (projectiveSL 3 K)} (ht₀ : t₀ ∈ T)
    (ht₀s : t₀ ∉ semilinearAutGroup 3 K) :
    ∃ N : GL (Fin 3) K, ∀ t ∈ T, ∃ (θ : K ≃+* K) (ε : ℕ),
      t = conjAut 3 K N * (fieldAut 3 K θ * dualAut 3 K ^ ε) * (conjAut 3 K N)⁻¹ := by
  classical
  set S := semilinearAutGroup 3 K with hSdef
  obtain ⟨s, hsT, hsS, ⟨H, ρ, hsH⟩, hpow⟩ := exists_semilinear_gen hT2 hR
  have hcomm : t₀ * s = s * t₀ := by
    have hc1 := eq_one_of_semilinear hT2 hR (t := t₀ * s * t₀⁻¹ * s⁻¹)
      (T.mul_mem (T.mul_mem (T.mul_mem ht₀ hsT) (T.inv_mem ht₀)) (T.inv_mem hsT))
      (S.mul_mem (conj_mem_semilinear t₀ hsS) (S.inv_mem hsS)) (by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K
            (ProjectivePlane.linearFieldPart K (le_refl 3) t₀)
            (ProjectivePlane.linearFieldPart K (le_refl 3) s)]
        group)
    calc t₀ * s = (t₀ * s * t₀⁻¹ * s⁻¹) * s * t₀ := by group
      _ = s * t₀ := by rw [hc1, one_mul]
  have ht₀2S : t₀ ^ 2 ∈ S := by
    have := mul_inv_mem_semilinear (t' := t₀⁻¹) ht₀s
      (fun h' => ht₀s (by simpa using S.inv_mem h'))
    rwa [inv_inv, ← sq] at this
  obtain ⟨m, hm⟩ := hpow _ (T.pow_mem ht₀ 2) ht₀2S
  obtain ⟨a, ha⟩ : ∃ a, a = conjAut 3 K H := ⟨_, rfl⟩
  rw [← ha] at hsH
  obtain ⟨t', ht'⟩ : ∃ t', t' = a⁻¹ * t₀ * a := ⟨_, rfl⟩
  have ht's : t' ∉ S := fun h' => ht₀s (by
    have := conj_mem_semilinear a h'
    rwa [ht', show a * (a⁻¹ * t₀ * a) * a⁻¹ = t₀ by group] at this)
  obtain ⟨A', σ', ht'eq⟩ := exists_graph_form ht's
  have hfρ : fieldAut 3 K ρ = a⁻¹ * s * a := by rw [hsH]; group
  have hcomm' : conjAut 3 K A' * fieldAut 3 K σ' * dualAut 3 K * fieldAut 3 K ρ =
      fieldAut 3 K ρ * (conjAut 3 K A' * fieldAut 3 K σ' * dualAut 3 K) := by
    rw [← ht'eq, hfρ, ht']
    calc a⁻¹ * t₀ * a * (a⁻¹ * s * a) = a⁻¹ * (t₀ * s) * a := by group
      _ = a⁻¹ * (s * t₀) * a := by rw [hcomm]
      _ = a⁻¹ * s * a * (a⁻¹ * t₀ * a) := by group
  have hsq' : (conjAut 3 K A' * fieldAut 3 K σ' * dualAut 3 K) ^ 2 = fieldAut 3 K ρ ^ m := by
    rw [← ht'eq, hfρ, ht']
    have e1 : (a⁻¹ * t₀ * a) ^ 2 = a⁻¹ * t₀ ^ 2 * a := by rw [sq, sq]; group
    have e2 : (a⁻¹ * s * a) ^ m = a⁻¹ * s ^ m * a := by
      have := conj_zpow (a := a⁻¹) (b := s) (i := m)
      rwa [inv_inv] at this
    rw [e1, e2, hm]
  obtain ⟨k, hkρ, hk⟩ := exists_graph_conj hp2 hcomm' hsq'
  obtain ⟨b, hb⟩ : ∃ b, b = conjAut 3 K k := ⟨_, rfl⟩
  have hfk : b * fieldAut 3 K ρ * b⁻¹ = fieldAut 3 K ρ := by
    have e := fieldAut_mul_conjAut ρ k
    rw [hkρ, ← hb] at e
    rw [← e]
    group
  have hNab : conjAut 3 K (H * k) = a * b := by rw [map_mul, ha, hb]
  refine ⟨H * k, ?_⟩
  have hsN : s = a * b * fieldAut 3 K ρ * (a * b)⁻¹ := by
    rw [hsH]
    conv_lhs => rw [← hfk]
    group
  have ht₀N : t₀ = a * b * (fieldAut 3 K σ' * dualAut 3 K ^ 1) * (a * b)⁻¹ := by
    have e : t₀ = a * t' * a⁻¹ := by rw [ht']; group
    rw [e, ht'eq, hk, ← hb, pow_one]
    group
  have hsj : ∀ j : ℤ, s ^ j = a * b * fieldAut 3 K (ρ ^ j) * (a * b)⁻¹ := by
    intro j
    rw [hsN, conj_zpow, map_zpow]
  intro t ht
  rw [hNab]
  by_cases htS : t ∈ S
  · obtain ⟨j, rfl⟩ := hpow t ht htS
    exact ⟨ρ ^ j, 0, by rw [hsj, pow_zero, mul_one]⟩
  · obtain ⟨j, hj⟩ := hpow _ (T.mul_mem ht (T.inv_mem ht₀)) (mul_inv_mem_semilinear htS ht₀s)
    refine ⟨ρ ^ j * σ', 1, ?_⟩
    have e : t = t * t₀⁻¹ * t₀ := by group
    rw [e, hj, hsj, ht₀N, map_mul (fieldAut 3 K)]
    group

theorem outerCentConcl_of_not_semilinear [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp3 : 3 < p) {T : Subgroup (MulAut (projectiveSL 3 K))} (hT2 : IsPGroup 2 T)
    (hR : T ⊓ innP K = ⊥) {t₀ : MulAut (projectiveSL 3 K)} (ht₀ : t₀ ∈ T)
    (ht₀s : t₀ ∉ semilinearAutGroup 3 K) : OuterCentConcl (innP K) T := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨N, hform⟩ := exists_conj_fieldAut_dualAut hp2 hT2 hR ht₀ ht₀s
  obtain ⟨P, hPP, hPσ⟩ := exists_orthFrame (K := K) hp2
  refine outerCentConcl_of_fix_conj hp3 (N * P⁻¹) fun t ht => ?_
  obtain ⟨θ, ε, rfl⟩ := hform t ht
  exact ⟨conj_fix_frame (τ := tauOne) hPP hPσ map_tauOne tauOne_jZero N θ ε,
    conj_fix_frame (τ := tauTwo) hPP hPσ map_tauTwo tauTwo_jZero N θ ε⟩

end Graph

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
