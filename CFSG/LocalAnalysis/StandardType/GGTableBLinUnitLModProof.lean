module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLModPSL

public section

namespace CFSG.StandardType.LinUnitL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K]

@[expose] def heartSet {L' : Type} [Group L'] (φ' : SpecialLinearGroup (Fin d) K →* L') (p : ℕ) :
    Set (MulAut L') :=
  {a | ∃ (D : SpecialLinearGroup (Fin d) K) (u : Fin d → K),
    (D : Matrix (Fin d) (Fin d) K) = diagonal u ∧ (∀ i, u i ^ p = 1) ∧ a = MulAut.conj (φ' D)}

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem card_le_mul_card_heart (hp : p.Prime) (hd : 0 < d) {L' : Type} [Group L'] [Finite L']
    {φ' : SpecialLinearGroup (Fin d) K →* L'} (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hAp : ∀ a ∈ A, a ^ p = 1) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) :
    Nat.card A ≤ p * Nat.card (Subgroup.closure (heartSet φ' p)) := by
  classical
  have := Fact.mk hp
  choose tA htA' using fun a : A => hdiag a a.2
  have htA : ∀ a : A, ActsDiag φ' a (tA a) := htA'
  set i0 : Fin d := ⟨0, hd⟩
  have hne : ∀ (a : A) k, tA a k ≠ 0 := fun a k => (htA a).ne_zero k
  have hrat : ∀ (a : A) (t : Fin d → K), ActsDiag φ' a t →
      ∀ k, tA a k * (tA a i0)⁻¹ = t k * (t i0)⁻¹ := by
    intro a t ht k
    by_cases hk : k = i0
    · rw [hk, mul_inv_cancel₀ (hne a i0), mul_inv_cancel₀ (ht.ne_zero i0)]
    · exact (htA a).ratio hφker ht hk
  let χf : A → Kˣ := fun a => Units.mk0 (∏ k, tA a k * (tA a i0)⁻¹)
    (Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (hne a k) (inv_ne_zero (hne a i0)))
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    apply Units.ext
    simp only [χf, Units.val_mk0, Units.val_mul]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hrat (a * b) _ ((htA a).mul (htA b)) k, mul_inv, mul_mul_mul_comm]
  let χ : A →* Kˣ := MonoidHom.mk' χf hχmul
  have hrange : χ.range ≤ rootsOfUnity p K := by
    rintro _ ⟨a, rfl⟩
    rw [mem_rootsOfUnity']
    change (∏ k, tA a k * (tA a i0)⁻¹) ^ p = 1
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun k _ => (htA a).ratio_pow hφker (hAp a a.2) k i0
  have hker : ∀ a : A, χ a = 1 → (a : MulAut L') ∈ heartSet φ' p := by
    intro a ha
    have h1 : ∏ k, tA a k * (tA a i0)⁻¹ = 1 := by
      have := congrArg Units.val ha
      simpa [χ, χf] using this
    refine ⟨diagSLOf _ h1, _, coe_diagSLOf _ _,
      fun k => (htA a).ratio_pow hφker (hAp a a.2) k i0, ?_⟩
    exact (ActsDiag.mul_const (htA a) (inv_ne_zero (hne a i0))).unique hφ's
      (actsDiag_conj (coe_diagSLOf _ h1))
  have hc1 := TableB.card_range_mul_card_ker χ
  have hc2 : Nat.card χ.range ≤ p := (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity K p)
  have hc3 : Nat.card χ.ker ≤ Nat.card (Subgroup.closure (heartSet φ' p)) := by
    have hle : χ.ker.map A.subtype ≤ Subgroup.closure (heartSet φ' p) := by
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.subset_closure (hker a ha)
    calc Nat.card χ.ker = Nat.card (χ.ker.map A.subtype) :=
          (Subgroup.card_map_of_injective A.subtype_injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  rw [← hc1]
  exact Nat.mul_le_mul hc2 hc3

omit [CharP K 2] in
theorem conj_mem_heart_of_normalizes (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1)
    (hd : 5 ≤ d) {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}
    (hφ's : Function.Surjective φ') (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) {n : L'}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) {h : MulAut L'}
    (hh : h ∈ heartSet φ' p) : MulAut.conj n * h * (MulAut.conj n)⁻¹ ∈ heartSet φ' p := by
  classical
  obtain ⟨g, rfl⟩ := hφ's n
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hpv : ∀ k l : Fin d, ∀ m, ggPairVec k l ζ m ^ p = 1 := by
    intro k l m
    rw [ggPairVec_apply]
    split_ifs <;> simp [mul_pow, inv_pow, hζ.pow_eq_one]
  have hconj : ∀ s : SpecialLinearGroup (Fin d) K,
      MulAut.conj (φ' (g * s * g⁻¹)) =
        MulAut.conj (φ' g) * MulAut.conj (φ' s) * (MulAut.conj (φ' g))⁻¹ := by
    intro s
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D' : Fin d → K,
      ((SpecialLinearGroup.toGL g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        diagonal (rootT ζ i j) =
      diagonal D' * ((SpecialLinearGroup.toGL g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    set Dij := diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij) with hDij
    set X := g * Dij * g⁻¹ with hX
    have hXA : MulAut.conj (φ' X) ∈ A := by
      have h1 : MulAut.conj (φ' Dij) ∈ A :=
        conj_mem_of_selfCent hsc hdiag (coe_diagSLOf _ _) (rootT_pow hζ.pow_eq_one i j)
      rw [hX, hconj]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp h1
    have hXd : (X : Matrix (Fin d) (Fin d) K).IsDiag :=
      isDiag_of_conj_comm hφker hd hζinv fun k l _ D hD =>
        TableB.IsElemAbelian.comm hA hXA (conj_mem_of_selfCent hsc hdiag hD (hpv k l))
    refine ⟨fun k => (X : Matrix (Fin d) (Fin d) K) k k, ?_⟩
    have e1 : X * g = g * Dij := by rw [hX]; group
    have e2 := congrArg (fun y : SpecialLinearGroup (Fin d) K => (y : Matrix (Fin d) (Fin d) K)) e1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at e2
    have hXm : (X : Matrix (Fin d) (Fin d) K) =
        diagonal fun k => (X : Matrix (Fin d) (Fin d) K) k k :=
      ((isDiag_iff_diagonal_diag _).mp hXd).symm
    rw [SpecialLinearGroup.coe_GL_coe_matrix, ← coe_diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij),
      ← hDij, ← e2]
    exact congrArg (· * (g : Matrix (Fin d) (Fin d) K)) hXm
  obtain ⟨π, hπ⟩ := exists_perm_mul_diagonal hζinv (SpecialLinearGroup.toGL g) hmono
  obtain ⟨D, u, hD, hu, rfl⟩ := hh
  refine ⟨g * D * g⁻¹, u ∘ π, ?_, fun i => hu (π i), (hconj D).symm⟩
  have h1 := hπ u
  rw [SpecialLinearGroup.coe_GL_coe_matrix] at h1
  have hgg : (g : Matrix (Fin d) (Fin d) K) * ((g⁻¹ : SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hD, h1,
    Matrix.mul_assoc, hgg, Matrix.mul_one]

theorem ggTableBModuleSCr_PSL (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) {r : ℕ}
    (hrd : d - 2 ≤ r) :
    GGTableBModuleSCr p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have := Fact.mk hp
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_card_sub_one hpK
  obtain ⟨φ', hφ's, hφker, hdiag⟩ := exists_model hp hpK hd hψ hker hperf hA hAI
    ((Nat.pow_le_pow_right hp.pos hrd).trans hr) h3
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  set H := Subgroup.closure (heartSet φ' p) with hH
  have hVA : heartSet φ' p ⊆ A := by
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_selfCent hsc hdiag hD hu
  have hHA : H ≤ A := (Subgroup.closure_le A).mpr hVA
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  refine ⟨H, _, hHA, ?_, card_le_mul_card_heart hp (by omega) hφ's hφker hAp hdiag, ?_,
    weyl_spec hφker hAp hdiag, ?_⟩
  · intro hbot
    set i0 : Fin d := ⟨0, by omega⟩
    set i1 : Fin d := ⟨1, by omega⟩
    set i2 : Fin d := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have hi02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    set D₁ := diagSLOf (rootT ζ i0 i1) (prod_rootT hζ0 h01)
    have he₁ : MulAut.conj (φ' D₁) ∈ H :=
      Subgroup.subset_closure ⟨D₁, _, coe_diagSLOf _ _, rootT_pow hζ.pow_eq_one i0 i1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at he₁
    have h2 : ActsDiag φ' (MulAut.conj (φ' D₁)) (fun _ => (1 : K)) := by
      rw [he₁]
      exact actsDiag_one
    have h3' := (actsDiag_conj (φ' := φ') (coe_diagSLOf _ (prod_rootT hζ0 h01))).ratio hφker h2 hi02
    rw [rootT_left, rootT_other ζ (Ne.symm hi02) (by simp [i2, i1, Fin.ext_iff])] at h3'
    simp only [inv_one, mul_one] at h3'
    exact hζ1 h3'
  · intro n hn h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx =>
      exact Subgroup.subset_closure
        (conj_mem_heart_of_normalizes hp hp2 hpK hd hφ's hφker hA hsc hdiag hn hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have e : MulAut.conj n * (x * y) * (MulAut.conj n)⁻¹ =
          (MulAut.conj n * x * (MulAut.conj n)⁻¹) * (MulAut.conj n * y * (MulAut.conj n)⁻¹) := by
        group
      rw [e]
      exact H.mul_mem hx hy
    | inv x _ hx =>
      have e : MulAut.conj n * x⁻¹ * (MulAut.conj n)⁻¹ =
          (MulAut.conj n * x * (MulAut.conj n)⁻¹)⁻¹ := by group
      rw [e]
      exact H.inv_mem hx
  · intro A' hA'A hA'ne hinv
    obtain ⟨⟨a₀, ha₀⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA'ne
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    refine (Subgroup.closure_le A').mpr ?_
    rintro _ ⟨D, u, hD, hu, rfl⟩
    exact conj_mem_of_invariant hp (by omega) hφ's hφker hA'A hsc hdiag hAp
      (fun σ a ha => hinv _ ⟨σ, rfl⟩ a ha) ha₀ ha₀1' hD hu

end CFSG.StandardType.LinUnitL

end
