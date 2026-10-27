module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3ParO
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
open scoped Pointwise Matrix

private theorem s16t3_map_mem_singularFlags {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {k : ℕ} {W : Fin k → Submodule K V}
    (hW : W ∈ CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularFlags Q k)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (fun i => (W i).map (g : V →ₗ[K] V)) ∈
      CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularFlags Q k := by
  rw [CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_singularFlags] at hW ⊢
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i x hx => ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hW.1 i
  · exact Submodule.map_mono (hW.2.1 hij)
  · rw [Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hgy : Q ((g : V →ₗ[K] V) y) = Q y := hg y
    rw [hgy]
    exact hW.2.2 i y hy

private theorem s16t3_symm_mem_tailFlag_iff {K : Type} [Field K] {r : ℕ}
    (v : Fin r ⊕ Fin r ⊕ Fin 2 → K) (i : ℕ) :
    (tailModelEquiv r K (Fin 2)).symm v ∈ tailFlag K (Fin 2 → K) r i ↔
      v ∈ s16t3Flag (k := r) (R := Fin r ⊕ Fin 2) (K := K) i := by
  rw [mem_tailFlag_iff, CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.mem_flag]
  have c1 : ∀ j : Fin r,
      ((tailModelEquiv r K (Fin 2)).symm v).1 (Sum.inr j) = v (Sum.inr (Sum.inl j)) :=
    fun _ => rfl
  have c2 : ∀ j : Fin r,
      ((tailModelEquiv r K (Fin 2)).symm v).1 (Sum.inl j) = v (Sum.inl j) :=
    fun _ => rfl
  have c3 : ∀ j : Fin 2,
      ((tailModelEquiv r K (Fin 2)).symm v).2 j = v (Sum.inr (Sum.inr j)) :=
    fun _ => rfl
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ c hc
    rcases c with j | j
    · by_cases hj : (j : ℕ) < i
      · exact ⟨j, rfl, hj⟩
      · exact absurd (by rw [← c2 j]; exact h2 j (not_lt.1 hj)) hc
    · rcases j with j | j
      · exact absurd (by rw [← c1 j]; exact h1 j) hc
      · have h3j : ((tailModelEquiv r K (Fin 2)).symm v).2 j = 0 := by
          simpa using congrFun h3 j
        exact absurd (by rw [← c3 j]; exact h3j) hc
  · intro hv
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j
      by_contra h
      obtain ⟨l, hl, -⟩ := hv (Sum.inr (Sum.inl j)) h
      exact absurd hl (by simp)
    · intro j hj
      by_contra h
      obtain ⟨l, hl, hlt⟩ := hv (Sum.inl j) h
      simp only [Sum.inl.injEq] at hl
      omega
    · funext j
      show ((tailModelEquiv r K (Fin 2)).symm v).2 j = 0
      by_contra hj
      have hvj : v (Sum.inr (Sum.inr j)) ≠ 0 := fun h0 => hj (by rw [c3 j, h0])
      obtain ⟨l, hl, -⟩ := hv (Sum.inr (Sum.inr j)) hvj
      exact absurd hl (by simp)

private theorem s16t3_map_mem_tailFlag_iff {K : Type} [Field K] {r : ℕ}
    (w : (Fin r ⊕ Fin r → K) × (Fin 2 → K)) (i : ℕ) :
    tailModelEquiv r K (Fin 2) w ∈ s16t3Flag (k := r) (R := Fin r ⊕ Fin 2) (K := K) i ↔
      w ∈ tailFlag K (Fin 2 → K) r i := by
  have h := s16t3_symm_mem_tailFlag_iff (K := K) (r := r) (tailModelEquiv r K (Fin 2) w) i
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

theorem s16t3_omminus_fix {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {X : Subgroup (Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)}
    (hX : IsPGroup 2 ↥X)
    (hXQ : ∀ x ∈ X, ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K,
      StatedQuadMinus m K b c (Matrix.mulVec (x : Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
        (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) v) = StatedQuadMinus m K b c v) :
    ∃ g ∈ StatedOmega (StatedQuadMinus m K b c),
      ∀ x ∈ X, g⁻¹ * x * g ∈ s16t3Borel (StatedQuadMinus m K b c) (m - 1) := by
  have hK2 : IsF2 K := IsF2.of_natCard_eq_two hK
  haveI : IsF2 K := hK2
  have hc : c = 1 := by
    apply IsF2.eq_one_of_ne_zero
    intro hc0
    apply hbc 0
    rw [hc0]
    ring
  have hb : b = 1 := by
    apply IsF2.eq_one_of_ne_zero
    intro hb0
    apply hbc 1
    rw [hb0, hc]
    calc (1 : K) ^ 2 + 0 * 1 + 1 = 1 + 1 := by ring
      _ = 0 := IsF2.one_add_one
  subst hb
  subst hc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero IsF2.two_eq_zero
  let qA : QuadraticForm K (Fin 2 → K) := minusTailForm K 1 1
  let Q : QuadraticForm K ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) :=
    quadTail (m - 1) qA
  let e : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := tailModelEquiv (m - 1) K (Fin 2)
  have hφ : ∀ w, StatedQuadMinus m K 1 1 (e w) = Q w := by
    intro w
    have h := (minusTailIsometry m K 1 1).map_app' w
    rw [coe_quadMinus m K 1 1] at h
    exact h
  have hφq : ∀ w, quadMinus m K 1 1 (e w) = Q w := by
    intro w
    rw [coe_quadMinus m K 1 1]
    exact hφ w
  let ψ : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K ≃*
      (((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K))) :=
    (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).trans (conjAut e).symm
  have ψ_apply : ∀ (A : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
      (w : (Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)),
      ψ A w = e.symm (A *ᵥ e w) := fun _ _ => rfl
  have mulVec_e : ∀ (B : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K)
      (w : (Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)), B *ᵥ e w = e (ψ B w) := by
    intro B w
    rw [ψ_apply B w, LinearEquiv.apply_symm_apply]
  let X' : Subgroup (((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K))) := X.map ψ.toMonoidHom
  have hX' : IsPGroup 2 ↥X' := hX.map ψ.toMonoidHom
  have hX'O : X' ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    show Q (ψ A w) = Q w
    calc Q (ψ A w) = Q (e.symm (A *ᵥ e w)) := by rw [ψ_apply A w]
      _ = StatedQuadMinus m K 1 1 (A *ᵥ e w) := by
            rw [← hφ (e.symm (A *ᵥ e w)), LinearEquiv.apply_symm_apply]
      _ = StatedQuadMinus m K 1 1 (e w) := hXQ A hA (e w)
      _ = Q w := hφ w
  let s₀ : Fin (m - 1) → Submodule K ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) :=
    stdFlag K (Fin 2 → K) (m - 1)
  have hani : qA.Anisotropic := anisotropic_minusTailForm irreducible_one_one
  have hreg : (QuadraticMap.polarBilin qA).Nondegenerate :=
    nondegenerate_minusTailForm irreducible_one_one
  have hAne : ∃ a : Fin 2 → K, a ≠ 0 := ⟨fun _ => 1, by
    intro h
    exact one_ne_zero (congrFun h 0)⟩
  have horbit : MulAction.orbit (orthElementaryGroup Q) s₀ =
      CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularFlags Q (m - 1) :=
    orbit_stdFlag hani hAne
  have hodd : ¬ 2 ∣ Nat.card (MulAction.orbit (orthElementaryGroup Q) s₀) := by
    rw [horbit]
    exact not_dvd_card_singularFlags (A := Fin 2 → K) (r := m - 1) (qA := qA) hani hreg
      (by rw [finrank_fin_two_fun]; norm_num)
  have hinv : ∀ x ∈ X', ∀ t ∈ MulAction.orbit (orthElementaryGroup Q) s₀,
      x • t ∈ MulAction.orbit (orthElementaryGroup Q) s₀ := by
    intro x hx t ht
    rw [horbit] at ht ⊢
    have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hX'O hx
    show (fun i => (t i).map (x : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) →ₗ[K]
      ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)))) ∈
      CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularFlags Q (m - 1)
    exact s16t3_map_mem_singularFlags ht hxO
  obtain ⟨g, hgE, hgstab⟩ := s16t3_exists_conj_stabilizer (s₀ := s₀)
    (E := orthElementaryGroup Q) (X := X') hX' hodd hinv
  let g' : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K := ψ.symm g
  have hψg' : ψ g' = g := MulEquiv.apply_symm_apply ψ g
  have hOmega : StatedOmega (StatedQuadMinus m K 1 1) =
      (orthElementaryGroup Q).comap ψ.toMonoidHom := by
    rw [statedOmega_eq_comap_conjAut e hφ,
      commutator_orthogonalGroup_eq_of_isometry_minus (Q := Q) (m := m) (by omega) e hφq]
    rfl
  refine ⟨g', ?_, ?_⟩
  · rw [hOmega, Subgroup.mem_comap]
    show ψ g' ∈ orthElementaryGroup Q
    rw [hψg']
    exact hgE
  · intro x hx
    have hx' : ψ x ∈ X' := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hstab := hgstab (ψ x) hx'
    rw [MulAction.mem_stabilizer_iff] at hstab
    let B : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K := g'⁻¹ * x * g'
    change B ∈ s16t3Borel (StatedQuadMinus m K 1 1) (m - 1)
    let y : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) := g⁻¹ * ψ x * g
    have hy_smul : y • s₀ = s₀ := hstab
    have hψB : ψ B = y := by
      show ψ (g'⁻¹ * x * g') = g⁻¹ * ψ x * g
      simp only [map_mul, map_inv, hψg']
    have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthElementaryGroup_le Q hgE
      have hxO : ψ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hX'O hx'
      exact mul_mem (mul_mem (inv_mem hgO) hxO) hgO
    have hyQ : ∀ w, Q (y w) = Q w := fun w =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hyO w
    have hmap : ∀ j : Fin (m - 1),
        (s₀ j).map (y : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) →ₗ[K]
          ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K))) = s₀ j := by
      intro j
      have h := congrFun hy_smul j
      show (s₀ j).map (y : ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K)) →ₗ[K]
        ((Fin (m - 1) ⊕ Fin (m - 1) → K) × (Fin 2 → K))) = s₀ j
      exact h
    have hyflag : ∀ i, 1 ≤ i → i ≤ m - 1 → ∀ w ∈ tailFlag K (Fin 2 → K) (m - 1) i,
        y w ∈ tailFlag K (Fin 2 → K) (m - 1) i := by
      intro i hi1 hir w hw
      have hj : i - 1 < m - 1 := by omega
      have hji : ((⟨i - 1, hj⟩ : Fin (m - 1)) : ℕ) + 1 = i := by
        simp only [Fin.val_mk]; omega
      have h := hmap ⟨i - 1, hj⟩
      have hw' : w ∈ s₀ ⟨i - 1, hj⟩ := by
        show w ∈ tailFlag K (Fin 2 → K) (m - 1) (((⟨i - 1, hj⟩ : Fin (m - 1)) : ℕ) + 1)
        rw [hji]
        exact hw
      have hyw : y w ∈ s₀ ⟨i - 1, hj⟩ := by
        rw [← h]
        exact Submodule.mem_map.mpr ⟨w, hw', rfl⟩
      show y w ∈ tailFlag K (Fin 2 → K) (m - 1) i
      rw [← hji]
      exact hyw
    have hB_apply : ∀ v, B *ᵥ v = e (y (e.symm v)) := by
      intro v
      have h := mulVec_e B (e.symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      rw [hψB] at h
      exact h
    rw [s16t3Borel]
    refine ⟨fun v => ?_, fun i hi1 hir v hv => ?_⟩
    · calc StatedQuadMinus m K 1 1 (B *ᵥ v)
          = StatedQuadMinus m K 1 1 (e (y (e.symm v))) := by rw [hB_apply v]
        _ = Q (y (e.symm v)) := hφ _
        _ = Q (e.symm v) := hyQ _
        _ = StatedQuadMinus m K 1 1 (e (e.symm v)) := (hφ _).symm
        _ = StatedQuadMinus m K 1 1 v := by rw [LinearEquiv.apply_symm_apply]
    · have h1 : e.symm v ∈ tailFlag K (Fin 2 → K) (m - 1) i :=
        (s16t3_symm_mem_tailFlag_iff (K := K) (r := m - 1) v i).2 hv
      have h2 : y (e.symm v) ∈ tailFlag K (Fin 2 → K) (m - 1) i := hyflag i hi1 hir _ h1
      rw [hB_apply v]
      exact (s16t3_map_mem_tailFlag_iff (K := K) (r := m - 1) (y (e.symm v)) i).2 h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
