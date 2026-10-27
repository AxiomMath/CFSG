module

public import CFSG.LocalAnalysis.StandardType.GGLangSolvBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4StdKernel
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoKernel
import CFSG.LocalAnalysis.StandardType.GGLangSixRoot
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoClass
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoFrame

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSF4Std

private theorem j4cOrthNcard :
    ∀ e ∈ rts, (rts.filter (fun γ => decide (ipL γ e = 0))).length = 18 := by
  decide +kernel

theorem langRatDetectsTwoF4_class_cases
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {a : Fin Tag.F4.rank → Lˣ}
    (hap : ∀ j, a j ^ 3 = 1) (i : KernelComponent (rootCharHom a)) :
    (∀ γ, IsRoot Tag.F4 γ → rootChar a γ = 1) ∨
      ((componentRoots (rootCharHom a) i).ncard = 6 ∧
        ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ γ' ∈ componentRoots (rootCharHom a) i,
          iform γ γ = iform γ' γ' ∧ iform γ γ' ≠ 0) ∨
      ∃ e, IsRoot Tag.F4 e ∧
        componentRoots (rootCharHom a) i = {γ | IsRoot Tag.F4 γ ∧ iform γ e = 0} := by
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param hap
  by_cases hk0 : ∃ j, k j ≠ 0
  · by_cases hA : KernelA2A2 k
    · right; left
      obtain ⟨γ₀, hγ₀i⟩ := Quotient.exists_rep i
      rw [← hγ₀i, componentRoots_eq_sameLength hω3 hω1 hak hA (γ₀ := γ₀.1) γ₀.2]
      have hγ₀len : ipF4 γ₀.1 γ₀.1 = 2 ∨ ipF4 γ₀.1 γ₀.1 = 4 := by
        have h := iform_self_cases noG2_F4 γ₀.2.1
        rw [iform_F4] at h
        exact h
      have hset : ∀ c : ℤ, {γ : V4 | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = c} =
          {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 ∧ ipF4 γ γ = c} := by
        intro c
        ext γ
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq, kernelRoots_eq hω3 hω1 hak, Set.mem_setOf_eq]
        tauto
      rw [hset (ipF4 γ₀.1 γ₀.1)]
      refine ⟨?_, fun γ hγ γ' hγ' => ⟨?_, ?_⟩⟩
      · rcases hγ₀len with h2 | h4
        · rw [h2]; exact hA.card_short
        · rw [h4]; exact hA.card_long
      · rw [iform_F4, iform_F4, hγ.2.2, hγ'.2.2]
      · rw [iform_F4]
        exact hA.same γ γ' hγ.1 hγ'.1 hγ.2.1 hγ'.2.1 (by rw [hγ.2.2, hγ'.2.2])
    · right; right
      have hB : KernelB k := (classify_kernel2 k hk3 hk0).resolve_right hA
      rcases (classify_kernel k hk3 hk0).resolve_right hA with ⟨e, he, horth⟩
      obtain ⟨e', he', rfl⟩ := (mem_rts_iff e).1 he
      refine ⟨vec4 e', (mem_rts_iff _).2 ⟨e', he', rfl⟩, ?_⟩
      rw [componentRoots_eq_kernelRoots_of_kernelB hω3 hω1 hak hB i, kernelRoots_eq hω3 hω1 hak]
      have hkcard : {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0}.ncard = 18 := hB.card
      have hecard : {γ : V4 | IsRoot Tag.F4 γ ∧ iform γ (vec4 e') = 0}.ncard = 18 := by
        rw [ncard_roots_filter (fun γ : V4 => iform γ (vec4 e') = 0)]
        simp only [iform_F4, ipF4_vec4]
        exact j4cOrthNcard e' he'
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ ((finite_setOf_isRoot Tag.F4).subset
        fun γ hγ => hγ.1)
      · intro γ hγ
        exact ⟨hγ.1, by rw [iform_F4]; exact horth γ hγ.1 hγ.2⟩
      · rw [hecard, hkcard]
  · left
    intro γ hγ
    rw [rootChar_eq_pow_kdot hak γ]
    have hk : ∀ j, k j = 0 := fun j => not_not.1 (fun hj => hk0 ⟨j, hj⟩)
    have hzero : kdot k γ = 0 := by
      simp only [kdot, hk, Nat.cast_zero, zero_mul, add_zero]
    rw [hzero, zpow_zero]

private def j4cSixPt : Fin 3 → ℤ × ℤ := ![(1, 1), (0, 1), (0, 0)]

private def j4cSixQ (z w : ℤ × ℤ) : ℤ := 2 * z.1 * w.1 - z.1 * w.2 - z.2 * w.1 + 2 * z.2 * w.2

private def j4cSixR2 : Finset (ℤ × ℤ) := {(1, 0), (0, 1), (1, 1), (-1, 0), (0, -1), (-1, -1)}

private theorem j4cSixR2_card : j4cSixR2.card = 6 := by decide +kernel

private theorem j4cSixPt_sub_mem : ∀ x y : Fin 3, x ≠ y → j4cSixPt x - j4cSixPt y ∈ j4cSixR2 := by
  decide +kernel

private theorem j4cSixR2_exists :
    ∀ z ∈ j4cSixR2, ∃ a b : Fin 3, a ≠ b ∧ z = j4cSixPt a - j4cSixPt b := by
  decide +kernel

private theorem j4cSixQ_self : ∀ a b : Fin 3, a ≠ b →
    j4cSixQ (j4cSixPt a - j4cSixPt b) (j4cSixPt a - j4cSixPt b) = 2 := by
  decide +kernel

private theorem j4cSixRefl_pts : ∀ a b : Fin 3, a ≠ b → ∀ x y : Fin 3,
    (j4cSixPt x - j4cSixPt y) -
        j4cSixQ (j4cSixPt a - j4cSixPt b) (j4cSixPt x - j4cSixPt y) • (j4cSixPt a - j4cSixPt b) =
      j4cSixPt (Equiv.swap a b x) - j4cSixPt (Equiv.swap a b y) := by
  decide +kernel

private theorem j4cSixNoNeg : ∀ σ : Equiv.Perm (Fin 3), ¬ ∀ x y : Fin 3, x ≠ y →
    j4cSixPt (σ x) - j4cSixPt (σ y) = -(j4cSixPt x - j4cSixPt y) := by
  decide +kernel

private def j4cSixIota (γ δ : V4) : ℤ × ℤ →+ V4 :=
  (zmultiplesHom V4 γ).coprod (zmultiplesHom V4 δ)

private theorem j4cSixIota_apply (γ δ : V4) (z : ℤ × ℤ) : j4cSixIota γ δ z = z.1 • γ + z.2 • δ := by
  simp [j4cSixIota, AddMonoidHom.coprod_apply]

private theorem j4cSixIota_iform
    {γ δ : V4} {κ : ℤ} (hγγ : iform γ γ = 2 * κ) (hδδ : iform δ δ = 2 * κ)
    (hγδ : iform γ δ = -κ) (z w : ℤ × ℤ) :
    iform (j4cSixIota γ δ z) (j4cSixIota γ δ w) = κ * j4cSixQ z w := by
  rw [j4cSixIota_apply, j4cSixIota_apply]
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, hγγ, hδδ, hγδ,
    iform_comm δ γ, j4cSixQ]
  ring

private theorem j4cSixIota_injective
    {γ δ : V4} {κ : ℤ} (hκ : κ ≠ 0) (hγγ : iform γ γ = 2 * κ) (hδδ : iform δ δ = 2 * κ)
    (hγδ : iform γ δ = -κ) : Function.Injective (j4cSixIota γ δ) := by
  intro z z' h
  have h1 := j4cSixIota_iform hγγ hδδ hγδ z (1, 0)
  have h2 := j4cSixIota_iform hγγ hδδ hγδ z' (1, 0)
  have h3 := j4cSixIota_iform hγγ hδδ hγδ z (0, 1)
  have h4 := j4cSixIota_iform hγγ hδδ hγδ z' (0, 1)
  rw [h] at h1 h3
  have e1 := mul_left_cancel₀ hκ (h1.symm.trans h2)
  have e2 := mul_left_cancel₀ hκ (h3.symm.trans h4)
  simp only [j4cSixQ] at e1 e2
  exact Prod.ext (by omega) (by omega)

private theorem j4cSixRefl_iota
    {γ δ : V4} {κ : ℤ} (hκ : κ ≠ 0) (hγγ : iform γ γ = 2 * κ) (hδδ : iform δ δ = 2 * κ)
    (hγδ : iform γ δ = -κ) {z : ℤ × ℤ} (hz : IsRoot Tag.F4 (j4cSixIota γ δ z))
    (hzz : j4cSixQ z z = 2) (w : ℤ × ℤ) :
    rootReflection (j4cSixIota γ δ z) • j4cSixIota γ δ w =
      j4cSixIota γ δ (w - j4cSixQ z w • z) := by
  rw [rootReflection_smul hz]
  have hmul := corootPair_mul hz (j4cSixIota γ δ w)
  rw [j4cSixIota_iform hγγ hδδ hγδ, j4cSixIota_iform hγγ hδδ hγδ, hzz] at hmul
  have hc : corootPair (j4cSixIota γ δ z) (j4cSixIota γ δ w) = j4cSixQ z w := by
    have h2 : κ * 2 ≠ 0 := mul_ne_zero hκ two_ne_zero
    apply mul_right_cancel₀ h2
    rw [hmul]
    ring
  rw [hc, map_sub, map_zsmul]

private theorem j4cSixClass_eq
    {Ψ : Set V4} (hΨ : IsRootComponent Ψ) (h6 : Ψ.ncard = 6) {γ δ : V4} (hγ : γ ∈ Ψ)
    (hδ : δ ∈ Ψ) {κ : ℤ} (hκ : κ ≠ 0) (hγγ : iform γ γ = 2 * κ) (hδδ : iform δ δ = 2 * κ)
    (hγδ : iform γ δ = -κ) : Ψ = j4cSixIota γ δ '' (j4cSixR2 : Set (ℤ × ℤ)) := by
  have hι := j4cSixIota_injective hκ hγγ hδδ hγδ
  have hγr := hΨ.isRoot γ hγ
  have hsum : γ + δ ∈ Ψ := by
    have h := hΨ.reflection_mem δ hδ γ hγ
    have e10 : j4cSixIota γ δ (1, 0) = γ := by simp [j4cSixIota_apply]
    have e01 : j4cSixIota γ δ (0, 1) = δ := by simp [j4cSixIota_apply]
    have e11 : j4cSixIota γ δ (1, 1) = γ + δ := by simp [j4cSixIota_apply]
    have h1 : rootReflection γ • δ = γ + δ := by
      have h2 := j4cSixRefl_iota hκ hγγ hδδ hγδ (z := (1, 0)) (by rw [e10]; exact hγr)
        (by decide +kernel) (0, 1)
      have hq : j4cSixQ (1, 0) (0, 1) = -1 := by decide +kernel
      have e : ((0, 1) : ℤ × ℤ) - (-1 : ℤ) • (1, 0) = (1, 1) := by decide +kernel
      rw [e10, e01, hq, e, e11] at h2
      exact h2
    rwa [h1] at h
  have hsub : j4cSixIota γ δ '' (j4cSixR2 : Set (ℤ × ℤ)) ⊆ Ψ := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ j4cSixR2 := Finset.mem_coe.1 hz
    simp only [j4cSixR2, Finset.mem_insert, Finset.mem_singleton] at hz'
    rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [j4cSixIota_apply] using hγ
    · simpa [j4cSixIota_apply] using hδ
    · simpa [j4cSixIota_apply] using hsum
    · simpa [j4cSixIota_apply] using hΨ.neg_mem γ hγ
    · simpa [j4cSixIota_apply] using hΨ.neg_mem δ hδ
    · rw [j4cSixIota_apply]
      have h := hΨ.neg_mem _ hsum
      rw [neg_add_rev, add_comm] at h
      simpa using h
  have hfin : Ψ.Finite := Set.finite_of_ncard_pos (by omega)
  have hcard : (j4cSixIota γ δ '' (j4cSixR2 : Set (ℤ × ℤ))).ncard = 6 := by
    rw [Set.ncard_image_of_injective _ hι, Set.ncard_coe_finset, j4cSixR2_card]
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) hfin).symm

private theorem j4cSixNotInner
    {Ψ : Set V4} (hΨ : IsRootComponent Ψ) (h6 : Ψ.ncard = 6) {γ δ : V4} (hγ : γ ∈ Ψ)
    (hδ : δ ∈ Ψ) {κ : ℤ} (hκ : κ ≠ 0) (hγγ : iform γ γ = 2 * κ) (hδδ : iform δ δ = 2 * κ)
    (hγδ : iform γ δ = -κ) (σ : V4 → V4) (hσ : ∀ ε ∈ Ψ, σ ε = -ε) : ¬ twistInner Ψ σ := by
  rintro ⟨w, hw, hwσ⟩
  have hι := j4cSixIota_injective hκ hγγ hδδ hγδ
  have hΨeq := j4cSixClass_eq hΨ h6 hγ hδ hκ hγγ hδδ hγδ
  have hQ : ∀ w ∈ Subgroup.closure {s : WeylGroup Tag.F4 | ∃ ε ∈ Ψ, s = rootReflection ε},
      ∃ π : Equiv.Perm (Fin 3), ∀ x y : Fin 3,
        w • j4cSixIota γ δ (j4cSixPt x - j4cSixPt y) =
          j4cSixIota γ δ (j4cSixPt (π x) - j4cSixPt (π y)) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨ε, hε, rfl⟩ := hs
      have hε' := hε
      rw [hΨeq] at hε'
      obtain ⟨z, hz, rfl⟩ := hε'
      obtain ⟨a, b, hab, rfl⟩ := j4cSixR2_exists z (Finset.mem_coe.1 hz)
      refine ⟨Equiv.swap a b, fun x y => ?_⟩
      rw [j4cSixRefl_iota hκ hγγ hδδ hγδ (hΨ.isRoot _ hε) (j4cSixQ_self a b hab) _,
        j4cSixRefl_pts a b hab x y]
    | one => exact ⟨1, fun x y => by simp⟩
    | mul w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨π₁, hπ₁⟩ := h₁
      obtain ⟨π₂, hπ₂⟩ := h₂
      refine ⟨π₁ * π₂, fun x y => ?_⟩
      rw [mul_smul, hπ₂ x y, hπ₁]
      rfl
    | inv w _ h =>
      obtain ⟨π, hπ⟩ := h
      refine ⟨π⁻¹, fun x y => ?_⟩
      have h' := hπ (π⁻¹ x) (π⁻¹ y)
      have hx : π (π⁻¹ x) = x := π.apply_symm_apply x
      have hy : π (π⁻¹ y) = y := π.apply_symm_apply y
      rw [hx, hy] at h'
      rw [← h', inv_smul_smul]
  obtain ⟨π, hπ⟩ := hQ w hw
  refine j4cSixNoNeg π fun x y hxy => ?_
  apply hι
  have hmem : j4cSixIota γ δ (j4cSixPt x - j4cSixPt y) ∈ Ψ := by
    rw [hΨeq]
    exact ⟨_, Finset.mem_coe.2 (j4cSixPt_sub_mem x y hxy), rfl⟩
  rw [← hπ x y, ← hwσ _ hmem, hσ _ hmem, map_neg]

private theorem j4cSixSameLenAngle :
    ∀ g ∈ rts, ∀ d ∈ rts, ipL g g = ipL d d → ipL g d ≠ 0 → d ≠ g →
      d ≠ g.map (fun x => -x) → 2 * ipL g d = ipL g g ∨ 2 * ipL g d = - ipL g g := by
  decide +kernel

private theorem j4cSixVec4_neg (g : List ℤ) : vec4 (g.map (fun x => -x)) = -vec4 g := by
  funext i
  simp only [vec4, Pi.neg_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases g[(i : ℕ)]? <;> simp

private theorem j4cSix_iform_neg_right {τ : Tag}
    (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]
  ring

private theorem j4cSix_iform_neg_neg {τ : Tag}
    (x y : Fin τ.rank → ℤ) : iform (-x) (-y) = iform x y := by
  rw [← neg_one_smul ℤ x, ← neg_one_smul ℤ y, iform_smul_left, iform_smul_right]
  ring

private theorem j4cSixA2Pair
    {Ψ : Set V4} (hΨ : IsRootComponent Ψ) (h6 : Ψ.ncard = 6)
    (hn : ∀ γ ∈ Ψ, ∀ γ' ∈ Ψ, iform γ γ = iform γ' γ' ∧ iform γ γ' ≠ 0) :
    ∃ γ ∈ Ψ, ∃ δ ∈ Ψ, iform γ γ = iform δ δ ∧ 2 * iform γ δ = - iform γ γ := by
  obtain ⟨γ, hγ⟩ : Ψ.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨δ, hδ, hδγ, hδnγ⟩ : ∃ δ ∈ Ψ, δ ≠ γ ∧ δ ≠ -γ := by
    by_contra hcon
    push Not at hcon
    have hsub : Ψ ⊆ {γ, -γ} := fun δ hδ => by
      by_cases h : δ = γ
      · simp [h]
      · simp [hcon δ hδ h]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({γ, -γ} : Set V4).ncard ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    omega
  obtain ⟨hlen, hne⟩ := hn γ hγ δ hδ
  obtain ⟨g, hg, rfl⟩ := (mem_rts_iff γ).1 (hΨ.isRoot γ hγ)
  obtain ⟨d, hd, rfl⟩ := (mem_rts_iff δ).1 (hΨ.isRoot δ hδ)
  have hlen' : ipL g g = ipL d d := by simpa only [iform_F4, ipF4_vec4] using hlen
  have hne' : ipL g d ≠ 0 := by simpa only [iform_F4, ipF4_vec4] using hne
  rcases j4cSixSameLenAngle g hg d hd hlen' hne' (fun h => hδγ (by rw [h]))
      (fun h => hδnγ (by rw [h, j4cSixVec4_neg])) with h | h
  · refine ⟨vec4 g, hγ, -vec4 d, hΨ.neg_mem _ hδ, ?_, ?_⟩
    · rw [j4cSix_iform_neg_neg]
      exact hlen
    · rw [j4cSix_iform_neg_right, iform_F4, iform_F4, ipF4_vec4, ipF4_vec4]
      omega
  · exact ⟨vec4 g, hγ, vec4 d, hδ, hlen, by rw [iform_F4, iform_F4, ipF4_vec4, ipF4_vec4]; exact h⟩

theorem langRatDetectsTwoF4_langSmallSolv_of_ncard_six
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .F4 L p₀) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot .F4 γ → S.ρ γ = -γ)
    {a : Fin Tag.F4.rank → Lˣ} (ha : rootDiagUnit .F4 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (h6 : (componentRoots (rootCharHom a) i).ncard = 6)
    (hn : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ γ' ∈ componentRoots (rootCharHom a) i,
      iform γ γ = iform γ' γ' ∧ iform γ γ' ≠ 0) :
    LangSmallSolv S.D.q S.ρ (rootCharHom a) i := by
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) :=
    isRootComponent_componentRoots i
  have hρΨ : (S.ρ : V4 → V4) '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    ext γ
    constructor
    · rintro ⟨γ', hγ', rfl⟩
      rw [hρ γ' (hΨ.isRoot γ' hγ')]
      exact hΨ.neg_mem γ' hγ'
    · intro hγ
      refine ⟨-γ, hΨ.neg_mem γ hγ, ?_⟩
      rw [hρ (-γ) (IsRoot.neg (hΨ.isRoot γ hγ)), neg_neg]
  have hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one S ha i hρΨ
  obtain ⟨γ, hγ, δ, hδ, hlen, hrel⟩ := j4cSixA2Pair hΨ h6 hn
  have hκ : iform γ δ ≠ 0 := (hn γ hγ δ hδ).2
  have hγγ : iform γ γ = 2 * (-iform γ δ) := by omega
  have hδδ : iform δ δ = 2 * (-iform γ δ) := by omega
  have hni : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : V4 → V4)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]) := by
    rw [hs]
    exact j4cSixNotInner hΨ h6 hγ hδ (neg_ne_zero.2 hκ) hγγ hδδ (neg_neg _).symm _
      (fun ε hε => by simpa using hρ ε (hΨ.isRoot ε hε))
  right
  refine ⟨?_, ?_, h6⟩
  · rw [hs, hq, pow_one]
  · have hc := compRank_eq_two_of_ncard_eq_six hΨ h6
    unfold twistKind
    rw [if_neg hni]
    simp [hc, h6]

end CFSG.StandardType.LangRat
