module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKernelCount
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.TwE6RootKill

@[expose] def chainPt : Fin TwistTag.E6.tag.rank → Fin 6 → Fin TwistTag.E6.tag.rank → ℤ :=
  ![![![0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0],
      ![0, 1, 0, 1, 1, 1], ![1, 2, 2, 3, 2, 1]],
    ![![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, -1, -1, -2, -1, 0],
      ![0, -1, -1, -2, -1, -1], ![0, -1, -1, -2, -2, -1]],
    ![![0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 0],
      ![1, 1, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 1]],
    ![![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0], ![0, 0, -1, -1, -1, 0],
      ![0, 0, -1, -1, -1, -1], ![0, -1, -1, -2, -2, -1]],
    ![![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1], ![0, -1, -1, -2, -1, 0]],
    ![![0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0],
      ![1, 1, 1, 1, 0, 0], ![0, -1, -1, -2, -2, -1]]]

theorem chainPt_sub_mem : ∀ (j : Fin TwistTag.E6.tag.rank) (i i' : Fin 6), i < i' →
    List.ofFn (chainPt j i' - chainPt j i) ∈ TwistTag.E6.tag.artifactRoots := by
  decide +kernel

theorem iform_chainPt : ∀ (j : Fin TwistTag.E6.tag.rank) (i : Fin 6),
    iform (chainPt j i) (Pi.single j 1) = 0 := by
  decide +kernel

theorem exists_chain_of_isRoot
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) :
    ∃ P : Fin 6 → Fin TwistTag.E6.tag.rank → ℤ, (∀ i, iform (P i) β = 0) ∧
      ∀ i i', i < i' → IsRoot TwistTag.E6.tag (P i' - P i) := by
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hβ
  refine ⟨fun i => w • chainPt j i, fun i => ?_, fun i i' hii => ?_⟩
  · rw [iform_smul]
    exact iform_chainPt j i
  · rw [← smul_sub]
    exact CFSG.LieType.Chevalley.IsRoot.smul
      (isRoot_iff_mem_artifactRoots.2 (chainPt_sub_mem j i i' hii)) w

theorem corootTuple_sub {L : Type} [Field L] (γ γ' : Fin TwistTag.E6.tag.rank → ℤ) (ζ : Lˣ) :
    corootTuple (γ - γ') ζ = corootTuple γ ζ * (corootTuple γ' ζ)⁻¹ := by
  funext k
  simp only [corootTuple, Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib, zpow_sub]

theorem iform_sub_left_rk {τ : Tag} (x x' y : Fin τ.rank → ℤ) :
    iform (x - x') y = iform x y - iform x' y := by
  simp only [iform, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem rootChar_mul_inv_rk {τ : Tag} {L : Type} [Field L] (u v : Fin τ.rank → Lˣ)
    (β : Fin τ.rank → ℤ) : rootChar (u * v⁻¹) β = rootChar u β * (rootChar v β)⁻¹ := by
  simp only [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar, Pi.mul_apply,
    Pi.inv_apply, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]


theorem exists_corootTuple_mem_of_kills {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A) {p : ℕ} (hp : p.Prime)
    (hpK : ringChar K ≠ p) (hA : IsElemAbelian p A) (hcard : p ^ 5 < 6 * Nat.card A)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) (hkill : TwDataKills D β) :
    ∃ γ, IsRoot TwistTag.E6.tag γ ∧ iform γ β = 0 ∧
      ∃ ζ : (AlgebraicClosure K)ˣ, ζ ^ p = 1 ∧ ζ ≠ 1 ∧ ∃ x ∈ A,
        rootDiagUnit TwistTag.E6.tag (corootTuple γ ζ) =
          D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero ((p : ℕ) : K) := ⟨fun h => hpK (by
    rcases (Nat.dvd_prime hp).1 ((ringChar.spec K p).1 h) with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · exact h1)⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (AlgebraicClosure K)ˣ, IsPrimitiveRoot ζ p :=
    ⟨_, IsPrimitiveRoot.isUnit_unit hp.ne_zero hζ0⟩
  obtain ⟨P, hPβ, hProot⟩ := exists_chain_of_isRoot hβ
  set ι := baseChangeGL (algebraMap K (AlgebraicClosure K)) with hι
  choose a ha haβ using (hkill : ∀ x ∈ A, ∃ a : Fin TwistTag.E6.tag.rank →
    (AlgebraicClosure K)ˣ, rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ * ι (D.c * x * D.c⁻¹) * D.g0 ∧
      rootChar a β = 1)
  have hap : ∀ x (hx : x ∈ A), ∀ k, a x hx k ^ p = 1 := by
    intro x hx
    have hz : ι (D.c * x * D.c⁻¹) ^ p = 1 := by
      rw [← map_pow, conj_pow, hA.2 x hx, mul_one, mul_inv_cancel, map_one]
    have h1 : rootDiagUnit TwistTag.E6.tag (a x hx) ^ p = 1 := by
      rw [ha x hx]
      have hc := conj_pow (a := D.g0⁻¹) (b := ι (D.c * x * D.c⁻¹)) (i := p)
      rw [inv_inv] at hc
      rw [hc, hz, mul_one, inv_mul_cancel]
    have h2 : rootDiagUnit TwistTag.E6.tag (a x hx ^ p) = rootDiagUnit TwistTag.E6.tag 1 := by
      have hmp := map_pow (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)) (a x hx) p
      change rootDiagUnit TwistTag.E6.tag (a x hx ^ p) = rootDiagUnit TwistTag.E6.tag (a x hx) ^ p
        at hmp
      rw [hmp, h1, CFSG.LieType.Chevalley.rootDiagUnit_one]
    exact fun k => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h2) k
  have hφinj : ∀ x x' : ModGL TwistTag.E6.tag K,
      D.g0⁻¹ * ι (D.c * x * D.c⁻¹) * D.g0 = D.g0⁻¹ * ι (D.c * x' * D.c⁻¹) * D.g0 → x = x' := by
    intro x x' h
    have h4 := baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      (mul_left_cancel (mul_right_cancel h))
    exact mul_left_cancel (mul_right_cancel h4)
  have hφ : ∀ x x' : ModGL TwistTag.E6.tag K,
      D.g0⁻¹ * ι (D.c * (x' * x⁻¹) * D.c⁻¹) * D.g0 =
        D.g0⁻¹ * ι (D.c * x' * D.c⁻¹) * D.g0 * (D.g0⁻¹ * ι (D.c * x * D.c⁻¹) * D.g0)⁻¹ := by
    intro x x'
    rw [show D.c * (x' * x⁻¹) * D.c⁻¹ = D.c * x' * D.c⁻¹ * (D.c * x * D.c⁻¹)⁻¹ by group,
      map_mul, map_inv]
    group
  let T := {b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ //
    (∀ k, b k ^ p = 1) ∧ rootChar b β = 1}
  have hlog : ∀ b : T, ∃ y : Fin TwistTag.E6.tag.rank → ZMod p,
      (fun k => ζ ^ ((y k).val : ℤ)) = b.1 := fun b => exists_zpow_val_eq_rk hζ b.2.1
  choose y hy using hlog
  have hyβ : ∀ b : T, ∑ k, y b k * (β k : ZMod p) = 0 := fun b =>
    (rootChar_val_eq_one_iff_wk hζ (y b) β).1 (by rw [hy b]; exact b.2.2)
  let lg : T → {z : Fin TwistTag.E6.tag.rank → ZMod p // ∑ k, z k * (β k : ZMod p) = 0} :=
    fun b => ⟨y b, hyβ b⟩
  have hlg : Function.Injective lg := by
    intro b b' h
    apply Subtype.ext
    rw [← hy b, ← hy b']
    exact congrArg (fun z : Fin TwistTag.E6.tag.rank → ZMod p => fun k => ζ ^ ((z k).val : ℤ))
      (congrArg Subtype.val h)
  haveI : Finite T := Finite.of_injective lg hlg
  obtain ⟨k0, hk0⟩ := exists_intCast_ne_zero_of_isRoot hβ p
  have hT : Nat.card T ≤ p ^ 5 :=
    (Nat.card_le_card_of_injective lg hlg).trans (card_hyperplane_le β hk0)
  have hcP : ∀ i, rootChar (corootTuple (P i) ζ) β = 1 := fun i => by
    rw [rootChar_corootTuple, iform_comm, hPβ i, zpow_zero]
  have hcPp : ∀ i k, corootTuple (P i) ζ k ^ p = 1 := fun i k =>
    zpow_pow_eq_one_rk hζ.pow_eq_one _
  let F : Fin 6 × A → T := fun ix =>
    ⟨corootTuple (P ix.1) ζ * (a ix.2.1 ix.2.2)⁻¹, fun k => by
        rw [Pi.mul_apply, Pi.inv_apply, mul_pow, inv_pow, hcPp, hap, inv_one, mul_one],
      by rw [rootChar_mul_inv_rk, hcP, haβ, inv_one, mul_one]⟩
  by_contra hno
  have key : ∀ (i i' : Fin 6) (x x' : A), i < i' →
      corootTuple (P i) ζ * (a x.1 x.2)⁻¹ = corootTuple (P i') ζ * (a x'.1 x'.2)⁻¹ → False := by
    rintro i i' ⟨x, hx⟩ ⟨x', hx'⟩ hii h1
    have h2 : corootTuple (P i' - P i) ζ = a x' hx' * (a x hx)⁻¹ := by
      rw [corootTuple_sub, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at h1
      rw [← h1, mul_comm]
    refine hno ⟨P i' - P i, hProot i i' hii, by rw [iform_sub_left_rk, hPβ, hPβ, sub_zero], ζ,
      hζ.pow_eq_one, hζ.ne_one hp.one_lt, x' * x⁻¹, mul_mem hx' (inv_mem hx), ?_⟩
    rw [h2, CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_inv,
      ha, ha, hφ]
  have hF : Function.Injective F := by
    rintro ⟨i, x⟩ ⟨i', x'⟩ h
    have h1 : corootTuple (P i) ζ * (a x.1 x.2)⁻¹ = corootTuple (P i') ζ * (a x'.1 x'.2)⁻¹ :=
      congrArg Subtype.val h
    rcases lt_trichotomy i i' with hii | rfl | hii
    · exact (key i i' x x' hii h1).elim
    · have h3 : a x.1 x.2 = a x'.1 x'.2 := inv_injective (mul_left_cancel h1)
      have h4 := hφinj x.1 x'.1 (by rw [← ha x.1 x.2, ← ha x'.1 x'.2, h3])
      exact Prod.ext rfl (Subtype.ext h4)
    · exact (key i' i x' x hii h1.symm).elim
  have h6 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin] at h6
  exact absurd (h6.trans hT) (not_le.mpr hcard)

end CFSG.StandardType.TwE6RootAs

end
