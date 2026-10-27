module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUInFrame

public section

namespace CFSG.StandardType

namespace CoordSUIn

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CoordSU Multiplicative
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.OddIso

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

section Involution

theorem stdHermForm_eq_zero_symm {u v : Fin n → K} (huv : stdHermForm h n u v = 0) :
    stdHermForm h n v u = 0 := by
  rw [← (stdHermForm_isSymm h n).eq u v, huv, map_zero]

theorem exists_decomp₃ {U₁ U₂ : Submodule K (Fin n → K)} (hnd₁ : NondegOn (stdHermForm h n) U₁)
    (hnd₂ : NondegOn (stdHermForm h n) U₂)
    (horth : ∀ u ∈ U₁, ∀ v ∈ U₂, stdHermForm h n u v = 0) (v : Fin n → K) :
    ∃ v₁ ∈ U₁, ∃ v₂ ∈ U₂, ∃ z ∈ U₁.orthogonalBilin (stdHermForm h n),
      z ∈ U₂.orthogonalBilin (stdHermForm h n) ∧ v = v₁ + v₂ + z := by
  obtain ⟨v₁, hv₁, z₁, hz₁, rfl⟩ := exists_add_orth hnd₁ v
  obtain ⟨v₂, hv₂, z, hz, rfl⟩ := exists_add_orth hnd₂ z₁
  refine ⟨v₁, hv₁, v₂, hv₂, z, Submodule.mem_orthogonalBilin.mpr fun m hm => ?_, hz, by abel⟩
  have h1 : stdHermForm h n m (v₂ + z) = 0 := (Submodule.mem_orthogonalBilin.mp hz₁) m hm
  rwa [map_add, horth m hm v₂ hv₂, zero_add] at h1

theorem stdHermForm_split {U₁ U₂ : Submodule K (Fin n → K)}
    (horth : ∀ u ∈ U₁, ∀ v ∈ U₂, stdHermForm h n u v = 0) {a a' b b' c c' : Fin n → K}
    (ha : a ∈ U₁) (ha' : a' ∈ U₁) (hb : b ∈ U₂) (hb' : b' ∈ U₂)
    (hc₁ : c ∈ U₁.orthogonalBilin (stdHermForm h n)) (hc₂ : c ∈ U₂.orthogonalBilin (stdHermForm h n))
    (hc₁' : c' ∈ U₁.orthogonalBilin (stdHermForm h n))
    (hc₂' : c' ∈ U₂.orthogonalBilin (stdHermForm h n)) :
    stdHermForm h n (a + b + c) (a' + b' + c') =
      stdHermForm h n a a' + stdHermForm h n b b' + stdHermForm h n c c' := by
  have e1 : stdHermForm h n a b' = 0 := horth a ha b' hb'
  have e2 : stdHermForm h n a c' = 0 := (Submodule.mem_orthogonalBilin.mp hc₁') a ha
  have e3 : stdHermForm h n b a' = 0 := stdHermForm_eq_zero_symm (horth a' ha' b hb)
  have e4 : stdHermForm h n b c' = 0 := (Submodule.mem_orthogonalBilin.mp hc₂') b hb
  have e5 : stdHermForm h n c a' = 0 :=
    stdHermForm_eq_zero_symm ((Submodule.mem_orthogonalBilin.mp hc₁) a' ha')
  have e6 : stdHermForm h n c b' = 0 :=
    stdHermForm_eq_zero_symm ((Submodule.mem_orthogonalBilin.mp hc₂) b' hb')
  simp only [map_add, LinearMap.add_apply, e1, e2, e3, e4, e5, e6]
  abel

theorem exists_swapEnd {U₁ U₂ : Submodule K (Fin n → K)} (hnd₁ : NondegOn (stdHermForm h n) U₁)
    (hnd₂ : NondegOn (stdHermForm h n) U₂)
    (horth : ∀ u ∈ U₁, ∀ v ∈ U₂, stdHermForm h n u v = 0)
    {θ : (Fin n → K) →ₗ[K] (Fin n → K)} (hθU : ∀ u ∈ U₁, θ u ∈ U₂)
    (hθB : ∀ u ∈ U₁, ∀ v ∈ U₁, stdHermForm h n (θ u) (θ v) = stdHermForm h n u v)
    (hθs : ∀ w ∈ U₂, ∃ u ∈ U₁, θ u = w) :
    ∃ σ : Module.End K (Fin n → K), σ * σ = 1 ∧ (∀ u ∈ U₁, σ u = θ u) ∧
      (∀ u ∈ U₁, σ (θ u) = u) ∧
      (∀ z ∈ U₁.orthogonalBilin (stdHermForm h n), z ∈ U₂.orthogonalBilin (stdHermForm h n) →
        σ z = z) ∧
      ∀ v w, stdHermForm h n (σ v) (σ w) = stdHermForm h n v w := by
  classical
  have hinj : Function.Injective (θ.restrict hθU) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, hu⟩ h0
    have h0' : θ u = 0 := congrArg Subtype.val h0
    refine Subtype.ext (hnd₁ u hu fun m hm => ?_)
    rw [← hθB m hm u hu, h0', map_zero]
  have hsurj : Function.Surjective (θ.restrict hθU) := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, rfl⟩ := hθs w hw
    exact ⟨⟨u, hu⟩, rfl⟩
  let e : U₁ ≃ₗ[K] U₂ := LinearEquiv.ofBijective (θ.restrict hθU) ⟨hinj, hsurj⟩
  have he : ∀ u : U₁, (e u : Fin n → K) = θ u := fun u => rfl
  have hθe : ∀ w : U₂, θ (e.symm w) = w := fun w => by
    rw [← he, LinearEquiv.apply_symm_apply]
  have heθ : ∀ u (hu : u ∈ U₁), (e.symm ⟨θ u, hθU u hu⟩ : Fin n → K) = u := fun u hu => by
    have h1 : e ⟨u, hu⟩ = ⟨θ u, hθU u hu⟩ := Subtype.ext (he _)
    rw [← h1, LinearEquiv.symm_apply_apply]
  have hc₁ := CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hnd₁
  have hc₂ := CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hnd₂
  let τ : Module.End K (Fin n → K) := LinearMap.ofIsCompl hc₂ (U₁.subtype ∘ₗ e.symm.toLinearMap)
    (U₂.orthogonalBilin (stdHermForm h n)).subtype
  let σ : Module.End K (Fin n → K) := LinearMap.ofIsCompl hc₁ (U₂.subtype ∘ₗ e.toLinearMap)
    (τ ∘ₗ (U₁.orthogonalBilin (stdHermForm h n)).subtype)
  have hU₂ : ∀ w ∈ U₂, w ∈ U₁.orthogonalBilin (stdHermForm h n) := fun w hw =>
    Submodule.mem_orthogonalBilin.mpr fun m hm => horth m hm w hw
  have hσ₁ : ∀ u ∈ U₁, σ u = θ u := fun u hu =>
    LinearMap.ofIsCompl_apply_left hc₁ (φ := U₂.subtype ∘ₗ e.toLinearMap)
      (ψ := τ ∘ₗ (U₁.orthogonalBilin (stdHermForm h n)).subtype) ⟨u, hu⟩
  have hσ' : ∀ z ∈ U₁.orthogonalBilin (stdHermForm h n), σ z = τ z := fun z hz =>
    LinearMap.ofIsCompl_apply_right hc₁ (φ := U₂.subtype ∘ₗ e.toLinearMap)
      (ψ := τ ∘ₗ (U₁.orthogonalBilin (stdHermForm h n)).subtype) ⟨z, hz⟩
  have hσ₂ : ∀ w (hw : w ∈ U₂), σ w = e.symm ⟨w, hw⟩ := fun w hw => by
    rw [hσ' w (hU₂ w hw)]
    exact LinearMap.ofIsCompl_apply_left hc₂ (φ := U₁.subtype ∘ₗ e.symm.toLinearMap)
      (ψ := (U₂.orthogonalBilin (stdHermForm h n)).subtype) ⟨w, hw⟩
  have hσ₀ : ∀ z ∈ U₁.orthogonalBilin (stdHermForm h n),
      z ∈ U₂.orthogonalBilin (stdHermForm h n) → σ z = z := fun z hz₁ hz₂ => by
    rw [hσ' z hz₁]
    exact LinearMap.ofIsCompl_apply_right hc₂ (φ := U₁.subtype ∘ₗ e.symm.toLinearMap)
      (ψ := (U₂.orthogonalBilin (stdHermForm h n)).subtype) ⟨z, hz₂⟩
  have hσθ : ∀ u ∈ U₁, σ (θ u) = u := fun u hu => by
    rw [hσ₂ _ (hθU u hu), heθ u hu]
  have hσσ₂ : ∀ w ∈ U₂, σ (σ w) = w := fun w hw => by
    rw [hσ₂ w hw, hσ₁ _ (e.symm ⟨w, hw⟩).2, hθe]
  refine ⟨σ, ?_, hσ₁, hσθ, hσ₀, fun v w => ?_⟩
  · refine LinearMap.ext fun v => ?_
    obtain ⟨v₁, hv₁, v₂, hv₂, z, hz₁, hz₂, rfl⟩ := exists_decomp₃ hnd₁ hnd₂ horth v
    rw [Module.End.mul_apply, Module.End.one_apply, map_add, map_add, map_add, map_add, hσ₁ v₁ hv₁,
      hσθ v₁ hv₁, hσσ₂ v₂ hv₂, hσ₀ z hz₁ hz₂, hσ₀ z hz₁ hz₂]
  · obtain ⟨v₁, hv₁, v₂, hv₂, z, hz₁, hz₂, rfl⟩ := exists_decomp₃ hnd₁ hnd₂ horth v
    obtain ⟨w₁, hw₁, w₂, hw₂, z', hz₁', hz₂', rfl⟩ := exists_decomp₃ hnd₁ hnd₂ horth w
    have hv₂' := (e.symm ⟨v₂, hv₂⟩).2
    have hw₂' := (e.symm ⟨w₂, hw₂⟩).2
    have ev : σ (v₁ + v₂ + z) = (e.symm ⟨v₂, hv₂⟩ : Fin n → K) + θ v₁ + z := by
      rw [map_add, map_add, hσ₁ v₁ hv₁, hσ₂ v₂ hv₂, hσ₀ z hz₁ hz₂]
      abel
    have ew : σ (w₁ + w₂ + z') = (e.symm ⟨w₂, hw₂⟩ : Fin n → K) + θ w₁ + z' := by
      rw [map_add, map_add, hσ₁ w₁ hw₁, hσ₂ w₂ hw₂, hσ₀ z' hz₁' hz₂']
      abel
    have e2 : stdHermForm h n (e.symm ⟨v₂, hv₂⟩ : Fin n → K) (e.symm ⟨w₂, hw₂⟩ : Fin n → K) =
        stdHermForm h n v₂ w₂ := by
      rw [← hθB _ hv₂' _ hw₂', hθe, hθe]
    rw [ev, ew, stdHermForm_split horth hv₂' hw₂' (hθU v₁ hv₁) (hθU w₁ hw₁) hz₁ hz₂ hz₁' hz₂',
      stdHermForm_split horth hv₁ hw₁ hv₂ hw₂ hz₁ hz₂ hz₁' hz₂', hθB v₁ hv₁ w₁ hw₁, e2]
    abel

theorem exists_su_of_sq_eq_one (h : UnitaryFieldData 2 f K) {σ : Module.End K (Fin n → K)}
    (hσσ : σ * σ = 1) (hσB : ∀ v w, stdHermForm h n (σ v) (σ w) = stdHermForm h n v w) :
    ∃ s : ↥(unitarySU 2 f K n), lin s = σ := by
  have : CharP K 2 := h.charP
  set M := LinearMap.toMatrixAlgEquiv' σ with hM
  have hMv : ∀ v, M *ᵥ v = σ v := by
    intro v
    rw [← Matrix.toLinAlgEquiv'_apply, hM, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  have hMM : M * M = 1 := by rw [hM, ← map_mul, hσσ, map_one]
  have hdet : M.det = 1 := by
    have h1 : M.det * M.det = 1 := by rw [← Matrix.det_mul, hMM, Matrix.det_one]
    have h2 : (M.det + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, one_pow, sq, h1, CharTwo.add_self_eq_zero]
    have h3 : M.det + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
    rw [← sub_eq_zero, CharTwo.sub_eq_add]
    exact h3
  let g₀ : GL (Fin n) K := ⟨M, M, hMM, hMM⟩
  have hg₀ : g₀ ∈ unitarySU 2 f K n := (mem_unitarySU_iff_isometry h).mpr ⟨hdet, fun x y => by
    change stdHermForm h n (M *ᵥ x) (M *ᵥ y) = _
    rw [hMv, hMv]
    exact hσB x y⟩
  exact ⟨⟨g₀, hg₀⟩, LinearMap.ext fun v => by rw [lin_apply]; exact hMv v⟩

end Involution

section ClassSwap

variable {p : ℕ} {A : Subgroup ↥(unitarySU 2 f K n)}

theorem lin_b_apply_of_ne (F : PieceFrame f n K h p A) {k l : Fin F.r} (hkl : k ≠ l)
    {u : Fin n → K} (hu : u ∈ rng (F.y l)) : lin (F.b k) u = u :=
  F.b_off k u (F.mem_orth hkl hu)

theorem pow_apply_eq_of_eqOn {X Y : Module.End K (Fin n → K)} {U : Submodule K (Fin n → K)}
    (hU : ∀ u ∈ U, X u ∈ U) (hXY : ∀ u ∈ U, X u = Y u) (k : ℕ) {u : Fin n → K} (hu : u ∈ U) :
    (Y ^ k) u = (X ^ k) u := by
  have := SUTB.aeval_eq_of_eqOn hU hXY (Polynomial.X ^ k) hu
  rw [map_pow, aeval_X, map_pow, aeval_X] at this
  exact this.symm

theorem exists_classSwap (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {i j : Fin F.r}
    (hij : i ≠ j) {m : ℕ} (hm : ¬ p ∣ m) {g : K[X]}
    (hg : g ∈ primaryFactors (lin (F.b i * F.b j ^ m)))
    (hgi : ∃ w ∈ rng (F.y i), w ≠ 0 ∧ aeval (lin (F.b i * F.b j ^ m)) g w = 0)
    (hgj : ∃ w ∈ rng (F.y j), w ≠ 0 ∧ aeval (lin (F.b i * F.b j ^ m)) g w = 0) :
    ∃ σ : ↥(unitarySU 2 f K n), σ * σ = 1 ∧
      σ * (F.b i * F.b j ^ m) = (F.b i * F.b j ^ m) * σ ∧ σ * F.b i * σ = F.b j ^ m ∧
      ∀ k, k ≠ i → k ≠ j → σ * F.b k * σ = F.b k := by
  classical
  have : Finite K := h.finite
  have hp0 : 0 < p := hA.prime.pos
  set x := F.b i * F.b j ^ m with hx
  set U₁ := rng (F.y i) with hU₁
  set U₂ := rng (F.y j) with hU₂
  have hxA : x ∈ A := A.mul_mem (F.b_mem i) (A.pow_mem (F.b_mem j) m)
  have hnd₁ : NondegOn (stdHermForm h n) U₁ := F.nondeg hA i
  have hnd₂ : NondegOn (stdHermForm h n) U₂ := F.nondeg hA j
  have horth : ∀ u ∈ U₁, ∀ v ∈ U₂, stdHermForm h n u v = 0 := F.orth i j hij
  have hbjU₁ : ∀ u ∈ U₁, lin (F.b j ^ m) u = u := fun u hu =>
    lin_pow_apply_of_fix (lin_b_apply_of_ne F (Ne.symm hij) hu) m
  have hbiU₂ : ∀ w ∈ U₂, lin (F.b i) w = w := fun w hw => lin_b_apply_of_ne F hij hw
  have hbjm : ∀ w ∈ U₂, lin (F.b j ^ m) w ∈ U₂ :=
    rng_inv hA (F.y_mem j) (A.pow_mem (F.b_mem j) m)
  have hxU₁ : ∀ u ∈ U₁, lin x u = lin (F.b i) u := fun u hu => by
    rw [hx, lin_mul, Module.End.mul_apply, hbjU₁ u hu]
  have hxU₂ : ∀ w ∈ U₂, lin x w = lin (F.b j ^ m) w := fun w hw => by
    rw [hx, lin_mul, Module.End.mul_apply, hbiU₂ _ (hbjm w hw)]
  have hinv₁ : ∀ u ∈ U₁, lin x u ∈ U₁ := rng_inv hA (F.y_mem i) hxA
  have hinv₂ : ∀ u ∈ U₂, lin x u ∈ U₂ := rng_inv hA (F.y_mem j) hxA
  have hxW : ∀ z ∈ U₁.orthogonalBilin (stdHermForm h n),
      z ∈ U₂.orthogonalBilin (stdHermForm h n) → lin x z = z := by
    intro z hz₁ hz₂
    rw [hx, lin_mul, Module.End.mul_apply, lin_pow_apply_of_fix (F.b_off j z hz₂) m,
      F.b_off i z hz₁]
  have hmin₁ : ∀ W : Submodule K (Fin n → K), W ≤ U₁ → W ≠ ⊥ →
      NondegOn (stdHermForm h n) W → (∀ w ∈ W, lin x w ∈ W) → W = U₁ := by
    intro W hW hW0 hWnd hWx
    refine F.minimal i W hW hW0 hWnd fun a ha w hw => ?_
    obtain ⟨k, hk⟩ := F.cyc i a ha
    have hxy : ∀ u ∈ U₁, lin x u = lin (F.y i) u := fun u hu => by
      rw [hxU₁ u hu, F.b_on i u hu]
    rw [hk w (hW hw), SUTB.lin_pow, pow_apply_eq_of_eqOn hinv₁ hxy k (hW hw)]
    exact invariant_pow hWx k w hw
  obtain ⟨m', hm'⟩ := exists_pow_pow_eq hA (F.y_mem j) hm
  have hmin₂ : ∀ W : Submodule K (Fin n → K), W ≤ U₂ → W ≠ ⊥ →
      NondegOn (stdHermForm h n) W → (∀ w ∈ W, lin x w ∈ W) → W = U₂ := by
    intro W hW hW0 hWnd hWx
    refine F.minimal j W hW hW0 hWnd fun a ha w hw => ?_
    obtain ⟨k, hk⟩ := F.cyc j a ha
    have hxy : ∀ u ∈ U₂, lin x u = lin (F.y j ^ m) u := fun u hu => by
      rw [hxU₂ u hu, lin_b_pow_on hA F j m hu]
    rw [hk w (hW hw), ← hm', ← pow_mul, SUTB.lin_pow, pow_apply_eq_of_eqOn hinv₂ hxy _ (hW hw)]
    exact invariant_pow hWx _ w hw
  obtain ⟨θ, hθU, hθB, hθx, hθs⟩ := exists_isometry_of_pieces h
    (unitaryPrimaryData_toUnit h hA hxA) hp0 (hA.lin_pow hxA) hnd₁ hnd₂ hinv₁ hinv₂ hmin₁ hmin₂
    hg hgi hgj
  have hθx' : ∀ u ∈ U₁, θ (lin x u) = lin x (θ u) := hθx
  obtain ⟨σ₀, hσσ, hσ₁, hσθ, hσ₀, hσB⟩ := exists_swapEnd hnd₁ hnd₂ horth hθU hθB hθs
  obtain ⟨σ, hσ⟩ := exists_su_of_sq_eq_one h hσσ hσB
  have hU₂θ : ∀ w ∈ U₂, ∃ u ∈ U₁, w = θ u := fun w hw => by
    obtain ⟨u, hu, rfl⟩ := hθs w hw
    exact ⟨u, hu, rfl⟩
  have hext : ∀ a c : ↥(unitarySU 2 f K n), (∀ u ∈ U₁, lin a u = lin c u) →
      (∀ u ∈ U₁, lin a (θ u) = lin c (θ u)) →
      (∀ z ∈ U₁.orthogonalBilin (stdHermForm h n), z ∈ U₂.orthogonalBilin (stdHermForm h n) →
        lin a z = lin c z) → a = c := by
    intro a c h1 h2 h3
    refine eq_of_lin_apply fun v => ?_
    obtain ⟨v₁, hv₁, v₂, hv₂, z, hz₁, hz₂, rfl⟩ := exists_decomp₃ hnd₁ hnd₂ horth v
    obtain ⟨u, hu, rfl⟩ := hU₂θ v₂ hv₂
    rw [map_add, map_add, map_add, map_add, h1 v₁ hv₁, h2 u hu, h3 z hz₁ hz₂]
  refine ⟨σ, ?_, ?_, ?_, fun k hki hkj => ?_⟩
  · apply lin_injective
    rw [lin_mul, hσ, hσσ, lin_one]
  · refine hext _ _ (fun u hu => ?_) (fun u hu => ?_) fun z hz₁ hz₂ => ?_
    · rw [lin_mul σ x, lin_mul x σ, Module.End.mul_apply, Module.End.mul_apply, hσ,
        hσ₁ _ (hinv₁ u hu), hθx' u hu, hσ₁ u hu]
    · rw [lin_mul σ x, lin_mul x σ, Module.End.mul_apply, Module.End.mul_apply, hσ, ← hθx' u hu,
        hσθ _ (hinv₁ u hu), hσθ u hu]
    · rw [lin_mul σ x, lin_mul x σ, Module.End.mul_apply, Module.End.mul_apply, hσ,
        hxW z hz₁ hz₂, hσ₀ z hz₁ hz₂, hxW z hz₁ hz₂]
  · refine hext _ _ (fun u hu => ?_) (fun u hu => ?_) fun z hz₁ hz₂ => ?_
    · rw [lin_mul (σ * F.b i) σ, lin_mul σ (F.b i), Module.End.mul_apply, Module.End.mul_apply, hσ,
        hσ₁ u hu, hbiU₂ _ (hθU u hu), hσθ u hu, hbjU₁ u hu]
    · rw [lin_mul (σ * F.b i) σ, lin_mul σ (F.b i), Module.End.mul_apply, Module.End.mul_apply, hσ,
        hσθ u hu, ← hxU₁ u hu, hσ₁ _ (hinv₁ u hu), hθx' u hu, hxU₂ _ (hθU u hu)]
    · rw [lin_mul (σ * F.b i) σ, lin_mul σ (F.b i), Module.End.mul_apply, Module.End.mul_apply, hσ,
        hσ₀ z hz₁ hz₂, F.b_off i z hz₁, hσ₀ z hz₁ hz₂, lin_pow_apply_of_fix (F.b_off j z hz₂) m]
  · have hbkW : ∀ z ∈ U₁.orthogonalBilin (stdHermForm h n),
        z ∈ U₂.orthogonalBilin (stdHermForm h n) →
        lin (F.b k) z ∈ U₁.orthogonalBilin (stdHermForm h n) ∧
          lin (F.b k) z ∈ U₂.orthogonalBilin (stdHermForm h n) := by
      intro z hz₁ hz₂
      constructor
      · refine Submodule.mem_orthogonalBilin.mpr fun a ha => ?_
        rw [← lin_b_apply_of_ne F hki ha, isometry_lin h]
        exact (Submodule.mem_orthogonalBilin.mp hz₁) a ha
      · refine Submodule.mem_orthogonalBilin.mpr fun a ha => ?_
        rw [← lin_b_apply_of_ne F hkj ha, isometry_lin h]
        exact (Submodule.mem_orthogonalBilin.mp hz₂) a ha
    refine hext _ _ (fun u hu => ?_) (fun u hu => ?_) fun z hz₁ hz₂ => ?_
    · rw [lin_mul (σ * F.b k) σ, lin_mul σ (F.b k), Module.End.mul_apply, Module.End.mul_apply, hσ,
        hσ₁ u hu, lin_b_apply_of_ne F hkj (hθU u hu), hσθ u hu, lin_b_apply_of_ne F hki hu]
    · rw [lin_mul (σ * F.b k) σ, lin_mul σ (F.b k), Module.End.mul_apply, Module.End.mul_apply, hσ,
        hσθ u hu, lin_b_apply_of_ne F hki hu, hσ₁ u hu, lin_b_apply_of_ne F hkj (hθU u hu)]
    · rw [lin_mul (σ * F.b k) σ, lin_mul σ (F.b k), Module.End.mul_apply, Module.End.mul_apply, hσ,
        hσ₀ z hz₁ hz₂, hσ₀ _ (hbkW z hz₁ hz₂).1 (hbkW z hz₁ hz₂).2]

theorem classSwap_b_right (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {i j : Fin F.r}
    {m m' : ℕ} (hmm' : m * m' % p = 1) {σ : ↥(unitarySU 2 f K n)} (hσσ : σ * σ = 1)
    (hσx : σ * (F.b i * F.b j ^ m) = (F.b i * F.b j ^ m) * σ)
    (hσi : σ * F.b i * σ = F.b j ^ m) : σ * F.b j * σ = F.b i ^ m' := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  have hc : ∀ a, σ * a * σ = MulAut.conj σ a := fun a => by rw [MulAut.conj_apply, hσinv]
  have hcomm : Commute (F.b i) (F.b j) := hA.comm _ (F.b_mem i) _ (F.b_mem j)
  have hbj : F.b j ^ (m * m') = F.b j := by
    rw [pow_eq_pow_mod _ (hA.pow _ (F.b_mem j)), hmm', pow_one]
  have hxm : (F.b i * F.b j ^ m) ^ m' = F.b i ^ m' * F.b j := by
    rw [(hcomm.pow_right m).mul_pow, ← pow_mul, hbj]
  have hcx : MulAut.conj σ (F.b i * F.b j ^ m) = F.b i * F.b j ^ m := by
    rw [← hc, hσx, mul_assoc, hσσ, mul_one]
  have hbj' : F.b j = (F.b i ^ m')⁻¹ * (F.b i * F.b j ^ m) ^ m' := by
    rw [hxm, inv_mul_cancel_left]
  rw [hc, hbj', map_mul, map_inv, map_pow, map_pow, hcx, ← hc, hσi, ← pow_mul, hbj, hxm,
    (hcomm.pow_left m').eq, inv_mul_cancel_left]

end ClassSwap

end CoordSUIn

end CFSG.StandardType
