module

public import CFSG.RankThree.PartOne.KFR4.Defs

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.LieType.Universal.Unitary
open scoped Matrix

namespace CDec

section Field

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem exists_sigma_ne (D : EvenNormPlane K E) : ∃ θ : E, D.σ θ ≠ θ := by
  by_contra h
  push Not at h
  exact D.σ_ne_one (AlgEquiv.ext fun x => (h x).trans (AlgEquiv.one_apply x).symm)

theorem eq_zero_of_forall (D : EvenNormPlane K E) {γ δ : E}
    (h : ∀ u, γ * u + δ * D.σ u = 0) : γ = 0 ∧ δ = 0 := by
  obtain ⟨θ, hθ⟩ := exists_sigma_ne D
  have h1 := h 1
  have h2 := h θ
  rw [map_one, mul_one, mul_one] at h1
  have hne : θ - D.σ θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hγ : γ * (θ - D.σ θ) = 0 := by linear_combination h2 - D.σ θ * h1
  have hγ0 : γ = 0 := (mul_eq_zero.1 hγ).resolve_right hne
  exact ⟨hγ0, by linear_combination h1 - hγ0⟩

theorem exists_eq_add_sigma (D : EvenNormPlane K E) (φ : E →ₗ[K] E) :
    ∃ α β : E, ∀ u, φ u = α * u + β * D.σ u := by
  have : Module.Finite K E := Module.finite_of_finrank_pos (by rw [D.finrank_eq]; omega)
  obtain ⟨θ, hθ⟩ := exists_sigma_ne D
  have hne : θ - D.σ θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  have hli : LinearIndependent K ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    apply hθ
    rw [← ha, Algebra.smul_def, mul_one, AlgEquiv.commutes]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [D.finrank_eq])
  refine ⟨(φ θ - D.σ θ * φ 1) / (θ - D.σ θ), (θ * φ 1 - φ θ) / (θ - D.σ θ), fun u => ?_⟩
  let ψ : E →ₗ[K] E := ((φ θ - D.σ θ * φ 1) / (θ - D.σ θ)) • LinearMap.id +
    ((θ * φ 1 - φ θ) / (θ - D.σ θ)) • D.σ.toLinearMap
  have key : φ = ψ := by
    refine b.ext fun i => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    fin_cases i
    · simp only [ψ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        AlgEquiv.toLinearMap_apply, smul_eq_mul]
      simp
      field_simp
      ring
    · simp only [ψ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        AlgEquiv.toLinearMap_apply, smul_eq_mul]
      simp
      field_simp
      ring
  exact LinearMap.congr_fun key u

end Field

section Torus

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}
  (S : StdData K E p)

theorem rot_ne_one {c : ZMod p} (hc : c ≠ 0) : S.rot c ≠ 1 := by
  intro h
  apply hc
  apply S.rot_injective
  rw [h, S.rot_zero]

theorem comp_eq {A : AddSubgroup (Fin 3 → ZMod p)} (hA : Coherent A) {i j : Fin 3}
    (hi : ∃ a ∈ A, a i ≠ 0) (φ : E →ₗ[K] E)
    (hφ : ∀ s ∈ A, ∀ u, φ (S.rot (s i) * u) = S.rot (s j) * φ u) :
    (∀ u, φ u = φ 1 * u) ∧ ((∃ a ∈ A, a i ≠ a j) → φ 1 = 0) := by
  obtain ⟨α, β, hαβ⟩ := exists_eq_add_sigma S.D φ
  have key : ∀ s ∈ A, α * (S.rot (s i) - S.rot (s j)) = 0 ∧
      β * (S.rot (-s i) - S.rot (s j)) = 0 := by
    intro s hs
    apply eq_zero_of_forall S.D
    intro u
    have h := hφ s hs u
    simp only [hαβ, map_mul, S.sigma_rot] at h
    linear_combination h
  have hβ : β = 0 := by
    by_contra hβ
    obtain ⟨a, ha, hai⟩ := hi
    apply hai
    refine hA i j (fun s hs => ?_) a ha
    have h := (mul_eq_zero.1 (key s hs).2).resolve_left hβ
    have h2 : -s i = s j := S.rot_injective (sub_eq_zero.1 h)
    rw [← h2, neg_neg]
  have hφ1 : φ 1 = α := by rw [hαβ, hβ]; simp
  refine ⟨fun u => by rw [hαβ, hβ, hφ1]; ring, fun ⟨a, ha, hne⟩ => ?_⟩
  rw [hφ1]
  refine (mul_eq_zero.1 (key a ha).1).resolve_right fun h => hne ?_
  exact S.rot_injective (sub_eq_zero.1 h)

theorem tor_single (s : Fin 3 → ZMod p) (i : Fin 3) (u : E) :
    tor S s ((Pi.single i u : Fin 3 → E), (0 : K × K)) =
      ((Pi.single i (S.rot (s i) * u) : Fin 3 → E), (0 : K × K)) := by
  refine Prod.ext (funext fun j => ?_) rfl
  by_cases h : j = i
  · subst h; simp [tor_apply]
  · simp [tor_apply, h]

end Torus

section Unitary

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem herm_mulVec (D : EvenNormPlane K E) {M : Matrix (Fin 3) (Fin 3) E}
    (hM : conjTr D.σ.toRingEquiv M * M = 1) (z w : Fin 3 → E) :
    ∑ j, D.σ ((M *ᵥ z) j) * (M *ᵥ w) j = ∑ j, D.σ (z j) * w j := by
  have h1 : (fun j => D.σ ((M *ᵥ z) j)) = (M.map D.σ) *ᵥ (fun j => D.σ (z j)) := by
    funext j
    simp [Matrix.mulVec, dotProduct, map_sum]
  calc ∑ j, D.σ ((M *ᵥ z) j) * (M *ᵥ w) j = (fun j => D.σ ((M *ᵥ z) j)) ⬝ᵥ (M *ᵥ w) := rfl
    _ = ((M.map D.σ) *ᵥ (fun j => D.σ (z j))) ⬝ᵥ (M *ᵥ w) := by rw [h1]
    _ = (fun j => D.σ (z j)) ⬝ᵥ ((conjTr D.σ.toRingEquiv M * M) *ᵥ w) := by
        rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
        rfl
    _ = ∑ j, D.σ (z j) * w j := by rw [hM, Matrix.one_mulVec]; rfl

theorem matToG_mem_orth (D : EvenNormPlane K E) {M : GL (Fin 3) E} (hM : M ∈ Uni D) :
    matToG K M ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  show Qs D ((M : Matrix (Fin 3) (Fin 3) E) *ᵥ v.1, v.2) = Qs D v
  rw [Qs_apply, Qs_apply]
  congr 1
  apply (algebraMap K E).injective
  simp only [map_sum, D.algebraMap_N]
  have := herm_mulVec D hM v.1 v.1
  simp_rw [mul_comm _ (D.σ _)]
  exact this

open CFSG.RankThree.OrthogonalInvolutions in
theorem matToG_mem_Om [Module.Finite K E] (D : EvenNormPlane K E) {M : GL (Fin 3) E}
    (hM : M ∈ Uni D) : matToG K M ∈ Om D := by
  rw [Om_eq_omegaGroup]
  refine ⟨matToG_mem_orth D hM, ?_⟩
  let L : (Fin 3 → E) →ₗ[E] (Fin 3 → E) := ((M : Matrix (Fin 3) (Fin 3) E) - 1).mulVecLin
  have hrange : commSpace (matToG K M) =
      ((LinearMap.range L).restrictScalars K).map (LinearMap.inl K (Fin 3 → E) (K × K)) := by
    ext v
    simp only [commSpace, LinearMap.mem_range, Submodule.mem_map,
      Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨L w.1, ⟨w.1, rfl⟩, ?_⟩
      refine Prod.ext ?_ ?_
      · simp [L]
        rfl
      · exact (sub_self w.2).symm
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      refine ⟨(z, 0), Prod.ext ?_ ?_⟩
      · simp [L]
        rfl
      · simp
        rfl
  have hinj : Function.Injective (LinearMap.inl K (Fin 3 → E) (K × K)) :=
    LinearMap.inl_injective
  rw [hrange, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq,
    LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv K E _ (LinearMap.range L)).restrictScalars K)]
  obtain ⟨c, hc⟩ := Module.finrank_dvd_finrank_right K E (LinearMap.range L)
  rw [hc, D.finrank_eq]
  exact even_two_mul c

theorem mulVec_eq_self {M : Matrix (Fin 3) (Fin 3) E} {F : Finset (Fin 3)}
    (hM : ∀ i ∈ F, M *ᵥ Pi.single i 1 = Pi.single i 1) {z : Fin 3 → E}
    (hz : ∀ j, j ∉ F → z j = 0) : M *ᵥ z = z := by
  have h : ∀ j i, M j i * z i = (1 : Matrix (Fin 3) (Fin 3) E) j i * z i := by
    intro j i
    by_cases hi : i ∈ F
    · have := congrFun (hM i hi) j
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
      rw [this]
      simp [Matrix.one_apply, Pi.single_apply]
    · rw [hz i hi, mul_zero, mul_zero]
  funext j
  calc (M *ᵥ z) j = ∑ i, M j i * z i := rfl
    _ = ∑ i, (1 : Matrix (Fin 3) (Fin 3) E) j i * z i := Finset.sum_congr rfl fun i _ => h j i
    _ = z j := by simp [Matrix.one_apply]

theorem mulVec_apply_eq_zero {N : Matrix (Fin 3) (Fin 3) E} {F : Finset (Fin 3)}
    (hN : ∀ i ∈ F, ∀ k, N i k = (1 : Matrix (Fin 3) (Fin 3) E) i k) {z : Fin 3 → E}
    (hz : ∀ i ∈ F, z i = 0) {i : Fin 3} (hi : i ∈ F) : (N *ᵥ z) i = 0 := by
  calc (N *ᵥ z) i = ∑ k, N i k * z k := rfl
    _ = ∑ k, (1 : Matrix (Fin 3) (Fin 3) E) i k * z k :=
        Finset.sum_congr rfl fun k _ => by rw [hN i hi k]
    _ = z i := by simp [Matrix.one_apply]
    _ = 0 := hz i hi

theorem row_eq_of_col (D : EvenNormPlane K E) {M : Matrix (Fin 3) (Fin 3) E}
    (hM : conjTr D.σ.toRingEquiv M * M = 1) {i : Fin 3}
    (hi : M *ᵥ Pi.single i 1 = Pi.single i 1) (k : Fin 3) :
    M i k = (1 : Matrix (Fin 3) (Fin 3) E) i k := by
  have h1 := congrFun (congrFun hM i) k
  have hcol : ∀ j, M j i = (1 : Matrix (Fin 3) (Fin 3) E) j i := fun j => by
    have := congrFun hi j
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]
    simp [Matrix.one_apply, Pi.single_apply]
  simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply] at h1
  simp only [hcol] at h1
  simpa [Matrix.one_apply] using h1

theorem polar_mat_single (D : EvenNormPlane K E) (i k : Fin 3) (u w : E) :
    polar (Qs D) ((Pi.single i u : Fin 3 → E), (0 : K × K))
      ((Pi.single k w : Fin 3 → E), (0 : K × K)) = if i = k then polar D.N u w else 0 := by
  rw [polar_Qs]
  fin_cases i <;> fin_cases k <;> simp [Fin.sum_univ_three]

end Unitary

section Coord

variable {K E : Type} [Field K] [Field E] [Algebra K E]

noncomputable def mat (g : Vs K E ≃ₗ[K] Vs K E) (F : Finset (Fin 3)) :
    Matrix (Fin 3) (Fin 3) E :=
  Matrix.of fun j i => if i ∈ F then (1 : Matrix (Fin 3) (Fin 3) E) j i
    else (g ((Pi.single i 1 : Fin 3 → E), (0 : K × K))).1 j

theorem mat_of_mem {g : Vs K E ≃ₗ[K] Vs K E} {F : Finset (Fin 3)} {i : Fin 3} (hi : i ∈ F)
    (j : Fin 3) : mat g F j i = (1 : Matrix (Fin 3) (Fin 3) E) j i := by
  simp [mat, hi]

theorem mat_of_not_mem {g : Vs K E ≃ₗ[K] Vs K E} {F : Finset (Fin 3)} {i : Fin 3} (hi : i ∉ F)
    (j : Fin 3) : mat g F j i = (g ((Pi.single i 1 : Fin 3 → E), (0 : K × K))).1 j := by
  simp [mat, hi]

theorem mat_mulVec_single {g : Vs K E ≃ₗ[K] Vs K E} {F : Finset (Fin 3)} {i : Fin 3}
    (hi : i ∈ F) : mat g F *ᵥ Pi.single i 1 = Pi.single i 1 := by
  funext j
  rw [Matrix.mulVec_single_one, Matrix.col_apply, mat_of_mem hi]
  simp [Matrix.one_apply, Pi.single_apply]

@[expose] noncomputable def compLin (g : Vs K E ≃ₗ[K] Vs K E) (i j : Fin 3) : E →ₗ[K] E :=
  (LinearMap.proj j : (Fin 3 → E) →ₗ[K] E) ∘ₗ LinearMap.fst K (Fin 3 → E) (K × K) ∘ₗ
    (g : Vs K E →ₗ[K] Vs K E) ∘ₗ LinearMap.inl K (Fin 3 → E) (K × K) ∘ₗ
      LinearMap.single K (fun _ : Fin 3 => E) i

theorem compLin_apply (g : Vs K E ≃ₗ[K] Vs K E) (i j : Fin 3) (u : E) :
    compLin g i j u = (g ((Pi.single i u : Fin 3 → E), (0 : K × K))).1 j := rfl

@[expose] noncomputable def compH (g : Vs K E ≃ₗ[K] Vs K E) (i : Fin 3) : E →ₗ[K] K × K :=
  LinearMap.snd K (Fin 3 → E) (K × K) ∘ₗ (g : Vs K E →ₗ[K] Vs K E) ∘ₗ
    LinearMap.inl K (Fin 3 → E) (K × K) ∘ₗ LinearMap.single K (fun _ : Fin 3 => E) i

theorem compH_apply (g : Vs K E ≃ₗ[K] Vs K E) (i : Fin 3) (u : E) :
    compH g i u = (g ((Pi.single i u : Fin 3 → E), (0 : K × K))).2 := rfl

end Coord

section Cent

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}
  {S : StdData K E p} {A : AddSubgroup (Fin 3 → ZMod p)}

theorem apply_tor {g : Vs K E ≃ₗ[K] Vs K E} (hg : ∀ a ∈ A, g * tor S a = tor S a * g)
    {a : Fin 3 → ZMod p} (ha : a ∈ A) (v : Vs K E) : g (tor S a v) = tor S a (g v) := by
  rw [← LinearEquiv.mul_apply, hg a ha, LinearEquiv.mul_apply]

theorem compLin_rel {g : Vs K E ≃ₗ[K] Vs K E} (hg : ∀ a ∈ A, g * tor S a = tor S a * g)
    {s : Fin 3 → ZMod p} (hs : s ∈ A) (i j : Fin 3) (u : E) :
    compLin g i j (S.rot (s i) * u) = S.rot (s j) * compLin g i j u := by
  rw [compLin_apply, compLin_apply, ← tor_single S s i u, apply_tor hg hs, tor_apply]

theorem compH_rel {g : Vs K E ≃ₗ[K] Vs K E} (hg : ∀ a ∈ A, g * tor S a = tor S a * g)
    {s : Fin 3 → ZMod p} (hs : s ∈ A) (i : Fin 3) (u : E) :
    compH g i (S.rot (s i) * u) = compH g i u := by
  rw [compH_apply, compH_apply, ← tor_single S s i u, apply_tor hg hs, tor_apply]

theorem exists_ne_zero_of_not_mem {i : Fin 3} (hi : i ∉ fixedSet A) : ∃ a ∈ A, a i ≠ 0 := by
  by_contra h
  push Not at h
  exact hi (mem_fixedSet.2 h)

theorem tor_eq_self {s : Fin 3 → ZMod p} (hs : s ∈ A) {v : Vs K E}
    (hv : v ∈ Ufix K E (fixedSet A)) : tor S s v = v := by
  refine Prod.ext (funext fun j => ?_) rfl
  rw [tor_apply]
  by_cases hj : j ∈ fixedSet A
  · simp [mem_fixedSet.1 hj s hs, S.rot_zero]
  · simp [hv j hj]

theorem mem_Ufix_of_comm {h : Vs K E ≃ₗ[K] Vs K E} (hh : ∀ a ∈ A, h * tor S a = tor S a * h)
    {v : Vs K E} (hv : v ∈ Ufix K E (fixedSet A)) : h v ∈ Ufix K E (fixedSet A) := by
  intro j hj
  obtain ⟨a, ha, haj⟩ := exists_ne_zero_of_not_mem hj
  have h1 := congrArg (fun x => (x v).1 j) (hh a ha)
  simp only [LinearEquiv.mul_apply, tor_eq_self ha hv, tor_apply] at h1
  have h2 : (S.rot (a j) - 1) * (h v).1 j = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (rot_ne_one S haj))

variable (hA : Coherent A) {g : Vs K E ≃ₗ[K] Vs K E}
  (hg : ∀ a ∈ A, g * tor S a = tor S a * g)
include hA hg

theorem g_single {i : Fin 3} (hi : i ∉ fixedSet A) (u : E) :
    g ((Pi.single i u : Fin 3 → E), (0 : K × K)) = (fun j => mat g (fixedSet A) j i * u, 0) := by
  have hi' := exists_ne_zero_of_not_mem hi
  refine Prod.ext (funext fun j => ?_) ?_
  · dsimp only
    rw [mat_of_not_mem hi]
    exact (comp_eq S hA hi' (compLin g i j) fun s hs u => compLin_rel hg hs i j u).1 u
  · obtain ⟨a, ha, hai⟩ := hi'
    have hω : S.rot (a i) - 1 ≠ 0 := sub_ne_zero.2 (rot_ne_one S hai)
    have e : S.rot (a i) * ((S.rot (a i) - 1)⁻¹ * u) - (S.rot (a i) - 1)⁻¹ * u = u := by
      rw [← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ hω, one_mul]
    rw [← compH_apply, ← e, map_sub, compH_rel hg ha, sub_self]

theorem g_single' (i : Fin 3) (u : E) (hu : i ∈ fixedSet A → u = 0) :
    g ((Pi.single i u : Fin 3 → E), (0 : K × K)) = (fun j => mat g (fixedSet A) j i * u, 0) := by
  by_cases hi : i ∈ fixedSet A
  · rw [hu hi, Pi.single_zero, Prod.mk_zero_zero, map_zero]
    refine Prod.ext (funext fun j => ?_) rfl
    simp
  · exact g_single hA hg hi u

theorem mat_zero {i j : Fin 3} (h : ∃ a ∈ A, a i ≠ a j) : mat g (fixedSet A) j i = 0 := by
  by_cases hi : i ∈ fixedSet A
  · rw [mat_of_mem hi, Matrix.one_apply_ne]
    rintro rfl
    obtain ⟨a, _, ha⟩ := h
    exact ha rfl
  · rw [mat_of_not_mem hi]
    exact (comp_eq S hA (exists_ne_zero_of_not_mem hi) (compLin g i j)
      fun s hs u => compLin_rel hg hs i j u).2 h

theorem mat_unitary (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs S.D)) :
    conjTr S.D.σ.toRingEquiv (mat g (fixedSet A)) * mat g (fixedSet A) = 1 := by
  ext i k
  rw [show (conjTr S.D.σ.toRingEquiv (mat g (fixedSet A)) * mat g (fixedSet A)) i k =
      ∑ j, S.D.σ (mat g (fixedSet A) j i) * mat g (fixedSet A) j k by
    simp [conjTr, Matrix.mul_apply]]
  by_cases hi : i ∈ fixedSet A
  · simp only [mat_of_mem hi]
    have h1 : ∑ j, S.D.σ ((1 : Matrix (Fin 3) (Fin 3) E) j i) * mat g (fixedSet A) j k =
        mat g (fixedSet A) i k := by
      simp [Matrix.one_apply]
    rw [h1]
    by_cases hk : k ∈ fixedSet A
    · exact mat_of_mem hk i
    · obtain ⟨a, ha, hak⟩ := exists_ne_zero_of_not_mem hk
      rw [mat_zero hA hg ⟨a, ha, by rwa [mem_fixedSet.1 hi a ha]⟩, Matrix.one_apply_ne]
      rintro rfl
      exact hk hi
  · by_cases hk : k ∈ fixedSet A
    · simp only [mat_of_mem hk]
      have h1 : ∑ j, S.D.σ (mat g (fixedSet A) j i) * (1 : Matrix (Fin 3) (Fin 3) E) j k =
          S.D.σ (mat g (fixedSet A) k i) := by
        simp [Matrix.one_apply]
      rw [h1]
      obtain ⟨a, ha, hai⟩ := exists_ne_zero_of_not_mem hi
      rw [mat_zero hA hg ⟨a, ha, by rwa [mem_fixedSet.1 hk a ha]⟩, map_zero, Matrix.one_apply_ne]
      rintro rfl
      exact hi hk
    · have hH : ∑ j, S.D.σ (mat g (fixedSet A) j i) * mat g (fixedSet A) j k =
          S.D.σ (mat g (fixedSet A) 0 i) * mat g (fixedSet A) 0 k +
          S.D.σ (mat g (fixedSet A) 1 i) * mat g (fixedSet A) 1 k +
          S.D.σ (mat g (fixedSet A) 2 i) * mat g (fixedSet A) 2 k := Fin.sum_univ_three _
      have hσH : S.D.σ (∑ j, S.D.σ (mat g (fixedSet A) j i) * mat g (fixedSet A) j k) =
          mat g (fixedSet A) 0 i * S.D.σ (mat g (fixedSet A) 0 k) +
          mat g (fixedSet A) 1 i * S.D.σ (mat g (fixedSet A) 1 k) +
          mat g (fixedSet A) 2 i * S.D.σ (mat g (fixedSet A) 2 k) := by
        simp [Fin.sum_univ_three, S.D.sigma_sigma]
      have key : ∀ u : E,
          (S.D.σ (∑ j, S.D.σ (mat g (fixedSet A) j i) * mat g (fixedSet A) j k) -
            (1 : Matrix (Fin 3) (Fin 3) E) i k) * u +
          ((∑ j, S.D.σ (mat g (fixedSet A) j i) * mat g (fixedSet A) j k) -
            (1 : Matrix (Fin 3) (Fin 3) E) i k) * S.D.σ u = 0 := by
        intro u
        have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
          ((Pi.single i u : Fin 3 → E), (0 : K × K)) ((Pi.single k 1 : Fin 3 → E), (0 : K × K))
        rw [g_single hA hg hi, g_single hA hg hk, polar_mat_single, polar_Qs] at h
        have h' := congrArg (algebraMap K E) h
        rw [hσH, hH]
        by_cases hik : i = k
        · subst hik
          simp [algebraMap_polar_N, Fin.sum_univ_three] at h'
          rw [Matrix.one_apply_eq]
          linear_combination h'
        · simp [algebraMap_polar_N, Fin.sum_univ_three, hik] at h'
          rw [Matrix.one_apply_ne hik]
          linear_combination h'
      exact sub_eq_zero.1 (eq_zero_of_forall S.D key).2

theorem g_W {w : Vs K E} (hw : ∀ i ∈ fixedSet A, w.1 i = 0) (hw2 : w.2 = 0) :
    g w = (mat g (fixedSet A) *ᵥ w.1, w.2) := by
  have e : w = ((Pi.single 0 (w.1 0) : Fin 3 → E), (0 : K × K)) +
      ((Pi.single 1 (w.1 1) : Fin 3 → E), (0 : K × K)) +
      ((Pi.single 2 (w.1 2) : Fin 3 → E), (0 : K × K)) := by
    refine Prod.ext (funext fun j => ?_) ?_
    · fin_cases j <;> simp
    · simp [hw2]
  rw [congrArg g e, map_add, map_add, g_single' hA hg 0 (w.1 0) (hw 0),
    g_single' hA hg 1 (w.1 1) (hw 1), g_single' hA hg 2 (w.1 2) (hw 2)]
  refine Prod.ext (funext fun j => ?_) ?_
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [hw2]

end Cent

end CDec

section Std

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

open CDec in
theorem centralizer_decomp (A : AddSubgroup (Fin 3 → ZMod p)) (hA : Coherent A)
    {g : Vs K E ≃ₗ[K] Vs K E} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs S.D))
    (hg : ∀ a ∈ A, g * tor S a = tor S a * g) :
    ∃ (f : Vs K E ≃ₗ[K] Vs K E) (M : GL (Fin 3) E), f ∈ Supp S.D (fixedSet A) ∧
      UniBdP S.D A M ∧ g = f * matToG K M ∧ (g ∈ Om S.D → f ∈ Om S.D) := by
  have hU := mat_unitary hA hg hgO
  let Mg : GL (Fin 3) E := ⟨mat g (fixedSet A), conjTr S.D.σ.toRingEquiv (mat g (fixedSet A)),
    mul_eq_one_comm.1 hU, hU⟩
  have hMg : Mg ∈ Uni S.D := hU
  have hmU : ∀ v ∈ Ufix K E (fixedSet A), matToG K Mg v = v := fun v hv =>
    Prod.ext (mulVec_eq_self (fun i hi => mat_mulVec_single hi) hv) rfl
  have hmU' : ∀ v ∈ Ufix K E (fixedSet A), (matToG K Mg)⁻¹ v = v := by
    intro v hv
    calc (matToG K Mg)⁻¹ v = (matToG K Mg)⁻¹ (matToG K Mg v) := by rw [hmU v hv]
      _ = v := by simp
  have hginv : ∀ a ∈ A, g⁻¹ * tor S a = tor S a * g⁻¹ := fun a ha =>
    (Commute.inv_left (hg a ha) : _)
  have hSupp : g * (matToG K Mg)⁻¹ ∈ Supp S.D (fixedSet A) := by
    refine ⟨mul_mem hgO (inv_mem (matToG_mem_orth S.D hMg)), fun v => ?_, fun v hv hv2 => ?_⟩
    · rw [LinearEquiv.mul_apply]
      constructor
      · intro hv
        rw [hmU' v hv]
        exact mem_Ufix_of_comm hg hv
      · intro hv
        have h1 : (matToG K Mg)⁻¹ v ∈ Ufix K E (fixedSet A) := by
          have := mem_Ufix_of_comm hginv hv
          simpa using this
        have h2 := hmU _ h1
        rw [show matToG K Mg ((matToG K Mg)⁻¹ v) = v by simp] at h2
        rw [h2]
        exact h1
    · rw [LinearEquiv.mul_apply]
      have hw1 : ∀ i ∈ fixedSet A, ((matToG K Mg)⁻¹ v).1 i = 0 := by
        intro i hi
        show (conjTr S.D.σ.toRingEquiv (mat g (fixedSet A)) *ᵥ v.1) i = 0
        refine mulVec_apply_eq_zero (fun i hi k => ?_) hv hi
        simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, mat_of_mem hi]
        simp [Matrix.one_apply, eq_comm]
      have hw2 : ((matToG K Mg)⁻¹ v).2 = 0 := hv2
      rw [g_W hA hg hw1 hw2]
      show matToG K Mg ((matToG K Mg)⁻¹ v) = v
      simp
  refine ⟨g * (matToG K Mg)⁻¹, Mg, hSupp, ⟨hMg, fun i hi => ?_, fun i j hij => mat_zero hA hg hij⟩,
    (inv_mul_cancel_right g _).symm,
    fun hgOm => mul_mem hgOm (inv_mem (matToG_mem_Om S.D hMg))⟩
  exact mat_mulVec_single (mem_fixedSet.2 hi)

set_option linter.unusedSectionVars false in
theorem supp_commute_matToG (A : AddSubgroup (Fin 3 → ZMod p)) {f : Vs K E ≃ₗ[K] Vs K E}
    (hf : f ∈ Supp S.D (fixedSet A)) {M : GL (Fin 3) E} (hM : UniBdP S.D A M) :
    f * matToG K M = matToG K M * f := by
  obtain ⟨-, hfU, hfW⟩ := hf
  obtain ⟨hMU, hMcol, -⟩ := hM
  have hcol : ∀ i ∈ fixedSet A,
      (M : Matrix (Fin 3) (Fin 3) E) *ᵥ Pi.single i 1 = Pi.single i 1 :=
    fun i hi => hMcol i (mem_fixedSet.1 hi)
  have hmU : ∀ v ∈ Ufix K E (fixedSet A), matToG K M v = v :=
    fun v hv => Prod.ext (CDec.mulVec_eq_self hcol hv) rfl
  have hmW : ∀ w : Vs K E, (∀ i ∈ fixedSet A, w.1 i = 0) →
      ∀ i ∈ fixedSet A, (matToG K M w).1 i = 0 := fun w hw i hi =>
    CDec.mulVec_apply_eq_zero (fun i hi k => CDec.row_eq_of_col S.D hMU (hcol i hi) k) hw hi
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  let u : Vs K E := (fun j => if j ∈ fixedSet A then v.1 j else 0, v.2)
  let w : Vs K E := (fun j => if j ∈ fixedSet A then 0 else v.1 j, 0)
  have hvuw : v = u + w := Prod.ext (funext fun j => by
    by_cases hj : j ∈ fixedSet A <;> simp [u, w, hj]) (by simp [u, w])
  have huU : u ∈ Ufix K E (fixedSet A) := fun j hj => by simp [u, hj]
  have hwF : ∀ i ∈ fixedSet A, w.1 i = 0 := fun i hi => by simp [w, hi]
  have hw2 : w.2 = 0 := rfl
  have hfu : f u ∈ Ufix K E (fixedSet A) := (hfU u).1 huU
  rw [hvuw]
  simp only [map_add]
  rw [hmU u huU, hfW w hwF hw2, hfW _ (hmW w hwF) hw2, hmU _ hfu]

end Std

end CFSG.RankThree.PartOne.KFR4
