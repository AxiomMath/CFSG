module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOrthogonalBlocks
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.RankThree.Classical.OrthogonalOrderThree
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.RankThree.CentralCover.LinearUnitaryFourGroupWitness

public noncomputable section

universe u

namespace CFSG.RankThree.CentralCover

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancingLocal.OrthogonalBlocks
open scoped Pointwise

section Data

theorem cycledData_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : ∃ v₁ v₂ v₃ a b : G, CycledFourGroup v₁ v₂ v₃ a ∧ b⁻¹ * a * b = a⁻¹ ∧ orderOf b = 2) :
    ∃ v₁ v₂ v₃ a b : H, CycledFourGroup v₁ v₂ v₃ a ∧ b⁻¹ * a * b = a⁻¹ ∧ orderOf b = 2 := by
  obtain ⟨v₁, v₂, v₃, a, b, h, hb, hb2⟩ := hG
  refine ⟨e v₁, e v₂, e v₃, e a, e b,
    h.map e.toMonoidHom (fun h1 => h.ne_one (e.injective (h1.trans (map_one e).symm))), ?_, ?_⟩
  · rw [← map_inv, ← map_mul, ← map_mul, hb, map_inv]
  · rw [MulEquiv.orderOf_eq]
    exact hb2

theorem cycledData_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (S : Subgroup (GL ι F)) {G₀ : Type*} [Group G₀] {g₁ g₂ g₃ c d : G₀}
    (h : CycledFourGroup g₁ g₂ g₃ c) (hd : d⁻¹ * c * d = c⁻¹) (hd2 : d ^ 2 = 1)
    (ψ : G₀ →* GL ι F) (hψ : Function.Injective ψ) (h₁ : ψ g₁ ∈ S) (h₂ : ψ g₂ ∈ S)
    (h₃ : ψ g₃ ∈ S) (hc : ψ c ∈ S) (hdS : ψ d ∈ S) :
    ∃ v₁ v₂ v₃ a b : StatedProj S, CycledFourGroup v₁ v₂ v₃ a ∧ b⁻¹ * a * b = a⁻¹ ∧
      orderOf b = 2 := by
  have hne : ψ g₁ ≠ 1 := fun h1 => h.ne_one (hψ (h1.trans (map_one ψ).symm))
  have hS : CycledFourGroup (⟨ψ g₁, h₁⟩ : S) ⟨ψ g₂, h₂⟩ ⟨ψ g₃, h₃⟩ ⟨ψ c, hc⟩ :=
    CycledFourGroup.of_injective (f := S.subtype) S.subtype_injective (h.map ψ hne)
  have hdS' : (⟨ψ d, hdS⟩ : S)⁻¹ * ⟨ψ c, hc⟩ * ⟨ψ d, hdS⟩ = (⟨ψ c, hc⟩ : S)⁻¹ :=
    Subtype.ext (by
      change (ψ d)⁻¹ * ψ c * ψ d = (ψ c)⁻¹
      rw [← map_inv, ← map_mul, ← map_mul, hd, map_inv])
  have hd2S : (⟨ψ d, hdS⟩ : S) ^ 2 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow]; change ψ d ^ 2 = 1; rw [← map_pow, hd2, map_one])
  obtain ⟨-, h', -, hbc, hb2⟩ :=
    hS.quotient_witness hdS' hd2S (statedProjMk S) (ker_statedProjMk_le_center S)
  exact ⟨_, _, _, _, _, h', hbc, hb2⟩

theorem witness_of_cycledData {T : Type*} [Group T]
    (hT : ∃ v₁ v₂ v₃ a b : T, CycledFourGroup v₁ v₂ v₃ a ∧ b⁻¹ * a * b = a⁻¹ ∧ orderOf b = 2) :
    ∃ (V : Subgroup T) (a b : T), IsKleinFour V ∧ orderOf a = 3 ∧ orderOf b = 2 ∧
      a ∈ normalizer (V : Set T) ∧ b⁻¹ * a * b = a⁻¹ ∧
      (∃ w₁ w₂ w₃ : T, (V : Set T) = {1, w₁, w₂, w₃} ∧ w₁ ≠ 1 ∧ w₂ ≠ 1 ∧ w₃ ≠ 1 ∧ w₁ ≠ w₂ ∧
        w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧ a * w₁ * a⁻¹ = w₂ ∧ a * w₂ * a⁻¹ = w₃ ∧ a * w₃ * a⁻¹ = w₁) ∧
      V ⊓ zpowers a = ⊥ ∧ (V : Set T) * (zpowers a : Set T) = (V ⊔ zpowers a : Subgroup T) ∧
      Nat.card (V ⊔ zpowers a : Subgroup T) = 12 ∧
      ∀ (K : Type u) [Group K] [Finite K] (π : K →* T), Function.Surjective π →
        π.ker ≤ center K → IsPGroup 3 π.ker →
        (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = V ∧ Set.InjOn π U) ∧
        ∀ U : Subgroup K, IsPGroup 2 U → U.map π = V → Set.InjOn π U →
          π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
          ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = a ∧
            (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
              u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
              x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
            x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
            (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
            (U ⊔ zpowers x).map π = V ⊔ zpowers a ∧
            Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
            π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧
            π.ker ⊔ (U ⊔ zpowers x) = (V ⊔ zpowers a).comap π := by
  obtain ⟨v₁, v₂, v₃, a, b, h, hb, hb2⟩ := hT
  have hV := h.coe_closure
  obtain ⟨hK, ha3, hN, hdisj, hmul, hcard⟩ := h.quotient_facts hV
  refine ⟨closure {v₁, v₂, v₃}, a, b, hK, ha3, hb2, hN, hb, ⟨v₁, v₂, v₃, hV, h.ne_one,
    h.two_ne_one, h.three_ne_one, h.one_ne_two, h.one_ne_three, h.two_ne_three, h.conj_one,
    h.conj_two, h.conj_three⟩, hdisj, hmul, hcard, ?_⟩
  intro K _ _ π hπ hZ hZ3
  exact h.cover hb hV π hπ hZ hZ3

end Data

section Three

variable (F : Type) [Field F]

theorem exists_gl3_data :
    ∃ g₁ g₂ g₃ c d : GL (Fin 3) F, CycledFourGroup g₁ g₂ g₃ c ∧ d⁻¹ * c * d = c⁻¹ ∧
      d ^ 2 = 1 ∧ (g₁ : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      (g₂ : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ (g₃ : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
      (c : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ (d : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  by_cases hF : ringChar F = 2
  · have : CharP F 2 := ringChar.eq_iff.1 hF
    exact ⟨_, _, _, _, _, evenCycled F, evenB₀_conj F, evenB₀_sq F, det_evenU₁ F, det_evenU₂ F,
      det_evenU₃ F, det_evenA₀ F, det_evenB₀ F⟩
  · exact ⟨_, _, _, _, _, oddCycled F hF, oddB₀_conj F, oddB₀_sq F, det_oddDiag₁ F,
      det_oddDiag₂ F, det_oddDiag₃ F, det_oddA₀ F, det_oddB₀ F⟩

end Three

section Embed

variable {F : Type} [Field F] {r : ℕ}

@[expose] def finSplit3 (hr : 3 ≤ r) : Fin 3 ⊕ Fin (r - 3) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hr))

@[expose] def embed3GL (hr : 3 ≤ r) : GL (Fin 3) F →* GL (Fin r) F :=
  (Units.map (MonoidHom.ofClass (reindexAlgEquiv F F (finSplit3 hr)))).comp
    (blockDiagHom (MonoidHom.id _) 1)

theorem coe_embed3GL (hr : 3 ≤ r) (g : GL (Fin 3) F) :
    (embed3GL hr g : Matrix (Fin r) (Fin r) F) =
      reindex (finSplit3 hr) (finSplit3 hr)
        (fromBlocks (g : Matrix (Fin 3) (Fin 3) F) 0 0
          (1 : Matrix (Fin (r - 3)) (Fin (r - 3)) F)) := by
  simp [embed3GL, coe_blockDiagHom, Matrix.coe_reindexAlgEquiv]

theorem embed3GL_injective (hr : 3 ≤ r) : Function.Injective (embed3GL (F := F) hr) := by
  intro g g' h
  have h' := congrArg (fun x : GL (Fin r) F => (x : Matrix (Fin r) (Fin r) F)) h
  simp only [coe_embed3GL] at h'
  exact Units.ext ((fromBlocks_inj.1 ((reindex _ _).injective h')).1)

theorem det_embed3GL (hr : 3 ≤ r) (g : GL (Fin 3) F) :
    (embed3GL hr g : Matrix (Fin r) (Fin r) F).det = (g : Matrix (Fin 3) (Fin 3) F).det := by
  rw [coe_embed3GL, det_reindex_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem unitary_embed3GL (hr : 3 ≤ r) {q : ℕ} (hq : q ≠ 0) {g : GL (Fin 3) F}
    (hg : ((g : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ * (g : Matrix (Fin 3) (Fin 3) F) = 1) :
    ((embed3GL hr g : Matrix (Fin r) (Fin r) F).map (· ^ q))ᵀ *
      (embed3GL hr g : Matrix (Fin r) (Fin r) F) = 1 := by
  have h0 : ∀ {m n : Type} [Fintype m] [Fintype n], (0 : Matrix m n F).map (· ^ q) = 0 :=
    fun {_ _} _ _ => Matrix.map_zero _ (zero_pow hq)
  rw [coe_embed3GL, reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
    fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h0,
    Matrix.map_one (fun x : F => x ^ q) (zero_pow hq) (one_pow q), hg]
  simp only [transpose_zero, transpose_one, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.mul_one, fromBlocks_one, submatrix_one_equiv]

end Embed

section Linear

variable {F : Type} [Field F]

theorem cycledData_statedSL {r : ℕ} (hr : 3 ≤ r) :
    ∃ v₁ v₂ v₃ a b : StatedProj (StatedSL r F), CycledFourGroup v₁ v₂ v₃ a ∧
      b⁻¹ * a * b = a⁻¹ ∧ orderOf b = 2 := by
  obtain ⟨g₁, g₂, g₃, c, d, h, hd, hd2, h₁, h₂, h₃, hc, hdd⟩ := exists_gl3_data F
  have hmem : ∀ g : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      embed3GL hr g ∈ StatedSL r F := fun g hg =>
    subset_closure (show (embed3GL hr g : Matrix (Fin r) (Fin r) F).det = 1 by
      rw [det_embed3GL, hg])
  exact cycledData_statedProj _ h hd hd2 (embed3GL hr) (embed3GL_injective hr) (hmem _ h₁)
    (hmem _ h₂) (hmem _ h₃) (hmem _ hc) (hmem _ hdd)

theorem cycledData_statedSU_odd {r q : ℕ} (hr : 3 ≤ r) (hq : Odd q) (hF : ringChar F ≠ 2) :
    ∃ v₁ v₂ v₃ a b : StatedProj (StatedSU r q F), CycledFourGroup v₁ v₂ v₃ a ∧
      b⁻¹ * a * b = a⁻¹ ∧ orderOf b = 2 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact absurd hq (by decide)
  have hmem : ∀ g : GL (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F).det = 1 →
      ((g : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ * (g : Matrix (Fin 3) (Fin 3) F) = 1 →
      embed3GL hr g ∈ StatedSU r q F := fun g hg hgu =>
    subset_closure ⟨by rw [det_embed3GL, hg], unitary_embed3GL hr hq0 hgu⟩
  exact cycledData_statedProj _ (oddCycled F hF) (oddB₀_conj F) (oddB₀_sq F) (embed3GL hr)
    (embed3GL_injective hr) (hmem _ (det_oddDiag₁ F) (unitary_oddDiag₁ hq))
    (hmem _ (det_oddDiag₂ F) (unitary_oddDiag₂ hq)) (hmem _ (det_oddDiag₃ F) (unitary_oddDiag₃ hq))
    (hmem _ (det_oddA₀ F) (unitary_oddA₀ hq)) (hmem _ (det_oddB₀ F) (unitary_oddB₀ hq))

@[expose] def permData {r : ℕ} (hr : 4 ≤ r) : Equiv.Perm (Fin 4) →* GL (Fin r) F :=
  CFSG.RankThree.Classical.permGL.comp (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hr))

theorem permData_injective {r : ℕ} (hr : 4 ≤ r) : Function.Injective (permData (F := F) hr) := by
  refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
  by_contra hne
  have hne' : Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hr) σ ≠ 1 := fun h1 =>
    hne (Equiv.Perm.viaEmbeddingHom_injective _ (h1.trans (map_one _).symm))
  apply CFSG.RankThree.Classical.permGL_not_mem_statedScalars (K := F) hne'
  change permData hr σ ∈ StatedScalars (Fin r) F
  rw [hσ]
  exact one_mem _

theorem permGL_mem_statedSU [CharP F 2] {r q : ℕ} (hq : q ≠ 0) (σ : Equiv.Perm (Fin r)) :
    CFSG.RankThree.Classical.permGL σ ∈ StatedSU r q F := by
  refine subset_closure ⟨?_, ?_⟩
  · rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> simp [h, CharTwo.neg_eq]
  · rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply]
    have hmap : ((σ⁻¹).permMatrix F).map (· ^ q) = (σ⁻¹).permMatrix F := by
      ext i j
      simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs
      · exact one_pow q
      · exact zero_pow hq
    rw [hmap, transpose_permMatrix, ← permMatrix_mul, inv_inv, inv_mul_cancel]
    simp

theorem cycledData_statedSU_even [CharP F 2] {r q : ℕ} (hr : 4 ≤ r) (hq : q ≠ 0) :
    ∃ v₁ v₂ v₃ a b : StatedProj (StatedSU r q F), CycledFourGroup v₁ v₂ v₃ a ∧
      b⁻¹ * a * b = a⁻¹ ∧ orderOf b = 2 := by
  have h : CycledFourGroup (Equiv.swap (0 : Fin 4) 1 * Equiv.swap 2 3)
      (Equiv.swap 0 3 * Equiv.swap 1 2) (Equiv.swap 0 2 * Equiv.swap 1 3)
      (Equiv.swap 0 2 * Equiv.swap 0 1) :=
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hmem : ∀ σ : Equiv.Perm (Fin 4), permData (F := F) hr σ ∈ StatedSU r q F := fun σ =>
    permGL_mem_statedSU hq _
  exact cycledData_statedProj _ h (d := Equiv.swap 0 1) (by decide) (by decide) (permData hr)
    (permData_injective hr) (hmem _) (hmem _) (hmem _) (hmem _) (hmem _)

end Linear

section Symplectic

variable {F : Type} [Field F]

theorem leviSp_injective {r : ℕ} :
    Function.Injective (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.leviSp
      (r := r) (k := F)) := by
  intro A B h
  have h' := congrArg (fun x : StatedSp r F =>
    ((x : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) h
  simp only [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.coe_leviSp] at h'
  exact Units.ext (fromBlocks_inj.1 h').1

theorem cycledData_statedSp {r : ℕ} (hr : 3 ≤ r) :
    ∃ v₁ v₂ v₃ a b : StatedProj (StatedSp r F), CycledFourGroup v₁ v₂ v₃ a ∧
      b⁻¹ * a * b = a⁻¹ ∧ orderOf b = 2 := by
  obtain ⟨g₁, g₂, g₃, c, d, h, hd, hd2, -⟩ := exists_gl3_data F
  let ψ : GL (Fin 3) F →* GL (Fin r ⊕ Fin r) F := (StatedSp r F).subtype.comp
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.leviSp.comp (embed3GL hr))
  have hψ : Function.Injective ψ :=
    (StatedSp r F).subtype_injective.comp (leviSp_injective.comp (embed3GL_injective hr))
  have hmem : ∀ g, ψ g ∈ StatedSp r F := fun g =>
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.leviSp (embed3GL hr g)).2
  exact cycledData_statedProj _ h hd hd2 ψ hψ (hmem _) (hmem _) (hmem _) (hmem _) (hmem _)

end Symplectic

section Orthogonal

variable {F : Type} [Field F] {r : ℕ} {M : Type} [Fintype M] [DecidableEq M]

theorem HypForm.rho_injective (H : HypForm r M F) : Function.Injective H.rho := by
  intro A B h
  have h' := congrArg (fun x : GL (Fin r ⊕ M) F => (x : Matrix (Fin r ⊕ M) (Fin r ⊕ M) F)) h
  simp only [HypForm.coe_rho] at h'
  exact Units.ext (fromBlocks_inj.1 h').1

theorem rho_embed3GL_mem_statedOmega (H : HypForm r M F) (hr : 3 ≤ r) {Q : (Fin r ⊕ M → F) → F}
    (hQ : ∀ v, H.Q v = Q v) {g : GL (Fin 3) F} (hg : (g : Matrix (Fin 3) (Fin 3) F).det = 1) :
    H.rho (embed3GL hr g) ∈ StatedOmega Q := by
  set O := closure {A : GL (Fin r ⊕ M) F | ∀ v, Q ((A : Matrix (Fin r ⊕ M) (Fin r ⊕ M) F) *ᵥ v) =
    Q v} with hO
  let φ : SpecialLinearGroup (Fin 3) F →* GL (Fin r ⊕ M) F :=
    (H.rho.comp (embed3GL hr)).comp SpecialLinearGroup.toGL
  have hφO : (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)).map φ ≤ O := by
    rintro _ ⟨x, -, rfl⟩
    refine subset_closure fun v => ?_
    rw [← hQ, ← hQ]
    exact H.rho_isometry _ v
  have hperf : (⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)), ⊤⁆ :
      Subgroup (SpecialLinearGroup (Fin 3) F)) = ⊤ :=
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3)
      le_rfl).commutator_eq_top
  have hmem : φ ⟨g, hg⟩ ∈ StatedOmega Q := by
    have hx : φ ⟨g, hg⟩ ∈ (⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)), ⊤⁆ :
        Subgroup (SpecialLinearGroup (Fin 3) F)).map φ := by
      rw [hperf]
      exact mem_map_of_mem φ (mem_top _)
    rw [map_commutator] at hx
    exact commutator_mono hφO hφO hx
  have hgl : SpecialLinearGroup.toGL (⟨g, hg⟩ : SpecialLinearGroup (Fin 3) F) = g := Units.ext rfl
  rw [← hgl]
  exact hmem

theorem cycledData_statedOmega (H : HypForm r M F) (hr : 3 ≤ r) {Q : (Fin r ⊕ M → F) → F}
    (hQ : ∀ v, H.Q v = Q v) :
    ∃ v₁ v₂ v₃ a b : StatedProj (StatedOmega Q), CycledFourGroup v₁ v₂ v₃ a ∧
      b⁻¹ * a * b = a⁻¹ ∧ orderOf b = 2 := by
  obtain ⟨g₁, g₂, g₃, c, d, h, hd, hd2, h₁, h₂, h₃, hc, hdd⟩ := exists_gl3_data F
  exact cycledData_statedProj _ h hd hd2 (H.rho.comp (embed3GL hr))
    ((HypForm.rho_injective H).comp (embed3GL_injective hr))
    (rho_embed3GL_mem_statedOmega H hr hQ h₁) (rho_embed3GL_mem_statedOmega H hr hQ h₂)
    (rho_embed3GL_mem_statedOmega H hr hQ h₃) (rho_embed3GL_mem_statedOmega H hr hQ hc)
    (rho_embed3GL_mem_statedOmega H hr hQ hdd)

theorem tail_Q_eq {W : Type} [Fintype W] [DecidableEq W] (qW : (W → F) → F)
    (v : Fin r ⊕ (Fin r ⊕ W) → F) :
    (HypForm.tail r W qW).Q v =
      ∑ i, v (.inl i) * v (.inr (.inl i)) + qW (v ∘ Sum.inr ∘ Sum.inr) := by
  simp [HypForm.Q, HypForm.tail, fromCols_mulVec, dotProduct, Function.comp_def]

theorem plus_Q_eq (v : Fin r ⊕ Fin r → F) :
    (HypForm.plus (K := F) r).Q v = ∑ i, v (.inl i) * v (.inr i) := by
  simp [HypForm.Q, HypForm.plus, dotProduct]

end Orthogonal

theorem higher_classical_central_three_cover_four_group_witness {T : Type} [Group T] [Finite T]
    {t : StatedLieTag} {n p f : ℕ} (hT : StatedClassicalModel T t n p f)
    (ht : ((t = .PSL ∨ t = .PSU) ∧ 4 ≤ n) ∨ (t = .PSp ∧ 3 ≤ n) ∨
      (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)) :
    ∃ (V : Subgroup T) (a b : T), IsKleinFour V ∧ orderOf a = 3 ∧ orderOf b = 2 ∧
      a ∈ normalizer (V : Set T) ∧ b⁻¹ * a * b = a⁻¹ ∧
      (∃ w₁ w₂ w₃ : T, (V : Set T) = {1, w₁, w₂, w₃} ∧ w₁ ≠ 1 ∧ w₂ ≠ 1 ∧ w₃ ≠ 1 ∧ w₁ ≠ w₂ ∧
        w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧ a * w₁ * a⁻¹ = w₂ ∧ a * w₂ * a⁻¹ = w₃ ∧ a * w₃ * a⁻¹ = w₁) ∧
      V ⊓ zpowers a = ⊥ ∧ (V : Set T) * (zpowers a : Set T) = (V ⊔ zpowers a : Subgroup T) ∧
      Nat.card (V ⊔ zpowers a : Subgroup T) = 12 ∧
      ∀ (K : Type u) [Group K] [Finite K] (π : K →* T), Function.Surjective π →
        π.ker ≤ center K → IsPGroup 3 π.ker →
        (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map π = V ∧ Set.InjOn π U) ∧
        ∀ U : Subgroup K, IsPGroup 2 U → U.map π = V → Set.InjOn π U →
          π.ker ⊓ U = ⊥ ∧ π.ker ⊔ U = V.comap π ∧
          ∃ x ∈ normalizer (U : Set K), orderOf x = 3 ∧ π x = a ∧
            (∃ u₁ u₂ u₃ : K, (U : Set K) = {1, u₁, u₂, u₃} ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₃ ≠ 1 ∧
              u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
              x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₃ ∧ x * u₃ * x⁻¹ = u₁) ∧
            x ∉ center K ∧ U ⊓ zpowers x = ⊥ ∧
            (U : Set K) * (zpowers x : Set K) = (U ⊔ zpowers x : Subgroup K) ∧
            (U ⊔ zpowers x).map π = V ⊔ zpowers a ∧
            Set.InjOn π (U ⊔ zpowers x : Subgroup K) ∧
            π.ker ⊓ (U ⊔ zpowers x) = ⊥ ∧
            π.ker ⊔ (U ⊔ zpowers x) = (V ⊔ zpowers a).comap π := by
  apply witness_of_cycledData
  obtain ⟨hadm, hmodel⟩ := hT
  rcases ht with ⟨rfl | rfl, hn⟩ | ⟨rfl, hn⟩ | (rfl | rfl | rfl)
  · obtain ⟨F, _, _, -, ⟨e⟩⟩ := hmodel
    exact cycledData_of_mulEquiv e.symm (cycledData_statedSL (by omega))
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
    have hp := hadm.1
    have hq0 : p ^ f ≠ 0 := pow_ne_zero _ hp.ne_zero
    by_cases h2 : ringChar F = 2
    · have : CharP F 2 := ringChar.eq_iff.1 h2
      exact cycledData_of_mulEquiv e.symm (cycledData_statedSU_even hn hq0)
    · have : Fintype F := Fintype.ofFinite F
      have hodd : Odd (p ^ f) := by
        have hcard : Fintype.card F % 2 ≠ 0 := fun h0 =>
          h2 (FiniteField.even_card_iff_char_two.2 h0)
        rw [← Nat.card_eq_fintype_card, hF] at hcard
        rcases Nat.even_or_odd (p ^ f) with he | ho
        · exact absurd (Nat.even_iff.1 (Nat.even_pow.2 ⟨he, by norm_num⟩)) hcard
        · exact ho
      exact cycledData_of_mulEquiv e.symm (cycledData_statedSU_odd (by omega) hodd h2)
  · obtain ⟨F, _, _, -, ⟨e⟩⟩ := hmodel
    exact cycledData_of_mulEquiv e.symm (cycledData_statedSp hn)
  · obtain ⟨F, _, _, -, ⟨e⟩⟩ := hmodel
    have hn : 3 ≤ n := hadm.2.2.1
    exact cycledData_of_mulEquiv e.symm (cycledData_statedOmega
      (HypForm.tail n Unit (fun w => w () ^ 2)) hn (fun v => by
        rw [tail_Q_eq]
        rfl))
  · obtain ⟨F, _, _, -, ⟨e⟩⟩ := hmodel
    have hn : 4 ≤ n := hadm.2.2
    exact cycledData_of_mulEquiv e.symm (cycledData_statedOmega (HypForm.plus n) (by omega)
      (fun v => by
        rw [plus_Q_eq]
        rfl))
  · obtain ⟨F, _, _, -, b, c, -, ⟨e⟩⟩ := hmodel
    have hn : 4 ≤ n := hadm.2.2
    exact cycledData_of_mulEquiv e.symm (cycledData_statedOmega
      (HypForm.tail (n - 1) (Fin 2) (fun w => w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2))
      (by omega) (fun v => by
        rw [tail_Q_eq]
        simp only [StatedQuadMinus, Function.comp_apply]
        ring))

end CFSG.RankThree.CentralCover
