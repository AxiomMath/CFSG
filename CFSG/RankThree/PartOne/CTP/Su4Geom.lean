module

public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

section Orth

variable {K : Type} [Field K] (σ : K ≃+* K) {n : ℕ}

@[expose] def hermOrth (S : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {v | ∀ s ∈ S, herm σ s v = 0}
  add_mem' := fun {a b} ha hb s hs => by rw [herm_add_right, ha s hs, hb s hs, add_zero]
  zero_mem' := fun s _ => herm_zero_right σ s
  smul_mem' := fun c v hv s hs => by rw [herm_smul_right, hv s hs, mul_zero]

theorem mem_hermOrth {S : Submodule K (Fin n → K)} {v : Fin n → K} :
    v ∈ hermOrth σ S ↔ ∀ s ∈ S, herm σ s v = 0 := Iff.rfl

@[expose] def conjV (v : Fin n → K) : Fin n → K := fun i => σ (v i)

theorem conjV_conjV (hσ : ∀ c, σ (σ c) = c) (v : Fin n → K) : conjV σ (conjV σ v) = v := by
  funext i
  simp [conjV, hσ]

@[expose] def conjSub (_hσ : ∀ c, σ (σ c) = c) (S : Submodule K (Fin n → K)) :
    Submodule K (Fin n → K) where
  carrier := {v | conjV σ v ∈ S}
  add_mem' := fun {a b} ha hb => by
    have : conjV σ (a + b) = conjV σ a + conjV σ b := by
      funext i
      simp [conjV]
    show conjV σ (a + b) ∈ S
    rw [this]
    exact S.add_mem ha hb
  zero_mem' := by
    have : conjV σ (0 : Fin n → K) = 0 := by
      funext i
      simp [conjV]
    show conjV σ 0 ∈ S
    rw [this]
    exact S.zero_mem
  smul_mem' := fun c v hv => by
    have : conjV σ (c • v) = σ c • conjV σ v := by
      funext i
      simp [conjV]
    show conjV σ (c • v) ∈ S
    rw [this]
    exact S.smul_mem _ hv

theorem finrank_conjSub (hσ : ∀ c, σ (σ c) = c) (S : Submodule K (Fin n → K)) :
    Module.finrank K (conjSub σ hσ S) = Module.finrank K S := by
  let j : conjSub σ hσ S ≃+ S :=
    { toFun := fun v => ⟨conjV σ v.1, v.2⟩
      invFun := fun s => ⟨conjV σ s.1, by
        show conjV σ (conjV σ s.1) ∈ S
        rw [conjV_conjV σ hσ]
        exact s.2⟩
      left_inv := fun v => Subtype.ext (conjV_conjV σ hσ v.1)
      right_inv := fun s => Subtype.ext (conjV_conjV σ hσ s.1)
      map_add' := fun a b => by
        apply Subtype.ext
        funext i
        simp [conjV] }
  have h : Module.rank K (conjSub σ hσ S) = Module.rank K S := by
    refine rank_eq_of_equiv_equiv (σ : K → K) j σ.bijective ?_
    intro r m
    apply Subtype.ext
    funext i
    simp [j, conjV]
  unfold Module.finrank
  rw [h]

theorem finrank_hermOrth_add (hσ : ∀ c, σ (σ c) = c) (S : Submodule K (Fin n → K)) :
    Module.finrank K (hermOrth σ S) + Module.finrank K S = n := by
  have hnd : (Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero (by simp))
  have h := LinearMap.BilinForm.finrank_orthogonal hnd (conjSub σ hσ S)
  have hort : hermOrth σ S =
      (Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) K)).orthogonal (conjSub σ hσ S) := by
    ext v
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro hv m hm
      have h1 := hv (conjV σ m) hm
      have h2 : herm σ (conjV σ m) v = m ⬝ᵥ v := by
        simp only [herm, conjV, hσ]
        rfl
      rw [Matrix.toBilin'_apply', Matrix.one_mulVec]
      rw [h2] at h1
      exact h1
    · intro hv s hs
      have hm : conjV σ s ∈ conjSub σ hσ S := by
        show conjV σ (conjV σ s) ∈ S
        rw [conjV_conjV σ hσ]
        exact hs
      have h1 := hv _ hm
      rw [Matrix.toBilin'_apply', Matrix.one_mulVec] at h1
      have h2 : herm σ s v = conjV σ s ⬝ᵥ v := rfl
      rw [h2]
      exact h1
  rw [hort]
  have h2 : Module.finrank K S ≤ n := by simpa using Submodule.finrank_le S
  rw [finrank_conjSub σ hσ S] at h
  simp only [Module.finrank_fin_fun] at h
  omega

end Orth

section Eig

variable {K : Type} [Field K] {σ : K ≃+* K}

abbrev matU {n : ℕ} (g : SUid σ n) : Matrix (Fin n) (Fin n) K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem matU_one {n : ℕ} : matU (1 : SUid σ n) = 1 := rfl

theorem matU_mul {n : ℕ} (g h : SUid σ n) : matU (g * h) = matU g * matU h := rfl

@[expose] noncomputable def actU (σ : K ≃+* K) (n : ℕ) : SUid σ n →* Module.End K (Fin n → K) where
  toFun g := Matrix.mulVecLin (matU g)
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [matU_one]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp [matU_mul, Matrix.mulVec_mulVec]

@[expose] noncomputable def eigU (g : SUid σ 4) (l : K) : Submodule K (Fin 4 → K) :=
  Module.End.eigenspace (Matrix.mulVecLin (matU g)) l

theorem mem_eigU {g : SUid σ 4} {l : K} {v : Fin 4 → K} : v ∈ eigU g l ↔ g • v = l • v := by
  simp [eigU, smul_def]

theorem herm_eigU_eq_zero (g : SUid σ 4) {l m : K} (hlm : σ l * m ≠ 1) {u v : Fin 4 → K}
    (hu : u ∈ eigU g l) (hv : v ∈ eigU g m) : herm σ u v = 0 := by
  have h := herm_smul_smul σ g u v
  rw [mem_eigU.mp hu, mem_eigU.mp hv, herm_smul_left, herm_smul_right, ← mul_assoc] at h
  have h2 : (σ l * m - 1) * herm σ u v = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hlm)

theorem eq_one_of_mul_self_eq_one' [CharP K 2] {l : K} (h : l * l = 1) : l = 1 := by
  rcases mul_self_eq_one_iff.mp h with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

theorem actU_pow_eq_one {n p : ℕ} {g : SUid σ n} (hg : g ^ p = 1) :
    (Matrix.mulVecLin (matU g) : Module.End K (Fin n → K)) ^ p = 1 := by
  have h := congrArg (actU σ n) hg
  rwa [map_pow, map_one] at h

theorem iSup_eigU_eq_top {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) {g : SUid σ 4}
    (hg : g ^ p = 1) : ⨆ l, eigU g l = ⊤ :=
  CFSG.RankThree.PartOne.iSup_eigenspace_eq_top_of_pow_eq_one hζ (actU_pow_eq_one hg)

theorem pow_eq_one_of_mem_eigU {n p : ℕ} {g : SUid σ n} (hg : g ^ p = 1) {l : K}
    {v : Fin n → K} (hv : v ∈ Module.End.eigenspace (Matrix.mulVecLin (matU g)) l) (hv0 : v ≠ 0) :
    l ^ p = 1 := by
  have h1 := actU_pow_eq_one hg
  have hev : Module.End.HasEigenvector (Matrix.mulVecLin (matU g)) l v := ⟨hv, hv0⟩
  have h2 := hev.pow_apply p
  rw [h1, Module.End.one_apply] at h2
  have h3 : (l ^ p - 1) • v = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hv0)

@[expose] noncomputable def movU (g : SUid σ 4) : Submodule K (Fin 4 → K) :=
  ⨆ (l : K) (_ : l ≠ 1), eigU g l

theorem eigU_le_movU {g : SUid σ 4} {l : K} (hl : l ≠ 1) : eigU g l ≤ movU g :=
  le_iSup₂_of_le l hl le_rfl

theorem movU_le_hermOrth_eigU_one (g : SUid σ 4) : movU g ≤ hermOrth σ (eigU g 1) := by
  refine iSup₂_le fun l hl v hv => ?_
  rw [mem_hermOrth]
  intro s hs
  exact herm_eigU_eq_zero g (by simpa using hl) hs hv

theorem isCompl_eigU_one_movU {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {g : SUid σ 4} (hg : g ^ p = 1) : IsCompl (eigU g 1) (movU g) := by
  have hind : iSupIndep (fun l : K => eigU g l) := Module.End.eigenspaces_iSupIndep _
  refine ⟨hind 1, ?_⟩
  rw [codisjoint_iff, eq_top_iff, ← iSup_eigU_eq_top hζ hg, iSup_split_single _ (1 : K)]
  exact le_rfl

theorem eq_zero_of_herm_sup (hσ : ∀ c, σ (σ c) = c) {S T : Submodule K (Fin 4 → K)}
    (h : S ⊔ T = ⊤) {v : Fin 4 → K} (hS : ∀ s ∈ S, herm σ s v = 0)
    (hT : ∀ t ∈ T, herm σ t v = 0) : v = 0 := by
  refine eq_zero_of_herm σ fun y => ?_
  have hy : y ∈ S ⊔ T := by rw [h]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  rw [herm_add_right, herm_eq_zero_comm σ hσ (hS s hs), herm_eq_zero_comm σ hσ (hT t ht),
    add_zero]

theorem eigU_one_nondeg (hσ : ∀ c, σ (σ c) = c) {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {g : SUid σ 4} (hg : g ^ p = 1) {u : Fin 4 → K}
    (hu : u ∈ eigU g 1) (h : ∀ w ∈ eigU g 1, herm σ w u = 0) : u = 0 := by
  refine eq_zero_of_herm_sup hσ (isCompl_eigU_one_movU hζ hg).sup_eq_top h fun t ht => ?_
  exact herm_eq_zero_comm σ hσ (movU_le_hermOrth_eigU_one g ht u hu)

theorem movU_nondeg (hσ : ∀ c, σ (σ c) = c) {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) {g : SUid σ 4} (hg : g ^ p = 1) {u : Fin 4 → K}
    (hu : u ∈ movU g) (h : ∀ w ∈ movU g, herm σ w u = 0) : u = 0 :=
  eq_zero_of_herm_sup hσ (isCompl_eigU_one_movU hζ hg).sup_eq_top
    (fun s hs => movU_le_hermOrth_eigU_one g hu s hs) h

theorem finrank_eigU_one_add_movU {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {g : SUid σ 4} (hg : g ^ p = 1) :
    Module.finrank K (eigU g 1) + Module.finrank K (movU g) = 4 := by
  have h := Submodule.finrank_add_eq_of_isCompl (isCompl_eigU_one_movU hζ hg)
  simpa using h

section Dim

variable {K : Type} [Field K] {σ : K ≃+* K} {p : ℕ} [NeZero p] {ζ : K}

theorem ne_zero_of_pow_eq_one' {l : K} (hl : l ^ p = 1) : l ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne p)] at hl
  exact zero_ne_one hl

theorem herm_eigU_self_eq_zero [CharP K 2] (g : SUid σ 4) {l : K} (hl : l ≠ 1) (hσl : σ l = l)
    {u v : Fin 4 → K} (hu : u ∈ eigU g l) (hv : v ∈ eigU g l) : herm σ u v = 0 := by
  refine herm_eigU_eq_zero g (fun h => hl ?_) hu hv
  rw [hσl] at h
  exact eq_one_of_mul_self_eq_one' h

theorem finrank_eigU_le_two [CharP K 2] (hσ : ∀ c, σ (σ c) = c) (g : SUid σ 4) {l : K}
    (hl : l ≠ 1) (hσl : σ l = l) : Module.finrank K (eigU g l) ≤ 2 := by
  have hle : eigU g l ≤ hermOrth σ (eigU g l) := fun v hv =>
    (mem_hermOrth σ).mpr fun s hs => herm_eigU_self_eq_zero g hl hσl hs hv
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_hermOrth_add σ hσ (eigU g l)
  omega

theorem finrank_eigU_le_inv (hσ : ∀ c, σ (σ c) = c) (hζ : IsPrimitiveRoot ζ p) {g : SUid σ 4}
    (hg : g ^ p = 1) {l : K} (hσl : σ l = l) :
    Module.finrank K (eigU g l) ≤ Module.finrank K (eigU g l⁻¹) := by
  set U : Submodule K (Fin 4 → K) := ⨆ (m : K) (_ : m ≠ l⁻¹), eigU g m with hU
  have hind : iSupIndep (fun m : K => eigU g m) := Module.End.eigenspaces_iSupIndep _
  have hdisj : Disjoint (eigU g l⁻¹) U := hind l⁻¹
  have hsup : eigU g l⁻¹ ⊔ U = ⊤ := by
    rw [eq_top_iff, ← iSup_eigU_eq_top hζ hg, iSup_split_single _ (l⁻¹)]
  have hUle : U ≤ hermOrth σ (eigU g l) := by
    refine iSup₂_le fun m hm v hv => ?_
    rw [mem_hermOrth]
    intro s hs
    refine herm_eigU_eq_zero g ?_ hs hv
    rw [hσl]
    intro h1
    exact hm (eq_inv_of_mul_eq_one_right h1)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (eigU g l⁻¹) U
  rw [hdisj.eq_bot, finrank_bot, hsup, finrank_top] at h1
  have h2 := Submodule.finrank_mono hUle
  have h3 := finrank_hermOrth_add σ hσ (eigU g l)
  simp only [Module.finrank_fin_fun] at h1 h3
  omega

theorem finrank_eigU_inv (hσ : ∀ c, σ (σ c) = c) (hζ : IsPrimitiveRoot ζ p) {g : SUid σ 4}
    (hg : g ^ p = 1) (hfix : ∀ l : K, l ^ p = 1 → σ l = l) {l : K} (hlp : l ^ p = 1) :
    Module.finrank K (eigU g l) = Module.finrank K (eigU g l⁻¹) := by
  have hl0 := ne_zero_of_pow_eq_one' hlp
  have hlp' : (l⁻¹) ^ p = 1 := by rw [inv_pow, hlp, inv_one]
  have h1 := finrank_eigU_le_inv hσ hζ hg (hfix l hlp)
  have h2 := finrank_eigU_le_inv hσ hζ hg (hfix _ hlp')
  rw [inv_inv] at h2
  exact le_antisymm h1 h2

theorem disjoint_eigU {g : SUid σ 4} {l m : K} (h : l ≠ m) : Disjoint (eigU g l) (eigU g m) :=
  (Module.End.eigenspaces_iSupIndep _).pairwiseDisjoint h

end Dim

end Eig

end CFSG.RankThree.PartOne.CTP
