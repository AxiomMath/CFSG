module

public import CFSG.Quasithin.Background.JonesParshallSp4Perfect
public import CFSG.Quasithin.Background.JonesParshallWords

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit
open scoped commutatorElement

section Group

variable {G : Type*} [Group G] {K : Subgroup G} {τ : G}

theorem zpow_conj_mem (h₁ : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K) (h₂ : ∀ k ∈ K, τ⁻¹ * k * τ ∈ K)
    (n : ℤ) : ∀ k ∈ K, τ ^ n * k * τ ^ (-n) ∈ K := by
  induction n using Int.induction_on with
  | zero =>
    intro k hk
    simpa using hk
  | succ i ih =>
    intro k hk
    have h := h₁ _ (ih k hk)
    have e : τ ^ ((i : ℤ) + 1) * k * τ ^ (-((i : ℤ) + 1)) =
        τ * (τ ^ (i : ℤ) * k * τ ^ (-(i : ℤ))) * τ⁻¹ := by group
    rw [e]
    exact h
  | pred i ih =>
    intro k hk
    have h := h₂ _ (ih k hk)
    have e : τ ^ (-(i : ℤ) - 1) * k * τ ^ (-(-(i : ℤ) - 1)) =
        τ⁻¹ * (τ ^ (-(i : ℤ)) * k * τ ^ (-(-(i : ℤ)))) * τ := by group
    rw [e]
    exact h

theorem exists_zpow_mul_of_mem_closure (h₁ : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K)
    (h₂ : ∀ k ∈ K, τ⁻¹ * k * τ ∈ K) {g : G}
    (hg : g ∈ Subgroup.closure (insert τ (K : Set G))) :
    ∃ n : ℤ, ∃ k ∈ K, g = τ ^ n * k := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, 1, K.one_mem, by simp⟩
    · exact ⟨0, x, hx, by simp⟩
  | one => exact ⟨0, 1, K.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, k, hk, rfl⟩ := hx
    obtain ⟨m, k', hk', rfl⟩ := hy
    refine ⟨n + m, τ ^ (-m) * k * τ ^ (-(-m)) * k',
      K.mul_mem (zpow_conj_mem h₁ h₂ (-m) k hk) hk', ?_⟩
    group
  | inv x _ hx =>
    obtain ⟨n, k, hk, rfl⟩ := hx
    refine ⟨-n, τ ^ n * k⁻¹ * τ ^ (-n), zpow_conj_mem h₁ h₂ n _ (K.inv_mem hk), ?_⟩
    group

theorem commutator_le_of_normalizes (h₁ : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K)
    (h₂ : ∀ k ∈ K, τ⁻¹ * k * τ ∈ K) {S : Subgroup G}
    (hS : S ≤ Subgroup.closure (insert τ (K : Set G))) : ⁅S, S⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨n, k, hk, rfl⟩ := exists_zpow_mul_of_mem_closure h₁ h₂ (hS hg)
  obtain ⟨m, k', hk', rfl⟩ := exists_zpow_mul_of_mem_closure h₁ h₂ (hS hh)
  have hC : τ ^ (-m) * k * τ ^ (-(-m)) * k' * k⁻¹ * (τ ^ (-n) * k'⁻¹ * τ ^ (-(-n))) ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem (zpow_conj_mem h₁ h₂ (-m) k hk) hk') (K.inv_mem hk))
      (zpow_conj_mem h₁ h₂ (-n) _ (K.inv_mem hk'))
  have e : ⁅τ ^ n * k, τ ^ m * k'⁆ = τ ^ (n + m) *
      (τ ^ (-m) * k * τ ^ (-(-m)) * k' * k⁻¹ * (τ ^ (-n) * k'⁻¹ * τ ^ (-(-n)))) *
        τ ^ (-(n + m)) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact zpow_conj_mem h₁ h₂ (n + m) _ hC

theorem wordEval_mem {k : ℕ} {S : Subgroup G} {gens : Fin k → G} (h : ∀ i, gens i ∈ S)
    (w : List (Fin k)) : wordEval gens w ∈ S := by
  induction w with
  | nil => exact S.one_mem
  | cons i w ih => exact S.mul_mem (h i) ih

end Group

section Two

@[expose] def matA : Matrix Ix Ix (ZMod 2) :=
  fromBlocks !![0, 0; 0, 0] !![0, 1; 1, 1] !![1, 1; 1, 0] !![0, 0; 0, 0]

@[expose] def matB : Matrix Ix Ix (ZMod 2) :=
  fromBlocks !![0, 0; 0, 1] !![1, 0; 1, 0] !![1, 1; 0, 0] !![0, 1; 1, 1]

@[expose] def matXa : Matrix Ix Ix (ZMod 2) :=
  fromBlocks !![0, 0; 0, 0] !![0, 1; 1, 0] !![0, 1; 1, 0] !![0, 0; 0, 0]

@[expose] def matYa : Matrix Ix Ix (ZMod 2) :=
  fromBlocks !![0, 1; 0, 0] !![1, 0; 1, 0] !![0, 0; 1, 0] !![0, 1; 0, 1]

@[expose] def matXb : Matrix Ix Ix (ZMod 2) :=
  fromBlocks !![0, 0; 0, 0] !![0, 1; 1, 0] !![0, 1; 1, 0] !![0, 0; 1, 0]

@[expose] def matYb : Matrix Ix Ix (ZMod 2) :=
  fromBlocks !![0, 0; 1, 0] !![0, 1; 1, 1] !![1, 1; 0, 0] !![0, 0; 1, 1]

theorem matA_mem : matAᵀ * spJ (ZMod 2) * matA = spJ (ZMod 2) := by decide +kernel

theorem matB_mem : matBᵀ * spJ (ZMod 2) * matB = spJ (ZMod 2) := by decide +kernel

theorem matXa_mem : matXaᵀ * spJ (ZMod 2) * matXa = spJ (ZMod 2) := by decide +kernel

theorem matYa_mem : matYaᵀ * spJ (ZMod 2) * matYa = spJ (ZMod 2) := by decide +kernel

theorem matXb_mem : matXbᵀ * spJ (ZMod 2) * matXb = spJ (ZMod 2) := by decide +kernel

theorem matYb_mem : matYbᵀ * spJ (ZMod 2) * matYb = spJ (ZMod 2) := by decide +kernel

@[expose] def gA : GL Ix (ZMod 2) := spUnit matA matA_mem

@[expose] def gB : GL Ix (ZMod 2) := spUnit matB matB_mem

@[expose] def gT : GL Ix (ZMod 2) := spX (1 : ZMod 2) 0 0

theorem gA_eq : gA = ⁅spUnit matXa matXa_mem, spUnit matYa matYa_mem⁆ := by decide +kernel

theorem gB_eq : gB = ⁅spUnit matXb matXb_mem, spUnit matYb matYb_mem⁆ := by decide +kernel

theorem gA_mem : gA ∈ ⁅sp4 (ZMod 2), sp4 (ZMod 2)⁆ := by
  rw [gA_eq]
  exact Subgroup.commutator_mem_commutator matXa_mem matYa_mem

theorem gB_mem : gB ∈ ⁅sp4 (ZMod 2), sp4 (ZMod 2)⁆ := by
  rw [gB_eq]
  exact Subgroup.commutator_mem_commutator matXb_mem matYb_mem

@[expose] def subAB : Subgroup (GL Ix (ZMod 2)) := Subgroup.closure {gA, gB}

theorem gT_conj_gA : gT * gA * gT⁻¹ = wordEval ![gA, gB] [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1] :=
  by decide +kernel

theorem gT_conj_gB : gT * gB * gT⁻¹ = wordEval ![gA, gB] [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0] :=
  by decide +kernel

theorem gT_inv : gT⁻¹ = gT := by decide +kernel

theorem gens_mem_subAB : ∀ i, (![gA, gB] : Fin 2 → GL Ix (ZMod 2)) i ∈ subAB := by
  intro i
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem gT_conj_mem : ∀ k ∈ subAB, gT * k * gT⁻¹ ∈ subAB := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · rw [gT_conj_gA]
      exact wordEval_mem gens_mem_subAB _
    · rw [gT_conj_gB]
      exact wordEval_mem gens_mem_subAB _
  | one => simp
  | mul x y _ _ hx hy =>
    have e : gT * (x * y) * gT⁻¹ = (gT * x * gT⁻¹) * (gT * y * gT⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : gT * x⁻¹ * gT⁻¹ = (gT * x * gT⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem gT_conj_mem' : ∀ k ∈ subAB, gT⁻¹ * k * gT ∈ subAB := by
  intro k hk
  have h := gT_conj_mem k hk
  rw [gT_inv] at h ⊢
  exact h

theorem spX_zero (F : Type) [Field F] [CharP F 2] : spX (0 : F) 0 0 = 1 :=
  sp4_ext fun x y z w => by
    rw [spX_smul]
    simp

theorem spY_zero (F : Type) [Field F] [CharP F 2] : spY (0 : F) 0 0 = 1 :=
  sp4_ext fun x y z w => by
    rw [spY_smul]
    simp

theorem spZ_zero (F : Type) [Field F] [CharP F 2] : spZ (0 : F) = 1 :=
  sp4_ext fun x y z w => by
    rw [spZ_smul]
    simp

theorem spZ'_zero (F : Type) [Field F] [CharP F 2] : spZ' (0 : F) = 1 :=
  sp4_ext fun x y z w => by
    rw [spZ'_smul]
    simp

theorem rootGens_two_subset :
    rootGens (ZMod 2) ⊆ Subgroup.closure (insert gT (subAB : Set (GL Ix (ZMod 2)))) := by
  set C := Subgroup.closure (insert gT (subAB : Set (GL Ix (ZMod 2))))
  have hg : ∀ i, (![gT, gA, gB] : Fin 3 → GL Ix (ZMod 2)) i ∈ C := by
    intro i
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (gens_mem_subAB 0))
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (gens_mem_subAB 1))
  have hw : ∀ w, wordEval ![gT, gA, gB] w ∈ C := wordEval_mem hg
  have hcase : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  have hX1 : ∀ t : ZMod 2, (spX t 0 0 : GL Ix (ZMod 2)) ∈ C := fun t => by
    rcases hcase t with rfl | rfl
    · rw [spX_zero]
      exact C.one_mem
    · have e : (spX (1 : ZMod 2) 0 0 : GL Ix (ZMod 2)) = wordEval ![gT, gA, gB] [0] := by
        decide +kernel
      rw [e]
      exact hw _
  have hX2 : ∀ t : ZMod 2, (spX 0 t 0 : GL Ix (ZMod 2)) ∈ C := fun t => by
    rcases hcase t with rfl | rfl
    · rw [spX_zero]
      exact C.one_mem
    · have e : (spX (0 : ZMod 2) 1 0 : GL Ix (ZMod 2)) =
          wordEval ![gT, gA, gB] [2, 1, 2, 1, 0, 2, 2, 1] := by decide +kernel
      rw [e]
      exact hw _
  have hX3 : ∀ t : ZMod 2, (spX 0 0 t : GL Ix (ZMod 2)) ∈ C := fun t => by
    rcases hcase t with rfl | rfl
    · rw [spX_zero]
      exact C.one_mem
    · have e : (spX (0 : ZMod 2) 0 1 : GL Ix (ZMod 2)) =
          wordEval ![gT, gA, gB] [0, 2, 2, 1, 2, 2] := by decide +kernel
      rw [e]
      exact hw _
  have hY1 : ∀ t : ZMod 2, (spY t 0 0 : GL Ix (ZMod 2)) ∈ C := fun t => by
    rcases hcase t with rfl | rfl
    · rw [spY_zero]
      exact C.one_mem
    · have e : (spY (1 : ZMod 2) 0 0 : GL Ix (ZMod 2)) =
          wordEval ![gT, gA, gB] [2, 0, 2, 2, 2] := by decide +kernel
      rw [e]
      exact hw _
  have hY2 : ∀ t : ZMod 2, (spY 0 t 0 : GL Ix (ZMod 2)) ∈ C := fun t => by
    rcases hcase t with rfl | rfl
    · rw [spY_zero]
      exact C.one_mem
    · have e : (spY (0 : ZMod 2) 1 0 : GL Ix (ZMod 2)) =
          wordEval ![gT, gA, gB] [0, 1, 2, 0, 1, 0, 1, 2] := by decide +kernel
      rw [e]
      exact hw _
  have hY3 : ∀ t : ZMod 2, (spY 0 0 t : GL Ix (ZMod 2)) ∈ C := fun t => by
    rcases hcase t with rfl | rfl
    · rw [spY_zero]
      exact C.one_mem
    · have e : (spY (0 : ZMod 2) 0 1 : GL Ix (ZMod 2)) =
          wordEval ![gT, gA, gB] [2, 2, 2, 1, 0, 1, 2] := by decide +kernel
      rw [e]
      exact hw _
  rintro g (⟨a, b, d, rfl⟩ | ⟨a, b, d, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩)
  · have e : spX a b d = spX a 0 0 * spX 0 b 0 * spX (0 : ZMod 2) 0 d := by
      rw [spX_mul, spX_mul]
      congr 1 <;> ring
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul]
    exact C.mul_mem (C.mul_mem (hX1 a) (hX2 b)) (hX3 d)
  · have e : spY a b d = spY a 0 0 * spY 0 b 0 * spY (0 : ZMod 2) 0 d := by
      rw [spY_mul, spY_mul]
      congr 1 <;> ring
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul]
    exact C.mul_mem (C.mul_mem (hY1 a) (hY2 b)) (hY3 d)
  · rcases hcase t with rfl | rfl
    · rw [spZ_zero]
      exact C.one_mem
    · have e : (spZ (1 : ZMod 2) : GL Ix (ZMod 2)) =
          wordEval ![gT, gA, gB] [2, 0, 2, 1, 2, 1, 2, 2] := by decide +kernel
      rw [e]
      exact hw _
  · rcases hcase t with rfl | rfl
    · rw [spZ'_zero]
      exact C.one_mem
    · have e : (spZ' (1 : ZMod 2) : GL Ix (ZMod 2)) =
          wordEval ![gT, gA, gB] [0, 2, 2, 1, 2, 1, 2] := by decide +kernel
      rw [e]
      exact hw _

theorem sp4Two_commutator_eq : ⁅sp4 (ZMod 2), sp4 (ZMod 2)⁆ = subAB := by
  refine le_antisymm (commutator_le_of_normalizes gT_conj_mem gT_conj_mem' ?_) ?_
  · rw [sp4_eq_closure, Subgroup.closure_le]
    exact rootGens_two_subset
  · rw [subAB, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact gA_mem
    · exact gB_mem

end Two

section Fox

theorem subAB_le : subAB ≤ sp4 (ZMod 2) := by
  rw [subAB, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact matA_mem
  · exact matB_mem

@[expose] def muAB : ↥subAB →* AddMonoid.End (Ix → ZMod 2) :=
  muSp.comp (Subgroup.inclusion subAB_le)

theorem muAB_apply (g : ↥subAB) (v : Ix → ZMod 2) : muAB g v = (g : GL Ix (ZMod 2)) • v := rfl

@[expose] def gensAB : Fin 2 → ↥subAB := ![⟨gA, gens_mem_subAB 0⟩, ⟨gB, gens_mem_subAB 1⟩]

theorem closure_gensAB : Subgroup.closure (Set.range gensAB) = ⊤ := by
  have e : Set.range gensAB = ((↑) : ↥subAB → GL Ix (ZMod 2)) ⁻¹' {gA, gB} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
    · rintro (h | h)
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext (Set.mem_singleton_iff.mp h).symm⟩
  rw [e]
  exact Subgroup.closure_closure_coe_preimage

@[expose] def relsAB : List (List (Fin 2)) :=
  [[0, 0], [1, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]]

theorem relsAB_spec : ∀ r ∈ relsAB, wordEval ![gA, gB] r = 1 := by decide +kernel

theorem wordEval_gensAB (w : List (Fin 2)) :
    ((wordEval gensAB w : ↥subAB) : GL Ix (ZMod 2)) = wordEval ![gA, gB] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change ((gensAB i : ↥subAB) : GL Ix (ZMod 2)) * ((wordEval gensAB w : ↥subAB) :
      GL Ix (ZMod 2)) = _
    rw [ih]
    fin_cases i <;> rfl

@[expose] def foxIx {k : ℕ} (mats : Fin k → Matrix Ix Ix (ZMod 2)) (vals : Fin k → Ix → ZMod 2) :
    List (Fin k) → Ix → ZMod 2
  | [] => 0
  | i :: w => vals i + mats i *ᵥ foxIx mats vals w

theorem foxEval_AB (vals : Fin 2 → Ix → ZMod 2) (w : List (Fin 2)) :
    foxEval muAB gensAB vals w = foxIx ![matA, matB] vals w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change vals i + muAB (gensAB i) (foxEval muAB gensAB vals w) =
      vals i + ![matA, matB] i *ᵥ foxIx ![matA, matB] vals w
    rw [ih]
    fin_cases i <;> rfl

theorem sol_AB : ∀ a b c d a' b' c' d' : ZMod 2,
    (∀ r ∈ relsAB, foxIx ![matA, matB] ![vec4 a b c d, vec4 a' b' c' d'] r = 0) →
    (∃ x y z w : ZMod 2, vec4 a b c d = matA *ᵥ vec4 x y z w - vec4 x y z w ∧
        vec4 a' b' c' d' = matB *ᵥ vec4 x y z w - vec4 x y z w) ∨
    (∃ x y z w : ZMod 2, vec4 a b c d = matA *ᵥ vec4 x y z w - vec4 x y z w ∧
        vec4 a' b' c' d' = vec4 0 0 1 0 + (matB *ᵥ vec4 x y z w - vec4 x y z w)) := by
  decide +kernel

theorem not_cob_AB : ¬∃ x y z w : ZMod 2, (0 : Ix → ZMod 2) = matA *ᵥ vec4 x y z w - vec4 x y z w ∧
    vec4 (0 : ZMod 2) 0 1 0 = matB *ᵥ vec4 x y z w - vec4 x y z w := by
  decide +kernel

theorem Z1A_comp {H G M : Type*} [Group H] [Group G] [AddCommGroup M]
    {μ : G →* AddMonoid.End M} (ι : H →* G) {f : G → M} (hf : f ∈ Z1A μ) :
    f ∘ ι ∈ Z1A (μ.comp ι) := fun g h => by
  simp only [Function.comp_apply, map_mul, MonoidHom.comp_apply]
  exact hf _ _

@[expose] def cocAB : ↥subAB → Ix → ZMod 2 := spF0 ∘ Subgroup.inclusion subAB_le

theorem cocAB_mem : cocAB ∈ Z1A muAB := Z1A_comp _ spF0_mem

theorem sqrtF_zmod (x : ZMod 2) : sqrtF x = x := by
  apply sq_inj
  rw [sqrtF_sq]
  revert x
  decide

theorem cocAB_gen0 : cocAB (gensAB 0) = 0 := by
  funext i
  change sqrtF (quadQ (matA i)) = 0
  rw [sqrtF_zmod]
  revert i
  decide

theorem cocAB_gen1 : cocAB (gensAB 1) = vec4 0 0 1 0 := by
  funext i
  change sqrtF (quadQ (matB i)) = vec4 0 0 1 0 i
  rw [sqrtF_zmod]
  revert i
  decide

theorem eq_of_agree_AB {f f' : ↥subAB → (Ix → ZMod 2)} (hf : f ∈ Z1A muAB) (hf' : f' ∈ Z1A muAB)
    (h0 : f (gensAB 0) = f' (gensAB 0)) (h1 : f (gensAB 1) = f' (gensAB 1)) : f = f' := by
  have h := eq_zero_of_vanish_closure (sub_mem hf hf') closure_gensAB (by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact sub_eq_zero.mpr h0
    · exact sub_eq_zero.mpr h1)
  exact sub_eq_zero.mp h

theorem cocAB_not_mem : cocAB ∉ B1A muAB := by
  rintro ⟨v, hv⟩
  apply not_cob_AB
  refine ⟨v (.inl 0), v (.inl 1), v (.inr 0), v (.inr 1), ?_, ?_⟩
  · rw [← vec4_eta v, ← cocAB_gen0, ← hv]
    rfl
  · rw [← vec4_eta v, ← cocAB_gen1, ← hv]
    rfl

theorem card_Z1A_AB : Nat.card (Z1A muAB) = 2 * Nat.card (B1A muAB) := by
  let Φ : ZMod 2 × B1A muAB → Z1A muAB := fun p =>
    ⟨p.1.val • cocAB + p.2.1, add_mem (AddSubgroup.nsmul_mem _ cocAB_mem _) (B1A_le_Z1A _ p.2.2)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨c, b⟩ ⟨c', b'⟩ h
      have h' : c.val • cocAB + b.1 = c'.val • cocAB + b'.1 := by
        simpa [Φ] using congrArg Subtype.val h
      have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      have key : c = c' := by
        rcases hc c with rfl | rfl <;> rcases hc c' with rfl | rfl
        · rfl
        · exfalso
          apply cocAB_not_mem
          have : cocAB = b.1 - b'.1 := by
            simp only [ZMod.val_zero, zero_smul, zero_add, ZMod.val_one, one_smul] at h'
            rw [h']
            abel
          rw [this]
          exact sub_mem b.2 b'.2
        · exfalso
          apply cocAB_not_mem
          have : cocAB = b'.1 - b.1 := by
            simp only [ZMod.val_zero, zero_smul, zero_add, ZMod.val_one, one_smul] at h'
            rw [← h']
            abel
          rw [this]
          exact sub_mem b'.2 b.2
        · rfl
      subst key
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h'))
    · rintro ⟨f, hf⟩
      have hrel : ∀ r ∈ relsAB, foxIx ![matA, matB] ![f (gensAB 0), f (gensAB 1)] r = 0 := by
        intro r hr
        have h := (foxEval_AB (fun i => f (gensAB i)) r).symm.trans
          (Z1A_wordEval hf gensAB r).symm
        have h1 : wordEval gensAB r = 1 :=
          Subtype.ext ((wordEval_gensAB r).trans (relsAB_spec r hr))
        rw [h1, Z1A_one hf] at h
        have hv : (![f (gensAB 0), f (gensAB 1)] : Fin 2 → Ix → ZMod 2) =
            fun i => f (gensAB i) := by
          funext i
          fin_cases i <;> rfl
        rw [hv]
        exact h
      rw [vec4_eta (f (gensAB 0)), vec4_eta (f (gensAB 1))] at hrel
      rcases sol_AB _ _ _ _ _ _ _ _ hrel with ⟨x, y, z, w, hv₀, hv₁⟩ | ⟨x, y, z, w, hv₀, hv₁⟩
      · refine ⟨(0, ⟨coboundaryA muAB (vec4 x y z w), ⟨_, rfl⟩⟩), Subtype.ext ?_⟩
        simp only [Φ, ZMod.val_zero, zero_smul, zero_add]
        refine (eq_of_agree_AB hf (B1A_le_Z1A _ ⟨_, rfl⟩) ?_ ?_).symm
        · rw [vec4_eta (f (gensAB 0)), hv₀]
          rfl
        · rw [vec4_eta (f (gensAB 1)), hv₁]
          rfl
      · refine ⟨(1, ⟨coboundaryA muAB (vec4 x y z w), ⟨_, rfl⟩⟩), Subtype.ext ?_⟩
        simp only [Φ, ZMod.val_one, one_smul]
        refine (eq_of_agree_AB hf (add_mem cocAB_mem (B1A_le_Z1A _ ⟨_, rfl⟩)) ?_ ?_).symm
        · rw [vec4_eta (f (gensAB 0)), hv₀, Pi.add_apply, cocAB_gen0]
          exact (zero_add _).symm
        · rw [vec4_eta (f (gensAB 1)), hv₁, Pi.add_apply, cocAB_gen1]
          rfl
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_zmod]

end Fox

end CFSG.Quasithin.JonesParshall
