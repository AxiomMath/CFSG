module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08TestLin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {n : ℕ}

@[expose] def permN (σ : Equiv.Perm (Fin n)) : Vn n ≃ₗ[ZMod 3] Vn n :=
  LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) σ.symm

@[expose] def oneN (n : ℕ) : Vn n := fun _ => 1

theorem permN_apply (σ : Equiv.Perm (Fin n)) (v : Vn n) (i : Fin n) :
    permN σ v i = v (σ.symm i) := by
  rfl


theorem permN_single (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permN σ (Pi.single i 1) = Pi.single (σ i) 1 := by
  funext j
  rw [permN_apply]
  simp only [Pi.single_apply, Equiv.symm_apply_eq]


@[expose] noncomputable def permHom (n : ℕ) :
    Equiv.Perm (Fin n) →* (Vn n ≃ₗ[ZMod 3] Vn n) where
  toFun := permN
  map_one' := by
    apply LinearEquiv.ext
    intro v
    funext i
    rw [permN]
    rfl
  map_mul' := by
    intro σ τ
    apply LinearEquiv.ext
    intro v
    funext i
    change permN (σ * τ) v i = (permN σ) ((permN τ) v) i
    rw [permN_apply, permN_apply, permN_apply]
    have h : (σ * τ).symm i = τ.symm (σ.symm i) := by
      rw [Equiv.symm_apply_eq]
      simp [Equiv.Perm.mul_apply]
    rw [h]

@[expose] noncomputable def permGroup (n : ℕ) : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n) :=
  (permHom n).range

theorem permN_mul (σ τ : Equiv.Perm (Fin n)) :
    permN (σ * τ) = permN σ * permN τ := by
  apply LinearEquiv.ext
  intro v
  funext i
  rw [LinearEquiv.mul_apply, permN_apply, permN_apply, permN_apply]
  have h : (σ * τ).symm i = τ.symm (σ.symm i) := by
    rw [Equiv.symm_apply_eq]
    simp [Equiv.Perm.mul_apply]
  rw [h]

theorem permN_inv (σ : Equiv.Perm (Fin n)) : (permN σ)⁻¹ = permN σ⁻¹ := by
  change (permN σ).symm = permN σ⁻¹
  rw [permN, permN, LinearEquiv.funCongrLeft_symm]
  rfl

theorem permN_oneN (σ : Equiv.Perm (Fin n)) : permN σ (oneN n) = oneN n := by
  funext i
  rw [permN_apply]
  rfl

theorem permN_conj_refl (σ : Equiv.Perm (Fin n)) (c a : Vn n) (h : a ⬝ᵥ c = 2) :
    permN σ * refl c a h * (permN σ)⁻¹ =
      refl (c ∘ σ.symm) (a ∘ σ.symm) (by
        rw [dotProduct_comp_equiv_symm]
        simpa [Function.comp_def] using h) := by
  rw [conj_refl]
  apply LinearEquiv.ext
  intro v
  have h1 : permN σ c = fun i => c (σ.symm i) := by
    funext i
    rw [permN_apply]
  have h2 : dualVec ((permN σ).symm : Vn n →ₗ[ZMod 3] Vn n) a = fun i => a (σ.symm i) := by
    funext i
    rw [dualVec]
    have hs : (permN σ).symm (Pi.single i 1) = Pi.single (σ.symm i) 1 := by
      change (permN σ)⁻¹ (Pi.single i 1) = Pi.single (σ.symm i) 1
      rw [permN_inv, permN_single]
      congr 1
    change a ⬝ᵥ (permN σ).symm (Pi.single i 1) = a (σ.symm i)
    rw [hs]
    simp [dotProduct_single]
  simp only [refl_apply, h1, h2]
  rfl


theorem dot_sub_single_self {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (Pi.single i 1 - Pi.single j 1 : Vn n) ⬝ᵥ (Pi.single i 1 - Pi.single j 1) = 2 := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  rw [single_dotProduct, dotProduct_single, dotProduct_single, dotProduct_single]
  simp [Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij)]
  ring

theorem dot_sub_single {n : ℕ} (a : Vn n) (i j : Fin n) :
    a ⬝ᵥ (Pi.single i 1 - Pi.single j 1) = a i - a j := by
  rw [dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]

theorem sub_single_dot {n : ℕ} (c : Vn n) (i j : Fin n) :
    (Pi.single i 1 - Pi.single j 1) ⬝ᵥ c = c i - c j := by
  rw [sub_dotProduct, single_dotProduct, single_dotProduct, one_mul, one_mul]

theorem permN_swap {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    permN (Equiv.swap i j) =
      refl (Pi.single i 1 - Pi.single j 1) (Pi.single i 1 - Pi.single j 1)
        (dot_sub_single_self i j hij) := by
  apply LinearEquiv.ext
  intro v
  funext k
  rw [refl_apply, permN_apply]
  by_cases hki : k = i
  · subst k
    simp [Pi.single_eq_same, Pi.single_eq_of_ne hij]
  · by_cases hkj : k = j
    · subst k
      simp [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]
    · have hsk : (Equiv.swap i j).symm k = k := by
        rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hkj]
      rw [hsk]
      simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj]

theorem TestHyp.sym_perm {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)} {x : Vn n}
    (hW : permGroup n ≤ W) (hT : TestHyp W x A M) {c a : Vn n} {h : a ⬝ᵥ c = 2}
    (hu : refl c a h ∈ A) (i j : Fin n) : a i = a j ↔ c i = c j := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  · have hswapW : permN (Equiv.swap i j) ∈ W := hW ⟨Equiv.swap i j, rfl⟩
    have hswapM : permN (Equiv.swap i j) ∈ M := hT.W_le hswapW
    have hswapA : permN (Equiv.swap i j) ∈ A := hT.le hswapM
    have hswap_eq : permN (Equiv.swap i j) =
        refl (Pi.single i 1 - Pi.single j 1) (Pi.single i 1 - Pi.single j 1)
          (dot_sub_single_self i j hij) := permN_swap i j hij
    have hconjA : refl (Pi.single i 1 - Pi.single j 1)
        (Pi.single i 1 - Pi.single j 1) (dot_sub_single_self i j hij) ∈ A := by
      rwa [← hswap_eq]
    have hsym := sym_of_noTransv hT.noTransv h
      (dot_sub_single_self i j hij) hu hconjA
    have h1 : a ⬝ᵥ (Pi.single i 1 - Pi.single j 1) = a i - a j := dot_sub_single a i j
    have h2 : (Pi.single i 1 - Pi.single j 1) ⬝ᵥ c = c i - c j := sub_single_dot c i j
    rw [h1, h2] at hsym
    rw [sub_eq_zero, sub_eq_zero] at hsym
    exact hsym


theorem oneN_ne_zero [NeZero n] : (oneN n : Vn n) ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin n)
  simp [oneN] at h0

theorem smul_oneN_cases (t : ZMod 3) :
    t • oneN n = 0 ∨ t • oneN n = oneN n ∨ t • oneN n = -oneN n := by
  fin_cases t
  · left; change (0 : ZMod 3) • oneN n = 0; rw [zero_smul]
  · right; left; change (1 : ZMod 3) • oneN n = oneN n; rw [one_smul]
  · right; right; change (2 : ZMod 3) • oneN n = -oneN n
    rw [show (2 : ZMod 3) = -1 by decide, neg_one_smul]

theorem dot_one_ne [NeZero n] {c a : Vn n} (hac : a ⬝ᵥ c = 2)
    {u : Vn n ≃ₗ[ZMod 3] Vn n} (hu : u = refl c a hac)
    (h : ¬ FixesLine (oneN n) u) : a ⬝ᵥ oneN n ≠ 0 := by
  intro h0
  apply h
  left
  rw [hu, refl_apply, h0, zero_smul, sub_zero]

theorem c_ne_smul_one [NeZero n] {c a : Vn n} (hac : a ⬝ᵥ c = 2)
    {u : Vn n ≃ₗ[ZMod 3] Vn n} (hu : u = refl c a hac)
    (h : ¬ FixesLine (oneN n) u) : ∀ μ : ZMod 3, c ≠ μ • oneN n := by
  intro μ hμ
  have hu0 : u (oneN n) ≠ 0 := by
    intro h0
    have h10 : (oneN n : Vn n) = 0 := by
      have := congrArg (fun x => u⁻¹ x) h0
      simpa using this
    exact oneN_ne_zero h10
  have hval : u (oneN n) = (1 - (a ⬝ᵥ oneN n) * μ) • oneN n := by
    rw [hu, refl_apply, hμ, ← mul_smul]
    conv_rhs => rw [sub_smul, one_smul]
  rcases smul_oneN_cases (1 - (a ⬝ᵥ oneN n) * μ) with h0 | h1 | h1
  · exact hu0 (hval.trans h0)
  · have hnot := h
    rw [FixesLine] at hnot
    push Not at hnot
    exact hnot.1 (hval.trans h1)
  · have hnot := h
    rw [FixesLine] at hnot
    push Not at hnot
    exact hnot.2 (hval.trans h1)

theorem refl_proof_irrel (c a : Vn n) (h h' : a ⬝ᵥ c = 2) :
    refl c a h = refl c a h' := by
  apply LinearEquiv.ext
  intro v
  rfl

theorem exists_fun_of_sym {c a : Vn n} (hs : ∀ i j, a i = a j ↔ c i = c j) :
    ∃ f : ZMod 3 → ZMod 3, a = f ∘ c := by
  classical
  let f : ZMod 3 → ZMod 3 := fun y => if h : ∃ i, c i = y then a (Classical.choose h) else 0
  refine ⟨f, funext fun i => ?_⟩
  have hex : ∃ j, c j = c i := ⟨i, rfl⟩
  have hspec : c (Classical.choose hex) = c i := Classical.choose_spec hex
  have ha : a (Classical.choose hex) = a i := (hs _ _).mpr hspec
  show a i = f (c i)
  simp only [f, dif_pos hex]
  exact ha.symm

theorem exists_perm_monotone (c : Vn n) :
    ∃ σ : Equiv.Perm (Fin n), Monotone (fun i => (c (σ i)).val) :=
  ⟨Tuple.sort (fun i => (c i).val), by
    simpa only [Function.comp_def] using Tuple.monotone_sort (fun i => (c i).val)⟩

theorem TestHyp.exists_sorted [NeZero n] {W A M : Subgroup (Vn n ≃ₗ[ZMod 3] Vn n)}
    (hW : permGroup n ≤ W) (hT : TestHyp W (oneN n) A M) {u : Vn n ≃ₗ[ZMod 3] Vn n} (hu : u ∈ A)
    (huR : IsRefl u) (hux : ¬ FixesLine (oneN n) u) :
    ∃ (σ : Equiv.Perm (Fin n)) (c : Vn n) (f : ZMod 3 → ZMod 3),
      Monotone (fun i => (c i).val) ∧ (∀ i j, f (c i) = f (c j) ↔ c i = c j) ∧
      (f ∘ c) ⬝ᵥ oneN n ≠ 0 ∧ (∀ μ : ZMod 3, c ≠ μ • oneN n) ∧
      ∃ (h : (f ∘ c) ⬝ᵥ c = 2), permN σ * u * (permN σ)⁻¹ = refl c (f ∘ c) h := by
  obtain ⟨c0, a0, h0, hu_eq⟩ := eq_refl_of_isRefl huR
  have hsym0 : ∀ i j, a0 i = a0 j ↔ c0 i = c0 j := by
    intro i j
    exact TestHyp.sym_perm hW hT (by rw [← hu_eq]; exact hu) i j
  obtain ⟨f0, hf0⟩ := exists_fun_of_sym hsym0
  obtain ⟨τ, hmono⟩ := exists_perm_monotone c0
  let σ : Equiv.Perm (Fin n) := τ⁻¹
  let c : Vn n := c0 ∘ τ
  let f : ZMod 3 → ZMod 3 := f0
  have hσ : σ.symm = τ := by
    dsimp [σ]
    exact Equiv.symm_symm τ
  have hc_eq : c0 ∘ σ.symm = c := by
    funext i
    rw [hσ]
  have ha_eq : a0 ∘ σ.symm = f ∘ c := by
    funext i
    rw [Function.comp_apply, hf0]
    rfl
  have hmono' : Monotone (fun i => (c i).val) := by
    simpa [c, Function.comp_def] using hmono
  have hsym : ∀ i j, f (c i) = f (c j) ↔ c i = c j := by
    intro i j
    have h := hsym0 (τ i) (τ j)
    rw [hf0] at h
    simpa [c, f, Function.comp_def] using h
  have hdot : (f ∘ c) ⬝ᵥ oneN n ≠ 0 := by
    have hcomp : f ∘ c = a0 ∘ τ := by
      funext i
      rw [Function.comp_apply, hf0]
      rfl
    rw [hcomp]
    have hdot_eq : (a0 ∘ τ) ⬝ᵥ oneN n = a0 ⬝ᵥ oneN n := by
      simp only [dotProduct, oneN, Function.comp_apply]
      exact Equiv.sum_comp τ (fun i => a0 i * 1)
    have h0ne : a0 ⬝ᵥ oneN n ≠ 0 := dot_one_ne h0 hu_eq hux
    rw [hdot_eq]
    exact h0ne
  have hcne : ∀ μ : ZMod 3, c ≠ μ • oneN n := by
    intro μ hμ
    have hc0 : c0 = μ • oneN n := by
      funext i
      have h := congrFun hμ (τ.symm i)
      simpa [c, Function.comp_def, oneN, Pi.smul_apply] using h
    exact c_ne_smul_one h0 hu_eq hux μ hc0
  have hconj : permN σ * u * (permN σ)⁻¹ =
      refl c (f ∘ c) (by
        rw [← ha_eq, ← hc_eq]
        rw [dotProduct_comp_equiv_symm]
        simpa [Function.comp_def] using h0) := by
    rw [hu_eq]
    rw [permN_conj_refl σ c0 a0 h0]
    congr 2
  refine ⟨σ, c, f, hmono', hsym, hdot, hcne, ?_⟩
  exact ⟨_, hconj⟩


theorem permGroup_le_of_adjacent {m : ℕ} {W : Subgroup (Vn (m + 1) ≃ₗ[ZMod 3] Vn (m + 1))}
    (h : ∀ i : Fin m, permN (Equiv.swap i.castSucc i.succ) ∈ W) : permGroup (m + 1) ≤ W := by
  rintro _ ⟨σ, rfl⟩
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top σ
  induction hσ using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, rfl⟩ := hτ
    exact h i
  | one =>
    rw [map_one]
    exact W.one_mem
  | mul τ ρ _ _ hτ hρ =>
    rw [map_mul]
    exact W.mul_mem hτ hρ


end CFSG.StandardType.TestLin

end
