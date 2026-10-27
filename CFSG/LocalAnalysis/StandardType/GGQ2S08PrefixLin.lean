module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08PermLin

public section

namespace CFSG.StandardType.TestLin

open Matrix

variable {m : ℕ}

@[expose] def prefEquiv (m : ℕ) : Fin m ≃ {i : Fin (m + 1) // i ≠ Fin.last m} where
  toFun i := ⟨i.castSucc, by simp⟩
  invFun i := ⟨i.1.val, by
    have h1 : i.1.val < m + 1 := i.1.isLt
    have h2 : i.1.val ≠ m := by
      intro h
      exact i.2 (Fin.ext h)
    omega
  ⟩
  left_inv i := by
    apply Fin.ext
    rfl
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    rfl

@[expose] noncomputable def permLastFun (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.ofSubtype (p := fun i : Fin (m + 1) => i ≠ Fin.last m)
    ((prefEquiv m).symm.trans (τ.trans (prefEquiv m)))

theorem permLastFun_castSucc (τ : Equiv.Perm (Fin m)) (i : Fin m) :
    permLastFun τ i.castSucc = (τ i).castSucc := by
  rw [permLastFun, Equiv.Perm.ofSubtype_apply_of_mem]
  · rfl
  · simp

theorem permLastFun_last (τ : Equiv.Perm (Fin m)) :
    permLastFun τ (Fin.last m) = Fin.last m := by
  rw [permLastFun, Equiv.Perm.ofSubtype_apply_of_not_mem]
  simp

theorem permLastFun_one : permLastFun (1 : Equiv.Perm (Fin m)) = 1 := by
  ext k
  by_cases hk : k = Fin.last m
  · subst hk
    rw [permLastFun_last]
    rfl
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
    simp [permLastFun_castSucc]

theorem permLastFun_mul (τ ρ : Equiv.Perm (Fin m)) :
    permLastFun (τ * ρ) = permLastFun τ * permLastFun ρ := by
  ext k
  by_cases hk : k = Fin.last m
  · subst hk
    simp [permLastFun_last]
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
    simp [permLastFun_castSucc]

@[expose] noncomputable def permLast (m : ℕ) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin (m + 1)) where
  toFun := permLastFun
  map_one' := permLastFun_one
  map_mul' := permLastFun_mul

theorem permLast_castSucc (τ : Equiv.Perm (Fin m)) (i : Fin m) :
    permLast m τ i.castSucc = (τ i).castSucc :=
  permLastFun_castSucc τ i

theorem permLast_last (τ : Equiv.Perm (Fin m)) :
    permLast m τ (Fin.last m) = Fin.last m :=
  permLastFun_last τ

theorem TestHyp.exists_sorted_init {m : ℕ}
    {W A M : Subgroup (Vn (m + 1) ≃ₗ[ZMod 3] Vn (m + 1))}
    (hW : ∀ σ : Equiv.Perm (Fin (m + 1)), σ (Fin.last m) = Fin.last m → permN σ ∈ W)
    (hT : TestHyp W (Pi.single (Fin.last m) 1) A M)
    {u : Vn (m + 1) ≃ₗ[ZMod 3] Vn (m + 1)}
    (hu : u ∈ A) (huR : IsRefl u) :
    ∃ (σ : Equiv.Perm (Fin (m + 1))) (c a : Vn (m + 1)) (f : ZMod 3 → ZMod 3)
      (h : a ⬝ᵥ c = 2),
      σ (Fin.last m) = Fin.last m ∧ Monotone (fun i : Fin m => (c i.castSucc).val) ∧
      (∀ i : Fin m, a i.castSucc = f (c i.castSucc)) ∧
      (∀ i j : Fin m, f (c i.castSucc) = f (c j.castSucc) ↔ c i.castSucc = c j.castSucc) ∧
      permN σ * u * (permN σ)⁻¹ = refl c a h := by
  classical
  obtain ⟨c0, a0, h0, hu_eq⟩ := eq_refl_of_isRefl huR
  have hsym0 : ∀ i j : Fin m,
      a0 i.castSucc = a0 j.castSucc ↔ c0 i.castSucc = c0 j.castSucc := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · have hne : i.castSucc ≠ j.castSucc := fun h =>
        hij (Fin.ext (by simpa using congrArg Fin.val h))
      have hswap_last : Equiv.swap i.castSucc j.castSucc (Fin.last m) = Fin.last m := by
        rw [Equiv.swap_apply_of_ne_of_ne]
        · exact (Fin.castSucc_ne_last i).symm
        · exact (Fin.castSucc_ne_last j).symm
      have hswapW : permN (Equiv.swap i.castSucc j.castSucc) ∈ W := hW _ hswap_last
      have hswapM : permN (Equiv.swap i.castSucc j.castSucc) ∈ M := hT.W_le hswapW
      have hswapA : permN (Equiv.swap i.castSucc j.castSucc) ∈ A := hT.le hswapM
      have hswap_eq := permN_swap i.castSucc j.castSucc hne
      have hconjA : refl (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
          (Pi.single i.castSucc 1 - Pi.single j.castSucc 1)
          (dot_sub_single_self i.castSucc j.castSucc hne) ∈ A := by
        rwa [← hswap_eq]
      have hsym := sym_of_noTransv hT.noTransv h0
        (dot_sub_single_self i.castSucc j.castSucc hne)
        (by rw [← hu_eq]; exact hu) hconjA
      rw [dot_sub_single, sub_single_dot, sub_eq_zero, sub_eq_zero] at hsym
      exact hsym
  let c' : Vn m := fun i => c0 i.castSucc
  let a' : Vn m := fun i => a0 i.castSucc
  have hsym' : ∀ i j : Fin m, a' i = a' j ↔ c' i = c' j := hsym0
  obtain ⟨f, hf⟩ := exists_fun_of_sym hsym'
  obtain ⟨τ, hmono⟩ := exists_perm_monotone c'
  let σ : Equiv.Perm (Fin (m + 1)) := (permLast m τ)⁻¹
  have hσsymm : σ.symm = permLast m τ := by
    change ((permLast m τ)⁻¹)⁻¹ = permLast m τ
    rw [inv_inv]
  let c : Vn (m + 1) := c0 ∘ σ.symm
  let a : Vn (m + 1) := a0 ∘ σ.symm
  have hc_cast : ∀ i : Fin m, c i.castSucc = c' (τ i) := by
    intro i
    change c0 (σ.symm i.castSucc) = c' (τ i)
    rw [hσsymm, permLast_castSucc]
  have ha_cast : ∀ i : Fin m, a i.castSucc = a' (τ i) := by
    intro i
    change a0 (σ.symm i.castSucc) = a' (τ i)
    rw [hσsymm, permLast_castSucc]
  have hσlast : σ (Fin.last m) = Fin.last m := by
    have h : σ.symm (Fin.last m) = Fin.last m := by rw [hσsymm, permLast_last]
    calc σ (Fin.last m) = σ (σ.symm (Fin.last m)) := by rw [h]
      _ = Fin.last m := Equiv.apply_symm_apply σ _
  have hmono' : Monotone (fun i : Fin m => (c i.castSucc).val) := by
    simpa [hc_cast] using hmono
  have haf : ∀ i : Fin m, a i.castSucc = f (c i.castSucc) := by
    intro i
    rw [ha_cast i, hc_cast i]
    exact congrFun hf (τ i)
  have hinj : ∀ i j : Fin m,
      f (c i.castSucc) = f (c j.castSucc) ↔ c i.castSucc = c j.castSucc := by
    intro i j
    rw [hc_cast i, hc_cast j]
    have hfi := congrFun hf (τ i)
    have hfj := congrFun hf (τ j)
    simp only [Function.comp_apply] at hfi hfj
    rw [← hfi, ← hfj]
    exact hsym0 (τ i) (τ j)
  have hnew : a ⬝ᵥ c = 2 := by
    change (a0 ∘ σ.symm) ⬝ᵥ (c0 ∘ σ.symm) = 2
    rw [show (a0 ∘ σ.symm) ⬝ᵥ (c0 ∘ σ.symm) = a0 ⬝ᵥ c0 from by
      simpa [Function.comp_def] using
        dotProduct_comp_equiv_symm (e := σ) (u := a0 ∘ σ.symm) (x := c0)]
    exact h0
  refine ⟨σ, c, a, f, hnew, hσlast, hmono', haf, hinj, ?_⟩
  calc permN σ * u * (permN σ)⁻¹
      = permN σ * refl c0 a0 h0 * (permN σ)⁻¹ := by rw [hu_eq]
    _ = refl (c0 ∘ σ.symm) (a0 ∘ σ.symm) _ := permN_conj_refl σ c0 a0 h0
    _ = refl c a hnew := by
        exact refl_proof_irrel _ _ _ _

theorem permLastFun_swap {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    permLastFun (Equiv.swap i j) = Equiv.swap i.castSucc j.castSucc := by
  ext k
  by_cases hk : k = Fin.last m
  · subst hk
    rw [permLastFun_last, Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.castSucc_ne_last i).symm
    · exact (Fin.castSucc_ne_last j).symm
  · obtain ⟨l, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
    rw [permLastFun_castSucc]
    by_cases hli : l = i
    · subst hli
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hlj : l = j
      · subst hlj
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj,
          Equiv.swap_apply_of_ne_of_ne
            (fun h => hli (Fin.castSucc_injective m h))
            (fun h => hlj (Fin.castSucc_injective m h))]

theorem permN_prefix_mem_closure {n ℓ : ℕ} (hℓ : n ≤ ℓ)
    {S : Fin ℓ → Vn (n + 2) ≃ₗ[ZMod 3] Vn (n + 2)}
    (hS : ∀ i : Fin n,
      S (Fin.castLE hℓ i) = permN (Equiv.swap i.castSucc.castSucc i.succ.castSucc)) :
    ∀ σ : Equiv.Perm (Fin (n + 2)), σ (Fin.last (n + 1)) = Fin.last (n + 1) →
      permN σ ∈ Subgroup.closure (Set.range S) := by
  classical
  have hgen : ∀ τ : Equiv.Perm (Fin (n + 1)),
      permN (permLast (n + 1) τ) ∈ Subgroup.closure (Set.range S) := by
    intro τ
    have htop : Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) = ⊤ := by
      simpa using Equiv.Perm.mclosure_swap_castSucc_succ n
    have hτ : τ ∈ Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [htop]
      exact Submonoid.mem_top τ
    refine Submonoid.closure_induction ?_ ?_ ?_ hτ
    · rintro ρ ⟨i, rfl⟩
      have hswap : permLastFun (Equiv.swap i.castSucc i.succ) =
          Equiv.swap i.castSucc.castSucc i.succ.castSucc :=
        permLastFun_swap _ _ (Fin.castSucc_lt_succ.ne)
      change permN (permLastFun (Equiv.swap i.castSucc i.succ)) ∈
        Subgroup.closure (Set.range S)
      rw [hswap, ← hS i]
      exact Subgroup.subset_closure ⟨Fin.castLE hℓ i, rfl⟩
    · change permN (permLastFun (1 : Equiv.Perm (Fin (n + 1)))) ∈
        Subgroup.closure (Set.range S)
      rw [permLastFun_one]
      change (permHom (n + 2)) 1 ∈ Subgroup.closure (Set.range S)
      rw [map_one]
      exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      change permN (permLastFun (a * b)) ∈ Subgroup.closure (Set.range S)
      rw [permLastFun_mul, permN_mul]
      exact Subgroup.mul_mem _ ha hb
  intro σ hσ
  let p : Fin (n + 2) → Prop := fun i => i ≠ Fin.last (n + 1)
  have hp : ∀ i, p (σ i) ↔ p i := by
    intro i
    constructor
    · intro h hi
      have hlast : σ i = Fin.last (n + 1) := by rw [hi, hσ]
      exact h hlast
    · intro h hsi
      have h3 : σ.symm (Fin.last (n + 1)) = Fin.last (n + 1) := by
        have h := congrArg σ.symm hσ
        rw [Equiv.symm_apply_apply] at h
        exact h.symm
      have h1 : i = Fin.last (n + 1) := by
        have h2 : σ.symm (σ i) = σ.symm (Fin.last (n + 1)) := by rw [hsi]
        rwa [Equiv.symm_apply_apply, h3] at h2
      exact h h1
  let τ : Equiv.Perm (Fin (n + 1)) :=
    (prefEquiv (n + 1)).trans
      ((σ.subtypePerm hp).trans (prefEquiv (n + 1)).symm)
  have hτσ : permLast (n + 1) τ = σ := by
    ext k
    by_cases hk : k = Fin.last (n + 1)
    · subst hk
      rw [permLast_last, hσ]
    · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hk
      rw [permLast_castSucc]
      rfl
  rw [← hτσ]
  exact hgen τ

end CFSG.StandardType.TestLin

end
