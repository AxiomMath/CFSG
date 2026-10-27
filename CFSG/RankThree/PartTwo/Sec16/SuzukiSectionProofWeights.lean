module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Matrix Polynomial Module

variable {K : Type} [Field K]

@[expose] noncomputable def endL :
    GL (Fin 3) K →* Module.End (AlgebraicClosure K) (Fin 3 → AlgebraicClosure K) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K) ≃ₐ[AlgebraicClosure K]
      _).toAlgHom.toRingHom.toMonoidHom.comp
    (((algebraMap K (AlgebraicClosure K)).mapMatrix :
        Matrix (Fin 3) (Fin 3) K →+* _).toMonoidHom.comp
      (Units.coeHom (Matrix (Fin 3) (Fin 3) K)))

theorem endL_injective : Function.Injective (endL (K := K)) := by
  intro g h hgh
  apply Units.ext
  have h1 : (g : Matrix (Fin 3) (Fin 3) K).map (algebraMap K (AlgebraicClosure K)) =
      (h : Matrix (Fin 3) (Fin 3) K).map (algebraMap K (AlgebraicClosure K)) :=
    Matrix.toLin'.injective hgh
  ext i j
  exact (algebraMap K (AlgebraicClosure K)).injective (congrFun (congrFun h1 i) j)

@[expose] noncomputable def wsp (M : Subgroup (GL (Fin 3) K)) (χ : M → AlgebraicClosure K) :
    Submodule (AlgebraicClosure K) (Fin 3 → AlgebraicClosure K) :=
  ⨅ m : M, (endL (m : GL (Fin 3) K)).maxGenEigenspace (χ m)

variable {M : Subgroup (GL (Fin 3) K)}

theorem iSup_wsp_eq_top (hM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) : ⨆ χ, wsp M χ = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun m : M => endL (m : GL (Fin 3) K))
    (fun x y _ => by
      change endL (x : GL (Fin 3) K) * endL (y : GL (Fin 3) K) =
        endL (y : GL (Fin 3) K) * endL (x : GL (Fin 3) K)
      rw [← map_mul, ← map_mul, hM x x.2 y y.2])
    (fun m => Module.End.iSup_maxGenEigenspace_eq_top _)

theorem iSupIndep_wsp (hM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) : iSupIndep (wsp M) :=
  Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun m : M => endL (m : GL (Fin 3) K)) fun x y φ =>
      Module.End.mapsTo_maxGenEigenspace_of_comm (by
        change endL (y : GL (Fin 3) K) * endL (x : GL (Fin 3) K) =
          endL (x : GL (Fin 3) K) * endL (y : GL (Fin 3) K)
        rw [← map_mul, ← map_mul, hM y y.2 x x.2]) φ

theorem apply_of_mem_wsp {n : ℕ} (hn : (n : K) ≠ 0) (hMn : ∀ m ∈ M, m ^ n = 1) (m : M)
    {χ : M → AlgebraicClosure K} {v : Fin 3 → AlgebraicClosure K} (hv : v ∈ wsp M χ) :
    endL (m : GL (Fin 3) K) v = χ m • v := by
  have hv' : v ∈ (endL (m : GL (Fin 3) K)).maxGenEigenspace (χ m) :=
    (Submodule.mem_iInf _).mp hv m
  have hnL : (n : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
    exact fun h => hn ((algebraMap K (AlgebraicClosure K)).injective (by rw [h, map_zero]))
  have hsep : (X ^ n - C (1 : AlgebraicClosure K)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 hnL one_ne_zero
  have haeval : aeval (endL (m : GL (Fin 3) K)) (X ^ n - C (1 : AlgebraicClosure K)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, ← map_pow, hMn m m.2, map_one, sub_self]
  have hss := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval
  rw [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at hv'
  exact Module.End.mem_eigenspace_iff.mp hv'

@[expose] def conjInv {g : GL (Fin 3) K} (hg : g ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K)))
    (m : M) : M :=
  ⟨g⁻¹ * m * g, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) m).mp m.2
    simpa using this⟩

theorem coe_conjInv {g : GL (Fin 3) K} (hg : g ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K)))
    (m : M) : (conjInv hg m : GL (Fin 3) K) = g⁻¹ * m * g :=
  rfl

theorem map_mem_wsp {g : GL (Fin 3) K} (hg : g ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K)))
    {χ : M → AlgebraicClosure K} {v : Fin 3 → AlgebraicClosure K} (hv : v ∈ wsp M χ) :
    endL g v ∈ wsp M (χ ∘ conjInv hg) := by
  rw [wsp, Submodule.mem_iInf] at hv ⊢
  intro m
  have hv' := hv (conjInv hg m)
  rw [Module.End.mem_maxGenEigenspace] at hv' ⊢
  obtain ⟨k, hk⟩ := hv'
  refine ⟨k, ?_⟩
  have hcomm : endL (m : GL (Fin 3) K) * endL g = endL g * endL (conjInv hg m : GL (Fin 3) K) := by
    rw [← map_mul, ← map_mul, coe_conjInv]
    congr 1
    group
  have hstep : (endL (m : GL (Fin 3) K) - χ (conjInv hg m) • 1) * endL g =
      endL g * (endL (conjInv hg m : GL (Fin 3) K) - χ (conjInv hg m) • 1) := by
    rw [sub_mul, mul_sub, hcomm, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hpow : ∀ j : ℕ, (endL (m : GL (Fin 3) K) - χ (conjInv hg m) • 1) ^ j * endL g =
      endL g * (endL (conjInv hg m : GL (Fin 3) K) - χ (conjInv hg m) • 1) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, mul_assoc, hstep, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have h1 := congrArg (fun f : Module.End (AlgebraicClosure K) (Fin 3 → AlgebraicClosure K) =>
    f v) (hpow k)
  simp only [Module.End.mul_apply] at h1
  change ((endL (m : GL (Fin 3) K) - χ (conjInv hg m) • 1) ^ k) (endL g v) = 0
  rw [h1, hk, map_zero]

abbrev Wt (M : Subgroup (GL (Fin 3) K)) : Type := {χ : M → AlgebraicClosure K // wsp M χ ≠ ⊥}

theorem wsp_comp_ne_bot {g : GL (Fin 3) K} (hg : g ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K)))
    {χ : M → AlgebraicClosure K} (hχ : wsp M χ ≠ ⊥) : wsp M (χ ∘ conjInv hg) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  intro hbot
  have h1 := map_mem_wsp hg hv
  rw [hbot, Submodule.mem_bot] at h1
  apply hv0
  have hinj : Function.Injective (endL g) := by
    intro x y hxy
    have := congrArg (endL g⁻¹) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      at this
  exact hinj (h1.trans (map_zero _).symm)

theorem weight_pow {n : ℕ} (hn : (n : K) ≠ 0) (hMn : ∀ m ∈ M, m ^ n = 1)
    {χ : M → AlgebraicClosure K} (hχ : wsp M χ ≠ ⊥) (m : M) (k : ℕ) : χ (m ^ k) = χ m ^ k := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have h1 := apply_of_mem_wsp hn hMn (m ^ k) hv
  have h2 : ∀ j : ℕ, (endL (m : GL (Fin 3) K) ^ j) v = χ m ^ j • v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, apply_of_mem_wsp hn hMn m hv, smul_smul,
        pow_succ]
  rw [Subgroup.coe_pow, map_pow, h2 k] at h1
  exact (smul_left_injective _ hv0 h1).symm

theorem eq_one_of_isPerfect_of_card_le_three {X I : Type*} [Group X] [Finite X] [Fintype I]
    [DecidableEq I] (hI : Fintype.card I ≤ 3) (hXp : Group.IsPerfect X)
    (hX3 : ¬ 3 ∣ Nat.card X) (ρ : X →* Equiv.Perm I) (g : X) : ρ g = 1 := by
  set H := ρ.range with hH
  have hHp : Group.IsPerfect H := Group.IsPerfect.range ρ
  have hdvd6 : Nat.card H ∣ 6 := by
    have h1 : Nat.card H ∣ Nat.card (Equiv.Perm I) := Subgroup.card_subgroup_dvd_card H
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := I)] at h1
    exact h1.trans ((Nat.factorial_dvd_factorial hI).trans (by norm_num [Nat.factorial]))
  have h3 : ¬ 3 ∣ Nat.card H := fun h => hX3 (h.trans (Subgroup.card_range_dvd ρ))
  have hcard : Nat.card H = 1 := by
    have hle : Nat.card H ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    have hpos : 0 < Nat.card H := Nat.card_pos
    interval_cases h : Nat.card H
    · rfl
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic H := isCyclic_of_prime_card h
      have : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [h]; norm_num)
      exact Group.IsPerfect.not_isMulCommutative H inferInstance
    · exact absurd (by norm_num) h3
    · norm_num at hdvd6
    · norm_num at hdvd6
    · exact absurd (by norm_num) h3
  have hmem : ρ g ∈ H := ⟨g, rfl⟩
  rw [Subgroup.eq_bot_of_card_eq H hcard, Subgroup.mem_bot] at hmem
  exact hmem

theorem le_centralizer_of_le_normalizer {X : Subgroup (GL (Fin 3) K)} {n : ℕ}
    (hM : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (hMn : ∀ m ∈ M, m ^ n = 1) (hn : (n : K) ≠ 0)
    (hXM : X ≤ Subgroup.normalizer (M : Set (GL (Fin 3) K))) [Finite X]
    (hXp : Group.IsPerfect X) (hX3 : ¬ 3 ∣ Nat.card X) :
    ∀ g ∈ X, ∀ m ∈ M, g * m = m * g := by
  classical
  have hind := iSupIndep_wsp hM
  let _ : Fintype (Wt M) := hind.fintypeNeBotOfFiniteDimensional
  have hcard : Fintype.card (Wt M) ≤ 3 := by
    have := hind.subtype_ne_bot_le_finrank
    rwa [Module.finrank_fin_fun] at this
  have hconj1 : ∀ (g h : GL (Fin 3) K) (hg : g ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K)))
      (hh : h ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K)))
      (hgh : g * h ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K))) (m : M),
      conjInv hgh m = conjInv hh (conjInv hg m) := fun g h hg hh hgh m => by
    apply Subtype.ext
    simp only [coe_conjInv]
    group
  have hconjone : ∀ (h1 : (1 : GL (Fin 3) K) ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K)))
      (m : M), conjInv h1 m = m := fun h1 m => Subtype.ext (by simp [coe_conjInv])
  let act : X → Wt M → Wt M := fun g χ =>
    ⟨χ.1 ∘ conjInv (hXM g.2), wsp_comp_ne_bot (hXM g.2) χ.2⟩
  have hact_mul : ∀ g h : X, ∀ χ, act (g * h) χ = act g (act h χ) := fun g h χ => by
    apply Subtype.ext
    funext m
    change χ.1 (conjInv (hXM (g * h).2) m) = χ.1 (conjInv (hXM h.2) (conjInv (hXM g.2) m))
    rw [hconj1]
  have hact_one : ∀ χ, act 1 χ = χ := fun χ => by
    apply Subtype.ext
    funext m
    change χ.1 (conjInv (hXM (1 : X).2) m) = χ.1 m
    rw [hconjone]
  let ρ : X →* Equiv.Perm (Wt M) :=
    { toFun := fun g =>
        { toFun := act g
          invFun := act g⁻¹
          left_inv := fun χ => by rw [← hact_mul, inv_mul_cancel, hact_one]
          right_inv := fun χ => by rw [← hact_mul, mul_inv_cancel, hact_one] }
      map_one' := Equiv.ext fun χ => hact_one χ
      map_mul' := fun g h => Equiv.ext fun χ => hact_mul g h χ }
  have hfix : ∀ g : X, ∀ χ : Wt M, act g χ = χ := fun g χ => by
    have h1 := eq_one_of_isPerfect_of_card_le_three hcard hXp hX3 ρ g
    exact congrArg (fun e : Equiv.Perm (Wt M) => e χ) h1
  intro g hg m hm
  have hgm : endL (g⁻¹ * m * g) = endL m := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ ⨆ χ, wsp M χ := (iSup_wsp_eq_top hM).symm ▸ Submodule.mem_top
    refine Submodule.iSup_induction (wsp M) (motive := fun v =>
      endL (g⁻¹ * m * g) v = endL m v) hv ?_ (by simp) (fun x y hx hy => by
        rw [map_add, map_add, hx, hy])
    intro χ x hx
    by_cases hχ : wsp M χ = ⊥
    · rw [hχ, Submodule.mem_bot] at hx
      rw [hx, map_zero, map_zero]
    · have h1 := apply_of_mem_wsp hn hMn (conjInv (hXM hg) ⟨m, hm⟩) hx
      have h2 := apply_of_mem_wsp hn hMn ⟨m, hm⟩ hx
      have h3 := congrArg (fun ψ : Wt M => ψ.1 ⟨m, hm⟩) (hfix ⟨g, hg⟩ ⟨χ, hχ⟩)
      change χ (conjInv (hXM hg) ⟨m, hm⟩) = χ ⟨m, hm⟩ at h3
      rw [coe_conjInv] at h1
      rw [h1, h2, h3]
  have h1 := endL_injective hgm
  calc g * m = g * (g⁻¹ * m * g) := by rw [h1]
    _ = m * g := by group

theorem false_of_order_five [Finite K] {y g : GL (Fin 3) K} (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1)
    (h5 : (5 : K) ≠ 0) (hg : g * y * g⁻¹ = y ^ 2) : False := by
  classical
  set M := Subgroup.zpowers y with hMdef
  have hM : ∀ x ∈ M, ∀ z ∈ M, x * z = z * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self y i j).eq
  have hMn : ∀ m ∈ M, m ^ 5 = 1 := by
    rintro _ ⟨i, rfl⟩
    change (y ^ i) ^ 5 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy5, one_zpow]
  have hn : ((5 : ℕ) : K) ≠ 0 := by exact_mod_cast h5
  have hyM : y ∈ M := Subgroup.mem_zpowers y
  have hc : ∀ i : ℕ, (g⁻¹ * y * g) ^ i = g⁻¹ * y ^ i * g := fun i => by
    simpa using conj_pow (a := g⁻¹) (b := y) (i := i)
  have hz : g⁻¹ * y * g = y ^ 3 := by
    have h1 : (g⁻¹ * y * g) ^ 2 = y := by
      calc (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g := hc 2
        _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hg]
        _ = y := by group
    have h2 : (g⁻¹ * y * g) ^ 5 = 1 := by
      calc (g⁻¹ * y * g) ^ 5 = g⁻¹ * y ^ 5 * g := hc 5
        _ = 1 := by rw [hy5]; group
    calc g⁻¹ * y * g = (g⁻¹ * y * g) ^ 6 := by
          rw [show 6 = 5 + 1 by norm_num, pow_succ, h2, one_mul]
      _ = ((g⁻¹ * y * g) ^ 2) ^ 3 := by rw [← pow_mul]
      _ = y ^ 3 := by rw [h1]
  have hgM : g ∈ Subgroup.normalizer (M : Set (GL (Fin 3) K)) := by
    have hle : M.map (MulAut.conj g).toMonoidHom ≤ M := by
      rw [hMdef, MonoidHom.map_zpowers, Subgroup.zpowers_le]
      change g * y * g⁻¹ ∈ Subgroup.zpowers y
      rw [hg]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2
    exact Subgroup.mem_normalizer_fintype fun w hw => hle ⟨w, hw, rfl⟩
  have hind := iSupIndep_wsp hM
  let _ : Fintype (Wt M) := hind.fintypeNeBotOfFiniteDimensional
  have hcard : Fintype.card (Wt M) ≤ 3 := by
    have := hind.subtype_ne_bot_le_finrank
    rwa [Module.finrank_fin_fun] at this
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ : Wt M, χ.1 ⟨y, hyM⟩ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hy1
    apply endL_injective
    rw [map_one]
    apply LinearMap.ext
    intro v
    have hv : v ∈ ⨆ χ, wsp M χ := (iSup_wsp_eq_top hM).symm ▸ Submodule.mem_top
    refine Submodule.iSup_induction (wsp M) (motive := fun v => endL y v = (1 : Module.End _ _) v)
      hv ?_ (by simp) (fun x z hx hz => by rw [map_add, map_add, hx, hz])
    intro χ x hx
    by_cases hχ : wsp M χ = ⊥
    · rw [hχ, Submodule.mem_bot] at hx
      rw [hx, map_zero, map_zero]
    · have h1 := apply_of_mem_wsp hn hMn ⟨y, hyM⟩ hx
      have h2 : χ ⟨y, hyM⟩ = 1 := hall ⟨χ, hχ⟩
      rw [h2, one_smul] at h1
      rw [Module.End.one_apply]
      exact h1
  let act : Wt M → Wt M := fun χ => ⟨χ.1 ∘ conjInv hgM, wsp_comp_ne_bot hgM χ.2⟩
  have hact : ∀ χ : Wt M, (act χ).1 ⟨y, hyM⟩ = χ.1 ⟨y, hyM⟩ ^ 3 := by
    intro χ
    change χ.1 (conjInv hgM ⟨y, hyM⟩) = χ.1 ⟨y, hyM⟩ ^ 3
    have h1 : conjInv hgM ⟨y, hyM⟩ = ⟨y, hyM⟩ ^ 3 := Subtype.ext (by rw [coe_conjInv, hz]; rfl)
    rw [h1, weight_pow hn hMn χ.2]
  set lam := χ₀.1 ⟨y, hyM⟩ with hlam
  have hlam5 : lam ^ 5 = 1 := by
    rw [hlam, ← weight_pow hn hMn χ₀.2]
    have h1 : (⟨y, hyM⟩ : M) ^ 5 = 1 := Subtype.ext hy5
    rw [h1]
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot χ₀.2
    have h2 := apply_of_mem_wsp hn hMn (1 : M) hv
    rw [OneMemClass.coe_one, map_one, Module.End.one_apply] at h2
    have h3 : (1 : AlgebraicClosure K) • v = χ₀.1 1 • v := by rw [one_smul]; exact h2
    exact (smul_left_injective _ hv0 h3).symm
  let w : Fin 4 → Wt M := fun i => act^[i] χ₀
  have hw : ∀ i : Fin 4, (w i).1 ⟨y, hyM⟩ = lam ^ (3 ^ (i : ℕ)) := by
    intro i
    change (act^[(i : ℕ)] χ₀).1 ⟨y, hyM⟩ = lam ^ (3 ^ (i : ℕ))
    generalize (i : ℕ) = k
    induction k with
    | zero => simp [hlam]
    | succ k ih =>
      rw [Function.iterate_succ_apply', hact, ih, ← pow_mul, pow_succ]
  have hdist : ∀ a b : ℕ, a < 5 → b < 5 → a < b → lam ^ a = lam ^ b → False := by
    intro a b ha hb hab h
    have h1 : lam ^ (b - a) = 1 := by
      have hne : lam ≠ 0 := fun h0 => by rw [h0, zero_pow (by norm_num)] at hlam5; norm_num at hlam5
      have : lam ^ a * lam ^ (b - a) = lam ^ a * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hab.le, mul_one, h]
      exact mul_left_cancel₀ (pow_ne_zero _ hne) this
    have h2 : orderOf lam ∣ Nat.gcd 5 (b - a) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hlam5) (orderOf_dvd_of_pow_eq_one h1)
    have h3 : Nat.gcd 5 (b - a) = 1 := by
      have : b - a < 5 := by omega
      have : 0 < b - a := by omega
      interval_cases (b - a) <;> rfl
    rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact hχ₀ h2
  have hinjpow : ∀ a b : ℕ, a < 5 → b < 5 → lam ^ a = lam ^ b → a = b := by
    intro a b ha hb h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact (hdist a b ha hb hab h).elim
    · exact hab
    · exact (hdist b a hb ha hab h.symm).elim
  have hres : ∀ i j : Fin 4, 3 ^ (i : ℕ) % 5 = 3 ^ (j : ℕ) % 5 → i = j := by decide
  have hwinj : Function.Injective w := by
    intro i j hij
    have h1 := congrArg (fun ψ : Wt M => ψ.1 ⟨y, hyM⟩) hij
    simp only [hw] at h1
    have hred : ∀ i : Fin 4, lam ^ (3 ^ (i : ℕ)) = lam ^ (3 ^ (i : ℕ) % 5) := fun i => by
      conv_lhs => rw [← Nat.div_add_mod (3 ^ (i : ℕ)) 5, pow_add, pow_mul, hlam5, one_pow,
        one_mul]
    rw [hred i, hred j] at h1
    exact hres i j (hinjpow _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1)
  have h4 := Fintype.card_le_of_injective w hwinj
  rw [Fintype.card_fin] at h4
  omega

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
