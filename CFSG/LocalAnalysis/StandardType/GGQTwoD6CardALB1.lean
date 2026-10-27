module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112AModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private def ggQ2d6l_psum (m : Fin 6 → ZMod 3) (i : Fin 5) : ZMod 3 :=
  ∑ j : Fin 6, if (j : ℕ) ≤ (i : ℕ) then m j else 0

private lemma ggQ2d6l_psum_sub (m n : Fin 6 → ZMod 3) (i : Fin 5) :
    ggQ2d6l_psum (m - n) i = ggQ2d6l_psum m i - ggQ2d6l_psum n i := by
  simp only [ggQ2d6l_psum, Pi.sub_apply]
  have h : (∑ x : Fin 6, if (x : ℕ) ≤ (i : ℕ) then m x - n x else 0) =
      (∑ x : Fin 6, ((if (x : ℕ) ≤ (i : ℕ) then m x else 0) -
        (if (x : ℕ) ≤ (i : ℕ) then n x else 0))) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hc : (j : ℕ) ≤ (i : ℕ) <;> simp [hc]
  rw [h]
  exact Finset.sum_sub_distrib _ _

private lemma ggQ2d6l_psum_single (a : Fin 6) (i : Fin 5) :
    ggQ2d6l_psum (Pi.single a 1) i = if (a : ℕ) ≤ (i : ℕ) then 1 else 0 := by
  rw [ggQ2d6l_psum, Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [Pi.single_eq_of_ne hba]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma ggQ2d6l_psum_delta (a b : Fin 6) (i : Fin 5) :
    ggQ2d6l_psum (Pi.single a 1 - Pi.single b 1) i =
      (if (a : ℕ) ≤ (i : ℕ) then (1 : ZMod 3) else 0) -
        (if (b : ℕ) ≤ (i : ℕ) then (1 : ZMod 3) else 0) := by
  rw [ggQ2d6l_psum_sub, ggQ2d6l_psum_single, ggQ2d6l_psum_single]

private lemma ggQ2d6l_psum_succ (i k : Fin 5) :
    ggQ2d6l_psum (Pi.single i.castSucc 1 - Pi.single i.succ 1) k =
      if k = i then 1 else 0 := by
  rw [ggQ2d6l_psum_delta]
  simp only [Fin.val_castSucc, Fin.val_succ]
  by_cases hki : k = i
  · subst hki
    simp
  · have hne : (k : ℕ) ≠ (i : ℕ) := fun h => hki (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : ¬ ((i : ℕ) ≤ (k : ℕ)) := by omega
      have h2 : ¬ ((i : ℕ) + 1 ≤ (k : ℕ)) := by omega
      rw [if_neg h1, if_neg h2]
      simp [hki]
    · have h1 : (i : ℕ) ≤ (k : ℕ) := by omega
      have h2 : (i : ℕ) + 1 ≤ (k : ℕ) := by omega
      rw [if_pos h1, if_pos h2]
      simp [hki]

private noncomputable def ggQ2d6l_mu {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 5 → V) : (Fin 6 → ZMod 3) →ₗ[ZMod 3] V where
  toFun m := ∑ i : Fin 5, ggQ2d6l_psum m i • h i
  map_add' x y := by
    simp only [ggQ2d6l_psum, Pi.add_apply]
    have h : (∑ i : Fin 5, (∑ j : Fin 6, if (j : ℕ) ≤ (i : ℕ) then x j + y j else 0) • h i) =
        ∑ i : Fin 5, ((∑ j : Fin 6, if (j : ℕ) ≤ (i : ℕ) then x j else 0) +
          (∑ j : Fin 6, if (j : ℕ) ≤ (i : ℕ) then y j else 0)) • h i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      have hxy : (∑ j : Fin 6, if (j : ℕ) ≤ (i : ℕ) then x j + y j else 0) =
          ∑ j : Fin 6, ((if (j : ℕ) ≤ (i : ℕ) then x j else 0) +
            (if (j : ℕ) ≤ (i : ℕ) then y j else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hc : (j : ℕ) ≤ (i : ℕ) <;> simp [hc]
      rw [hxy, Finset.sum_add_distrib]
    rw [h]
    simp only [add_smul]
    exact Finset.sum_add_distrib
  map_smul' c x := by
    simp only [ggQ2d6l_psum, Pi.smul_apply, smul_eq_mul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hcx : (∑ j : Fin 6, if (j : ℕ) ≤ (i : ℕ) then c * x j else 0) =
        c * (∑ j : Fin 6, if (j : ℕ) ≤ (i : ℕ) then x j else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hc : (j : ℕ) ≤ (i : ℕ) <;> simp [hc]
    rw [hcx, mul_smul]
    simp

private lemma ggQ2d6l_mu_inj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 5 → V) (hb : LinearIndependent (ZMod 3) h)
    {m : Fin 6 → ZMod 3} (hm : m ∈ d6SumZero) (hm0 : ggQ2d6l_mu h m = 0) : m = 0 := by
  have hp : ∀ i : Fin 5, ggQ2d6l_psum m i = 0 := by
    have hind := hb
    rw [Fintype.linearIndependent_iff] at hind
    exact hind (fun i => ggQ2d6l_psum m i) hm0
  have hs : ∑ j : Fin 6, m j = 0 := by
    simpa [d6SumZero] using hm
  funext k
  simp only [Pi.zero_apply]
  fin_cases k
  · have h0 := hp 0
    simp [ggQ2d6l_psum] at h0
    simpa using h0
  · change m 1 = 0
    have h0 := hp 0
    have h1 := hp 1
    simp [ggQ2d6l_psum, Fin.sum_univ_six] at h0 h1
    linear_combination h1 - h0
  · change m 2 = 0
    have h1 := hp 1
    have h2 := hp 2
    simp [ggQ2d6l_psum, Fin.sum_univ_six] at h1 h2
    linear_combination h2 - h1
  · change m 3 = 0
    have h2 := hp 2
    have h3 := hp 3
    simp [ggQ2d6l_psum, Fin.sum_univ_six] at h2 h3
    linear_combination h3 - h2
  · change m 4 = 0
    have h3 := hp 3
    have h4 := hp 4
    simp [ggQ2d6l_psum, Fin.sum_univ_six] at h3 h4
    linear_combination h4 - h3
  · change m 5 = 0
    have h4 := hp 4
    have hs' := hs
    simp [Fin.sum_univ_six] at hs'
    simp [ggQ2d6l_psum, Fin.sum_univ_six] at h4
    linear_combination hs' - h4

private lemma ggQ2d6l_alpha_mu {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A 5 i j : ℤ) : ZMod 3))
    (i : Fin 5) (m : Fin 6 → ZMod 3) (hm : m ∈ d6SumZero) :
    α i (ggQ2d6l_mu h m) = m i.castSucc - m i.succ := by
  have hs : ∑ j : Fin 6, m j = 0 := by
    simpa [d6SumZero] using hm
  simp only [ggQ2d6l_mu, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul, hα]
  fin_cases i
  · simp [ggQ2d6l_psum, Fin.sum_univ_five, Fin.sum_univ_six, CartanMatrix.A]; ring_nf
  · simp [ggQ2d6l_psum, Fin.sum_univ_five, Fin.sum_univ_six, CartanMatrix.A]; ring_nf
  · simp [ggQ2d6l_psum, Fin.sum_univ_five, Fin.sum_univ_six, CartanMatrix.A]; ring_nf
  · simp [ggQ2d6l_psum, Fin.sum_univ_five, Fin.sum_univ_six, CartanMatrix.A]; ring_nf
  · simp [ggQ2d6l_psum, Fin.sum_univ_five, Fin.sum_univ_six, CartanMatrix.A] at hs ⊢
    rw [show (2 : ZMod 3) = 1 + 1 by decide, mul_add, mul_one]
    linear_combination (norm := abel) hs

private lemma ggQ2d6l_psum_swap (j : Fin 5) (m : Fin 6 → ZMod 3) (i : Fin 5) :
    ggQ2d6l_psum (d6PermAct (Equiv.swap j.castSucc j.succ) m) i =
      ggQ2d6l_psum m i + (if i = j then m j.succ - m j.castSucc else 0) := by
  fin_cases j <;> fin_cases i <;>
    simp only [ggQ2d6l_psum, d6PermAct, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft,
      Fin.sum_univ_six, Fin.val_zero,
      Fin.val_one, Fin.val_two]
  all_goals simp [Equiv.swap_apply_def]
  all_goals ring

private lemma ggQ2d6l_mu_swap {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A 5 i j : ℤ) : ZMod 3))
    (r : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (i : Fin 5) (m : Fin 6 → ZMod 3) (hm : m ∈ d6SumZero) :
    r i (ggQ2d6l_mu h m) =
      ggQ2d6l_mu h (d6PermAct (Equiv.swap i.castSucc i.succ) m) := by
  have hαmu := ggQ2d6l_alpha_mu h α hα i m hm
  have hdiff : ggQ2d6l_mu h (d6PermAct (Equiv.swap i.castSucc i.succ) m) =
      ggQ2d6l_mu h m + (m i.succ - m i.castSucc) • h i := by
    simp only [ggQ2d6l_mu]
    have hterm : ∀ k : Fin 5,
        ggQ2d6l_psum (d6PermAct (Equiv.swap i.castSucc i.succ) m) k • h k =
        ggQ2d6l_psum m k • h k +
          (if k = i then (m i.succ - m i.castSucc) else 0) • h k := by
      intro k
      rw [ggQ2d6l_psum_swap, add_smul]
    have hsum : (∑ k : Fin 5,
        (if k = i then (m i.succ - m i.castSucc) else 0) • h k) =
        (m i.succ - m i.castSucc) • h i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        rw [if_neg hki, zero_smul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    calc
      ∑ k : Fin 5, ggQ2d6l_psum (d6PermAct (Equiv.swap i.castSucc i.succ) m) k • h k
          = ∑ k : Fin 5, (ggQ2d6l_psum m k • h k +
              (if k = i then (m i.succ - m i.castSucc) else 0) • h k) :=
            Finset.sum_congr rfl (fun k _ => hterm k)
      _ = (∑ k : Fin 5, ggQ2d6l_psum m k • h k) +
            (∑ k : Fin 5,
              (if k = i then (m i.succ - m i.castSucc) else 0) • h k) :=
            Finset.sum_add_distrib
      _ = (∑ k : Fin 5, ggQ2d6l_psum m k • h k) +
            (m i.succ - m i.castSucc) • h i := by rw [hsum]
  rw [hr i (ggQ2d6l_mu h m), hαmu, hdiff]
  simp only [sub_eq_add_neg]
  module

private lemma ggQ2d6l_mu_delta {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 5 → V) (i : Fin 5) :
    ggQ2d6l_mu h (Pi.single i.castSucc 1 - Pi.single i.succ 1) = h i := by
  simp only [ggQ2d6l_mu, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · rw [ggQ2d6l_psum_succ, if_pos rfl, one_smul]
  · intro k _ hki
    rw [ggQ2d6l_psum_succ, if_neg hki, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma ggQ2d6l_r_mul_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A 5 i j : ℤ) : ZMod 3))
    (r : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (i : Fin 5) : r i * r i = 1 := by
  have hrefl : α i (h i) = (2 : ZMod 3) := by
    rw [hα i i]
    fin_cases i <;> decide
  have hreq : r i = Module.reflection hrefl := by
    ext v
    rw [hr i v, Module.reflection_apply]
  rw [hreq]
  nth_rewrite 2 [← Module.reflection_inv hrefl]
  exact mul_inv_cancel _

private lemma ggQ2d6l_r_symm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A 5 i j : ℤ) : ZMod 3))
    (r : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (i : Fin 5) : (r i).symm = r i := by
  have hrefl : α i (h i) = (2 : ZMod 3) := by
    rw [hα i i]
    fin_cases i <;> decide
  have hreq : r i = Module.reflection hrefl := by
    ext v
    rw [hr i v, Module.reflection_apply]
  rw [hreq, Module.reflection_symm]

private lemma ggQ2d6l_swap_diff (a b : Fin 6) (hab : a ≠ b) (p : Fin 6 → ZMod 3) :
    p - d6PermAct (Equiv.swap a b) p =
      (p a - p b) • (Pi.single a 1 - Pi.single b 1) := by
  funext j
  simp only [Pi.sub_apply]
  have h1 : (d6PermAct (Equiv.swap a b) p) j = p ((Equiv.swap a b) j) := by
    simp [d6PermAct, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft]
  rw [h1]
  simp only [Pi.smul_apply]
  by_cases hja : j = a
  · subst hja
    rw [Equiv.swap_apply_left]
    simp [hab]
    ring_nf
  · by_cases hjb : j = b
    · subst hjb
      rw [Equiv.swap_apply_right]
      simp [hja]
      ring_nf
    · rw [Equiv.swap_apply_def]
      simp [hja, hjb]

private noncomputable def ggQ2d6l_fLin {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (U : Submodule (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (h : ∀ v : V, a v - v ∈ U) : V →ₗ[ZMod 3] U where
  toFun v := ⟨a v - v, h v⟩
  map_add' x y := by
    ext
    simp only [map_add, Submodule.coe_add]
    module
  map_smul' c x := by
    ext
    simp [smul_sub]

private noncomputable def ggQ2d6l_restrict {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (U : Submodule (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (ha : ∀ u : U, a (u : V) ∈ U) (hai : ∀ u : U, a.symm (u : V) ∈ U) :
    U ≃ₗ[ZMod 3] U where
  toFun u := ⟨a (u : V), ha u⟩
  invFun u := ⟨a.symm (u : V), hai u⟩
  map_add' x y := by ext; exact map_add a (x : V) (y : V)
  map_smul' c x := by ext; exact map_smul a c (x : V)
  left_inv u := by ext; exact a.symm_apply_apply (u : V)
  right_inv u := by ext; exact a.apply_symm_apply (u : V)

theorem ggQ2d6l_A5lift {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (h : Fin 5 → V)
    (hb : LinearIndependent (ZMod 3) h) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.A 5 i j : ℤ) : ZMod 3))
    (r : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (hnt : ∀ a ∈ Subgroup.closure (Set.range r), ∀ (q : Module.Dual (ZMod 3) V) (w : V),
      q ≠ 0 → w ≠ 0 → q w = 0 → (∀ v, a v = v + q v • w) → False) :
    ∃ Dm : D6Mod V, Function.Injective Dm.ρ ∧
      ∀ i : Fin 5, Dm.ρ (Equiv.swap i.castSucc i.succ) = r i := by
  let U : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range h)
  have hU : ∀ j, h j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hbU : LinearIndependent (ZMod 3) (fun i => (⟨h i, hU i⟩ : U)) := by
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    have hval := congrArg (fun x : U => (x : V)) hg
    simpa using hval
  have hspanU : Submodule.span (ZMod 3)
      (Set.range (fun i => (⟨h i, hU i⟩ : U))) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hxU : (x : V) ∈ U := x.2
    have hmem : (⟨(x : V), hxU⟩ : U) ∈ Submodule.span (ZMod 3)
        (Set.range (fun i => (⟨h i, hU i⟩ : U))) := by
      refine Submodule.span_induction
        (p := fun y hy => (⟨y, hy⟩ : U) ∈ Submodule.span (ZMod 3)
          (Set.range (fun i => (⟨h i, hU i⟩ : U)))) ?_ ?_ ?_ ?_ hxU
      · rintro y ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, rfl⟩
      · exact Submodule.zero_mem _
      · intro y z hy hz ihy ihz
        exact Submodule.add_mem _ ihy ihz
      · intro c y hy ihy
        exact Submodule.smul_mem _ c ihy
    simpa using hmem
  let αU : Fin 5 → Module.Dual (ZMod 3) U := fun i => (α i).comp U.subtype
  have hαU : ∀ i j, αU i (⟨h j, hU j⟩ : U) = ((CartanMatrix.A 5 i j : ℤ) : ZMod 3) :=
    fun i j => hα i j
  obtain ⟨Φ₀, hΦ₀inj, hΦ₀swap⟩ :=
    ggQ2xKD_A_model (n := 5) (by omega) (fun i => (⟨h i, hU i⟩ : U)) hbU hspanU αU hαU
  let μ : d6SumZero →ₗ[ZMod 3] V := (ggQ2d6l_mu h).comp d6SumZero.subtype
  have hμ_apply : ∀ m : d6SumZero, μ m = ggQ2d6l_mu h (m : Fin 6 → ZMod 3) := fun m => rfl
  have hμ_inj : Function.Injective μ := by
    intro x y hxy
    apply Subtype.ext
    have hm : ((x : Fin 6 → ZMod 3) - (y : Fin 6 → ZMod 3)) ∈ d6SumZero :=
      d6SumZero.sub_mem x.2 y.2
    have h0 : ggQ2d6l_mu h ((x : Fin 6 → ZMod 3) - (y : Fin 6 → ZMod 3)) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (ggQ2d6l_mu_inj h hb hm h0)
  have hδmem_gen : ∀ a b : Fin 6,
      (Pi.single a 1 - Pi.single b 1 : Fin 6 → ZMod 3) ∈ d6SumZero := by
    intro a b
    simp only [d6SumZero, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply]
    fin_cases a <;> fin_cases b <;> decide
  have hδmem : ∀ i : Fin 5,
      (Pi.single i.castSucc 1 - Pi.single i.succ 1 : Fin 6 → ZMod 3) ∈ d6SumZero :=
    fun i => hδmem_gen i.castSucc i.succ
  have hμ_range : LinearMap.range μ = U := by
    apply le_antisymm
    · rintro v ⟨m, rfl⟩
      change (∑ i : Fin 5, ggQ2d6l_psum (m : Fin 6 → ZMod 3) i • h i) ∈ U
      exact Submodule.sum_mem U (fun i _ => Submodule.smul_mem U _ (hU i))
    · apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      exact ⟨⟨Pi.single i.castSucc 1 - Pi.single i.succ 1, hδmem i⟩,
        ggQ2d6l_mu_delta h i⟩
  let μU : d6SumZero →ₗ[ZMod 3] U := μ.codRestrict U (fun m => by
    rw [← hμ_range]
    exact LinearMap.mem_range_self μ m)
  have hμU_bij : Function.Bijective μU := by
    constructor
    · intro x y hxy
      apply hμ_inj
      exact congrArg (fun u : U => (u : V)) hxy
    · intro u
      have hu : (u : V) ∈ LinearMap.range μ := by rw [hμ_range]; exact u.2
      obtain ⟨m, hm⟩ := hu
      refine ⟨m, ?_⟩
      ext
      exact hm
  let μEquiv : d6SumZero ≃ₗ[ZMod 3] U := LinearEquiv.ofBijective μU hμU_bij
  have hμEquiv_apply : ∀ m, (μEquiv m : V) = ggQ2d6l_mu h (m : Fin 6 → ZMod 3) :=
    fun m => rfl
  have hr2 : ∀ i : Fin 5, r i * r i = 1 := fun i => ggQ2d6l_r_mul_self h α hα r hr i
  let Hsub : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range r)
  have hpresR : ∀ (i : Fin 5) (v : V), v ∈ U → r i v ∈ U := by
    intro i v hv
    refine Submodule.span_induction (p := fun y _ => r i y ∈ U) ?_ ?_ ?_ ?_ hv
    · rintro y ⟨j, rfl⟩
      rw [hr i (h j)]
      exact Submodule.sub_mem U (hU j) (Submodule.smul_mem U (α i (h j)) (hU i))
    · rw [map_zero]
      exact Submodule.zero_mem U
    · intro y z hy hz ihy ihz
      rw [map_add]
      exact Submodule.add_mem U ihy ihz
    · intro c y hy ihy
      rw [map_smul]
      exact Submodule.smul_mem U c ihy
  have hQ : ∀ a : V ≃ₗ[ZMod 3] V, a ∈ Hsub →
      (∀ u : U, a (u : V) ∈ U) ∧ (∀ u : U, a.symm (u : V) ∈ U) := by
    intro a ha
    refine Subgroup.closure_induction
      (p := fun a _ => (∀ u : U, a (u : V) ∈ U) ∧ (∀ u : U, a.symm (u : V) ∈ U))
      ?_ ?_ ?_ ?_ ha
    · rintro x ⟨i, rfl⟩
      exact ⟨fun u => hpresR i u u.2, fun u => by
        rw [ggQ2d6l_r_symm h α hα r hr i]
        exact hpresR i u u.2⟩
    · constructor
      · intro u; exact u.2
      · intro u; exact u.2
    · intro x y hx hy ihx ihy
      constructor
      · intro u
        exact ihx.1 ⟨y (u : V), ihy.1 u⟩
      · intro u
        change y.symm (x.symm (u : V)) ∈ U
        exact ihy.2 ⟨x.symm (u : V), ihx.2 u⟩
    · intro x hx ih
      constructor
      · exact ih.2
      · intro u
        change x (u : V) ∈ U
        exact ih.1 u
  have hDiff : ∀ a : V ≃ₗ[ZMod 3] V, a ∈ Hsub → ∀ v : V, a v - v ∈ U := by
    intro a ha
    refine Subgroup.closure_induction (p := fun a _ => ∀ v : V, a v - v ∈ U)
      ?_ ?_ ?_ ?_ ha
    · rintro x ⟨i, rfl⟩
      intro v
      have h : r i v - v = -(α i v • h i) := by rw [hr i v]; abel
      rw [h]
      exact Submodule.neg_mem U (Submodule.smul_mem U (α i v) (hU i))
    · intro v
      simp
    · intro x y hx hy ihx ihy v
      have h1 : x (y v) - y v ∈ U := ihx (y v)
      have h2 : y v - v ∈ U := ihy v
      have h : x (y v) - v = (x (y v) - y v) + (y v - v) := by abel
      change x (y v) - v ∈ U
      rw [h]
      exact Submodule.add_mem U h1 h2
    · intro x hx ih v
      have h1 : x (x.symm v) - x.symm v ∈ U := ih (x.symm v)
      have h : x.symm v - v = -(x (x.symm v) - x.symm v) := by
        rw [x.apply_symm_apply]
        abel
      change x.symm v - v ∈ U
      rw [h]
      exact Submodule.neg_mem U h1
  let R : Hsub →* (U ≃ₗ[ZMod 3] U) :=
    { toFun := fun a => ggQ2d6l_restrict U a.1 (hQ a.1 a.2).1 (hQ a.1 a.2).2
      map_one' := by ext u; rfl
      map_mul' := by intro a b; ext u; rfl }
  have hRr : ∀ i : Fin 5,
      R ⟨r i, Subgroup.subset_closure ⟨i, rfl⟩⟩ = Φ₀ (Equiv.swap i.castSucc i.succ) := by
    intro i
    ext u
    change r i (u : V) = (Φ₀ (Equiv.swap i.castSucc i.succ)) u
    rw [hΦ₀swap i u, hr i (u : V)]
    rfl
  have hGen : ∀ σ : Equiv.Perm (Fin 6), ∃ a : Hsub, R a = Φ₀ σ ∧
      ∀ m : d6SumZero, a.1 (μ m) = μ ⟨d6PermAct σ m, d6PermAct_mem σ m.2⟩ := by
    intro σ
    have htop := Equiv.Perm.mclosure_swap_castSucc_succ 5
    have hmem : σ ∈ Submonoid.closure
        (Set.range (fun i : Fin 5 => Equiv.swap i.castSucc i.succ)) := by
      rw [htop]
      exact Submonoid.mem_top σ
    refine Submonoid.closure_induction
      (motive := fun σ _ => ∃ a : Hsub, R a = Φ₀ σ ∧
        ∀ m : d6SumZero, a.1 (μ m) = μ ⟨d6PermAct σ m, d6PermAct_mem σ m.2⟩)
      ?_ ?_ ?_ hmem
    · rintro x ⟨i, rfl⟩
      refine ⟨⟨r i, Subgroup.subset_closure ⟨i, rfl⟩⟩, hRr i, ?_⟩
      intro m
      change r i (μ m) = μ ⟨d6PermAct (Equiv.swap i.castSucc i.succ) m,
        d6PermAct_mem (Equiv.swap i.castSucc i.succ) m.2⟩
      rw [hμ_apply m]
      change r i (ggQ2d6l_mu h (m : Fin 6 → ZMod 3)) =
        ggQ2d6l_mu h (d6PermAct (Equiv.swap i.castSucc i.succ) (m : Fin 6 → ZMod 3))
      rw [ggQ2d6l_mu_swap h α hα r hr i (m : Fin 6 → ZMod 3) m.2]
    · refine ⟨1, ?_, ?_⟩
      · simp
      · intro m
        change μ m = μ ⟨d6PermAct 1 m, d6PermAct_mem 1 m.2⟩
        apply congrArg μ
        apply Subtype.ext
        funext k
        congr 1
    · rintro x y hx hy ⟨a, haR, haE⟩ ⟨b, hbR, hbE⟩
      refine ⟨a * b, ?_, ?_⟩
      · rw [map_mul, map_mul, haR, hbR]
      · intro m
        change a.1 (b.1 (μ m)) = μ ⟨d6PermAct (x * y) m,
          d6PermAct_mem (x * y) m.2⟩
        rw [hbE m]
        rw [haE ⟨d6PermAct y m, d6PermAct_mem y m.2⟩]
        rfl
  have hker : ∀ a : Hsub, R a = 1 → a = 1 := by
    intro a haR
    by_contra hne
    let g : V →ₗ[ZMod 3] U := ggQ2d6l_fLin U a.1 (hDiff a.1 a.2)
    let gbar : V →ₗ[ZMod 3] d6SumZero := μEquiv.symm.toLinearMap.comp g
    let coord : Fin 6 → (V →ₗ[ZMod 3] ZMod 3) := fun j =>
      (LinearMap.proj j : (Fin 6 → ZMod 3) →ₗ[ZMod 3] ZMod 3).comp
        (d6SumZero.subtype.comp gbar)
    have hg_coe : ∀ v : V, (g v : V) = a.1 v - v := fun v => rfl
    have hbar : ∀ v : V, μEquiv (gbar v) = g v := fun v => μEquiv.apply_symm_apply (g v)
    let act : Equiv.Perm (Fin 6) → d6SumZero → d6SumZero :=
      fun σ m => ⟨d6PermAct σ m, d6PermAct_mem σ m.2⟩
    let dsub : d6SumZero → d6SumZero → d6SumZero := fun x y =>
      ⟨(x : Fin 6 → ZMod 3) - y, d6SumZero.sub_mem x.2 y.2⟩
    have hμ_dsub : ∀ x y : d6SumZero, μ (dsub x y) = μ x - μ y := by
      intro x y
      change ggQ2d6l_mu h ((x : Fin 6 → ZMod 3) - y) =
        ggQ2d6l_mu h x - ggQ2d6l_mu h y
      exact map_sub (ggQ2d6l_mu h) _ _
    have hcoord_U : ∀ (j : Fin 6) (u : U), coord j (u : V) = 0 := by
      intro j u
      have hau : a.1 (u : V) = (u : V) := by
        have h := congrArg (fun e : U ≃ₗ[ZMod 3] U => (e : U → U) u) haR
        exact congrArg (fun x : U => (x : V))
          (by simpa [R, ggQ2d6l_restrict] using h)
      have hgu : g (u : V) = 0 := by
        apply Subtype.ext
        rw [hg_coe]
        rw [hau, sub_self]
        rfl
      have hbaru : gbar (u : V) = 0 := by
        change μEquiv.symm (g (u : V)) = 0
        rw [hgu]
        exact map_zero μEquiv.symm
      have hval := congrFun (congrArg (fun x : d6SumZero => (x : Fin 6 → ZMod 3)) hbaru) j
      simpa [coord, gbar] using hval
    by_cases hcase : ∀ j k : Fin 6, coord j = coord k
    · let c0 : d6SumZero := ⟨fun _ => (1 : ZMod 3), by
        simp only [d6SumZero, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply]
        decide⟩
      let φ : V →ₗ[ZMod 3] ZMod 3 := coord 0
      have hgb : ∀ v : V, gbar v = φ v • c0 := by
        intro v
        apply Subtype.ext
        funext j
        have hjk := congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f v) (hcase j 0)
        simpa [coord, φ, c0] using hjk
      have hc0_ne : c0 ≠ 0 := by
        intro h
        have := congrFun (congrArg (fun x : d6SumZero => (x : Fin 6 → ZMod 3)) h) 0
        simp [c0] at this
      have hφ_ne : φ ≠ 0 := by
        intro hφ
        apply hne
        apply Subtype.ext
        ext v
        have hv : (g v : V) = 0 := by
          have hφ0 : φ v = 0 := by rw [hφ]; rfl
          have h0 : gbar v = 0 := by rw [hgb v, hφ0, zero_smul]
          rw [← hbar v, h0, map_zero]
          rfl
        change a.1 v = v
        rw [← sub_eq_zero, ← hg_coe v]
        exact hv
      have hw : (μ c0 : V) ≠ 0 := by
        intro h
        exact hc0_ne (hμ_inj (by simpa using h))
      have hwU : (μ c0 : V) ∈ U := by
        rw [← hμ_range]
        exact LinearMap.mem_range_self μ c0
      have hφw : φ (μ c0) = 0 := hcoord_U 0 ⟨μ c0, hwU⟩
      have hact : ∀ v : V, a.1 v = v + φ v • (μ c0) := by
        intro v
        have hgv : (g v : V) = φ v • (μ c0) := by
          rw [← hbar v, hgb v, map_smul]
          rfl
        calc a.1 v = v + (g v : V) := by
              rw [hg_coe v]
              abel
          _ = v + φ v • (μ c0) := by rw [hgv]
      exact hnt a a.2 φ (μ c0) hφ_ne hw hφw hact
    · push Not at hcase
      obtain ⟨a0, b0, habcoord⟩ := hcase
      have hab : a0 ≠ b0 := fun h => habcoord (by rw [h])
      have hv0ex : ∃ v, coord a0 v ≠ coord b0 v := by
        by_contra h
        apply habcoord
        ext v
        by_contra hv
        exact h ⟨v, hv⟩
      obtain ⟨v0, hv0⟩ := hv0ex
      obtain ⟨P, hPR, hPE⟩ := hGen (Equiv.swap a0 b0)
      let k : Hsub := P * a * P⁻¹
      let T : Hsub := a * k⁻¹
      have hkR : R k = 1 := by
        simp only [k, map_mul, map_inv, hPR, haR, mul_one]
        exact mul_inv_cancel _
      have hTR : R T = 1 := by
        simp only [T, map_mul, map_inv, hkR, haR, mul_one, inv_one]
      let d : d6SumZero := ⟨Pi.single a0 1 - Pi.single b0 1, hδmem_gen a0 b0⟩
      let w : V := μ d
      let q : V →ₗ[ZMod 3] ZMod 3 :=
        { toFun := fun v => coord a0 v - coord b0 v
          map_add' := by intro x y; simp only [map_add]; abel
          map_smul' := by
            intro c x
            simp only [map_smul, smul_eq_mul, RingHom.id_apply]
            rw [mul_sub, mul_comm c ((coord a0) x), mul_comm c ((coord b0) x)] }
      have hq_ne : q ≠ 0 := by
        intro hq
        apply hv0
        have h := congrArg (fun f : V →ₗ[ZMod 3] ZMod 3 => f v0) hq
        have h' : coord a0 v0 - coord b0 v0 = 0 := by simpa [q] using h
        exact sub_eq_zero.mp h' 
      have hd_ne : (d : Fin 6 → ZMod 3) ≠ 0 := by
        intro h
        have := congrFun h a0
        simp [d, Pi.single_eq_same, Pi.single_eq_of_ne hab] at this
        norm_num at this
      have hw : w ≠ 0 := by
        intro h
        apply hd_ne
        have hm : μ d = μ (0 : d6SumZero) := by simpa [w] using h
        have hd0 : d = 0 := hμ_inj hm
        exact congrArg (fun x : d6SumZero => (x : Fin 6 → ZMod 3)) hd0
      have hwU : w ∈ U := by
        change μ d ∈ U
        rw [← hμ_range]
        exact LinearMap.mem_range_self μ d
      have hqw : q w = 0 := by
        have h1 := hcoord_U a0 ⟨w, hwU⟩
        have h2 := hcoord_U b0 ⟨w, hwU⟩
        simp [q, h1, h2]
      have hkact : ∀ v : V, k.1 v = v + μEquiv (act (Equiv.swap a0 b0) (gbar v)) := by
        intro v
        let u : V := P.1.symm v - v
        have hu : u ∈ U := hDiff P.1⁻¹ (Subgroup.inv_mem Hsub P.2) v
        have hPi : P.1.symm v = v + u := by dsimp [u]; abel
        have ha_u : a.1 u = u := by
          have h := congrArg (fun e : U ≃ₗ[ZMod 3] U => (e : U → U) ⟨u, hu⟩) haR
          simpa [R, ggQ2d6l_restrict] using h
        have hPg : P.1 (g v) = μEquiv (act (Equiv.swap a0 b0) (gbar v)) := by
          rw [← hbar v]
          change P.1 (μ (gbar v)) =
            μ ⟨d6PermAct (Equiv.swap a0 b0) (gbar v : Fin 6 → ZMod 3),
              d6PermAct_mem (Equiv.swap a0 b0) (gbar v).2⟩
          exact hPE (gbar v)
        calc k.1 v = P.1 (a.1 (P.1.symm v)) := rfl
          _ = P.1 (a.1 (v + u)) := by rw [hPi]
          _ = P.1 (a.1 v + a.1 u) := by rw [map_add]
          _ = P.1 ((v + (g v : V)) + u) := by
                have hav : a.1 v = v + (g v : V) := by rw [hg_coe v]; abel
                rw [hav, ha_u]
          _ = P.1 ((v + u) + (g v : V)) := by congr 1; abel
          _ = P.1 (v + u) + P.1 (g v) := by rw [map_add]
          _ = v + P.1 (g v) := by rw [← hPi, LinearEquiv.apply_symm_apply]
          _ = v + μEquiv (act (Equiv.swap a0 b0) (gbar v)) := by rw [hPg]
      have hkinv : ∀ v : V,
          k.1.symm v = v - μEquiv (act (Equiv.swap a0 b0) (gbar v)) := by
        intro v
        let qV : V := μEquiv (act (Equiv.swap a0 b0) (gbar v))
        have hqVU : qV ∈ U := (μEquiv _).2
        have hkq : k.1 qV = qV := by
          have h := congrArg (fun e : U ≃ₗ[ZMod 3] U => (e : U → U) ⟨qV, hqVU⟩) hkR
          simpa [R, ggQ2d6l_restrict] using h
        apply k.1.injective
        rw [k.1.apply_symm_apply]
        symm
        change k.1 (v - qV) = v
        rw [map_sub, hkact v, hkq]
        abel
      have hTact : ∀ v : V, T.1 v = v + q v • w := by
        intro v
        let p : d6SumZero := gbar v
        let qV : V := μEquiv (act (Equiv.swap a0 b0) p)
        have hqVU : qV ∈ U := (μEquiv _).2
        have ha_q : a.1 qV = qV := by
          have h := congrArg (fun e : U ≃ₗ[ZMod 3] U => (e : U → U) ⟨qV, hqVU⟩) haR
          simpa [R, ggQ2d6l_restrict] using h
        have hp_sub : dsub p (act (Equiv.swap a0 b0) p) = (q v) • d := by
          apply Subtype.ext
          change (p : Fin 6 → ZMod 3) -
              (((act (Equiv.swap a0 b0) p : d6SumZero) : Fin 6 → ZMod 3)) =
            (q v) • (Pi.single a0 1 - Pi.single b0 1)
          have hcoeff : q v = (p : Fin 6 → ZMod 3) a0 - (p : Fin 6 → ZMod 3) b0 := rfl
          rw [hcoeff]
          exact ggQ2d6l_swap_diff a0 b0 hab (p : Fin 6 → ZMod 3)
        have hdiff : (g v : V) - qV = q v • w := by
          have hgv : (g v : V) = μ p := by rw [← hbar v]; rfl
          have hqV : qV = μ ⟨act (Equiv.swap a0 b0) p,
              d6PermAct_mem (Equiv.swap a0 b0) p.2⟩ := rfl
          calc (g v : V) - qV = μ p - μ (act (Equiv.swap a0 b0) p) := by rw [hgv, hqV]
            _ = μ (dsub p (act (Equiv.swap a0 b0) p)) := by rw [hμ_dsub]
            _ = μ ((q v) • d) := by rw [hp_sub]
            _ = q v • μ d := by rw [map_smul]
            _ = q v • w := rfl
        calc T.1 v = a.1 (k.1.symm v) := rfl
          _ = a.1 (v - qV) := by rw [hkinv v]
          _ = a.1 v - a.1 qV := by rw [map_sub]
          _ = (v + (g v : V)) - qV := by
                have hav : a.1 v = v + (g v : V) := by rw [hg_coe v]; abel
                rw [hav, ha_q]
          _ = v + ((g v : V) - qV) := by abel
          _ = v + q v • w := by rw [hdiff]
      exact hnt T T.2 q w hq_ne hw hqw hTact
  have hRinj : Function.Injective R := by
    intro x y hxy
    have h1 : R (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy]
      simp
    have h2 : x * y⁻¹ = 1 := hker _ h1
    calc x = x * y⁻¹ * y := by group
      _ = 1 * y := by rw [h2]
      _ = y := one_mul y
  let ρ : Equiv.Perm (Fin 6) →* Hsub :=
    { toFun := fun σ => Classical.choose (hGen σ)
      map_one' := by
        apply hRinj
        rw [(Classical.choose_spec (hGen 1)).1, map_one]
        rw [map_one]
      map_mul' := by
        intro σ τ
        apply hRinj
        rw [(Classical.choose_spec (hGen (σ * τ))).1, map_mul, map_mul,
          (Classical.choose_spec (hGen σ)).1, (Classical.choose_spec (hGen τ)).1] }
  have hρinj : Function.Injective ρ := by
    intro σ τ hστ
    have h1 : Φ₀ σ = Φ₀ τ := by
      calc Φ₀ σ = R (ρ σ) := ((Classical.choose_spec (hGen σ)).1).symm
        _ = R (ρ τ) := by rw [hστ]
        _ = Φ₀ τ := (Classical.choose_spec (hGen τ)).1
    exact hΦ₀inj h1
  let Dm : D6Mod V :=
    { ρ := Hsub.subtype.comp ρ
      μ := μ
      μ_inj := hμ_inj
      μ_comm := by
        intro σ m
        exact (Classical.choose_spec (hGen σ)).2 m
      triv := by
        intro σ v
        rw [hμ_range]
        exact hDiff (ρ σ).1 (ρ σ).2 v }
  refine ⟨Dm, ?_, ?_⟩
  · intro σ τ hστ
    apply hρinj
    exact Subtype.ext hστ
  · intro i
    have hR : R (ρ (Equiv.swap i.castSucc i.succ)) =
        Φ₀ (Equiv.swap i.castSucc i.succ) :=
      (Classical.choose_spec (hGen (Equiv.swap i.castSucc i.succ))).1
    have hEq : ρ (Equiv.swap i.castSucc i.succ) =
        ⟨r i, Subgroup.subset_closure ⟨i, rfl⟩⟩ := by
      apply hRinj
      rw [hR, hRr i]
    exact congrArg (fun a : Hsub => (a.1 : V ≃ₗ[ZMod 3] V)) hEq

end CFSG.StandardType

end
