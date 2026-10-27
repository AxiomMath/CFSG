module

public import CFSG.RankThree.GF2n.Smith81.S81JAct

public section

namespace CFSG.RankThree.GF2n.Smith81.S81J

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem linearIndependent_of_eigen {ι D : Type*} [Finite ι] (r : D → V →ₗ[K] V) (w : ι → V)
    (χ : ι → D → K) (hw : ∀ i, w i ≠ 0) (hr : ∀ i d, r d (w i) = χ i d • w i)
    (hsep : ∀ i j, i ≠ j → ∃ d, χ i d ≠ χ j d) : LinearIndependent K w := by
  classical
  have key : ∀ i : ι, ∀ t : Finset ι, i ∉ t → ∃ (P : Module.End K V) (lam : ι → K),
      (∀ m, P (w m) = lam m • w m) ∧ lam i ≠ 0 ∧ ∀ k ∈ t, lam k = 0 := by
    intro i t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, fun _ => 1, fun m => by simp, one_ne_zero, by simp⟩
    | insert j t hjt ih =>
      intro hi
      have hij : i ≠ j := by
        intro h
        apply hi
        rw [h]
        exact Finset.mem_insert_self j t
      have hit : i ∉ t := fun h => hi (Finset.mem_insert_of_mem h)
      obtain ⟨P, lam, hP, hlam, hzero⟩ := ih hit
      obtain ⟨d, hd⟩ := hsep i j hij
      refine ⟨(r d - (χ j d) • (1 : Module.End K V)) * P, fun m => (χ m d - χ j d) * lam m,
        ?_, ?_, ?_⟩
      · intro m
        rw [Module.End.mul_apply, hP m, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, hr, ← sub_smul, smul_smul, mul_comm (lam m)]
      · exact mul_ne_zero (sub_ne_zero.mpr hd) hlam
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk'
        · simp
        · show (χ k d - χ j d) * lam k = 0
          rw [hzero k hk', mul_zero]
  rw [linearIndependent_iff']
  intro s g hs i hi
  obtain ⟨P, lam, hP, hlam, hzero⟩ := key i (s.erase i) (Finset.notMem_erase i s)
  have h1 : P (∑ k ∈ s, g k • w k) = 0 := by rw [hs, map_zero]
  rw [map_sum, Finset.sum_eq_single i] at h1
  · rw [map_smul, hP i, smul_smul] at h1
    rcases smul_eq_zero.mp h1 with h | h
    · exact (mul_eq_zero.mp h).resolve_right hlam
    · exact absurd h (hw i)
  · intro k hk hki
    rw [map_smul, hP k, hzero k (Finset.mem_erase.mpr ⟨hki, hk⟩), zero_smul, smul_zero]
  · intro h
    exact absurd hi h

abbrev J3 : Type := {I : Finset (Fin 6) // I.card = 3}

theorem card_J3 : Nat.card J3 = 20 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem weights_sep [CharP K 2] {ξ : Kˣ →* Kˣ} (hξ : ∃ c, ξ c ≠ 1) {I J : Finset (Fin 6)}
    (hI : I.card = 3) (hJ : J.card = 3) (hIJ : I ≠ J) :
    ∃ d : Fin 6 → Kˣ, ∏ i, d i = 1 ∧ ξ (∏ i ∈ I, d i) ≠ ξ (∏ i ∈ J, d i) := by
  obtain ⟨c, hc⟩ := hξ
  have hIJs : ¬ I ⊆ J := fun h => hIJ (Finset.eq_of_subset_of_card_le h (by omega))
  have hJIs : ¬ J ⊆ I := fun h => hIJ (Finset.eq_of_subset_of_card_le h (by omega)).symm
  obtain ⟨p, hpI, hpJ⟩ := Finset.not_subset.mp hIJs
  obtain ⟨r, hrJ, hrI⟩ := Finset.not_subset.mp hJIs
  have hpr : p ≠ r := by
    intro h
    apply hrI
    rw [← h]
    exact hpI
  have hd_p : cOn p r c p = c := by simp [cOn]
  have hd_r : cOn p r c r = c⁻¹ := by simp [cOn, hpr.symm]
  have hd_other : ∀ b, b ≠ p → b ≠ r → cOn p r c b = 1 := fun b hbp hbr => by
    simp [cOn, hbp, hbr]
  refine ⟨cOn p r c, ?_, ?_⟩
  · rw [Finset.prod_eq_mul (s := Finset.univ) p r hpr
      (fun x _ hx => hd_other x hx.1 hx.2)
      (fun h => absurd (Finset.mem_univ p) h) (fun h => absurd (Finset.mem_univ r) h),
      hd_p, hd_r, mul_inv_cancel]
  · have hPI : ∏ i ∈ I, cOn p r c i = c := by
      rw [Finset.prod_eq_single p (fun b hb hbp => hd_other b hbp (fun hbr => hrI (hbr ▸ hb)))
        (fun h => absurd hpI h), hd_p]
    have hPJ : ∏ i ∈ J, cOn p r c i = c⁻¹ := by
      rw [Finset.prod_eq_single r (fun b hb hbr => hd_other b (fun hbp => hpJ (hbp ▸ hb)) hbr)
        (fun h => absurd hrJ h), hd_r]
    rw [hPI, hPJ]
    intro hEq
    apply hc
    have h1 : ξ c * ξ c = 1 := by
      calc ξ c * ξ c = ξ c * ξ c⁻¹ := by rw [← hEq]
        _ = ξ (c * c⁻¹) := (map_mul ξ c c⁻¹).symm
        _ = 1 := by rw [mul_inv_cancel, map_one]
    have h2 : ((ξ c : Kˣ) : K) * ((ξ c : Kˣ) : K) = 1 := by
      have := congrArg Units.val h1
      simpa using this
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : ((ξ c : Kˣ) : K) - 1 = 0 := by
      apply mul_self_eq_zero.mp
      linear_combination h2 + (1 - ((ξ c : Kˣ) : K)) * h2K
    exact Units.ext (sub_eq_zero.mp h3)

namespace SLAct

variable (A : SLAct K V)

private theorem basB_swap_mem : ∀ x y w : Fin 6, (x ∈ I0 ↔ y ∈ I0) →
    (Equiv.swap x y w ∈ I0 ↔ w ∈ I0) := by
  decide

private theorem basB_image_swap : ∀ x y : Fin 6, (x ∈ I0 ↔ y ∈ I0) →
    I0.image (Equiv.swap x y) = I0 := by
  decide

private theorem basB_symm_mem (σ : Equiv.Perm (Fin 6)) (S : Finset (Fin 6)) (z : Fin 6) :
    σ.symm z ∈ S ↔ z ∈ S.image σ := by
  constructor
  · intro hz
    exact Finset.mem_image.mpr ⟨σ.symm z, hz, σ.apply_symm_apply z⟩
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    rwa [Equiv.symm_apply_apply]

private theorem basB_swap_fix [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {x y : Fin 6}
    (hxy : x ∈ I0 ↔ y ∈ I0) :
    ∀ v ∈ A.Fix (Wc K I0), A.act (pm K (Equiv.swap x y)) v = v := by
  have hp : ((pm K (Equiv.swap x y) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    det_pm (K := K) _
  have hpp : pm K (Equiv.swap x y) * pm K (Equiv.swap x y) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hmap : (Wc K I0).map (Matrix.mulVecLin
      ((pm K (Equiv.swap x y) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = Wc K I0 := by
    rw [Wc_map_pm (K := K), basB_image_swap x y hxy]
  have hpW : ∀ w ∈ Wc K I0,
      ((pm K (Equiv.swap x y) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec w ∈ Wc K I0 := by
    intro w hw
    have h2 := Submodule.mem_map_of_mem (f := Matrix.mulVecLin
      ((pm K (Equiv.swap x y) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hw
    rw [hmap] at h2
    exact h2
  exact act_invol_fix A hp hpp hpW h0

private theorem basB_fix_perm [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) :
    ∀ n : ℕ, ∀ ρ : Equiv.Perm (Fin 6), (Finset.univ.filter fun x => ρ x ≠ x).card = n →
      (∀ x, ρ x ∈ I0 ↔ x ∈ I0) → ∀ v ∈ A.Fix (Wc K I0), A.act (pm K ρ) v = v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ρ hn hρ
    by_cases h1 : ∃ x, ρ x ≠ x
    · obtain ⟨x, hx⟩ := h1
      have hs : x ∈ I0 ↔ ρ x ∈ I0 := (hρ x).symm
      have hsI : ∀ w, Equiv.swap x (ρ x) w ∈ I0 ↔ w ∈ I0 :=
        fun w => basB_swap_mem x (ρ x) w hs
      have hρ' : ∀ z, (Equiv.swap x (ρ x) * ρ) z ∈ I0 ↔ z ∈ I0 := by
        intro z
        rw [Equiv.Perm.mul_apply]
        exact (hsI (ρ z)).trans (hρ z)
      have hsub : Finset.univ.filter (fun z => (Equiv.swap x (ρ x) * ρ) z ≠ z) ⊆
          Finset.univ.filter (fun z => ρ z ≠ z) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        intro hzρ
        apply hz
        rw [Equiv.Perm.mul_apply, hzρ]
        apply Equiv.swap_apply_of_ne_of_ne
        · intro hzx
          rw [hzx] at hzρ
          exact hx hzρ
        · intro hzy
          rw [hzy] at hzρ
          exact hx (ρ.injective hzρ)
      have hdec : (Finset.univ.filter fun z => (Equiv.swap x (ρ x) * ρ) z ≠ z).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset hsub]
        refine ⟨x, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hx
        · intro hmem
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          apply hmem
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      have hIH := ih _ hdec (Equiv.swap x (ρ x) * ρ) rfl hρ'
      have hfac : pm K ρ = pm K (Equiv.swap x (ρ x)) * pm K (Equiv.swap x (ρ x) * ρ) := by
        rw [← map_mul, Equiv.swap_mul_self_mul]
      intro v hv
      rw [hfac, A.act_mul (pm K (Equiv.swap x (ρ x))) (pm K (Equiv.swap x (ρ x) * ρ))
        (det_pm (K := K) _) (det_pm (K := K) _), Module.End.mul_apply, hIH v hv]
      exact basB_swap_fix A h0 hs v hv
    · simp only [not_exists, not_not] at h1
      have hρ1 : ρ = 1 := Equiv.ext h1
      subst hρ1
      intro v _
      simp [A.act_one]

theorem act_pm_fix_of_stab [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1)
    {ρ : Equiv.Perm (Fin 6)} (hρ : ∀ x, ρ x ∈ I0 ↔ x ∈ I0) :
    ∀ v ∈ A.Fix (Wc K I0), A.act (pm K ρ) v = v :=
  basB_fix_perm A h0 _ ρ rfl hρ

theorem act_pm_eq [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1)
    {σ τ : Equiv.Perm (Fin 6)} (h : I0.image σ = I0.image τ) :
    ∀ v ∈ A.Fix (Wc K I0), A.act (pm K σ) v = A.act (pm K τ) v := by
  intro v hv
  have hz : ∀ z, τ.symm z ∈ I0 ↔ σ.symm z ∈ I0 := by
    intro z
    rw [basB_symm_mem τ I0 z, basB_symm_mem σ I0 z, h]
  have hρ : ∀ x, (τ⁻¹ * σ) x ∈ I0 ↔ x ∈ I0 := by
    intro x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    have hx := hz (σ x)
    rw [Equiv.symm_apply_apply] at hx
    exact hx
  have hfac : pm K σ = pm K τ * pm K (τ⁻¹ * σ) := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [hfac, A.act_mul (pm K τ) (pm K (τ⁻¹ * σ)) (det_pm (K := K) τ)
    (det_pm (K := K) (τ⁻¹ * σ)), Module.End.mul_apply, act_pm_fix_of_stab A h0 hρ v hv]

noncomputable def vI (v₀ : V) (I : Finset (Fin 6)) : V :=
  if h : I.card = 3 then A.act (pm K (Classical.choose (exists_perm_image_eq I h))) v₀ else 0

theorem vI_eq [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {v₀ : V}
    (hv₀ : v₀ ∈ A.Fix (Wc K I0)) (σ : Equiv.Perm (Fin 6)) :
    A.act (pm K σ) v₀ = A.vI v₀ (I0.image σ) := by
  have hcard : (I0.image σ).card = 3 := by
    rw [Finset.card_image_of_injective _ σ.injective]
    decide
  have hτ := Classical.choose_spec (exists_perm_image_eq (I0.image σ) hcard)
  unfold vI
  rw [dif_pos hcard]
  exact act_pm_eq A h0 hτ.symm v₀ hv₀

theorem vI_I0 [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {v₀ : V}
    (hv₀ : v₀ ∈ A.Fix (Wc K I0)) : A.vI v₀ I0 = v₀ := by
  have h := vI_eq A h0 hv₀ 1
  have h1 : I0.image (1 : Equiv.Perm (Fin 6)) = I0 := by simp
  rw [h1, map_one, A.act_one, Module.End.one_apply] at h
  exact h.symm

theorem vI_mem [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {v₀ : V}
    (hv₀ : v₀ ∈ A.Fix (Wc K I0)) {I : Finset (Fin 6)} (hI : I.card = 3) :
    A.vI v₀ I ∈ A.Fix (Wc K I) := by
  obtain ⟨σ, hσ⟩ := exists_perm_image_eq I hI
  have e := vI_eq A h0 hv₀ σ
  rw [hσ] at e
  rw [← e]
  have hmem : A.act (pm K σ) v₀ ∈ (A.Fix (Wc K I0)).map (A.act (pm K σ)) :=
    Submodule.mem_map_of_mem hv₀
  rwa [act_pm_Fix A σ I0, hσ] at hmem

theorem vI_ne_zero [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {v₀ : V}
    (hv₀ : v₀ ∈ A.Fix (Wc K I0)) (hv0 : v₀ ≠ 0) {I : Finset (Fin 6)} (hI : I.card = 3) :
    A.vI v₀ I ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_perm_image_eq I hI
  have e := vI_eq A h0 hv₀ σ
  rw [hσ] at e
  intro h
  apply hv0
  have hinv := act_inv_act A (det_pm (K := K) σ) v₀
  rw [e, h, map_zero] at hinv
  exact hinv.symm

theorem act_dg_vI [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {v₀ : V}
    (hv₀ : v₀ ∈ A.Fix (Wc K I0)) {ξ : Kˣ →* Kˣ}
    (hξ : ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0), A.act (dg (cOn 0 3 c)) v = ((ξ c : Kˣ) : K) • v)
    {I : Finset (Fin 6)} (hI : I.card = 3) (d : Fin 6 → Kˣ) (hd : ∏ i, d i = 1) :
    A.act (dg d) (A.vI v₀ I) = ((ξ (∏ i ∈ I, d i) : Kˣ) : K) • A.vI v₀ I :=
  weight_I A h0 hξ hI d hd (A.vI v₀ I) (vI_mem A h0 hv₀ hI)

theorem linearIndependent_vI [CharP K 2] (h0 : finrank K (A.Fix (Wc K I0)) = 1) {v₀ : V}
    (hv₀ : v₀ ∈ A.Fix (Wc K I0)) (hv0 : v₀ ≠ 0) {ξ : Kˣ →* Kˣ}
    (hξ : ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0), A.act (dg (cOn 0 3 c)) v = ((ξ c : Kˣ) : K) • v)
    (hξ1 : ∃ c, ξ c ≠ 1) : LinearIndependent K (fun I : J3 => A.vI v₀ I.1) := by
  refine linearIndependent_of_eigen
    (fun d : {d : Fin 6 → Kˣ // ∏ i, d i = 1} => A.act (dg d.1))
    (fun I : J3 => A.vI v₀ I.1)
    (fun (I : J3) (d : {d : Fin 6 → Kˣ // ∏ i, d i = 1}) => ((ξ (∏ i ∈ I.1, d.1 i) : Kˣ) : K))
    (fun I => vI_ne_zero A h0 hv₀ hv0 I.2) ?_ ?_
  · intro I d
    exact act_dg_vI A h0 hv₀ hξ I.2 d.1 d.2
  · intro I J hIJ
    have hne : I.1 ≠ J.1 := fun h => hIJ (Subtype.ext h)
    obtain ⟨d, hd, hne'⟩ := weights_sep hξ1 I.2 J.2 hne
    exact ⟨⟨d, hd⟩, fun heq => hne' (Units.ext heq)⟩

theorem span_vI [CharP K 2] (hV : finrank K V = 20)
    (h0 : finrank K (A.Fix (Wc K I0)) = 1) {v₀ : V}
    (hv₀ : v₀ ∈ A.Fix (Wc K I0)) (hv0 : v₀ ≠ 0) {ξ : Kˣ →* Kˣ}
    (hξ : ∀ c : Kˣ, ∀ v ∈ A.Fix (Wc K I0), A.act (dg (cOn 0 3 c)) v = ((ξ c : Kˣ) : K) • v)
    (hξ1 : ∃ c, ξ c ≠ 1) : Submodule.span K (Set.range (fun I : J3 => A.vI v₀ I.1)) = ⊤ := by
  have hli : LinearIndependent K (fun I : J3 => A.vI v₀ I.1) :=
    A.linearIndependent_vI h0 hv₀ hv0 hξ hξ1
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos (by rw [hV]; norm_num)
  letI : Fintype J3 := Fintype.ofFinite J3
  apply hli.span_eq_top_of_card_eq_finrank'
  rw [← Nat.card_eq_fintype_card, card_J3, hV]

end SLAct

end CFSG.RankThree.GF2n.Smith81.S81J
