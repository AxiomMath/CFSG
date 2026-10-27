module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmGenAux_dE_apply {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 1)) :
    dE n i k = if k = i then 1 else 0 := by
  simp [dE, Pi.single_apply]

private lemma hdRo7DSmGenAux_dB_one_eq_sum {n : ℕ} (u v : DV n) :
    dB 1 u v = ∑ i : Fin (n + 1), u i * v i := by
  rw [dB, Fin.sum_univ_succ]
  simp only [one_mul]

private lemma hdRo7DSmGenAux_dB_one_dE {n : ℕ} (k : Fin (n + 1)) (v : DV n) :
    dB 1 (dE n k) v = v k := by
  rw [hdRo7DSmGenAux_dB_one_eq_sum]
  simp only [hdRo7DSmGenAux_dE_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [if_neg hb]
    simp
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma hdRo7DSmGenAux_dB_one_add {n : ℕ} (u u' v : DV n) :
    dB 1 (u + u') v = dB 1 u v + dB 1 u' v := by
  simp only [hdRo7DSmGenAux_dB_one_eq_sum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma hdRo7DSmGenAux_dB_one_sub {n : ℕ} (u u' v : DV n) :
    dB 1 (u - u') v = dB 1 u v - dB 1 u' v := by
  simp only [hdRo7DSmGenAux_dB_one_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hdRo7DSmGenAux_dB_one_sub_apply {n : ℕ} (i j : Fin (n + 1)) (v : DV n) :
    dB 1 (dE n i - dE n j) v = v i - v j := by
  rw [hdRo7DSmGenAux_dB_one_sub, hdRo7DSmGenAux_dB_one_dE, hdRo7DSmGenAux_dB_one_dE]

private lemma hdRo7DSmGenAux_dB_one_add_apply {n : ℕ} (i j : Fin (n + 1)) (v : DV n) :
    dB 1 (dE n i + dE n j) v = v i + v j := by
  rw [hdRo7DSmGenAux_dB_one_add, hdRo7DSmGenAux_dB_one_dE, hdRo7DSmGenAux_dB_one_dE]

private lemma hdRo7DSmGenAux_two_mul_two : (2 : ZMod 3) * 2 = 1 := by decide

private lemma hdRo7DSmGenAux_dB_one_sub_self {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    dB 1 (dE n i - dE n j) (dE n i - dE n j) = 2 := by
  rw [hdRo7DSmGenAux_dB_one_sub_apply]
  simp only [hdRo7DSmGenAux_dE_apply, Pi.sub_apply]
  simp [hij, Ne.symm hij]
  decide

private lemma hdRo7DSmGenAux_dB_one_add_self {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    dB 1 (dE n i + dE n j) (dE n i + dE n j) = 2 := by
  rw [hdRo7DSmGenAux_dB_one_add_apply]
  simp only [hdRo7DSmGenAux_dE_apply, Pi.add_apply]
  simp [hij, Ne.symm hij]
  decide

private lemma hdRo7DSmGenAux_ext {n : ℕ} {f g : DGL n}
    (h : ∀ k, f (dE n k) = g (dE n k)) : f = g := by
  have h' : (f : DV n →ₗ[ZMod 3] DV n) = (g : DV n →ₗ[ZMod 3] DV n) :=
    Module.Basis.ext (b := dStd n) fun i => by simpa [dStd, dE] using h i
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun (l : DV n →ₗ[ZMod 3] DV n) => l v) h'

private lemma hdRo7DSmGenAux_eq_of_dRefl {n : ℕ} {ρ : ZMod 3} {r s : DGL n} {h : DV n}
    (hr : DRefl ρ r h) (hs : DRefl ρ s h) : r = s :=
  LinearEquiv.ext fun v => by rw [hr.2 v, hs.2 v]

private lemma hdRo7DSmGenAux_dActL_dE {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) (hc : ∀ i, c i = 1 ∨ c i = -1) (k : Fin (n + 1)) :
    dActL σ c hc (dE n k) = c k • dE n (σ k) := by
  funext j
  rw [dActL_apply, dAct, Pi.smul_apply, hdRo7DSmGenAux_dE_apply,
    hdRo7DSmGenAux_dE_apply]
  by_cases h : j = σ k
  · have h' : σ.symm j = k := by rw [h, Equiv.symm_apply_apply]
    rw [if_pos h', if_pos h, h']
    simp
  · have h' : ¬ σ.symm j = k := fun hh => h (by rw [← hh, Equiv.apply_symm_apply])
    rw [if_neg h', if_neg h, smul_zero, mul_zero]

private def hdRo7DSmGenAux_pairSign {n : ℕ} (i j : Fin (n + 1)) : Fin (n + 1) → ZMod 3 :=
  fun k => if k = i ∨ k = j then -1 else 1

private lemma hdRo7DSmGenAux_pairSign_val {n : ℕ} (i j : Fin (n + 1)) :
    ∀ k, hdRo7DSmGenAux_pairSign i j k = 1 ∨ hdRo7DSmGenAux_pairSign i j k = -1 := by
  intro k
  unfold hdRo7DSmGenAux_pairSign
  split_ifs <;> simp

private lemma hdRo7DSmGenAux_pairSign_swap {n : ℕ} {i j : Fin (n + 1)}
    (k : Fin (n + 1)) :
    hdRo7DSmGenAux_pairSign i j (Equiv.swap i j k) =
      hdRo7DSmGenAux_pairSign i j k := by
  unfold hdRo7DSmGenAux_pairSign
  by_cases hki : k = i
  · rw [hki, Equiv.swap_apply_left, if_pos (Or.inr rfl), if_pos (Or.inl rfl)]
  · by_cases hkj : k = j
    · rw [hkj, Equiv.swap_apply_right, if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]

private lemma hdRo7DSmGenAux_pairSign_eq_mul {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j)
    (k : Fin (n + 1)) :
    hdRo7DSmGenAux_pairSign i j k =
      (if k = i then -1 else 1 : ZMod 3) * (if k = j then -1 else 1) := by
  unfold hdRo7DSmGenAux_pairSign
  by_cases hki : k = i
  · rw [hki, if_pos (Or.inl rfl), if_pos rfl, if_neg hij]
    ring
  · by_cases hkj : k = j
    · rw [hkj, if_pos (Or.inr rfl), if_neg (Ne.symm hij), if_pos rfl]
      ring
    · rw [if_neg (fun h => h.elim hki hkj), if_neg hki, if_neg hkj]
      ring

private lemma hdRo7DSmGenAux_dAct_sub_apply {n : ℕ} (i j : Fin (n + 1)) (v : DV n)
    (k : Fin (n + 1)) :
    dAct (Equiv.swap i j) (fun _ => 1) v k = v (Equiv.swap i j k) := by
  rw [dAct, Equiv.symm_swap]
  simp

private lemma hdRo7DSmGenAux_dAct_add_apply {n : ℕ} {i j : Fin (n + 1)}
    (v : DV n) (k : Fin (n + 1)) :
    dAct (Equiv.swap i j) (hdRo7DSmGenAux_pairSign i j) v k =
      hdRo7DSmGenAux_pairSign i j k * v (Equiv.swap i j k) := by
  rw [dAct, Equiv.symm_swap, hdRo7DSmGenAux_pairSign_swap]

private lemma hdRo7DSmGenAux_dRef_sub {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) (v : DV n) :
    dRef 1 (dE n i - dE n j) v = dAct (Equiv.swap i j) (fun _ => 1) v := by
  funext k
  rw [dRef, Pi.sub_apply, Pi.smul_apply, hdRo7DSmGenAux_dB_one_sub_self hij,
    hdRo7DSmGenAux_dB_one_sub_apply, hdRo7DSmGenAux_two_mul_two, smul_eq_mul,
    hdRo7DSmGenAux_dAct_sub_apply]
  simp only [hdRo7DSmGenAux_dE_apply, Pi.sub_apply]
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [Ne.symm hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      simp [hki, hkj]

private lemma hdRo7DSmGenAux_dRef_add {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) (v : DV n) :
    dRef 1 (dE n i + dE n j) v =
      dAct (Equiv.swap i j) (hdRo7DSmGenAux_pairSign i j) v := by
  funext k
  rw [dRef, Pi.sub_apply, Pi.smul_apply, hdRo7DSmGenAux_dB_one_add_self hij,
    hdRo7DSmGenAux_dB_one_add_apply, hdRo7DSmGenAux_two_mul_two, smul_eq_mul,
    hdRo7DSmGenAux_dAct_add_apply]
  simp only [hdRo7DSmGenAux_dE_apply, Pi.add_apply, hdRo7DSmGenAux_pairSign]
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [Ne.symm hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
      simp [hki, hkj]

private lemma hdRo7DSmGenAux_dRefl_sub {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    DRefl 1 (dActL (Equiv.swap i j) (fun _ => 1) (fun _ => Or.inl rfl))
      (dE n i - dE n j) := by
  refine ⟨?_, fun v => ?_⟩
  · rw [hdRo7DSmGenAux_dB_one_sub_self hij]
    decide
  · rw [dActL_apply]
    exact (hdRo7DSmGenAux_dRef_sub hij v).symm

private lemma hdRo7DSmGenAux_dRefl_add {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    DRefl 1 (dActL (Equiv.swap i j) (hdRo7DSmGenAux_pairSign i j)
      (hdRo7DSmGenAux_pairSign_val i j)) (dE n i + dE n j) := by
  refine ⟨?_, fun v => ?_⟩
  · rw [hdRo7DSmGenAux_dB_one_add_self hij]
    decide
  · rw [dActL_apply]
    exact (hdRo7DSmGenAux_dRef_add hij v).symm

private lemma hdRo7DSmGenAux_dActL_congr {n : ℕ} {σ σ' : Equiv.Perm (Fin (n + 1))}
    {c c' : Fin (n + 1) → ZMod 3} (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hc' : ∀ i, c' i = 1 ∨ c' i = -1) (hσ : σ = σ') (hcc : ∀ i, c i = c' i) :
    dActL σ c hc = dActL σ' c' hc' := by
  subst hσ
  apply hdRo7DSmGenAux_ext
  intro k
  rw [hdRo7DSmGenAux_dActL_dE, hdRo7DSmGenAux_dActL_dE, hcc k]

private lemma hdRo7DSmGenAux_dActL_one {n : ℕ} (c : Fin (n + 1) → ZMod 3)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (h1 : ∀ i, c i = 1) : dActL 1 c hc = 1 := by
  apply hdRo7DSmGenAux_ext
  intro k
  rw [hdRo7DSmGenAux_dActL_dE, Equiv.Perm.one_apply, h1 k, one_smul]
  rfl

private lemma hdRo7DSmGenAux_dActL_mul {n : ℕ} {σ σ' : Equiv.Perm (Fin (n + 1))}
    {c c' : Fin (n + 1) → ZMod 3} (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hc' : ∀ i, c' i = 1 ∨ c' i = -1) :
    dActL σ c hc * dActL σ' c' hc' =
      dActL (σ * σ') (fun k => c' k * c (σ' k)) (fun k => by
        rcases hc (σ' k) with h | h <;> rcases hc' k with h' | h' <;>
          simp [h, h']) := by
  apply hdRo7DSmGenAux_ext
  intro k
  simp only [LinearEquiv.mul_apply, hdRo7DSmGenAux_dActL_dE, map_smul, smul_smul,
    Equiv.Perm.mul_apply]

private lemma hdRo7DSmGenAux_dActL_inv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) (hc : ∀ i, c i = 1 ∨ c i = -1) :
    (dActL σ c hc)⁻¹ =
      dActL σ.symm (fun j => c (σ.symm j)) (fun j => hc (σ.symm j)) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [hdRo7DSmGenAux_dActL_mul]
  have hprod : ∀ k : Fin (n + 1), c (σ.symm k) * c (σ.symm k) = 1 := by
    intro k
    rcases hc (σ.symm k) with h | h <;> rw [h] <;> decide
  have hσ1 : σ * σ.symm = (1 : Equiv.Perm (Fin (n + 1))) := mul_inv_cancel σ
  rw [hdRo7DSmGenAux_dActL_congr (hc := _) (hc' := fun _ => Or.inl rfl) (hσ := hσ1)
    (hcc := fun k => hprod k)]
  exact hdRo7DSmGenAux_dActL_one (fun _ => 1) (fun _ => Or.inl rfl) (fun _ => rfl)

private lemma hdRo7DSmGenAux_dActL_decomp {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) (hc : ∀ i, c i = 1 ∨ c i = -1) :
    dActL σ c hc = dActL 1 (fun j => c (σ.symm j)) (fun j => hc (σ.symm j)) *
      dActL σ 1 (fun _ => Or.inl rfl) := by
  apply hdRo7DSmGenAux_ext
  intro k
  simp only [LinearEquiv.mul_apply, hdRo7DSmGenAux_dActL_dE,
    Equiv.Perm.one_apply, Equiv.symm_apply_apply, one_smul, Pi.one_apply]

private noncomputable def hdRo7DSmGenAux_lift {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, τ)

private lemma hdRo7DSmGenAux_lift_zero {n : ℕ} (τ : Equiv.Perm (Fin n)) :
    hdRo7DSmGenAux_lift τ 0 = 0 :=
  Equiv.Perm.decomposeFin_symm_apply_zero 0 τ

private lemma hdRo7DSmGenAux_lift_succ {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    hdRo7DSmGenAux_lift τ i.succ = (τ i).succ := by
  rw [hdRo7DSmGenAux_lift, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
  rfl

private lemma hdRo7DSmGenAux_lift_mul {n : ℕ} (τ τ' : Equiv.Perm (Fin n)) :
    hdRo7DSmGenAux_lift (τ * τ') = hdRo7DSmGenAux_lift τ * hdRo7DSmGenAux_lift τ' := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [hdRo7DSmGenAux_lift_zero, Equiv.Perm.mul_apply, hdRo7DSmGenAux_lift_zero,
      hdRo7DSmGenAux_lift_zero]
  · simp only [hdRo7DSmGenAux_lift_succ, Equiv.Perm.mul_apply]

private lemma hdRo7DSmGenAux_lift_one {n : ℕ} :
    hdRo7DSmGenAux_lift (1 : Equiv.Perm (Fin n)) = 1 := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [hdRo7DSmGenAux_lift_zero]
    rfl
  · rw [hdRo7DSmGenAux_lift_succ]
    simp

private lemma hdRo7DSmGenAux_lift_swap {n : ℕ} (a b : Fin n) :
    hdRo7DSmGenAux_lift (Equiv.swap a b) = Equiv.swap a.succ b.succ := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [hdRo7DSmGenAux_lift_zero,
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm (Fin.succ_ne_zero b).symm]
  · rw [hdRo7DSmGenAux_lift_succ]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib,
          Equiv.swap_apply_of_ne_of_ne (fun h => hia (Fin.succ_injective n h))
            (fun h => hib (Fin.succ_injective n h))]

private lemma hdRo7DSmGenAux_lift_surj {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} (hσ : σ 0 = 0) :
    ∃ τ : Equiv.Perm (Fin n), hdRo7DSmGenAux_lift τ = σ := by
  refine ⟨(Equiv.Perm.decomposeFin σ).2, ?_⟩
  have hfst : (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
    have h := Equiv.Perm.decomposeFin_symm_apply_zero (Equiv.Perm.decomposeFin σ).1
      (Equiv.Perm.decomposeFin σ).2
    rw [← Prod.eta (Equiv.Perm.decomposeFin σ),
      Equiv.Perm.decomposeFin.symm_apply_apply] at h
    exact h.symm
  have hpair : (σ 0, (Equiv.Perm.decomposeFin σ).2) = Equiv.Perm.decomposeFin σ := by
    rw [← hfst]
  have hsucc : ∀ i : Fin n,
      σ i.succ = ((Equiv.Perm.decomposeFin σ).2 i).succ := by
    intro i
    have h := Equiv.Perm.decomposeFin_symm_apply_succ (Equiv.Perm.decomposeFin σ).2 (σ 0) i
    rw [hpair, Equiv.Perm.decomposeFin.symm_apply_apply, hσ, Equiv.swap_self] at h
    simpa using h
  rw [hdRo7DSmGenAux_lift]
  have h2 : (0, (Equiv.Perm.decomposeFin σ).2) = Equiv.Perm.decomposeFin σ := by
    rw [← hσ]
    exact hpair
  rw [h2, Equiv.Perm.decomposeFin.symm_apply_apply]

private noncomputable def hdRo7DSmGenAux_permHom (n : ℕ) :
    Equiv.Perm (Fin n) →* DGL n where
  toFun τ := dActL (hdRo7DSmGenAux_lift τ) (fun _ => 1) (fun _ => Or.inl rfl)
  map_one' := by
    apply hdRo7DSmGenAux_ext
    intro k
    rw [hdRo7DSmGenAux_dActL_dE, hdRo7DSmGenAux_lift_one, Equiv.Perm.one_apply, one_smul]
    rfl
  map_mul' τ τ' := by
    apply hdRo7DSmGenAux_ext
    intro k
    simp only [LinearEquiv.mul_apply, hdRo7DSmGenAux_dActL_dE, hdRo7DSmGenAux_lift_mul,
      Equiv.Perm.mul_apply, one_smul]

private lemma hdRo7DSmGenAux_permHom_swap {n : ℕ} (a b : Fin n) :
    hdRo7DSmGenAux_permHom n (Equiv.swap a b) =
      dActL (Equiv.swap a.succ b.succ) (fun _ => 1) (fun _ => Or.inl rfl) := by
  show dActL (hdRo7DSmGenAux_lift (Equiv.swap a b)) (fun _ => 1) (fun _ => Or.inl rfl) = _
  rw [hdRo7DSmGenAux_lift_swap]

private lemma hdRo7DSmGenAux_perm_mem {n : ℕ} (hn : 2 ≤ n) (G : Subgroup (DGL n))
    (hminus : ∀ i j : Fin n, j.val = i.val + 1 → ∃ r ∈ G, DRefl 1 r (dE n i.succ - dE n j.succ)) :
    ∀ τ : Equiv.Perm (Fin n), hdRo7DSmGenAux_permHom n τ ∈ G := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro τ
  set K : Subgroup (Equiv.Perm (Fin (m + 1))) :=
    G.comap (hdRo7DSmGenAux_permHom (m + 1)) with hK
  have hgen : Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) = ⊤ :=
    Equiv.Perm.mclosure_swap_castSucc_succ m
  have hsub : (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) ⊆ K.toSubmonoid := by
    rintro σ ⟨i, rfl⟩
    obtain ⟨r, hrG, hr⟩ := hminus i.castSucc i.succ (by simp)
    have hij : (i.castSucc : Fin (m + 1)).succ ≠ (i.succ : Fin (m + 1)).succ := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at h2
      omega
    have heq : r = dActL (Equiv.swap (i.castSucc : Fin (m + 1)).succ
        (i.succ : Fin (m + 1)).succ) (fun _ => 1) (fun _ => Or.inl rfl) :=
      hdRo7DSmGenAux_eq_of_dRefl hr (hdRo7DSmGenAux_dRefl_sub hij)
    show hdRo7DSmGenAux_permHom (m + 1) (Equiv.swap i.castSucc i.succ) ∈ G
    rw [hdRo7DSmGenAux_permHom_swap]
    rw [← heq]
    exact hrG
  have htop : (⊤ : Subgroup (Equiv.Perm (Fin (m + 1)))) ≤ K := by
    intro σ _
    exact Submonoid.closure_le.mpr hsub (hgen ▸ Submonoid.mem_top σ)
  exact htop (Subgroup.mem_top τ)

private noncomputable def hdRo7DSmGenAux_sgnOf {n : ℕ} (k : Fin (n + 1)) : DGL n :=
  dActL 1 (fun i => if i = k then -1 else 1) (fun i => by by_cases h : i = k <;> simp [h])

private lemma hdRo7DSmGenAux_sgnOf_apply {n : ℕ} (i k : Fin (n + 1)) :
    hdRo7DSmGenAux_sgnOf i (dE n k) = ((if k = i then -1 else 1 : ZMod 3)) • dE n k := by
  rw [hdRo7DSmGenAux_sgnOf, hdRo7DSmGenAux_dActL_dE, Equiv.Perm.one_apply]

private lemma hdRo7DSmGenAux_sgnOf_mul {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    hdRo7DSmGenAux_sgnOf i * hdRo7DSmGenAux_sgnOf j =
      dActL 1 (hdRo7DSmGenAux_pairSign i j) (hdRo7DSmGenAux_pairSign_val i j) := by
  apply hdRo7DSmGenAux_ext
  intro k
  simp only [LinearEquiv.mul_apply, hdRo7DSmGenAux_sgnOf_apply, map_smul, smul_smul,
    hdRo7DSmGenAux_dActL_dE, Equiv.Perm.one_apply, hdRo7DSmGenAux_pairSign_eq_mul hij]
  congr 1
  ring

private lemma hdRo7DSmGenAux_pair_prod {n : ℕ} {i j : Fin (n + 1)} (hij : i ≠ j) :
    dActL (Equiv.swap i j) (hdRo7DSmGenAux_pairSign i j) (hdRo7DSmGenAux_pairSign_val i j) *
      dActL (Equiv.swap i j) (fun _ => 1) (fun _ => Or.inl rfl) =
      hdRo7DSmGenAux_sgnOf i * hdRo7DSmGenAux_sgnOf j := by
  rw [hdRo7DSmGenAux_dActL_mul]
  rw [hdRo7DSmGenAux_dActL_congr (hc := _) (hc' := _)
    (hσ := Equiv.swap_mul_self i j)
    (hcc := fun k => by rw [one_mul, hdRo7DSmGenAux_pairSign_swap])]
  exact (hdRo7DSmGenAux_sgnOf_mul hij).symm

private lemma hdRo7DSmGenAux_conj_sgn {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (a : Fin (n + 1)) :
    dActL σ (fun _ => 1) (fun _ => Or.inl rfl) * hdRo7DSmGenAux_sgnOf a *
      (dActL σ (fun _ => 1) (fun _ => Or.inl rfl))⁻¹ =
      hdRo7DSmGenAux_sgnOf (σ a) := by
  rw [hdRo7DSmGenAux_dActL_inv]
  apply hdRo7DSmGenAux_ext
  intro k
  simp only [LinearEquiv.mul_apply, hdRo7DSmGenAux_sgnOf_apply, hdRo7DSmGenAux_dActL_dE,
    one_smul, map_smul, Equiv.apply_symm_apply]
  congr 1
  have hiff : σ.symm k = a ↔ k = σ a := Equiv.symm_apply_eq σ
  by_cases h : k = σ a
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

private lemma hdRo7DSmGenAux_exists_perm_pair {m : ℕ} (a b x y : Fin m)
    (hab : a ≠ b) (hxy : x ≠ y) : ∃ σ : Equiv.Perm (Fin m), σ a = x ∧ σ b = y := by
  by_cases hxa : x = a
  · have hay : a ≠ y := fun h => hxy (by rw [hxa, h])
    refine ⟨Equiv.swap b y, ?_, ?_⟩
    · rw [hxa, Equiv.swap_apply_of_ne_of_ne hab hay]
    · exact Equiv.swap_apply_left b y
  · refine ⟨Equiv.swap (Equiv.swap a x b) y * Equiv.swap a x, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      refine Equiv.swap_apply_of_ne_of_ne ?_ hxy
      by_cases hxb : x = b
      · rw [hxb, Equiv.swap_apply_right]
        exact Ne.symm hab
      · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hxb)]
        exact hxb
    · rw [Equiv.Perm.mul_apply]
      exact Equiv.swap_apply_left _ _

private lemma hdRo7DSmGenAux_conj_pair {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (a b : Fin (n + 1)) :
    dActL σ (fun _ => 1) (fun _ => Or.inl rfl) *
        (hdRo7DSmGenAux_sgnOf a * hdRo7DSmGenAux_sgnOf b) *
        (dActL σ (fun _ => 1) (fun _ => Or.inl rfl))⁻¹ =
      hdRo7DSmGenAux_sgnOf (σ a) * hdRo7DSmGenAux_sgnOf (σ b) := by
  rw [show dActL σ (fun _ => 1) (fun _ => Or.inl rfl) *
        (hdRo7DSmGenAux_sgnOf a * hdRo7DSmGenAux_sgnOf b) *
        (dActL σ (fun _ => 1) (fun _ => Or.inl rfl))⁻¹ =
      (dActL σ (fun _ => 1) (fun _ => Or.inl rfl) * hdRo7DSmGenAux_sgnOf a *
        (dActL σ (fun _ => 1) (fun _ => Or.inl rfl))⁻¹) *
      (dActL σ (fun _ => 1) (fun _ => Or.inl rfl) * hdRo7DSmGenAux_sgnOf b *
        (dActL σ (fun _ => 1) (fun _ => Or.inl rfl))⁻¹) from by group]
  rw [hdRo7DSmGenAux_conj_sgn, hdRo7DSmGenAux_conj_sgn]

private lemma hdRo7DSmGenAux_pair_mem {n : ℕ} (hn : 2 ≤ n) (G : Subgroup (DGL n))
    (hminus : ∀ i j : Fin n, j.val = i.val + 1 → ∃ r ∈ G, DRefl 1 r (dE n i.succ - dE n j.succ))
    (hplus : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ r ∈ G, DRefl 1 r (dE n i.succ + dE n j.succ)) :
    ∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 → a ≠ b →
      hdRo7DSmGenAux_sgnOf a * hdRo7DSmGenAux_sgnOf b ∈ G := by
  intro a b ha0 hb0 hab
  have hbase : hdRo7DSmGenAux_sgnOf ((⟨n - 2, by omega⟩ : Fin n).succ) *
      hdRo7DSmGenAux_sgnOf ((⟨n - 1, by omega⟩ : Fin n).succ) ∈ G := by
    obtain ⟨r, hrG, hr⟩ := hminus (⟨n - 2, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
      (by simp only; omega)
    obtain ⟨s, hsG, hs⟩ := hplus (⟨n - 2, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
      (by simp only; omega) (by simp only; omega)
    have hij : (⟨n - 2, by omega⟩ : Fin n).succ ≠ (⟨n - 1, by omega⟩ : Fin n).succ := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.val_succ] at h2
      omega
    have hr' : r = dActL (Equiv.swap ((⟨n - 2, by omega⟩ : Fin n).succ)
        ((⟨n - 1, by omega⟩ : Fin n).succ)) (fun _ => 1) (fun _ => Or.inl rfl) :=
      hdRo7DSmGenAux_eq_of_dRefl hr (hdRo7DSmGenAux_dRefl_sub hij)
    have hs' : s = dActL (Equiv.swap ((⟨n - 2, by omega⟩ : Fin n).succ)
        ((⟨n - 1, by omega⟩ : Fin n).succ))
        (hdRo7DSmGenAux_pairSign _ _) (hdRo7DSmGenAux_pairSign_val _ _) :=
      hdRo7DSmGenAux_eq_of_dRefl hs (hdRo7DSmGenAux_dRefl_add hij)
    rw [← hdRo7DSmGenAux_pair_prod hij]
    rw [← hs', ← hr']
    exact Subgroup.mul_mem _ hsG hrG
  obtain ⟨τ, hτa, hτb⟩ := hdRo7DSmGenAux_exists_perm_pair
    (⟨n - 2, by omega⟩ : Fin n) (⟨n - 1, by omega⟩ : Fin n)
    (Fin.pred a ha0) (Fin.pred b hb0) (by
      intro h
      have h2 := congrArg Fin.val h
      simp only at h2
      omega) (by
      have h := Fin.succ_pred a ha0
      have h2 := Fin.succ_pred b hb0
      intro hh
      apply hab
      rw [← h, ← h2, hh])
  have hPa : hdRo7DSmGenAux_lift τ ((⟨n - 2, by omega⟩ : Fin n).succ) = a := by
    rw [hdRo7DSmGenAux_lift_succ, hτa, Fin.succ_pred]
  have hPb : hdRo7DSmGenAux_lift τ ((⟨n - 1, by omega⟩ : Fin n).succ) = b := by
    rw [hdRo7DSmGenAux_lift_succ, hτb, Fin.succ_pred]
  have hP : dActL (hdRo7DSmGenAux_lift τ) (fun _ => 1) (fun _ => Or.inl rfl) ∈ G :=
    hdRo7DSmGenAux_perm_mem hn G hminus τ
  have hconj := hdRo7DSmGenAux_conj_pair (hdRo7DSmGenAux_lift τ)
    ((⟨n - 2, by omega⟩ : Fin n).succ) ((⟨n - 1, by omega⟩ : Fin n).succ)
  rw [hPa, hPb] at hconj
  rw [← hconj]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hP hbase) (Subgroup.inv_mem _ hP)

private lemma hdRo7DSmGenAux_list_prod_sign {n : ℕ} (l : List (Fin (n + 1)))
    (hnd : l.Nodup) (k : Fin (n + 1)) :
    (l.map (fun i => ((if k = i then -1 else 1 : ZMod 3)))).prod =
      (if k ∈ l then -1 else 1) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have hnot : i ∉ l := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, List.prod_cons, ih hnd']
    by_cases hki : k = i
    · rw [hki, if_pos rfl, if_neg hnot, if_pos (List.mem_cons_self)]
      ring
    · rw [if_neg hki]
      by_cases hmem : k ∈ l
      · rw [if_pos hmem, if_pos (List.mem_cons_of_mem i hmem)]
        ring
      · rw [if_neg hmem, if_neg (fun h => by
            rcases List.mem_cons.mp h with h' | h'
            · exact hki h'
            · exact hmem h')]
        ring

private lemma hdRo7DSmGenAux_list_prod_signPair_apply {n : ℕ} (l : List (Fin (n + 1)))
    (i0 k : Fin (n + 1)) :
    (l.map (fun j => hdRo7DSmGenAux_sgnOf i0 * hdRo7DSmGenAux_sgnOf j)).prod (dE n k) =
      (l.map (fun j => ((if k = i0 then -1 else 1 : ZMod 3) *
        (if k = j then -1 else 1)))).prod • dE n k := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, map_smul,
      hdRo7DSmGenAux_sgnOf_apply, smul_smul]
    congr 1
    ring

private lemma hdRo7DSmGenAux_list_prod_signPair_scalar_aux {n : ℕ}
    (l : List (Fin (n + 1))) (i0 k : Fin (n + 1)) :
    (l.map (fun j => ((if k = i0 then -1 else 1 : ZMod 3) *
      (if k = j then -1 else 1)))).prod =
      (if k = i0 then -1 else 1 : ZMod 3) ^ l.length *
        (l.map (fun j => ((if k = j then -1 else 1 : ZMod 3)))).prod := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]
    ring

private lemma hdRo7DSmGenAux_list_prod_signPair_scalar {n : ℕ} (l : List (Fin (n + 1)))
    (i0 k : Fin (n + 1)) (hnd : l.Nodup) (hi0 : i0 ∉ l) :
    (l.map (fun j => ((if k = i0 then -1 else 1 : ZMod 3) *
      (if k = j then -1 else 1)))).prod =
      (if k = i0 then (-1 : ZMod 3) ^ l.length else (if k ∈ l then -1 else 1)) := by
  rw [hdRo7DSmGenAux_list_prod_signPair_scalar_aux, hdRo7DSmGenAux_list_prod_sign l hnd k]
  by_cases hk : k = i0
  · rw [hk]
    simp [hi0]
  · simp [hk]

private lemma hdRo7DSmGenAux_list_prod_signPair_mem {n : ℕ} (G : Subgroup (DGL n))
    (l : List (Fin (n + 1))) (i0 : Fin (n + 1)) (hi0 : i0 ∉ l)
    (hpair : ∀ j, j ∈ l → hdRo7DSmGenAux_sgnOf i0 * hdRo7DSmGenAux_sgnOf j ∈ G) :
    (l.map (fun j => hdRo7DSmGenAux_sgnOf i0 * hdRo7DSmGenAux_sgnOf j)).prod ∈ G := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Subgroup.mul_mem _ (hpair j (List.mem_cons_self))
      (ih (fun h => hi0 (List.mem_cons_of_mem j h))
        (fun x hx => hpair x (List.mem_cons_of_mem j hx)))

private lemma hdRo7DSmGenAux_even_card_of_prod {n : ℕ} (c : Fin (n + 1) → ZMod 3)
    (hc : ∀ i, c i = 1 ∨ c i = -1) (hprod : ∏ i, c i = 1) :
    Even (Finset.univ.filter (fun i => c i = -1)).card := by
  let s := Finset.univ.filter (fun i => c i = -1)
  have h1 : (∏ i, c i) = (-1 : ZMod 3) ^ s.card := by
    have hc' : (∏ i, c i) = ∏ i, (if c i = -1 then (-1 : ZMod 3) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      rcases hc i with h | h <;> simp [h]
    rw [hc']
    rw [← Finset.prod_filter (s := Finset.univ) (f := fun _ => (-1 : ZMod 3))
      (p := fun i => c i = -1), Finset.prod_const]
  have h2 : (-1 : ZMod 3) ^ s.card = 1 := by rw [← h1, hprod]
  rcases Nat.even_or_odd s.card with he | ho
  · exact he
  · exfalso
    rw [Odd.neg_one_pow ho] at h2
    exact (by decide : (-1 : ZMod 3) ≠ 1) h2

private lemma hdRo7DSmGenAux_diag_mem {n : ℕ} (G : Subgroup (DGL n)) (i0 : Fin (n + 1))
    (hi0 : i0 ≠ 0)
    (hpair : ∀ a b : Fin (n + 1), a ≠ 0 → b ≠ 0 → a ≠ b →
      hdRo7DSmGenAux_sgnOf a * hdRo7DSmGenAux_sgnOf b ∈ G)
    {c : Fin (n + 1) → ZMod 3} (h0 : c 0 = 1) (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hprod : ∏ i, c i = 1) : dActL 1 c hc ∈ G := by
  classical
  let s := Finset.univ.filter (fun k => c k = -1)
  have heven : Even s.card := hdRo7DSmGenAux_even_card_of_prod c hc hprod
  have hmem : ∀ i, i ∈ s ↔ c i = -1 := by
    intro i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
  have h0s : (0 : Fin (n + 1)) ∉ s := by
    rw [hmem, h0]
    decide
  let l := (s.erase i0).toList
  have hnd : l.Nodup := Finset.nodup_toList _
  have hi0l : i0 ∉ l := by
    rw [show l = (s.erase i0).toList from rfl, Finset.mem_toList]
    exact Finset.notMem_erase i0 s
  have hmeml : ∀ k, k ∈ l ↔ c k = -1 ∧ k ≠ i0 := by
    intro k
    rw [show l = (s.erase i0).toList from rfl, Finset.mem_toList, Finset.mem_erase, hmem k]
    constructor
    · exact fun h => ⟨h.2, h.1⟩
    · exact fun h => ⟨h.2, h.1⟩
  have hDmem : (l.map (fun j => hdRo7DSmGenAux_sgnOf i0 *
      hdRo7DSmGenAux_sgnOf j)).prod ∈ G := by
    refine hdRo7DSmGenAux_list_prod_signPair_mem G l i0 hi0l (fun j hj => ?_)
    have hj' := (hmeml j).mp hj
    exact hpair i0 j hi0 (by
      intro hj0
      have := hj'.1
      rw [hj0, h0] at this
      exact absurd this (by decide)) (Ne.symm hj'.2)
  have happly : ∀ k : Fin (n + 1),
      (l.map (fun j => hdRo7DSmGenAux_sgnOf i0 * hdRo7DSmGenAux_sgnOf j)).prod (dE n k) =
        c k • dE n k := by
    intro k
    rw [hdRo7DSmGenAux_list_prod_signPair_apply l i0 k,
      hdRo7DSmGenAux_list_prod_signPair_scalar l i0 k hnd hi0l]
    by_cases hk : k = i0
    · rw [hk, if_pos rfl]
      congr 1
      show (-1 : ZMod 3) ^ l.length = c i0
      rw [show l.length = (s.erase i0).card from Finset.length_toList _]
      by_cases his : i0 ∈ s
      · rw [Finset.card_erase_of_mem his]
        have hodd : Odd (s.card - 1) := by
          obtain ⟨r, hr⟩ := heven
          have hpos : 0 < s.card := Finset.card_pos.mpr ⟨i0, his⟩
          exact ⟨r - 1, by omega⟩
        rw [Odd.neg_one_pow hodd]
        exact ((hmem i0).mp his).symm
      · rw [show (s.erase i0).card = s.card from by rw [Finset.erase_eq_of_notMem his],
          Even.neg_one_pow heven]
        rcases hc i0 with h | h
        · exact h.symm
        · exfalso
          exact his ((hmem i0).mpr h)
    · rw [if_neg hk]
      congr 1
      by_cases hkl : k ∈ l
      · rw [if_pos hkl, ((hmeml k).mp hkl).1]
      · rw [if_neg hkl]
        have hck : c k = 1 := by
          rcases hc k with h | h
          · exact h
          · exfalso
            exact hkl ((hmeml k).mpr ⟨h, hk⟩)
        rw [hck]
  have hdecomp : dActL 1 c hc = (l.map (fun j => hdRo7DSmGenAux_sgnOf i0 *
      hdRo7DSmGenAux_sgnOf j)).prod := by
    apply hdRo7DSmGenAux_ext
    intro k
    rw [happly k, hdRo7DSmGenAux_dActL_dE, Equiv.Perm.one_apply]
  rw [hdecomp]
  exact hDmem

theorem dSmGen_holds : DSmGenLeaf := by
  intro n hn G hminus hplus a ha
  obtain ⟨σ, c, hσ0, hc0, hc, hprod, hact⟩ := ha
  have ha_eq : a = dActL σ c hc := by
    apply hdRo7DSmGenAux_ext
    intro k
    have h1 : dStd n k = dE n k := by simp [dStd, dE]
    have h2 : dStd n (σ k) = dE n (σ k) := by simp [dStd, dE]
    rw [← h1, hact k, h1, hdRo7DSmGenAux_dActL_dE, ← h2]
  rw [ha_eq, hdRo7DSmGenAux_dActL_decomp σ c hc]
  obtain ⟨τ, hτ⟩ := hdRo7DSmGenAux_lift_surj hσ0
  have hP : dActL σ (1 : Fin (n + 1) → ZMod 3) (fun _ => Or.inl rfl) =
      hdRo7DSmGenAux_permHom n τ := by
    rw [← hτ]
    rfl
  rw [hP]
  refine Subgroup.mul_mem _ ?_ (hdRo7DSmGenAux_perm_mem hn G hminus τ)
  have h0' : c (σ.symm 0) = 1 := by
    have hs0 : σ.symm 0 = 0 := by
      rw [Equiv.symm_apply_eq]
      exact hσ0.symm
    rw [hs0, hc0]
  have hprod' : ∏ j, c (σ.symm j) = 1 := by
    rw [Equiv.prod_comp σ.symm c]
    exact hprod
  exact hdRo7DSmGenAux_diag_mem G (⟨1, by omega⟩ : Fin (n + 1)) (by simp)
    (hdRo7DSmGenAux_pair_mem hn G hminus hplus) h0' (fun j => hc (σ.symm j)) hprod'

end CFSG.StandardType.HdRo7D.Small
