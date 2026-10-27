module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAPerm

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
theorem hdRo7SmAsmAux_basis {m : ℕ} (v : SMV m) :
    v = ∑ i, (v i) • (Pi.single i (1 : ZMod 3) : SMV m) := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne' hb, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj
theorem hdRo7SmAsmAux_dual_eq {m : ℕ} (φ : Module.Dual (ZMod 3) (SMV m)) :
    smDual (fun i => φ (Pi.single i (1 : ZMod 3))) = φ := by
  apply LinearMap.ext
  intro v
  rw [hdRo7SmAAux_smDual_apply, smDot]
  conv_rhs => rw [hdRo7SmAsmAux_basis v, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul]
  ring
theorem hdRo7SmAsmAux_smDual_smul {m : ℕ} (c : ZMod 3) (w : SMV m) :
    smDual (c • w) = c • smDual w := by
  apply LinearMap.ext
  intro v
  rw [hdRo7SmAAux_smDual_apply, LinearMap.smul_apply, smul_eq_mul, hdRo7SmAAux_smDual_apply]
  simp only [smDot, Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem hdRo7SmAsmAux_refl_unique {m : ℕ} {r r' : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (h : SMRefl r u φ) (h' : SMRefl r' u φ) : r = r' := by
  apply LinearEquiv.ext
  intro v
  rw [h.2 v, h'.2 v]
theorem hdRo7SmAsmAux_smDot_smul {m : ℕ} (c : ZMod 3) (w u : SMV m) :
    smDot (c • w) (c • u) = (c * c) * smDot w u := by
  simp only [smDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem hdRo7SmAsmAux_smul_smul {m : ℕ} {c : ZMod 3} (hcc : c * c = 1) (w u v : SMV m) :
    smDual (c • w) v • (c • u) = smDual w v • u := by
  rw [hdRo7SmAsmAux_smDual_smul, LinearMap.smul_apply, smul_eq_mul]
  simp only [smul_smul]
  have hc : (c * (smDual w) v) * c = smDual w v := by
    rw [mul_assoc, mul_comm (smDual w v) c, ← mul_assoc, hcc, one_mul]
  rw [hc]
theorem hdRo7SmAsmAux_smRefl_scale {m : ℕ} {r : SMGL m} {u w : SMV m} {c : ZMod 3}
    (hc : c = 1 ∨ c = -1) :
    SMRefl r (c • u) (smDual (c • w)) ↔ SMRefl r u (smDual w) := by
  have hcc : c * c = 1 := by rcases hc with rfl | rfl <;> decide
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := h.1
      rw [hdRo7SmAAux_smDual_apply, hdRo7SmAsmAux_smDot_smul, hcc, one_mul] at h1
      rwa [hdRo7SmAAux_smDual_apply]
    · intro v
      have h2 := h.2 v
      rw [hdRo7SmAsmAux_smul_smul hcc w u v] at h2
      exact h2
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := h.1
      rw [hdRo7SmAAux_smDual_apply] at h1
      rw [hdRo7SmAAux_smDual_apply, hdRo7SmAsmAux_smDot_smul, hcc, one_mul]
      exact h1
    · intro v
      have h2 := h.2 v
      rw [hdRo7SmAsmAux_smul_smul hcc w u v]
      exact h2
theorem hdRo7SmAsmAux_smDot_comp {m : ℕ} (σ : Equiv.Perm (Fin m)) (b a : SMV m) :
    smDot (fun i => b (σ i)) (fun i => a (σ i)) = smDot b a := by
  simp only [smDot]
  exact Equiv.sum_comp σ (fun j => b j * a j)
theorem hdRo7SmAsmAux_smDual_permLin_symm {m : ℕ} (σ : Equiv.Perm (Fin m)) (b : SMV m) (v : SMV m) :
    smDual b ((hdRo7SmAAux_permLin m σ)⁻¹ v) = smDual (fun i => b (σ.symm i)) v := by
  have hS : (hdRo7SmAAux_permLin m σ)⁻¹ v = fun i => v (σ i) := by
    funext i
    rw [← map_inv]
    exact hdRo7SmAAux_permLin_apply σ⁻¹ v i
  rw [hS, hdRo7SmAAux_smDual_apply, hdRo7SmAAux_smDual_apply, smDot, smDot]
  simpa using Equiv.sum_comp σ (fun i => b (σ.symm i) * v i)
theorem hdRo7SmAsmAux_permLin_conj_refl {m : ℕ} (σ : Equiv.Perm (Fin m)) {r : SMGL m} {a b : SMV m}
    (h : SMRefl r a (smDual b)) :
    SMRefl (hdRo7SmAAux_permLin m σ * r * (hdRo7SmAAux_permLin m σ)⁻¹)
      (fun i => a (σ.symm i)) (smDual (fun i => b (σ.symm i))) := by
  rcases h with ⟨h1, h2⟩
  rw [hdRo7SmAAux_smDual_apply] at h1
  refine ⟨?_, ?_⟩
  · rw [hdRo7SmAAux_smDual_apply, hdRo7SmAsmAux_smDot_comp σ.symm b a]
    exact h1
  · intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h2 ((hdRo7SmAAux_permLin m σ)⁻¹ v)]
    rw [map_sub, map_smul]
    have hTS : hdRo7SmAAux_permLin m σ ((hdRo7SmAAux_permLin m σ)⁻¹ v) = v :=
      LinearEquiv.apply_symm_apply _ _
    have hTa : hdRo7SmAAux_permLin m σ a = fun i => a (σ.symm i) := by
      funext i; exact hdRo7SmAAux_permLin_apply σ a i
    rw [hTS, hTa, hdRo7SmAsmAux_smDual_permLin_symm]
theorem hdRo7SmAsmAux_transp_isPerm {m : ℕ} {p : SMV m × SMV m} (hp : SMTClass p) {r : SMGL m}
    (h : SMRefl r p.1 (smDual p.2)) : SMIsPerm r := by
  obtain ⟨i, j, s, hij, hs, h1, h2⟩ := hp
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> decide
  set w : SMV m := Pi.single i (1 : ZMod 3) - Pi.single j 1 with hw
  refine ⟨Equiv.swap i j, ?_⟩
  intro v k
  rw [h.2 v]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  rw [hdRo7SmAsmAux_smDual_smul, LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
  have hd : smDual w v = v i - v j := hdRo7SmAAux_smDual_diff i j v
  rw [hd]
  have hassoc : (s * (v i - v j)) * (s * w k) = (v i - v j) * (w k) := by
    rw [← mul_assoc, mul_assoc s (v i - v j) s, mul_comm (v i - v j) s, ← mul_assoc,
      hss, one_mul]
  rw [hassoc]
  have hwk : w k = (Pi.single i (1 : ZMod 3) - Pi.single j 1 : SMV m) k := by rw [hw]
  rw [hwk]
  by_cases hki : k = i
  · subst hki
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
    simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, sub_zero, mul_one]
    ring
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.symm_swap, Equiv.swap_apply_right]
      simp only [Pi.sub_apply, Pi.single_eq_of_ne' hij, Pi.single_eq_same, zero_sub, mul_neg,
        mul_one]
      ring
    · rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hkj]
      simp only [Pi.sub_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, sub_zero,
        mul_zero, sub_zero]
theorem hdRo7SmAsmAux_class_conj {m : ℕ} {r r' : SMGL m} {u w q1 q2 : SMV m}
    (h : SMRefl r u (smDual w)) (h' : SMRefl r' q1 (smDual q2))
    (hc : SMClass (u, w) (q1, q2)) :
    ∃ σ : Equiv.Perm (Fin m), r = hdRo7SmAAux_permLin m σ * r' * (hdRo7SmAAux_permLin m σ)⁻¹ := by
  obtain ⟨π, c, hcs, hcomp⟩ := hc
  refine ⟨π.symm, ?_⟩
  have hconj : SMRefl (hdRo7SmAAux_permLin m π.symm * r' * (hdRo7SmAAux_permLin m π.symm)⁻¹)
      (fun i => q1 (π i)) (smDual (fun i => q2 (π i))) :=
    hdRo7SmAsmAux_permLin_conj_refl π.symm h'
  have hscaled := (hdRo7SmAsmAux_smRefl_scale (r := hdRo7SmAAux_permLin m π.symm * r' *
      (hdRo7SmAAux_permLin m π.symm)⁻¹) (u := fun i => q1 (π i))
      (w := fun i => q2 (π i)) hcs).mpr hconj
  have hu : u = c • (fun i => q1 (π i)) := by funext i; exact (hcomp i).1
  have hw : w = c • (fun i => q2 (π i)) := by funext i; exact (hcomp i).2
  rw [hu, hw] at h
  exact hdRo7SmAsmAux_refl_unique h hscaled
theorem hdRo7SmAsmAux_eq_smGroup {m : ℕ} {H : Subgroup (SMGL m)} {X : List (SMV m × SMV m)}
    (hP : ∀ g, SMIsPerm g → g ∈ H)
    (hXeq : ∀ p, p ∈ smRefSet H ↔ (SMTClass p ∨ ∃ q ∈ X, SMClass p q))
    {S : Set (SMGL m)} (hS_eq : H = Subgroup.closure S)
    (hS_refl : ∀ r ∈ S, ∃ u φ, SMRefl r u φ) :
    H = smGroup m X := by
  apply le_antisymm
  · rw [hS_eq]
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨u, φ, hrefl⟩ := hS_refl s hs
    set w : SMV m := fun i => φ (Pi.single i (1 : ZMod 3)) with hwdef
    have hφ : smDual w = φ := hdRo7SmAsmAux_dual_eq φ
    have hrefl' : SMRefl s u (smDual w) := by rw [hφ]; exact hrefl
    have hsH : s ∈ H := by rw [hS_eq]; exact Subgroup.subset_closure hs
    have hpR : (u, w) ∈ smRefSet H := ⟨s, hsH, hrefl'⟩
    have hclass := (hXeq (u, w)).mp hpR
    rw [smGroup]
    rcases hclass with hT | ⟨q, hqX, hqclass⟩
    · exact Subgroup.subset_closure (Or.inl (hdRo7SmAsmAux_transp_isPerm hT hrefl'))
    · have hqR : q ∈ smRefSet H := by
        rw [hXeq q]
        exact Or.inr ⟨q, hqX, ⟨1, 1, Or.inl rfl, by intro i; simp⟩⟩
      obtain ⟨r', hr'H, hr'refl⟩ := hqR
      have hr'mem : r' ∈ smGroup m X := by
        rw [smGroup]
        exact Subgroup.subset_closure (Or.inr ⟨q, hqX, hr'refl⟩)
      obtain ⟨σ, hσeq⟩ := hdRo7SmAsmAux_class_conj hrefl' hr'refl hqclass
      have hperm : hdRo7SmAAux_permLin m σ ∈ smGroup m X := by
        rw [smGroup]
        exact Subgroup.subset_closure (Or.inl (hdRo7SmAAux_isPerm_permLin σ))
      rw [hσeq]
      exact Subgroup.mul_mem (smGroup m X) (Subgroup.mul_mem (smGroup m X) hperm hr'mem) ((smGroup m X).inv_mem hperm)
  · rw [smGroup]
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with hg | hg
    · exact hP g hg
    · obtain ⟨q, hqX, hqrefl⟩ := hg
      have hqR : q ∈ smRefSet H := by
        rw [hXeq q]
        exact Or.inr ⟨q, hqX, ⟨1, 1, Or.inl rfl, by intro i; simp⟩⟩
      obtain ⟨r, hrH, hrrefl⟩ := hqR
      rw [hdRo7SmAsmAux_refl_unique hqrefl hrrefl]
      exact hrH
theorem hdRo7SmAsmAux_refl_invol {m : ℕ} {r : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (h : SMRefl r u φ) : r * r = 1 := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, h.2 (r v), h.2 v, map_sub, map_smul, h.1]
  change v - φ v • u - (φ v - φ v • 2) • u = v
  rw [smul_eq_mul]
  have hscal : (φ v - φ v * 2 : ZMod 3) = -(φ v) := by ring_nf
  rw [hscal]
  simp only [neg_smul]
  abel
theorem hdRo7SmAsmAux_singleton_closure {G : Type*} [Group G] (a : G) (ha : a * a = 1) {g : G}
    (hg : g ∈ Subgroup.closure ({a} : Set G)) : g = 1 ∨ g = a := by
  rw [Subgroup.mem_closure_singleton] at hg
  obtain ⟨n, rfl⟩ := hg
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [hk, show k + k = (2 : ℤ) * k by ring, zpow_mul, zpow_two, ha, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, zpow_two, ha, one_zpow, one_mul, zpow_one]
theorem hdRo7SmAsmAux_cx7_snd : sm7cx.2 = (fun _ => (1 : ZMod 3)) := by
  funext i; fin_cases i <;> rfl
theorem hdRo7SmAsmAux_cx7_fst : sm7cx.1 = (2 : ZMod 3) • (fun _ => (1 : ZMod 3)) := by
  funext i; fin_cases i <;> rfl
theorem hdRo7SmAsmAux_cx7_fst_apply (j : Fin 7) : sm7cx.1 j = (2 : ZMod 3) := by
  fin_cases j <;> rfl
theorem hdRo7SmAsmAux_cx7_snd_apply (j : Fin 7) : sm7cx.2 j = (1 : ZMod 3) := by
  fin_cases j <;> rfl
theorem hdRo7SmAsmAux_cx7_smDual (v : SMV 7) : smDual sm7cx.2 v = ∑ i, v i := by
  rw [hdRo7SmAsmAux_cx7_snd, hdRo7SmAAux_smDual_apply]
  simp [smDot]
theorem hdRo7SmAsmAux_cx7_refl_form {s : SMGL 7} (h : SMRefl s sm7cx.1 (smDual sm7cx.2)) (v : SMV 7) :
    s v = v + (∑ i, v i) • (fun _ => (1 : ZMod 3)) := by
  rw [h.2 v, hdRo7SmAsmAux_cx7_smDual, hdRo7SmAsmAux_cx7_fst]
  rw [smul_smul]
  have htwo : (2 : ZMod 3) = -1 := by decide
  rw [show (∑ i, v i) * 2 = -(∑ i, v i) by rw [htwo, mul_neg, mul_one]]
  simp only [neg_smul]
  abel
theorem hdRo7SmAsmAux_permLin_sum {m : ℕ} (σ : Equiv.Perm (Fin m)) (v : SMV m) :
    ∑ i, (hdRo7SmAAux_permLin m σ v) i = ∑ i, v i := by
  simp only [hdRo7SmAAux_permLin_apply]
  exact Equiv.sum_comp σ.symm v
theorem hdRo7SmAsmAux_permLin_ones {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    hdRo7SmAAux_permLin m σ (fun _ => (1 : ZMod 3)) = fun _ => (1 : ZMod 3) := by
  funext i; simp [hdRo7SmAAux_permLin_apply]
theorem hdRo7SmAsmAux_cx7_comm_perm {s : SMGL 7} (h : SMRefl s sm7cx.1 (smDual sm7cx.2))
    (σ : Equiv.Perm (Fin 7)) : Commute s (hdRo7SmAAux_permLin 7 σ) := by
  apply LinearEquiv.ext
  intro v
  ext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hdRo7SmAsmAux_cx7_refl_form h (hdRo7SmAAux_permLin 7 σ v), hdRo7SmAsmAux_cx7_refl_form h v]
  rw [map_add, map_smul, hdRo7SmAsmAux_permLin_sum σ v, hdRo7SmAsmAux_permLin_ones]
theorem hdRo7SmAsmAux_cx7_not_perm {s : SMGL 7} (h : SMRefl s sm7cx.1 (smDual sm7cx.2)) :
    ¬ SMIsPerm s := by
  rintro ⟨σ, hσ⟩
  have e0 := hσ (Pi.single 0 (1 : ZMod 3)) 0
  rw [hdRo7SmAsmAux_cx7_refl_form h] at e0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, Finset.sum_apply,
    Pi.single_eq_same, Finset.sum_eq_single] at e0
  rcases eq_or_ne (σ.symm 0) 0 with h0 | h0
  · rw [h0, Pi.single_eq_same] at e0
    exact (by decide : ¬ ((2 : ZMod 3) = 1)) e0
  · rw [Pi.single_eq_of_ne h0] at e0
    exact (by decide : ¬ ((2 : ZMod 3) = 0)) e0
theorem hdRo7SmAsmAux_cx7_class_refl {s : SMGL 7} {u w : SMV 7}
    (h : SMRefl s u (smDual w)) (hc : SMClass (u, w) sm7cx) :
    SMRefl s sm7cx.1 (smDual sm7cx.2) := by
  obtain ⟨π, c, hcs, hcomp⟩ := hc
  have hu : u = c • sm7cx.1 := by
    funext i
    rw [show u i = c * sm7cx.1 (π i) from (hcomp i).1, Pi.smul_apply,
      hdRo7SmAsmAux_cx7_fst_apply (π i), hdRo7SmAsmAux_cx7_fst_apply i, smul_eq_mul]
  have hw : w = c • sm7cx.2 := by
    funext i
    rw [show w i = c * sm7cx.2 (π i) from (hcomp i).2, Pi.smul_apply,
      hdRo7SmAsmAux_cx7_snd_apply (π i), hdRo7SmAsmAux_cx7_snd_apply i, smul_eq_mul]
  rw [hu, hw] at h
  exact (hdRo7SmAsmAux_smRefl_scale (r := s) (u := sm7cx.1) (w := sm7cx.2) hcs).mp h
theorem hdRo7SmAsmAux_cx8_fst_apply (j : Fin 8) : sm8cx.1 j = (1 : ZMod 3) := by
  fin_cases j <;> rfl
theorem hdRo7SmAsmAux_cx8_snd_apply (j : Fin 8) : sm8cx.2 j = (1 : ZMod 3) := by
  fin_cases j <;> rfl
theorem hdRo7SmAsmAux_cx8_snd : sm8cx.2 = (fun _ => (1 : ZMod 3)) := by
  funext i; exact hdRo7SmAsmAux_cx8_snd_apply i
theorem hdRo7SmAsmAux_cx8_fst : sm8cx.1 = (fun _ => (1 : ZMod 3)) := by
  funext i; exact hdRo7SmAsmAux_cx8_fst_apply i
theorem hdRo7SmAsmAux_cx8_smDual (v : SMV 8) : smDual sm8cx.2 v = ∑ i, v i := by
  rw [hdRo7SmAsmAux_cx8_snd, hdRo7SmAAux_smDual_apply]
  simp [smDot]
theorem hdRo7SmAsmAux_cx8_refl_form {s : SMGL 8} (h : SMRefl s sm8cx.1 (smDual sm8cx.2)) (v : SMV 8) :
    s v = v - (∑ i, v i) • (fun _ => (1 : ZMod 3)) := by
  rw [h.2 v, hdRo7SmAsmAux_cx8_smDual, hdRo7SmAsmAux_cx8_fst]
theorem hdRo7SmAsmAux_cx8_comm_perm {s : SMGL 8} (h : SMRefl s sm8cx.1 (smDual sm8cx.2))
    (σ : Equiv.Perm (Fin 8)) : Commute s (hdRo7SmAAux_permLin 8 σ) := by
  apply LinearEquiv.ext
  intro v
  ext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [hdRo7SmAsmAux_cx8_refl_form h (hdRo7SmAAux_permLin 8 σ v), hdRo7SmAsmAux_cx8_refl_form h v]
  rw [map_sub, map_smul, hdRo7SmAsmAux_permLin_sum σ v, hdRo7SmAsmAux_permLin_ones]
theorem hdRo7SmAsmAux_cx8_not_perm {s : SMGL 8} (h : SMRefl s sm8cx.1 (smDual sm8cx.2)) :
    ¬ SMIsPerm s := by
  rintro ⟨σ, hσ⟩
  have e1 := hσ (Pi.single 0 (1 : ZMod 3)) 1
  rw [hdRo7SmAsmAux_cx8_refl_form h] at e1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, Finset.sum_apply,
    Pi.single_eq_same, Finset.sum_eq_single] at e1
  rcases eq_or_ne (σ.symm 1) 0 with h0 | h0
  · rw [h0, Pi.single_eq_same] at e1
    exact (by decide : ¬ ((-1 : ZMod 3) = 1)) e1
  · rw [Pi.single_eq_of_ne h0] at e1
    exact (by decide : ¬ ((-1 : ZMod 3) = 0)) e1
theorem hdRo7SmAsmAux_cx8_class_refl {s : SMGL 8} {u w : SMV 8}
    (h : SMRefl s u (smDual w)) (hc : SMClass (u, w) sm8cx) :
    SMRefl s sm8cx.1 (smDual sm8cx.2) := by
  obtain ⟨π, c, hcs, hcomp⟩ := hc
  have hu : u = c • sm8cx.1 := by
    funext i
    rw [show u i = c * sm8cx.1 (π i) from (hcomp i).1, Pi.smul_apply,
      hdRo7SmAsmAux_cx8_fst_apply (π i), hdRo7SmAsmAux_cx8_fst_apply i, smul_eq_mul]
  have hw : w = c • sm8cx.2 := by
    funext i
    rw [show w i = c * sm8cx.2 (π i) from (hcomp i).2, Pi.smul_apply,
      hdRo7SmAsmAux_cx8_snd_apply (π i), hdRo7SmAsmAux_cx8_snd_apply i, smul_eq_mul]
  rw [hu, hw] at h
  exact (hdRo7SmAsmAux_smRefl_scale (r := s) (u := sm8cx.1) (w := sm8cx.2) hcs).mp h
theorem hdRo7SmAsmAux_conn_isolated {α : Type*} [Mul α] {S : Set α} {a : α}
    (hcomm : ∀ b ∈ S, Commute a b) {t : α}
    (ht : Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ ¬ Commute x y) a t) :
    t = a := by
  induction ht with
  | refl => rfl
  | tail hbase hstep ih =>
      exfalso
      rw [ih] at hstep
      exact hstep.2.2 (hcomm _ hstep.2.1)
theorem hdRo7SmAsmAux_isPerm_mem_range {m : ℕ} {g : SMGL m} (hg : SMIsPerm g) :
    g ∈ (hdRo7SmAAux_permLin m).range := by
  obtain ⟨σ, hσ⟩ := hg
  exact ⟨σ, by ext v i; rw [hdRo7SmAAux_permLin_apply, hσ]⟩
theorem hdRo7SmAsmAux_mem_range_isPerm {m : ℕ} {g : SMGL m}
    (hg : g ∈ (hdRo7SmAAux_permLin m).range) : SMIsPerm g := by
  obtain ⟨σ, hσ⟩ := hg
  exact ⟨σ, fun v i => by rw [← hσ]; rfl⟩
theorem hdRo7SmAsmAux_cx_contra {m : ℕ} {H : Subgroup (SMGL m)} {S : Set (SMGL m)} {cx : SMV m × SMV m}
    {g0 : SMGL m}
    (hP : ∀ g, SMIsPerm g → g ∈ H)
    (hS_eq : H = Subgroup.closure S)
    (hS_conn : ∀ r ∈ S, ∀ t ∈ S,
      Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ ¬ Commute a b) r t)
    (hpart : ∀ s ∈ S, SMIsPerm s ∨ SMRefl s cx.1 (smDual cx.2))
    (hnotperm : ∀ s, SMRefl s cx.1 (smDual cx.2) → ¬ SMIsPerm s)
    (hcomm : ∀ s, SMRefl s cx.1 (smDual cx.2) → ∀ g, SMIsPerm g → Commute s g)
    (hg0perm : SMIsPerm g0) (hg0ne1 : g0 ≠ 1)
    (hg0ne : ¬ SMRefl g0 cx.1 (smDual cx.2))
    (hcxR : ∃ r0 ∈ H, SMRefl r0 cx.1 (smDual cx.2)) :
    False := by
  by_cases hex : ∃ s ∈ S, ¬ SMIsPerm s
  · obtain ⟨a, haS, hanp⟩ := hex
    have ha : SMRefl a cx.1 (smDual cx.2) := (hpart a haS).resolve_left hanp
    have hcomm_all : ∀ t ∈ S, Commute a t := by
      intro t ht
      rcases hpart t ht with htp | ht'
      · exact hcomm a ha t htp
      · have hta : t = a := hdRo7SmAsmAux_refl_unique ht' ha
        rw [hta]
    have hSsub : S ⊆ {a} := by
      intro t ht
      have := hdRo7SmAsmAux_conn_isolated hcomm_all (hS_conn a haS t ht)
      simpa [this]
    have hHa : H = Subgroup.closure ({a} : Set (SMGL m)) := by
      rw [hS_eq]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro t ht
        have ht' : t = a := by have := hSsub ht; simpa using this
        rw [ht']
        exact Subgroup.subset_closure (Set.mem_singleton a)
      · rw [Subgroup.closure_le]
        intro t ht
        rw [Set.mem_singleton_iff] at ht
        rw [ht]
        exact Subgroup.subset_closure haS
    have hinvol : a * a = 1 := hdRo7SmAsmAux_refl_invol ha
    have hg0H : g0 ∈ H := hP g0 hg0perm
    have hg0cl : g0 ∈ Subgroup.closure ({a} : Set (SMGL m)) := by rwa [← hHa]
    rcases hdRo7SmAsmAux_singleton_closure a hinvol hg0cl with h1 | ha'
    · exact hg0ne1 h1
    · exact hg0ne (by rw [ha']; exact ha)
  · push Not at hex
    have hHperm : ∀ g ∈ H, SMIsPerm g := by
      intro g hg
      have hle : H ≤ (hdRo7SmAAux_permLin m).range := by
        rw [hS_eq]
        rw [Subgroup.closure_le]
        intro s hs
        exact hdRo7SmAsmAux_isPerm_mem_range (hex s hs)
      exact hdRo7SmAsmAux_mem_range_isPerm (hle hg)
    obtain ⟨r0, hr0H, hr0refl⟩ := hcxR
    exact hnotperm r0 hr0refl (hHperm r0 hr0H)
theorem hdRo7SmAsmAux_isPerm_eq_permLin {m : ℕ} {g : SMGL m} (hg : SMIsPerm g) :
    ∃ σ : Equiv.Perm (Fin m), g = hdRo7SmAAux_permLin m σ := by
  obtain ⟨σ, hσ⟩ := hg
  exact ⟨σ, by ext v i; rw [hσ, hdRo7SmAAux_permLin_apply]⟩
theorem hdRo7SmAsmAux_cx7_swap_perm :
    SMIsPerm (hdRo7SmAAux_permLin 7 (Equiv.swap 0 1)) :=
  hdRo7SmAAux_isPerm_permLin (Equiv.swap 0 1)
theorem hdRo7SmAsmAux_cx7_swap_ne_one :
    hdRo7SmAAux_permLin 7 (Equiv.swap 0 1) ≠ 1 := fun h =>
  (by decide : (Equiv.swap 0 1 : Equiv.Perm (Fin 7)) ≠ 1)
    (hdRo7SmAAux_permLin_injective 7 h)
theorem hdRo7SmAsmAux_cx8_swap_perm :
    SMIsPerm (hdRo7SmAAux_permLin 8 (Equiv.swap 0 1)) :=
  hdRo7SmAAux_isPerm_permLin (Equiv.swap 0 1)
theorem hdRo7SmAsmAux_cx8_swap_ne_one :
    hdRo7SmAAux_permLin 8 (Equiv.swap 0 1) ≠ 1 := fun h =>
  (by decide : (Equiv.swap 0 1 : Equiv.Perm (Fin 8)) ≠ 1)
    (hdRo7SmAAux_permLin_injective 8 h)

end CFSG.StandardType.HdRo7SU.Small

end
