module

public import CFSG.LocalAnalysis.StandardType.GGDRootFork

public section

namespace CFSG.StandardType

open Matrix

def ggSignOfBit (b : Fin 2) : ℤ := if b = 0 then 1 else -1

theorem ggSignOfBit_mem (b : Fin 2) : ggSignOfBit b = 1 ∨ ggSignOfBit b = -1 := by
  fin_cases b <;> simp [ggSignOfBit]

def ggD4Std : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, -1, 0, 0; -1, 0, 1, 0; -1, 0, -1, 0; 0, 1, 0, 1]

theorem ggD4Std_zero_apply (c : Fin 4) :
    ggD4Std 0 c = if c = 0 then 1 else if c = 1 then -1 else 0 := by
  fin_cases c <;> rfl

def ggD4Leaves : Finset (Fin 4 → ℤ) :=
  {![-1, 0, 1, 0], ![-1, 0, -1, 0], ![-1, 0, 0, 1], ![-1, 0, 0, -1],
   ![0, 1, 1, 0], ![0, 1, -1, 0], ![0, 1, 0, 1], ![0, 1, 0, -1]}

def ggIsSignedPerm (w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ)) : Prop :=
  ∀ a, w.2 a = 1 ∨ w.2 a = -1

def ggSignedPermsFour : Finset (Equiv.Perm (Fin 4) × (Fin 4 → ℤ)) :=
  ((Finset.univ : Finset (Equiv.Perm (Fin 4))).product
      (Finset.univ : Finset (Fin 4 → Fin 2))).image fun p =>
    (p.1, fun a => ggSignOfBit (p.2 a))

def ggSignedPermAction (w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ))
    (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun b => w.2 (w.1.symm b) * x (w.1.symm b)

def ggSignedPermMul (v w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ)) :
    Equiv.Perm (Fin 4) × (Fin 4 → ℤ) :=
  (w.1.trans v.1, fun a => w.2 a * v.2 (w.1 a))

def ggSignedPermsFourFix : Finset (Equiv.Perm (Fin 4) × (Fin 4 → ℤ)) :=
  (Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2 × Fin 2)).image fun p =>
    ((if p.1 = 0 then 1 else Equiv.swap 0 1).trans
        (if p.2.1 = 0 then 1 else Equiv.swap 2 3),
     fun a => if a = 0 then (if p.1 = 0 then 1 else -1)
       else if a = 1 then (if p.1 = 0 then 1 else -1)
       else if a = 2 then ggSignOfBit p.2.2.1 else ggSignOfBit p.2.2.2)

def ggPermsFixZero : Finset (Equiv.Perm (Fin 4)) :=
  {1, Equiv.swap 1 2, Equiv.swap 1 3, Equiv.swap 2 3,
    (Equiv.swap 1 2).trans (Equiv.swap 2 3),
    (Equiv.swap 1 3).trans (Equiv.swap 2 3)}

theorem ggSignedPermAction_apply (w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ))
    (x : Fin 4 → ℤ) (a : Fin 4) :
    ggSignedPermAction w x (w.1 a) = w.2 a * x a := by
  simp [ggSignedPermAction]

theorem ggIsSignedPerm_of_mem_ggSignedPermsFour {w} (hw : w ∈ ggSignedPermsFour) :
    ggIsSignedPerm w := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
  intro a
  exact ggSignOfBit_mem (p.2 a)

theorem mem_ggSignedPermsFour_iff {w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ)} :
    w ∈ ggSignedPermsFour ↔ ggIsSignedPerm w := by
  constructor
  · exact ggIsSignedPerm_of_mem_ggSignedPermsFour
  · intro hw
    refine Finset.mem_image.mpr
      ⟨(w.1, fun a => if w.2 a = 1 then (0 : Fin 2) else 1), by simp, ?_⟩
    apply Prod.ext
    · rfl
    · funext a
      rcases hw a with h | h <;> simp [ggSignOfBit, h]

theorem ggSignedPermMul_mem {v w}
    (hv : v ∈ ggSignedPermsFour) (hw : w ∈ ggSignedPermsFour) :
    ggSignedPermMul v w ∈ ggSignedPermsFour := by
  rw [mem_ggSignedPermsFour_iff] at hv hw ⊢
  intro a
  rcases hw a with h | h <;> rcases hv (w.1 a) with h' | h' <;> simp [ggSignedPermMul, h, h']

theorem ggSignedPermAction_mul (v w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ))
    (x : Fin 4 → ℤ) :
    ggSignedPermAction (ggSignedPermMul v w) x = ggSignedPermAction v (ggSignedPermAction w x) := by
  funext b
  simp only [ggSignedPermAction, ggSignedPermMul, Equiv.symm_trans_apply,
    Equiv.apply_symm_apply]
  simp only [mul_assoc, mul_comm (v.2 _), mul_left_comm]

theorem ggDDot_ggSignedPermAction (w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ))
    (hw : ggIsSignedPerm w) (x y : Fin 4 → ℤ) :
    ggDDot (ggSignedPermAction w x) (ggSignedPermAction w y) = ggDDot x y := by
  simp only [ggDDot, ggSignedPermAction]
  rw [Equiv.sum_comp w.1.symm (fun b => (w.2 b * x b) * (w.2 b * y b))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases hw a with h | h <;> simp [h]

theorem ggSignedPermAction_mem_dRootSet {w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ)}
    (hw : ggIsSignedPerm w) {γ : Fin 4 → ℤ} (hγ : γ ∈ ggDRootSet 4) :
    ggSignedPermAction w γ ∈ ggDRootSet 4 := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := hγ
  let v : Fin 4 → ℤ := Pi.single a s + Pi.single b t
  change ggSignedPermAction w v ∈ ggDRootSet 4
  have hsa : w.2 a * s = 1 ∨ w.2 a * s = -1 := by
    rcases hw a with h | h <;> rcases hs with hs | hs <;> simp [h, hs]
  have htb : w.2 b * t = 1 ∨ w.2 b * t = -1 := by
    rcases hw b with h | h <;> rcases ht with ht | ht <;> simp [h, ht]
  have hne : w.1 a ≠ w.1 b := fun h => hab (w.1.injective h)
  refine ⟨w.1 a, w.1 b, w.2 a * s, w.2 b * t, fun h => hab (w.1.injective h),
    hsa, htb, ?_⟩
  funext c
  by_cases hca : c = w.1 a
  · subst hca
    have hsym : w.1.symm (w.1 a) = a := Equiv.symm_apply_apply w.1 a
    have h1 : v a = s := by
      change (Pi.single a s : Fin 4 → ℤ) a + (Pi.single b t : Fin 4 → ℤ) a = s
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
    rw [ggSignedPermAction, hsym, h1, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hne, add_zero]
  · by_cases hcb : c = w.1 b
    · subst hcb
      have hsym : w.1.symm (w.1 b) = b := Equiv.symm_apply_apply w.1 b
      have h1 : v b = t := by
        change (Pi.single a s : Fin 4 → ℤ) b + (Pi.single b t : Fin 4 → ℤ) b = t
        rw [Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same, zero_add]
      rw [ggSignedPermAction, hsym, h1, Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hne),
        Pi.single_eq_same, zero_add]
    · have hsa' : w.1.symm c ≠ a :=
        fun h => hca (by rw [← h, Equiv.apply_symm_apply])
      have hsb' : w.1.symm c ≠ b :=
        fun h => hcb (by rw [← h, Equiv.apply_symm_apply])
      have h1 : v (w.1.symm c) = 0 := by
        change (Pi.single a s : Fin 4 → ℤ) (w.1.symm c) +
          (Pi.single b t : Fin 4 → ℤ) (w.1.symm c) = 0
        rw [Pi.single_eq_of_ne hsa', Pi.single_eq_of_ne hsb', add_zero]
      rw [ggSignedPermAction, h1, mul_zero, Pi.add_apply, Pi.single_eq_of_ne hca,
        Pi.single_eq_of_ne hcb, add_zero]

theorem ggD4Leaves_mem_of_dRoot {γ : Fin 4 → ℤ} (hγ : γ ∈ ggDRootSet 4)
    (h : ggDDot γ (ggD4Std 0) = -1) : γ ∈ ggD4Leaves := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := hγ
  let v : Fin 4 → ℤ := Pi.single a s + Pi.single b t
  change ggDDot v (ggD4Std 0) = -1 at h
  have h01 : v 0 + -v 1 = -1 := by
    simpa [ggDDot, ggD4Std, Fin.sum_univ_succ] using h
  change v ∈ ggD4Leaves
  fin_cases a <;> fin_cases b <;>
    first
      | exact absurd rfl hab
      | (rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
         simp [v] at h01 ⊢ <;>
         first | omega | decide +kernel)

theorem exists_ggSignedPerm_map_std0 {γ : Fin 4 → ℤ} (hγ : γ ∈ ggDRootSet 4) :
    ∃ w ∈ ggSignedPermsFour, ggSignedPermAction w γ = ggD4Std 0 := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := hγ
  let v : Fin 4 → ℤ := Pi.single a s + Pi.single b t
  change ∃ w ∈ ggSignedPermsFour, ggSignedPermAction w v = ggD4Std 0
  let π : Equiv.Perm (Fin 4) :=
    (Equiv.swap a 0).trans (Equiv.swap ((Equiv.swap a 0) b) 1)
  have hπa : π a = 0 := by
    have hb0 : (Equiv.swap a 0) b ≠ 0 := by
      intro h
      have h' : (Equiv.swap a 0) b = (Equiv.swap a 0) a := by
        rw [h, Equiv.swap_apply_left]
      exact hab ((Equiv.swap a 0).injective h'.symm)
    have h0b : (0 : Fin 4) ≠ (Equiv.swap a 0) b := Ne.symm hb0
    have hswap : (Equiv.swap ((Equiv.swap a 0) b) 1) (0 : Fin 4) = 0 :=
      Equiv.swap_apply_of_ne_of_ne h0b (by decide)
    simp [π, Equiv.trans_apply, hswap]
  have hπb : π b = 1 := by
    simp [π, Equiv.trans_apply]
  let ε : Fin 4 → ℤ := fun x => if x = a then s else if x = b then -t else 1
  have hε : ∀ x, ε x = 1 ∨ ε x = -1 := by
    intro x
    by_cases hxa : x = a
    · rw [hxa]
      have hval : ε a = s := by simp [ε]
      rw [hval]
      exact hs
    · by_cases hxb : x = b
      · rw [hxb]
        have hba : b ≠ a := Ne.symm hab
        have hval : ε b = -t := by simp [ε, hba]
        rw [hval]
        rcases ht with ht | ht <;> simp [ht]
      · have hval : ε x = 1 := by simp [ε, hxa, hxb]
        rw [hval]
        exact Or.inl rfl
  refine ⟨(π, ε), ?_, ?_⟩
  · rw [mem_ggSignedPermsFour_iff]
    exact hε
  · funext c
    rw [ggD4Std_zero_apply]
    by_cases hc0 : c = 0
    · subst hc0
      have hsym : π.symm 0 = a := by rw [← hπa, Equiv.symm_apply_apply]
      have h1 : v a = s := by
        change (Pi.single a s : Fin 4 → ℤ) a + (Pi.single b t : Fin 4 → ℤ) a = s
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero]
      have hεa : ε a = s := by simp [ε]
      rw [ggSignedPermAction, hsym, h1]
      change ε a * s = if (0 : Fin 4) = 0 then (1 : ℤ) else if (0 : Fin 4) = 1 then -1 else 0
      rw [hεa]
      rcases hs with hs | hs <;> simp [hs]
    · by_cases hc1 : c = 1
      · subst hc1
        have hsym : π.symm 1 = b := by
          apply π.injective
          rw [Equiv.apply_symm_apply, hπb]
        have h1 : v b = t := by
          change (Pi.single a s : Fin 4 → ℤ) b + (Pi.single b t : Fin 4 → ℤ) b = t
          rw [Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same, zero_add]
        have hεb : ε b = -t := by simp [ε, Ne.symm hab]
        rw [ggSignedPermAction, hsym, h1]
        change ε b * t = if (1 : Fin 4) = 0 then (1 : ℤ) else if (1 : Fin 4) = 1 then -1 else 0
        rw [hεb]
        rcases ht with ht | ht <;> simp [ht]
      · have hsa : π.symm c ≠ a := by
          intro h
          exact hc0 (by rw [← Equiv.apply_symm_apply π c, h, hπa])
        have hsb : π.symm c ≠ b := by
          intro h
          exact hc1 (by rw [← Equiv.apply_symm_apply π c, h, hπb])
        have h1 : v (π.symm c) = 0 := by
          change (Pi.single a s : Fin 4 → ℤ) (π.symm c) +
            (Pi.single b t : Fin 4 → ℤ) (π.symm c) = 0
          rw [Pi.single_eq_of_ne hsa, Pi.single_eq_of_ne hsb, add_zero]
        rw [ggSignedPermAction, h1]
        change ε (π.symm c) * 0 = if c = 0 then (1 : ℤ) else if c = 1 then -1 else 0
        rw [mul_zero]
        simp [hc0, hc1]

theorem ggSignedPermsFourFix_subset : ggSignedPermsFourFix ⊆ ggSignedPermsFour := by
  intro w hw
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨p1, p2, p3, p4⟩ := p
  rw [mem_ggSignedPermsFour_iff]
  intro a
  fin_cases p1 <;> fin_cases p2 <;> fin_cases p3 <;> fin_cases p4 <;>
    fin_cases a <;> simp [ggSignOfBit]

theorem exists_ggSignedPerm_of_leaf_triple (t1 t2 t3 : Fin 4 → ℤ)
    (h1 : t1 ∈ ggD4Leaves) (h2 : t2 ∈ ggD4Leaves) (h3 : t3 ∈ ggD4Leaves)
    (h12 : ggDDot t1 t2 = 0) (h13 : ggDDot t1 t3 = 0) (h23 : ggDDot t2 t3 = 0) :
    ∃ w ∈ ggSignedPermsFourFix, ∃ f ∈ ggPermsFixZero, f 0 = 0 ∧
      ggSignedPermAction w t1 = ggD4Std (f 1) ∧
      ggSignedPermAction w t2 = ggD4Std (f 2) ∧
      ggSignedPermAction w t3 = ggD4Std (f 3) := by
  have h : ∀ u1 ∈ ggD4Leaves, ∀ u2 ∈ ggD4Leaves, ∀ u3 ∈ ggD4Leaves,
      ggDDot u1 u2 = 0 → ggDDot u1 u3 = 0 → ggDDot u2 u3 = 0 →
      ∃ w ∈ ggSignedPermsFourFix, ∃ f ∈ ggPermsFixZero, f 0 = 0 ∧
        ggSignedPermAction w u1 = ggD4Std (f 1) ∧
        ggSignedPermAction w u2 = ggD4Std (f 2) ∧
        ggSignedPermAction w u3 = ggD4Std (f 3) := by
    decide +kernel
  exact h t1 h1 t2 h2 t3 h3 h12 h13 h23

theorem card_eq_four_of_dRoot_gram {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (ρ : Λ → Fin 4 → ℤ) (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j)
    (hcard : 4 ≤ Fintype.card Λ) : Fintype.card Λ = 4 := by
  classical
  have hfin : TauCeti.IsFiniteType C := isFiniteType_of_ggIsWeylMatrixFixed hM hC
  have hdet : C.det ≠ 0 := hfin.det_ne_zero
  let D : Matrix Λ (Fin 4) ℚ := fun i a => (ρ i a : ℚ)
  let Dt : Matrix (Fin 4) Λ ℚ := D.transpose
  have hBB : C.map (Int.castRingHom ℚ) = D * Dt := by
    ext i j
    change (C i j : ℚ) = (D * Dt) i j
    rw [Matrix.mul_apply]
    simp only [Dt, Matrix.transpose_apply]
    rw [← hgram i j]
    simp only [D, ggDDot, Int.cast_sum, Int.cast_mul]
  have hLI : LinearIndependent ℚ (fun i : Λ => fun a : Fin 4 => (ρ i a : ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hker : Dt *ᵥ c = 0 := by
      funext a
      change (∑ x, Dt a x * c x) = 0
      simp only [Dt, D]
      have hco := congrFun hc a
      have hco' : ∑ x, (ρ x a : ℚ) * c x = 0 := by
        simpa [D, mul_comm] using hco
      exact hco'
    have hCv : (C.map (Int.castRingHom ℚ)) *ᵥ c = 0 := by
      rw [hBB, ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]
    by_contra hc0
    have hcne : c ≠ 0 := by
      intro h
      exact hc0 (fun i => congrFun h i)
    have hdetq : (C.map (Int.castRingHom ℚ)).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hcne, hCv⟩
    have hdetq' : (C.det : ℚ) = 0 := by
      have hmap : (C.det : ℚ) = (C.map (Int.castRingHom ℚ)).det := by
        simpa [RingHom.mapMatrix] using RingHom.map_det (Int.castRingHom ℚ) C
      rw [hmap, hdetq]
    exact hdet (by exact_mod_cast hdetq')
  have hle : Fintype.card Λ ≤ 4 := by
    have h := hLI.fintype_card_le_finrank
    have hfr : Module.finrank ℚ (Fin 4 → ℚ) = 4 := by
      rw [Module.finrank_pi, Fintype.card_fin]
    omega
  omega


def ggD4Roots : Finset (Fin 4 → ℤ) :=
  {![1, 1, 0, 0], ![1, -1, 0, 0], ![-1, 1, 0, 0], ![-1, -1, 0, 0],
   ![1, 0, 1, 0], ![1, 0, -1, 0], ![-1, 0, 1, 0], ![-1, 0, -1, 0],
   ![1, 0, 0, 1], ![1, 0, 0, -1], ![-1, 0, 0, 1], ![-1, 0, 0, -1],
   ![0, 1, 1, 0], ![0, 1, -1, 0], ![0, -1, 1, 0], ![0, -1, -1, 0],
   ![0, 1, 0, 1], ![0, 1, 0, -1], ![0, -1, 0, 1], ![0, -1, 0, -1],
   ![0, 0, 1, 1], ![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, -1]}

theorem mem_ggD4Roots_of_dRoot {γ : Fin 4 → ℤ} (hγ : γ ∈ ggDRootSet 4) : γ ∈ ggD4Roots := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := hγ
  fin_cases a <;> fin_cases b <;>
    first
      | exact absurd rfl hab
      | (rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> decide +kernel)

theorem ggDDot_ne_zero_of_adj_four {β γ δ : Fin 4 → ℤ} (hβ : β ∈ ggDRootSet 4)
    (hγ : γ ∈ ggDRootSet 4) (hδ : δ ∈ ggDRootSet 4) (hβγ : ggDDot β γ = -1)
    (hδβ : ggDDot δ β = 0) : ggDDot δ γ ≠ 0 := by
  have key : ∀ u ∈ ggD4Leaves, ∀ v ∈ ggD4Roots, ggDDot v (ggD4Std 0) = 0 → ggDDot v u ≠ 0 := by
    decide +kernel
  obtain ⟨w, hw, hwβ⟩ := exists_ggSignedPerm_map_std0 hβ
  have hws := ggIsSignedPerm_of_mem_ggSignedPermsFour hw
  have hγ' : ggSignedPermAction w γ ∈ ggD4Leaves := by
    refine ggD4Leaves_mem_of_dRoot (ggSignedPermAction_mem_dRootSet hws hγ) ?_
    rw [← hwβ, ggDDot_ggSignedPermAction w hws, ggDDot_comm, hβγ]
  have hδ' : ggDDot (ggSignedPermAction w δ) (ggD4Std 0) = 0 := by
    rw [← hwβ, ggDDot_ggSignedPermAction w hws, hδβ]
  rw [← ggDDot_ggSignedPermAction w hws δ γ]
  exact key _ hγ' _ (mem_ggD4Roots_of_dRoot (ggSignedPermAction_mem_dRootSet hws hδ)) hδ'

theorem ggSignedPermAction_std0_of_mem_fix {w : Equiv.Perm (Fin 4) × (Fin 4 → ℤ)}
    (hw : w ∈ ggSignedPermsFourFix) : ggSignedPermAction w (ggD4Std 0) = ggD4Std 0 := by
  have h : ∀ w ∈ ggSignedPermsFourFix, ggSignedPermAction w (ggD4Std 0) = ggD4Std 0 := by
    decide +kernel
  exact h w hw

theorem two_le_card_filter_of_mem_pair {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {P : ι → Prop} [DecidablePred P] {y z : ι} (hy : y ∈ S) (hz : z ∈ S) (hyz : y ≠ z)
    (hPy : P y) (hPz : P z) : 2 ≤ (S.filter P).card := by
  have hsub : ({y, z} : Finset ι) ⊆ S.filter P := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hy, hPy⟩
    · exact Finset.mem_filter.mpr ⟨hz, hPz⟩
  calc 2 = ({y, z} : Finset ι).card := (Finset.card_pair hyz).symm
    _ ≤ (S.filter P).card := Finset.card_le_card hsub

theorem ggFiniteType_not_triangle {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}
    (hA : TauCeti.IsFiniteType A) (hsymm : ∀ i j, A i j = A j i) {x y z : ι}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h₁ : A x y ≠ 0) (h₂ : A x z ≠ 0) (h₃ : A y z ≠ 0) : False := by
  have hs : ∀ {i j}, A i j ≠ 0 → A j i ≠ 0 := fun h => by rwa [hsymm]
  refine ggResI_no_cycle hA {x, y, z} ⟨x, by simp⟩ fun i hi => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact two_le_card_filter_of_mem_pair (by simp) (by simp) hyz ⟨Ne.symm hxy, h₁⟩
      ⟨Ne.symm hxz, h₂⟩
  · exact two_le_card_filter_of_mem_pair (by simp) (by simp) hxz ⟨hxy, hs h₁⟩
      ⟨Ne.symm hyz, h₃⟩
  · exact two_le_card_filter_of_mem_pair (by simp) (by simp) hxy ⟨hxz, hs h₂⟩ ⟨hyz, hs h₃⟩

theorem ggFiniteType_not_square {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℤ}
    (hA : TauCeti.IsFiniteType A) (hsymm : ∀ i j, A i j = A j i) {x y z w : ι}
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (h₁ : A x y ≠ 0) (h₂ : A y z ≠ 0) (h₃ : A z w ≠ 0) (h₄ : A w x ≠ 0) : False := by
  have hs : ∀ {i j}, A i j ≠ 0 → A j i ≠ 0 := fun h => by rwa [hsymm]
  refine ggResI_no_cycle hA {x, y, z, w} ⟨x, by simp⟩ fun i hi => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact two_le_card_filter_of_mem_pair (by simp) (by simp) hyw ⟨Ne.symm hxy, h₁⟩
      ⟨Ne.symm hxw, hs h₄⟩
  · exact two_le_card_filter_of_mem_pair (by simp) (by simp) hxz ⟨hxy, hs h₁⟩
      ⟨Ne.symm hyz, h₂⟩
  · exact two_le_card_filter_of_mem_pair (by simp) (by simp) hyw ⟨hyz, hs h₂⟩
      ⟨Ne.symm hzw, h₃⟩
  · exact two_le_card_filter_of_mem_pair (by simp) (by simp) (Ne.symm hxz) ⟨hzw, hs h₃⟩
      ⟨hxw, h₄⟩

theorem exists_ggD4Centre {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (ρ : Λ → Fin 4 → ℤ) (hρ : ∀ i, ρ i ∈ ggDRootSet 4)
    (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j) (hcard : Fintype.card Λ = 4) :
    ∃ c j₁ j₂ j₃ : Λ, c ≠ j₁ ∧ c ≠ j₂ ∧ c ≠ j₃ ∧ j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧
      C c j₁ = -1 ∧ C c j₂ = -1 ∧ C c j₃ = -1 ∧ C j₁ j₂ = 0 ∧ C j₁ j₃ = 0 ∧ C j₂ j₃ = 0 := by
  have hsymm : ∀ i j, C i j = C j i := fun i j => by
    rw [← hgram i j, ← hgram j i, ggDDot_comm]
  have hoff := ggIntCartan_offdiag_of_gram hC ρ hρ hgram
  have hA : TauCeti.IsFiniteType C := isFiniteType_of_ggIsWeylMatrixFixed hM hC
  have hne : ∀ {x y}, x ≠ y → C x y ≠ 0 → C x y = -1 := fun hxy h =>
    (hoff _ _ hxy).resolve_left h
  have hs : ∀ {x y}, C x y ≠ 0 → C y x ≠ 0 := fun h => by rwa [hsymm]
  have hadj : ∀ {x y z}, x ≠ y → C x y ≠ 0 → C z x = 0 → C z y ≠ 0 := by
    intro x y z hxy h hzx
    have h₁ := hne hxy h
    rw [← hgram] at h₁ hzx ⊢
    exact ggDDot_ne_zero_of_adj_four (hρ x) (hρ y) (hρ z) h₁ hzx
  obtain ⟨β, γ, hβγ, hβγ0⟩ : ∃ β γ : Λ, β ≠ γ ∧ C β γ ≠ 0 := by
    obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Λ)
    rcases (ggRC_weyl_connected hM i j).cases_head with h | ⟨k, ⟨hik, hk⟩, -⟩
    · exact absurd h hij
    · exact ⟨i, k, hik, fun h0 => hk ((ggIntCartan_zero_iff hC hik).mp h0)⟩
  obtain ⟨δ₁, δ₂, hδ, hset⟩ :
      ∃ δ₁ δ₂ : Λ, δ₁ ≠ δ₂ ∧ (Finset.univ.erase β).erase γ = {δ₁, δ₂} := by
    have hγmem : γ ∈ Finset.univ.erase β := Finset.mem_erase.mpr ⟨Ne.symm hβγ, Finset.mem_univ _⟩
    refine Finset.card_eq_two.mp ?_
    rw [Finset.card_erase_of_mem hγmem, Finset.card_erase_of_mem (Finset.mem_univ β),
      Finset.card_univ, hcard]
  have hδmem : ∀ δ, δ ∈ (Finset.univ.erase β).erase γ → δ ≠ β ∧ δ ≠ γ := fun δ h => by
    rw [Finset.mem_erase, Finset.mem_erase] at h
    exact ⟨h.2.1, h.1⟩
  obtain ⟨h1β, h1γ⟩ := hδmem δ₁ (by rw [hset]; simp)
  obtain ⟨h2β, h2γ⟩ := hδmem δ₂ (by rw [hset]; simp)
  have hone : ∀ δ, δ ≠ β → δ ≠ γ → (C δ β ≠ 0 ∧ C δ γ = 0) ∨ (C δ β = 0 ∧ C δ γ ≠ 0) := by
    intro δ h₁ h₂
    by_cases hb : C δ β = 0
    · exact Or.inr ⟨hb, hadj hβγ hβγ0 hb⟩
    · refine Or.inl ⟨hb, ?_⟩
      by_contra hc
      exact ggFiniteType_not_triangle hA hsymm hβγ (Ne.symm h₁) (Ne.symm h₂) hβγ0 (hs hb) (hs hc)
  rcases hone δ₁ h1β h1γ with ⟨a₁, a₂⟩ | ⟨a₁, a₂⟩ <;>
    rcases hone δ₂ h2β h2γ with ⟨b₁, b₂⟩ | ⟨b₁, b₂⟩
  ·
    have h₁₂ : C δ₁ δ₂ = 0 := by
      by_contra h
      exact ggFiniteType_not_triangle hA hsymm (Ne.symm h1β) (Ne.symm h2β) hδ (hs a₁) (hs b₁) h
    refine ⟨β, γ, δ₁, δ₂, hβγ, Ne.symm h1β, Ne.symm h2β, Ne.symm h1γ, Ne.symm h2γ, hδ,
      hne hβγ hβγ0, hne (Ne.symm h1β) (hs a₁), hne (Ne.symm h2β) (hs b₁), ?_, ?_, h₁₂⟩
    · rw [hsymm]; exact a₂
    · rw [hsymm]; exact b₂
  ·
    exact (ggFiniteType_not_square hA hsymm h1β h1γ hδ hβγ (Ne.symm h2β) (Ne.symm h2γ) a₁ hβγ0
      (hs b₂) (hs (hadj (Ne.symm h2γ) (hs b₂) a₂))).elim
  ·
    exact (ggFiniteType_not_square hA hsymm h1γ h1β hδ (Ne.symm hβγ) (Ne.symm h2γ) (Ne.symm h2β)
      a₂ (hs hβγ0) (hs b₁) (hs (hadj (Ne.symm h2β) (hs b₁) a₁))).elim
  ·
    have h₁₂ : C δ₁ δ₂ = 0 := by
      by_contra h
      exact ggFiniteType_not_triangle hA hsymm (Ne.symm h1γ) (Ne.symm h2γ) hδ (hs a₂) (hs b₂) h
    refine ⟨γ, β, δ₁, δ₂, Ne.symm hβγ, Ne.symm h1γ, Ne.symm h2γ, Ne.symm h1β, Ne.symm h2β, hδ,
      hne (Ne.symm hβγ) (hs hβγ0), hne (Ne.symm h1γ) (hs a₂), hne (Ne.symm h2γ) (hs b₂), ?_, ?_,
      h₁₂⟩
    · rw [hsymm]; exact a₁
    · rw [hsymm]; exact b₁

theorem ggVecFour_injective {α : Type*} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all

theorem exists_ggSignedPerm_normalForm {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (ρ : Λ → Fin 4 → ℤ) (hρ : ∀ i, ρ i ∈ ggDRootSet 4)
    (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j) (hcard : Fintype.card Λ = 4) :
    ∃ w ∈ ggSignedPermsFour, ∃ g : Λ ≃ Fin 4,
      ∀ i, ggSignedPermAction w (ρ i) = ggD4Std (g i) := by
  obtain ⟨c, j₁, j₂, j₃, h01, h02, h03, h12, h13, h23, hc₁, hc₂, hc₃, h₁₂, h₁₃, h₂₃⟩ :=
    exists_ggD4Centre hM hC ρ hρ hgram hcard
  have hsymm : ∀ i j, C i j = C j i := fun i j => by
    rw [← hgram i j, ← hgram j i, ggDDot_comm]
  obtain ⟨w₀, hw₀, hw₀c⟩ := exists_ggSignedPerm_map_std0 (hρ c)
  have hw₀s := ggIsSignedPerm_of_mem_ggSignedPermsFour hw₀
  have hleaf : ∀ j, C c j = -1 → ggSignedPermAction w₀ (ρ j) ∈ ggD4Leaves := fun j hj =>
    ggD4Leaves_mem_of_dRoot (ggSignedPermAction_mem_dRootSet hw₀s (hρ j)) (by
      rw [← hw₀c, ggDDot_ggSignedPermAction w₀ hw₀s, hgram, hsymm, hj])
  have horth : ∀ j j', C j j' = 0 →
      ggDDot (ggSignedPermAction w₀ (ρ j)) (ggSignedPermAction w₀ (ρ j')) = 0 := fun j j' h => by
    rw [ggDDot_ggSignedPermAction w₀ hw₀s, hgram, h]
  obtain ⟨w₁, hw₁, f, -, hf0, hf₁, hf₂, hf₃⟩ := exists_ggSignedPerm_of_leaf_triple _ _ _
    (hleaf j₁ hc₁) (hleaf j₂ hc₂) (hleaf j₃ hc₃) (horth _ _ h₁₂) (horth _ _ h₁₃) (horth _ _ h₂₃)
  have he : Function.Injective ![c, j₁, j₂, j₃] := ggVecFour_injective h01 h02 h03 h12 h13 h23
  have hbij : Function.Bijective ![c, j₁, j₂, j₃] := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨he, by rw [Fintype.card_fin, hcard]⟩
  let E : Fin 4 ≃ Λ := Equiv.ofBijective _ hbij
  refine ⟨ggSignedPermMul w₁ w₀, ggSignedPermMul_mem (ggSignedPermsFourFix_subset hw₁) hw₀,
    E.symm.trans f, fun i => ?_⟩
  obtain ⟨a, rfl⟩ := hbij.2 i
  have hEa : (E.symm.trans f) (![c, j₁, j₂, j₃] a) = f a := congrArg f (E.symm_apply_apply a)
  rw [hEa, ggSignedPermAction_mul]
  fin_cases a
  · change ggSignedPermAction w₁ (ggSignedPermAction w₀ (ρ c)) = ggD4Std (f 0)
    rw [hw₀c, ggSignedPermAction_std0_of_mem_fix hw₁, hf0]
  · exact hf₁
  · exact hf₂
  · exact hf₃

theorem exists_signedPerm_of_dRoot_bases_four {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (ρ ρ' : Λ → Fin 4 → ℤ) (hρ : ∀ i, ρ i ∈ ggDRootSet 4) (hρ' : ∀ i, ρ' i ∈ ggDRootSet 4)
    (hgram : ∀ i j, ggDDot (ρ i) (ρ j) = C i j) (hgram' : ∀ i j, ggDDot (ρ' i) (ρ' j) = C i j)
    (hcard : 4 ≤ Fintype.card Λ) :
    ∃ (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ℤ) (σ : Equiv.Perm Λ), (∀ a, ε a = 1 ∨ ε a = -1) ∧
      (∀ i j, C (σ i) (σ j) = C i j) ∧ ∀ i a, ρ' i (π a) = ε a * ρ (σ i) a := by
  have h4 := card_eq_four_of_dRoot_gram hM hC ρ hgram hcard
  obtain ⟨w, hw, g, hg⟩ := exists_ggSignedPerm_normalForm hM hC ρ hρ hgram h4
  obtain ⟨w', hw', g', hg'⟩ := exists_ggSignedPerm_normalForm hM hC ρ' hρ' hgram' h4
  have hws := ggIsSignedPerm_of_mem_ggSignedPermsFour hw
  have hws' := ggIsSignedPerm_of_mem_ggSignedPermsFour hw'
  obtain ⟨σ, hgσ⟩ : ∃ σ : Equiv.Perm Λ, ∀ i, g (σ i) = g' i :=
    ⟨g'.trans g.symm, fun i => by simp⟩
  have hσ : ∀ i, ggSignedPermAction w (ρ (σ i)) = ggSignedPermAction w' (ρ' i) := fun i => by
    rw [hg, hg', hgσ]
  refine ⟨w.1.trans w'.1.symm, fun a => w'.2 (w'.1.symm (w.1 a)) * w.2 a, σ,
    fun a => ?_, fun i j => ?_, fun i a => ?_⟩
  · rcases hws' (w'.1.symm (w.1 a)) with h | h <;> rcases hws a with h' | h' <;> simp [h, h']
  · rw [← hgram (σ i) (σ j), ← hgram' i j,
      ← ggDDot_ggSignedPermAction w hws (ρ (σ i)) (ρ (σ j)), hσ, hσ,
      ggDDot_ggSignedPermAction w' hws']
  · show ρ' i (w'.1.symm (w.1 a)) = w'.2 (w'.1.symm (w.1 a)) * w.2 a * ρ (σ i) a
    have h₁ := congrFun (hσ i) (w.1 a)
    rw [ggSignedPermAction_apply] at h₁
    change w.2 a * ρ (σ i) a = w'.2 (w'.1.symm (w.1 a)) * ρ' i (w'.1.symm (w.1 a)) at h₁
    rcases hws' (w'.1.symm (w.1 a)) with h | h <;> rw [h] at h₁ ⊢ <;> linarith

end CFSG.StandardType

end
