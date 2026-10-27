module

public import CFSG.RankThree.PartOne.SEITZ8.D4Defs

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

variable {K : Type} [Field K]

@[expose] noncomputable def jLab : Label d4 → Label d4 → ℤ
  | .inl i, .inl j => if (i.val = 2) ≠ (j.val = 2) then 1 else 0
  | .inr α, .inr β => open Classical in if β.1 = -α.1 then 1 else 0
  | _, _ => 0

@[expose] noncomputable def jForm (K : Type) [Field K] : LinearMap.BilinForm K (RootModule d4 K) :=
  Finsupp.linearCombination K fun a => Finsupp.linearCombination K fun b => (jLab a b : K)

theorem jForm_single (a b : Label d4) :
    jForm K (Finsupp.single a 1) (Finsupp.single b 1) = (jLab a b : K) := by
  simp [jForm, Finsupp.linearCombination_single]

theorem jLab_comm (a b : Label d4) : jLab a b = jLab b a := by
  rcases a with i | ⟨α, hα⟩ <;> rcases b with j | ⟨β, hβ⟩
  · simp only [jLab]
    by_cases h : (i.val = 2) ≠ (j.val = 2)
    · rw [ite_eq_left h, ite_eq_left (Ne.symm h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (Ne.symm h'))]
  · rfl
  · rfl
  · simp only [jLab]
    by_cases h : β = -α
    · have h' : α = -β := by rw [h]; simp
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬ α = -β := fun e => h (by rw [e]; simp)
      rw [ite_eq_right h, ite_eq_right h']

theorem jForm_comm (x y : RootModule d4 K) : jForm K x y = jForm K y x := by
  have h : LinearMap.flip (jForm K) = jForm K := by
    refine LinearMap.ext_basis Finsupp.basisSingleOne Finsupp.basisSingleOne fun a b => ?_
    simp only [Finsupp.coe_basisSingleOne, LinearMap.flip_apply, jForm_single, jLab_comm b a]
  calc jForm K x y = LinearMap.flip (jForm K) y x := rfl
    _ = jForm K y x := by rw [h]

theorem jForm_rootVec_left (γ : Fin d4.rank → ℤ) (x : RootModule d4 K) :
    jForm K (rootVec d4 K (-γ)) x = coordAt γ x := by
  by_cases hγ : IsRoot d4 γ
  · have hγ' := isRoot_neg_d4 hγ
    rw [rootVec_eq_single K hγ']
    induction x using Finsupp.induction_linear with
    | zero => simp [coordAt]
    | add x y hx hy => rw [map_add, hx, hy, coordAt_add]
    | single b r =>
      rw [← Finsupp.smul_single_one b r, map_smul, coordAt_smul]
      congr 1
      rcases b with j | ⟨δ, hδ⟩
      · rw [jForm_single]
        have : Finsupp.single (Sum.inl j : Label d4) (1 : K) = hVec d4 K j := rfl
        rw [this, coordAt_hVec]
        simp [jLab]
      · rw [jForm_single, ← rootVec_eq_single K hδ]
        by_cases h : γ = δ
        · subst h
          rw [coordAt_rootVec_self hγ]
          simp [jLab]
        · rw [coordAt_rootVec_ne h]
          have : ¬ δ = γ := fun e => h e.symm
          simp [jLab, this]
  · have h' : ¬ IsRoot d4 (-γ) := fun h => hγ (by simpa using isRoot_neg_d4 h)
    rw [rootVec, dite_eq_right h']
    simp [coordAt, hγ]

theorem jForm_rootVec_left' {γ δ : Fin d4.rank → ℤ} (h : δ = -γ)
    (x : RootModule d4 K) : jForm K (rootVec d4 K δ) x = coordAt γ x := by
  subst h
  exact jForm_rootVec_left γ x

theorem jForm_hVec_outer {i : Fin d4.rank} (hi : i.val ≠ 2) (x : RootModule d4 K) :
    jForm K (hVec d4 K i) x = x (Sum.inl ⟨2, by decide⟩) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, Finsupp.add_apply]
  | single b r =>
    rw [← Finsupp.smul_single_one b r, map_smul, Finsupp.smul_apply]
    congr 1
    have : hVec d4 K i = Finsupp.single (Sum.inl i : Label d4) 1 := rfl
    rw [this, jForm_single]
    rcases b with j | δ
    · by_cases h : j.val = 2
      · have hj : j = ⟨2, by decide⟩ := Fin.ext h
        subst hj
        simp [jLab, hi]
      · have hj : ¬ j = (⟨2, by decide⟩ : Fin d4.rank) := fun e => h (by rw [e])
        simp [jLab, hi, h, hj]
    · simp [jLab]

theorem jForm_hVec_central (x : RootModule d4 K) :
    jForm K (hVec d4 K ⟨2, by decide⟩) x =
      x (Sum.inl ⟨0, by decide⟩) + x (Sum.inl ⟨1, by decide⟩) + x (Sum.inl ⟨3, by decide⟩) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, hx, hy]
    simp only [Finsupp.add_apply]
    ring
  | single b r =>
    rw [← Finsupp.smul_single_one b r, map_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    have : hVec d4 K ⟨2, by decide⟩ = Finsupp.single (Sum.inl ⟨2, by decide⟩ : Label d4) 1 := rfl
    rw [this, jForm_single]
    rcases b with j | δ
    · have hj : j.val < 4 := j.2
      have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
      rcases this with h | h | h | h
      · have e : j = (⟨0, by decide⟩ : Fin d4.rank) := Fin.ext h
        subst e
        simp [jLab]
      · have e : j = (⟨1, by decide⟩ : Fin d4.rank) := Fin.ext h
        subst e
        simp [jLab]
      · have e : j = (⟨2, by decide⟩ : Fin d4.rank) := Fin.ext h
        subst e
        simp [jLab]
      · have e : j = (⟨3, by decide⟩ : Fin d4.rank) := Fin.ext h
        subst e
        simp [jLab]
    · simp [jLab]

abbrev DIdx : Type := Idx (Tag.rootCertificate d4)

@[expose] def jIdx : DIdx → DIdx → ℤ
  | .inl i, .inl j => if (i.val == 2) != (j.val == 2) then 1 else 0
  | .inr m, .inr n =>
    if vecBEq ((Tag.rootCertificate d4).root n) (-((Tag.rootCertificate d4).root m)) then 1 else 0
  | _, _ => 0

@[expose] def jColL : Col (Tag.rootCertificate d4) → DIdx → ℤ
  | none, _ => 0
  | some (a, z), b => z * jIdx a b

@[expose] def jColR : DIdx → Col (Tag.rootCertificate d4) → ℤ
  | _, none => 0
  | a, some (b, z) => z * jIdx a b

@[expose] def dIdxList : List DIdx :=
  (List.finRange (Tag.rank d4)).map Sum.inl ++
    (List.finRange (Tag.rootCertificate d4).roots.length).map Sum.inr

@[expose] def selfAdjB (f : DIdx → Col (Tag.rootCertificate d4)) : Bool :=
  dIdxList.all fun a => dIdxList.all fun b => (jColL (f a) b - jColR a (f b)) % 2 == 0

@[expose] def formCheck : Bool :=
  (List.finRange (Tag.rank d4)).all fun i => [1, 2, 3].all fun k =>
    selfAdjB (xCol (Tag.rootCertificate d4) (Tag.stringData d4) i k) &&
      selfAdjB (yCol (Tag.rootCertificate d4) (Tag.stringData d4) i k)

theorem formCheck_eq : formCheck = true := by decide +kernel

theorem mem_dIdxList (a : DIdx) : a ∈ dIdxList := by
  rcases a with j | m <;> simp [dIdxList]

theorem selfAdjB_spec {f : DIdx → Col (Tag.rootCertificate d4)} (h : selfAdjB f = true)
    (a b : DIdx) : (jColL (f a) b - jColR a (f b)) % 2 = 0 := by
  simp only [selfAdjB, List.all_eq_true, beq_iff_eq] at h
  exact h a (mem_dIdxList a) b (mem_dIdxList b)

section Certs


theorem jLab_toLabel (a b : DIdx) :
    jLab (toLabel (Tag.rootCertificate_check d4) a) (toLabel (Tag.rootCertificate_check d4) b) =
      jIdx a b := by
  rcases a with i | m <;> rcases b with j | n
  · simp only [jLab, jIdx, toLabel]
    by_cases h1 : i.val = 2 <;> by_cases h2 : j.val = 2 <;> simp [h1, h2]
  · rfl
  · rfl
  · simp only [jLab, jIdx, toLabel]
    by_cases h : (Tag.rootCertificate d4).root n = -(Tag.rootCertificate d4).root m
    · rw [ite_eq_left h, ite_eq_left (vecBEq_iff.2 h)]
    · rw [ite_eq_right h, ite_eq_right fun e => h (vecBEq_iff.1 e)]

theorem jForm_toVec_single (u : Col (Tag.rootCertificate d4)) (b : DIdx) :
    jForm K (toVec (Tag.rootCertificate_check d4) K u)
      (Finsupp.single (toLabel (Tag.rootCertificate_check d4) b) 1) = (jColL u b : K) := by
  rcases u with _ | ⟨a, z⟩
  · simp [jColL]
  · rw [toVec_some, map_smul, LinearMap.smul_apply, jForm_single, jLab_toLabel]
    simp [jColL]

theorem jForm_single_toVec (a : DIdx) (u : Col (Tag.rootCertificate d4)) :
    jForm K (Finsupp.single (toLabel (Tag.rootCertificate_check d4) a) 1)
      (toVec (Tag.rootCertificate_check d4) K u) = (jColR a u : K) := by
  rcases u with _ | ⟨b, z⟩
  · simp [jColR]
  · rw [toVec_some, map_smul, jForm_single, jLab_toLabel]
    simp [jColR]

theorem selfAdj_of_check [CharP K 2] {T : Module.End K (RootModule d4 K)}
    {f : DIdx → Col (Tag.rootCertificate d4)}
    (hT : ∀ a, T (Finsupp.single (toLabel (Tag.rootCertificate_check d4) a) 1) =
      toVec (Tag.rootCertificate_check d4) K (f a)) (hf : selfAdjB f = true)
    (x y : RootModule d4 K) : jForm K (T x) y = jForm K x (T y) := by
  have key : (jForm K).compl₁₂ T LinearMap.id = (jForm K).compl₁₂ LinearMap.id T := by
    refine LinearMap.ext_basis Finsupp.basisSingleOne Finsupp.basisSingleOne fun a b => ?_
    obtain ⟨a', rfl⟩ := surjective_toLabel (Tag.rootCertificate_check d4) a
    obtain ⟨b', rfl⟩ := surjective_toLabel (Tag.rootCertificate_check d4) b
    simp only [Finsupp.coe_basisSingleOne, LinearMap.compl₁₂_apply, LinearMap.id_apply]
    rw [hT a', hT b', jForm_toVec_single, jForm_single_toVec]
    have h2 := selfAdjB_spec hf a' b'
    obtain ⟨m, hm⟩ : (2 : ℤ) ∣ jColL (f a') b' - jColR a' (f b') := Int.dvd_of_emod_eq_zero h2
    have : (jColL (f a') b' : K) - (jColR a' (f b') : K) = 0 := by
      have h3 := congrArg (Int.cast : ℤ → K) hm
      push_cast at h3
      rw [h3, show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_mul]
    exact sub_eq_zero.1 this
  exact LinearMap.congr_fun₂ key x y

end Certs

section Invariance

variable [CharP K 2]

theorem jForm_xCoeff_comm (i : Fin d4.rank) {k : ℕ} (hk : k ∈ [1, 2, 3])
    (x y : RootModule d4 K) :
    jForm K (xCoeff d4 K i k x) y = jForm K x (xCoeff d4 K i k y) := by
  refine selfAdj_of_check (f := xCol (Tag.rootCertificate d4) (Tag.stringData d4) i k)
    (fun a => ?_) ?_ x y
  · exact xCoeff_toLabel (Tag.rootCertificate_check d4) K (Tag.stringData_check d4) i k a
  · have h := formCheck_eq
    simp only [formCheck, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.and_eq_true] at h
    exact (h i k hk).1

theorem jForm_yCoeff_comm (i : Fin d4.rank) {k : ℕ} (hk : k ∈ [1, 2, 3])
    (x y : RootModule d4 K) :
    jForm K (yCoeff d4 K i k x) y = jForm K x (yCoeff d4 K i k y) := by
  refine selfAdj_of_check (f := yCol (Tag.rootCertificate d4) (Tag.stringData d4) i k)
    (fun a => ?_) ?_ x y
  · exact yCoeff_toLabel (Tag.rootCertificate_check d4) K (Tag.stringData_check d4) i k a
  · have h := formCheck_eq
    simp only [formCheck, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.and_eq_true] at h
    exact (h i k hk).2

theorem jForm_xOp_comm (i : Fin d4.rank) (c : K) (x y : RootModule d4 K) :
    jForm K (xOp d4 K i c x) y = jForm K x (xOp d4 K i c y) := by
  rw [xOp_eq_sum_xCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk4 : k < 4 := Finset.mem_range.1 hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [xCoeff_zero]
  · rw [jForm_xCoeff_comm i (by interval_cases k <;> simp) x y]

theorem jForm_yOp_comm (i : Fin d4.rank) (c : K) (x y : RootModule d4 K) :
    jForm K (yOp d4 K i c x) y = jForm K x (yOp d4 K i c y) := by
  rw [yOp_eq_sum_yCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk4 : k < 4 := Finset.mem_range.1 hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [yCoeff_zero]
  · rw [jForm_yCoeff_comm i (by interval_cases k <;> simp) x y]

theorem jForm_xOp (i : Fin d4.rank) (c : K) (x y : RootModule d4 K) :
    jForm K (xOp d4 K i c x) (xOp d4 K i c y) = jForm K x y := by
  rw [jForm_xOp_comm, ← Module.End.mul_apply (xOp d4 K i c) (xOp d4 K i c) y,
    xOp_mul_xOp (upTransport d4), CharTwo.add_self_eq_zero, xOp_zero]
  rfl

theorem jForm_yOp (i : Fin d4.rank) (c : K) (x y : RootModule d4 K) :
    jForm K (yOp d4 K i c x) (yOp d4 K i c y) = jForm K x y := by
  rw [jForm_yOp_comm, ← Module.End.mul_apply (yOp d4 K i c) (yOp d4 K i c) y,
    yOp_mul_yOp (downTransport d4), CharTwo.add_self_eq_zero, yOp_zero]
  rfl

end Invariance

@[expose] def jInv (K : Type) [Field K] : Subgroup (ModGL d4 K) where
  carrier := {g | ∀ x y : RootModule d4 K,
    jForm K ((g : Module.End K (RootModule d4 K)) x) ((g : Module.End K (RootModule d4 K)) y) =
      jForm K x y}
  mul_mem' := by
    intro a b ha hb x y
    rw [Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  one_mem' := by
    intro x y
    simp
  inv_mem' := by
    intro a ha x y
    have h1 : ∀ z : RootModule d4 K, (a : Module.End K (RootModule d4 K))
        (((a⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K)) z) = z := fun z => by
      rw [← Module.End.mul_apply, Units.mul_inv]
      rfl
    have := ha (((a⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K)) x)
      (((a⁻¹ : ModGL d4 K) : Module.End K (RootModule d4 K)) y)
    rw [h1, h1] at this
    exact this.symm

section Group

variable [CharP K 2]

theorem adjointGroup_le_jInv : adjointGroup d4 K ≤ jInv K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, h | h⟩
  · intro x y
    rw [h]
    exact jForm_xOp i c x y
  · intro x y
    rw [h]
    exact jForm_yOp i c x y

theorem jForm_invariant (g : adjointGroup d4 K) (x y : RootModule d4 K) :
    jForm K (g • x) (g • y) = jForm K x y :=
  adjointGroup_le_jInv g.2 x y

theorem jForm_smul_left (r : adjointGroup d4 K) (x y : RootModule d4 K) :
    jForm K (r • x) y = jForm K x (r⁻¹ • y) := by
  have := jForm_invariant r x (r⁻¹ • y)
  rwa [smul_inv_smul] at this

end Group

end CFSG.RankThree.PartOne.SEITZ8
