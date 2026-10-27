module

public import CFSG.RankThree.PartOne.SEITZ6.G2Defs
public import CFSG.RankThree.PartOne.SEITZ3.LongRoot

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.SEITZ3

variable {K : Type} [Field K]

@[expose] noncomputable def jLab : Label .G2 → Label .G2 → ℤ
  | .inl i, .inl j => if i = j then 0 else 1
  | .inr α, .inr β => open Classical in if β.1 = -α.1 then 1 else 0
  | _, _ => 0

@[expose] noncomputable def jForm (K : Type) [Field K] : LinearMap.BilinForm K (RootModule .G2 K) :=
  Finsupp.linearCombination K fun a => Finsupp.linearCombination K fun b => (jLab a b : K)

theorem jForm_single (a b : Label .G2) :
    jForm K (Finsupp.single a 1) (Finsupp.single b 1) = (jLab a b : K) := by
  simp [jForm, Finsupp.linearCombination_single]

theorem jLab_comm (a b : Label .G2) : jLab a b = jLab b a := by
  rcases a with i | ⟨α, hα⟩ <;> rcases b with j | ⟨β, hβ⟩
  · simp only [jLab]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · rfl
  · rfl
  · simp only [jLab]
    by_cases h : β = -α
    · have h' : α = -β := by rw [h]; simp
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬ α = -β := fun e => h (by rw [e]; simp)
      rw [ite_eq_right h, ite_eq_right h']

theorem jForm_comm (x y : RootModule .G2 K) : jForm K x y = jForm K y x := by
  have h : LinearMap.flip (jForm K) = jForm K := by
    refine LinearMap.ext_basis Finsupp.basisSingleOne Finsupp.basisSingleOne fun a b => ?_
    simp only [Finsupp.coe_basisSingleOne, LinearMap.flip_apply, jForm_single, jLab_comm b a]
  calc jForm K x y = LinearMap.flip (jForm K) y x := rfl
    _ = jForm K y x := by rw [h]

theorem neg_rt_mem : ∀ p < 12, ∃ q < 12, rt q = -rt p := by decide +kernel

theorem isRoot_neg {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) :
    IsRoot .G2 (-γ) := by
  obtain ⟨p, hp, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  rw [len_roots] at hp
  obtain ⟨q, hq, h⟩ := neg_rt_mem p hp
  exact h ▸ isRoot_rt hq

theorem jForm_rootVec_left (γ : Fin (Tag.rank .G2) → ℤ) (x : RootModule .G2 K) :
    jForm K (rootVec .G2 K (-γ)) x = coordAt γ x := by
  by_cases hγ : IsRoot .G2 γ
  · have hγ' := isRoot_neg hγ
    rw [rootVec_eq_single K hγ']
    induction x using Finsupp.induction_linear with
    | zero => simp [coordAt]
    | add x y hx hy => rw [map_add, hx, hy, coordAt_add]
    | single b r =>
      rw [← Finsupp.smul_single_one b r, map_smul, coordAt_smul]
      congr 1
      rcases b with j | ⟨δ, hδ⟩
      · rw [jForm_single]
        have : Finsupp.single (Sum.inl j : Label .G2) (1 : K) = hVec .G2 K j := rfl
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
  · have h' : ¬ IsRoot .G2 (-γ) := fun h => hγ (by simpa using isRoot_neg h)
    rw [rootVec, dite_eq_right h']
    simp [coordAt, hγ]

theorem jForm_rootVec_left' {γ δ : Fin (Tag.rank .G2) → ℤ} (h : δ = -γ)
    (x : RootModule .G2 K) : jForm K (rootVec .G2 K δ) x = coordAt γ x := by
  subst h
  exact jForm_rootVec_left γ x

theorem jForm_hVec_left (i j : Fin (Tag.rank .G2)) (hij : i ≠ j) (x : RootModule .G2 K) :
    jForm K (hVec .G2 K i) x = x (Sum.inl j) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, Finsupp.add_apply]
  | single b r =>
    rw [← Finsupp.smul_single_one b r, map_smul, Finsupp.smul_apply]
    congr 1
    have : hVec .G2 K i = Finsupp.single (Sum.inl i : Label .G2) 1 := rfl
    rw [this, jForm_single]
    rcases b with j' | δ
    · have hi : i.val < 2 := i.2
      have hj : j.val < 2 := j.2
      have hj' : j'.val < 2 := j'.2
      have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
      by_cases h1 : i = j'
      · subst h1
        simp [jLab, hij]
      · have h2 : j' = j := Fin.ext (by
          have : j'.val ≠ i.val := fun e => h1 (Fin.ext e.symm)
          omega)
        subst h2
        simp [jLab, h1]
    · simp [jLab]

abbrev GIdx : Type := Idx (Tag.rootCertificate .G2)

@[expose] def jIdx : GIdx → GIdx → ℤ
  | .inl i, .inl j => if i = j then 0 else 1
  | .inr m, .inr n =>
    if vecBEq ((Tag.rootCertificate .G2).root n) (-(Tag.rootCertificate .G2).root m) then 1 else 0
  | _, _ => 0

@[expose] def jColL : Col (Tag.rootCertificate .G2) → GIdx → ℤ
  | none, _ => 0
  | some (a, z), b => z * jIdx a b

@[expose] def jColR : GIdx → Col (Tag.rootCertificate .G2) → ℤ
  | _, none => 0
  | a, some (b, z) => z * jIdx a b

@[expose] def gIdxList : List GIdx :=
  (List.finRange (Tag.rank .G2)).map Sum.inl ++
    (List.finRange (Tag.rootCertificate .G2).roots.length).map Sum.inr

@[expose] def selfAdjB (f : GIdx → Col (Tag.rootCertificate .G2)) : Bool :=
  gIdxList.all fun a => gIdxList.all fun b => (jColL (f a) b - jColR a (f b)) % 2 == 0

@[expose] def formCheck : Bool :=
  (List.finRange (Tag.rank .G2)).all fun i => [1, 2, 3].all fun k =>
    selfAdjB (xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i k) &&
      selfAdjB (yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i k)

theorem formCheck_eq : formCheck = true := by decide +kernel

theorem mem_gIdxList (a : GIdx) : a ∈ gIdxList := by
  rcases a with j | m <;> simp [gIdxList]

theorem selfAdjB_spec {f : GIdx → Col (Tag.rootCertificate .G2)} (h : selfAdjB f = true)
    (a b : GIdx) : (jColL (f a) b - jColR a (f b)) % 2 = 0 := by
  simp only [selfAdjB, List.all_eq_true, beq_iff_eq] at h
  exact h a (mem_gIdxList a) b (mem_gIdxList b)

section Certs


theorem jLab_toLabel (a b : GIdx) :
    jLab (toLabel (Tag.rootCertificate_check .G2) a) (toLabel (Tag.rootCertificate_check .G2) b) =
      jIdx a b := by
  rcases a with i | m <;> rcases b with j | n
  · rfl
  · rfl
  · rfl
  · simp only [jLab, jIdx, toLabel]
    by_cases h : (Tag.rootCertificate .G2).root n = -(Tag.rootCertificate .G2).root m
    · rw [ite_eq_left h, ite_eq_left (vecBEq_iff.2 h)]
    · rw [ite_eq_right h, ite_eq_right fun e => h (vecBEq_iff.1 e)]

theorem jForm_toVec_single (u : Col (Tag.rootCertificate .G2)) (b : GIdx) :
    jForm K (toVec (Tag.rootCertificate_check .G2) K u)
      (Finsupp.single (toLabel (Tag.rootCertificate_check .G2) b) 1) = (jColL u b : K) := by
  rcases u with _ | ⟨a, z⟩
  · simp [jColL]
  · rw [toVec_some, map_smul, LinearMap.smul_apply, jForm_single, jLab_toLabel]
    simp [jColL]

theorem jForm_single_toVec (a : GIdx) (u : Col (Tag.rootCertificate .G2)) :
    jForm K (Finsupp.single (toLabel (Tag.rootCertificate_check .G2) a) 1)
      (toVec (Tag.rootCertificate_check .G2) K u) = (jColR a u : K) := by
  rcases u with _ | ⟨b, z⟩
  · simp [jColR]
  · rw [toVec_some, map_smul, jForm_single, jLab_toLabel]
    simp [jColR]

theorem selfAdj_of_check [CharP K 2] {T : Module.End K (RootModule .G2 K)}
    {f : GIdx → Col (Tag.rootCertificate .G2)}
    (hT : ∀ a, T (Finsupp.single (toLabel (Tag.rootCertificate_check .G2) a) 1) =
      toVec (Tag.rootCertificate_check .G2) K (f a)) (hf : selfAdjB f = true)
    (x y : RootModule .G2 K) : jForm K (T x) y = jForm K x (T y) := by
  have key : (jForm K).compl₁₂ T LinearMap.id = (jForm K).compl₁₂ LinearMap.id T := by
    refine LinearMap.ext_basis Finsupp.basisSingleOne Finsupp.basisSingleOne fun a b => ?_
    obtain ⟨a', rfl⟩ := surjective_toLabel (Tag.rootCertificate_check .G2) a
    obtain ⟨b', rfl⟩ := surjective_toLabel (Tag.rootCertificate_check .G2) b
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

theorem jForm_xCoeff_comm (i : Fin (Tag.rank .G2)) {k : ℕ} (hk : k ∈ [1, 2, 3])
    (x y : RootModule .G2 K) :
    jForm K (xCoeff .G2 K i k x) y = jForm K x (xCoeff .G2 K i k y) := by
  refine selfAdj_of_check (f := xCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i k)
    (fun a => ?_) ?_ x y
  · exact xCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i k a
  · have h := formCheck_eq
    simp only [formCheck, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.and_eq_true] at h
    exact (h i k hk).1

theorem jForm_yCoeff_comm (i : Fin (Tag.rank .G2)) {k : ℕ} (hk : k ∈ [1, 2, 3])
    (x y : RootModule .G2 K) :
    jForm K (yCoeff .G2 K i k x) y = jForm K x (yCoeff .G2 K i k y) := by
  refine selfAdj_of_check (f := yCol (Tag.rootCertificate .G2) (Tag.stringData .G2) i k)
    (fun a => ?_) ?_ x y
  · exact yCoeff_toLabel (Tag.rootCertificate_check .G2) K (Tag.stringData_check .G2) i k a
  · have h := formCheck_eq
    simp only [formCheck, List.all_eq_true, List.mem_finRange, true_implies,
      Bool.and_eq_true] at h
    exact (h i k hk).2

theorem jForm_xOp_comm (i : Fin (Tag.rank .G2)) (c : K) (x y : RootModule .G2 K) :
    jForm K (xOp .G2 K i c x) y = jForm K x (xOp .G2 K i c y) := by
  rw [xOp_eq_sum_xCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk4 : k < 4 := Finset.mem_range.1 hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [xCoeff_zero]
  · rw [jForm_xCoeff_comm i (by interval_cases k <;> simp) x y]

theorem jForm_yOp_comm (i : Fin (Tag.rank .G2)) (c : K) (x y : RootModule .G2 K) :
    jForm K (yOp .G2 K i c x) y = jForm K x (yOp .G2 K i c y) := by
  rw [yOp_eq_sum_yCoeff]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk4 : k < 4 := Finset.mem_range.1 hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [yCoeff_zero]
  · rw [jForm_yCoeff_comm i (by interval_cases k <;> simp) x y]

theorem jForm_xOp (i : Fin (Tag.rank .G2)) (c : K) (x y : RootModule .G2 K) :
    jForm K (xOp .G2 K i c x) (xOp .G2 K i c y) = jForm K x y := by
  rw [jForm_xOp_comm, ← Module.End.mul_apply (xOp .G2 K i c) (xOp .G2 K i c) y,
    xOp_mul_xOp (upTransport .G2), CharTwo.add_self_eq_zero, xOp_zero]
  rfl

theorem jForm_yOp (i : Fin (Tag.rank .G2)) (c : K) (x y : RootModule .G2 K) :
    jForm K (yOp .G2 K i c x) (yOp .G2 K i c y) = jForm K x y := by
  rw [jForm_yOp_comm, ← Module.End.mul_apply (yOp .G2 K i c) (yOp .G2 K i c) y,
    yOp_mul_yOp (downTransport .G2), CharTwo.add_self_eq_zero, yOp_zero]
  rfl

end Invariance

@[expose] def jInv (K : Type) [Field K] : Subgroup (ModGL .G2 K) where
  carrier := {g | ∀ x y : RootModule .G2 K,
    jForm K ((g : Module.End K (RootModule .G2 K)) x) ((g : Module.End K (RootModule .G2 K)) y) =
      jForm K x y}
  mul_mem' := by
    intro a b ha hb x y
    rw [Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, ha, hb]
  one_mem' := by
    intro x y
    simp
  inv_mem' := by
    intro a ha x y
    have h1 : ∀ z : RootModule .G2 K, (a : Module.End K (RootModule .G2 K))
        (((a⁻¹ : ModGL .G2 K) : Module.End K (RootModule .G2 K)) z) = z := fun z => by
      rw [← Module.End.mul_apply, Units.mul_inv]
      rfl
    have := ha (((a⁻¹ : ModGL .G2 K) : Module.End K (RootModule .G2 K)) x)
      (((a⁻¹ : ModGL .G2 K) : Module.End K (RootModule .G2 K)) y)
    rw [h1, h1] at this
    exact this.symm

section Group

variable [CharP K 2]

theorem adjointGroup_le_jInv : adjointGroup .G2 K ≤ jInv K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, h | h⟩
  · intro x y
    rw [h]
    exact jForm_xOp i c x y
  · intro x y
    rw [h]
    exact jForm_yOp i c x y

theorem jForm_invariant (g : adjointGroup .G2 K) (x y : RootModule .G2 K) :
    jForm K (g • x) (g • y) = jForm K x y :=
  adjointGroup_le_jInv g.2 x y

end Group

end CFSG.RankThree.PartOne.SEITZ6
