module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallStars

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsItem316Small

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Matrix Equiv
open scoped commutatorElement

section Weight

variable {n : ℕ}

@[expose] def wt (y : Fin n → ZMod 2) : ℕ := ∑ i, (y i).val

@[expose] def heartQ (y : Fin n → ZMod 2) : ZMod 2 := ((wt y / 2 : ℕ) : ZMod 2)

@[expose] def permVec (σ : Perm (Fin n)) (y : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => y (σ⁻¹ i)

theorem permVec_add (σ : Perm (Fin n)) (y z : Fin n → ZMod 2) :
    permVec σ (y + z) = permVec σ y + permVec σ z := rfl

theorem permVec_one (y : Fin n → ZMod 2) : permVec 1 y = y := rfl

theorem permVec_mul (σ τ : Perm (Fin n)) (y : Fin n → ZMod 2) :
    permVec (σ * τ) y = permVec σ (permVec τ y) := by
  funext i
  simp [permVec, _root_.mul_inv_rev, Perm.mul_apply]

theorem permVec_allOnes (σ : Perm (Fin n)) : permVec σ (allOnes n) = allOnes n := rfl

theorem permVec_single (σ : Perm (Fin n)) (i : Fin n) :
    permVec σ (Pi.single i 1) = Pi.single (σ i) 1 := by
  funext m
  simp only [permVec, Pi.single_apply, Perm.inv_eq_iff_eq]

theorem sum_permVec (σ : Perm (Fin n)) (y : Fin n → ZMod 2) :
    ∑ i, permVec σ y i = ∑ i, y i :=
  Equiv.sum_comp σ⁻¹ y

theorem wt_permVec (σ : Perm (Fin n)) (y : Fin n → ZMod 2) : wt (permVec σ y) = wt y :=
  Equiv.sum_comp σ⁻¹ (fun i => (y i).val)

theorem heartQ_permVec (σ : Perm (Fin n)) (y : Fin n → ZMod 2) :
    heartQ (permVec σ y) = heartQ y := by
  rw [heartQ, heartQ, wt_permVec]

theorem heartQ_zero : heartQ (0 : Fin n → ZMod 2) = 0 := by
  simp [heartQ, wt]

theorem zmod_two_val_add_one (t : ZMod 2) : (t + 1).val + t.val = 1 := by
  revert t; decide

theorem zmod_two_eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t; decide

theorem zmod_two_neg_add_one_add (t : ZMod 2) : -(t + 1) + t = 1 := by
  revert t; decide

theorem wt_add_allOnes (y : Fin n → ZMod 2) : wt (y + allOnes n) + wt y = n := by
  simp only [wt, ← Finset.sum_add_distrib, Pi.add_apply, allOnes, zmod_two_val_add_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem sum_eq_wt (y : Fin n → ZMod 2) : ∑ i, y i = ((wt y : ℕ) : ZMod 2) := by
  simp [wt]

theorem two_dvd_wt {y : Fin n → ZMod 2} (hy : ∑ i, y i = 0) : 2 ∣ wt y := by
  rw [sum_eq_wt] at hy
  exact (ZMod.natCast_eq_zero_iff _ _).1 hy

theorem heartQ_add_allOnes (h4 : 4 ∣ n) {y : Fin n → ZMod 2} (hy : ∑ i, y i = 0) :
    heartQ (y + allOnes n) = heartQ y := by
  have h1 := wt_add_allOnes y
  have h2 := two_dvd_wt hy
  rw [heartQ, heartQ, ZMod.natCast_eq_natCast_iff']
  omega

theorem mem_zmultiples_allOnes {z : Fin n → ZMod 2} :
    z ∈ AddSubgroup.zmultiples (allOnes n) ↔ z = 0 ∨ z = allOnes n := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have hk : k • allOnes n = fun _ => ((k : ZMod 2)) := by
      funext i
      simp [allOnes]
    rw [hk]
    rcases zmod_two_eq_zero_or_one (k : ZMod 2) with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨0, zero_zsmul _⟩
    · exact ⟨1, one_zsmul _⟩

theorem mem_evenWeightOnes {z : evenWeight n} :
    z ∈ evenWeightOnes n ↔ (z : Fin n → ZMod 2) = 0 ∨ (z : Fin n → ZMod 2) = allOnes n := by
  rw [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, mem_zmultiples_allOnes]

theorem mk_eq_of_eq_or {a b : evenWeight n}
    (h : (a : Fin n → ZMod 2) = b ∨ (a : Fin n → ZMod 2) = b + allOnes n) :
    (a : altHeart n) = (b : altHeart n) := by
  rw [QuotientAddGroup.eq, mem_evenWeightOnes]
  rcases h with h | h
  · left
    simp [h]
  · right
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, h]
    funext i
    simp only [Pi.add_apply, Pi.neg_apply, allOnes]
    exact zmod_two_neg_add_one_add _

theorem mk_evenWeightPerm_eq (σ : Perm (Fin n)) {a b : evenWeight n}
    (h : (a : altHeart n) = (b : altHeart n)) :
    (evenWeightPerm σ a : altHeart n) = (evenWeightPerm σ b : altHeart n) := by
  rw [QuotientAddGroup.eq, mem_evenWeightOnes] at h ⊢
  have e : ((-(evenWeightPerm σ a) + evenWeightPerm σ b : evenWeight n) : Fin n → ZMod 2) =
      permVec σ ((-a + b : evenWeight n) : Fin n → ZMod 2) := rfl
  rw [e]
  rcases h with h | h
  · left
    rw [h]
    rfl
  · right
    rw [h, permVec_allOnes]

end Weight

theorem commutator_perm_eq_alternatingGroup (n : ℕ) :
    commutator (Perm (Fin n)) = alternatingGroup (Fin n) := by
  refine le_antisymm alternatingGroup.commutator_perm_le ?_
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  obtain ⟨τ, hτ⟩ := isConj_iff.1
    (Equiv.Perm.isConj_iff_cycleType_eq.2 (Equiv.Perm.cycleType_inv σ).symm)
  have h3 : σ ^ 3 = 1 := by
    rw [← Equiv.Perm.IsThreeCycle.orderOf hσ]
    exact pow_orderOf_eq_one σ
  have hc : ⁅τ, σ⁆ = σ := by
    rw [commutatorElement_def, hτ]
    calc σ⁻¹ * σ⁻¹ = σ⁻¹ * σ⁻¹ * σ ^ 3 := by rw [h3, mul_one]
      _ = σ := by group
  rw [SetLike.mem_coe, _root_.commutator_def, ← hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top τ) (Subgroup.mem_top σ)

@[expose] def colMatrix {α β : Type} (S : β → α → ZMod 2) : Matrix α β (ZMod 2) :=
  Matrix.of fun i k => S k i

theorem colMatrix_mulVec {α β : Type} [Fintype β] (S : β → α → ZMod 2) (y : β → ZMod 2) :
    colMatrix S *ᵥ y = ∑ k, y k • S k := by
  funext i
  simp [colMatrix, mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem matrix_ext_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι (ZMod 2)}
    (h : ∀ w, A *ᵥ w = B *ᵥ w) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

@[expose] def isoGroupOf {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2) :
    Subgroup (GL ι (ZMod 2)) :=
  Subgroup.closure {A : GL ι (ZMod 2) | ∀ v, Q ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Q v}

structure HeartModel (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Q : (ι → ZMod 2) → ZMod 2) where
  S : ι → Fin n → ZMod 2
  c : Fin n → ι → ZMod 2
  three_le : 3 ≤ n
  odd_or_four_dvd : Odd n ∨ 4 ∣ n
  CP : colMatrix c * colMatrix S = 1
  sum_S : ∀ k, ∑ i, S k i = 0
  PC : ∀ y : Fin n → ZMod 2, ∑ i, y i = 0 →
    colMatrix S *ᵥ (colMatrix c *ᵥ y) = y ∨ colMatrix S *ᵥ (colMatrix c *ᵥ y) = y + allOnes n
  sum_c : ∑ _i : Fin n, (1 : ZMod 2) = 0 → ∑ i, c i = 0
  Q_eq : ∀ w, Q w = heartQ (colMatrix S *ᵥ w)
  hA : ∀ i j, i ≠ j → Q (c i + c j) = 1
  hB : ∀ w, Q w = 1 → ∃ i j, i ≠ j ∧ w = c i + c j
  hS2 : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    Q (c i + c j + c k + c l) ≠ 1
  hS3 : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    c i + c j + c k + c l ≠ 0

namespace HeartModel

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Q : (ι → ZMod 2) → ZMod 2}
  (M : HeartModel n ι Q)

abbrev P : Matrix (Fin n) ι (ZMod 2) := colMatrix M.S

abbrev C : Matrix ι (Fin n) (ZMod 2) := colMatrix M.c

theorem C_single (i : Fin n) : M.C *ᵥ Pi.single i 1 = M.c i := by
  rw [colMatrix_mulVec, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem C_P (w : ι → ZMod 2) : M.C *ᵥ (M.P *ᵥ w) = w := by
  rw [mulVec_mulVec, M.CP, one_mulVec]

theorem sum_P (w : ι → ZMod 2) : ∑ i, (M.P *ᵥ w) i = 0 := by
  rw [colMatrix_mulVec]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, M.sum_S]

theorem P_mem (w : ι → ZMod 2) : M.P *ᵥ w ∈ evenWeight n := M.sum_P w

theorem C_ones (h : ∑ _i : Fin n, (1 : ZMod 2) = 0) : M.C *ᵥ allOnes n = 0 := by
  rw [colMatrix_mulVec]
  simpa [allOnes] using M.sum_c h

include M in
theorem four_dvd (h : ∑ _i : Fin n, (1 : ZMod 2) = 0) : 4 ∣ n := by
  rcases M.odd_or_four_dvd with ho | h4
  · exfalso
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    have := (ZMod.natCast_eq_zero_iff n 2).1 h
    obtain ⟨k, rfl⟩ := ho
    omega
  · exact h4

theorem PC' {y : Fin n → ZMod 2} (hy : ∑ i, y i = 0) :
    M.P *ᵥ (M.C *ᵥ y) = y ∨
      (M.P *ᵥ (M.C *ᵥ y) = y + allOnes n ∧ ∑ _i : Fin n, (1 : ZMod 2) = 0) := by
  rcases M.PC y hy with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    have := M.sum_P (M.C *ᵥ y)
    rw [h] at this
    simpa [Finset.sum_add_distrib, hy, allOnes] using this

theorem C_perm_PC (σ : Perm (Fin n)) {y : Fin n → ZMod 2} (hy : ∑ i, y i = 0) :
    M.C *ᵥ permVec σ (M.P *ᵥ (M.C *ᵥ y)) = M.C *ᵥ permVec σ y := by
  rcases M.PC' hy with h | ⟨h, hones⟩
  · rw [h]
  · rw [h, permVec_add, permVec_allOnes, mulVec_add, M.C_ones hones, add_zero]

@[expose] noncomputable def ρlin (σ : Perm (Fin n)) :
    (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
  M.C.mulVecLin ∘ₗ LinearMap.funLeft (ZMod 2) (ZMod 2) (⇑σ⁻¹) ∘ₗ M.P.mulVecLin

theorem ρlin_apply (σ : Perm (Fin n)) (w : ι → ZMod 2) :
    M.ρlin σ w = M.C *ᵥ permVec σ (M.P *ᵥ w) := rfl

theorem toMatrix'_ρlin_mulVec (σ : Perm (Fin n)) (w : ι → ZMod 2) :
    LinearMap.toMatrix' (M.ρlin σ) *ᵥ w = M.C *ᵥ permVec σ (M.P *ᵥ w) := by
  rw [LinearMap.toMatrix'_mulVec, ρlin_apply]

@[expose] noncomputable def ρhom : Perm (Fin n) →* Matrix ι ι (ZMod 2) where
  toFun σ := LinearMap.toMatrix' (M.ρlin σ)
  map_one' := matrix_ext_mulVec fun w => by
    rw [toMatrix'_ρlin_mulVec, permVec_one, C_P, one_mulVec]
  map_mul' σ τ := matrix_ext_mulVec fun w => by
    rw [← mulVec_mulVec, toMatrix'_ρlin_mulVec, toMatrix'_ρlin_mulVec, toMatrix'_ρlin_mulVec,
      M.C_perm_PC σ ((sum_permVec τ _).trans (M.sum_P w)), permVec_mul]

@[expose] noncomputable def ρ : Perm (Fin n) →* GL ι (ZMod 2) :=
  M.ρhom.toHomUnits

theorem ρ_mulVec (σ : Perm (Fin n)) (w : ι → ZMod 2) :
    ((M.ρ σ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w = M.C *ᵥ permVec σ (M.P *ᵥ w) :=
  M.toMatrix'_ρlin_mulVec σ w

theorem ρ_C (σ : Perm (Fin n)) {y : Fin n → ZMod 2} (hy : ∑ i, y i = 0) :
    ((M.ρ σ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ (M.C *ᵥ y) = M.C *ᵥ permVec σ y := by
  rw [ρ_mulVec, M.C_perm_PC σ hy]

theorem sum_single_add_single (i j : Fin n) :
    ∑ m, (Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) : Fin n → ZMod 2) m = 0 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    if_true]
  decide

theorem ρ_c (σ : Perm (Fin n)) (i j : Fin n) :
    ((M.ρ σ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ (M.c i + M.c j) =
      M.c (σ i) + M.c (σ j) := by
  rw [← M.C_single i, ← M.C_single j, ← mulVec_add, M.ρ_C σ (sum_single_add_single i j),
    permVec_add, permVec_single, permVec_single, mulVec_add, M.C_single, M.C_single]

theorem Q_ρ (σ : Perm (Fin n)) (w : ι → ZMod 2) :
    Q (((M.ρ σ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w) = Q w := by
  rw [M.Q_eq, M.Q_eq, ρ_mulVec]
  have hy : ∑ i, permVec σ (M.P *ᵥ w) i = 0 := (sum_permVec σ _).trans (M.sum_P w)
  rcases M.PC' hy with h | ⟨h, hones⟩
  · rw [h, heartQ_permVec]
  · rw [h, heartQ_add_allOnes (four_dvd M hones) hy, heartQ_permVec]

theorem charTwo (v : ι → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero (v i)

include M in
theorem Q_zero : Q 0 = 0 := by
  rw [M.Q_eq, mulVec_zero, heartQ_zero]

theorem exists_three (hn : 3 ≤ n) (i : Fin n) : ∃ j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  by_cases h0 : i.val = 0
  · exact ⟨⟨1, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff, h0], by simp [Fin.ext_iff, h0],
      by simp [Fin.ext_iff]⟩
  · by_cases h1 : i.val = 1
    · exact ⟨⟨0, by omega⟩, ⟨2, by omega⟩, by simp [Fin.ext_iff, h1],
        by simp [Fin.ext_iff, h1], by simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff, h0],
        by simp [Fin.ext_iff, h1], by simp [Fin.ext_iff]⟩

theorem C_eq_sum (a : Fin n) {y : Fin n → ZMod 2} (hy : ∑ i, y i = 0) :
    M.C *ᵥ y = ∑ j, y j • (M.c a + M.c j) := by
  rw [colMatrix_mulVec]
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hy, zero_smul, zero_add]

theorem eq_of_agree (a : Fin n) {B B' : Matrix ι ι (ZMod 2)}
    (h : ∀ j, B *ᵥ (M.c a + M.c j) = B' *ᵥ (M.c a + M.c j)) : B = B' := by
  refine matrix_ext_mulVec fun w => ?_
  rw [← M.C_P w, M.C_eq_sum a (M.sum_P w), mulVec_sum, mulVec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_smul, mulVec_smul, h j]

theorem exists_ρ_eq (A : GL ι (ZMod 2))
    (hA : ∀ v, Q ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Q v) : ∃ σ, M.ρ σ = A := by
  have hn := M.three_le
  let a : Fin n := ⟨0, by omega⟩
  let b₁ : Fin n := ⟨1, by omega⟩
  let b₂ : Fin n := ⟨2, by omega⟩
  have h1 : a ≠ b₁ := by simp [a, b₁, Fin.ext_iff]
  have h2 : a ≠ b₂ := by simp [a, b₂, Fin.ext_iff]
  have h12 : b₁ ≠ b₂ := by simp [b₁, b₂, Fin.ext_iff]
  let g : (ι → ZMod 2) →+ (ι → ZMod 2) := (A : Matrix ι ι (ZMod 2)).mulVecLin.toAddMonoidHom
  have hg : Function.Injective g := by
    intro v v' h
    have h' := congrArg (fun u => ((A⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ u) h
    simp only [g, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, mulVec_mulVec] at h'
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, one_mulVec] at h'
  obtain ⟨σ, hσ⟩ := exists_perm_of_isometry Q M.c charTwo (Q_zero M) M.hA M.hB M.hS2 M.hS3
    h1 h2 h12 g hg hA
  refine ⟨σ, Units.ext (M.eq_of_agree a fun j => ?_)⟩
  rw [M.ρ_c σ a j]
  exact (hσ j).symm

theorem range_ρ : M.ρ.range = isoGroupOf Q := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨σ, rfl⟩
    exact Subgroup.subset_closure (M.Q_ρ σ)
  · rw [isoGroupOf, Subgroup.closure_le]
    intro A hA
    obtain ⟨σ, hσ⟩ := M.exists_ρ_eq A hA
    exact ⟨σ, hσ⟩

theorem ρ_injective : Function.Injective M.ρ := by
  refine (injective_iff_map_eq_one M.ρ).2 fun σ hσ => ?_
  have hfix : ∀ i j, M.c (σ i) + M.c (σ j) = M.c i + M.c j := by
    intro i j
    rw [← M.ρ_c σ i j, hσ, Units.val_one, one_mulVec]
  ext i
  obtain ⟨j, k, hij, hik, hjk⟩ := exists_three M.three_le i
  have e1 := pair_cases Q M.c charTwo (Q_zero M) M.hA M.hS3 (σ.injective.ne hij) hij (hfix i j)
  have e2 := pair_cases Q M.c charTwo (Q_zero M) M.hA M.hS3 (σ.injective.ne hik) hik (hfix i k)
  rcases e1 with ⟨h, -⟩ | ⟨h, -⟩
  · exact congrArg Fin.val h
  · rcases e2 with ⟨h', -⟩ | ⟨h', -⟩
    · exact congrArg Fin.val h'
    · exact absurd (h.symm.trans h') hjk

theorem commutator_isoGroup :
    ⁅isoGroupOf Q, isoGroupOf Q⁆ = (alternatingGroup (Fin n)).map M.ρ := by
  rw [← M.range_ρ, MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    ← commutator_perm_eq_alternatingGroup, _root_.commutator_def]

@[expose] noncomputable def φ : ↥⁅isoGroupOf Q, isoGroupOf Q⁆ ≃* alternatingGroup (Fin n) :=
  (MulEquiv.subgroupCongr M.commutator_isoGroup).trans
    ((alternatingGroup (Fin n)).equivMapOfInjective M.ρ M.ρ_injective).symm

theorem ρ_φ (g : ↥⁅isoGroupOf Q, isoGroupOf Q⁆) :
    M.ρ (M.φ g : Perm (Fin n)) = (g : GL ι (ZMod 2)) := by
  have h := Subgroup.coe_equivMapOfInjective_apply (alternatingGroup (Fin n)) M.ρ M.ρ_injective
    (M.φ g)
  rw [← h]
  simp [φ]

@[expose] noncomputable def ψhom : (ι → ZMod 2) →+ altHeart n :=
  (QuotientAddGroup.mk' (evenWeightOnes n)).comp
    (AddMonoidHom.codRestrict M.P.mulVecLin.toAddMonoidHom (evenWeight n) M.P_mem)

theorem ψhom_apply (w : ι → ZMod 2) :
    M.ψhom w = ((⟨M.P *ᵥ w, M.P_mem w⟩ : evenWeight n) : altHeart n) := rfl

theorem ψhom_C {y : Fin n → ZMod 2} (hy : ∑ i, y i = 0) :
    M.ψhom (M.C *ᵥ y) = ((⟨y, hy⟩ : evenWeight n) : altHeart n) := by
  rw [ψhom_apply]
  apply mk_eq_of_eq_or
  rcases M.PC' hy with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem ψhom_bijective : Function.Bijective M.ψhom := by
  refine ⟨(injective_iff_map_eq_zero M.ψhom).2 fun w hw => ?_, fun q => ?_⟩
  · rw [ψhom_apply, QuotientAddGroup.eq_zero_iff, mem_evenWeightOnes] at hw
    rcases hw with h | h
    · rw [← M.C_P w]
      change M.C *ᵥ (M.P *ᵥ w) = 0
      rw [show M.P *ᵥ w = 0 from h, mulVec_zero]
    · have hones : ∑ _i : Fin n, (1 : ZMod 2) = 0 := by
        have := M.sum_P w
        rw [show M.P *ᵥ w = allOnes n from h] at this
        exact this
      rw [← M.C_P w]
      change M.C *ᵥ (M.P *ᵥ w) = 0
      rw [show M.P *ᵥ w = allOnes n from h, M.C_ones hones]
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨M.C *ᵥ (x : Fin n → ZMod 2), M.ψhom_C x.2⟩

@[expose] noncomputable def ψ : (ι → ZMod 2) ≃+ altHeart n :=
  AddEquiv.ofBijective M.ψhom M.ψhom_bijective

theorem ψ_apply (w : ι → ZMod 2) : M.ψ w = M.ψhom w := rfl

theorem intertwine (g : ↥⁅isoGroupOf Q, isoGroupOf Q⁆) (w : ι → ZMod 2) (x : evenWeight n)
    (hx : M.ψ w = (x : altHeart n)) :
    M.ψ (((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w) =
      (evenWeightPerm (M.φ g : Perm (Fin n)) x : altHeart n) := by
  rw [← M.ρ_φ g, ψ_apply, ρ_mulVec]
  have hy : ∑ i, permVec (M.φ g : Perm (Fin n)) (M.P *ᵥ w) i = 0 :=
    (sum_permVec _ _).trans (M.sum_P w)
  rw [M.ψhom_C hy]
  rw [ψ_apply, ψhom_apply] at hx
  exact mk_evenWeightPerm_eq (M.φ g : Perm (Fin n)) hx

end HeartModel

end CFSG.RankThree.PartTwo.Sec19.SimsItem316Small
