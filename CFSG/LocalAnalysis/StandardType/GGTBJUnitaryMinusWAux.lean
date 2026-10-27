module

public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenWeyl

import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.SpJoin

open Multiplicative

variable {r p : ℕ}

private noncomputable def flipCoords (r p : ℕ) (T : Finset (Fin r)) :
    Equiv.Perm (Fin r → Multiplicative (ZMod p)) where
  toFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  invFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  left_inv v := by funext t; by_cases h : t ∈ T <;> simp [h]
  right_inv v := by funext t; by_cases h : t ∈ T <;> simp [h]

@[simp] private theorem flipCoords_apply (r p : ℕ) (T : Finset (Fin r))
    (v : Fin r → Multiplicative (ZMod p)) (t : Fin r) :
    flipCoords r p T v t = if t ∈ T then (v t)⁻¹ else v t := rfl

private theorem flipCoords_mem_spSignedGroup (T : Finset (Fin r)) :
    flipCoords r p T ∈ spSignedGroup r p := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      have h : flipCoords r p ∅ = 1 := by
        ext v t
        simp [flipCoords_apply]
      rw [h]
      exact Subgroup.one_mem _
  | insert a T ha ih =>
      have hstep : flipCoords r p (insert a T) = coordInv r p a * flipCoords r p T := by
        ext v t
        rw [flipCoords_apply, Equiv.Perm.mul_apply, coordInv_apply]
        by_cases ht : t = a
        · subst ht
          simp [ha]
        · rw [Function.update_apply, if_neg ht, flipCoords_apply]
          simp [Finset.mem_insert, ht]
      rw [hstep]
      exact Subgroup.mul_mem _ (coordInv_mem_spSignedGroup a) ih

theorem exists_mem_spSignedGroup_flip (T : Finset (Fin r)) :
    ∃ w ∈ spSignedGroup r p, ∀ v i, w v i = if i ∈ T then (v i)⁻¹ else v i :=
  ⟨flipCoords r p T, flipCoords_mem_spSignedGroup T, fun _ _ => rfl⟩

theorem exists_mem_spSignedGroup_coord (π : Equiv.Perm (Fin r)) (T : Finset (Fin r)) :
    ∃ w ∈ spSignedGroup r p, ∀ v i, w v (π i) = if i ∈ T then (v i)⁻¹ else v i := by
  obtain ⟨w₁, hw₁, hval⟩ := exists_mem_spSignedGroup_flip (r := r) (p := p) T
  refine ⟨coordPerm r p π * w₁,
    Subgroup.mul_mem _ (coordPerm_mem_spSignedGroup π) hw₁, fun v i => ?_⟩
  rw [Equiv.Perm.mul_apply, coordPerm_apply]
  rw [Equiv.symm_apply_apply]
  exact hval v i

end CFSG.StandardType.SpJoin

namespace CFSG.StandardType.SuSplitRootGen

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher Multiplicative

variable {n r ε p : ℕ} {K : Type} [Field K]

theorem diagonal_mul_eq_mul_diagonal_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (d : ι → R) (M : Matrix ι ι R)
    (h : ∀ a b, M a b ≠ 0 → d a = d b) : Matrix.diagonal d * M = M * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hab : M a b = 0
  · rw [hab, mul_zero, zero_mul]
  · rw [h a b hab]
    exact mul_comm (d b) (M a b)

theorem map_pow_prime_eq_one {H : Type*} [Monoid H]
    (τ : Multiplicative (Fin r → ZMod p) →* H) (t : Fin r → ZMod p) :
    τ (ofAdd t) ^ p = 1 := by
  have hpt : p • t = 0 := by
    funext i
    show p • t i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← map_pow, show (ofAdd t : Multiplicative (Fin r → ZMod p)) ^ p = ofAdd (p • t) from
    (ofAdd_nsmul p t).symm, hpt]
  simp

theorem hypFrame_ofAdd {G : Type} [Group G] {h : UnitaryFieldData 2 n K}
    (φ : hypSU h r ε →* G) (τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε)
    (t : Fin r → ZMod p) :
    hypFrame φ τ (MulEquiv.piMultiplicative (fun _ : Fin r => ZMod p) (ofAdd t)) =
      φ (τ (ofAdd t)) := rfl

theorem hypFrame_eq_ofAdd {G : Type} [Group G] {h : UnitaryFieldData 2 n K}
    (φ : hypSU h r ε →* G) (τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε)
    (v : Fin r → Multiplicative (ZMod p)) :
    hypFrame φ τ v = φ (τ (ofAdd (fun i => toAdd (v i)))) := by
  have hv : v = MulEquiv.piMultiplicative (fun _ : Fin r => ZMod p)
      (ofAdd (fun i => toAdd (v i))) := by
    funext i
    simp [MulEquiv.piMultiplicative, ofAdd_toAdd, toAdd_ofAdd]
  conv_lhs => rw [hv]
  rw [hypFrame_ofAdd]

@[expose] def constSubgroup {m : ℕ} (p : ℕ) (S : Finset (Fin m)) :
    Subgroup (Fin m → Multiplicative (ZMod p)) where
  carrier := {v | ∀ i ∈ S, ∀ j ∈ S, v i = v j}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb i hi j hj
    rw [Pi.mul_apply, Pi.mul_apply, ha i hi j hj, hb i hi j hj]
  inv_mem' := by
    intro a ha i hi j hj
    rw [Pi.inv_apply, Pi.inv_apply, ha i hi j hj]

theorem mem_constSubgroup {m p : ℕ} {S : Finset (Fin m)}
    {v : Fin m → Multiplicative (ZMod p)} :
    v ∈ constSubgroup p S ↔ ∀ i ∈ S, ∀ j ∈ S, v i = v j := Iff.rfl

@[expose] def trivSubgroup {m : ℕ} (p : ℕ) (S : Finset (Fin m)) :
    Subgroup (Fin m → Multiplicative (ZMod p)) where
  carrier := {v | ∀ i ∈ S, v i = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb i hi
    rw [Pi.mul_apply, ha i hi, hb i hi, mul_one]
  inv_mem' := by
    intro a ha i hi
    rw [Pi.inv_apply, ha i hi, inv_one]

theorem mem_trivSubgroup {m p : ℕ} {S : Finset (Fin m)}
    {v : Fin m → Multiplicative (ZMod p)} :
    v ∈ trivSubgroup p S ↔ ∀ i ∈ S, v i = 1 := Iff.rfl

theorem card_fun_multiplicative {ι : Type*} [Fintype ι] (p : ℕ) :
    Nat.card (ι → Multiplicative (ZMod p)) = p ^ Fintype.card ι := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
  congr 1
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem card_constSubgroup {m p : ℕ} {S : Finset (Fin m)} (hS : S.Nonempty) :
    Nat.card ↥(constSubgroup (p := p) S) = p ^ (m - S.card + 1) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  let f : ↥(constSubgroup (p := p) S) →
      Multiplicative (ZMod p) × (↥(Sᶜ) → Multiplicative (ZMod p)) :=
    fun v => (v.1 i₀, fun i => v.1 i.1)
  let g : Multiplicative (ZMod p) × (↥(Sᶜ) → Multiplicative (ZMod p)) →
      ↥(constSubgroup (p := p) S) :=
    fun q => ⟨fun i => if h : i ∈ S then q.1 else q.2 ⟨i, by simpa using h⟩, by
      intro i hi j hj
      simp only [dif_pos hi, dif_pos hj]⟩
  have hleft : Function.LeftInverse g f := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    funext i
    show (if h : i ∈ S then v i₀ else v ⟨i, _⟩) = v i
    by_cases hi : i ∈ S
    · simp only [dif_pos hi]
      exact (hv i hi i₀ hi₀).symm
    · simp only [dif_neg hi]
  have hright : Function.RightInverse g f := by
    rintro ⟨c, u⟩
    apply Prod.ext
    · show (if h : i₀ ∈ S then c else u ⟨i₀, _⟩) = c
      simp only [dif_pos hi₀]
    · funext i
      show (if h : i.1 ∈ S then c else u ⟨i.1, _⟩) = u i
      simp only [dif_neg (Finset.mem_compl.mp i.2)]
  have hcard : Nat.card ↥(constSubgroup (p := p) S) =
      Nat.card (Multiplicative (ZMod p) × (↥(Sᶜ) → Multiplicative (ZMod p))) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hleft.injective, hright.surjective⟩)
  rw [hcard, Nat.card_prod, card_fun_multiplicative]
  have hz : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hz, ← pow_succ']
  congr 1
  rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]

theorem card_trivSubgroup {m p : ℕ} {S : Finset (Fin m)} :
    Nat.card ↥(trivSubgroup (p := p) S) = p ^ (m - S.card) := by
  classical
  let f : ↥(trivSubgroup (p := p) S) → (↥(Sᶜ) → Multiplicative (ZMod p)) :=
    fun v i => v.1 i.1
  let g : (↥(Sᶜ) → Multiplicative (ZMod p)) → ↥(trivSubgroup (p := p) S) :=
    fun u => ⟨fun i => if h : i ∈ S then 1 else u ⟨i, by simpa using h⟩, by
      intro i hi
      simp only [dif_pos hi]⟩
  have hleft : Function.LeftInverse g f := by
    rintro ⟨v, hv⟩
    apply Subtype.ext
    funext i
    show (if h : i ∈ S then (1 : Multiplicative (ZMod p)) else v ⟨i, _⟩) = v i
    by_cases hi : i ∈ S
    · simp only [dif_pos hi]
      exact (hv i hi).symm
    · simp only [dif_neg hi]
  have hright : Function.RightInverse g f := by
    intro u
    funext i
    show (if h : i.1 ∈ S then (1 : Multiplicative (ZMod p)) else u ⟨i.1, _⟩) = u i
    simp only [dif_neg (Finset.mem_compl.mp i.2)]
  have hcard : Nat.card ↥(trivSubgroup (p := p) S) =
      Nat.card (↥(Sᶜ) → Multiplicative (ZMod p)) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hleft.injective, hright.surjective⟩)
  rw [hcard, card_fun_multiplicative]
  congr 1
  rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]

theorem coe_leviSU_matrix (h : UnitaryFieldData 2 n K)
    (A : SpecialLinearGroup (Fin r) K) :
    (((leviSU h ε A : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      blk3 ((A : Matrix (Fin r) (Fin r) K)) 0 0 1 0
        (leviDual h (SpecialLinearGroup.toGL A)) := by
  rw [coe_leviSU, coe_leviGL, SpecialLinearGroup.coe_GL_coe_matrix]

theorem leviDual_apply (h : UnitaryFieldData 2 n K) (A : SpecialLinearGroup (Fin r) K)
    (i j : Fin r) :
    leviDual h (SpecialLinearGroup.toGL A) i j =
      h.bar (((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) j i) := by
  have hinv : ((SpecialLinearGroup.toGL A)⁻¹ : GL (Fin r) K) = SpecialLinearGroup.toGL A⁻¹ :=
    (map_inv (SpecialLinearGroup.toGL) A).symm
  rw [leviDual, hinv, SpecialLinearGroup.coe_GL_coe_matrix, Matrix.transpose_apply]
  rfl

theorem leviSU_commute_splitTorus (h : UnitaryFieldData 2 n K) {ζ : K}
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ)
    {S : Finset (Fin r)} {A : SpecialLinearGroup (Fin r) K}
    (hA : A ∈ CFSG.RankThree.CALinearPlane.coordBlockSL K S) {t : Fin r → ZMod p}
    (ht : ∀ i ∈ S, ∀ j ∈ S, t i = t j) :
    leviSU h ε A * τ (ofAdd t) = τ (ofAdd t) * leviSU h ε A := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hτ t,
    coe_leviSU_matrix]
  refine (diagonal_mul_eq_mul_diagonal_of_support (splitEntries ζ t) _ ?_).symm
  intro a b hab
  rcases a with i | k | i <;> rcases b with j | l | j
  · simp only [blk3_inl_inl] at hab
    simp only [splitEntries]
    by_cases hij : i = j
    · subst hij; rfl
    · have hi : i ∈ S := by
        by_contra hi
        rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA i j (Or.inl hi)] at hab
        simp [hij] at hab
      have hj : j ∈ S := by
        by_contra hj
        rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA i j (Or.inr hj)] at hab
        simp [hij] at hab
      rw [ht i hi j hj]
  · exact absurd hab (by simp)
  · exact absurd hab (by simp)
  · exact absurd hab (by simp)
  · simp only [splitEntries]
  · exact absurd hab (by simp)
  · exact absurd hab (by simp)
  · exact absurd hab (by simp)
  · simp only [blk3_inr_inr_inr_inr] at hab
    simp only [splitEntries]
    have hne : ((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) j i ≠ 0 := by
      intro h0
      apply hab
      rw [leviDual_apply, h0, map_zero]
    by_cases hij : i = j
    · subst hij; rfl
    · have hi : i ∈ S := by
        by_contra hi
        have h1 := CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp
          (Subgroup.inv_mem (CFSG.RankThree.CALinearPlane.coordBlockSL K S) hA) j i (Or.inr hi)
        rw [h1, if_neg (Ne.symm hij)] at hne
        exact hne rfl
      have hj : j ∈ S := by
        by_contra hj
        have h1 := CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp
          (Subgroup.inv_mem (CFSG.RankThree.CALinearPlane.coordBlockSL K S) hA) j i (Or.inl hj)
        rw [h1, if_neg (Ne.symm hij)] at hne
        exact hne rfl
      rw [ht i hi j hj]

theorem hypBlock_mono {h : UnitaryFieldData 2 n K} {T T' : Set (HypIndex r ε)}
    (hsub : T ⊆ T') : hypBlock h T ≤ hypBlock h T' := by
  intro g hg
  rw [mem_hypBlock] at hg ⊢
  intro a b hab
  exact hg a b (by
    rcases hab with ha | hb
    · exact Or.inl fun hT => ha (hsub hT)
    · exact Or.inr fun hT => hb (hsub hT))

theorem lineCoords_subset_zeroCoords {S : Finset (Fin r)} {i : Fin r} (hi : i ∈ S) :
    lineCoords (ε := ε) i ⊆ zeroCoords (ε := ε) S := by
  intro a ha
  simp only [lineCoords, Set.mem_setOf_eq] at ha
  simp only [zeroCoords, Set.mem_setOf_eq]
  rcases ha with rfl | ⟨k, rfl⟩ | rfl
  · exact Or.inl ⟨i, hi, rfl⟩
  · exact Or.inr (Or.inl ⟨k, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, hi, rfl⟩)

theorem mem_zeroCoords_inl {S : Finset (Fin r)} (i : Fin r) :
    (Sum.inl i : HypIndex r ε) ∈ zeroCoords (ε := ε) S ↔ i ∈ S := by
  simp [zeroCoords]

theorem mem_zeroCoords_inr_inr {S : Finset (Fin r)} (i : Fin r) :
    (Sum.inr (Sum.inr i) : HypIndex r ε) ∈ zeroCoords (ε := ε) S ↔ i ∈ S := by
  simp [zeroCoords]

theorem leviSU_mem_hypBlock (h : UnitaryFieldData 2 n K) {S : Finset (Fin r)}
    {A : SpecialLinearGroup (Fin r) K} (hA : A ∈ CFSG.RankThree.CALinearPlane.coordBlockSL K S) :
    leviSU h ε A ∈ hypBlock h (zeroCoords (ε := ε) S) := by
  rw [mem_hypBlock]
  intro a b hab
  rw [coe_leviSU_matrix]
  rcases a with i | k | i <;> rcases b with j | l | j
  · rw [mem_zeroCoords_inl, mem_zeroCoords_inl] at hab
    rw [blk3_inl_inl, CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp hA i j hab]
    simp [Matrix.one_apply]
  · rw [blk3_inl_inr_inl]
    simp
  · rw [blk3_inl_inr_inr]
    simp
  · rw [blk3_inr_inl_inl]
    simp
  · rw [blk3_inr_inl_inr_inl]
    simp [Matrix.one_apply]
  · rw [blk3_inr_inl_inr_inr]
    simp
  · rw [blk3_inr_inr_inl]
    simp
  · rw [blk3_inr_inr_inr_inl]
    simp
  · rw [mem_zeroCoords_inr_inr, mem_zeroCoords_inr_inr] at hab
    rw [blk3_inr_inr_inr_inr, leviDual_apply]
    have hX : ((A⁻¹ : SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) j i =
        if j = i then 1 else 0 :=
      CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff.mp
        (Subgroup.inv_mem (CFSG.RankThree.CALinearPlane.coordBlockSL K S) hA) j i
        (hab.elim Or.inr Or.inl)
    rw [hX]
    by_cases hji : j = i
    · rw [if_pos hji, map_one]
      simp [Matrix.one_apply, hji]
    · rw [if_neg hji, map_zero]
      simp [Ne.symm hji]

theorem hypBlock_commute_diagonal (h : UnitaryFieldData 2 n K) {T : Set (HypIndex r ε)}
    {g : hypSU h r ε} (hg : g ∈ hypBlock h T) {d : HypIndex r ε → K}
    (hd : ∀ a ∈ T, ∀ b ∈ T, d a = d b) :
    (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        diagonal d =
      diagonal d * (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  refine (diagonal_mul_eq_mul_diagonal_of_support d _ ?_).symm
  rintro a b hab
  rw [mem_hypBlock] at hg
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
  · exact hd a ha b hb
  · have hne : a ≠ b := fun h => hb (h ▸ ha)
    rw [hg a b (Or.inr hb)] at hab
    simp [hne] at hab
  · have hne : a ≠ b := fun h => ha (h ▸ hb)
    rw [hg a b (Or.inl ha)] at hab
    simp [hne] at hab
  · rw [hg a b (Or.inl ha)] at hab
    by_cases hab' : a = b
    · subst hab'; rfl
    · simp [hab'] at hab

end CFSG.StandardType.SuSplitRootGen

end
