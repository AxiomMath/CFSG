module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompScalar

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane
open scoped commutatorElement

namespace CFSG.StandardType

namespace CoordSL

section Generic

variable {G : Type*} [Group G]

theorem le_or_commutator_eq_bot_of_normal [Finite G] {L₁ H N : Subgroup G}
    (hcomp : CFSG.Assembly.IsComponentOf L₁ H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    L₁ ≤ N ∨ ⁅L₁, N⁆ = ⊥ := by
  have hLC : L₁ ≤ H := hcomp.1
  have hc :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLC).mp hcomp
  rcases CFSG.LocalAnalysis.ComponentInitial.component_normal_subgroup hc hN with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hLC h)
  · right
    have h' := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hLC h
    rwa [inf_eq_left.mpr hNH] at h'

theorem eq_of_isComponentOf_range {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) (f : Q →* G)
    {L₁ : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L₁ f.range) : L₁ = f.range := by
  have hq := hL.2.2
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hQ f with h | h
  · exfalso
    refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
    have hx1 : x = 1 := by
      have := hL.1 hx
      rwa [h, Subgroup.mem_bot] at this
    have hy1 : y = 1 := by
      have := hL.1 hy
      rwa [h, Subgroup.mem_bot] at this
    rw [hx1, hy1]
  · have hc :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL.1).mp hL
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups h hc.2 with h' | h'
    · exact le_antisymm hL.1 (Subgroup.subgroupOf_eq_top.mp h')
    · exfalso
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      have hxc : (⟨x, hL.1 hx⟩ : f.range) ∈ Subgroup.center f.range :=
        h' (Subgroup.mem_subgroupOf.mpr hx)
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨y, hL.1 hy⟩)).symm

theorem pow_three_le_natCard [Finite G] {p : ℕ} {H : Subgroup G}
    (f : ZMod p × ZMod p × ZMod p → G) (hf : Function.Injective f) (hH : ∀ a, f a ∈ H) :
    p ^ 3 ≤ Nat.card H := by
  have h := Nat.card_le_card_of_injective (fun a => (⟨f a, hH a⟩ : H))
    (fun a b hab => hf (congrArg Subtype.val hab))
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_zmod, ← pow_two, ← pow_succ'] at h

end Generic

section SmallSL

variable {G : Type*} [Group G] {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ}

omit [Finite k] [CharP k 2] in
theorem specialLinear_comm_of_le_one {m : ℕ} (hm : m ≤ 1)
    (A B : Matrix.SpecialLinearGroup (Fin m) k) : A * B = B * A := by
  have : Subsingleton (Fin m) := Fin.subsingleton_iff_le_one.mpr hm
  apply Subtype.ext
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, mul_comm]

theorem quasisimple_of_le_map_coordBlockSL
    (φ : Matrix.SpecialLinearGroup (Fin n) k →* G) {J : Finset (Fin n)} {L₁ : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple L₁) (hL : L₁ ≤ (coordBlockSL k J).map φ) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin J.card) k) := by
  have hrange : (coordBlockSL k J).map φ = (φ.comp (blockSLOn k J)).range := by
    rw [MonoidHom.range_comp, range_blockSLOn]
  rw [hrange] at hL
  have h2 : 2 ≤ J.card := by
    by_contra h1
    refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
    obtain ⟨X, rfl⟩ := hL hx
    obtain ⟨Y, rfl⟩ := hL hy
    rw [← map_mul, ← map_mul, specialLinear_comm_of_le_one (by omega) X Y]
  have h22 : J.card ≠ 2 ∨ Nat.card k ≠ 2 := by
    by_contra h22
    rw [not_or, not_not, not_not] at h22
    have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) k) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable k
        (Or.inl h22.2)
    have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) k) :=
      Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
    have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin J.card) k) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear (K := k)
          (finCongr h22.1)).toMonoidHom)
        (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear (K := k) (finCongr h22.1)).injective
    have hS : Group.IsSolvable (φ.comp (blockSLOn k J)).range :=
      Group.isSolvable_of_surjective (φ.comp (blockSLOn k J)).rangeRestrict_surjective
    exact LinSemisimple.false_of_isQuasisimple_of_le_isSolvable hq hL
  exact CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple J.card k h2
    h22 (Or.inr LinSemisimple.natCard_ne_three)

end SmallSL

section Involution

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

theorem commute_of_map_commute_of_mul_self {G : Type*} [Group G]
    {φ : Matrix.SpecialLinearGroup (Fin n) K →* G}
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    {u t : Matrix.SpecialLinearGroup (Fin n) K} (htt : t * t = 1) (h : φ u * φ t = φ t * φ u) :
    u * t = t * u := by
  have hz : ⁅u, t⁆ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
    refine hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  have h2 := LinSemisimple.sq_commutatorElement_eq_one htt hz
  exact commutatorElement_eq_one_iff_mul_comm.mp (eq_one_of_mem_center_of_sq_eq_one hz h2)

theorem two_eq_zero_adjoinRoot {g : K[X]} [Fact (Irreducible g)] : (2 : AdjoinRoot g) = 0 := by
  rw [← map_ofNat (algebraMap K (AdjoinRoot g)) 2, CharTwo.two_eq_zero, map_zero]

theorem theta_transvection_mul_self {g : K[X]} [Fact (Irreducible g)] {s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (c : AdjoinRoot g) :
    theta g ε (Matrix.SpecialLinearGroup.transvection hij c) *
      theta g ε (Matrix.SpecialLinearGroup.transvection hij c) = 1 := by
  rw [← map_mul, ← Matrix.SpecialLinearGroup.transvection_add, ← two_mul, two_eq_zero_adjoinRoot,
    zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]

end Involution

section ZeroTorus

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ}
  {β : Fin s → ZMod p} {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
  {hC : (rootMat g).det = 1}

@[expose] noncomputable def torusAct' (g : K[X]) [Fact (Irreducible g)] (k : Fin s → ℕ) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)) where
  toFun := torusAct g k
  map_add' x y := Prod.ext (funext fun i => by simp [torusAct, mul_add]) rfl
  map_smul' c x := Prod.ext (funext fun i => by simp [torusAct]) rfl

omit [Fact (Irreducible g)] in
theorem torusAct'_apply [Fact (Irreducible g)] (k : Fin s → ℕ)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) : torusAct' g k x = torusAct g k x :=
  rfl

theorem frameForm_nsMat' (k : Fin s → ℕ) :
    frameForm g ε (SLNS.nsMat ε (rootMat g) k) = torusAct' g k :=
  LinearMap.ext (frameForm_nsMat g ε k)

theorem torusAct_eq_self_of_projN {k : Fin s → ℕ} (hk : ∀ i, β i = 0 → k i = 0)
    {v : (Fin s → AdjoinRoot g) × (Fin r → K)} (hv : projN β v = 0) : torusAct g k v = v := by
  have hv' := projN_eq_zero_iff.mp hv
  refine Prod.ext (funext fun i => ?_) rfl
  change AdjoinRoot.root g ^ k i * v.1 i = v.1 i
  by_cases hi : β i = 0
  · rw [hk i hi, pow_zero, one_mul]
  · rw [hv' i hi, mul_zero]

theorem nsSL_mem_zeroBlock {k : Fin s → ℕ} (hk : ∀ i, β i ≠ 0 → k i = 0) :
    SLNS.nsSL ε hC k ∈ coordBlockSL K (zeroCoords ε β) := by
  have h1 : projN (r := r) β ∘ₗ torusAct' g k = projN β := by
    refine LinearMap.ext fun x => Prod.ext (funext fun i => ?_) rfl
    simp only [LinearMap.comp_apply, torusAct'_apply, projN_apply, torusAct]
    by_cases hi : β i = 0
    · simp [hi]
    · simp [hi, hk i hi]
  have h2 : torusAct' g k ∘ₗ projN (r := r) β = projN β := by
    refine LinearMap.ext fun x => Prod.ext (funext fun i => ?_) rfl
    simp only [LinearMap.comp_apply, torusAct'_apply, projN_apply, torusAct]
    by_cases hi : β i = 0
    · simp [hi]
    · simp [hi, hk i hi]
  refine ⟨?_, ?_⟩
  · apply frameForm_injective g ε
    change frameForm g ε (compIndicator K (zeroCoords ε β) * SLNS.nsMat ε (rootMat g) k) = _
    rw [frameForm_mul, frameForm_compIndicator, frameForm_nsMat']
    exact h1
  · apply frameForm_injective g ε
    change frameForm g ε (SLNS.nsMat ε (rootMat g) k * compIndicator K (zeroCoords ε β)) = _
    rw [frameForm_mul, frameForm_compIndicator, frameForm_nsMat']
    exact h2


theorem comm_zeroBlock_of_torus {k : Fin s → ℕ} (hk : ∀ i, β i = 0 → k i = 0)
    {M : Matrix.SpecialLinearGroup (Fin n) K} (hM : M ∈ coordBlockSL K (zeroCoords ε β)) :
    SLNS.nsSL ε hC k * M = M * SLNS.nsSL ε hC k := by
  obtain ⟨hM1, hM2⟩ := hM
  set φ := frameForm g ε (M : Matrix (Fin n) (Fin n) K) with hφ
  have hP1 : projN (r := r) β ∘ₗ φ = projN β := by
    have h := congrArg (frameForm g ε) hM1
    rwa [frameForm_mul, frameForm_compIndicator] at h
  have hP2 : φ ∘ₗ projN (r := r) β = projN β := by
    have h := congrArg (frameForm g ε) hM2
    rwa [frameForm_mul, frameForm_compIndicator] at h
  have hfixN : ∀ z, projN β z = z → φ z = z := fun z hz => by
    have h := congrArg (fun f => f z) hP2
    simp only [LinearMap.comp_apply, hz] at h
    exact h
  have hkerN : ∀ z, projN β z = 0 → projN β (φ z) = 0 := fun z hz => by
    have h := congrArg (fun f => f z) hP1
    simp only [LinearMap.comp_apply] at h
    rw [h, hz]
  apply Subtype.ext
  apply frameForm_injective g ε
  change frameForm g ε (SLNS.nsMat ε (rootMat g) k * (M : Matrix (Fin n) (Fin n) K)) =
    frameForm g ε ((M : Matrix (Fin n) (Fin n) K) * SLNS.nsMat ε (rootMat g) k)
  rw [frameForm_mul, frameForm_mul, frameForm_nsMat', ← hφ]
  refine frame_ext (fun j x => ?_) (fun w => ?_)
  · simp only [LinearMap.comp_apply, torusAct'_apply]
    by_cases hj : β j = 0
    · have hz : projN β ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) = 0 :=
        projN_eq_zero_iff.mpr fun i hi => by
          have hij : i ≠ j := fun h => hi (h ▸ hj)
          simp [hij]
      rw [torusAct_eq_self_of_projN hk hz, torusAct_eq_self_of_projN hk (hkerN _ hz)]
    · have hz : projN β ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) =
          ((Pi.single j x : Fin s → AdjoinRoot g), (0 : Fin r → K)) :=
        projN_eq_self_iff.mpr ⟨fun i hi => by
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          simp [hij], rfl⟩
      have hz' : projN β (torusAct g k ((Pi.single j x : Fin s → AdjoinRoot g),
          (0 : Fin r → K))) = torusAct g k (Pi.single j x, 0) :=
        projN_eq_self_iff.mpr ⟨fun i hi => by
          have hij : i ≠ j := fun h => hj (h ▸ hi)
          simp [torusAct, hij], rfl⟩
      rw [hfixN _ hz, hfixN _ hz']
  · simp only [LinearMap.comp_apply, torusAct'_apply]
    have hz : projN β ((0 : Fin s → AdjoinRoot g), w) = 0 :=
      projN_eq_zero_iff.mpr fun i _ => rfl
    rw [torusAct_eq_self_of_projN hk hz, torusAct_eq_self_of_projN hk (hkerN _ hz)]

end ZeroTorus

section ClassTorus

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ}
  {β : Fin s → ZMod p} {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}
  {hC : (rootMat g).det = 1}

theorem comm_classBlock_of_torus {c : ZMod p} {k : Fin s → ℕ}
    (hk : ∀ i j, β i = c → β j = c → k i = k j)
    {M : Matrix.SpecialLinearGroup (Fin s) (AdjoinRoot g)}
    (hM : M ∈ coordBlockSL (AdjoinRoot g) (classSet β c)) :
    theta g ε M * SLNS.nsSL ε hC k = SLNS.nsSL ε hC k * theta g ε M := by
  have hM' := mem_coordBlockSL_iff.mp hM
  apply Subtype.ext
  change thetaMat g ε (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) * SLNS.nsMat ε (rootMat g) k =
    SLNS.nsMat ε (rootMat g) k * thetaMat g ε (M : Matrix (Fin s) (Fin s) (AdjoinRoot g))
  rw [← thetaMat_diagonal, ← thetaMat_mul, ← thetaMat_mul]
  congr 1
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i ∈ classSet β c ∧ j ∈ classSet β c
  · rw [hk i j (mem_classSet.mp hij.1) (mem_classSet.mp hij.2), mul_comm]
  · have h1 : i ∉ classSet β c ∨ j ∉ classSet β c := by
      by_contra h
      push Not at h
      exact hij h
    rw [hM' i j h1]
    by_cases hij' : i = j
    · subst hij'
      simp
    · simp [hij']

theorem diag_mem_classBlock [NeZero p] (hζ : AdjoinRoot.root g ^ p = 1) {c : ZMod p}
    {t : Fin s → ZMod p} (hsupp : ∀ i, β i ≠ c → t i = 0) (hsum : ∑ i, t i = 0) :
    ∃ D ∈ coordBlockSL (AdjoinRoot g) (classSet β c),
      theta g ε D = SLNS.nsSL ε hC (fun i => (t i).val) := by
  have hdvd : p ∣ ∑ i, (t i).val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
    simpa [ZMod.natCast_zmod_val] using hsum
  have hdet : (Matrix.diagonal fun i => AdjoinRoot.root g ^ (t i).val).det = 1 := by
    rw [Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
    obtain ⟨m, hm⟩ := hdvd
    rw [hm, pow_mul, hζ, one_pow]
  set D : Matrix.SpecialLinearGroup (Fin s) (AdjoinRoot g) := ⟨_, hdet⟩ with hD
  refine ⟨D, ?_, Subtype.ext (thetaMat_diagonal g ε fun i => (t i).val)⟩
  rw [mem_coordBlockSL_iff]
  intro i j hij
  change Matrix.diagonal (fun i => AdjoinRoot.root g ^ (t i).val) i j = _
  rw [Matrix.diagonal_apply]
  by_cases hij' : i = j
  · subst hij'
    have hi : β i ≠ c := by
      rcases hij with h | h <;> exact fun h' => h (mem_classSet.mpr h')
    simp [hsupp i hi]
  · simp [hij']

theorem four_le_natCard_adjoinRoot [Finite K] (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
    (hp3 : 3 ≤ p) : 4 ≤ Nat.card (AdjoinRoot g) := by
  have : Finite (AdjoinRoot g) := finite_adjoinRoot
  have hp0 : p ≠ 0 := by omega
  set u : (AdjoinRoot g)ˣ := (hprim.isUnit hp0).unit with hu
  have hu' : IsPrimitiveRoot u p := IsPrimitiveRoot.coe_units_iff.mp (by simpa [hu] using hprim)
  have hdvd : p ∣ Nat.card (AdjoinRoot g)ˣ := hu'.eq_orderOf ▸ orderOf_dvd_natCard u
  rw [Nat.card_units] at hdvd
  have h2 : 1 < Nat.card (AdjoinRoot g) := Finite.one_lt_card
  have h3 : p ≤ Nat.card (AdjoinRoot g) - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

end ClassTorus

end CoordSL

end CFSG.StandardType
