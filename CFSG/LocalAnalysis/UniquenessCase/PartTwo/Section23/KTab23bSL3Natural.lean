module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD
public import CFSG.Quasithin.H13.A5S1521b
public import CFSG.Quasithin.Background.HConj
public import CFSG.RankThree.GF2n.Stroth80.GriessLinear
public import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2Parabolic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open scoped Pointwise commutatorElement Matrix

theorem isL2_bar2_perfectCore_Q3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (j : Fin 2) :
    IsL2 (Bar2 (perfectCore (Q3 K j))) n := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnab := sl2_nonabelian hK4
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := sl2_isSimple hK4
  have hmodel : CFSG.Blueprint.LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 n :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (K := K) (m := 2) (f := n)
        (by norm_num) hn hK)
  let e : Bar2 (perfectCore (Q3 K j)) ≃* StatedProj (StatedSL 2 K) :=
    (modO2EquivOfHom hnab (blk3 (K := K) j)
      (blk3_surjective hK4 j) (blk3_ker_isPGroup ⟨n, hK⟩ j)).trans sl2EquivStatedProj
  exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) e.symm hmodel

theorem perfectCore_Q3_eq_bot_of_card_two {K : Type} [Field K] [Finite K]
    (hK2 : Nat.card K = 2) (j : Fin 2) : perfectCore (Q3 K j) = ⊥ := by
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨1, by rw [hK2]; norm_num⟩
  have hSL : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) := by
    refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK2]
    norm_num
  have hkerS : Group.IsSolvable (blk3 (K := K) j).ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (blk3_ker_isPGroup hK j).isNilpotent
    infer_instance
  have hN : Group.IsSolvable ↥(perfectCore (Q3 K j)) :=
    Group.isSolvable_of_ker_le_range (blk3 (K := K) j).ker.subtype (blk3 j)
      (by rw [Subgroup.range_subtype])
  have := (isSolvable_iff_perfectCore_eq_bot (perfectCore (Q3 K j))).mp hN
  rwa [perfectCore_eq_self_of_perfect (perfectCore_perfect _)] at this

@[expose] def stdLineSub (K : Type) [Field K] : Subgroup (CFSG.Quasithin.H.StdMod (Fin 3) K) where
  carrier := {x | Multiplicative.toAdd x ∈ stdLine K}
  one_mem' := by simp [mem_stdLine]
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd (x * y) ∈ stdLine K
    rw [toAdd_mul]
    exact (stdLine K).add_mem hx hy
  inv_mem' := by
    intro x hx
    change Multiplicative.toAdd x⁻¹ ∈ stdLine K
    rw [toAdd_inv]
    exact (stdLine K).neg_mem hx

@[expose] def stdPlaneSub (K : Type) [Field K] : Subgroup (CFSG.Quasithin.H.StdMod (Fin 3) K) where
  carrier := {x | Multiplicative.toAdd x ∈ stdPlane K}
  one_mem' := by simp [mem_stdPlane]
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd (x * y) ∈ stdPlane K
    rw [toAdd_mul]
    exact (stdPlane K).add_mem hx hy
  inv_mem' := by
    intro x hx
    change Multiplicative.toAdd x⁻¹ ∈ stdPlane K
    rw [toAdd_inv]
    exact (stdPlane K).neg_mem hx

theorem mem_stdLineSub {K : Type} [Field K]
    {x : CFSG.Quasithin.H.StdMod (Fin 3) K} :
    x ∈ stdLineSub K ↔ Multiplicative.toAdd x ∈ stdLine K := Iff.rfl

theorem mem_stdPlaneSub {K : Type} [Field K]
    {x : CFSG.Quasithin.H.StdMod (Fin 3) K} :
    x ∈ stdPlaneSub K ↔ Multiplicative.toAdd x ∈ stdPlane K := Iff.rfl

@[expose] def submoduleSub (K : Type) [Field K] (W : Submodule K (Fin 3 → K)) :
    Subgroup (CFSG.Quasithin.H.StdMod (Fin 3) K) where
  carrier := {x | Multiplicative.toAdd x ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd (x * y) ∈ W
    rw [toAdd_mul]
    exact W.add_mem hx hy
  inv_mem' := by
    intro x hx
    change Multiplicative.toAdd x⁻¹ ∈ W
    rw [toAdd_inv]
    exact W.neg_mem hx

theorem stdLineSub_eq_submoduleSub (K : Type) [Field K] :
    stdLineSub K = submoduleSub K (stdLine K) := rfl

theorem stdPlaneSub_eq_submoduleSub (K : Type) [Field K] :
    stdPlaneSub K = submoduleSub K (stdPlane K) := rfl

theorem fixV_map_conj {V : Type} [CommGroup V] (A : Subgroup (MulAut V)) (h : MulAut V) :
    fixV (A.map (MulAut.conj h).toMonoidHom) = (fixV A).map h.toMonoidHom := by
  ext v
  constructor
  · intro hv
    refine Subgroup.mem_map.mpr ⟨h⁻¹ v, ?_, by simp⟩
    intro a ha
    have hmem : h * a * h⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map_of_mem _ ha
    have hfix := hv (h * a * h⁻¹) hmem
    change (h * a * h⁻¹) v = v at hfix
    have := congrArg (fun w => h⁻¹ w) hfix
    change a (h⁻¹ v) = h⁻¹ v
    simpa [MulAut.mul_apply, mul_assoc] using this
  · rintro ⟨w, hw, rfl⟩ a ha
    obtain ⟨b, hb, hau⟩ := Subgroup.mem_map.mp ha
    change (a : MulAut V) (h w) = h w
    rw [← hau]
    change (h * (b : MulAut V) * h⁻¹) (h w) = h w
    simp only [MulAut.mul_apply]
    rw [MulAut.inv_apply_self, hw b hb]

theorem commV_map_conj {V : Type} [CommGroup V] (A : Subgroup (MulAut V)) (h : MulAut V) :
    commV (A.map (MulAut.conj h).toMonoidHom) = (commV A).map h.toMonoidHom := by
  have hset : {w : V | ∃ x ∈ A.map (MulAut.conj h).toMonoidHom, ∃ v : V, x v * v⁻¹ = w} =
      h.toMonoidHom '' {w : V | ∃ x ∈ A, ∃ v : V, x v * v⁻¹ = w} := by
    ext w
    constructor
    · rintro ⟨x, hx, v, rfl⟩
      obtain ⟨b, hb, hau⟩ := Subgroup.mem_map.mp hx
      refine ⟨b (h⁻¹ v) * (h⁻¹ v)⁻¹, ⟨b, hb, h⁻¹ v, rfl⟩, ?_⟩
      rw [← hau]
      simp [MulAut.mul_apply, mul_assoc]
    · rintro ⟨g, ⟨b, hb, v, rfl⟩, rfl⟩
      refine ⟨h * (b : MulAut V) * h⁻¹, Subgroup.mem_map_of_mem _ hb, h v, ?_⟩
      simp [MulAut.mul_apply, mul_assoc]
  unfold commV
  rw [hset, MonoidHom.map_closure]

@[expose] noncomputable def piNat {K : Type} [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K →* MulAut (CFSG.Quasithin.H.StdMod (Fin 3) K) :=
  (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSL 3 K)).comp
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom

theorem piNat_apply {K : Type} [Field K] (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    piNat A = CFSG.Quasithin.H.matAut A := by
  change CFSG.Quasithin.H.natAut (CFSG.Open.StatedSL 3 K)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A) = _
  change CFSG.Quasithin.H.matAut
      (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A) :
        ↥(CFSG.Open.StatedSL 3 K)) : GL (Fin 3) K) = _
  rfl

@[expose] noncomputable def UH (K : Type) [Field K] :
    Subgroup (MulAut (CFSG.Quasithin.H.StdMod (Fin 3) K)) :=
  (unitriangular 3 K).map (piNat (K := K))

theorem eq_uSL_of_mem_unitriangular {K : Type} [Field K]
    {A : Matrix.SpecialLinearGroup (Fin 3) K} (hA : A ∈ unitriangular 3 K) :
    ∃ a b c : K, A = CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL a b c := by
  rw [← usl_eq_unitriangular] at hA
  exact CFSG.ClassicalInvolution.ModelFacts.OddCover.mem_Usl.mp hA

theorem coe_toGL_uSL {K : Type} [Field K] (a b c : K) :
    ((Matrix.SpecialLinearGroup.toGL (uSL a b c) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = uMat a b c := by
  change ((uSL a b c : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = uMat a b c
  exact coe_uSL a b c

theorem toAdd_matAut_apply {K : Type} [Field K] (g : GL (Fin 3) K)
    (x : CFSG.Quasithin.H.StdMod (Fin 3) K) :
    Multiplicative.toAdd (CFSG.Quasithin.H.matAut g x) =
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd x := by
  rw [← ofAdd_toAdd x]
  rfl

theorem fixV_UH (K : Type) [Field K] [Finite K] [CharP K 2] :
    fixV (UH K) = stdLineSub K := by
  ext x
  rw [mem_stdLineSub, mem_stdLine]
  constructor
  · intro hx
    have hmem1 : piNat (K := K) (uSL 1 0 0) ∈ UH K :=
      Subgroup.mem_map_of_mem _ (by
        rw [← usl_eq_unitriangular]
        exact uSL_mem_Usl _ _ _)
    have hmem2 : piNat (K := K) (uSL 0 0 1) ∈ UH K :=
      Subgroup.mem_map_of_mem _ (by
        rw [← usl_eq_unitriangular]
        exact uSL_mem_Usl _ _ _)
    have h1 := hx _ hmem1
    have h2 := hx _ hmem2
    rw [piNat_apply] at h1 h2
    have hv1 := congrArg (fun y => (Multiplicative.toAdd y) 0) h1
    have hv2 := congrArg (fun y => (Multiplicative.toAdd y) 1) h2
    rw [toAdd_matAut_apply, coe_toGL_uSL, uMat_mulVec] at hv1 hv2
    simp only [Pi.zero_apply, mul_zero, zero_mul, add_zero, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] at hv1 hv2
    refine ⟨?_, ?_⟩
    · exact add_left_cancel (a := Multiplicative.toAdd x 0) (by simpa using hv1)
    · exact add_left_cancel (a := Multiplicative.toAdd x 1) (by simpa using hv2)
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨a, b, c, rfl⟩ := eq_uSL_of_mem_unitriangular hA
    rw [piNat_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_matAut_apply, coe_toGL_uSL, uMat_mulVec]
    funext i
    fin_cases i <;> simp [h1, h2]

theorem commV_UH (K : Type) [Field K] [Finite K] [CharP K 2] :
    commV (UH K) = stdPlaneSub K := by
  apply le_antisymm
  · rw [commV, Subgroup.closure_le]
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a, b, c, rfl⟩ := eq_uSL_of_mem_unitriangular hA
    change piNat (K := K) (uSL a b c) v * v⁻¹ ∈ stdPlaneSub K
    rw [mem_stdPlaneSub, mem_stdPlane]
    rw [piNat_apply]
    change (Multiplicative.toAdd
      (CFSG.Quasithin.H.matAut (uSL a b c) v * v⁻¹)) 2 = 0
    rw [toAdd_mul, toAdd_inv, toAdd_matAut_apply]
    rw [coe_toGL_uSL, uMat_mulVec]
    simp
  · intro v hv
    rw [mem_stdPlaneSub, mem_stdPlane] at hv
    rw [commV]
    refine Subgroup.subset_closure ⟨piNat (K := K) (uSL 0 (Multiplicative.toAdd v 0)
      (Multiplicative.toAdd v 1)), ?_, Multiplicative.ofAdd (![0, 0, 1] : Fin 3 → K), ?_⟩
    · change piNat (K := K) (uSL 0 (Multiplicative.toAdd v 0)
        (Multiplicative.toAdd v 1)) ∈ (unitriangular 3 K).map (piNat (K := K))
      exact Subgroup.mem_map_of_mem _ (by
        rw [← usl_eq_unitriangular]
        exact uSL_mem_Usl _ _ _)
    · apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, piNat_apply, toAdd_matAut_apply]
      rw [coe_toGL_uSL, uMat_mulVec]
      funext i
      fin_cases i <;> simp [hv]

noncomputable def eSL (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K ≃* CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).trans
    (CFSG.Quasithin.H.natEquiv (CFSG.Open.StatedSL 3 K))

theorem eSL_coe (K : Type) [Field K] (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((eSL K A : CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)) :
      MulAut (CFSG.Quasithin.H.StdMod (Fin 3) K)) = piNat A := by
  change ((CFSG.Quasithin.H.natEquiv (CFSG.Open.StatedSL 3 K))
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K) A) :
      MulAut (CFSG.Quasithin.H.StdMod (Fin 3) K)) = _
  rw [CFSG.Quasithin.H.coe_natEquiv]
  rfl

@[expose] noncomputable def StdS (K : Type) [Field K] :
    Subgroup (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)) :=
  (unitriangular 3 K).map (eSL K).toMonoidHom

@[expose] noncomputable def StdB (K : Type) [Field K] :
    Subgroup (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)) :=
  (upperTriangular 3 K).map (eSL K).toMonoidHom

@[expose] noncomputable def StdQ (K : Type) [Field K] (j : Fin 2) :
    Subgroup (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)) :=
  (Q3 K j).map (eSL K).toMonoidHom

theorem StdQ_eq_map (K : Type) [Field K] (j : Fin 2) :
    StdQ K j = (Q3 K j).map (eSL K).toMonoidHom := rfl

theorem StdS_map_subtype (K : Type) [Field K] :
    (StdS K).map (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)).subtype = UH K := by
  have hcomp : (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)).subtype.comp
      (eSL K).toMonoidHom = piNat (K := K) :=
    MonoidHom.ext fun x => eSL_coe K x
  rw [StdS, Subgroup.map_map, hcomp, UH]

theorem normalizer_StdS (K : Type) [Field K] :
    Subgroup.normalizer (StdS K : Set
      (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))) = StdB K := by
  have h := Subgroup.map_equiv_normalizer_eq (unitriangular 3 K) (eSL K)
  rw [normalizer_unitriangular] at h
  exact h.symm

theorem isSylowTwoOf_StdS (K : Type) [Field K] [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (StdS K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (p := 2) (K := K) (n := 3) (by norm_num)
  have hU0 : CFSG.QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have h := CFSG.Quasithin.H13.A5.isSylowTwoOf_map hU0 (eSL K).toMonoidHom
  rwa [Subgroup.map_top_of_surjective _ (eSL K).surjective] at h

theorem overgroups_StdB (K : Type) [Field K] [Finite K] [CharP K 2]
    {P : Subgroup (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))}
    (hBP : StdB K ≤ P) :
    P = StdB K ∨ P = StdQ K 0 ∨ P = StdQ K 1 ∨ P = ⊤ := by
  classical
  let e := eSL K
  set A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) := P.comap e.toMonoidHom with hA
  have hmap : A.map e.toMonoidHom = P :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective P
  have hBA : upperTriangular 3 K ≤ A := by
    rw [← Subgroup.map_le_iff_le_comap]
    exact hBP
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  set I := borelOvergroupCuts A with hI
  have hsub : I ⊆ ({1, 2} : Set ℕ) := by
    rintro i ⟨hi1, hi3, -⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · left
    have hI12 : I = {1, 2} := Set.Subset.antisymm hsub (by
      intro i hi
      rcases hi with rfl | rfl
      · exact h1
      · exact h2)
    rw [← hmap, hAeq, hI12, ← upperTriangular_eq_flagStabilizer]
    rfl
  · right; left
    have hI1 : I = {1} := Set.Subset.antisymm (by
      intro i hi
      rcases hsub hi with rfl | rfl
      · rfl
      · exact absurd hi h2) (by
      intro i hi
      rw [Set.mem_singleton_iff.mp hi]
      exact h1)
    rw [← hmap, hAeq, hI1]
    change Subgroup.map e.toMonoidHom (flagStabilizer 3 K {((0 : Fin 2) : ℕ) + 1}) = StdQ K 0
    rw [← Q3_eq (K := K) 0]
    rfl
  · right; right; left
    have hI2 : I = {2} := Set.Subset.antisymm (by
      intro i hi
      rcases hsub hi with rfl | rfl
      · exact absurd hi h1
      · rfl) (by
      intro i hi
      rw [Set.mem_singleton_iff.mp hi]
      exact h2)
    rw [← hmap, hAeq, hI2]
    change Subgroup.map e.toMonoidHom (flagStabilizer 3 K {((1 : Fin 2) : ℕ) + 1}) = StdQ K 1
    rw [← Q3_eq (K := K) 1]
    rfl
  · right; right; right
    have hI0 : I = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun i hi => by
      rcases hsub hi with rfl | rfl
      · exact h1 hi
      · exact h2 hi)
    rw [← hmap, hAeq, hI0, flagStabilizer_empty,
      Subgroup.map_top_of_surjective _ e.surjective]

theorem stabilizer_submoduleSub (K : Type) [Field K] (W : Submodule K (Fin 3 → K)) :
    letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) :=
      MulDistribMulAction.compHom _ (piNat (K := K))
    letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
    letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
    MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 3) K)
      (submoduleSub K W : Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) = LinearFlag.stabilizer W := by
  letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) :=
    MulDistribMulAction.compHom _ (piNat (K := K))
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
  ext A
  rw [MulAction.mem_stabilizer_iff, LinearFlag.mem_stabilizer]
  constructor
  · intro h
    apply le_antisymm
    · intro v hv
      obtain ⟨w, hw, hwv⟩ := hv
      have hw' : Multiplicative.ofAdd w ∈ (submoduleSub K W :
          Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := hw
      have h1 : A • (Multiplicative.ofAdd w) ∈ (submoduleSub K W :
          Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := by
        have hsm : A • (Multiplicative.ofAdd w) ∈
            A • (submoduleSub K W : Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) :=
          Set.smul_mem_smul_set hw'
        rw [h] at hsm
        exact hsm
      have h2 : Multiplicative.toAdd (A • (Multiplicative.ofAdd w)) ∈ W := h1
      change Multiplicative.toAdd (piNat (K := K) A (Multiplicative.ofAdd w)) ∈ W at h2
      rw [piNat_apply, toAdd_matAut_apply, toAdd_ofAdd] at h2
      change ((A : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W at h2
      rwa [← Matrix.mulVecLin_apply, hwv] at h2
    · intro v hv
      have hv' : Multiplicative.ofAdd v ∈ (submoduleSub K W :
          Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := hv
      have h2 : Multiplicative.ofAdd v ∈ A • (submoduleSub K W :
          Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := by
        rw [show A • (submoduleSub K W : Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) =
          (submoduleSub K W : Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) from h]
        exact hv' 
      obtain ⟨w, hw, hwv⟩ := Set.mem_smul_set.mp h2
      refine ⟨Multiplicative.toAdd w, hw, ?_⟩
      have this := congrArg Multiplicative.toAdd hwv
      change Multiplicative.toAdd (piNat (K := K) A w) = v at this
      rw [piNat_apply, toAdd_matAut_apply] at this
      change Multiplicative.toAdd (piNat (K := K) A w) = v
      rw [piNat_apply, toAdd_matAut_apply]
      exact this
  · intro h
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Set.mem_smul_set.mp hv
      have hw' : Multiplicative.toAdd w ∈ W := hw
      have h1 : (A : Matrix.SpecialLinearGroup (Fin 3) K) *ᵥ Multiplicative.toAdd w ∈ W := by
        rw [← h]
        exact ⟨w, hw', rfl⟩
      have this := congrArg Multiplicative.toAdd hwv
      change Multiplicative.toAdd v ∈ W
      rw [← this]
      change Multiplicative.toAdd (piNat (K := K) A w) ∈ W
      rwa [piNat_apply, toAdd_matAut_apply]
    · intro hv
      have h1 : Multiplicative.toAdd v ∈ W.map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) := by
        rw [h]
        exact hv
      obtain ⟨w, hw, hwv⟩ := h1
      refine Set.mem_smul_set.mpr ⟨Multiplicative.ofAdd w, hw, ?_⟩
      apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (piNat (K := K) A (Multiplicative.ofAdd w)) = Multiplicative.toAdd v
      rw [piNat_apply, toAdd_matAut_apply]
      exact hwv

theorem Q3_zero_eq_stabilizer_stdLineSub (K : Type) [Field K] :
    letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) :=
      MulDistribMulAction.compHom _ (piNat (K := K))
    letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
    letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
    MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 3) K)
      (stdLineSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) = Q3 K 0 := by
  letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) :=
    MulDistribMulAction.compHom _ (piNat (K := K))
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
  rw [stdLineSub_eq_submoduleSub, stabilizer_submoduleSub]
  simp [Q3_eq, LinearFlag.flagStabilizer_singleton]
  rw [← stdLine_eq_flagSpace]

theorem Q3_one_eq_stabilizer_stdPlaneSub (K : Type) [Field K] :
    letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) :=
      MulDistribMulAction.compHom _ (piNat (K := K))
    letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
    letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
    MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 3) K)
      (stdPlaneSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) = Q3 K 1 := by
  letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) :=
    MulDistribMulAction.compHom _ (piNat (K := K))
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
  rw [stdPlaneSub_eq_submoduleSub, stabilizer_submoduleSub]
  simp [Q3_eq, LinearFlag.flagStabilizer_singleton]
  rw [← stdPlane_eq_flagSpace]

theorem StdQ_zero_eq_stabilizer_stdLineSub (K : Type) [Field K] [Finite K] [CharP K 2] :
    letI : MulDistribMulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)).subtype
    letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
    letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
    MulAction.stabilizer (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (stdLineSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) = StdQ K 0 := by
  letI : MulDistribMulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)).subtype
  letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
  letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
  letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.compHom _ (piNat (K := K))
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
  have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
    (eSL K) (Equiv.refl (Set (CFSG.Quasithin.H.StdMod (Fin 3) K))) ?_
    (stdLineSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3) K))
  · rw [Q3_zero_eq_stabilizer_stdLineSub] at h
    rw [StdQ]
    exact h.symm
  · intro g z
    change (piNat (K := K) g) '' z = (eSL K g : MulAut
      (CFSG.Quasithin.H.StdMod (Fin 3) K)) '' z
    rw [← eSL_coe K g]

theorem StdQ_one_eq_stabilizer_stdPlaneSub (K : Type) [Field K] [Finite K] [CharP K 2] :
    letI : MulDistribMulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)).subtype
    letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
    letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
    MulAction.stabilizer (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (stdPlaneSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) = StdQ K 1 := by
  letI : MulDistribMulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K)).subtype
  letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
  letI : MulAction (CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
  letI : MulDistribMulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.compHom _ (piNat (K := K))
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.Quasithin.H.StdMod (Fin 3) K) := MulDistribMulAction.toMulAction
  letI : MulAction (Matrix.SpecialLinearGroup (Fin 3) K)
      (Set (CFSG.Quasithin.H.StdMod (Fin 3) K)) := Set.mulActionSet
  have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
    (eSL K) (Equiv.refl (Set (CFSG.Quasithin.H.StdMod (Fin 3) K))) ?_
    (stdPlaneSub K : Set (CFSG.Quasithin.H.StdMod (Fin 3) K))
  · rw [Q3_one_eq_stabilizer_stdPlaneSub] at h
    rw [StdQ]
    exact h.symm
  · intro g z
    change (piNat (K := K) g) '' z = (eSL K g : MulAut
      (CFSG.Quasithin.H.StdMod (Fin 3) K)) '' z
    rw [← eSL_coe K g]

theorem Hinf_eq_perfectCore {G : Type} [Group G] (H : Subgroup G) :
    Hinf H = CFSG.Quasithin.perfectCore H :=
  (CFSG.Quasithin.perfectCore_eq_map_perfectResidual H).symm

theorem Hinf_map_eq_bot {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Subgroup X) (h : Hinf P = ⊥) :
    Hinf (P.map e.toMonoidHom) = ⊥ := by
  rw [← Hinf_map e.toMonoidHom P, h, Subgroup.map_bot]

theorem isL2_bar2_hinf_map_equiv {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Subgroup X) {n : ℕ} (h : IsL2 (Bar2 (Hinf P)) n) :
    IsL2 (Bar2 (Hinf (P.map e.toMonoidHom))) n := by
  have hHinf : (Hinf P).map e.toMonoidHom = Hinf (P.map e.toMonoidHom) :=
    Hinf_map e.toMonoidHom P
  let eSub : ↥(Hinf P) ≃* ↥(Hinf (P.map e.toMonoidHom)) :=
    ((Hinf P).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hHinf)
  obtain ⟨ebar⟩ := nonempty_bar2_mulEquiv_of_equiv eSub
  exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n)
    ebar h

theorem fixedPointSubgroup_eq_fixV {V : Type} [CommGroup V] (A : Subgroup (MulAut V)) :
    letI : MulDistribMulAction ↥A V := MulDistribMulAction.compHom V A.subtype
    fixedPointSubgroup ↥A V = fixV A := by
  letI : MulDistribMulAction ↥A V := MulDistribMulAction.compHom V A.subtype
  ext v
  constructor
  · intro hv x hx
    have := hv ⟨x, hx⟩
    rw [MulAction.compHom_smul_def] at this
    exact this
  · intro hv x
    rw [MulAction.compHom_smul_def]
    exact hv x.1 x.2

theorem stabilizer_map_conj_subgroup {V : Type} [CommGroup V]
    (H : Subgroup (MulAut V)) (h : ↥H) (W : Subgroup V) :
    letI : MulDistribMulAction ↥H V := MulDistribMulAction.compHom V H.subtype
    letI : MulAction ↥H V := MulDistribMulAction.toMulAction
    letI : MulAction ↥H (Set V) := Set.mulActionSet
    MulAction.stabilizer ↥H
      ((W.map ((h : ↥H) : MulAut V).toMonoidHom : Subgroup V) : Set V) =
      (MulAction.stabilizer ↥H (W : Set V)).map (MulAut.conj h).toMonoidHom := by
  letI : MulDistribMulAction ↥H V := MulDistribMulAction.compHom V H.subtype
  letI : MulAction ↥H V := MulDistribMulAction.toMulAction
  letI : MulAction ↥H (Set V) := Set.mulActionSet
  have hset : (h : ↥H) • (W : Set V) =
      (W.map ((h : ↥H) : MulAut V).toMonoidHom : Subgroup V) := by
    ext x
    simp only [Set.mem_smul_set, Subgroup.mem_map, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, by simpa [MulAction.compHom_smul_def] using hxy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, by simpa [MulAction.compHom_smul_def] using hxy⟩
  rw [← hset]
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj (h : ↥H) (W : Set V)

theorem map_subtype_stabilizer_eq_inf {V : Type} [CommGroup V]
    (H : Subgroup (MulAut V)) (W : Subgroup V) :
    letI : MulDistribMulAction ↥H V := MulDistribMulAction.compHom V H.subtype
    letI : MulAction ↥H V := MulDistribMulAction.toMulAction
    letI : MulAction ↥H (Set V) := Set.mulActionSet
    (MulAction.stabilizer ↥H (W : Set V)).map H.subtype =
      MulAction.stabilizer (MulAut V) (W : Set V) ⊓ H := by
  letI : MulDistribMulAction ↥H V := MulDistribMulAction.compHom V H.subtype
  letI : MulAction ↥H V := MulDistribMulAction.toMulAction
  letI : MulAction ↥H (Set V) := Set.mulActionSet
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, g.2⟩
    have hg' : ((g : ↥H) : MulAut V) • (W : Set V) = (W : Set V) := by
      have := MulAction.mem_stabilizer_iff.mp hg
      change ((g : ↥H) : MulAut V) • (W : Set V) = (W : Set V) at this
      exact this
    exact hg'
  · rintro ⟨hx, hxH⟩
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    change x • (W : Set V) = (W : Set V)
    exact hx

theorem map_subtype_stabilizer_conj_normalizer {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} (t : MulAut V)
    (ht : t ∈ Subgroup.normalizer (H : Set (MulAut V))) (W : Subgroup V) :
    letI : MulDistribMulAction ↥H V := MulDistribMulAction.compHom V H.subtype
    letI : MulAction ↥H V := MulDistribMulAction.toMulAction
    letI : MulAction ↥H (Set V) := Set.mulActionSet
    ((MulAction.stabilizer ↥H (W : Set V)).map H.subtype).map (MulAut.conj t).toMonoidHom =
      (MulAction.stabilizer ↥H ((W.map t.toMonoidHom : Subgroup V) : Set V)).map H.subtype := by
  letI : MulDistribMulAction ↥H V := MulDistribMulAction.compHom V H.subtype
  letI : MulAction ↥H V := MulDistribMulAction.toMulAction
  letI : MulAction ↥H (Set V) := Set.mulActionSet
  have hWset : (t : MulAut V) • (W : Set V) =
      ((W.map t.toMonoidHom : Subgroup V) : Set V) := by
    ext x
    simp only [Set.mem_smul_set, Subgroup.mem_map, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy⟩
  have hHmap : H.map (MulAut.conj t).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  rw [map_subtype_stabilizer_eq_inf H W,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj t (W : Set V),
    hWset, hHmap, ← map_subtype_stabilizer_eq_inf H (W.map t.toMonoidHom)]

theorem sl3NaturalLine_holds : SL3NaturalLine := by
  intro K hF hFin n hK
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by
      rw [← Nat.card_eq_fintype_card]
      exact hK)
  have hKgt : 1 < Nat.card K := Finite.one_lt_card
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hK
    simp at hK
    omega
  set V := CFSG.Quasithin.H.StdMod (Fin 3) K with hV
  set H : Subgroup (MulAut V) := CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K) with hH
  change SL3Line V H n
  unfold SL3Line
  intro S
  intro ℓ Pℓ
  intro Tstar hTnorm hT2 hST
  intro Good Pstar hmin
  classical
  have hSylS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥H) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hSylStd : CFSG.QuasithinUnique.IsSylowTwoOf (StdS K) ⊤ := isSylowTwoOf_StdS (K := K)
  obtain ⟨h, -, hconj⟩ :=
    CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hSylStd hSylS
  let SH : Subgroup (MulAut V) := (S : Subgroup ↥H).map H.subtype
  have hcomp : H.subtype.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj ((h : ↥H) : MulAut V)).toMonoidHom.comp H.subtype := by
    ext x
    rfl
  have hSH : SH = (UH K).map (MulAut.conj ((h : ↥H) : MulAut V)).toMonoidHom := by
    dsimp [SH]
    rw [hconj, Subgroup.map_map, hcomp, ← Subgroup.map_map, StdS_map_subtype]
    rfl
  have hℓ : ℓ = (stdLineSub K).map ((h : ↥H) : MulAut V).toMonoidHom := by
    have h1 : ℓ = fixV SH := by
      dsimp [ℓ, SH]
      rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
    rw [h1, hSH, fixV_map_conj, fixV_UH]
  have hW2 : commV SH = (stdPlaneSub K).map ((h : ↥H) : MulAut V).toMonoidHom := by
    rw [hSH, commV_map_conj, commV_UH]
  have hPℓ : Pℓ = (StdQ K 0).map (MulAut.conj h).toMonoidHom := by
    have hstab : MulAction.stabilizer ↥H
        (((stdLineSub K).map ((h : ↥H) : MulAut V).toMonoidHom : Subgroup V) : Set V) =
        (MulAction.stabilizer ↥H (stdLineSub K : Set V)).map
          (MulAut.conj h).toMonoidHom := by
      exact stabilizer_map_conj_subgroup H h (stdLineSub K)
    dsimp [Pℓ]
    rw [hℓ]
    change MulAction.stabilizer ↥H
      (((stdLineSub K).map ((h : ↥H) : MulAut V).toMonoidHom : Subgroup V) : Set V) =
      (StdQ K 0).map (MulAut.conj h).toMonoidHom
    rw [hstab]
    have hstabQ0 : MulAction.stabilizer ↥H (stdLineSub K : Set V) = StdQ K 0 := by
      change MulAction.stabilizer
        ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
        (stdLineSub K : Set V) = StdQ K 0
      exact StdQ_zero_eq_stabilizer_stdLineSub (K := K)
    rw [hstabQ0]
  let Qplane : Subgroup ↥H := MulAction.stabilizer ↥H ((commV SH : Subgroup V) : Set V)
  have hQplane : Qplane = (StdQ K 1).map (MulAut.conj h).toMonoidHom := by
    have hstab : MulAction.stabilizer ↥H
        (((stdPlaneSub K).map ((h : ↥H) : MulAut V).toMonoidHom : Subgroup V) : Set V) =
        (MulAction.stabilizer ↥H (stdPlaneSub K : Set V)).map
          (MulAut.conj h).toMonoidHom := by
      exact stabilizer_map_conj_subgroup H h (stdPlaneSub K)
    dsimp [Qplane]
    rw [hW2]
    change MulAction.stabilizer ↥H
      (((stdPlaneSub K).map ((h : ↥H) : MulAut V).toMonoidHom : Subgroup V) : Set V) =
      (StdQ K 1).map (MulAut.conj h).toMonoidHom
    rw [hstab]
    have hstabQ1 : MulAction.stabilizer ↥H (stdPlaneSub K : Set V) = StdQ K 1 := by
      change MulAction.stabilizer
        ↥(CFSG.Quasithin.H.natImage (CFSG.Open.StatedSL 3 K))
        (stdPlaneSub K : Set V) = StdQ K 1
      exact StdQ_one_eq_stabilizer_stdPlaneSub (K := K)
    rw [hstabQ1]
  have hB : Subgroup.normalizer (S : Set ↥H) =
      (StdB K).map (MulAut.conj h).toMonoidHom := by
    change Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H) =
      (StdB K).map (MulAut.conj h).toMonoidHom
    rw [hconj, ← Subgroup.map_equiv_normalizer_eq (StdS K) (MulAut.conj h), normalizer_StdS]
  have hBP : Subgroup.normalizer (S : Set ↥H) ≤ Pstar :=
    hmin.1.1.normalizer_le S hmin.1.2.1
  have hB_le_Pℓ : Subgroup.normalizer (S : Set ↥H) ≤ Pℓ := by
    rw [hB, hPℓ]
    exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
      (Subgroup.map_mono (f := (eSL K).toMonoidHom) (upperTriangular_le_Q3 0))
  have hS_Qplane : (S : Subgroup ↥H) ≤ Qplane := by
    rw [hconj, hQplane]
    exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
      (Subgroup.map_mono (f := (eSL K).toMonoidHom)
        ((unitriangular_le_upperTriangular 3 K).trans (upperTriangular_le_Q3 1)))
  have hB_Qplane : Subgroup.normalizer (S : Set ↥H) ≤ Qplane := by
    rw [hB, hQplane]
    exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
      (Subgroup.map_mono (f := (eSL K).toMonoidHom) (upperTriangular_le_Q3 1))
  have hQpar : IsParabolicTwo ↥H Qplane := ⟨S, hB_Qplane⟩
  have hTstarH : Tstar ⊓ H = SH := by
    have hSylUH : CFSG.QuasithinUnique.IsSylowTwoOf (UH K) H := by
      have h := CFSG.Quasithin.H13.A5.isSylowTwoOf_map hSylStd H.subtype
      rwa [show (⊤ : Subgroup ↥H).map H.subtype = H from by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype], StdS_map_subtype] at h
    have hHmap : H.map (MulAut.conj ((h : ↥H) : MulAut V)).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer h.2)
    have hSylSH : CFSG.QuasithinUnique.IsSylowTwoOf SH H := by
      have h := hSylUH.map_equiv (MulAut.conj ((h : ↥H) : MulAut V))
      rwa [← hSH, hHmap] at h
    have hX2 : IsPGroup 2 ↥(Tstar ⊓ H) := by
      intro x
      obtain ⟨k, hk⟩ := hT2 ⟨(x : MulAut V), x.2.1⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    exact hSylSH.eq_of_le (le_inf hST (Subgroup.map_subtype_le _)) inf_le_right hX2
  have hSH_normal : ∀ t ∈ Tstar, SH.map (MulAut.conj t).toMonoidHom = SH := by
    intro t ht
    have hle : SH.map (MulAut.conj t).toMonoidHom ≤ SH := by
      rintro x ⟨s, hs, rfl⟩
      obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.mp hs
      have htH : t * (s0 : MulAut V) * t⁻¹ ∈ H :=
        ((Subgroup.mem_normalizer_iff.mp (hTnorm ht)) (s0 : MulAut V)).mp s0.2
      have hmem : t * (s0 : MulAut V) * t⁻¹ ∈ Tstar ⊓ H :=
        ⟨Tstar.mul_mem (Tstar.mul_mem ht (hST (Subgroup.mem_map_of_mem H.subtype hs0)))
            (Tstar.inv_mem ht), htH⟩
      rwa [hTstarH] at hmem
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective])
  have hQgoodT : ∀ t ∈ Tstar,
      (Qplane.map H.subtype).map (MulAut.conj t).toMonoidHom = Qplane.map H.subtype := by
    intro t ht
    have hW2_t : (commV SH).map t.toMonoidHom = commV SH := by
      rw [← commV_map_conj SH t, hSH_normal t ht]
    have hstab := map_subtype_stabilizer_conj_normalizer t (hTnorm ht) (commV SH)
    dsimp [Qplane]
    calc
      Subgroup.map (MulAut.conj t).toMonoidHom
          (Subgroup.map H.subtype (MulAction.stabilizer ↥H (commV SH : Set V))) =
          Subgroup.map H.subtype
            (MulAction.stabilizer ↥H ((commV SH).map t.toMonoidHom : Set V)) := by
            exact hstab
      _ = Subgroup.map H.subtype
            (MulAction.stabilizer ↥H (commV SH : Set V)) := by
            rw [hW2_t]
  have hnotStd : ¬ (StdQ K 1) ≤ (StdQ K 0) := by
    intro hle
    have hle' : Q3 K 1 ≤ Q3 K 0 := by
      apply (Subgroup.map_le_map_iff_of_injective (f := (eSL K).toMonoidHom) (eSL K).injective).mp
      simpa [StdQ] using hle
    have hmem1 : reflElt 3 K 1 ∈ Q3 K 1 := by
      rw [Q3_eq, LinearFlag.flagStabilizer_singleton]
      simpa [LinearFlag.flagStabilizer_singleton] using
        (reflElt_mem_flagStabilizer_singleton_iff (K := K) (i := 2) (j := 1)
          (by norm_num) (by norm_num)).mpr (by norm_num : (1 : ℕ) ≠ 2)
    have hmem0 : reflElt 3 K 1 ∈ Q3 K 0 := hle' hmem1
    rw [Q3_eq, LinearFlag.flagStabilizer_singleton] at hmem0
    have hmem0' : reflElt 3 K 1 ∈ flagStabilizer 3 K {1} := by
      simpa [LinearFlag.flagStabilizer_singleton] using hmem0
    exact (reflElt_mem_flagStabilizer_singleton_iff (K := K) (i := 1) (j := 1)
      (by norm_num) (by norm_num)).mp hmem0' (by norm_num)
  have hQnotLePℓ : ¬ Qplane ≤ Pℓ := by
    intro hle
    apply hnotStd
    rw [hQplane, hPℓ] at hle
    exact (Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective).mp hle
  have hQ3ne : Q3 K 1 ≠ ⊤ := by
    rw [Q3_eq, LinearFlag.flagStabilizer_singleton]
    exact LinearFlag.stabilizer_flagSpace_ne_top (K := K) (n := 3) (d := 2)
      (by norm_num) (by norm_num)
  have hStdQne : StdQ K 1 ≠ ⊤ := by
    intro htop
    apply hQ3ne
    have htop' : StdQ K 1 = (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map
        (eSL K).toMonoidHom := by
      rw [htop, Subgroup.map_top_of_surjective _ (eSL K).surjective]
    exact (Subgroup.map_injective (f := (eSL K).toMonoidHom) (eSL K).injective)
      (by simpa [StdQ] using htop')
  have hQne : Qplane ≠ ⊤ := by
    intro htop
    apply hStdQne
    have hmap := congrArg (fun X : Subgroup ↥H => X.map (MulAut.conj h⁻¹).toMonoidHom) htop
    rw [hQplane, Subgroup.map_map] at hmap
    have hcomp5 : ((MulAut.conj h⁻¹).toMonoidHom).comp (MulAut.conj h).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp5, Subgroup.map_id,
      Subgroup.map_top_of_surjective _ (MulAut.conj h⁻¹).surjective] at hmap
    exact hmap
  have hQgood : Good Qplane := ⟨hQpar, hS_Qplane, hQgoodT, hQnotLePℓ⟩
  have hP'B : StdB K ≤ Pstar.map (MulAut.conj h⁻¹).toMonoidHom := by
    have hmono := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hBP
    rw [hB, Subgroup.map_map] at hmono
    have hcomp3 : ((MulAut.conj h⁻¹).toMonoidHom).comp (MulAut.conj h).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp3, Subgroup.map_id] at hmono
    exact hmono
  have hPP' : (Pstar.map (MulAut.conj h⁻¹).toMonoidHom).map
      (MulAut.conj h).toMonoidHom = Pstar := by
    rw [Subgroup.map_map]
    have hcomp4 : ((MulAut.conj h).toMonoidHom).comp ((MulAut.conj h⁻¹).toMonoidHom) =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp4, Subgroup.map_id]
  rcases overgroups_StdB (K := K) hP'B with hP' | hP' | hP' | hP'
  ·
    exfalso
    have hPstar : Pstar = Subgroup.normalizer (S : Set ↥H) := by
      rw [← hPP', hP', ← hB]
    exact hmin.1.2.2.2 (hPstar ▸ hB_le_Pℓ)
  ·
    exfalso
    have hPstar : Pstar = Pℓ := by
      rw [← hPP', hP', ← hPℓ]
    exact hmin.1.2.2.2 (hPstar ▸ le_rfl)
  ·
    have hPstar : Pstar = Qplane := by
      rw [← hPP', hP', ← hQplane]
    refine ⟨?_, ?_⟩
    · rw [hPstar]
      exact hQne
    · rw [hPstar]
      by_cases hn : n = 1
      · right
        refine ⟨hn, ?_⟩
        have hK2 : Nat.card K = 2 := by rw [hK, hn]; norm_num
        have hstdBot : Hinf (Q3 K 1) = ⊥ := by
          rw [Hinf_eq_perfectCore]
          exact perfectCore_Q3_eq_bot_of_card_two hK2 1
        have hstdBotStd : Hinf (StdQ K 1) = ⊥ := by
          rw [StdQ_eq_map]
          exact Hinf_map_eq_bot (eSL K) (Q3 K 1) hstdBot
        rw [hQplane]
        exact Hinf_map_eq_bot (MulAut.conj h) (StdQ K 1) hstdBotStd
      · left
        have hn2 : 2 ≤ n := by omega
        have hstd : IsL2 (Bar2 (Hinf (Q3 K 1))) n := by
          rw [Hinf_eq_perfectCore]
          exact isL2_bar2_perfectCore_Q3 hK hn2 1
        have hstdStd : IsL2 (Bar2 (Hinf (StdQ K 1))) n := by
          rw [StdQ_eq_map]
          exact isL2_bar2_hinf_map_equiv (eSL K) (Q3 K 1) hstd
        rw [hQplane]
        exact isL2_bar2_hinf_map_equiv (MulAut.conj h) (StdQ K 1) hstdStd
  ·
    exfalso
    have hPstarTop : Pstar = ⊤ := by
      rw [← hPP', hP', Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective]
    have htop_le : (⊤ : Subgroup ↥H) ≤ Qplane := by
      rw [← hPstarTop]
      exact hmin.2 hQgood (by rw [hPstarTop]; exact le_top)
    exact hQne (top_le_iff.mp htop_le)

theorem kTab23b_SL3_line_uncond_final (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsSLn ↥H 3 n ∧ CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Tstar : Subgroup (MulAut W),
        Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
        IsPGroup 2 ↥Tstar →
        (S : Subgroup ↥H).map H.subtype ≤ Tstar →
        let Good : Subgroup ↥H → Prop := fun Pstar =>
          IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
          (∀ t ∈ Tstar,
            (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
          ¬ Pstar ≤ Pℓ
        ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
          Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥)) :=
  kTab23b_SL3_line_uncond W H n hnat hperf hline sl3NaturalLine_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
