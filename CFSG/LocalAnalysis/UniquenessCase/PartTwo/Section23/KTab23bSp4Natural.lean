module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSp4
public import CFSG.ClassicalGroups.Symplectic.Sp4LagrangianParabolic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.Quasithin.Vol2.KGNatSp4Levi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.QuasithinUnique.Setup.X7a
open CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.Vol2.KGNat
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ClassicalGroups.Symplectic.Sp4
open scoped Pointwise commutatorElement Matrix

abbrev Vsp4 (K : Type) [Field K] := CFSG.Quasithin.H.StdMod (Fin 2 ⊕ Fin 2) K

abbrev Hsp (K : Type) [Field K] : Subgroup (MulAut (Vsp4 K)) :=
  CFSG.Quasithin.H.natImage (CFSG.Open.StatedSp 2 K)

@[expose] noncomputable def eSp4 (K : Type) [Field K] : CFSG.Open.StatedSp 2 K ≃* Hsp K :=
  CFSG.Quasithin.H.natEquiv (CFSG.Open.StatedSp 2 K)

theorem eSp4_apply (K : Type) [Field K] (g : CFSG.Open.StatedSp 2 K) :
    ((eSp4 K g : Hsp K) : MulAut (Vsp4 K)) = CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) g :=
  CFSG.Quasithin.H.coe_natEquiv _ g

theorem toAdd_natAut_apply (K : Type) [Field K] (g : CFSG.Open.StatedSp 2 K) (x : Vsp4 K) :
    Multiplicative.toAdd (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) g x) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Multiplicative.toAdd x := by
  rw [← ofAdd_toAdd x]
  change Multiplicative.toAdd
    (CFSG.Quasithin.H.matAut (g : GL (Fin 2 ⊕ Fin 2) K)
      (Multiplicative.ofAdd (Multiplicative.toAdd x))) = _
  rfl

@[expose] noncomputable def StdSsp (K : Type) [Field K] : Subgroup (Hsp K) :=
  (unipotent 2 K).map (eSp4 K).toMonoidHom

@[expose] noncomputable def StdQsp (K : Type) [Field K] (j : Fin 2) : Subgroup (Hsp K) :=
  (Q2 K j).map (eSp4 K).toMonoidHom

@[expose] noncomputable def StdBsp (K : Type) [Field K] : Subgroup (Hsp K) :=
  (borelSubgroup 2 K).map (eSp4 K).toMonoidHom

theorem StdQsp_eq_map (K : Type) [Field K] (j : Fin 2) :
    StdQsp K j = (Q2 K j).map (eSp4 K).toMonoidHom := rfl

theorem StdSsp_map_subtype (K : Type) [Field K] :
    (StdSsp K).map (Hsp K).subtype =
      (unipotent 2 K).map (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K)) := by
  have hcomp : (Hsp K).subtype.comp (eSp4 K).toMonoidHom =
      CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) :=
    MonoidHom.ext fun g => eSp4_apply K g
  rw [StdSsp, Subgroup.map_map, hcomp]

theorem isSylowTwoOf_StdSsp (K : Type) [Field K] [Finite K] [CharP K 2] :
    CFSG.QuasithinUnique.IsSylowTwoOf (StdSsp K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (p := 2) (K := K) (r := 2)
  have hU0 : CFSG.QuasithinUnique.IsSylowTwoOf (unipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have h := CFSG.Quasithin.H13.A5.isSylowTwoOf_map hU0 (eSp4 K).toMonoidHom
  have htop : (⊤ : Subgroup (CFSG.Open.StatedSp 2 K)).map (eSp4 K).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (eSp4 K).surjective
  dsimp only [StdSsp]
  rw [htop] at h
  exact h

theorem normalizer_StdSsp (K : Type) [Field K] :
    Subgroup.normalizer (StdSsp K : Set (Hsp K)) = StdBsp K := by
  have h := Subgroup.map_equiv_normalizer_eq (unipotent 2 K) (eSp4 K)
  rw [normalizer_unipotent] at h
  exact h.symm

@[expose] def submoduleSubSp4 (K : Type) [Field K]
    (W : Submodule K (Fin 2 ⊕ Fin 2 → K)) : Subgroup (Vsp4 K) where
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

abbrev spLineSub (K : Type) [Field K] : Subgroup (Vsp4 K) :=
  submoduleSubSp4 K (spLine K)

theorem mem_spLineSub (K : Type) [Field K] {x : Vsp4 K} :
    x ∈ spLineSub K ↔ Multiplicative.toAdd x ∈ spLine K := Iff.rfl

theorem fixV_natAut_unipotent (K : Type) [Field K] [Finite K] [CharP K 2] :
    fixV ((unipotent 2 K).map (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K))) =
      spLineSub K := by
  ext x
  constructor
  · intro hx
    rw [mem_spLineSub, mem_spLine]
    have hv : ∀ g ∈ unipotent 2 K,
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          Multiplicative.toAdd x = Multiplicative.toAdd x := by
      intro g hg
      have h := hx (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) g)
        (Subgroup.mem_map_of_mem _ hg)
      have h' := congrArg Multiplicative.toAdd h
      rw [toAdd_natAut_apply] at h'
      exact h'
    have hline := unipotent_fixed_eq_smul (Multiplicative.toAdd x) hv
    refine ⟨?_, ?_, ?_⟩
    · rw [hline]; simp
    · rw [hline]; simp
    · rw [hline]; simp
  · intro hx
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    apply Multiplicative.toAdd.injective
    rw [toAdd_natAut_apply]
    have hmem : Multiplicative.toAdd x ∈ spLine K := hx
    rw [mem_spLine] at hmem
    obtain ⟨h1, h2, h3⟩ := hmem
    have he0 : ((g : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) =
        Pi.single (Sum.inl 0) (1 : K) := by
      obtain ⟨A, C, hA, hC, hM⟩ := mem_unipotent.mp hg
      rw [hM]
      have hx1 : ((Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∘ Sum.inl) =
          (Pi.single (0 : Fin 2) (1 : K) : Fin 2 → K) := by
        funext i
        simp [Pi.single]
      have hx2 : ((Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∘ Sum.inr) =
          (0 : Fin 2 → K) := by
        funext i
        simp
      rw [blockMat, Matrix.fromBlocks_mulVec, hx1, hx2, Matrix.mulVec_zero,
        Matrix.zero_mulVec, zero_add, add_zero]
      have hcol : A.col (0 : Fin 2) = Pi.single (0 : Fin 2) (1 : K) := by
        ext i
        rw [Matrix.col_apply]
        by_cases hi : i = 0
        · subst hi; simp [hA.2 0]
        · have hpos : (0 : Fin 2) < i := Fin.pos_iff_ne_zero.mpr hi
          rw [hA.1 hpos]
          simp [Pi.single_eq_of_ne hi]
      rw [Matrix.mulVec_single_one, hcol]
      funext i
      rcases i with j | j <;> simp [Pi.single]
    have hx' : Multiplicative.toAdd x =
        (Multiplicative.toAdd x (Sum.inl 0)) • (Pi.single (Sum.inl 0) (1 : K) :
          Fin 2 ⊕ Fin 2 → K) := by
      funext i
      rcases i with j | j <;> fin_cases j <;>
        simp [h1, h2, h3, Pi.single]
    rw [hx', Matrix.mulVec_smul, he0]

theorem stabilizer_submoduleSubSp4 (K : Type) [Field K]
    (W : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    letI : MulDistribMulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) :=
      MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K))
    letI : MulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) := MulDistribMulAction.toMulAction
    letI : MulAction (CFSG.Open.StatedSp 2 K) (Set (Vsp4 K)) := Set.mulActionSet
    MulAction.stabilizer (CFSG.Open.StatedSp 2 K) (submoduleSubSp4 K W : Set (Vsp4 K)) =
      stabilizer 2 K W := by
  letI : MulDistribMulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) :=
    MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K))
  letI : MulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) := MulDistribMulAction.toMulAction
  letI : MulAction (CFSG.Open.StatedSp 2 K) (Set (Vsp4 K)) := Set.mulActionSet
  ext A
  rw [MulAction.mem_stabilizer_iff, mem_stabilizer]
  constructor
  · intro h
    apply le_antisymm
    · intro v hv
      obtain ⟨w, hw, hwv⟩ := hv
      have hw' : Multiplicative.ofAdd w ∈ (submoduleSubSp4 K W : Set (Vsp4 K)) := hw
      have h1 : A • (Multiplicative.ofAdd w) ∈ (submoduleSubSp4 K W : Set (Vsp4 K)) := by
        have hsm : A • (Multiplicative.ofAdd w) ∈
            A • (submoduleSubSp4 K W : Set (Vsp4 K)) := Set.smul_mem_smul_set hw'
        rwa [h] at hsm
      have h2 : Multiplicative.toAdd (A • Multiplicative.ofAdd w) ∈ W := h1
      change Multiplicative.toAdd
        (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) A
          (Multiplicative.ofAdd w)) ∈ W at h2
      rw [toAdd_natAut_apply, toAdd_ofAdd] at h2
      change ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w ∈ W
        at h2
      rw [← Matrix.mulVecLin_apply, hwv] at h2
      exact h2
    · intro v hv
      have hv' : Multiplicative.ofAdd v ∈ (submoduleSubSp4 K W : Set (Vsp4 K)) := hv
      have h2 : Multiplicative.ofAdd v ∈ A • (submoduleSubSp4 K W : Set (Vsp4 K)) := by
        rw [show A • (submoduleSubSp4 K W : Set (Vsp4 K)) =
          (submoduleSubSp4 K W : Set (Vsp4 K)) from h]
        exact hv'
      obtain ⟨w, hw, hwv⟩ := Set.mem_smul_set.mp h2
      refine ⟨Multiplicative.toAdd w, hw, ?_⟩
      have this := congrArg Multiplicative.toAdd hwv
      change Multiplicative.toAdd
        (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) A w) = v at this
      rw [toAdd_natAut_apply] at this
      change Multiplicative.toAdd
        (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) A w) = v
      rw [toAdd_natAut_apply]
      exact this
  · intro h
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, hwv⟩ := Set.mem_smul_set.mp hv
      have hw' : Multiplicative.toAdd w ∈ W := hw
      have h1 : ((A : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Multiplicative.toAdd w ∈ W := by
        rw [← h]
        exact ⟨w, hw', rfl⟩
      have this := congrArg Multiplicative.toAdd hwv
      change Multiplicative.toAdd v ∈ W
      rw [← this]
      change Multiplicative.toAdd
        (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) A w) ∈ W
      rwa [toAdd_natAut_apply]
    · intro hv
      have h1 : Multiplicative.toAdd v ∈ W.map
          (mulVecLin ((A : GL (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
        rw [h]
        exact hv
      obtain ⟨w, hw, hwv⟩ := h1
      refine Set.mem_smul_set.mpr ⟨Multiplicative.ofAdd w, hw, ?_⟩
      apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd
        (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) A (Multiplicative.ofAdd w)) =
        Multiplicative.toAdd v
      rw [toAdd_natAut_apply, toAdd_ofAdd]
      exact hwv

theorem Q2_zero_eq_stabilizer_spLineSub (K : Type) [Field K] :
    letI : MulDistribMulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) :=
      MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K))
    letI : MulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) := MulDistribMulAction.toMulAction
    letI : MulAction (CFSG.Open.StatedSp 2 K) (Set (Vsp4 K)) := Set.mulActionSet
    MulAction.stabilizer (CFSG.Open.StatedSp 2 K) (spLineSub K : Set (Vsp4 K)) = Q2 K 0 := by
  letI : MulDistribMulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) :=
    MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K))
  letI : MulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) := MulDistribMulAction.toMulAction
  letI : MulAction (CFSG.Open.StatedSp 2 K) (Set (Vsp4 K)) := Set.mulActionSet
  rw [show spLineSub K = submoduleSubSp4 K (spLine K) from rfl, stabilizer_submoduleSubSp4]
  rw [Q2_eq, flagStabilizer_singleton_sp]
  have h1 : ((0 : Fin 2) : ℕ) + 1 = 1 := rfl
  rw [h1, flag_one_eq]

theorem StdQsp_zero_eq_stabilizer_spLineSub (K : Type) [Field K] :
    letI : MulDistribMulAction (Hsp K) (Vsp4 K) :=
      MulDistribMulAction.compHom _ (Hsp K).subtype
    letI : MulAction (Hsp K) (Vsp4 K) := MulDistribMulAction.toMulAction
    letI : MulAction (Hsp K) (Set (Vsp4 K)) := Set.mulActionSet
    MulAction.stabilizer (Hsp K) (spLineSub K : Set (Vsp4 K)) = StdQsp K 0 := by
  letI : MulDistribMulAction (Hsp K) (Vsp4 K) :=
    MulDistribMulAction.compHom _ (Hsp K).subtype
  letI : MulAction (Hsp K) (Vsp4 K) := MulDistribMulAction.toMulAction
  letI : MulAction (Hsp K) (Set (Vsp4 K)) := Set.mulActionSet
  letI : MulDistribMulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) :=
    MulDistribMulAction.compHom _ (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K))
  letI : MulAction (CFSG.Open.StatedSp 2 K) (Vsp4 K) := MulDistribMulAction.toMulAction
  letI : MulAction (CFSG.Open.StatedSp 2 K) (Set (Vsp4 K)) := Set.mulActionSet
  have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
    (eSp4 K) (Equiv.refl (Set (Vsp4 K))) ?_ (spLineSub K : Set (Vsp4 K))
  · rw [Q2_zero_eq_stabilizer_spLineSub] at h
    rw [StdQsp]
    exact h.symm
  · intro g z
    change (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K) g) '' z =
      (eSp4 K g : MulAut (Vsp4 K)) '' z
    rw [eSp4_apply]

theorem StdQsp_one_ne_top (K : Type) [Field K] [Finite K] :
    StdQsp K 1 ≠ ⊤ := by
  have hQ2ne : Q2 K 1 ≠ ⊤ := by
    rw [Q2_eq, flagStabilizer_singleton_sp]
    have h1 : ((1 : Fin 2) : ℕ) + 1 = 2 := rfl
    rw [h1]
    exact stabilizer_flag_ne_top (K := K) (r := 2) (d := 2) (by norm_num) (by norm_num)
  intro htop
  apply hQ2ne
  have hmap : (Q2 K 1).map (eSp4 K).toMonoidHom =
      (⊤ : Subgroup (CFSG.Open.StatedSp 2 K)).map (eSp4 K).toMonoidHom := by
    rw [← StdQsp, htop]
    exact (Subgroup.map_top_of_surjective _ (eSp4 K).surjective).symm
  exact (Subgroup.map_injective (f := (eSp4 K).toMonoidHom) (eSp4 K).injective) hmap

theorem StdQsp_one_not_le_StdQsp_zero (K : Type) [Field K] :
    ¬ StdQsp K 1 ≤ StdQsp K 0 := by
  intro hle
  have hle' : Q2 K 1 ≤ Q2 K 0 := by
    have h : (Q2 K 1).map (eSp4 K).toMonoidHom ≤
        (Q2 K 0).map (eSp4 K).toMonoidHom := by
      rwa [← StdQsp, ← StdQsp]
    exact (Subgroup.map_le_map_iff_of_injective (eSp4 K).injective).mp h
  have hmem1 : weylRep K 0 ∈ Q2 K 1 := by
    rw [Q2_eq]
    have h1 : ((1 : Fin 2) : ℕ) + 1 = 2 := rfl
    rw [h1]
    exact (weylRep_mem_flagStabilizer_singleton_iff (K := K) (i := 2) (by norm_num)
      (k := 0)).mpr (by norm_num)
  have hmem0 : weylRep K 0 ∈ Q2 K 0 := hle' hmem1
  rw [Q2_eq] at hmem0
  have h0 : ((0 : Fin 2) : ℕ) + 1 = 1 := rfl
  rw [h0] at hmem0
  exact (weylRep_mem_flagStabilizer_singleton_iff (K := K) (i := 1) (by norm_num)
    (k := 0)).mp hmem0 (by norm_num)

theorem flagStabilizer_le_of_subset (K : Type) [Field K] {I J : Set ℕ} (h : J ⊆ I) :
    flagStabilizer 2 K I ≤ flagStabilizer 2 K J := by
  intro g hg
  rw [mem_flagStabilizer] at hg ⊢
  exact fun i hi => hg i (h hi)

theorem overgroup_eq_Q2_of_not_le (K : Type) [Field K] [Finite K] [CharP K 2]
    {A : Subgroup (CFSG.Open.StatedSp 2 K)} (hBA : borelSubgroup 2 K ≤ A)
    (hAne : A ≠ ⊤) (hnot : ¬ A ≤ Q2 K 0) : A = Q2 K 1 := by
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  set I := borelCuts K A with hI
  have hIsub : I ⊆ ({1, 2} : Set ℕ) := by
    rintro i ⟨k, rfl, -⟩
    fin_cases k <;> simp
  have h1not : 1 ∉ I := by
    intro h1
    apply hnot
    rw [hAeq]
    have hsub : ({1} : Set ℕ) ⊆ I := by
      intro i hi
      rw [Set.mem_singleton_iff] at hi
      subst hi
      exact h1
    have hQ : flagStabilizer 2 K ({1} : Set ℕ) = Q2 K 0 := by
      rw [Q2_eq]
      congr 1
    exact (flagStabilizer_le_of_subset K hsub).trans hQ.le
  have hI2 : I = {2} := by
    ext i
    constructor
    · intro hi
      have := hIsub hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with rfl | rfl
      · exact absurd hi h1not
      · rfl
    · intro hi
      rw [Set.mem_singleton_iff] at hi
      subst hi
      by_contra h2
      have hempty : I = ∅ := by
        ext j
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hj
        have hj' := hIsub hj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj'
        rcases hj' with rfl | rfl
        · exact h1not hj
        · exact h2 hj
      rw [hempty, flagStabilizer_empty] at hAeq
      exact hAne hAeq
  rw [hAeq, hI2]
  rw [Q2_eq]
  congr 1

theorem toBlocks₂₁_eq_zero_of_mem_Q2_one {K : Type} [Field K] {g : StatedSp 2 K}
    (hg : g ∈ Q2 K 1) : (spMat g).toBlocks₂₁ = 0 := by
  ext i k
  exact spMat_inr_inl_of_mem_Q2_one hg i k

theorem mk''_coe {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (h : IsUnit A.det) :
    ((Matrix.GeneralLinearGroup.mk'' A h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = A := by
  rw [Matrix.GeneralLinearGroup.mk'', Matrix.nonsingInvUnit, val_unitOfInvertible]

theorem toBlocks₁₁_mul_of_lower_zero {K : Type} [Field K]
    {A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : A.toBlocks₂₁ = 0) (hB : B.toBlocks₂₁ = 0) :
    (A * B).toBlocks₁₁ = A.toBlocks₁₁ * B.toBlocks₁₁ := by
  rw [← Matrix.fromBlocks_toBlocks A, ← Matrix.fromBlocks_toBlocks B, hA, hB,
    Matrix.fromBlocks_multiply]
  simp

noncomputable def blkGL {K : Type} [Field K] : ↥(Q2 K 1) →* GL (Fin 2) K where
  toFun g := Matrix.GeneralLinearGroup.mk'' ((spMat g.1).toBlocks₁₁) (by
    obtain ⟨hA, -⟩ :=
      exists_blockMat_of_toBlocks₂₁_eq_zero (toBlocks₂₁_eq_zero_of_mem_Q2_one g.2)
    exact hA)
  map_one' := by
    apply Units.ext
    rw [mk''_coe]
    ext i j
    change ((1 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl i) (Sum.inl j) = (1 : Matrix (Fin 2) (Fin 2) K) i j
    simp [Matrix.one_apply]
  map_mul' g h := by
    apply Units.ext
    rw [Units.val_mul]
    conv_rhs => rw [mk''_coe, mk''_coe]
    rw [mk''_coe]
    change (spMat ((g : StatedSp 2 K) * (h : StatedSp 2 K))).toBlocks₁₁ =
      (spMat (g : StatedSp 2 K)).toBlocks₁₁ * (spMat (h : StatedSp 2 K)).toBlocks₁₁
    rw [spMat_mul, toBlocks₁₁_mul_of_lower_zero (toBlocks₂₁_eq_zero_of_mem_Q2_one g.2)
      (toBlocks₂₁_eq_zero_of_mem_Q2_one h.2)]

theorem blkGL_ker_le_radical {K : Type} [Field K] {g : ↥(Q2 K 1)}
    (hg : blkGL (K := K) g = 1) : (g : StatedSp 2 K) ∈ SymplecticFour.radical K := by
  have hblock : (spMat (g : StatedSp 2 K)).toBlocks₁₁ = 1 := by
    have h := congrArg (fun u : GL (Fin 2) K => ((u : Matrix (Fin 2) (Fin 2) K))) hg
    change ((Matrix.GeneralLinearGroup.mk'' ((spMat (g : StatedSp 2 K)).toBlocks₁₁) _ :
      GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 at h
    rw [mk''_coe] at h
    simpa using h
  obtain ⟨-, C, hC, hM⟩ :=
    exists_blockMat_of_toBlocks₂₁_eq_zero (toBlocks₂₁_eq_zero_of_mem_Q2_one g.2)
  have hM' : spMat (g : StatedSp 2 K) =
      blockMat ((spMat (g : StatedSp 2 K)).toBlocks₁₁) C := hM
  refine ⟨C, hC, ?_⟩
  apply Subtype.ext
  apply Units.ext
  change spMat (g : StatedSp 2 K) = spMat (SymplecticFour.tau hC)
  rw [hM', hblock]
  rw [show spMat (SymplecticFour.tau hC) = Matrix.fromBlocks 1 C 0 1 from
    SymplecticFour.coe_tau hC]
  simp [blockMat]

theorem isSolvable_Q2_one_of_card_two {K : Type} [Field K] [Finite K]
    (hK2 : Nat.card K = 2) : Group.IsSolvable ↥(Q2 K 1) := by
  have hrad : SymplecticFour.radical K ≤ Q2 K 1 :=
    SymplecticFour.radical_le_unipotent.trans
      (unipotent_le_borelSubgroup.trans (borelSubgroup_le_Q2 1))
  haveI : IsPGroup 2 (SymplecticFour.radical K) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [SymplecticFour.card_radical, hK2]
  haveI : Group.IsSolvable ↥(SymplecticFour.radical K) := by
    have := (‹IsPGroup 2 (SymplecticFour.radical K)›).isNilpotent
    infer_instance
  haveI : Group.IsSolvable (GL (Fin 2) K) := by
    have : Fintype K := Fintype.ofFinite K
    have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK2
    refine isSolvable_of_card_two_three (a := 1) (b := 1) ?_
    rw [Matrix.card_GL_field]
    rw [hF]
    simp [Fin.prod_univ_two]
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hrad) (blkGL (K := K)) ?_
  intro x hx
  refine ⟨⟨(x : StatedSp 2 K), blkGL_ker_le_radical hx⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem perfectCore_Q2_one_eq_bot_of_card_two {K : Type} [Field K] [Finite K]
    (hK2 : Nat.card K = 2) : perfectCore (Q2 K 1) = ⊥ := by
  haveI := isSolvable_Q2_one_of_card_two hK2
  exact (isSolvable_iff_perfectCore_eq_bot (Q2 K 1)).mp inferInstance

theorem isL2_bar2_perfectCore_Q2_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    IsL2 (Bar2 (perfectCore (Q2 K 1))) n := by
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnab := sl2_nonabelian (K := K) hK4
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := sl2_isSimple (K := K) hK4
  have hmodel : CFSG.Blueprint.LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 n :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (K := K) (m := 2) (f := n)
        (by norm_num) hn hK)
  let e : Bar2 (perfectCore (Q2 K 1)) ≃* StatedProj (StatedSL 2 K) :=
    (modO2EquivOfHom hnab (blkN (K := K) 1) (blkN_surjective hK4 1)
      (blkN_ker_isPGroup ⟨n, hK⟩ 1)).trans sl2EquivStatedProj
  exact CFSG.Blueprint.LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n)
    e.symm hmodel

theorem eq_StdQsp_one_of_overgroup {K : Type} [Field K] [Finite K] [CharP K 2]
    (S : Sylow 2 (Hsp K)) (h : ↥(Hsp K))
    (hconj : (S : Subgroup (Hsp K)) = (StdSsp K).map (MulAut.conj h).toMonoidHom)
    {A : Subgroup (Hsp K)}
    (hBA : Subgroup.normalizer (S : Set (Hsp K)) ≤ A)
    (hAne : A ≠ ⊤)
    (hnot : ¬ A ≤ (StdQsp K 0).map (MulAut.conj h).toMonoidHom) :
    A = (StdQsp K 1).map (MulAut.conj h).toMonoidHom := by
  have hcomp : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
      MonoidHom.id (Hsp K) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp' : ((MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom) =
      MonoidHom.id (Hsp K) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  let A₀ : Subgroup (Hsp K) := A.map (MulAut.conj h⁻¹).toMonoidHom
  have hAeq : A₀.map (MulAut.conj h).toMonoidHom = A := by
    change (A.map (MulAut.conj h⁻¹).toMonoidHom).map (MulAut.conj h).toMonoidHom = A
    rw [Subgroup.map_map, hcomp', Subgroup.map_id]
  have hB : Subgroup.normalizer (S : Set (Hsp K)) =
      (StdBsp K).map (MulAut.conj h).toMonoidHom := by
    change Subgroup.normalizer ((S : Subgroup (Hsp K)) : Set (Hsp K)) = _
    rw [hconj, ← Subgroup.map_equiv_normalizer_eq (StdSsp K) (MulAut.conj h),
      normalizer_StdSsp]
  have hB0 : StdBsp K ≤ A₀ := by
    have hm := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hBA
    rw [hB, Subgroup.map_map, hcomp, Subgroup.map_id] at hm
    exact hm
  have hA₀ne : A₀ ≠ ⊤ := by
    intro htop
    apply hAne
    rw [← hAeq, htop, Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective]
  have hnot0 : ¬ A₀ ≤ StdQsp K 0 := by
    intro hle
    apply hnot
    have hm := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hle
    rw [hAeq] at hm
    exact hm
  let A₁ : Subgroup (StatedSp 2 K) := A₀.comap (eSp4 K).toMonoidHom
  have hA₁map : A₁.map (eSp4 K).toMonoidHom = A₀ :=
    Subgroup.map_comap_eq_self_of_surjective (eSp4 K).surjective A₀
  have hA₁B : borelSubgroup 2 K ≤ A₁ := by
    rw [← Subgroup.map_le_iff_le_comap]
    rw [show (borelSubgroup 2 K).map (eSp4 K).toMonoidHom = StdBsp K from rfl]
    exact hB0
  have htopmap : (⊤ : Subgroup (StatedSp 2 K)).map (eSp4 K).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (eSp4 K).surjective
  have hA₁ne : A₁ ≠ ⊤ := by
    intro htop
    apply hA₀ne
    rw [← hA₁map, htop, htopmap]
  have hnot1 : ¬ A₁ ≤ Q2 K 0 := by
    intro hle
    apply hnot0
    have hm := Subgroup.map_mono (f := (eSp4 K).toMonoidHom) hle
    rw [hA₁map] at hm
    rw [StdQsp_eq_map]
    exact hm
  have hA₁eq := overgroup_eq_Q2_of_not_le K hA₁B hA₁ne hnot1
  have hA₀eq : A₀ = StdQsp K 1 := by
    rw [← hA₁map, hA₁eq, StdQsp_eq_map]
  rw [← hAeq, hA₀eq]

theorem sp4NaturalLine_holds : Sp4NaturalLine := by
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
  change Sp4Line (Vsp4 K) (Hsp K) n
  unfold Sp4Line
  intro S
  intro ℓ Pℓ
  intro Tstar hTnorm hT2 hST
  intro Good Pstar hmin
  classical
  have hSylS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥(Hsp K)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hSylStd : CFSG.QuasithinUnique.IsSylowTwoOf (StdSsp K) ⊤ := isSylowTwoOf_StdSsp K
  obtain ⟨h, -, hconj⟩ :=
    CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hSylStd hSylS
  let SH : Subgroup (MulAut (Vsp4 K)) := (S : Subgroup ↥(Hsp K)).map (Hsp K).subtype
  have hcomp : (Hsp K).subtype.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj ((h : ↥(Hsp K)) : MulAut (Vsp4 K))).toMonoidHom.comp (Hsp K).subtype := by
    ext x
    rfl
  have hSH : SH =
      ((unipotent 2 K).map (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K))).map
        (MulAut.conj ((h : ↥(Hsp K)) : MulAut (Vsp4 K))).toMonoidHom := by
    dsimp [SH]
    rw [hconj, Subgroup.map_map, hcomp, ← Subgroup.map_map, StdSsp_map_subtype]
    rfl
  have hℓ : ℓ = (spLineSub K).map ((h : ↥(Hsp K)) : MulAut (Vsp4 K)).toMonoidHom := by
    have h1 : ℓ = fixV SH := by
      dsimp [ℓ, SH]
      rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
    rw [h1, hSH, fixV_map_conj, fixV_natAut_unipotent]
  have hPℓ : Pℓ = (StdQsp K 0).map (MulAut.conj h).toMonoidHom := by
    have hstab := stabilizer_map_conj_subgroup (H := Hsp K) h (spLineSub K)
    dsimp [Pℓ]
    rw [hℓ]
    change MulAction.stabilizer (Hsp K)
      (((spLineSub K).map ((h : ↥(Hsp K)) : MulAut (Vsp4 K)).toMonoidHom :
        Subgroup (Vsp4 K)) : Set (Vsp4 K)) =
      (StdQsp K 0).map (MulAut.conj h).toMonoidHom
    have hstabQ0 : MulAction.stabilizer (Hsp K) (spLineSub K : Set (Vsp4 K)) = StdQsp K 0 :=
      StdQsp_zero_eq_stabilizer_spLineSub K
    exact hstab.trans (congrArg (fun X : Subgroup (Hsp K) => X.map (MulAut.conj h).toMonoidHom) hstabQ0)
  have hSylUH : CFSG.QuasithinUnique.IsSylowTwoOf
      ((unipotent 2 K).map (CFSG.Quasithin.H.natAut (CFSG.Open.StatedSp 2 K))) (Hsp K) := by
    have h := CFSG.Quasithin.H13.A5.isSylowTwoOf_map (isSylowTwoOf_StdSsp K) (Hsp K).subtype
    rwa [show (⊤ : Subgroup (Hsp K)).map (Hsp K).subtype = Hsp K from by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype], StdSsp_map_subtype] at h
  have hTstarH : Tstar ⊓ Hsp K = SH := by
    have hHmap : (Hsp K).map (MulAut.conj ((h : ↥(Hsp K)) : MulAut (Vsp4 K))).toMonoidHom =
        Hsp K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer h.2)
    have hSylSH : CFSG.QuasithinUnique.IsSylowTwoOf SH (Hsp K) := by
      have h := hSylUH.map_equiv (MulAut.conj ((h : ↥(Hsp K)) : MulAut (Vsp4 K)))
      rwa [← hSH, hHmap] at h
    have hX2 : IsPGroup 2 ↥(Tstar ⊓ Hsp K) := by
      intro x
      obtain ⟨k, hk⟩ := hT2 ⟨(x : MulAut (Vsp4 K)), x.2.1⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    exact hSylSH.eq_of_le (le_inf hST (Subgroup.map_subtype_le _)) inf_le_right hX2
  have htopH : (⊤ : Subgroup (Hsp K)).map (Hsp K).subtype = Hsp K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hSH_normal : ∀ t ∈ Tstar, SH.map (MulAut.conj t).toMonoidHom = SH := by
    intro t ht
    have hle : SH.map (MulAut.conj t).toMonoidHom ≤ SH := by
      rintro x ⟨s, hs, rfl⟩
      obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.mp hs
      have htH : t * (s0 : MulAut (Vsp4 K)) * t⁻¹ ∈ Hsp K :=
        ((Subgroup.mem_normalizer_iff.mp (hTnorm ht)) (s0 : MulAut (Vsp4 K))).mp s0.2
      have hmem : t * (s0 : MulAut (Vsp4 K)) * t⁻¹ ∈ Tstar ⊓ Hsp K :=
        ⟨Tstar.mul_mem (Tstar.mul_mem ht (hST (Subgroup.mem_map_of_mem (Hsp K).subtype hs0)))
            (Tstar.inv_mem ht), htH⟩
      rwa [hTstarH] at hmem
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective])
  have hSHsub : SH.subgroupOf (Hsp K) = (S : Subgroup (Hsp K)) := by
    ext x
    constructor
    · intro hx
      exact (Subgroup.mem_map_iff_mem (Hsp K).subtype_injective).mp hx
    · intro hx
      exact Subgroup.mem_map_of_mem _ hx
  have hB_amb : (Subgroup.normalizer (S : Set (Hsp K))).map (Hsp K).subtype =
      Subgroup.normalizer (SH : Set (MulAut (Vsp4 K))) ⊓ Hsp K := by
    change (Subgroup.normalizer ((S : Subgroup (Hsp K)) : Set (Hsp K))).map
      (Hsp K).subtype = Subgroup.normalizer (SH : Set (MulAut (Vsp4 K))) ⊓ Hsp K
    have hSHle : SH ≤ Hsp K := by
      rintro _ ⟨s, hs, rfl⟩
      exact s.2
    have h1 := Subgroup.subgroupOf_normalizer_eq (H := SH) (N := Hsp K) hSHle
    rw [hSHsub] at h1
    rw [← h1, Subgroup.subgroupOf_map_subtype]
  have hSHnorm : ∀ t ∈ Tstar,
      (Subgroup.normalizer (SH : Set (MulAut (Vsp4 K)))).map (MulAut.conj t).toMonoidHom =
        Subgroup.normalizer (SH : Set (MulAut (Vsp4 K))) := by
    intro t ht
    rw [Subgroup.map_equiv_normalizer_eq SH (MulAut.conj t), hSH_normal t ht]
  have hH_T : ∀ t ∈ Tstar, (Hsp K).map (MulAut.conj t).toMonoidHom = Hsp K := by
    intro t ht
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht)
  have hB_T : ∀ t ∈ Tstar,
      ((Subgroup.normalizer (S : Set (Hsp K))).map (Hsp K).subtype).map
        (MulAut.conj t).toMonoidHom =
      (Subgroup.normalizer (S : Set (Hsp K))).map (Hsp K).subtype := by
    intro t ht
    rw [hB_amb, Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective,
      hSHnorm t ht, hH_T t ht]
  have hℓ_T : ∀ t ∈ Tstar, ℓ.map (t : MulAut (Vsp4 K)).toMonoidHom = ℓ := by
    intro t ht
    have h1 : ℓ = fixV SH := by
      dsimp [ℓ, SH]
      rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
    rw [h1, ← fixV_map_conj SH t, hSH_normal t ht, ← h1]
  have hPℓ_T : ∀ t ∈ Tstar,
      (Pℓ.map (Hsp K).subtype).map (MulAut.conj t).toMonoidHom =
        Pℓ.map (Hsp K).subtype := by
    intro t ht
    dsimp [Pℓ]
    have h := map_subtype_stabilizer_conj_normalizer (H := Hsp K) t (hTnorm ht) ℓ
    have hset : ((t : MulAut (Vsp4 K)) '' (ℓ : Set (Vsp4 K))) = (ℓ : Set (Vsp4 K)) := by
      have h' := hℓ_T t ht
      exact congrArg (fun X : Subgroup (Vsp4 K) => (X : Set (Vsp4 K))) h'
    simpa [hset] using h
  let Qplane : Subgroup (Hsp K) := (StdQsp K 1).map (MulAut.conj h).toMonoidHom
  have hS_le_Q : (S : Subgroup (Hsp K)) ≤ Qplane := by
    rw [hconj]
    dsimp only [Qplane]
    exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
      (Subgroup.map_mono (f := (eSp4 K).toMonoidHom)
        (unipotent_le_borelSubgroup.trans (borelSubgroup_le_Q2 1)))
  have hB : Subgroup.normalizer (S : Set (Hsp K)) =
      (StdBsp K).map (MulAut.conj h).toMonoidHom := by
    change Subgroup.normalizer ((S : Subgroup (Hsp K)) : Set (Hsp K)) = _
    rw [hconj, ← Subgroup.map_equiv_normalizer_eq (StdSsp K) (MulAut.conj h),
      normalizer_StdSsp]
  have hB_Q : Subgroup.normalizer (S : Set (Hsp K)) ≤ Qplane := by
    rw [hB]
    dsimp only [Qplane]
    exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
      (Subgroup.map_mono (f := (eSp4 K).toMonoidHom) (borelSubgroup_le_Q2 1))
  have hQpar : IsParabolicTwo ↥(Hsp K) Qplane := ⟨S, hB_Q⟩
  have hQne : Qplane ≠ ⊤ := by
    intro htop
    apply StdQsp_one_ne_top K
    have hmap := congrArg (fun X : Subgroup (Hsp K) =>
      X.map (MulAut.conj h⁻¹).toMonoidHom) htop
    rw [Subgroup.map_map,
      show ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
        MonoidHom.id (Hsp K) from by ext x; simp [MulAut.conj_apply, mul_assoc],
      Subgroup.map_id, Subgroup.map_top_of_surjective _ (MulAut.conj h⁻¹).surjective] at hmap
    exact hmap
  have hQnotLePℓ : ¬ Qplane ≤ Pℓ := by
    intro hle
    apply StdQsp_one_not_le_StdQsp_zero K
    have hm := Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hle
    rw [hPℓ] at hm
    rw [Subgroup.map_map,
      show ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
        MonoidHom.id (Hsp K) from by ext x; simp [MulAut.conj_apply, mul_assoc],
      Subgroup.map_id, Subgroup.map_map,
      show ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
        MonoidHom.id (Hsp K) from by ext x; simp [MulAut.conj_apply, mul_assoc],
      Subgroup.map_id] at hm
    exact hm
  have hQgoodT : ∀ t ∈ Tstar,
      (Qplane.map (Hsp K).subtype).map (MulAut.conj t).toMonoidHom =
        Qplane.map (Hsp K).subtype := by
    intro t ht
    let At : Subgroup (MulAut (Vsp4 K)) :=
      (Qplane.map (Hsp K).subtype).map (MulAut.conj t).toMonoidHom
    have hAt_le : At ≤ Hsp K := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
      exact (Subgroup.mem_normalizer_iff.mp (hTnorm ht) (q : MulAut (Vsp4 K))).mp q.2
    let Q' : Subgroup (Hsp K) := At.subgroupOf (Hsp K)
    have hQ'map : Q'.map (Hsp K).subtype = At :=
      Subgroup.map_subgroupOf_eq_of_le hAt_le
    have hQ'B : Subgroup.normalizer (S : Set (Hsp K)) ≤ Q' := by
      intro x hx
      have hxAt : (x : MulAut (Vsp4 K)) ∈ At := by
        have h1 := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom)
          (Subgroup.map_mono (f := (Hsp K).subtype) hB_Q)
        rw [hB_T t ht] at h1
        exact h1 (Subgroup.mem_map_of_mem _ hx)
      exact hxAt
    have hQ'ne : Q' ≠ ⊤ := by
      intro htop
      have hAtTop : At = Hsp K := by
        rw [← hQ'map, htop]
        exact htopH
      have hQtop : Qplane.map (Hsp K).subtype = Hsp K := by
        have h := congrArg (fun X : Subgroup (MulAut (Vsp4 K)) =>
          X.map (MulAut.conj t⁻¹).toMonoidHom) hAtTop
        rw [Subgroup.map_map,
          show ((MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom) =
            MonoidHom.id (MulAut (Vsp4 K)) from by ext x; simp [MulAut.conj_apply, mul_assoc],
          Subgroup.map_id] at h
        rwa [hH_T t⁻¹ (Tstar.inv_mem ht)] at h
      apply hQne
      apply (Subgroup.map_injective (f := (Hsp K).subtype) (Hsp K).subtype_injective)
      rw [hQtop, htopH]
    have hQ'not : ¬ Q' ≤ Pℓ := by
      intro hle
      apply hQnotLePℓ
      have hAtP : At ≤ Pℓ.map (Hsp K).subtype := by
        rw [← hQ'map]
        exact Subgroup.map_mono (f := (Hsp K).subtype) hle
      have h2 := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hAtP
      rw [Subgroup.map_map,
        show ((MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom) =
          MonoidHom.id (MulAut (Vsp4 K)) from by ext x; simp [MulAut.conj_apply, mul_assoc],
        Subgroup.map_id] at h2
      rw [hPℓ_T t⁻¹ (Tstar.inv_mem ht)] at h2
      exact (Subgroup.map_le_map_iff_of_injective (Hsp K).subtype_injective).mp h2
    have hQ'eq : Q' = Qplane := by
      have hQ'not' : ¬ Q' ≤ (StdQsp K 0).map (MulAut.conj h).toMonoidHom := by
        rwa [← hPℓ]
      exact eq_StdQsp_one_of_overgroup S h hconj hQ'B hQ'ne hQ'not'
    change At = Qplane.map (Hsp K).subtype
    rw [← hQ'map, hQ'eq]
  have hQgood : Good Qplane := ⟨hQpar, hS_le_Q, hQgoodT, hQnotLePℓ⟩
  have hPstar_ne_top : Pstar ≠ ⊤ := by
    intro htop
    have hle : (⊤ : Subgroup (Hsp K)) ≤ Qplane := by
      rw [← htop]
      exact hmin.2 hQgood (by rw [htop]; exact le_top)
    exact hQne (top_le_iff.mp hle)
  have hnotPstar : ¬ Pstar ≤ (StdQsp K 0).map (MulAut.conj h).toMonoidHom := by
    rw [← hPℓ]
    exact hmin.1.2.2.2
  have hPstar_eq : Pstar = (StdQsp K 1).map (MulAut.conj h).toMonoidHom :=
    eq_StdQsp_one_of_overgroup S h hconj (hmin.1.1.normalizer_le S hmin.1.2.1)
      hPstar_ne_top hnotPstar
  refine ⟨?_, ?_⟩
  · rw [hPstar_eq]
    exact hQne
  · by_cases hn : n = 1
    · right
      refine ⟨hn, ?_⟩
      have hK2 : Nat.card K = 2 := by rw [hK, hn]; norm_num
      have hstdBot : Hinf (StdQsp K 1) = ⊥ := by
        rw [StdQsp_eq_map]
        exact Hinf_map_eq_bot (eSp4 K) (Q2 K 1)
          (by rw [Hinf_eq_perfectCore]; exact perfectCore_Q2_one_eq_bot_of_card_two hK2)
      rw [hPstar_eq]
      exact Hinf_map_eq_bot (MulAut.conj h) (StdQsp K 1) hstdBot
    · left
      have hn2 : 2 ≤ n := by omega
      have hstd : IsL2 (Bar2 (Hinf (StdQsp K 1))) n := by
        rw [StdQsp_eq_map]
        exact isL2_bar2_hinf_map_equiv (eSp4 K) (Q2 K 1)
          (by rw [Hinf_eq_perfectCore]; exact isL2_bar2_perfectCore_Q2_one hK hn2)
      rw [hPstar_eq]
      exact isL2_bar2_hinf_map_equiv (MulAut.conj h) (StdQsp K 1) hstd

theorem kTab23b_Sp4_line_uncond_final (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) :
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
  kTab23b_Sp4_line_uncond W H n hnat hperf hline sp4NaturalLine_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
