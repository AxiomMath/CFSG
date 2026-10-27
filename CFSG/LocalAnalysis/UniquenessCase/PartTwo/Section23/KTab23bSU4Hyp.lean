module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSU4
public import CFSG.Quasithin.H13.U4ParLineQuot
public import CFSG.LocalAnalysis.WeakClosure81.W15SixC
import CFSG.GroupTheory.PerfectTwoQuotient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par CFSG.Quasithin.H13.A5 CFSG.QuasithinUnique
open scoped Pointwise commutatorElement Matrix

@[expose] def subMul {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (W : Submodule K (ι → K)) : Subgroup (CFSG.Quasithin.H.StdMod ι K) :=
  W.toAddSubgroup.toSubgroup

@[simp] theorem mem_subMul {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {W : Submodule K (ι → K)} {x : CFSG.Quasithin.H.StdMod ι K} :
    x ∈ subMul W ↔ Multiplicative.toAdd x ∈ W := by
  simp [subMul]

theorem subMul_injective {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] :
    Function.Injective (subMul : Submodule K (ι → K) → Subgroup (CFSG.Quasithin.H.StdMod ι K)) := by
  intro W W' h
  have h' : W.toAddSubgroup = W'.toAddSubgroup := by
    simpa [subMul] using congrArg Subgroup.toAddSubgroup' h
  exact Submodule.toAddSubgroup_injective h'

theorem subMul_smul {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (g : GL ι K) (W : Submodule K (ι → K)) :
    subMul (W.map (Matrix.mulVecLin (g : Matrix ι ι K))) =
      CFSG.Quasithin.H.matAut g • subMul W := by
  classical
  have hinv : (CFSG.Quasithin.H.matAut g)⁻¹ = CFSG.Quasithin.H.matAut g⁻¹ := by
    simpa only [CFSG.Quasithin.H.matHom_apply] using
      (map_inv CFSG.Quasithin.H.matHom g).symm
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    rw [mem_subMul, Submodule.mem_map] at hx
    obtain ⟨b, hb, hb_eq⟩ := hx
    have hb_eq' : ((g : GL ι K) : Matrix ι ι K) *ᵥ b = Multiplicative.toAdd x := by
      simpa [Matrix.mulVecLin_apply] using hb_eq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rw [hinv, mem_subMul]
    change Multiplicative.toAdd (CFSG.Quasithin.H.matAut g⁻¹ x) ∈ W
    rw [show Multiplicative.toAdd (CFSG.Quasithin.H.matAut g⁻¹ x) =
        ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd x from rfl,
      ← hb_eq', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hb
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    rw [hinv, mem_subMul] at hx
    change Multiplicative.toAdd (CFSG.Quasithin.H.matAut g⁻¹ x) ∈ W at hx
    rw [mem_subMul, Submodule.mem_map]
    refine ⟨Multiplicative.toAdd (CFSG.Quasithin.H.matAut g⁻¹ x), hx, ?_⟩
    change Matrix.mulVecLin ((g : GL ι K) : Matrix ι ι K)
      (Multiplicative.toAdd (CFSG.Quasithin.H.matAut g⁻¹ x)) = Multiplicative.toAdd x
    rw [Matrix.mulVecLin_apply]
    change (((g : GL ι K) : Matrix ι ι K) *ᵥ
      ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd x) =
      Multiplicative.toAdd x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]

variable {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)

abbrev HypV : Type := CFSG.Quasithin.H.StdMod (HypIndex 2 0) K

noncomputable abbrev hypPi : ↥(hypSU h 2 0) →* MulAut (HypV (K := K)) :=
  CFSG.Quasithin.H.matHom.comp (hypSU h 2 0).subtype

noncomputable abbrev hypH : Subgroup (MulAut (HypV (K := K))) :=
  (hypSU h 2 0).map CFSG.Quasithin.H.matHom

theorem hypH_eq_top_map : hypH h = (⊤ : Subgroup ↥(hypSU h 2 0)).map (hypPi h) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, trivial, rfl⟩
  · rintro ⟨g, -, rfl⟩
    exact ⟨(g : GL (HypIndex 2 0) K), g.2, rfl⟩

noncomputable abbrev hypEH :
    ↥(hypSU h 2 0) ≃* ↥(hypH h) :=
  Subgroup.equivMapOfInjective (hypSU h 2 0) CFSG.Quasithin.H.matHom
    CFSG.Quasithin.H.matHom_injective

theorem hypEH_coe (g : ↥(hypSU h 2 0)) :
    ((hypEH h g : ↥(hypH h)) : MulAut (HypV (K := K))) = hypPi h g := rfl

noncomputable abbrev hypUH : Subgroup ↥(hypH h) :=
  (hypUnitriangular h 2 0).map (hypEH h).toMonoidHom

noncomputable abbrev hypBH : Subgroup ↥(hypH h) :=
  (hypBorel h 2 0).map (hypEH h).toMonoidHom

noncomputable abbrev hypPH : Subgroup ↥(hypH h) :=
  (parP h).map (hypEH h).toMonoidHom

noncomputable abbrev hypP2H : Subgroup ↥(hypH h) :=
  (parP2 h).map (hypEH h).toMonoidHom

noncomputable abbrev hypU : Subgroup (MulAut (HypV (K := K))) :=
  (hypUnitriangular h 2 0).map (hypPi h)

noncomputable abbrev hypB : Subgroup (MulAut (HypV (K := K))) :=
  (hypBorel h 2 0).map (hypPi h)

noncomputable abbrev hypP : Subgroup (MulAut (HypV (K := K))) :=
  (parP h).map (hypPi h)

noncomputable abbrev hypP2 : Subgroup (MulAut (HypV (K := K))) :=
  (parP2 h).map (hypPi h)

theorem hypU_eq_map_subtype : hypU h = ((hypUnitriangular h 2 0).map
    (hypSU h 2 0).subtype).map CFSG.Quasithin.H.matHom := by
  rw [hypU, Subgroup.map_map]

theorem hypB_eq_map_subtype : hypB h = ((hypBorel h 2 0).map
    (hypSU h 2 0).subtype).map CFSG.Quasithin.H.matHom := by
  rw [hypB, Subgroup.map_map]

theorem hypP_eq_map_subtype : hypP h = ((parP h).map
    (hypSU h 2 0).subtype).map CFSG.Quasithin.H.matHom := by
  rw [hypP, Subgroup.map_map]

theorem hypP2_eq_map_subtype : hypP2 h = ((parP2 h).map
    (hypSU h 2 0).subtype).map CFSG.Quasithin.H.matHom := by
  rw [hypP2, Subgroup.map_map]

theorem fixV_hypU : fixV (hypU h) = subMul (hypFlag h 2 0 1) := by
  ext x
  rw [mem_fixV, mem_subMul]
  constructor
  · intro hx
    have hv : ∀ u ∈ hypUnitriangular h 2 0,
        (((u : hypSU h 2 0) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
          Multiplicative.toAdd x = Multiplicative.toAdd x := by
      intro u hu
      have hmem : hypPi h (u : ↥(hypSU h 2 0)) ∈ hypU h :=
        Subgroup.mem_map_of_mem _ hu
      have h1 := hx _ hmem
      have h1' : CFSG.Quasithin.H.matAut (u : GL (HypIndex 2 0) K) x = x := h1
      have := congrArg Multiplicative.toAdd h1'
      change (((u : hypSU h 2 0) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ Multiplicative.toAdd x =
        Multiplicative.toAdd x at this
      exact this
    exact ((UnitaryHigher.unitriangular_invariant_isotropic_subspaces h (by norm_num)
      (by norm_num)).2.1 (Multiplicative.toAdd x)).mp hv
  · intro hx u hu
    obtain ⟨u0, hu0, rfl⟩ := Subgroup.mem_map.mp hu
    apply Multiplicative.toAdd.injective
    change (((u0 : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
      Multiplicative.toAdd x) = Multiplicative.toAdd x
    exact ((UnitaryHigher.unitriangular_invariant_isotropic_subspaces h (by norm_num)
      (by norm_num)).2.1 (Multiplicative.toAdd x)).mpr hx u0 hu0


theorem subMul_smul_hypSU (g : ↥(hypSU h 2 0)) (W : Submodule K (HypIndex 2 0 → K)) :
    subMul (g • W) = hypPi h g • subMul W := by
  change subMul (W.map (Matrix.mulVecLin ((g : GL (HypIndex 2 0) K) :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K))) =
      CFSG.Quasithin.H.matAut (g : GL (HypIndex 2 0) K) • subMul W
  exact subMul_smul (g : GL (HypIndex 2 0) K) W

theorem smul_set_hypH_eq (g : ↥(hypSU h 2 0)) (W : Submodule K (HypIndex 2 0 → K)) :
    letI : MulDistribMulAction ↥(hypH h) (HypV (K := K)) :=
      MulDistribMulAction.compHom _ (hypH h).subtype
    letI : MulAction ↥(hypH h) (HypV (K := K)) := MulDistribMulAction.toMulAction
    letI : MulAction ↥(hypH h) (Set (HypV (K := K))) := Set.mulActionSet
    ((hypEH h).toMonoidHom g : ↥(hypH h)) • (subMul W : Set (HypV (K := K))) =
      (hypPi h g : MulAut (HypV (K := K))) • (subMul W : Set (HypV (K := K))) := by
  letI : MulDistribMulAction ↥(hypH h) (HypV (K := K)) :=
    MulDistribMulAction.compHom _ (hypH h).subtype
  letI : MulAction ↥(hypH h) (HypV (K := K)) := MulDistribMulAction.toMulAction
  letI : MulAction ↥(hypH h) (Set (HypV (K := K))) := Set.mulActionSet
  ext y
  rw [Set.mem_smul_set, Set.mem_smul_set]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, hz, by simpa [MulAction.compHom_smul_def, hypEH_coe h g] using hzy⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, hz, by simpa [MulAction.compHom_smul_def, hypEH_coe h g] using hzy⟩

theorem stabilizer_subMul_hypFlag :
    letI : MulDistribMulAction ↥(hypH h) (HypV (K := K)) :=
      MulDistribMulAction.compHom _ (hypH h).subtype
    letI : MulAction ↥(hypH h) (HypV (K := K)) := MulDistribMulAction.toMulAction
    letI : MulAction ↥(hypH h) (Set (HypV (K := K))) := Set.mulActionSet
    MulAction.stabilizer ↥(hypH h) (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) =
      hypPH h := by
  letI : MulDistribMulAction ↥(hypH h) (HypV (K := K)) :=
    MulDistribMulAction.compHom _ (hypH h).subtype
  letI : MulAction ↥(hypH h) (HypV (K := K)) := MulDistribMulAction.toMulAction
  letI : MulAction ↥(hypH h) (Set (HypV (K := K))) := Set.mulActionSet
  have hact : ∀ (g : ↥(hypSU h 2 0)) (W : Submodule K (HypIndex 2 0 → K)),
      hypPi h g • subMul W = subMul (g • W) := fun g W => (subMul_smul_hypSU h g W).symm
  apply le_antisymm
  · intro x hx
    let g : ↥(hypSU h 2 0) := (hypEH h).symm x
    have hx' : x • (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) =
        (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) :=
      MulAction.mem_stabilizer_iff.mp hx
    have hx''set : (hypPi h g : MulAut (HypV (K := K))) •
        (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) =
        (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) := by
      have hx''' : ((hypEH h g : ↥(hypH h)) : MulAut (HypV (K := K))) •
          (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) =
          (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) := by
        rw [hypEH_coe h g]
        rw [← smul_set_hypH_eq h g (hypFlag h 2 0 1)]
        simpa [g] using hx'
      simpa [hypEH_coe h g] using hx'''
    have hx'' : hypPi h g • subMul (hypFlag h 2 0 1) = subMul (hypFlag h 2 0 1) :=
      SetLike.coe_injective hx''set
    have hg : g • hypFlag h 2 0 1 = hypFlag h 2 0 1 := by
      apply subMul_injective
      rw [← hact g (hypFlag h 2 0 1)]
      exact hx''
    exact Subgroup.mem_map.mpr ⟨g, hg, by simp [g]⟩
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MulAction.mem_stabilizer_iff]
    have hfix : g • hypFlag h 2 0 1 = hypFlag h 2 0 1 :=
      UnitaryHigher.mem_isoStabilizer.mp hg
    have h1 : hypPi h g • subMul (hypFlag h 2 0 1) = subMul (hypFlag h 2 0 1) := by
      rw [hact g (hypFlag h 2 0 1), hfix]
    have h1set : (hypPi h g : MulAut (HypV (K := K))) •
        (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) =
        (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) := by
      rw [← Subgroup.coe_pointwise_smul]
      exact congrArg (fun S : Subgroup (HypV (K := K)) => (S : Set (HypV (K := K)))) h1
    rw [show ((hypEH h).toMonoidHom g : ↥(hypH h)) •
        (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) =
        (hypPi h g : MulAut (HypV (K := K))) •
          (subMul (hypFlag h 2 0 1) : Set (HypV (K := K))) from smul_set_hypH_eq h g _]
    exact h1set


theorem overgroups_hypBorel_model {A : Subgroup (hypSU h 2 0)}
    (hBA : hypBorel h 2 0 ≤ A) :
    A = hypBorel h 2 0 ∨ A = parP h ∨ A = parP2 h ∨ A = ⊤ := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  set I := UnitaryHigher.overgroupCuts 0 h c hc A with hIdef
  have hI : I ⊆ Set.Icc 1 2 := UnitaryHigher.overgroupCuts_subset h hc A
  have hA : A = UnitaryHigher.flagStabilizer h 2 0 I := by
    simpa only [I] using
      (UnitaryHigher.eq_flagStabilizer_overgroupCuts h (r := 2) (ε := 0) (by norm_num)
        (by norm_num) hc hc0 A hBA)
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · left
    have hI12 : I = Set.Icc 1 2 := by
      refine Set.Subset.antisymm hI ?_
      rintro i ⟨hi1, hi2⟩
      rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
      · exact h1
      · have : i = 2 := by omega
        subst this
        exact h2
    rw [hA, hI12]
    rfl
  · right; left
    have hI1 : I = ({1} : Set ℕ) := by
      refine Set.Subset.antisymm ?_ ?_
      · intro i hi
        obtain ⟨hi1, hi2⟩ := hI hi
        rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
        · simp
        · have : i = 2 := by omega
          subst this
          exact absurd hi h2
      · intro i hi
        rw [Set.mem_singleton_iff] at hi
        subst hi
        exact h1
    rw [hA, hI1]
    simp [UnitaryHigher.flagStabilizer, parP]
  · right; right; left
    have hI2 : I = ({2} : Set ℕ) := by
      refine Set.Subset.antisymm ?_ ?_
      · intro i hi
        obtain ⟨hi1, hi2⟩ := hI hi
        rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
        · exact absurd hi h1
        · have : i = 2 := by omega
          subst this
          rfl
      · intro i hi
        rw [Set.mem_singleton_iff] at hi
        subst hi
        exact h2
    rw [hA, hI2]
    simp [UnitaryHigher.flagStabilizer, parP2]
  · right; right; right
    have hI0 : I = ∅ := by
      ext i
      rw [Set.mem_empty_iff_false]
      constructor
      · intro hi
        obtain ⟨hi1, hi2⟩ := hI hi
        rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
        · exact h1 hi
        · have : i = 2 := by omega
          subst this
          exact h2 hi
      · intro h
        exact absurd h (by simp)
    rw [hA, hI0, UnitaryHigher.flagStabilizer_empty]


theorem normalizer_hypUH : Subgroup.normalizer (hypUH h : Set ↥(hypH h)) = hypBH h := by
  have hmap := Subgroup.map_equiv_normalizer_eq (hypUnitriangular h 2 0) (hypEH h)
  rw [UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)] at hmap
  exact hmap.symm

theorem overgroups_BH {A : Subgroup ↥(hypH h)} (hBA : hypBH h ≤ A) :
    A = hypBH h ∨ A = hypPH h ∨ A = hypP2H h ∨ A = ⊤ := by
  let A0 : Subgroup ↥(hypSU h 2 0) := A.map (hypEH h).symm.toMonoidHom
  have hBA0 : hypBorel h 2 0 ≤ A0 := by
    have h1 : (hypBorel h 2 0).map (hypEH h).toMonoidHom ≤ A := hBA
    have h2 := Subgroup.map_mono (f := (hypEH h).symm.toMonoidHom) h1
    have hmap : ((hypBorel h 2 0).map (hypEH h).toMonoidHom).map
        (hypEH h).symm.toMonoidHom = hypBorel h 2 0 := by
      rw [Subgroup.map_map]
      simp
    rwa [hmap] at h2
  have hAeq : A = A0.map (hypEH h).toMonoidHom := by
    dsimp [A0]
    rw [Subgroup.map_map]
    simp
  rcases overgroups_hypBorel_model h hBA0 with hB | hP | hP2 | hTop
  · left
    rw [hAeq, hB]
  · right; left
    rw [hAeq, hP]
  · right; right; left
    rw [hAeq, hP2]
  · right; right; right
    rw [hAeq, hTop, Subgroup.map_top_of_surjective _ (hypEH h).surjective]

theorem overgroups_BH_conj {s : ↥(hypH h)} {A : Subgroup ↥(hypH h)}
    (hBA : (hypBH h).map (MulAut.conj s).toMonoidHom ≤ A) :
    A = (hypBH h).map (MulAut.conj s).toMonoidHom ∨
    A = (hypPH h).map (MulAut.conj s).toMonoidHom ∨
    A = (hypP2H h).map (MulAut.conj s).toMonoidHom ∨ A = ⊤ := by
  let A' : Subgroup ↥(hypH h) := A.map (MulAut.conj s⁻¹).toMonoidHom
  have hBA' : hypBH h ≤ A' := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj s⁻¹).toMonoidHom) hBA
    have hcomp : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [Subgroup.map_map, hcomp, Subgroup.map_id] at h1
  have hAeq : A = A'.map (MulAut.conj s).toMonoidHom :=
    (CFSG.QuasithinUnique.map_equiv_map_equiv_symm (MulAut.conj s) A).symm
  rcases overgroups_BH h hBA' with hB | hP | hP2 | hTop
  · left
    rw [hAeq, hB]
  · right; left
    rw [hAeq, hP]
  · right; right; left
    rw [hAeq, hP2]
  · right; right; right
    rw [hAeq, hTop, Subgroup.map_top_of_surjective _ (MulAut.conj s).surjective]


theorem hypPi_eq_subtype_comp :
    hypPi h = (hypH h).subtype.comp (hypEH h).toMonoidHom := by
  ext x
  rfl

theorem subtype_comp_conj (s : ↥(hypH h)) :
    (hypH h).subtype.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom.comp (hypH h).subtype := by
  ext x
  rfl

theorem hypB_eq_BH_map : hypB h = (hypBH h).map (hypH h).subtype := by
  rw [hypB, hypBH, Subgroup.map_map, hypPi_eq_subtype_comp]

theorem hypP_eq_PH_map : hypP h = (hypPH h).map (hypH h).subtype := by
  rw [hypP, hypPH, Subgroup.map_map, hypPi_eq_subtype_comp]

theorem hypP2_eq_P2H_map : hypP2 h = (hypP2H h).map (hypH h).subtype := by
  rw [hypP2, hypP2H, Subgroup.map_map, hypPi_eq_subtype_comp]

theorem hypBH_map_conj_subtype {s : ↥(hypH h)} :
    ((hypBH h).map (MulAut.conj s).toMonoidHom).map (hypH h).subtype =
      (hypB h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom := by
  rw [hypB_eq_BH_map, hypBH]
  simp only [Subgroup.map_map]
  rw [← MonoidHom.comp_assoc, subtype_comp_conj, MonoidHom.comp_assoc]

theorem hypPH_map_conj_subtype {s : ↥(hypH h)} :
    ((hypPH h).map (MulAut.conj s).toMonoidHom).map (hypH h).subtype =
      (hypP h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom := by
  rw [hypP_eq_PH_map, hypPH]
  simp only [Subgroup.map_map]
  rw [← MonoidHom.comp_assoc, subtype_comp_conj, MonoidHom.comp_assoc]

theorem hypP2H_map_conj_subtype {s : ↥(hypH h)} :
    ((hypP2H h).map (MulAut.conj s).toMonoidHom).map (hypH h).subtype =
      (hypP2 h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom := by
  rw [hypP2_eq_P2H_map, hypP2H]
  simp only [Subgroup.map_map]
  rw [← MonoidHom.comp_assoc, subtype_comp_conj, MonoidHom.comp_assoc]

theorem overgroups_hypB_conj_ambient {s : ↥(hypH h)} {A : Subgroup (MulAut (HypV (K := K)))}
    (hBA : (hypB h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom ≤ A)
    (hAH : A ≤ hypH h) :
    A = (hypB h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom ∨
    A = (hypP h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom ∨
    A = (hypP2 h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom ∨
    A = hypH h := by
  let AH : Subgroup ↥(hypH h) := A.subgroupOf (hypH h)
  have hAHmap : AH.map (hypH h).subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
  have hBAH : (hypBH h).map (MulAut.conj s).toMonoidHom ≤ AH := by
    have h2 : ((hypBH h).map (MulAut.conj s).toMonoidHom).map (hypH h).subtype ≤ A := by
      rw [hypBH_map_conj_subtype]
      exact hBA
    rw [← hAHmap] at h2
    exact (Subgroup.map_le_map_iff_of_injective (hypH h).subtype_injective).mp h2
  rcases overgroups_BH_conj h hBAH with hB | hP | hP2 | hTop
  · left
    rw [← hAHmap, hB, hypBH_map_conj_subtype]
  · right; left
    rw [← hAHmap, hP, hypPH_map_conj_subtype]
  · right; right; left
    rw [← hAHmap, hP2, hypP2H_map_conj_subtype]
  · right; right; right
    rw [← hAHmap, hTop, Subgroup.map_top, Subgroup.range_subtype]


theorem su4HypLine_holds (K : Type) [Field K] [Finite K] (a : ℕ)
    (h : UnitaryFieldData 2 a K) (hK : Nat.card K = (2 ^ a) ^ 2) :
    SU4Line (CFSG.Quasithin.H.StdMod (HypIndex 2 0) K)
      ((CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0).map CFSG.Quasithin.H.matHom) (2 * a) := by
  change SU4Line (HypV (K := K)) (hypH h) (2 * a)
  unfold SU4Line
  intro S
  intro ℓ Pℓ
  letI : MulDistribMulAction ↥S (HypV (K := K)) :=
    MulDistribMulAction.compHom _ (S : Subgroup ↥(hypH h)).subtype
  intro Tstar hTnorm hT2 hST
  intro Good
  intro hline
  intro Pstar hmin
  obtain ⟨a', hna, hSUn, hNat⟩ := hline
  have ha' : a' = a := by omega
  subst a'
  have hS_syl : IsSylowTwoOf (S : Subgroup ↥(hypH h)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hUH_syl : IsSylowTwoOf (hypUH h) ⊤ := by
    have hmap := isSylowTwoOf_map (isSylowTwoOf_hypUnitriangular h) (hypEH h).toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ (hypEH h).surjective] at hmap
  obtain ⟨s, -, hS_eq⟩ := IsSylowTwoOf.exists_conj hUH_syl hS_syl
  let B : Subgroup ↥(hypH h) := Subgroup.normalizer (S : Set ↥(hypH h))
  have hB_eq : B = (hypBH h).map (MulAut.conj s).toMonoidHom := by
    calc
      B = Subgroup.normalizer (S : Set ↥(hypH h)) := rfl
      _ = Subgroup.normalizer
            ((hypUH h).map (MulAut.conj s).toMonoidHom : Set ↥(hypH h)) := by
            rw [show (S : Set ↥(hypH h)) =
                ((hypUH h).map (MulAut.conj s).toMonoidHom : Set ↥(hypH h)) from
              congrArg (fun K : Subgroup ↥(hypH h) => (K : Set ↥(hypH h))) hS_eq]
      _ = (Subgroup.normalizer (hypUH h)).map (MulAut.conj s).toMonoidHom :=
            (Subgroup.map_equiv_normalizer_eq (hypUH h) (MulAut.conj s)).symm
      _ = (hypBH h).map (MulAut.conj s).toMonoidHom := by rw [normalizer_hypUH]
  have hℓ_fix : ℓ = fixV ((S : Subgroup ↥(hypH h)).map (hypH h).subtype) := by
    dsimp [ℓ]
    rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
  have hypU_eq_UH_map : hypU h = (hypUH h).map (hypH h).subtype := by
    rw [hypU, hypUH, Subgroup.map_map, hypPi_eq_subtype_comp]
  have hℓ_sub : ℓ = (subMul (hypFlag h 2 0 1)).map
      (s : MulAut (HypV (K := K))).toMonoidHom := by
    rw [hℓ_fix, hS_eq, Subgroup.map_map, subtype_comp_conj, Subgroup.map_map,
      MonoidHom.comp_assoc, ← hypPi_eq_subtype_comp, ← Subgroup.map_map]
    change fixV ((hypU h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom) =
      (subMul (hypFlag h 2 0 1)).map (s : MulAut (HypV (K := K))).toMonoidHom
    rw [fixV_map_conj, fixV_hypU]
  have hPℓ_eq : Pℓ = (hypPH h).map (MulAut.conj s).toMonoidHom := by
    dsimp [Pℓ]
    rw [hℓ_sub, stabilizer_map_conj_subgroup (hypH h) s (subMul (hypFlag h 2 0 1))]
    rw [stabilizer_subMul_hypFlag]
    rfl
  let SH : Subgroup (MulAut (HypV (K := K))) := (S : Subgroup ↥(hypH h)).map (hypH h).subtype
  have hSH_syl : IsSylowTwoOf SH (hypH h) := by
    have hmap := isSylowTwoOf_map hS_syl (hypH h).subtype
    rwa [Subgroup.map_top, Subgroup.range_subtype] at hmap
  have hTstarH : Tstar ⊓ hypH h = SH := by
    have hX2 : IsPGroup 2 ↥(Tstar ⊓ hypH h) := by
      intro x
      obtain ⟨k, hk⟩ := hT2 ⟨(x : MulAut (HypV (K := K))), x.2.1⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    exact hSH_syl.eq_of_le (le_inf hST (Subgroup.map_subtype_le _)) inf_le_right hX2
  have hSH_map_conj (t : MulAut (HypV (K := K))) (ht : t ∈ Tstar) :
      SH.map (MulAut.conj t).toMonoidHom = SH := by
    have hle : SH.map (MulAut.conj t).toMonoidHom ≤ SH := by
      rintro x ⟨y, hy, rfl⟩
      have hyT : y ∈ Tstar := (hTstarH ▸ hy).1
      have hyH : y ∈ hypH h := (hTstarH ▸ hy).2
      have htT : t * y * t⁻¹ ∈ Tstar :=
        Tstar.mul_mem (Tstar.mul_mem ht hyT) (Tstar.inv_mem ht)
      have htH : t * y * t⁻¹ ∈ hypH h :=
        (Subgroup.mem_normalizer_iff.mp (hTnorm ht) y).mp hyH
      have : t * y * t⁻¹ ∈ Tstar ⊓ hypH h := ⟨htT, htH⟩
      rwa [hTstarH] at this
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective])
  have hℓ_map (t : MulAut (HypV (K := K))) (ht : t ∈ Tstar) :
      ℓ.map t.toMonoidHom = ℓ := by
    rw [hℓ_fix]
    have hfix := fixV_map_conj SH t
    rw [hSH_map_conj t ht] at hfix
    exact hfix.symm
  have hPℓ_t (t : MulAut (HypV (K := K))) (ht : t ∈ Tstar) :
      (Pℓ.map (hypH h).subtype).map (MulAut.conj t).toMonoidHom =
        Pℓ.map (hypH h).subtype := by
    rw [map_subtype_stabilizer_conj_normalizer t (hTnorm ht) ℓ, hℓ_map t ht]
  have hB_inf : B.map (hypH h).subtype = Subgroup.normalizer SH ⊓ hypH h := by
    have hsub : SH.subgroupOf (hypH h) = (S : Subgroup ↥(hypH h)) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        have hyx' : y = x := Subtype.ext hyx
        rw [← hyx']
        exact hy
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_map_of_mem _ hx
    calc
      B.map (hypH h).subtype
          = ((Subgroup.normalizer SH).subgroupOf (hypH h)).map (hypH h).subtype := by
              rw [Subgroup.subgroupOf_normalizer_eq
                (Subgroup.map_subtype_le (S : Subgroup ↥(hypH h))), hsub]
              rfl
      _ = Subgroup.normalizer SH ⊓ hypH h := Subgroup.subgroupOf_map_subtype _ _
  have hB_t (t : MulAut (HypV (K := K))) (ht : t ∈ Tstar) :
      (B.map (hypH h).subtype).map (MulAut.conj t).toMonoidHom =
        B.map (hypH h).subtype := by
    rw [hB_inf, Subgroup.map_inf _ _ _ (MulAut.conj t).injective,
      Subgroup.map_equiv_normalizer_eq SH (MulAut.conj t), hSH_map_conj t ht]
    have hHt : (hypH h).map (MulAut.conj t).toMonoidHom = hypH h :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht)
    rw [hHt]
  let Q : Subgroup ↥(hypH h) := (hypP2H h).map (MulAut.conj s).toMonoidHom
  have hB_le_Pℓ : B ≤ Pℓ := by
    dsimp [B, Pℓ, ℓ]
    exact CFSG.GroupTheory.le_stabilizer_fixedPointSubgroup_of_le_normalizer
      (S := (S : Subgroup ↥(hypH h)))
      (K := Subgroup.normalizer (S : Set ↥(hypH h))) le_rfl
  have hP2_not_le_P : ¬ parP2 h ≤ parP h := by
    intro hle
    have hlt : parP2 h < parP h :=
      lt_of_le_of_ne hle (Ne.symm (parP_ne_parP2 h))
    have htop : parP h = ⊤ := (isCoatom_parP2 h).lt_iff.mp hlt
    exact (isCoatom_parP h).ne_top htop
  have hBH_lt_P2H : hypBH h < hypP2H h := by
    have hB0_le : hypBorel h 2 0 ≤ parP2 h :=
      UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) (by norm_num)
    have hB0_ne : hypBorel h 2 0 ≠ parP2 h := by
      intro heq
      apply hP2_not_le_P
      rw [← heq]
      exact UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) (by norm_num)
    have hlt0 : hypBorel h 2 0 < parP2 h := lt_of_le_of_ne hB0_le hB0_ne
    exact (Subgroup.map_lt_map_iff_of_injective (hypEH h).injective).mpr hlt0
  have hP2H_ne_top : hypP2H h ≠ ⊤ := by
    intro htop
    apply (isCoatom_parP2 h).ne_top
    have h' : hypP2H h = (⊤ : Subgroup ↥(hypSU h 2 0)).map (hypEH h).toMonoidHom := by
      rw [htop, Subgroup.map_top_of_surjective _ (hypEH h).surjective]
    exact Subgroup.map_injective (f := (hypEH h).toMonoidHom) (hypEH h).injective
      (by simpa [hypP2H] using h')
  have hP2H_not_le_PH : ¬ hypP2H h ≤ hypPH h := by
    intro hle
    apply hP2_not_le_P
    have hle0 : parP2 h ≤ parP h := by
      apply (Subgroup.map_le_map_iff_of_injective (f := (hypEH h).toMonoidHom) (hypEH h).injective).mp
      simpa [hypP2H, hypPH] using hle
    exact hle0
  have hB_lt_Q : B < Q := by
    rw [hB_eq, show Q = (hypP2H h).map (MulAut.conj s).toMonoidHom from rfl]
    exact (Subgroup.map_lt_map_iff_of_injective (MulAut.conj s).injective).mpr hBH_lt_P2H
  have hQ_lt_top : Q < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    apply hP2H_ne_top
    have h' : Q = (hypP2H h).map (MulAut.conj s).toMonoidHom := rfl
    rw [h'] at htop
    have h2 : hypP2H h = (⊤ : Subgroup ↥(hypH h)).map (MulAut.conj s⁻¹).toMonoidHom := by
      rw [← htop, Subgroup.map_map]
      have hcomp : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
          MonoidHom.id _ := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp, Subgroup.map_id]
    rw [Subgroup.map_top_of_surjective _ (MulAut.conj s⁻¹).surjective] at h2
    exact h2
  have hQ_not_le_Pℓ : ¬ Q ≤ Pℓ := by
    intro hle
    apply hP2H_not_le_PH
    have hcomp : (MulAut.conj s⁻¹).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hQinv : Q.map (MulAut.conj s⁻¹).toMonoidHom = hypP2H h := by
      rw [show Q = (hypP2H h).map (MulAut.conj s).toMonoidHom from rfl, Subgroup.map_map,
        hcomp, Subgroup.map_id]
    have hPℓinv : Pℓ.map (MulAut.conj s⁻¹).toMonoidHom = hypPH h := by
      rw [hPℓ_eq, Subgroup.map_map, hcomp, Subgroup.map_id]
    have h2 : Q.map (MulAut.conj s⁻¹).toMonoidHom ≤
        Pℓ.map (MulAut.conj s⁻¹).toMonoidHom := Subgroup.map_mono hle
    rwa [hQinv, hPℓinv] at h2
  have hQ_S : (S : Subgroup ↥(hypH h)) ≤ Q := by
    rw [hS_eq, show Q = (hypP2H h).map (MulAut.conj s).toMonoidHom from rfl]
    exact Subgroup.map_mono (by
      rw [hypP2H]
      exact Subgroup.map_mono (hypUnitriangular_le_hypBorel h |>.trans
        (UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) (by norm_num))))
  have hB_le_Q : B ≤ Q := by
    rw [hB_eq, show Q = (hypP2H h).map (MulAut.conj s).toMonoidHom from rfl]
    exact Subgroup.map_mono (by
      rw [hypP2H]
      exact Subgroup.map_mono (UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) (by norm_num)))
  have hQ_Tinv : ∀ t ∈ Tstar,
      (Q.map (hypH h).subtype).map (MulAut.conj t).toMonoidHom =
        Q.map (hypH h).subtype := by
    intro t ht
    let A : Subgroup (MulAut (HypV (K := K))) :=
      (Q.map (hypH h).subtype).map (MulAut.conj t).toMonoidHom
    have hBA : (hypB h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom ≤ A := by
      have hBs : B.map (hypH h).subtype =
          (hypB h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom := by
        rw [hB_eq, hypBH_map_conj_subtype]
      rw [← hBs, ← hB_t t ht]
      exact Subgroup.map_mono (Subgroup.map_mono hB_le_Q)
    have hAH : A ≤ hypH h := by
      dsimp [A]
      calc
        (Q.map (hypH h).subtype).map (MulAut.conj t).toMonoidHom
            ≤ (hypH h).map (MulAut.conj t).toMonoidHom :=
              Subgroup.map_mono (Subgroup.map_subtype_le _)
        _ = hypH h := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht)
    have hQ_amb : Q.map (hypH h).subtype =
        (hypP2 h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom := by
      rw [show Q = (hypP2H h).map (MulAut.conj s).toMonoidHom from rfl,
        hypP2H_map_conj_subtype]
    rcases overgroups_hypB_conj_ambient h hBA hAH with hA | hA | hA | hA
    · exfalso
      have hBs : (hypB h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom =
          B.map (hypH h).subtype := by
        rw [hB_eq, hypBH_map_conj_subtype]
      rw [hBs] at hA
      have hQ_B : Q.map (hypH h).subtype = B.map (hypH h).subtype := by
        have h1 : A = B.map (hypH h).subtype := hA
        dsimp [A] at h1
        rw [← hB_t t ht] at h1
        exact Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom)
          (MulAut.conj t).injective h1
      exact (ne_of_lt hB_lt_Q) (Subgroup.map_injective (f := (hypH h).subtype)
        (hypH h).subtype_injective hQ_B.symm)
    · exfalso
      have hPs : (hypP h).map (MulAut.conj (s : MulAut (HypV (K := K)))).toMonoidHom =
          Pℓ.map (hypH h).subtype := by
        rw [hPℓ_eq, hypPH_map_conj_subtype]
      rw [hPs] at hA
      have hQ_P : Q.map (hypH h).subtype = Pℓ.map (hypH h).subtype := by
        have h1 : A = Pℓ.map (hypH h).subtype := hA
        dsimp [A] at h1
        rw [← hPℓ_t t ht] at h1
        exact Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom)
          (MulAut.conj t).injective h1
      exact hQ_not_le_Pℓ (Subgroup.map_le_map_iff_of_injective
        (hypH h).subtype_injective |>.mp (le_of_eq hQ_P))
    · exact hA.trans hQ_amb.symm
    · exfalso
      have hQ_top : Q.map (hypH h).subtype = hypH h := by
        have h1 : A = hypH h := hA
        dsimp [A] at h1
        have hHt : (hypH h).map (MulAut.conj t).toMonoidHom = hypH h :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht)
        have h2 : (Q.map (hypH h).subtype).map (MulAut.conj t).toMonoidHom =
            (hypH h).map (MulAut.conj t).toMonoidHom := h1.trans hHt.symm
        exact Subgroup.map_injective (f := (MulAut.conj t).toMonoidHom)
          (MulAut.conj t).injective h2
      have hQ_top' : Q = ⊤ := by
        apply Subgroup.map_injective (f := (hypH h).subtype) (hypH h).subtype_injective
        simpa [Subgroup.map_top, Subgroup.range_subtype] using hQ_top
      exact (ne_of_lt hQ_lt_top) hQ_top'
  have hQ_par : IsParabolicTwo ↥(hypH h) Q := ⟨S, hB_le_Q⟩
  have hQgood : Good Q := ⟨hQ_par, hQ_S, hQ_Tinv, hQ_not_le_Pℓ⟩
  obtain ⟨S', hS'_par⟩ := hmin.1.1
  have hS'_syl : IsSylowTwoOf (S' : Subgroup ↥(hypH h)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S'
  have hS'_le : (S' : Subgroup ↥(hypH h)) ≤ Pstar :=
    (Subgroup.le_normalizer.trans hS'_par)
  have hS'_sylP : IsSylowTwoOf (S' : Subgroup ↥(hypH h)) Pstar :=
    isSylowTwoOf_of_le hS'_syl hS'_le
  have hS_sylP : IsSylowTwoOf (S : Subgroup ↥(hypH h)) Pstar :=
    isSylowTwoOf_of_le hS_syl hmin.1.2.1
  obtain ⟨p, hpP, hpconj⟩ := IsSylowTwoOf.exists_conj hS_sylP hS'_sylP
  have hB_le_Pstar : B ≤ Pstar := by
    intro x hx
    have hx' : p * x * p⁻¹ ∈ Pstar := by
      have hmem : p * x * p⁻¹ ∈ Subgroup.normalizer (S' : Set ↥(hypH h)) := by
        have hS' : (S' : Set ↥(hypH h)) =
            ((S : Subgroup ↥(hypH h)).map (MulAut.conj p).toMonoidHom : Set ↥(hypH h)) :=
          congrArg (fun K : Subgroup ↥(hypH h) => (K : Set ↥(hypH h))) hpconj
        rw [hS', ← Subgroup.map_equiv_normalizer_eq (S : Subgroup ↥(hypH h)) (MulAut.conj p)]
        exact Subgroup.mem_map_of_mem _ hx
      exact hS'_par hmem
    have heq : p⁻¹ * (p * x * p⁻¹) * p = x := by group
    rw [← heq]
    exact Pstar.mul_mem (Pstar.mul_mem (Pstar.inv_mem hpP) hx') hpP
  have hPstar_class : Pstar = B ∨ Pstar = Pℓ ∨ Pstar = Q ∨ Pstar = ⊤ := by
    have hclass := overgroups_BH_conj h (s := s) (A := Pstar) (by
      rw [← hB_eq]
      exact hB_le_Pstar)
    simpa only [hB_eq, hPℓ_eq, Q] using hclass
  rcases hPstar_class with hPB | hPP | hPQ | hPTop
  · exfalso
    exact hmin.1.2.2.2 (hPB ▸ hB_le_Pℓ)
  · exfalso
    exact hmin.1.2.2.2 (hPP ▸ le_rfl)
  · refine ⟨?_, ?_⟩
    · rw [hPQ]
      exact ne_of_lt hQ_lt_top
    · left
      rw [hPQ]
      have hstd : IsL2 (Bar2 (Hinf (parP2 h))) (2 * a) := by
        apply CFSG.LocalAnalysis.WeakClosure81.isL2_iff_isPSL.mpr
        have hHinf : Hinf (parP2 h) = perfectCore (parP2 h) := Hinf_eq_perfectCore (parP2 h)
        rw [hHinf]
        exact isPSL_modO2_perfectCore_parP2 h
      have hP2H : IsL2 (Bar2 (Hinf (hypP2H h))) (2 * a) := by
        rw [hypP2H]
        exact isL2_bar2_hinf_map_equiv (hypEH h) (parP2 h) hstd
      simpa [Q] using isL2_bar2_hinf_map_equiv (MulAut.conj s) (hypP2H h) hP2H
  · exfalso
    have htop_le : (⊤ : Subgroup ↥(hypH h)) ≤ Q := by
      rw [← hPTop]
      exact hmin.2 hQgood (by rw [hPTop]; exact le_top)
    exact (ne_of_lt hQ_lt_top) (top_le_iff.mp htop_le)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
