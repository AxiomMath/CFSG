module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylBRealize
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
import all CFSG.LieType.Universal.SymplecticRoots
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Weyl
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CoxeterSystem
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.ClassicalInvolution.Models.SymplecticPairs TauCeti.GLSymplecticFin CFSG.Assembly.LowTwoRank

section Shift

variable {n : ℕ}

@[expose] def spShift : RootSubgroupIndex n → RootSubgroupIndex (n + 1)
  | .positiveLong i => .positiveLong i.succ
  | .negativeLong i => .negativeLong i.succ
  | .difference i j h => .difference i.succ j.succ ((Fin.succ_injective _).ne h)
  | .positiveSum i j h => .positiveSum i.succ j.succ (Fin.succ_lt_succ_iff.mpr h)
  | .negativeSum i j h => .negativeSum i.succ j.succ (Fin.succ_lt_succ_iff.mpr h)

theorem cons_zero_single (i : Fin n) (x : ℤ) :
    (Fin.cons 0 (Pi.single i x) : Fin (n + 1) → ℤ) = Pi.single i.succ x := by
  funext a
  refine Fin.cases ?_ (fun a => ?_) a
  · simp [(Fin.succ_ne_zero i).symm]
  · simp [Pi.single_apply, Fin.succ_inj]

theorem stdVec_spShift (r : RootSubgroupIndex n) :
    stdVec (spShift r) = Fin.cons 0 (stdVec r) := by
  have hadd : ∀ u v : Fin n → ℤ,
      (Fin.cons 0 (u + v) : Fin (n + 1) → ℤ) = Fin.cons 0 u + Fin.cons 0 v := by
    intro u v
    funext a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  have hneg : ∀ u : Fin n → ℤ, (Fin.cons 0 (-u) : Fin (n + 1) → ℤ) = -Fin.cons 0 u := by
    intro u
    funext a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  have hsmul : ∀ u : Fin n → ℤ, (Fin.cons 0 (2 • u) : Fin (n + 1) → ℤ) = 2 • Fin.cons 0 u := by
    intro u
    funext a
    refine Fin.cases ?_ (fun a => ?_) a <;> simp
  cases r with
  | positiveLong i => simp only [spShift, stdVec, hsmul, cons_zero_single]
  | negativeLong i => simp only [spShift, stdVec, hneg, hsmul, cons_zero_single]
  | difference i j h =>
    simp only [spShift, stdVec, sub_eq_add_neg, hadd, ← Pi.single_neg, cons_zero_single]
  | positiveSum i j h => simp only [spShift, stdVec, hadd, cons_zero_single]
  | negativeSum i j h => simp only [spShift, stdVec, hneg, hadd, cons_zero_single]

theorem toStd_cons (γ : Fin n → ℤ) :
    toStd (n + 1) (Fin.cons 0 γ) = Fin.cons 0 (toStd n γ) := by
  funext a
  refine Fin.cases ?_ (fun a => ?_) a
  · simp [toStd]
  · rw [Fin.cons_succ, toStd_apply_eq, toStd_apply_eq, Fin.cons_succ]
    simp only [Fin.val_succ, Nat.add_sub_cancel, Nat.succ_pos, dite_true]
    have e2 : (if a.val + 1 + 1 = n + 1 then (2 : ℤ) else 1) = if a.val + 1 = n then 2 else 1 := by
      simp only [Nat.add_right_cancel_iff]
    rw [e2]
    congr 1
    by_cases ha : 0 < a.val
    · rw [dite_eq_left ha]
      have e : (⟨a.val, by omega⟩ : Fin (n + 1)) = Fin.succ ⟨a.val - 1, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Fin.cons_succ]
    · rw [dite_eq_right ha]
      have e : (⟨a.val, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (by simp; omega)
      rw [e, Fin.cons_zero]

theorem exists_spShift_of_stdVec_zero {r' : RootSubgroupIndex (n + 1)} (h : stdVec r' 0 = 0) :
    ∃ r : RootSubgroupIndex n, spShift r = r' := by
  have hsucc : ∀ i : Fin (n + 1), i ≠ 0 → ∃ i' : Fin n, i'.succ = i := fun i hi =>
    Fin.exists_succ_eq.mpr hi
  cases r' with
  | positiveLong i =>
    have hi : i ≠ 0 := fun e => by subst e; simp [stdVec] at h
    obtain ⟨i', rfl⟩ := hsucc i hi
    exact ⟨.positiveLong i', rfl⟩
  | negativeLong i =>
    have hi : i ≠ 0 := fun e => by subst e; simp [stdVec] at h
    obtain ⟨i', rfl⟩ := hsucc i hi
    exact ⟨.negativeLong i', rfl⟩
  | difference i j hij =>
    have hi : i ≠ 0 := fun e => by
      subst e
      simp [stdVec, Ne.symm hij] at h
    have hj : j ≠ 0 := fun e => by
      subst e
      simp [stdVec, hij] at h
    obtain ⟨i', rfl⟩ := hsucc i hi
    obtain ⟨j', rfl⟩ := hsucc j hj
    exact ⟨.difference i' j' (fun e => hij (by rw [e])), rfl⟩
  | positiveSum i j hij =>
    have hj : j ≠ 0 := fun e => by subst e; exact absurd hij (Fin.not_lt_zero i)
    have hi : i ≠ 0 := fun e => by
      subst e
      simp [stdVec, Ne.symm hj] at h
    obtain ⟨i', rfl⟩ := hsucc i hi
    obtain ⟨j', rfl⟩ := hsucc j hj
    exact ⟨.positiveSum i' j' (Fin.succ_lt_succ_iff.mp hij), rfl⟩
  | negativeSum i j hij =>
    have hj : j ≠ 0 := fun e => by subst e; exact absurd hij (Fin.not_lt_zero i)
    have hi : i ≠ 0 := fun e => by
      subst e
      simp [stdVec, Ne.symm hj] at h
    obtain ⟨i', rfl⟩ := hsucc i hi
    obtain ⟨j', rfl⟩ := hsucc j hj
    exact ⟨.negativeSum i' j' (Fin.succ_lt_succ_iff.mp hij), rfl⟩

theorem cons_mem_roots {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    (Fin.cons 0 γ : Fin (n + 1) → ℤ) ∈ roots (isFiniteType_cartanC (n + 1)) ∅ := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  exact mem_roots_of_stdVec (r := spShift r) (by rw [stdVec_spShift, hr, toStd_cons])

theorem exists_cons_of_root {γ' : Fin (n + 1) → ℤ}
    (hγ' : γ' ∈ roots (isFiniteType_cartanC (n + 1)) ∅) (h0 : γ' 0 = 0) :
    ∃ γ ∈ roots (isFiniteType_cartanC n) ∅, γ' = Fin.cons 0 γ := by
  have e : γ' = Fin.cons 0 (Fin.tail γ') := by
    rw [← h0]
    exact (Fin.cons_self_tail γ').symm
  obtain ⟨r', hr'⟩ := exists_stdVec_of_mem_roots hγ'
  rw [e, toStd_cons] at hr'
  obtain ⟨r, rfl⟩ := exists_spShift_of_stdVec_zero (by rw [hr', Fin.cons_zero])
  rw [stdVec_spShift] at hr'
  exact ⟨Fin.tail γ', mem_roots_of_stdVec (Fin.cons_right_injective _ hr'), e⟩

end Shift

section Block

variable (n : ℕ) (F : Type) [Field F]

@[expose] noncomputable def spLeviBlock : StatedSp n F →* StatedSp (n + 1) F :=
  spEmbed Fin.succ (Fin.succ_injective n)

variable {n F}

theorem spLeviBlock_injective : Function.Injective (spLeviBlock n F) :=
  spEmbed_injective (Fin.succ_injective n)

theorem spIncl_E (r : RootSubgroupIndex n) :
    spIncl (K := F) (Fin.succ : Fin n → Fin (n + 1)) * E F r *
      (spIncl (K := F) (Fin.succ : Fin n → Fin (n + 1))).transpose = E F (spShift r) := by
  cases r <;> simp only [E, spShift, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, spIncl_mul_single_mul_transpose, Sum.map_inl, Sum.map_inr]

theorem spLeviBlock_elt (r : RootSubgroupIndex n) (c : F) :
    spLeviBlock n F (elt r c) = elt (spShift r) c := by
  refine mat_injective ?_
  rw [spLeviBlock, mat_spEmbed, mat_elt, mat_elt, spEmbedMat, add_sub_cancel_left, Matrix.mul_smul,
    Matrix.smul_mul, spIncl_E]

theorem rootGroup_cons {γ : Fin n → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) :
    rootGroup (n + 1) F (Fin.cons 0 γ) = (rootGroup n F γ).map (spLeviBlock n F) := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  have hr' : stdVec (spShift r) = toStd (n + 1) (Fin.cons 0 γ) := by
    rw [stdVec_spShift, hr, toStd_cons]
  ext x
  rw [mem_rootGroup_iff hr', Subgroup.mem_map]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨elt r c, (mem_rootGroup_iff hr).mpr ⟨c, rfl⟩, spLeviBlock_elt r c⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).mp hy
    exact ⟨c, spLeviBlock_elt r c⟩

theorem mem_ggSupp_spLeviJ_iff {γ' : Fin (n + 1) → ℤ} :
    γ' ∈ ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n) ↔
      γ' ∈ roots (isFiniteType_cartanC (n + 1)) ∅ ∧ γ' 0 = 0 := by
  change (γ' ∈ roots (isFiniteType_cartanC (n + 1)) ∅ ∧
    ∀ i : Fin (n + 1), i ∉ spLeviJ n → γ' i = 0) ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 0 (by simp [mem_spLeviJ])⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi => ?_⟩
    have : i = 0 := Fin.ext (by have := mt mem_spLeviJ.mpr hi; simp only [Fin.val_zero]; omega)
    rw [this, h2]

theorem range_spBlock : (spLeviBlock n F).range = ggSub (Symplectic.rootDatum (n + 1) F)
    (ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← (Symplectic.isCTGroupDatum n F).iSup_eq_top, Subgroup.map_iSup]
    refine iSup_le fun γ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hγ => ?_
    rw [← rootGroup_cons hγ]
    exact rootGroup_le_ggSub (D := Symplectic.rootDatum (n + 1) F)
      (mem_ggSupp_spLeviJ_iff.mpr ⟨cons_mem_roots hγ, by simp⟩)
  · refine iSup₂_le fun γ' hγ' => ?_
    obtain ⟨h1, h2⟩ := mem_ggSupp_spLeviJ_iff.mp hγ'
    obtain ⟨γ, hγ, rfl⟩ := exists_cons_of_root h1 h2
    change rootGroup (n + 1) F (Fin.cons 0 γ) ≤ _
    rw [rootGroup_cons hγ, MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top

theorem spLeviBlock_mem (g : StatedSp n F) :
    spLeviBlock n F g ∈ ggSub (Symplectic.rootDatum (n + 1) F)
      (ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) := by
  rw [← range_spBlock]
  exact ⟨g, rfl⟩

theorem exists_spBlock_eq {u : StatedSp (n + 1) F}
    (hu : u ∈ ggSub (Symplectic.rootDatum (n + 1) F)
      (ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n))) :
    ∃ g, spLeviBlock n F g = u := by
  rw [← range_spBlock] at hu
  exact hu

theorem weylRep_eq_elt_of_lt {m : ℕ} {k : Fin m} (h : k.val + 1 < m) :
    weylRep m F k = elt (.difference k ⟨k.val + 1, h⟩ (ne_succ' h)) 1 *
      elt (.difference ⟨k.val + 1, h⟩ k (ne_succ' h).symm) (-1) *
        elt (.difference k ⟨k.val + 1, h⟩ (ne_succ' h)) 1 := by
  rw [weylRep_eq, weylElt_of_lt m F h]
  simp only [elt, RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd,
    ← map_mul]
  rfl

theorem weylRep_eq_elt_of_not_lt {m : ℕ} {k : Fin m} (h : ¬ k.val + 1 < m) :
    weylRep m F k = elt (.positiveLong k) 1 * elt (.negativeLong k) (-1) *
      elt (.positiveLong k) 1 := by
  rw [weylRep_eq, weylElt_of_not_lt m F h]
  simp only [elt, RootSubgroupIndex.hom_positiveLong, RootSubgroupIndex.hom_negativeLong,
    positiveLongRootTransvectionHom_apply, negativeLongRootTransvectionHom_apply, toAdd_ofAdd,
    ← map_mul]
  rfl

theorem spLeviBlock_weylRep (k : Fin n) :
    spLeviBlock n F (weylRep n F k) = weylRep (n + 1) F k.succ := by
  by_cases h : k.val + 1 < n
  · have h' : k.succ.val + 1 < n + 1 := by simp; omega
    have e : (⟨k.val + 1, h⟩ : Fin n).succ = ⟨k.succ.val + 1, h'⟩ := Fin.ext (by simp)
    rw [weylRep_eq_elt_of_lt h, weylRep_eq_elt_of_lt h', map_mul, map_mul, spLeviBlock_elt,
      spLeviBlock_elt]
    simp only [spShift, e]
  · have h' : ¬ k.succ.val + 1 < n + 1 := by simp; omega
    rw [weylRep_eq_elt_of_not_lt h, weylRep_eq_elt_of_not_lt h', map_mul, map_mul, spLeviBlock_elt,
      spLeviBlock_elt]
    rfl

end Block

section Hom

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

@[expose] noncomputable def spLeviHom (φ₁ : StatedSp n F →* X) :
    ggSub (Symplectic.rootDatum (n + 1) F)
      (ggSupp (Symplectic.rootDatum (n + 1) F) (spLeviJ n)) →* X :=
  φ₁.comp ((MonoidHom.ofInjective (spLeviBlock_injective (n := n) (F := F))).symm.toMonoidHom.comp
    (MulEquiv.subgroupCongr (range_spBlock (n := n) (F := F))).symm.toMonoidHom)

theorem spLeviHom_apply (φ₁ : StatedSp n F →* X) (g : StatedSp n F) :
    spLeviHom φ₁ ⟨spLeviBlock n F g, spLeviBlock_mem g⟩ = φ₁ g := by
  have h1 : (MulEquiv.subgroupCongr (range_spBlock (n := n) (F := F))).symm
      ⟨spLeviBlock n F g, spLeviBlock_mem g⟩ = MonoidHom.ofInjective spLeviBlock_injective g :=
    Subtype.ext (by rw [MonoidHom.ofInjective_apply]; rfl)
  change φ₁ ((MonoidHom.ofInjective (spLeviBlock_injective (n := n) (F := F))).symm
    ((MulEquiv.subgroupCongr (range_spBlock (n := n) (F := F))).symm
      ⟨spLeviBlock n F g, spLeviBlock_mem g⟩)) = φ₁ g
  rw [h1, MulEquiv.symm_apply_apply]

theorem ggExt_spLeviHom (φ₁ : StatedSp n F →* X) (g : StatedSp n F) :
    ggExt (spLeviHom φ₁) (spLeviBlock n F g) = φ₁ g := by
  rw [ggExt_of_mem _ (spLeviBlock_mem g), spLeviHom_apply]

theorem range_spLeviHom (φ₁ : StatedSp n F →* X) : (spLeviHom φ₁).range = φ₁.range := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨g, hg⟩ := exists_spBlock_eq u.2
    have e : u = ⟨spLeviBlock n F g, spLeviBlock_mem g⟩ := Subtype.ext hg.symm
    rw [e, spLeviHom_apply]
    exact ⟨g, rfl⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, spLeviHom_apply φ₁ g⟩

end Hom

end CFSG.StandardType
