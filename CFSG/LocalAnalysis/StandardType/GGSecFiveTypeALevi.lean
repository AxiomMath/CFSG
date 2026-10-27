module

public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneLevi

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal CFSG.LieType.RootSystem SpecialLinear

variable (n : ℕ) (F : Type) [Field F]

@[expose] noncomputable def slBlockMat (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) F :=
  Matrix.reindexAlgEquiv F F finSumFinEquiv
    (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) F))

variable {n F}

theorem slBlockMat_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (p q) :
    slBlockMat n F A (finSumFinEquiv p) (finSumFinEquiv q) =
      Matrix.fromBlocks A 0 0 (1 : Matrix (Fin 1) (Fin 1) F) p q := by
  simp [slBlockMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem slBlockMat_mul (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    slBlockMat n F (A * B) = slBlockMat n F A * slBlockMat n F B := by
  rw [slBlockMat, slBlockMat, slBlockMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem slBlockMat_one : slBlockMat n F (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) = 1 := by
  rw [slBlockMat, Matrix.fromBlocks_one, map_one]

theorem det_slBlockMat (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    (slBlockMat n F A).det = A.det := by
  rw [slBlockMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    mul_one]

theorem slBlockMat_injective : Function.Injective (slBlockMat n F) := fun A B h => by
  have h' := (Matrix.reindexAlgEquiv F F (finSumFinEquiv (m := n + 1) (n := 1))).injective h
  exact (Matrix.fromBlocks_inj.1 h').1

variable (n F) in
@[expose] noncomputable def slBlockHom :
    Matrix.SpecialLinearGroup (Fin (n + 1)) F →* Matrix.SpecialLinearGroup (Fin (n + 1 + 1)) F where
  toFun A := ⟨slBlockMat n F (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F),
    by rw [det_slBlockMat]; exact A.2⟩
  map_one' := Subtype.ext (by
    change slBlockMat n F ((1 : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, slBlockMat_one])
  map_mul' A B := Subtype.ext (by
    change slBlockMat n F ((A * B : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      slBlockMat n F (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
        slBlockMat n F (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, slBlockMat_mul])

theorem coe_slBlockHom (A : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    ((slBlockHom n F A : Matrix.SpecialLinearGroup (Fin (n + 1 + 1)) F) :
      Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) F) =
      slBlockMat n F (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := rfl

theorem slBlockHom_injective : Function.Injective (slBlockHom n F) := fun _ _ h =>
  Subtype.ext (slBlockMat_injective (congrArg Subtype.val h))

theorem castSucc_eq_finSumFinEquiv (a : Fin (n + 1)) :
    (a.castSucc : Fin (n + 1 + 1)) = finSumFinEquiv (Sum.inl a) := rfl

theorem last_eq_finSumFinEquiv :
    (Fin.last (n + 1) : Fin (n + 1 + 1)) = finSumFinEquiv (Sum.inr (0 : Fin 1)) := by
  rw [finSumFinEquiv_apply_right]
  exact Fin.ext (by simp)

theorem castAdd_one_eq (p : Fin (n + 1)) : (Fin.castAdd 1 p : Fin (n + 1 + 1)) = p.castSucc := rfl

theorem natAdd_zero_eq_last :
    (Fin.natAdd (n + 1) (0 : Fin 1) : Fin (n + 1 + 1)) = Fin.last (n + 1) :=
  Fin.ext (by simp)

theorem slBlockHom_transvection {i j : Fin (n + 1)} (hij : i ≠ j) (c : F) :
    slBlockHom n F (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection ((Fin.castSucc_injective _).ne hij) c := by
  apply Subtype.ext
  rw [coe_slBlockHom]
  ext a b
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective b
  rw [slBlockMat_apply]
  rcases p with p | p <;> rcases q with q | q
  · simp [SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
      castAdd_one_eq]
  · obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [SpecialLinearGroup.transvection_coe, castAdd_one_eq, natAdd_zero_eq_last,
      Fin.castSucc_ne_last]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    simp [SpecialLinearGroup.transvection_coe, castAdd_one_eq, natAdd_zero_eq_last,
      (Fin.castSucc_ne_last _).symm]
  · obtain rfl : p = 0 := Subsingleton.elim _ _
    obtain rfl : q = 0 := Subsingleton.elim _ _
    simp [SpecialLinearGroup.transvection_coe, natAdd_zero_eq_last]

theorem transvection_mem_rootGroup {m : ℕ} {i j : Fin (m + 1)} (hij : i ≠ j) {γ : Fin m → ℤ}
    (hγ : toStd m γ = Pi.single i 1 - Pi.single j 1) (c : F) :
    SpecialLinearGroup.transvection hij c ∈ rootGroup m F γ := by
  rw [rootGroup_eq m F hij hγ]
  exact transvection_mem_rootSubgroup hij c

theorem transvection_mem_rootGroup_single {m : ℕ} (k : Fin m) (hne : k.castSucc ≠ k.succ)
    (c : F) : SpecialLinearGroup.transvection hne c ∈ (rootDatum m F).rootGroup (Pi.single k 1) :=
  transvection_mem_rootGroup hne (toStd_single m k) c

theorem transvection_mem_rootGroup_neg_single {m : ℕ} (k : Fin m) (hne : k.succ ≠ k.castSucc)
    (c : F) :
    SpecialLinearGroup.transvection hne c ∈ (rootDatum m F).rootGroup (-Pi.single k 1) := by
  have h : toStd m (-Pi.single k 1) = Pi.single k.succ 1 - Pi.single k.castSucc 1 := by
    rw [toStd_neg, toStd_single, neg_sub]
  exact transvection_mem_rootGroup hne h c

omit [Field F] in
theorem transvection_eq_of_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    {i j i' j' : ι} (h : i ≠ j) (h' : i' ≠ j') (hi : i = i') (hj : j = j') (c : R) :
    SpecialLinearGroup.transvection h c = SpecialLinearGroup.transvection h' c := by
  subst hi
  subst hj
  rfl

theorem slBlockHom_weylRep (j : Fin n) :
    slBlockHom n F (weylRep n F j) = weylRep (n + 1) F j.castSucc := by
  simp only [weylRep, map_mul, slBlockHom_transvection]

theorem range_slBlockHom : (slBlockHom n F).range =
    ggSub (rootDatum (n + 1) F) (ggSupp (rootDatum (n + 1) F) (typeALeviJ (n + 1) (n + 1))) := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← iSup_fundamentalRootSubgroup_eq_top (m := n) (F := F),
      Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    have hk : (k.castSucc : Fin (n + 1)) ∈ typeALeviJ (n + 1) (n + 1) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
    have e : (k.castSucc : Fin (n + 1)).succ = k.succ.castSucc := Fin.succ_castSucc k
    have hne : (k.castSucc : Fin (n + 1)).castSucc ≠ (k.castSucc : Fin (n + 1)).succ :=
      Fin.castSucc_lt_succ.ne
    rintro _ ⟨z, hz, rfl⟩
    cases s
    · obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ z).mp hz
      rw [slBlockHom_transvection]
      refine rootGroup_le_ggSub (neg_single_mem_ggSupp hk) ?_
      rw [transvection_eq_of_eq _ hne.symm e.symm rfl c]
      exact transvection_mem_rootGroup_neg_single (k.castSucc : Fin (n + 1)) hne.symm c
    · obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ z).mp hz
      rw [slBlockHom_transvection]
      refine rootGroup_le_ggSub (single_mem_ggSupp hk) ?_
      rw [transvection_eq_of_eq _ hne rfl e.symm c]
      exact transvection_mem_rootGroup_single (k.castSucc : Fin (n + 1)) hne c
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b, hab, ha, hb, hγab⟩ := typeALevi_root_of_mem (n + 1) F hγ
    change rootGroup (n + 1) F γ ≤ _
    rw [rootGroup_eq (n + 1) F hab hγab]
    intro z hz
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup hab z).mp hz
    let a' : Fin (n + 1) := ⟨a.val, ha⟩
    let b' : Fin (n + 1) := ⟨b.val, hb⟩
    have ea : a'.castSucc = a := Fin.ext rfl
    have eb : b'.castSucc = b := Fin.ext rfl
    have hab' : a' ≠ b' := fun h => hab (by rw [← ea, ← eb, h])
    refine ⟨SpecialLinearGroup.transvection hab' c, ?_⟩
    rw [slBlockHom_transvection]

theorem slBlockHom_mem (g : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    slBlockHom n F g ∈
      ggSub (rootDatum (n + 1) F) (ggSupp (rootDatum (n + 1) F) (typeALeviJ (n + 1) (n + 1))) := by
  rw [← range_slBlockHom]
  exact ⟨g, rfl⟩


theorem exists_slBlockHom_eq {u : Matrix.SpecialLinearGroup (Fin (n + 1 + 1)) F}
    (hu : u ∈
      ggSub (rootDatum (n + 1) F) (ggSupp (rootDatum (n + 1) F) (typeALeviJ (n + 1) (n + 1)))) :
    ∃ g, slBlockHom n F g = u := by
  rw [← range_slBlockHom] at hu
  exact hu

section Hom

variable {X : Type*} [Group X]

@[expose] noncomputable def typeALeviHom (φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X) :
    ggSub (rootDatum (n + 1) F) (ggSupp (rootDatum (n + 1) F) (typeALeviJ (n + 1) (n + 1))) →* X :=
  φ₁.comp ((MonoidHom.ofInjective (slBlockHom_injective (n := n) (F := F))).symm.toMonoidHom.comp
    (MulEquiv.subgroupCongr (range_slBlockHom (n := n) (F := F))).symm.toMonoidHom)

theorem typeALeviHom_apply (φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    typeALeviHom φ₁ ⟨slBlockHom n F g, slBlockHom_mem g⟩ = φ₁ g := by
  have h1 : (MulEquiv.subgroupCongr (range_slBlockHom (n := n) (F := F))).symm
      ⟨slBlockHom n F g, slBlockHom_mem g⟩ = MonoidHom.ofInjective slBlockHom_injective g :=
    Subtype.ext (by rw [MonoidHom.ofInjective_apply]; rfl)
  change φ₁ ((MonoidHom.ofInjective (slBlockHom_injective (n := n) (F := F))).symm
    ((MulEquiv.subgroupCongr (range_slBlockHom (n := n) (F := F))).symm
      ⟨slBlockHom n F g, slBlockHom_mem g⟩)) = φ₁ g
  rw [h1, MulEquiv.symm_apply_apply]

theorem ggExt_typeALeviHom (φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    ggExt (typeALeviHom φ₁) (slBlockHom n F g) = φ₁ g := by
  rw [ggExt_of_mem _ (slBlockHom_mem g), typeALeviHom_apply]

theorem range_typeALeviHom (φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X) :
    (typeALeviHom φ₁).range = φ₁.range := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨g, hg⟩ := exists_slBlockHom_eq u.2
    have e : u = ⟨slBlockHom n F g, slBlockHom_mem g⟩ := Subtype.ext hg.symm
    rw [e, typeALeviHom_apply]
    exact ⟨g, rfl⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, typeALeviHom_apply φ₁ g⟩

end Hom

end CFSG.StandardType
