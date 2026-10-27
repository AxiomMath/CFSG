module

public import CFSG.Monster.B.Geometry.InitialIsometryTransport
public import CFSG.Monster.B.E6.StdF4Action

public noncomputable section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4

theorem ofThree_adj_equiv {ι ι' F : Type*} (e : ι ≃ ι') {i₁ i₂ i₃ : ι}
    {r₁ r₂ r₃ : F → F → Prop} {h₁ : Equivalence r₁} {h₂ : Equivalence r₂}
    {h₃ : Equivalence r₃} (j : ι') :
    (ChamberSystem.ofThree (e i₁) (e i₂) (e i₃) r₁ r₂ r₃ h₁ h₂ h₃).adj j =
      (ChamberSystem.ofThree i₁ i₂ i₃ r₁ r₂ r₃ h₁ h₂ h₃).adj (e.symm j) := by
  unfold ChamberSystem.ofThree
  dsimp only
  have key : ∀ i : ι, j = e i ↔ e.symm j = i := fun i => (Equiv.symm_apply_eq e).symm
  by_cases e₁ : j = e i₁
  · rw [ite_eq_left e₁, ite_eq_left ((key i₁).mp e₁)]
  · rw [ite_eq_right e₁, ite_eq_right fun h => e₁ ((key i₁).mpr h)]
    by_cases e₂ : j = e i₂
    · rw [ite_eq_left e₂, ite_eq_left ((key i₂).mp e₂)]
    · rw [ite_eq_right e₂, ite_eq_right fun h => e₂ ((key i₂).mpr h)]
      by_cases e₃ : j = e i₃
      · rw [ite_eq_left e₃, ite_eq_left ((key i₃).mp e₃)]
      · rw [ite_eq_right e₃, ite_eq_right fun h => e₃ ((key i₃).mpr h)]

theorem polarChamber_adj_nativeIdx {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (P : PolarSpace K V) (p l π : Fin 4) (j : Fin Tag.F4.rank) :
    (polarChamber P (nativeIdx p) (nativeIdx l) (nativeIdx π)).adj j =
      (polarChamber P p l π).adj (nativeIdx.symm j) :=
  ofThree_adj_equiv nativeIdx j

theorem nativeIdx_three : nativeIdx 3 = (3 : Fin Tag.F4.rank) := rfl
theorem nativeIdx_two : nativeIdx 2 = (2 : Fin Tag.F4.rank) := rfl
theorem nativeIdx_one : nativeIdx 1 = (1 : Fin Tag.F4.rank) := rfl
theorem nativeIdx_zero : nativeIdx 0 = (0 : Fin Tag.F4.rank) := rfl

theorem firstJ_eq_setOf : firstJ = {j : Fin 4 | j ≠ 0} := by
  ext j
  simp only [firstJ, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  rcases fin4_cases j with rfl | rfl | rfl | rfl <;> decide

theorem fourthJ_eq_setOf : FourthResidue.fourthJ = {j : Fin 4 | j ≠ 3} := by
  ext j
  simp only [FourthResidue.fourthJ, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  rcases fin4_cases j with rfl | rfl | rfl | rfl <;> decide

theorem preimage_unitTypes : nativeIdx ⁻¹' unitTypes = firstJ :=
  (Set.ext fun _ => Iff.rfl : nativeIdx ⁻¹' unitTypes = {j : Fin 4 | j ≠ 0}).trans
    firstJ_eq_setOf.symm

theorem preimage_orthTypes : nativeIdx ⁻¹' orthTypes = FourthResidue.fourthJ :=
  (Set.ext fun _ => Iff.rfl : nativeIdx ⁻¹' orthTypes = {j : Fin 4 | j ≠ 3}).trans
    fourthJ_eq_setOf.symm

theorem stdDistanceF4_eq_simple_iff
    (a b : C2E6Std.stdChamber) (j : Fin Tag.F4.rank) :
    stdDistanceF4 a b = (coxeterSystem .F4).simple j ↔
      stdDistance a b = ncs.simple (nativeIdx.symm j) := by
  have h : nativeWeylEquiv (ncs.simple (nativeIdx.symm j)) = (coxeterSystem .F4).simple j :=
    (nativeWeylEquiv_simple _).trans (congrArg _ (nativeIdx.apply_symm_apply j))
  exact ⟨fun e => nativeWeylEquiv.injective (e.trans h.symm),
    fun e => (congrArg nativeWeylEquiv e).trans h⟩

theorem residue_stdDistanceF4'
    (L : Set (Fin Tag.F4.rank)) (x : C2E6Std.stdChamber) :
    residue (coxeterSystem .F4) stdDistanceF4 L x = residue ncs stdDistance (nativeIdx ⁻¹' L) x :=
  residue_stdDistanceF4 L x

theorem std_end_transfer
    {F : Type*} {L : Set (Fin Tag.F4.rank)} {P : ChamberSystem (Fin 4) F}
    {P' : ChamberSystem (Fin Tag.F4.rank) F}
    (hP : ∀ j, P'.adj j = P.adj (nativeIdx.symm j))
    (hbase : ∃ ψ : F → C2E6Std.stdChamber,
      Set.BijOn ψ Set.univ (residue ncs stdDistance (nativeIdx ⁻¹' L) c₀) ∧
      ∀ a b j, stdDistance (ψ a) (ψ b) = ncs.simple j ↔ a ≠ b ∧ P.adj j a b)
    (x : C2E6Std.stdChamber) :
    ∃ f : residue (coxeterSystem .F4) stdDistanceF4 L x → F,
      IsChamberModel (coxeterSystem .F4) (resDist (coxeterSystem .F4) stdDistanceF4 L x) P' f := by
  induction x using QuotientGroup.induction_on with | H g => ?_
  obtain ⟨ψ, hψ, hadj⟩ := hbase
  obtain ⟨hψ', hadj'⟩ := bijOn_comp_of_isometry (MulAction.toPerm g)
    (stdDistance_groupPerm g) hψ hadj
  rw [toPerm_c₀] at hψ'
  refine exists_isChamberModel_of_bijOn (ψ := MulAction.toPerm g ∘ ψ) ?_ fun a b j => ?_
  · rw [residue_stdDistanceF4']
    exact hψ'
  · refine (stdDistanceF4_eq_simple_iff _ _ j).trans ?_
    rw [hadj', hP]

theorem hasClassicalEnds_std :
    HasClassicalEnds stdDistanceF4 where
  unit x := by
    refine std_end_transfer (P := polarChamber UData 3 2 1) (fun j => ?_) ?_ x
    · rw [← polarChamber_adj_nativeIdx, nativeIdx_three, nativeIdx_two, nativeIdx_one]
      rfl
    · rw [preimage_unitTypes]
      exact ⟨_, bijOn_of_isChamberModel isChamberModel_modelU⟩
  orth x := by
    refine std_end_transfer (P := polarChamber OData 0 1 2) (fun j => ?_) ?_ x
    · rw [← polarChamber_adj_nativeIdx, nativeIdx_zero, nativeIdx_one, nativeIdx_two]
      rfl
    · rw [preimage_orthTypes]
      exact ⟨_, bijOn_of_isChamberModel isChamberModel_modelO⟩

theorem encard_panel_one_std
    (x : C2E6Std.stdChamber) :
    (panel (coxeterSystem .F4) stdDistanceF4 1 x).encard ≤ 3 := by
  have h := encard_panel_stdDistanceF4 (1 : Fin Tag.F4.rank) x
  calc (panel (coxeterSystem .F4) stdDistanceF4 1 x).encard
      = if ((1 : Fin Tag.F4.rank) : ℕ) < 2 then 3 else 5 := h
    _ ≤ 3 := by rw [ite_eq_left (by decide)]

end CFSG.Monster.B.TwoA.Amalgam
