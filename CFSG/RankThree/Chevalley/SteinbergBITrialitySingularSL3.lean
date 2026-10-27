module

public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularRoots
public import CFSG.RankThree.Chevalley.SteinbergBITrialitySingularPerm
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharCentralizer
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.E6 CFSG.RankThree.Classical2 Matrix
open scoped Matrix MatrixGroups

variable {Ω : Type} [Field Ω]

theorem coe_d4A2QvEquiv
    (v : WeylGroup Tag.D4) (y : d4A2Qv Ω v) :
    ((d4A2QvEquiv v y : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
      d4A2Mat ((canonicalRep (coxeterSystem Tag.D4) Ω v)⁻¹ * (y : ModGL Tag.D4 Ω) *
        canonicalRep (coxeterSystem Tag.D4) Ω v) := by
  obtain ⟨_, q, hq, rfl⟩ := y
  have hsymm : (Subgroup.equivMapOfInjective (subsystemGroup Tag.D4 Ω d4SuppA2)
      (MulAut.conj (canonicalRep (coxeterSystem Tag.D4) Ω v)).toMonoidHom
      (MulAut.conj (canonicalRep (coxeterSystem Tag.D4) Ω v)).injective).symm
        ⟨_, q, hq, rfl⟩ = ⟨q, hq⟩ :=
    (MulEquiv.symm_apply_eq _).2 (Subtype.ext rfl)
  have e1 : d4A2QvEquiv v ⟨_, q, hq, rfl⟩ = d4A2Rep Ω ⟨q, hq⟩ := by
    have h2 := congrArg (MulEquiv.ofBijective (d4A2Rep Ω)
      ⟨d4A2Rep_injective, d4A2Rep_surjective⟩) hsymm
    exact h2
  rw [e1, coe_d4A2Rep]
  congr 1
  change q = _ * (canonicalRep (coxeterSystem Tag.D4) Ω v * q *
    (canonicalRep (coxeterSystem Tag.D4) Ω v)⁻¹) * _
  group

theorem chainRootA2_mem_d4A2Sigma {i j : Fin 3} (hij : i ≠ j) :
    chainRoot d4ChainA2 i j ∈ d4A2Sigma := by
  rw [← parabolicRoots_d4SuppA2]
  exact chainRootA2_mem_parabolicRoots hij

theorem pinnedX_mem_d4A2Qv
    (v : WeylGroup Tag.D4) {β : Fin Tag.D4.rank → ℤ}
    (hβ : β ∈ d4A2Sigma) (c : Ω) : pinnedX Tag.D4 Ω (v • β) c ∈ d4A2Qv Ω v := by
  rw [d4A2Qv_eq_rootSpan]
  refine pinnedX_mem_rootSpan ?_ c
  exact ⟨β, hβ, rfl⟩

theorem exists_d4A2QvEquiv_pinnedX
    (v : WeylGroup Tag.D4) {i j : Fin 3} (hij : i ≠ j) :
    ∃ κ : Ω, κ * κ = 1 ∧ ∀ c : Ω,
      ((d4A2QvEquiv v (⟨_, pinnedX_mem_d4A2Qv v (chainRootA2_mem_d4A2Sigma hij) c⟩ :
        d4A2Qv Ω v) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = 1 + single i j (κ * c) := by
  have hβ := isRoot_of_mem_d4A2Sigma (chainRootA2_mem_d4A2Sigma hij)
  obtain ⟨ε, hε, hn⟩ := exists_canonicalRep_mul_pinnedX_mul_inv Ω v hβ
  obtain ⟨ε', hε', hfam⟩ := d4A2RootFamily_all (K := Ω) i j hij
  have hε'2 : ((ε' : ℤ) : Ω) * (ε' : Ω) = 1 := by
    rcases hε' with rfl | rfl <;> norm_num
  refine ⟨(ε' : Ω) * ε, by linear_combination ε * ε * hε'2 + hε, fun c => ?_⟩
  rw [coe_d4A2QvEquiv]
  have e : (canonicalRep (coxeterSystem Tag.D4) Ω v)⁻¹ *
      pinnedX Tag.D4 Ω (v • chainRoot d4ChainA2 i j) c * canonicalRep (coxeterSystem Tag.D4) Ω v =
        pinnedX Tag.D4 Ω (chainRoot d4ChainA2 i j) (ε * c) := by
    have h := hn (ε * c)
    rw [← mul_assoc, hε, one_mul] at h
    rw [← h]
    group
  rw [e, hfam, mul_assoc]

theorem threeSixW_mul_add
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    tsW ε * tsW ε + ε • tsW ε + 1 = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpart⟩ := triality_three_six_unimodular_A2_root_partition
  have h := (hpart ε hε).2.1
  have hW : tsW ε = ε • trialityA := threeSixW_eq_smul hε
  rw [hW, ← sq]
  exact h

theorem threeSixW_mul_mul
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    tsW ε * tsW ε * tsW ε = ε • 1 := by
  have h := threeSixW_mul_add hε
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h2 : tsW ε * tsW ε = -(ε • tsW ε) - 1 := by
    rw [← sub_eq_zero, sub_eq_add_neg, neg_sub, ← h]
    abel
  rw [h2, sub_mul, neg_mul, smul_mul_assoc, h2, one_mul, smul_sub, smul_neg, smul_smul, hε2,
    one_smul]
  abel

theorem neg_mem_image_d4A2Sigma (v : WeylGroup Tag.D4) {α : Fin Tag.D4.rank → ℤ}
    (hα : α ∈ (fun β => v • β) '' d4A2Sigma) : -α ∈ (fun β => v • β) '' d4A2Sigma := by
  obtain ⟨β, hβ, rfl⟩ := hα
  refine ⟨-β, ?_, smul_neg v β⟩
  rw [mem_d4A2Sigma_iff] at hβ ⊢
  exact neg_mem_d4Sigma0List β hβ

theorem image_threeSixW_eq
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) :
    (fun α => tsW ε *ᵥ α) '' ((fun β => v • β) '' d4A2Sigma) =
      (fun β => v • β) '' d4A2Sigma := by
  refine Set.Subset.antisymm (Set.image_subset_iff.2 hstab) fun α hα => ?_
  have h3 := threeSixW_mul_mul hε
  have hmem : ε • (tsW ε *ᵥ (tsW ε *ᵥ α)) ∈ (fun β => v • β) '' d4A2Sigma := by
    have h2 := hstab _ (hstab α hα)
    rcases hε with rfl | rfl
    · rwa [one_smul]
    · rw [neg_one_smul]
      exact neg_mem_image_d4A2Sigma v h2
  refine ⟨_, hmem, ?_⟩
  change tsW ε *ᵥ (ε • (tsW ε *ᵥ (tsW ε *ᵥ α))) = α
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul]
  rcases hε with rfl | rfl <;> norm_num

theorem map_threeSixFrob_d4A2Qv
    (Fr : Ω →+* Ω) (hFr : Function.Surjective Fr) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) :
    (d4A2Qv Ω v).map (tsFrob Ω Fr ε) = d4A2Qv Ω v := by
  have h := map_tsFrob_rootSpan Fr hFr ε
    (S := ((fun β => v • β) '' d4A2Sigma : Set (Fin Tag.D4.rank → ℤ)))
    fun α hα => isRoot_of_mem_image_d4A2Sigma hα
  rw [image_threeSixW_eq hε v hstab] at h
  rw [d4A2Qv_eq_rootSpan]
  exact h

variable (Ω) in
@[expose] def threeSixQvFrob
    (Fr : Ω →+* Ω) (hFr : Function.Surjective Fr) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) : d4A2Qv Ω v ≃* d4A2Qv Ω v :=
  MulEquiv.ofBijective (((tsFrob Ω Fr ε).comp (d4A2Qv Ω v).subtype).codRestrict
    (d4A2Qv Ω v) fun x => (map_threeSixFrob_d4A2Qv Fr hFr hε v hstab).le ⟨(x : ModGL Tag.D4 Ω),
      x.2, rfl⟩)
    ⟨fun x y h => Subtype.ext (tsFrob_injective Fr ε (congrArg Subtype.val h)), fun y => by
      obtain ⟨x, hx, hxy⟩ := (map_threeSixFrob_d4A2Qv Fr hFr hε v hstab).ge y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem coe_threeSixQvFrob
    (Fr : Ω →+* Ω) (hFr : Function.Surjective Fr) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) (y : d4A2Qv Ω v) :
    ((threeSixQvFrob Ω Fr hFr hε v hstab y : d4A2Qv Ω v) : ModGL Tag.D4 Ω) =
      tsFrob Ω Fr ε (y : ModGL Tag.D4 Ω) :=
  rfl

variable (Ω) in
@[expose] def threeSixPhi
    (Fr : Ω →+* Ω) (hFr : Function.Surjective Fr) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) : SL(3, Ω) ≃* SL(3, Ω) :=
  (d4A2QvEquiv v).symm.trans ((threeSixQvFrob Ω Fr hFr hε v hstab).trans (d4A2QvEquiv v))

theorem mem_fixSubgroup_threeSixPhi
    (Fr : Ω →+* Ω) (hFr : Function.Surjective Fr) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma) (X : SL(3, Ω)) :
    X ∈ fixSubgroup (threeSixPhi Ω Fr hFr hε v hstab) ↔
      tsFrob Ω Fr ε ((d4A2QvEquiv v).symm X : ModGL Tag.D4 Ω) =
        ((d4A2QvEquiv v).symm X : ModGL Tag.D4 Ω) := by
  rw [mem_fixSubgroup, threeSixPhi, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← MulEquiv.eq_symm_apply, ← coe_threeSixQvFrob Fr hFr hε v hstab, Subtype.ext_iff]

theorem exists_threeSixPhi_transvection
    (Fr : Ω →+* Ω) (hFr : Function.Surjective Fr) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.D4)
    (hstab : ∀ α ∈ (fun β => v • β) '' d4A2Sigma,
      tsW ε *ᵥ α ∈ (fun β => v • β) '' d4A2Sigma)
    (p q : Fin 3 → Fin 3 → Fin 3) (hpq : ∀ i j : Fin 3, i ≠ j → p i j ≠ q i j)
    (hWv : ∀ i j : Fin 3, i ≠ j →
      tsW ε *ᵥ (v • chainRoot d4ChainA2 i j) = v • chainRoot d4ChainA2 (p i j) (q i j)) :
    ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      ((threeSixPhi Ω Fr hFr hε v hstab (SpecialLinearGroup.transvection hij t) : SL(3, Ω)) :
        Matrix (Fin 3) (Fin 3) Ω) = 1 + single (p i j) (q i j) ((b i j : Ω) * Fr t) := by
  classical
  choose κ hκ hΨ using fun (i j : Fin 3) (hij : i ≠ j) =>
    exists_d4A2QvEquiv_pinnedX (Ω := Ω) v hij
  choose η hη hF using fun (i j : Fin 3) (hij : i ≠ j) =>
    tsFrob_pinnedX (Ω := Ω) Fr ε
      (IsRoot.smul (isRoot_of_mem_d4A2Sigma (chainRootA2_mem_d4A2Sigma hij)) v)
  have hbsq : ∀ (i j : Fin 3) (hij : i ≠ j),
      (κ (p i j) (q i j) (hpq i j hij) * η i j hij * Fr (κ i j hij)) *
        (κ (p i j) (q i j) (hpq i j hij) * η i j hij * Fr (κ i j hij)) = 1 := by
    intro i j hij
    have h1 : Fr (κ i j hij) * Fr (κ i j hij) = 1 := by rw [← map_mul, hκ, map_one]
    linear_combination (η i j hij * η i j hij * (Fr (κ i j hij) * Fr (κ i j hij))) *
      hκ (p i j) (q i j) (hpq i j hij) + (Fr (κ i j hij) * Fr (κ i j hij)) * hη i j hij + h1
  refine ⟨fun i j => if hij : i ≠ j then Units.mkOfMulEqOne _ _ (hbsq i j hij) else 1,
    fun i j hij t => ?_⟩
  set y : d4A2Qv Ω v := ⟨_, pinnedX_mem_d4A2Qv v (chainRootA2_mem_d4A2Sigma hij)
    (κ i j hij * t)⟩ with hy
  have hΨy : d4A2QvEquiv v y = SpecialLinearGroup.transvection hij t := by
    refine Subtype.ext ?_
    rw [hy, hΨ i j hij, CFSG.LinearGroups.coe_transvection, ← mul_assoc, hκ, one_mul]
  have hsymm : (d4A2QvEquiv v).symm (SpecialLinearGroup.transvection hij t) = y :=
    (MulEquiv.symm_apply_eq _).2 hΨy.symm
  have hFy : threeSixQvFrob Ω Fr hFr hε v hstab y =
      ⟨_, pinnedX_mem_d4A2Qv v (chainRootA2_mem_d4A2Sigma (hpq i j hij))
        (η i j hij * Fr (κ i j hij * t))⟩ := by
    refine Subtype.ext ?_
    rw [coe_threeSixQvFrob, hy]
    change tsFrob Ω Fr ε (pinnedX Tag.D4 Ω (v • chainRoot d4ChainA2 i j) (κ i j hij * t)) = _
    rw [hF i j hij, hWv i j hij]
  rw [threeSixPhi, MulEquiv.trans_apply, MulEquiv.trans_apply, hsymm, hFy,
    hΨ (p i j) (q i j) (hpq i j hij)]
  beta_reduce
  rw [dite_eq_left hij, Units.val_mkOfMulEqOne, map_mul]
  congr 2
  ring

end CFSG.RankThree.Chevalley
