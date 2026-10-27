module

public import CFSG.Quasithin.Vol2.KGFactL3EvenMat

public section

namespace CFSG.Quasithin.H13.KGL3Even

open Matrix CFSG.Quasithin.H13.Ch4.KGSL3 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

@[expose] def levMat (g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  ((g : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ • blk (g : Matrix (Fin 3) (Fin 3) F)

theorem levP_eq (g : SpecialLinearGroup (Fin 3) F) : levP g = Matrix.mulVecLin (levMat g) := by
  ext c i
  simp [levP, levMat]

theorem entry22_mul {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ planeStab) :
    ((g * h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 =
      (g : Matrix (Fin 3) (Fin 3) F) 2 2 * (h : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  change ((g : Matrix (Fin 3) (Fin 3) F) * h) 2 2 = _
  simp [Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2]

theorem levMat_mul {g h : SpecialLinearGroup (Fin 3) F} (hg : g ∈ planeStab)
    (hh : h ∈ planeStab) : levMat (g * h) = levMat g * levMat h := by
  rw [levMat, levMat, levMat, entry22_mul hg, mul_inv, smul_mul_smul_comm]
  congr 1
  exact blk_mul _ hh.1 hh.2

theorem levMat_one : levMat (1 : SpecialLinearGroup (Fin 3) F) = 1 := by
  rw [levMat]
  change ((1 : Matrix (Fin 3) (Fin 3) F) 2 2)⁻¹ • blk (1 : Matrix (Fin 3) (Fin 3) F) = 1
  rw [blk_one]
  simp

@[expose] noncomputable def rho : ↥(planeStab : Subgroup (SpecialLinearGroup (Fin 3) F)) →*
    GL (Fin 2) F where
  toFun g := ⟨levMat g, levMat (g⁻¹ : ↥planeStab),
    by rw [← levMat_mul g.2 (g⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      levMat_one],
    by rw [← levMat_mul (g⁻¹).2 g.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      levMat_one]⟩
  map_one' := Units.ext levMat_one
  map_mul' g h := Units.ext (levMat_mul g.2 h.2)

theorem coe_rho (g : ↥(planeStab : Subgroup (SpecialLinearGroup (Fin 3) F))) :
    ((rho g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = levMat g :=
  rfl

theorem rho_eq_one_iff (g : ↥(planeStab : Subgroup (SpecialLinearGroup (Fin 3) F))) :
    rho g = 1 ↔ (g : SpecialLinearGroup (Fin 3) F) ∈
      Subgroup.centralizer ((uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :
        Set (SpecialLinearGroup (Fin 3) F)) := by
  constructor
  · intro h
    refine (planeCoord (F := F)).mem_centralizer g.2 fun c => ?_
    change levP (g : SpecialLinearGroup (Fin 3) F) c = c
    rw [levP_eq, Matrix.mulVecLin_apply, ← coe_rho, h]
    simp
  · intro h
    apply Units.ext
    rw [coe_rho, Units.val_one]
    have hc : ∀ c : Fin 2 → F, levMat (g : SpecialLinearGroup (Fin 3) F) *ᵥ c = c := by
      intro c
      have e := conj_uOf g.2 c
      have hcomm := Subgroup.mem_centralizer_iff.mp h (uOf c) (uOf_mem c)
      have e2 : (g : SpecialLinearGroup (Fin 3) F) * uOf c * (g : SpecialLinearGroup (Fin 3) F)⁻¹ =
          uOf c := by rw [← hcomm]; group
      rw [e2] at e
      have := uOf_injective e
      rw [levP_eq, Matrix.mulVecLin_apply] at this
      exact this.symm
    ext i j
    have := congrFun (hc (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simp only [Matrix.col_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]

theorem mSL_mem (M : SL(2, F)) :
    mSL ((M : Matrix (Fin 2) (Fin 2) F) 0 0) ((M : Matrix (Fin 2) (Fin 2) F) 0 1)
      ((M : Matrix (Fin 2) (Fin 2) F) 1 0) ((M : Matrix (Fin 2) (Fin 2) F) 1 1)
      (by rw [← Matrix.det_fin_two]; exact M.2) ∈ planeStab := by
  constructor <;> simp [mSL, mMat]

theorem levMat_mSL (M : SL(2, F)) :
    levMat (mSL ((M : Matrix (Fin 2) (Fin 2) F) 0 0) ((M : Matrix (Fin 2) (Fin 2) F) 0 1)
      ((M : Matrix (Fin 2) (Fin 2) F) 1 0) ((M : Matrix (Fin 2) (Fin 2) F) 1 1)
      (by rw [← Matrix.det_fin_two]; exact M.2)) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, mSL, mMat, blk]

@[expose] noncomputable def slKer : Subgroup (GL (Fin 2) F) :=
  (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker

theorem mem_slKer {g : GL (Fin 2) F} :
    g ∈ (slKer : Subgroup (GL (Fin 2) F)) ↔ (g : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [slKer, MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

theorem center_sl2_eq_bot [CharP F 2] : Subgroup.center SL(2, F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hr1 : r = 1 := by
    have : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linear_combination this - h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

@[expose] noncomputable def slEquiv : SL(2, F) ≃* ↥(slKer : Subgroup (GL (Fin 2) F)) :=
  MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toGL : SL(2, F) →* GL (Fin 2) F).codRestrict slKer
      fun A => mem_slKer.mpr A.2)
    ⟨fun A B h => Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val h), by
      rintro ⟨g, hg⟩
      refine ⟨⟨g, mem_slKer.mp hg⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl⟩

theorem isSimpleGroup_slKer [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup ↥(slKer : Subgroup (GL (Fin 2) F)) := by
  have hZ := center_sl2_eq_bot (F := F)
  let e : PSL(2, F) ≃* SL(2, F) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hS : IsSimpleGroup SL(2, F) :=
    e.isSimpleGroup_congr.mp (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)
  exact (slEquiv (F := F)).isSimpleGroup_congr.mp hS

theorem eq_bot_or_eq_slKer [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {N : Subgroup (GL (Fin 2) F)} (hN : N ≤ slKer)
    (hnorm : (slKer : Subgroup (GL (Fin 2) F)) ≤ Subgroup.normalizer (N : Set (GL (Fin 2) F))) :
    N = ⊥ ∨ N = slKer := by
  have := isSimpleGroup_slKer h4
  have hn : (N.subgroupOf slKer).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf slKer) with h | h
  · left
    rw [← Subgroup.map_subgroupOf_eq_of_le hN, h, Subgroup.map_bot]
  · right
    rw [← Subgroup.map_subgroupOf_eq_of_le hN, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem rho_image_eq [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {K : Subgroup (SpecialLinearGroup (Fin 3) F)} (hKP : K ≤ planeStab)
    (hPK : planeStab ≤ Subgroup.normalizer (K : Set (SpecialLinearGroup (Fin 3) F)))
    (hKZ : K ≤ ⁅K, K⁆ ⊔ scalars 3 F)
    (hKC : ¬ K ≤ Subgroup.centralizer ((uSub : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F))) :
    (K.subgroupOf planeStab).map rho = slKer := by
  set D : ↥(planeStab : Subgroup (SpecialLinearGroup (Fin 3) F)) →* Fˣ :=
    Matrix.GeneralLinearGroup.det.comp rho with hD
  let H : Subgroup (SpecialLinearGroup (Fin 3) F) := D.ker.map planeStab.subtype
  have hcomm : ⁅K, K⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ planeStab := by
      rw [commutatorElement_def]
      exact planeStab.mul_mem (planeStab.mul_mem (planeStab.mul_mem (hKP ha) (hKP hb))
        (planeStab.inv_mem (hKP ha))) (planeStab.inv_mem (hKP hb))
    refine ⟨⟨⁅a, b⁆, hab⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have e : (⟨⁅a, b⁆, hab⟩ : ↥planeStab) = ⁅(⟨a, hKP ha⟩ : ↥planeStab), ⟨b, hKP hb⟩⁆ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hscal : scalars 3 F ≤ H := by
    intro z hz
    have hzP : z ∈ planeStab := by
      obtain ⟨c, -, hc⟩ := hz
      constructor <;> rw [hc] <;> simp
    refine ⟨⟨z, hzP⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    obtain ⟨c, -, hc⟩ := hz
    apply Units.ext
    simp only [hD, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply, coe_rho,
      Units.val_one]
    have hlev : levMat z = 1 := by
      rw [levMat, hc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [blk, Matrix.scalar_apply, Units.ne_zero]
    rw [hlev, Matrix.det_one]
  have hKH : K ≤ H := hKZ.trans (sup_le hcomm hscal)
  have hle : (K.subgroupOf planeStab).map rho ≤ slKer := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨k', hk', hkk⟩ := hKH (Subgroup.mem_subgroupOf.mp hk)
    have : k' = k := Subtype.ext hkk
    subst this
    rw [mem_slKer]
    have := MonoidHom.mem_ker.mp hk'
    have := congrArg Units.val this
    simpa [hD] using this
  have hnorm : (slKer : Subgroup (GL (Fin 2) F)) ≤
      Subgroup.normalizer (((K.subgroupOf planeStab).map rho : Subgroup (GL (Fin 2) F)) :
        Set (GL (Fin 2) F)) := by
    intro M hM
    obtain ⟨A, hA⟩ := (slEquiv (F := F)).surjective ⟨M, hM⟩
    have hMA : M = ((slEquiv (F := F)) A : GL (Fin 2) F) := by rw [hA]
    rw [hMA]
    set m := mSL ((A : Matrix (Fin 2) (Fin 2) F) 0 0) ((A : Matrix (Fin 2) (Fin 2) F) 0 1)
      ((A : Matrix (Fin 2) (Fin 2) F) 1 0) ((A : Matrix (Fin 2) (Fin 2) F) 1 1)
      (by rw [← Matrix.det_fin_two]; exact A.2) with hm
    have hmP : m ∈ planeStab := mSL_mem A
    have hρm : rho ⟨m, hmP⟩ = ((slEquiv (F := F)) A : GL (Fin 2) F) := by
      apply Units.ext
      rw [coe_rho]
      exact levMat_mSL A
    rw [← hρm]
    have hmN : (⟨m, hmP⟩ : ↥planeStab) ∈ Subgroup.normalizer
        ((K.subgroupOf planeStab : Subgroup ↥planeStab) : Set ↥planeStab) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (hPK hmP) y
    exact Subgroup.le_normalizer_map rho ⟨_, hmN, rfl⟩
  rcases eq_bot_or_eq_slKer h4 hle hnorm with h | h
  · exfalso
    apply hKC
    intro k hk
    have hk' : rho ⟨k, hKP hk⟩ = 1 := by
      have : rho ⟨k, hKP hk⟩ ∈ (K.subgroupOf planeStab).map rho :=
        ⟨⟨k, hKP hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    exact (rho_eq_one_iff _).mp hk'
  · exact h

end CFSG.Quasithin.H13.KGL3Even
