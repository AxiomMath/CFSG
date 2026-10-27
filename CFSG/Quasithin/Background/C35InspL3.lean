module

public import CFSG.Quasithin.Background.C35InspNat
public import CFSG.Quasithin.Background.C35InspBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListTits
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsCycle
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.C4Statement
public import CFSG.Quasithin.Background.F918M7
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.SmithB51LnAut
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Walter.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

section SL3

variable {F : Type} [Field F]

local notation "⌜" x "⌝" => ((x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem eq_Q3_of_overgroup [Finite F] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k)
    {H : Subgroup (SpecialLinearGroup (Fin 3) F)} (hB : upperTriangular 3 F ≤ H) (hne : H ≠ ⊤)
    (hns : ¬ Group.IsSolvable ↥H) : ∃ j : Fin 2, H = Q3 F j := by
  obtain ⟨hH, -⟩ := borel_overgroups H hB
  set I := borelOvergroupCuts H with hI
  have hIc : ∀ i ∈ I, 1 ≤ i ∧ i < 3 := fun i hi => by
    obtain ⟨h1, h2, -⟩ := hi
    exact ⟨h1, h2⟩
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · exfalso
    apply hns
    have hle : H ≤ upperTriangular 3 F := by
      intro g hg
      rw [hH, mem_flagStabilizer] at hg
      have hs1 := hg 1 h1
      have hs2 := hg 2 h2
      rw [mem_upperTriangular]
      intro r c hrc
      fin_cases r <;> fin_cases c
      all_goals first
        | exact absurd hrc (by decide)
        | exact stabilizer_entries hs1 (by decide) (by decide)
        | exact stabilizer_entries hs2 (by decide) (by decide)
    have := isSolvable_upperTriangular (n := 3) hF
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  · have hIeq : I = {1} := by
      ext c
      rw [Set.mem_singleton_iff]
      constructor
      · intro hc
        obtain ⟨hc1, hc3⟩ := hIc c hc
        by_contra hc'
        have h2' : c = 2 := by omega
        exact h2 (h2' ▸ hc)
      · rintro rfl
        exact h1
    refine ⟨0, ?_⟩
    rw [hH, hIeq, Q3_eq]
    rfl
  · have hIeq : I = {2} := by
      ext c
      rw [Set.mem_singleton_iff]
      constructor
      · intro hc
        obtain ⟨hc1, hc3⟩ := hIc c hc
        by_contra hc'
        have h1' : c = 1 := by omega
        exact h1 (h1' ▸ hc)
      · rintro rfl
        exact h2
    refine ⟨1, ?_⟩
    rw [hH, hIeq, Q3_eq]
    rfl
  · exfalso
    apply hne
    have hIeq : I = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      obtain ⟨hc1, hc3⟩ := hIc c hc
      rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
      · exact h1 hc
      · exact h2 hc
    rw [hH, hIeq]
    exact flagStabilizer_empty _ _

section Radical

variable [Finite F]

theorem blk3_zero_apply (x : ↥(perfectCore (Q3 F 0))) (i k : Fin 2) :
    ((blk3 0 x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i k =
      ⌜x⌝ i.succ k.succ := by
  fin_cases i <;> fin_cases k <;> rfl

theorem blk3_one_apply (x : ↥(perfectCore (Q3 F 1))) (i k : Fin 2) :
    ((blk3 1 x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i k =
      ⌜x⌝ i.castSucc k.castSucc := by
  fin_cases i <;> fin_cases k <;> rfl

theorem n0_entries (x : ↥(perfectCore (Q3 F 0))) : ⌜x⌝ 0 0 = 1 ∧ ⌜x⌝ 1 0 = 0 ∧ ⌜x⌝ 2 0 = 0 := by
  have hQ : (x : SpecialLinearGroup (Fin 3) F) ∈ stabilizer (flagSpace 3 F 1) :=
    perfectCore_le _ x.2
  have h10 : ⌜x⌝ 1 0 = 0 := stabilizer_entries (k := 1) (l := 0) hQ (by decide) (by decide)
  have h20 : ⌜x⌝ 2 0 = 0 := stabilizer_entries (k := 2) (l := 0) hQ (by decide) (by decide)
  have hdet := (x : SpecialLinearGroup (Fin 3) F).2
  have hblk := (blk3 0 x).2
  rw [Matrix.det_fin_two, blk3_zero_apply, blk3_zero_apply, blk3_zero_apply,
    blk3_zero_apply] at hblk
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hblk
  rw [Matrix.det_fin_three, h10, h20] at hdet
  refine ⟨?_, h10, h20⟩
  linear_combination hdet - ⌜x⌝ 0 0 * hblk

theorem n1_entries (x : ↥(perfectCore (Q3 F 1))) : ⌜x⌝ 2 2 = 1 ∧ ⌜x⌝ 2 0 = 0 ∧ ⌜x⌝ 2 1 = 0 := by
  have hQ : (x : SpecialLinearGroup (Fin 3) F) ∈ stabilizer (flagSpace 3 F 2) :=
    perfectCore_le _ x.2
  have h20 : ⌜x⌝ 2 0 = 0 := stabilizer_entries (k := 2) (l := 0) hQ (by decide) (by decide)
  have h21 : ⌜x⌝ 2 1 = 0 := stabilizer_entries (k := 2) (l := 1) hQ (by decide) (by decide)
  have hdet := (x : SpecialLinearGroup (Fin 3) F).2
  have hblk := (blk3 1 x).2
  rw [Matrix.det_fin_two, blk3_one_apply, blk3_one_apply, blk3_one_apply,
    blk3_one_apply] at hblk
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at hblk
  rw [Matrix.det_fin_three, h20, h21] at hdet
  refine ⟨?_, h20, h21⟩
  linear_combination hdet - ⌜x⌝ 2 2 * hblk

theorem n0_rad (x : ↥(perfectCore (Q3 F 0))) (h : blk3 0 x = 1) :
    ⌜x⌝ 0 0 = 1 ∧ ⌜x⌝ 1 0 = 0 ∧ ⌜x⌝ 2 0 = 0 ∧ ⌜x⌝ 1 1 = 1 ∧ ⌜x⌝ 1 2 = 0 ∧ ⌜x⌝ 2 1 = 0 ∧
      ⌜x⌝ 2 2 = 1 := by
  obtain ⟨h00, h10, h20⟩ := n0_entries x
  have hb : ∀ i k : Fin 2, ⌜x⌝ i.succ k.succ = (1 : Matrix (Fin 2) (Fin 2) F) i k := by
    intro i k
    rw [← blk3_zero_apply, h]
    rfl
  have e11 := hb 0 0
  have e12 := hb 0 1
  have e21 := hb 1 0
  have e22 := hb 1 1
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e11 e12 e21 e22
  exact ⟨h00, h10, h20, e11, e12, e21, e22⟩

theorem n1_rad (x : ↥(perfectCore (Q3 F 1))) (h : blk3 1 x = 1) :
    ⌜x⌝ 0 0 = 1 ∧ ⌜x⌝ 0 1 = 0 ∧ ⌜x⌝ 1 0 = 0 ∧ ⌜x⌝ 1 1 = 1 ∧ ⌜x⌝ 2 0 = 0 ∧ ⌜x⌝ 2 1 = 0 ∧
      ⌜x⌝ 2 2 = 1 := by
  obtain ⟨h22, h20, h21⟩ := n1_entries x
  have hb : ∀ i k : Fin 2, ⌜x⌝ i.castSucc k.castSucc = (1 : Matrix (Fin 2) (Fin 2) F) i k := by
    intro i k
    rw [← blk3_one_apply, h]
    rfl
  have e00 := hb 0 0
  have e01 := hb 0 1
  have e10 := hb 1 0
  have e11 := hb 1 1
  simp only [Fin.castSucc_zero, Fin.castSucc_one, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11, h20, h21, h22⟩

@[expose] def rad0 (x : ↥(perfectCore (Q3 F 0))) : Fin 2 → F := ![⌜x⌝ 0 1, ⌜x⌝ 0 2]

@[expose] def rad1 (x : ↥(perfectCore (Q3 F 1))) : Fin 2 → F := ![⌜x⌝ 0 2, ⌜x⌝ 1 2]

omit [Finite F] in
theorem coe_mul3 {H : Subgroup (SpecialLinearGroup (Fin 3) F)} (x y : ↥H) :
    ⌜x * y⌝ = ⌜x⌝ * ⌜y⌝ := rfl

theorem rad0_mul (r s : ↥(perfectCore (Q3 F 0))) (hr : blk3 0 r = 1) (hs : blk3 0 s = 1) :
    rad0 (r * s) = rad0 r + rad0 s := by
  obtain ⟨r00, -, -, -, -, -, -⟩ := n0_rad r hr
  obtain ⟨-, -, -, s11, s12, s21, s22⟩ := n0_rad s hs
  ext i
  fin_cases i
  · show ⌜r * s⌝ 0 1 = ⌜r⌝ 0 1 + ⌜s⌝ 0 1
    rw [coe_mul3, Matrix.mul_apply, Fin.sum_univ_three, r00, s11, s21]
    ring
  · show ⌜r * s⌝ 0 2 = ⌜r⌝ 0 2 + ⌜s⌝ 0 2
    rw [coe_mul3, Matrix.mul_apply, Fin.sum_univ_three, r00, s12, s22]
    ring

theorem rad1_mul (r s : ↥(perfectCore (Q3 F 1))) (hr : blk3 1 r = 1) (hs : blk3 1 s = 1) :
    rad1 (r * s) = rad1 r + rad1 s := by
  obtain ⟨r00, r01, r10, r11, -, -, -⟩ := n1_rad r hr
  obtain ⟨-, -, -, -, -, -, s22⟩ := n1_rad s hs
  ext i
  fin_cases i
  · show ⌜r * s⌝ 0 2 = ⌜r⌝ 0 2 + ⌜s⌝ 0 2
    rw [coe_mul3, Matrix.mul_apply, Fin.sum_univ_three, r00, r01, s22]
    ring
  · show ⌜r * s⌝ 1 2 = ⌜r⌝ 1 2 + ⌜s⌝ 1 2
    rw [coe_mul3, Matrix.mul_apply, Fin.sum_univ_three, r10, r11, s22]
    ring

theorem eq_one_of_rad0 (r : ↥(perfectCore (Q3 F 0))) (hr : blk3 0 r = 1) (h0 : rad0 r = 0) :
    r = 1 := by
  obtain ⟨r00, r10, r20, r11, r12, r21, r22⟩ := n0_rad r hr
  have h01 : ⌜r⌝ 0 1 = 0 := congrFun h0 0
  have h02 : ⌜r⌝ 0 2 = 0 := congrFun h0 1
  refine Subtype.ext (Subtype.ext ?_)
  show ⌜r⌝ = 1
  ext i k
  fin_cases i <;> fin_cases k <;> simp [r00, r10, r20, r11, r12, r21, r22, h01, h02]

theorem eq_one_of_rad1 (r : ↥(perfectCore (Q3 F 1))) (hr : blk3 1 r = 1) (h0 : rad1 r = 0) :
    r = 1 := by
  obtain ⟨r00, r01, r10, r11, r20, r21, r22⟩ := n1_rad r hr
  have h02 : ⌜r⌝ 0 2 = 0 := congrFun h0 0
  have h12 : ⌜r⌝ 1 2 = 0 := congrFun h0 1
  refine Subtype.ext (Subtype.ext ?_)
  show ⌜r⌝ = 1
  ext i k
  fin_cases i <;> fin_cases k <;> simp [r00, r01, r10, r11, r20, r21, r22, h02, h12]

theorem rad0_conj (n r : ↥(perfectCore (Q3 F 0))) (hr : blk3 0 r = 1) :
    rad0 (n * r * n⁻¹) = (((blk3 0 n)⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ rad0 r := by
  set r' := n * r * n⁻¹ with hr'
  have hr'1 : blk3 0 r' = 1 := by
    rw [hr', map_mul, map_mul, hr, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨-, -, -, a11, a12, a21, a22⟩ := n0_rad r hr
  obtain ⟨b00, -, -, -, -, -, -⟩ := n0_rad r' hr'1
  obtain ⟨n00, -, -⟩ := n0_entries n
  have hcomm : ⌜r'⌝ * ⌜n⌝ = ⌜n⌝ * ⌜r⌝ := by
    have h : r' * n = n * r := by
      rw [hr']
      group
    exact congrArg (fun z : ↥(perfectCore (Q3 F 0)) => ⌜z⌝) h
  have e1 := congrFun (congrFun hcomm 0) 1
  have e2 := congrFun (congrFun hcomm 0) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e1 e2
  rw [b00, n00, a11, a21] at e1
  rw [b00, n00, a12, a22] at e2
  have key : ((blk3 0 n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ rad0 r' =
      rad0 r := by
    ext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
        blk3_zero_apply, rad0]
      simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination e1
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
        blk3_zero_apply, rad0]
      simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination e2
  have hDD : ((((blk3 0 n)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *
      ((blk3 0 n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ) = 1 := by
    rw [← Matrix.transpose_mul]
    have h : ((blk3 0 n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((blk3 0 n)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 :=
      congrArg (fun z : SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F))
        (mul_inv_cancel (blk3 0 n))
    rw [h, Matrix.transpose_one]
  rw [← key, Matrix.mulVec_mulVec, hDD, Matrix.one_mulVec]

theorem rad1_conj (n r : ↥(perfectCore (Q3 F 1))) (hr : blk3 1 r = 1) :
    rad1 (n * r * n⁻¹) = ((blk3 1 n : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ rad1 r := by
  set r' := n * r * n⁻¹ with hr'
  have hr'1 : blk3 1 r' = 1 := by
    rw [hr', map_mul, map_mul, hr, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨-, -, -, -, a20, a21, a22⟩ := n1_rad r hr
  obtain ⟨b00, b01, b10, b11, -, -, -⟩ := n1_rad r' hr'1
  obtain ⟨n22, -, -⟩ := n1_entries n
  have hcomm : ⌜r'⌝ * ⌜n⌝ = ⌜n⌝ * ⌜r⌝ := by
    have h : r' * n = n * r := by
      rw [hr']
      group
    exact congrArg (fun z : ↥(perfectCore (Q3 F 1)) => ⌜z⌝) h
  have e1 := congrFun (congrFun hcomm 0) 2
  have e2 := congrFun (congrFun hcomm 1) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e1 e2
  rw [b00, b01, n22, a22] at e1
  rw [b10, b11, n22, a22] at e2
  ext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, blk3_one_apply, rad1]
    simp only [Fin.castSucc_zero, Fin.castSucc_one, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination e1
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, blk3_one_apply, rad1]
    simp only [Fin.castSucc_zero, Fin.castSucc_one, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination e2

theorem radical_data [CharP F 2] (hK : ∃ k : ℕ, Nat.card F = 2 ^ k)
    (hK4 : ∃ s : Finset F, s.card = 4) (j : Fin 2) :
    ∃ (act : ↥(perfectCore (Q3 F j)) →* SpecialLinearGroup (Fin 2) F)
      (c : ↥(perfectCore (Q3 F j)) → (Fin 2 → F)),
      Function.Surjective act ∧ IsPGroup 2 act.ker ∧
      (∀ r s, act r = 1 → act s = 1 → c (r * s) = c r + c s) ∧
      (∀ r, act r = 1 → c r = 0 → r = 1) ∧
      (∀ n r, act r = 1 → c (n * r * n⁻¹) =
        ((act n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ c r) := by
  fin_cases j
  · have hact : ∀ r, ((CFSG.Quasithin.JonesParshall.invTransposeSL 2 F).toMonoidHom.comp
        (blk3 0)) r = 1 ↔ blk3 0 r = 1 := fun r => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    refine ⟨(CFSG.Quasithin.JonesParshall.invTransposeSL 2 F).toMonoidHom.comp (blk3 0), rad0,
      (CFSG.Quasithin.JonesParshall.invTransposeSL 2 F).surjective.comp (blk3_surjective hK4 0),
      ?_, fun r s hr hs => rad0_mul r s ((hact r).1 hr) ((hact s).1 hs),
      fun r hr h0 => eq_one_of_rad0 r ((hact r).1 hr) h0, fun n r hr => ?_⟩
    · rintro ⟨r, hr⟩
      obtain ⟨k, hk⟩ := blk3_ker_isPGroup hK 0 ⟨r, (hact r).1 hr⟩
      have h : r ^ 2 ^ k = 1 := (SubgroupClass.coe_pow _ _).symm.trans (congrArg Subtype.val hk)
      exact ⟨k, Subtype.ext ((SubgroupClass.coe_pow _ _).trans h)⟩
    · rw [rad0_conj n r ((hact r).1 hr)]
      rfl
  · exact ⟨blk3 1, rad1, blk3_surjective hK4 1, blk3_ker_isPGroup hK 1, rad1_mul, eq_one_of_rad1,
      fun n r hr => rad1_conj n r hr⟩

end Radical

end SL3

theorem l3_holds_base : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A),
    C35Base K Y M₀ V →
    ∀ f : ℕ, 2 ≤ f → IsPSL 3 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V := by
  intro A _ _ K Y M₀ V hD f hf2 hX
  classical
  have hX' := hX
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hX
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨f, hcard⟩
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  let φ : ↥K →* projectiveSL 3 F := (e.trans (statedSLEquivProjectiveSL 3 F)).toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφker : φ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := (e.trans (statedSLEquivProjectiveSL 3 F)).surjective y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    exact ⟨k, hx⟩
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU : IsSylowTwoOf (projUnitriangular 3 F) ⊤ := hP ▸ isSylowTwoOf_top_of_sylow P
  obtain ⟨g, hNY, hne, hns⟩ := hD.exists_conj_normalizer φ hφker.le hφs hU
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hθ
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hφker]
  have hYK : Y ≤ K := hD.parabolic.1
  have hM₀K : M₀ ≤ K := hD.eq_perfectCore ▸ (perfectCore_le Y).trans hYK
  have hZY : centerOf K ≤ Y := hD.center_le.trans (Subgroup.map_subtype_le _)
  have hB : upperTriangular 3 F ≤ (img θ Y).comap (proj 3 F) := by
    intro b hb
    show proj 3 F b ∈ img θ Y
    apply hNY
    rw [normalizer_projUnitriangular 2]
    exact ⟨b, hb, rfl⟩
  have hmc : ((img θ Y).comap (proj 3 F)).map (proj 3 F) = img θ Y :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 F) _
  have hŶne : (img θ Y).comap (proj 3 F) ≠ ⊤ := by
    intro h
    apply hne
    rw [← hmc, h, Subgroup.map_top_of_surjective _ (proj_surjective 3 F)]
  have hŶns : ¬ Group.IsSolvable ↥((img θ Y).comap (proj 3 F)) := by
    intro hs
    apply hns
    rw [← hmc]
    exact Group.isSolvable_of_surjective ((proj 3 F).subgroupMap_surjective _)
  obtain ⟨j, hj⟩ := eq_Q3_of_overgroup hK hB hŶne hŶns
  have hYj : img θ Y = (Q3 F j).map (proj 3 F) := by
    rw [← hj, hmc]
  have hMj : img θ M₀ = (perfectCore (Q3 F j)).map (proj 3 F) := by
    rw [hD.eq_perfectCore, img_perfectCore θ hYK, hYj, map_perfectCore]
  have hinj : Set.InjOn (proj 3 F)
      (perfectCore (Q3 F j) : Set (SpecialLinearGroup (Fin 3) F)) := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ (proj 3 F).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have h1 := blk3_scalars j ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩ (by rw [← ker_proj]; exact hz)
    exact inv_mul_eq_one.mp (congrArg Subtype.val h1)
  set ν := liftHom hM₀K θ (proj 3 F) (perfectCore (Q3 F j)) hinj hMj with hν
  have hνs := liftHom_surjective hM₀K θ (proj 3 F) (perfectCore (Q3 F j)) hinj hMj
  have hν1 : ∀ x : ↥M₀, ν x = 1 ↔ (x : A) ∈ centerOf K := by
    intro x
    rw [hν, liftHom_eq_one_iff, ← MonoidHom.mem_ker, hθker]
    exact mem_centerOf_iff.symm
  have hνker : IsPGroup 2 ν.ker := by
    rintro ⟨x, hx⟩
    have hxZ : (⟨x, hM₀K x.2⟩ : ↥K) ∈ Subgroup.center ↥K :=
      mem_centerOf_iff.1 ((hν1 x).1 hx)
    obtain ⟨k, hk⟩ := isPGroup_center hD.center ⟨_, hxZ⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(Subgroup.center ↥K) => ((z : ↥K) : A)) hk
    simpa using this
  obtain ⟨act, c, hacts, hactker, hcmul, hc0, hceq⟩ := radical_data hK hK4 j
  have hc1 : c 1 = 0 := by
    have h := hcmul 1 1 (map_one act) (map_one act)
    rw [mul_one] at h
    exact add_eq_left.mp h.symm
  have hMV := le_normalizer_of_comm hD.V_comm
  obtain ⟨hVO, -⟩ := hD.le_pCoreOf
  have hVZ : ¬ V ≤ V ⊓ centerOf K := by
    intro h
    apply hD.V_ne
    rw [← hD.V_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    exact Subgroup.mem_centralizer_iff.1 (h hv).2.2 m (hM₀K hm)
  have hcZ : ∀ (v : A) (hv : v ∈ V), act (ν ⟨v, hD.V_le hv⟩) = 1 →
      (c (ν ⟨v, hD.V_le hv⟩) = 0 ↔ v ∈ V ⊓ centerOf K) := by
    intro v hv h1
    constructor
    · intro h0
      exact ⟨hv, (hν1 _).1 (hc0 _ h1 h0)⟩
    · rintro ⟨-, hvZ⟩
      rw [(hν1 ⟨v, hD.V_le hv⟩).2 hvZ, hc1]
  obtain ⟨hOker, hnat⟩ := natural_of_radical hD.V_le hMV hVZ hVO hK4 ν hνs hνker act hacts
    hactker c hcmul hcZ hceq
  have hker2 : IsPGroup 2 (act.comp ν).ker := by
    rw [hOker]
    exact CFSG.pCore_isPGroup
  have hco : IsCoatom (img θ Y) := by
    rw [hYj]
    exact isCoatom_projStabilizer_flagSpace (K := F) (n := 3) (d := (j : ℕ) + 1) (by omega)
      (by have := j.isLt; omega)
  exact ⟨f, Or.inl hX', isMaxParabolic2_of_coatom θ hθker.le hD.parabolic hD.ne_top hZY hco,
    isPSL2_modO2 hcard hf2 _ (hacts.comp hνs) hker2,
    Or.inl ⟨F, inferInstance, Fintype.ofFinite F, by rw [Fintype.card_eq_nat_card, hcard], hnat⟩⟩

theorem l3_holds : ∀ (A : Type) [Group A] [Finite A] (K Y M₀ V : Subgroup A), C35Data K Y M₀ V →
    ∀ f : ℕ, 2 ≤ f → IsPSL 3 2 f (↥K ⧸ Subgroup.center ↥K) → C35Concl1 K Y M₀ V :=
  fun A _ _ K Y M₀ V hD => l3_holds_base A K Y M₀ V hD.toBase

end CFSG.Quasithin.C35Pf
