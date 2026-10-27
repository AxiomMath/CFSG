module

public import CFSG.Quasithin.Background.C35InspNat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.Quasithin.Background.A3Structure312
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
public import CFSG.Quasithin.Background.C35InspL45C
public import CFSG.Quasithin.Background.F918M7
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.SmithB51LnAut
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

section Generic

variable {A : Type} [Group A]

theorem mem_centralizer_of_comm_mem {K M₀ : Subgroup A} (hM₀K : M₀ ≤ K) (hperf : ⁅M₀, M₀⁆ = M₀)
    {v : A} (h : ∀ m ∈ M₀, v * m * v⁻¹ * m⁻¹ ∈ centerOf K) :
    v ∈ Subgroup.centralizer (M₀ : Set A) := by
  let f : ↥M₀ →* ↥(Subgroup.center ↥K) :=
    { toFun := fun m => ⟨⟨v * m * v⁻¹ * (m : A)⁻¹, (h m m.2).1⟩, mem_centerOf_iff.1 (h m m.2)⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show v * 1 * v⁻¹ * (1 : A)⁻¹ = 1
        group
      map_mul' := fun m m' => by
        apply Subtype.ext
        apply Subtype.ext
        show v * ((m : A) * m') * v⁻¹ * ((m : A) * m')⁻¹ =
          (v * m * v⁻¹ * (m : A)⁻¹) * (v * m' * v⁻¹ * (m' : A)⁻¹)
        have hz : (v * m' * v⁻¹ * (m' : A)⁻¹) * (m : A)⁻¹ =
            (m : A)⁻¹ * (v * m' * v⁻¹ * (m' : A)⁻¹) :=
          (Subgroup.mem_centralizer_iff.1 (h m' m'.2).2 _ (K.inv_mem (hM₀K m.2))).symm
        calc v * ((m : A) * m') * v⁻¹ * ((m : A) * m')⁻¹ =
              v * m * v⁻¹ * ((v * m' * v⁻¹ * (m' : A)⁻¹) * (m : A)⁻¹) := by group
          _ = _ := by
            rw [hz]
            group }
  have htop : commutator ↥M₀ = ⊤ := (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  have hker : (⟨m, hm⟩ : ↥M₀) ∈ f.ker := by
    apply Abelianization.commutator_subset_ker f
    rw [htop]
    exact Subgroup.mem_top _
  have h1 : v * m * v⁻¹ * m⁻¹ = 1 :=
    congrArg (fun z : ↥(Subgroup.center ↥K) => ((z : ↥K) : A)) (MonoidHom.mem_ker.mp hker)
  have h2 : v * m = m * v := by
    calc v * m = (v * m * v⁻¹ * m⁻¹) * (m * v) := by group
      _ = m * v := by rw [h1, one_mul]
  exact h2.symm

theorem eq_zero_of_central {N : Type} [Group N] {F : Type} [Field F]
    (act : N →* SpecialLinearGroup (Fin 2) F) (hact : Function.Surjective act)
    (c : N → (Fin 2 → F))
    (hceq : ∀ n r : N, act r = 1 → c (n * r * n⁻¹) =
      ((act n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ c r)
    {r : N} (hr : act r = 1) (hcent : ∀ n : N, n * r = r * n) : c r = 0 := by
  have hfix : ∀ D : SpecialLinearGroup (Fin 2) F,
      (D : Matrix (Fin 2) (Fin 2) F) *ᵥ c r = c r := by
    intro D
    obtain ⟨n, rfl⟩ := hact D
    rw [← hceq n r hr, hcent n, mul_inv_cancel_right]
  have h1 := hfix (sl2Upper 1)
  have h2 := hfix (sl2Lower 1)
  rw [sl2Upper_mulVec] at h1
  rw [sl2Lower_mulVec] at h2
  have e1 := congrFun h1 0
  have e2 := congrFun h2 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, add_eq_left,
    add_eq_right] at e1 e2
  ext i
  fin_cases i
  · exact e2
  · exact e1

end Generic

section Sp4

variable {F : Type} [Field F]

local notation "⟪" x "⟫" => spMat (x : StatedSp 2 F)

theorem eq_Q2_of_overgroup [Finite F] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k)
    {H : Subgroup (StatedSp 2 F)} (hB : borelSubgroup 2 F ≤ H) (hne : H ≠ ⊤)
    (hns : ¬ Group.IsSolvable ↥H) : ∃ j : Fin 2, H = Q2 F j := by
  obtain ⟨hH, -⟩ := borel_overgroups H hB
  set I := borelCuts F H with hI
  have hIc : ∀ i ∈ I, 1 ≤ i ∧ i ≤ 2 := borelCuts_le H
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I
  · exfalso
    apply hns
    have hle : H ≤ borelSubgroup 2 F := by
      intro g hg
      rw [hH, mem_flagStabilizer] at hg
      rw [mem_borelSubgroup]
      intro i hi1 hi2
      rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
      · exact hg 1 h1
      · exact hg 2 h2
    have := CFSG.QuasithinUnique.Setup.X7a.isSolvable_borelSubgroup (r := 2) hF
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  · have hIeq : I = {1} := by
      ext c
      rw [Set.mem_singleton_iff]
      constructor
      · intro hc
        obtain ⟨hc1, hc2⟩ := hIc c hc
        by_contra hc'
        have h2' : c = 2 := by omega
        exact h2 (h2' ▸ hc)
      · rintro rfl
        exact h1
    refine ⟨0, ?_⟩
    rw [hH, hIeq, Q2_eq]
    rfl
  · have hIeq : I = {2} := by
      ext c
      rw [Set.mem_singleton_iff]
      constructor
      · intro hc
        obtain ⟨hc1, hc2⟩ := hIc c hc
        by_contra hc'
        have h1' : c = 1 := by omega
        exact h1 (h1' ▸ hc)
      · rintro rfl
        exact h2
    refine ⟨1, ?_⟩
    rw [hH, hIeq, Q2_eq]
    rfl
  · exfalso
    apply hne
    have hIeq : I = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      obtain ⟨hc1, hc2⟩ := hIc c hc
      rcases (by omega : c = 1 ∨ c = 2) with rfl | rfl
      · exact h1 hc
      · exact h2 hc
    rw [hH, hIeq]
    exact flagStabilizer_empty

theorem isCoatom_Q2 (j : Fin 2) : IsCoatom (Q2 F j) := by
  have hj := j.isLt
  refine ⟨stabilizer_flag_ne_top (K := F) (r := 2) (d := (j : ℕ) + 1) (by omega) (by omega),
    fun M hM => ?_⟩
  rcases eq_of_stabilizer_flag_le (K := F) (r := 2) (d := (j : ℕ) + 1) (by omega) M hM.le with
    h | h
  · exact absurd h hM.ne'
  · exact h

section Radical

variable [Finite F]

theorem sp0_entries (x : ↥(perfectCore (Q2 F 0))) :
    ⟪x⟫ (Sum.inl 0) (Sum.inl 0) = 1 ∧ ⟪x⟫ (Sum.inl 1) (Sum.inl 0) = 0 ∧
      ⟪x⟫ (Sum.inr 0) (Sum.inl 0) = 0 ∧ ⟪x⟫ (Sum.inr 1) (Sum.inl 0) = 0 ∧
      ⟪x⟫ (Sum.inr 0) (Sum.inl 1) = 0 ∧ ⟪x⟫ (Sum.inr 0) (Sum.inr 0) = 1 ∧
      ⟪x⟫ (Sum.inr 0) (Sum.inr 1) = 0 := by
  have hQ : (x : StatedSp 2 F) ∈ Q2 F 0 := perfectCore_le _ x.2
  have h00 := spMat_inl_zero_eq_one_of_perfectCore x.2
  refine ⟨h00, spMat_col_zero_of_mem_Q2_zero hQ _ (by simp),
    spMat_col_zero_of_mem_Q2_zero hQ _ (by simp), spMat_col_zero_of_mem_Q2_zero hQ _ (by simp),
    spMat_inr_zero_of_mem_Q2_zero hQ (by simp), ?_, spMat_inr_zero_of_mem_Q2_zero hQ (by simp)⟩
  have h := spMat_key_of_mem_Q2_zero hQ (Sum.inr 0)
  rw [h00, one_mul] at h
  rw [h]
  simp

theorem blkN0_eq (x : ↥(perfectCore (Q2 F 0))) :
    ((blkN 0 x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![⟪x⟫ (Sum.inl 1) (Sum.inl 1), ⟪x⟫ (Sum.inl 1) (Sum.inr 1);
        ⟪x⟫ (Sum.inr 1) (Sum.inl 1), ⟪x⟫ (Sum.inr 1) (Sum.inr 1)] := by
  show blkIdx (sigma2 0) (spMat x.1) = _
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2]

theorem sp0_rad (x : ↥(perfectCore (Q2 F 0))) (h : blkN 0 x = 1) :
    ⟪x⟫ (Sum.inl 1) (Sum.inl 1) = 1 ∧ ⟪x⟫ (Sum.inl 1) (Sum.inr 1) = 0 ∧
      ⟪x⟫ (Sum.inr 1) (Sum.inl 1) = 0 ∧ ⟪x⟫ (Sum.inr 1) (Sum.inr 1) = 1 ∧
      ⟪x⟫ (Sum.inl 1) (Sum.inr 0) = ⟪x⟫ (Sum.inl 0) (Sum.inr 1) ∧
      ⟪x⟫ (Sum.inr 1) (Sum.inr 0) = -⟪x⟫ (Sum.inl 0) (Sum.inl 1) := by
  have hb := blkN0_eq x
  rw [h] at hb
  have e00 := congrFun (congrFun hb 0) 0
  have e01 := congrFun (congrFun hb 0) 1
  have e10 := congrFun (congrFun hb 1) 0
  have e11 := congrFun (congrFun hb 1) 1
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply] at e00 e01 e10 e11
  have u00 : ⟪x⟫ (Sum.inl 1) (Sum.inl 1) = 1 := by rw [← e00]; rfl
  have u01 : ⟪x⟫ (Sum.inl 1) (Sum.inr 1) = 0 := by rw [← e01]; rfl
  have u10 : ⟪x⟫ (Sum.inr 1) (Sum.inl 1) = 0 := by rw [← e10]; rfl
  have u11 : ⟪x⟫ (Sum.inr 1) (Sum.inr 1) = 1 := by rw [← e11]; rfl
  obtain ⟨x00, x10, x20, x30, y21, y22, y23⟩ := sp0_entries x
  have hs1 := congrFun₂ (mem_statedSp_iff.mp (x : StatedSp 2 F).2) (Sum.inl 1) (Sum.inr 0)
  have hs2 := congrFun₂ (mem_statedSp_iff.mp (x : StatedSp 2 F).2) (Sum.inr 1) (Sum.inr 0)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.transpose_apply,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply] at hs1 hs2
  simp only [spMat] at u00 u01 u10 u11 x00 x10 x20 x30 y21 y22 y23 ⊢
  simp [u00, u01, u10, u11, y21, y22, y23] at hs1 hs2
  refine ⟨u00, u01, u10, u11, ?_, ?_⟩
  · linear_combination -hs2
  · linear_combination hs1

@[expose] def spc0 (x : ↥(perfectCore (Q2 F 0))) : Fin 2 → F :=
  ![⟪x⟫ (Sum.inl 0) (Sum.inl 1), ⟪x⟫ (Sum.inl 0) (Sum.inr 1)]

omit [Finite F] in
theorem spMat_mul_sub {H : Subgroup (StatedSp 2 F)} (x y : ↥H) : ⟪x * y⟫ = ⟪x⟫ * ⟪y⟫ := rfl

theorem spc0_mul (r s : ↥(perfectCore (Q2 F 0))) (_hr : blkN 0 r = 1) (hs : blkN 0 s = 1) :
    spc0 (r * s) = spc0 r + spc0 s := by
  obtain ⟨r00, -, -, -, -, -, -⟩ := sp0_entries r
  obtain ⟨-, -, s20, -, s21, -, s23⟩ := sp0_entries s
  obtain ⟨s11, s13, s31, s33, -, -⟩ := sp0_rad s hs
  ext i
  fin_cases i
  · show ⟪r * s⟫ (Sum.inl 0) (Sum.inl 1) = ⟪r⟫ (Sum.inl 0) (Sum.inl 1) + ⟪s⟫ (Sum.inl 0) (Sum.inl 1)
    rw [spMat_mul_sub, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two,
      r00, s11, s21, s31]
    ring
  · show ⟪r * s⟫ (Sum.inl 0) (Sum.inr 1) = ⟪r⟫ (Sum.inl 0) (Sum.inr 1) + ⟪s⟫ (Sum.inl 0) (Sum.inr 1)
    rw [spMat_mul_sub, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two,
      r00, s13, s23, s33]
    ring

theorem sp0_conj (n r : ↥(perfectCore (Q2 F 0))) (hr : blkN 0 r = 1) :
    spc0 (n * r * n⁻¹) = (((blkN 0 n)⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ spc0 r := by
  set r' := n * r * n⁻¹ with hr'
  have hr'1 : blkN 0 r' = 1 := by
    rw [hr', map_mul, map_mul, hr, mul_one, map_inv, mul_inv_cancel]
  obtain ⟨-, -, a20, -, a21, -, a23⟩ := sp0_entries r
  obtain ⟨a11, a13, a31, a33, -, -⟩ := sp0_rad r hr
  obtain ⟨b00, -, -, -, -, -, -⟩ := sp0_entries r'
  obtain ⟨n00, -, -, -, n21, -, n23⟩ := sp0_entries n
  have hcomm : ⟪r'⟫ * ⟪n⟫ = ⟪n⟫ * ⟪r⟫ := by
    have h : r' * n = n * r := by
      rw [hr']
      group
    exact congrArg (fun z : ↥(perfectCore (Q2 F 0)) => ⟪z⟫) h
  have e1 := congrFun (congrFun hcomm (Sum.inl 0)) (Sum.inl 1)
  have e2 := congrFun (congrFun hcomm (Sum.inl 0)) (Sum.inr 1)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at e1 e2
  rw [b00, n00, a11, a21, a31, n21] at e1
  rw [b00, n00, a13, a23, a33, n23] at e2
  have key : ((blkN 0 n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *ᵥ
      spc0 r' = spc0 r := by
    rw [blkN0_eq]
    ext i
    fin_cases i
    · simp only [spc0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
      simp
      linear_combination e1
    · simp only [spc0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
      simp
      linear_combination e2
  have hDD : ((((blkN 0 n)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ *
      ((blkN 0 n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ) = 1 := by
    rw [← Matrix.transpose_mul]
    have h : ((blkN 0 n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((blkN 0 n)⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 :=
      congrArg (fun z : SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F))
        (mul_inv_cancel (blkN 0 n))
    rw [h, Matrix.transpose_one]
  rw [← key, Matrix.mulVec_mulVec, hDD, Matrix.one_mulVec]

theorem sp0_central (n r : ↥(perfectCore (Q2 F 0))) (hr : blkN 0 r = 1) (h0 : spc0 r = 0) :
    n * r = r * n := by
  obtain ⟨r00, r10, r20, r30, r21, r22, r23⟩ := sp0_entries r
  obtain ⟨r11, r13, r31, r33, r12, r32⟩ := sp0_rad r hr
  have ha : ⟪r⟫ (Sum.inl 0) (Sum.inl 1) = 0 := congrFun h0 0
  have hb : ⟪r⟫ (Sum.inl 0) (Sum.inr 1) = 0 := congrFun h0 1
  rw [ha, neg_zero] at r32
  rw [hb] at r12
  obtain ⟨n00, n10, n20, n30, n21, n22, n23⟩ := sp0_entries n
  have hrm : ⟪r⟫ = 1 + Matrix.single (Sum.inl 0) (Sum.inr 0) (⟪r⟫ (Sum.inl 0) (Sum.inr 0)) := by
    ext p q
    rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
      simp [r00, r10, r20, r30, r21, r22, r23, r11, r13, r31, r33, r12, r32, ha, hb]
  apply Subtype.ext
  apply statedSp_ext
  show ⟪n⟫ * ⟪r⟫ = ⟪r⟫ * ⟪n⟫
  rw [hrm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext p q
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [n00, n10, n20, n30, n21, n22, n23]

omit [Finite F] in
theorem sp1_blocks {x : StatedSp 2 F} (hx : x ∈ Q2 F 1) :
    spMat x = fromBlocks (spMat x).toBlocks₁₁ (spMat x).toBlocks₁₂ 0 (spMat x).toBlocks₂₂ := by
  have h21 : (spMat x).toBlocks₂₁ = 0 := by
    ext i k
    exact spMat_inr_inl_of_mem_Q2_one hx i k
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (spMat x)]
  rw [h21]

omit [Finite F] in
theorem sp1_rel {x : StatedSp 2 F} (hx : x ∈ Q2 F 1) :
    (spMat x).toBlocks₁₁ᵀ * (spMat x).toBlocks₂₂ = 1 ∧
      (spMat x).toBlocks₁₂ᵀ * (spMat x).toBlocks₂₂ =
        (spMat x).toBlocks₂₂ᵀ * (spMat x).toBlocks₁₂ := by
  have hs := mem_statedSp_iff.mp x.2
  have hb := sp1_blocks hx
  change (spMat x)ᵀ * fromBlocks 0 1 (-1) 0 * spMat x = fromBlocks 0 1 (-1) 0 at hs
  rw [hb, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hs
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.transpose_zero, Matrix.neg_mul, neg_zero] at hs
  obtain ⟨-, h12, -, h22⟩ := Matrix.fromBlocks_inj.mp hs
  refine ⟨h12, ?_⟩
  have := h22
  rw [neg_add_eq_zero] at this
  exact this.symm

theorem sp1_rad (x : ↥(perfectCore (Q2 F 1))) (h : blkN 1 x = 1) :
    ⟪x⟫ = fromBlocks 1 ⟪x⟫.toBlocks₁₂ 0 1 ∧ ⟪x⟫.toBlocks₁₂ᵀ = ⟪x⟫.toBlocks₁₂ := by
  have hQ : (x : StatedSp 2 F) ∈ Q2 F 1 := perfectCore_le _ x.2
  have hA : ⟪x⟫.toBlocks₁₁ = 1 := by
    have h1 : blkIdx (sigma2 1) (spMat x.1) = 1 := congrArg Subtype.val h
    ext i k
    have := congrFun (congrFun h1 i) k
    fin_cases i <;> fin_cases k <;> simpa [blkIdx, sigma2, Matrix.toBlocks₁₁] using this
  obtain ⟨hAC, hBC⟩ := sp1_rel hQ
  rw [hA, Matrix.transpose_one, Matrix.one_mul] at hAC
  rw [hAC, Matrix.mul_one, Matrix.transpose_one, Matrix.one_mul] at hBC
  refine ⟨?_, hBC⟩
  conv_lhs => rw [sp1_blocks hQ]
  rw [hA, hAC]

theorem blkN1_eq (x : ↥(perfectCore (Q2 F 1))) :
    ((blkN 1 x : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ⟪x⟫.toBlocks₁₁ := by
  show blkIdx (sigma2 1) (spMat x.1) = _
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, Matrix.toBlocks₁₁]

theorem sp1_conj_block (n r r' : ↥(perfectCore (Q2 F 1))) (hr' : r' = n * r * n⁻¹)
    (hr : blkN 1 r = 1) :
    blkN 1 r' = 1 ∧ ⟪r'⟫.toBlocks₁₂ = ⟪n⟫.toBlocks₁₁ * ⟪r⟫.toBlocks₁₂ * ⟪n⟫.toBlocks₁₁ᵀ := by
  have hr'1 : blkN 1 r' = 1 := by
    rw [hr', map_mul, map_mul, hr, mul_one, map_inv, mul_inv_cancel]
  refine ⟨hr'1, ?_⟩
  have hQ : (n : StatedSp 2 F) ∈ Q2 F 1 := perfectCore_le _ n.2
  obtain ⟨hAC, -⟩ := sp1_rel hQ
  have hCA : ⟪n⟫.toBlocks₂₂ * ⟪n⟫.toBlocks₁₁ᵀ = 1 := mul_eq_one_comm.mp hAC
  have hcomm : ⟪r'⟫ * ⟪n⟫ = ⟪n⟫ * ⟪r⟫ := by
    have h : r' * n = n * r := by
      rw [hr']
      group
    exact congrArg (fun z : ↥(perfectCore (Q2 F 1)) => ⟪z⟫) h
  rw [(sp1_rad r' hr'1).1, (sp1_rad r hr).1, sp1_blocks hQ, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply] at hcomm
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul] at hcomm
  obtain ⟨-, h12, -, -⟩ := Matrix.fromBlocks_inj.mp hcomm
  have hSC : ⟪r'⟫.toBlocks₁₂ * ⟪n⟫.toBlocks₂₂ = ⟪n⟫.toBlocks₁₁ * ⟪r⟫.toBlocks₁₂ := by
    rw [add_comm] at h12
    exact add_right_cancel h12
  calc ⟪r'⟫.toBlocks₁₂ = ⟪r'⟫.toBlocks₁₂ * (⟪n⟫.toBlocks₂₂ * ⟪n⟫.toBlocks₁₁ᵀ) := by
        rw [hCA, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hSC]

@[expose] noncomputable def frobSL [CharP F 2] :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F :=
  SpecialLinearGroup.map (frobenius F 2)

omit [Finite F] in
theorem frobSL_apply [CharP F 2] (D : SpecialLinearGroup (Fin 2) F) (i k : Fin 2) :
    ((frobSL D : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i k =
      (D : Matrix (Fin 2) (Fin 2) F) i k ^ 2 := by
  simp [frobSL, frobenius_def]

theorem frobSL_bijective [CharP F 2] : Function.Bijective (frobSL (F := F)) := by
  have hinj : Function.Injective (frobSL (F := F)) := by
    intro D D' h
    ext i k
    have := congrArg (fun z : SpecialLinearGroup (Fin 2) F =>
      (z : Matrix (Fin 2) (Fin 2) F) i k) h
    simp only [frobSL_apply] at this
    exact CharTwo.sq_injective this
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

@[expose] def spc1 (x : ↥(perfectCore (Q2 F 1))) : Fin 2 → F :=
  ![⟪x⟫ (Sum.inl 0) (Sum.inr 0), ⟪x⟫ (Sum.inl 1) (Sum.inr 1)]

theorem spc1_mul (r s : ↥(perfectCore (Q2 F 1))) (hr : blkN 1 r = 1) (hs : blkN 1 s = 1) :
    spc1 (r * s) = spc1 r + spc1 s := by
  have hrs : ⟪r * s⟫ = ⟪r⟫ * ⟪s⟫ := rfl
  have h := hrs
  rw [(sp1_rad r hr).1, (sp1_rad s hs).1, Matrix.fromBlocks_multiply] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.one_mul] at h
  have e : ∀ i : Fin 2, ⟪r * s⟫ (Sum.inl i) (Sum.inr i) =
      ⟪r⟫ (Sum.inl i) (Sum.inr i) + ⟪s⟫ (Sum.inl i) (Sum.inr i) := by
    intro i
    have := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
    rw [Matrix.fromBlocks_apply₁₂, Matrix.add_apply] at this
    rw [this, add_comm]
    rfl
  ext i
  fin_cases i
  · exact e 0
  · exact e 1

theorem sp1_conj [CharP F 2] (n r : ↥(perfectCore (Q2 F 1))) (hr : blkN 1 r = 1) :
    spc1 (n * r * n⁻¹) = ((frobSL (blkN 1 n) : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ spc1 r := by
  set r' := n * r * n⁻¹ with hr'
  obtain ⟨-, hS⟩ := sp1_conj_block n r r' hr' hr
  have hsym := (sp1_rad r hr).2
  have hsym01 : ⟪r⟫ (Sum.inl 1) (Sum.inr 0) = ⟪r⟫ (Sum.inl 0) (Sum.inr 1) := by
    have := congrFun (congrFun hsym 0) 1
    simpa [Matrix.toBlocks₁₂, Matrix.transpose_apply] using this
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e : ∀ i : Fin 2, ⟪r'⟫ (Sum.inl i) (Sum.inr i) =
      ⟪n⟫ (Sum.inl i) (Sum.inl 0) ^ 2 * ⟪r⟫ (Sum.inl 0) (Sum.inr 0) +
        ⟪n⟫ (Sum.inl i) (Sum.inl 1) ^ 2 * ⟪r⟫ (Sum.inl 1) (Sum.inr 1) := by
    intro i
    have := congrFun (congrFun hS i) i
    simp only [Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two, Matrix.of_apply] at this
    rw [this, hsym01]
    linear_combination (⟪n⟫ (Sum.inl i) (Sum.inl 0) * ⟪n⟫ (Sum.inl i) (Sum.inl 1) *
      ⟪r⟫ (Sum.inl 0) (Sum.inr 1)) * h2
  ext i
  fin_cases i
  · simp only [spc1, Matrix.mulVec, dotProduct, Fin.sum_univ_two, frobSL_apply, blkN1_eq]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.toBlocks₁₁, Matrix.of_apply]
    exact e 0
  · simp only [spc1, Matrix.mulVec, dotProduct, Fin.sum_univ_two, frobSL_apply, blkN1_eq]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.toBlocks₁₁, Matrix.of_apply]
    exact e 1

theorem sp1_central [CharP F 2] (n r : ↥(perfectCore (Q2 F 1))) (hr : blkN 1 r = 1)
    (h0 : spc1 r = 0) : n * r = r * n := by
  set r' := n * r * n⁻¹ with hr'
  obtain ⟨hr'1, hS⟩ := sp1_conj_block n r r' hr' hr
  have hsym := (sp1_rad r hr).2
  have h00 : ⟪r⟫ (Sum.inl 0) (Sum.inr 0) = 0 := congrFun h0 0
  have h11 : ⟪r⟫ (Sum.inl 1) (Sum.inr 1) = 0 := congrFun h0 1
  have hsym01 : ⟪r⟫ (Sum.inl 1) (Sum.inr 0) = ⟪r⟫ (Sum.inl 0) (Sum.inr 1) := by
    have := congrFun (congrFun hsym 0) 1
    simpa [Matrix.toBlocks₁₂, Matrix.transpose_apply] using this
  have hdet := (blkN 1 n).2
  rw [blkN1_eq, Matrix.det_fin_two] at hdet
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hSS : ⟪r'⟫.toBlocks₁₂ = ⟪r⟫.toBlocks₁₂ := by
    rw [hS]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp only [Matrix.toBlocks₁₂, Matrix.toBlocks₁₁, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, Matrix.of_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one] <;>
      rw [hsym01, h00, h11]
    · linear_combination (⟪n⟫ (Sum.inl 0) (Sum.inl 0) * ⟪n⟫ (Sum.inl 0) (Sum.inl 1) *
        ⟪r⟫ (Sum.inl 0) (Sum.inr 1)) * h2
    · linear_combination ⟪r⟫ (Sum.inl 0) (Sum.inr 1) * hdet +
        (⟪n⟫ (Sum.inl 0) (Sum.inl 1) * ⟪n⟫ (Sum.inl 1) (Sum.inl 0) *
          ⟪r⟫ (Sum.inl 0) (Sum.inr 1)) * h2
    · linear_combination ⟪r⟫ (Sum.inl 0) (Sum.inr 1) * hdet +
        (⟪n⟫ (Sum.inl 0) (Sum.inl 1) * ⟪n⟫ (Sum.inl 1) (Sum.inl 0) *
          ⟪r⟫ (Sum.inl 0) (Sum.inr 1)) * h2
    · linear_combination (⟪n⟫ (Sum.inl 1) (Sum.inl 0) * ⟪n⟫ (Sum.inl 1) (Sum.inl 1) *
        ⟪r⟫ (Sum.inl 0) (Sum.inr 1)) * h2
  have hrr : r' = r := by
    apply Subtype.ext
    apply statedSp_ext
    show ⟪r'⟫ = ⟪r⟫
    rw [(sp1_rad r' hr'1).1, (sp1_rad r hr).1, hSS]
  calc n * r = r' * n := by
        rw [hr']
        group
    _ = r * n := by rw [hrr]

end Radical

end Sp4

end CFSG.Quasithin.C35Pf
