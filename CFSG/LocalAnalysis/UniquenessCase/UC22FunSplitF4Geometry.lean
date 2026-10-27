module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitAmbient
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTorus
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LieType.HighestRoot.CentTrialitySL2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3
public import CFSG.LocalAnalysis.StandardType.GGJ4eComm
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZRootTorus
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLieFunFamily

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix Module CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.ModelFacts (stdRankOne)
open CFSG.StandardType.TableBF4Two (orthRoot isRoot_orthRoot)
open scoped MatrixGroups

theorem f4Frame_orthogonal_kernel : ∀ (k : Fin 4) (γ : Fin Tag.F4.rank → ℤ),
    γ ∈ rootFinset .F4 →
    (∀ j : Fin 4, j ≠ k → iform (orthRoot j) γ = 0) →
      γ = orthRoot k ∨ γ = -orthRoot k := by
  decide +kernel

theorem f4Frame_weighted_kernel : ∀ (k : Fin 4) (γ : Fin Tag.F4.rank → ℤ),
    γ ∈ rootFinset .F4 →
    (∑ j : Fin 4, if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (orthRoot j)) = 0 →
      γ = orthRoot k ∨ γ = -orthRoot k := by
  decide +kernel

theorem f4Frame_coroot_reconstruction
    {F : Type} [Field F] (b : Fin 4 → Fˣ) (k : Fin 4)
    (hb : ∀ j : Fin 4, j ≠ k → rootChar (τ := .F4) b (orthRoot j) = 1) :
    (fun i => b i ^ 2) = corootDiagF4 (orthRoot k) (rootChar (τ := .F4) b (orthRoot k)) := by
  have hr0 : rootChar (τ := .F4) b (orthRoot 0) = b 1 := by
    change (∏ i : Fin 4, b i ^ (orthRoot (0 : Fin 4) i)) = _
    simp [orthRoot, Fin.prod_univ_four]
  have hr1 : rootChar (τ := .F4) b (orthRoot 1) = b 1 * b 2 ^ 2 := by
    change (∏ i : Fin 4, b i ^ (orthRoot (1 : Fin 4) i)) = _
    simp [orthRoot, Fin.prod_univ_four]
  have hr2 : rootChar (τ := .F4) b (orthRoot 2) = b 1 * b 2 ^ 2 * b 3 ^ 2 := by
    change (∏ i : Fin 4, b i ^ (orthRoot (2 : Fin 4) i)) = _
    simp [orthRoot, Fin.prod_univ_four]
  have hr3 : rootChar (τ := .F4) b (orthRoot 3) = b 0 ^ 2 * b 1 ^ 3 * b 2 ^ 4 * b 3 ^ 2 := by
    change (∏ i : Fin 4, b i ^ (orthRoot (3 : Fin 4) i)) = _
    simp [orthRoot, Fin.prod_univ_four]
  have hexp : ∀ (k : Fin 4) (i : Fin 4), iform (τ := .F4) (orthRoot k) (Pi.single i 1) / (2 : ℤ) =
      (match k.val, i.val with
        | 0, 0 => -1 | 0, 1 => 2 | 0, 2 => -1
        | 1, 0 => -1 | 1, 2 => 1 | 1, 3 => -1
        | 2, 0 => -1 | 2, 3 => 1
        | 3, 0 => 1 | _, _ => 0 : ℤ) := by
    decide +kernel
  have hfour : b 2 ^ 4 = (b 2 ^ 2) ^ 2 := by group
  fin_cases k
  · have h1' : b 1 * b 2 ^ 2 = 1 := hr1 ▸ hb 1 (by decide)
    have h2' : b 1 * b 2 ^ 2 * b 3 ^ 2 = 1 := hr2 ▸ hb 2 (by decide)
    have h3' : b 0 ^ 2 * b 1 ^ 3 * b 2 ^ 4 * b 3 ^ 2 = 1 := hr3 ▸ hb 3 (by decide)
    have hb2 : b 2 ^ 2 = (b 1)⁻¹ := eq_inv_of_mul_eq_one_right h1'
    have hb3 : b 3 ^ 2 = 1 := by rw [h1', one_mul] at h2'; exact h2'
    have hb0 : b 0 ^ 2 = (b 1)⁻¹ := by
      rw [hfour, hb2, hb3, mul_one] at h3'
      have hh : b 1 ^ 3 * ((b 1)⁻¹) ^ 2 = b 1 := by group
      rw [mul_assoc, hh] at h3'
      exact eq_inv_of_mul_eq_one_left h3'
    funext i
    change Fin 4 at i
    change b i ^ 2 = (rootChar (τ := .F4) b (orthRoot 0)) ^ (iform (orthRoot 0) (Pi.single i 1) / 2)
    rw [hexp (0 : Fin 4) i, hr0]
    fin_cases i <;> norm_num
    · exact hb0
    · exact hb2
    · exact hb3
  · have hb1 : b 1 = 1 := hr0 ▸ hb 0 (by decide)
    have h2' : b 1 * b 2 ^ 2 * b 3 ^ 2 = 1 := hr2 ▸ hb 2 (by decide)
    have h3' : b 0 ^ 2 * b 1 ^ 3 * b 2 ^ 4 * b 3 ^ 2 = 1 := hr3 ▸ hb 3 (by decide)
    rw [hb1, one_mul] at h2'
    have hb3 : b 3 ^ 2 = (b 2 ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right h2'
    rw [hb1, one_pow, mul_one, hfour, hb3] at h3'
    have hh : (b 2 ^ 2) ^ 2 * (b 2 ^ 2)⁻¹ = b 2 ^ 2 := by group
    rw [mul_assoc, hh] at h3'
    have hb0 : b 0 ^ 2 = (b 2 ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h3'
    funext i
    change Fin 4 at i
    change b i ^ 2 = (rootChar (τ := .F4) b (orthRoot 1)) ^ (iform (orthRoot 1) (Pi.single i 1) / 2)
    rw [hexp (1 : Fin 4) i, hr1, hb1, one_mul]
    fin_cases i <;> norm_num
    · exact hb0
    · simp only [hb1, one_pow]
    · exact hb3
  · have hb1 : b 1 = 1 := hr0 ▸ hb 0 (by decide)
    have h1' : b 1 * b 2 ^ 2 = 1 := hr1 ▸ hb 1 (by decide)
    have h3' : b 0 ^ 2 * b 1 ^ 3 * b 2 ^ 4 * b 3 ^ 2 = 1 := hr3 ▸ hb 3 (by decide)
    have hb2 : b 2 ^ 2 = 1 := by simpa only [hb1, one_mul] using h1'
    rw [hb1, one_pow, mul_one, hfour, hb2, one_pow, mul_one] at h3'
    have hb0 : b 0 ^ 2 = (b 3 ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h3'
    funext i
    change Fin 4 at i
    change b i ^ 2 = (rootChar (τ := .F4) b (orthRoot 2)) ^ (iform (orthRoot 2) (Pi.single i 1) / 2)
    rw [hexp (2 : Fin 4) i, hr2, hb1, one_mul, hb2, one_mul]
    fin_cases i <;> norm_num
    · exact hb0
    · simp only [hb1, one_pow]
    · exact hb2
  · have hb1 : b 1 = 1 := hr0 ▸ hb 0 (by decide)
    have h1' : b 1 * b 2 ^ 2 = 1 := hr1 ▸ hb 1 (by decide)
    have h2' : b 1 * b 2 ^ 2 * b 3 ^ 2 = 1 := hr2 ▸ hb 2 (by decide)
    have hb2 : b 2 ^ 2 = 1 := by simpa only [hb1, one_mul] using h1'
    have hb3 : b 3 ^ 2 = 1 := by simpa only [hb1, one_mul, hb2] using h2'
    funext i
    change Fin 4 at i
    change b i ^ 2 = (rootChar (τ := .F4) b (orthRoot 3)) ^ (iform (orthRoot 3) (Pi.single i 1) / 2)
    rw [hexp (3 : Fin 4) i, hr3, hb1, one_pow, mul_one, hfour, hb2, one_pow, mul_one, hb3, mul_one]
    fin_cases i <;> norm_num
    · simp only [hb1, one_pow]
    · exact hb2
    · exact hb3


theorem iform_orthRoot_self (k : Fin 4) : iform (orthRoot k) (orthRoot k) = 4 := by
  revert k
  decide +kernel

theorem fixes_long_root_of_rootCharStabilizer_f4
    {F : Type} [Field F] {c : Fˣ}
    (hc : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ 4 → c ^ m ≠ 1)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β) (hβlen : iform β β = 4)
    {w : WeylGroup .F4} (hw : w ∈ rootCharStabilizer (corootDiagF4 β c)) : w • β = β := by
  have hpairs : ∀ i : Fin Tag.F4.rank, iform β (w • Pi.single i 1) / 2 =
      iform β (Pi.single i 1) / 2 := by
    intro i
    have h := hw (Pi.single i 1)
    rw [rootChar_corootDiagF4 hβ hβlen, rootChar_corootDiagF4 hβ hβlen] at h
    have hpow : c ^ (iform β (w • Pi.single i 1) / 2 - iform β (Pi.single i 1) / 2) = 1 := by
      rw [_root_.zpow_sub, h, mul_inv_cancel]
    have hbounds := abs_iform_le_four_F4 hβ (IsRoot.smul (isRoot_single .F4 i) w)
    have hbounds' := abs_iform_le_four_F4 hβ (isRoot_single .F4 i)
    have hd : iform β (w • Pi.single i 1) / 2 - iform β (Pi.single i 1) / 2 = 0 := by
      by_contra hne
      exact hc _ hne (by
        have habs : |iform β (w • Pi.single i 1) / 2 - iform β (Pi.single i 1) / 2| ≤ 4 := by
          rw [abs_le] at hbounds hbounds' ⊢
          omega
        have hh := Int.natCast_natAbs (iform β (w • Pi.single i 1) / 2 - iform β (Pi.single i 1) / 2)
        omega) hpow
    omega
  have hpairs' : ∀ i : Fin Tag.F4.rank, iform β (w • Pi.single i 1) = iform β (Pi.single i 1) := by
    intro i
    have h1 := even_iform_of_long_F4 hβ hβlen (w • Pi.single i 1)
    have h2 := even_iform_of_long_F4 hβ hβlen (Pi.single i 1)
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have h := hpairs i
    omega
  have hzero : w⁻¹ • β - β = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    have hp : ∀ i : Fin Tag.F4.rank, iform (w⁻¹ • β - β) (Pi.single i 1) = 0 := by
      intro i
      have hact : iform (w⁻¹ • β) (Pi.single i 1) = iform β (w • Pi.single i 1) := by
        rw [← iform_smul_smul w (w⁻¹ • β) (Pi.single i 1), smul_inv_smul]
      rw [iform_sub_left, hact, hpairs', sub_self]
    rw [CFSG.ClassicalInvolution.ModelFacts.Levi.iform_eq_sum_single] at hpos
    simp only [hp, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  have hfix : w⁻¹ • β = β := sub_eq_zero.mp hzero
  have h := congrArg (w • ·) hfix
  rw [smul_inv_smul] at h
  exact h.symm

theorem commute_pinnedX_of_commute_pm_one
    {τ : Tag} (hτ : τ ≠ .G2) {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (β : Fin τ.rank → ℤ) {y : ModGL τ F}
    (hp : Commute y (pinnedX τ F β 1)) (hm : Commute y (pinnedX τ F β (-1)))
    (c : F) : Commute y (pinnedX τ F β c) := by
  obtain ⟨A, B, _, _, hexp⟩ :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.pinnedX_expand (L := F) hτ β
  have hplus : (y : Module.End F (RootModule τ F)) * (1 + (1 : F) • A + (1 : F) ^ 2 • B) =
      (1 + (1 : F) • A + (1 : F) ^ 2 • B) * (y : Module.End F (RootModule τ F)) := by
    simpa only [hexp] using hp.units_val.eq
  have hminus : (y : Module.End F (RootModule τ F)) * (1 + (-1 : F) • A + (-1 : F) ^ 2 • B) =
      (1 + (-1 : F) • A + (-1 : F) ^ 2 • B) * (y : Module.End F (RootModule τ F)) := by
    simpa only [hexp] using hm.units_val.eq
  obtain ⟨hA, hB⟩ := CFSG.HardMathSupport.Timmesfeld.LangTorus.commute_of_pm_points
    h2 (one_ne_zero : (1 : F) ≠ 0) hplus hminus
  apply Units.ext
  simp only [Units.val_mul, hexp, mul_add, add_mul, mul_one, one_mul,
    mul_smul_comm, smul_mul_assoc, hA, hB]

theorem commute_rootRankOne_baseChange_of_ne_g2
    {τ : Tag} (hτ : τ ≠ .G2) {F L : Type} [Field F] [Field L]
    (ι : F →+* L) (h2 : (2 : L) ≠ 0) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {y : ModGL τ F} (hy : ∀ x ∈ rootRankOneGroup τ F β, Commute y x) :
    ∀ x ∈ rootRankOneGroup τ L β, Commute (baseChangeGL ι y) x := by
  have hspan : ∀ (E : Type) [Field E], rootRankOneGroup τ E β =
      rootSubgroup τ E β ⊔ rootSubgroup τ E (-β) := by
    intro E _
    exact (exceptional_Lang_root_rank_one_torus_transport τ E hβ).1
  have hpinned : ∀ γ, γ = β ∨ γ = -β → ∀ c : L,
      Commute (baseChangeGL ι y) (pinnedX τ L γ c) := by
    intro γ hγ c
    have hmem : ∀ z : F, pinnedX τ F γ z ∈ rootRankOneGroup τ F β := by
      intro z
      rw [hspan F]
      rcases hγ with rfl | rfl
      · exact Subgroup.mem_sup_left (mem_rootSubgroup.mpr ⟨z, rfl⟩)
      · exact Subgroup.mem_sup_right (mem_rootSubgroup.mpr ⟨z, rfl⟩)
    have hp := (hy _ (hmem 1)).map (baseChangeGL ι)
    have hm := (hy _ (hmem (-1))).map (baseChangeGL ι)
    rw [baseChangeGL_pinnedX, map_one] at hp
    rw [baseChangeGL_pinnedX, map_neg, map_one] at hm
    exact commute_pinnedX_of_commute_pm_one hτ h2 γ hp hm c
  have hle : rootRankOneGroup τ L β ≤ centralizer {baseChangeGL ι y} := by
    rw [hspan L]
    apply sup_le
    all_goals
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      change pinnedX τ L _ c ∈ centralizer {baseChangeGL ι y}
      rw [Subgroup.mem_centralizer_singleton_iff]
    · exact (hpinned β (Or.inl rfl) c).eq.symm
    · exact (hpinned (-β) (Or.inr rfl) c).eq.symm
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem weyl_mem_frame_reflection_closure_f4 (k : Fin 4) {w : WeylGroup .F4}
    (hw : ∀ j : Fin 4, j ≠ k → w • orthRoot j = orthRoot j) :
    w ∈ Subgroup.closure {s : WeylGroup .F4 | ∃ γ, (γ = orthRoot k ∨ γ = -orthRoot k) ∧
      s = rootReflection γ} := by
  classical
  let v : Fin Tag.F4.rank → ℤ :=
    ∑ j : Fin 4, if j = k then 0 else (5 : ℤ) ^ j.val • orthRoot j
  have hv : w • v = v := by
    simp only [v, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = k
    · simp only [hj, ↓reduceIte, smul_zero]
    · simp only [hj, ↓reduceIte, smul_comm w, hw j hj]
  have hstab : w ∈ weylStabilizer .F4 (RootSpace.ofLattice v) := by
    rw [mem_weylStabilizer, weylAct_ofLattice, hv]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .F4).2.2.2.2.2
    (RootSpace.ofLattice v)] at hstab
  apply (Subgroup.closure_mono ?_) hstab
  rintro s ⟨γ, hγ, hinner, rfl⟩
  obtain ⟨c, hc, hform⟩ := exists_inner_ofLattice_eq_iform .F4
  have hzero : iform γ v = 0 := by
    rw [hform] at hinner
    exact_mod_cast (mul_eq_zero.mp hinner).resolve_left hc.ne'
  have heq : iform γ v =
      ∑ j : Fin 4, if j = k then 0 else (5 : ℤ) ^ j.val * iform γ (orthRoot j) := by
    change iform γ (∑ j : Fin 4, if j = k then 0 else (5 : ℤ) ^ j.val • orthRoot j) = _
    rw [iform_finset_sum_right]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · simp [iform]
    · exact iform_smul_right _ _ _
  rw [heq] at hzero
  exact ⟨γ, f4Frame_weighted_kernel k γ (mem_rootFinset.mpr hγ) hzero, rfl⟩

theorem rootDiagUnit_corootDiagF4_mem_rankOne
    {F : Type} [Field F] {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β)
    (hlen : iform β β = 4) (c : Fˣ) :
    rootDiagUnit .F4 (corootDiagF4 β c) ∈ rootRankOneGroup .F4 F β := by
  have heq : rootTorusSL2 .F4 F β c = rootDiagUnit .F4 (corootDiagF4 β c) := by
    rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hβ]
    congr 1
    funext i
    rw [hlen]
    congr 1
    omega
  rw [← heq]
  exact ⟨_, rfl⟩

theorem mem_torus_mul_rankOne_of_commutes_other_f4
    {F : Type} [Field F] [Infinite F] (k : Fin 4) {y : ModGL .F4 F}
    (hy : y ∈ adjointGroup .F4 F)
    (hc : ∀ j : Fin 4, j ≠ k → ∀ x ∈ rootRankOneGroup .F4 F (orthRoot j), Commute y x) :
    ∃ t ∈ torusGroup .F4 F, ∃ r ∈ rootRankOneGroup .F4 F (orthRoot k), y = t * r := by
  classical
  let T : Set (Fin Tag.F4.rank → Fˣ) :=
    {a | ∃ j : Fin 4, j ≠ k ∧ ∃ c : Fˣ, a = corootDiagF4 (orthRoot j) c}
  let S : Set (Fin Tag.F4.rank → ℤ) := {γ | γ = orthRoot k ∨ γ = -orthRoot k}
  obtain ⟨c, hcPow⟩ := exists_unit_pow_ne_one (k := F) 4
  have hcZ : ∀ m : ℤ, m ≠ 0 → m.natAbs ≤ 4 → c ^ m ≠ 1 := by
    intro m hm hb heq
    have hz := eq_zero_of_zpow_eq_one hcPow (m := m) (by
      rw [← Int.natCast_natAbs]; exact_mod_cast hb) heq
    exact hm hz
  have horth : ∀ i j : Fin 4, i ≠ j → iform (orthRoot i) (orthRoot j) = 0 := by
    intro i j hij
    simpa only [iform, dotProduct, mulVec, Finset.mul_sum, mul_assoc] using
      CFSG.StandardType.TableBF4Two.orthRoot_orth i j hij
  have hkernel : CFSG.RankThree.PartOne.KE8F.famKernel T = S := by
    ext γ
    constructor
    · rintro ⟨hγ, hγT⟩
      apply f4Frame_orthogonal_kernel k γ (mem_rootFinset.mpr hγ)
      intro j hj
      have heq := hγT (corootDiagF4 (orthRoot j) c) ⟨j, hj, c, rfl⟩
      rw [rootChar_corootDiagF4 (isRoot_orthRoot j) (iform_orthRoot_self j)] at heq
      have hz : iform (orthRoot j) γ / 2 = 0 := by
        by_contra hne
        have hh := abs_iform_le_four_F4 (isRoot_orthRoot j) hγ
        exact hcZ _ hne (by
          rw [abs_le] at hh
          have ha := Int.natCast_natAbs (iform (orthRoot j) γ / 2)
          have habs : |iform (orthRoot j) γ / 2| ≤ 4 := by rw [abs_le]; omega
          omega) heq
      obtain ⟨a, ha⟩ := even_iform_of_long_F4 (isRoot_orthRoot j) (iform_orthRoot_self j) γ
      omega
    · intro hγ
      refine ⟨?_, ?_⟩
      · rcases hγ with rfl | rfl
        · exact isRoot_orthRoot k
        · exact IsRoot.neg (isRoot_orthRoot k)
      · rintro a ⟨j, hj, d, rfl⟩
        rw [rootChar_corootDiagF4 (isRoot_orthRoot j) (iform_orthRoot_self j)]
        rcases hγ with rfl | rfl
        · rw [horth j k hj]; simp
        · rw [iform_neg_right, horth j k hj]; simp
  have hstab : CFSG.RankThree.PartOne.KE8F.famStabilizer T ⊆
      (Subgroup.closure {s | ∃ γ ∈ CFSG.RankThree.PartOne.KE8F.famKernel T,
        s = rootReflection γ} : Set (WeylGroup .F4)) := by
    intro w hw
    have hfix : ∀ j : Fin 4, j ≠ k → w • orthRoot j = orthRoot j := by
      intro j hj
      exact fixes_long_root_of_rootCharStabilizer_f4 hcZ (isRoot_orthRoot j)
        (iform_orthRoot_self j) (hw _ ⟨j, hj, c, rfl⟩)
    change w ∈ Subgroup.closure _
    rw [hkernel]
    exact weyl_mem_frame_reflection_closure_f4 k hfix
  have hS : ∀ γ ∈ S, IsRoot .F4 γ := by
    rintro γ (rfl | rfl)
    · exact isRoot_orthRoot k
    · exact IsRoot.neg (isRoot_orthRoot k)
  have hSn : ∀ γ ∈ S, -γ ∈ S := by
    rintro γ (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  have hcomm : ∀ a ∈ T, y * rootDiagUnit .F4 a = rootDiagUnit .F4 a * y := by
    rintro a ⟨j, hj, d, rfl⟩
    exact (hc j hj _ (rootDiagUnit_corootDiagF4_mem_rankOne
      (isRoot_orthRoot j) (iform_orthRoot_self j) d)).eq
  have hmem := CFSG.RankThree.PartOne.KE8F.mem_torus_mul_rootSpan_of_commute_fam
    T hstab hS hSn (by rw [hkernel]) hy hcomm
  have heq : rootSpan .F4 F S = rootRankOneGroup .F4 F (orthRoot k) := by
    have hs : S = {orthRoot k, -orthRoot k} := by ext γ; simp only [S, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [hs, rootSpan, iSup_insert, iSup_singleton]
    exact (exceptional_Lang_root_rank_one_torus_transport .F4 F (isRoot_orthRoot k)).1.symm
  obtain ⟨t, ht, r, hr, hyr⟩ := hmem
  exact ⟨t, ht, r, heq ▸ hr, hyr.symm⟩

theorem square_mem_rankOne_of_commutes_other_f4
    {F : Type} [Field F] [Infinite F] (k : Fin 4) {y : ModGL .F4 F}
    (hy : y ∈ adjointGroup .F4 F)
    (hc : ∀ j : Fin 4, j ≠ k → ∀ x ∈ rootRankOneGroup .F4 F (orthRoot j), Commute y x) :
    y ^ 2 ∈ rootRankOneGroup .F4 F (orthRoot k) := by
  obtain ⟨t, ht, r, hr, hyr⟩ := mem_torus_mul_rankOne_of_commutes_other_f4 k hy hc
  obtain ⟨b, htb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hct : ∀ j : Fin 4, j ≠ k → ∀ x ∈ rootRankOneGroup .F4 F (orthRoot j), Commute t x := by
    intro j hj x hx
    obtain ⟨B, rfl⟩ := hr
    obtain ⟨A, rfl⟩ := hx
    have h := (hc j hj _ ⟨A, rfl⟩).mul_left
      (CFSG.StandardType.TableBF4Two.commute_rootSL2 hj.symm B A).inv_left
    simpa only [hyr, mul_inv_cancel_right] using h
  have hb : ∀ j : Fin 4, j ≠ k → rootChar b (orthRoot j) = 1 := by
    intro j hj
    have hmem : pinnedX .F4 F (orthRoot j) 1 ∈ rootRankOneGroup .F4 F (orthRoot j) := by
      rw [(exceptional_Lang_root_rank_one_torus_transport .F4 F (isRoot_orthRoot j)).1]
      exact Subgroup.mem_sup_left (mem_rootSubgroup.mpr ⟨1, rfl⟩)
    exact CFSG.LieType.Chevalley.rootChar_eq_one_of_commute_rootDiagUnit_pinnedX
      b (isRoot_orthRoot j) (by rw [← htb]; exact hct j hj _ hmem)
  have htsq : t ^ 2 ∈ rootRankOneGroup .F4 F (orthRoot k) := by
    have heq : t ^ 2 = rootDiagUnit .F4 (fun i => b i ^ 2) := by
      rw [htb]
      exact (map_pow (rootDiagUnitHom .F4 F) b 2).symm
    have hrec : (fun i : Fin Tag.F4.rank => b i ^ 2) =
        corootDiagF4 (orthRoot k) (rootChar (τ := .F4) b (orthRoot k)) :=
      f4Frame_coroot_reconstruction b k hb
    rw [heq, hrec]
    exact rootDiagUnit_corootDiagF4_mem_rankOne (isRoot_orthRoot k) (iform_orthRoot_self k) _
  have hnorm : t ∈ normalizer (rootRankOneGroup .F4 F (orthRoot k) : Set (ModGL .F4 F)) := by
    have hs : rootSpan .F4 F {orthRoot k, -orthRoot k} = rootRankOneGroup .F4 F (orthRoot k) := by
      rw [rootSpan, iSup_insert, iSup_singleton]
      exact (exceptional_Lang_root_rank_one_torus_transport .F4 F (isRoot_orthRoot k)).1.symm
    rw [← hs]
    exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (by
      rintro γ (rfl | h)
      · exact isRoot_orthRoot k
      · rw [Set.mem_singleton_iff] at h
        rw [h]
        exact IsRoot.neg (isRoot_orthRoot k)) ht
  have hconj : t⁻¹ * r * t ∈ rootRankOneGroup .F4 F (orthRoot k) := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hnorm) r).mp hr
    simpa only [inv_inv] using h
  have heq : y ^ 2 = t ^ 2 * (t⁻¹ * r * t * r) := by rw [hyr, pow_two, pow_two]; group
  rw [heq]
  exact mul_mem htsq (mul_mem hconj hr)

theorem mem_rankOne_of_commutes_other_f4_of_pow_eq_one
    {F : Type} [Field F] [Infinite F] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (k : Fin 4) {y : ModGL .F4 F} (hy : y ∈ adjointGroup .F4 F)
    (hc : ∀ j : Fin 4, j ≠ k → ∀ x ∈ rootRankOneGroup .F4 F (orthRoot j), Commute y x)
    (hyp : y ^ p = 1) : y ∈ rootRankOneGroup .F4 F (orthRoot k) := by
  have hysq := square_mem_rankOne_of_commutes_other_f4 k hy hc
  have hcop : Nat.Coprime 2 p := (Nat.coprime_two_right.mpr (hp.odd_of_ne_two hp2)).symm
  obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have heq : y = (y ^ 2) ^ m := by
    rw [← pow_mul, pow_eq_pow_mod (2 * m) hyp, hm, pow_one]
  rw [heq]
  exact pow_mem hysq m

theorem le_rankOne_of_commutes_other_f4
    {p e : ℕ} [hp : Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    (k : Fin 4) {R : Subgroup (adjointGroup .F4 (GaloisField p e))}
    (hgen : Subgroup.closure {x : R | x ^ p = 1} = ⊤)
    (hc : ∀ j : Fin 4, j ≠ k → Commutes R (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) j).range) :
    R ≤ (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) k).range := by
  let F := GaloisField p e
  let L := CFSG.ClassicalInvolution.ModelFacts.Levi.AlgClosGF p e
  let ι : F →+* L := algebraMap F L
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff L p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hp1 | hpTwo
    · exact hp.out.ne_one hp1
    · exact hp2 hpTwo
  have hcomm : ∀ j : Fin 4, j ≠ k → ∀ a : R,
      ∀ x ∈ rootRankOneGroup .F4 L (orthRoot j),
        Commute (baseChangeGL ι (a.1 : ModGL .F4 F)) x := by
    intro j hj a
    apply commute_rootRankOne_baseChange_of_ne_g2 (by decide) ι h2 (isRoot_orthRoot j)
    rintro x ⟨A, rfl⟩
    have hh := hc j hj a a.2 (CFSG.StandardType.TableBF4Two.rho F j A) ⟨A, rfl⟩
    exact congrArg (fun z : adjointGroup .F4 F => (z : ModGL .F4 F)) hh
  have hgenerators : ∀ a : R, a ^ p = 1 →
      a.1 ∈ (CFSG.StandardType.TableBF4Two.rho F k).range := by
    intro a hap
    have hbc : baseChangeGL ι (a.1 : ModGL .F4 F) ∈ rootRankOneGroup .F4 L (orthRoot k) := by
      apply mem_rankOne_of_commutes_other_f4_of_pow_eq_one hp.out hp2 k
        (baseChangeGL_mem_adjointGroup ι a.1.2) (fun j hj => hcomm j hj a)
      have h := congrArg (fun z : R => baseChangeGL ι (z.1 : ModGL .F4 F)) hap
      simpa only [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one] using h
    obtain ⟨B, hB⟩ := hbc
    have hfix : CFSG.LieType.AlgebraicGroups.entrywiseFrobGL .F4 L p e (rootSL2 .F4 L (orthRoot k) B) =
        rootSL2 .F4 L (orthRoot k) B := by
      rw [hB]
      exact entrywiseFrobGL_baseChangeGL_algebraMap _
    obtain ⟨A, hA⟩ := exists_rootSL2_of_frobFixed (isRoot_orthRoot k) hp2 hfix
    refine ⟨A, ?_⟩
    apply Subtype.ext
    apply baseChangeGL_injective ι
    simpa only [CFSG.StandardType.TableBF4Two.coe_rho] using hA.symm.trans hB
  have htop : (⊤ : Subgroup R) ≤
      ((CFSG.StandardType.TableBF4Two.rho F k).range).comap R.subtype := by
    rw [← hgen, Subgroup.closure_le]
    exact hgenerators
  intro a ha
  exact htop (show (⟨a, ha⟩ : R) ∈ (⊤ : Subgroup R) from trivial)

theorem rho_f4_mem_modelFund
    {p e : ℕ} [hp : Fact p.Prime] (k : Fin 4) :
    (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) k).range ∈
      fundamentalSubgroups .F4 (f4Datum (GaloisField p e)) := by
  have heq : (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) k).range =
      stdRankOne (f4Datum (GaloisField p e)) (orthRoot k) := by
    ext x
    rw [mem_stdRankOne_f4_iff' (isRoot_orthRoot k)]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩
      exact ⟨A, Subtype.ext hA.symm⟩
  rw [heq]
  have hlong := CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_f4Datum_of_iform_eq_four
    (K := GaloisField p e) (isRoot_orthRoot k) (iform_orthRoot_self k)
  refine ⟨1, orthRoot k, Or.inl ?_, ?_⟩
  · exact (CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_iff _ _).mp hlong
  · exact (CFSG.ClassicalInvolution.Generic.conjSub_one _).symm

theorem eq_of_commutes_other_f4_modelFund
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .F4 0 p e)
    (k : Fin 4) {R : Subgroup (adjointGroup .F4 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .F4 (f4Datum (GaloisField p e)))
    (hc : ∀ j : Fin 4, j ≠ k → Commutes R (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) j).range) :
    R = (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) k).range := by
  have : NeZero e := ⟨by have := hadm.2.1; omega⟩
  obtain ⟨eR⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
    hp2 (t := .F4) (by trivial) hadm (by decide) (by decide) hR
  let eR' : R ≃* SL2 (GaloisField p e) := eR
  have hle := le_rankOne_of_commutes_other_f4 hp2 k
    (CFSG.LieType.HighestRoot.closure_pow_eq_one_eq_top_of_mulEquiv p eR') hc
  let eA : SL2 (GaloisField p e) ≃*
      (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) k).range :=
    MonoidHom.ofInjective (CFSG.StandardType.TableBF4Two.rho_injective k)
  have hcard : Nat.card (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) k).range = Nat.card R :=
    (Nat.card_congr eA.toEquiv).symm.trans (Nat.card_congr eR'.toEquiv).symm
  have : Finite (adjointGroup .F4 (GaloisField p e)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hp2 hp.out (t := .F4) (by trivial) hadm
  exact Subgroup.eq_of_le_of_card_ge hle hcard.le


theorem exists_full_frame_funSet_f4
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .F4 0 p e) (hX : CFSG.Blueprint.LieModel X .F4 0 p e)
    (ψ : adjointGroup .F4 (GaloisField p e) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (adjointGroup .F4 (GaloisField p e))) (P : Sylow 2 X) :
    ∃ c : X, F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
      Set.range (fun k : Fin 4 => (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) k).range.map
        ((MulAut.conj c).toMonoidHom.comp ψ)) := by
  let F := GaloisField p e
  let A : Fin 4 → Subgroup (adjointGroup .F4 F) := fun k =>
    (CFSG.StandardType.TableBF4Two.rho F k).range
  have hA : ∀ k, IsFundamentalOver (p ^ e) ((A k).map ψ) := fun k =>
    ⟨.F4, 0, p, e, hp.out, hp2, rfl, trivial, hadm, ψ, hψ, hker,
      A k, rho_f4_mem_modelFund k, rfl⟩
  have hcA : ∀ i j, i ≠ j → Commutes (A i) (A j) := by
    intro i j hij
    rintro _ ⟨B, rfl⟩ _ ⟨C, rfl⟩
    exact CFSG.StandardType.TableBF4Two.commute_rho hij B C
  have hcψ : ∀ i j, i ≠ j → Commutes ((A i).map ψ) ((A j).map ψ) := by
    intro i j hij
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simpa only [map_mul] using congrArg ψ (hcA i j hij a ha b hb)
  have hnorm : ∀ i j, (A j).map ψ ≤ normalizer ((A i).map ψ : Set X) := by
    intro i j
    by_cases hij : i = j
    · subst j
      exact Subgroup.le_normalizer
    · have hcent : (A j).map ψ ≤ centralizer ((A i).map ψ : Set X) :=
        fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => hcψ i j hij b hb a ha)
      exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ e))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h)
    (fun k => (A k).map ψ) hA hnorm P
  let ψc : adjointGroup .F4 F →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (adjointGroup .F4 F) := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hc' : ∀ k, (A k).map ψc ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) := by
    intro k
    simpa only [ψc, Subgroup.map_map] using hc k
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX (by simp) (hc' 0).1
  have hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p f :=
    ⟨.F4, 0, e, hadm, rfl, hX.quotient_center hZ⟩
  refine ⟨c, ?_⟩
  ext J
  constructor
  · intro hJ
    by_contra hnot
    have hne : ∀ k, J ≠ (A k).map ψc := fun k h => hnot ⟨k, h.symm⟩
    obtain ⟨R, hR, hJR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX (by trivial) (by simp) hL2 ψc hψc hkerC hJ.1
    have hcomm : ∀ k, Commutes R (A k) := by
      intro k
      apply commutes_modelFund_of_commutes_map hp2 (t := .F4) (by trivial) hadm ψc hkerC hR
      rw [← hJR]
      have hh := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
        hp.out hp2 hdesc hL2 P hJ (hc' k) (hne k)
      exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hh ha) b hb).symm
    have heq := eq_of_commutes_other_f4_modelFund hp2 hadm 0 hR (fun j _ => hcomm j)
    exact hne 0 (hJR.trans (congrArg (Subgroup.map ψc) heq))
  · rintro ⟨k, rfl⟩
    exact hc' k

theorem ncard_funSet_le_four_of_f4
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .F4 0 p e) (hX : CFSG.Blueprint.LieModel X .F4 0 p e)
    (P : Sylow 2 X) :
    (F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)).ncard ≤ 4 := by
  obtain ⟨ψ₀, hψ₀, hker₀⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .F4 0 p e hp.out hp2 (by trivial) hadm X hX
  let ψ : adjointGroup .F4 (GaloisField p e) →* X := ψ₀
  have hψ : Function.Surjective ψ := hψ₀
  have hker : ψ.ker ≤ center (adjointGroup .F4 (GaloisField p e)) := hker₀
  obtain ⟨c, hfull⟩ := exists_full_frame_funSet_f4 hp2 hadm hX ψ hψ hker P
  rw [hfull]
  have h := Finite.card_range_le (fun k : Fin 4 =>
    (CFSG.StandardType.TableBF4Two.rho (GaloisField p e) k).range.map
      ((MulAut.conj c).toMonoidHom.comp ψ))
  simpa only [Nat.card_fin, ← Nat.card_coe_set_eq] using h

theorem centralizingLayer_funSet_eq_of_f4
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p e : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .F4 0 p e) (hX : CFSG.Blueprint.LieModel X .F4 0 p e)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X)) :
    centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J}
      {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
        J ≠ K ∧ x ∈ J} = K := by
  let F := GaloisField p e
  let A : Fin 4 → Subgroup (adjointGroup .F4 F) := fun k =>
    (CFSG.StandardType.TableBF4Two.rho F k).range
  obtain ⟨ψ₀, hψ₀, hker₀⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .F4 0 p e hp.out hp2 (by trivial) hadm X hX
  let ψ : adjointGroup .F4 F →* X := ψ₀
  have hψ : Function.Surjective ψ := hψ₀
  have hker : ψ.ker ≤ center (adjointGroup .F4 F) := hker₀
  obtain ⟨c, hfull⟩ := exists_full_frame_funSet_f4 hp2 hadm hX ψ hψ hker P
  let ψc : adjointGroup .F4 F →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (adjointGroup .F4 F) := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker] at ha ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using ha)
  have hfull' : F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X) =
      Set.range (fun k => (A k).map ψc) := hfull
  obtain ⟨k, hKmap⟩ : ∃ k, (A k).map ψc = K := by
    have hk : K ∈ Set.range (fun k => (A k).map ψc) := hfull' ▸ hK
    exact hk
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX (by simp) hK.1
  have hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p f :=
    ⟨.F4, 0, e, hadm, rfl, hX.quotient_center hZ⟩
  have hinj : Function.Injective (fun j => (A j).map ψc) := by
    intro i j heq
    by_contra hij
    have hcA : Commutes (A i) (A j) := by
      rintro _ ⟨B, rfl⟩ _ ⟨C, rfl⟩
      exact CFSG.StandardType.TableBF4Two.commute_rho hij B C
    let eA : A i ≃* SL2 F :=
      (MonoidHom.ofInjective (CFSG.StandardType.TableBF4Two.rho_injective i)).symm
    exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC eA hcA heq
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    obtain ⟨R, hR, hJR, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
      hp.out hp2 hadm hX (by trivial) (by simp) hL2 ψc hψc hkerC hJ.1
    let R' : Subgroup (adjointGroup .F4 F) := R
    have hR' : R' ∈ fundamentalSubgroups .F4 (f4Datum F) := hR
    have hJR' : J = R'.map ψc := hJR
    have hcomm : ∀ j : Fin 4, j ≠ k → Commutes R' (A j) := by
      intro j hj
      have hne : (A j).map ψc ≠ K := fun h => hj (hinj (h.trans hKmap.symm))
      have hcJ : Commutes (R'.map ψc) ((A j).map ψc) := by
        rw [← hJR']
        intro a ha b hb
        exact (Subgroup.mem_centralizer_iff.mp (hJ.2 ha) b
          ⟨(A j).map ψc, hfull'.symm ▸ ⟨j, rfl⟩, hne, hb⟩).symm
      exact commutes_modelFund_of_commutes_map hp2 (by trivial) hadm ψc hkerC hR' hcJ
    have heq : R' = A k := eq_of_commutes_other_f4_modelFund hp2 hadm k hR' hcomm
    rw [hJR', heq, hKmap]
  · refine le_centralizingLayer ⟨hK.1, ?_⟩
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro b ⟨J, hJ, hJK, hb⟩
    have hh := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hJ hK hJK
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hh hb) a ha).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
