module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJEq
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGRootNormInnerRankOne

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
  CFSG.LinearAlgebra.RootGroupSL CFSG.LieType.Universal
open Matrix

private theorem e6n2_h02 : (0 : Fin 3) ≠ 2 := by decide

private noncomputable def e6n2_e3 : DSpace F4 F4 ≃ₗ[F4] (Fin 3 → F4) where
  toFun v := ![v.1, v.2.1, v.2.2]
  invFun f := (f 0, f 1, f 2)
  map_add' u v := by
    ext i <;> fin_cases i <;> simp
  map_smul' c v := by
    ext i <;> fin_cases i <;> simp
  left_inv v := by
    ext <;> simp
  right_inv f := by
    ext i <;> fin_cases i <;> simp

private noncomputable def e6n2_eD :
    SpecialLinearGroup F4 (DSpace F4 F4) ≃* Matrix.SpecialLinearGroup (Fin 3) F4 :=
  (SpecialLinearGroup.congr_linearEquiv e6n2_e3).trans
    (Matrix.SpecialLinearGroup.toLin'_equiv).symm

private theorem e6n2_eD_rootElt (t : F4) :
    e6n2_eD (rootElt F4 F4 t) = Matrix.SpecialLinearGroup.transvection e6n2_h02 t := by
  apply Matrix.SpecialLinearGroup.toLin'_equiv.injective
  show Matrix.SpecialLinearGroup.toLin'_equiv
      ((SpecialLinearGroup.congr_linearEquiv e6n2_e3).trans
        (Matrix.SpecialLinearGroup.toLin'_equiv).symm (rootElt F4 F4 t)) = _
  rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  apply SpecialLinearGroup.ext
  intro v
  rw [SpecialLinearGroup.congr_linearEquiv_apply_apply]
  show e6n2_e3 (rootEquiv F4 F4 t (e6n2_e3.symm v)) =
    (Matrix.SpecialLinearGroup.toLin'_equiv (Matrix.SpecialLinearGroup.transvection e6n2_h02 t)) v
  rw [show (Matrix.SpecialLinearGroup.toLin'_equiv
        (Matrix.SpecialLinearGroup.transvection e6n2_h02 t)) v =
      Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.transvection e6n2_h02 t) v
      from rfl]
  rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec_eq]
  ext i <;> fin_cases i <;>
    simp [e6n2_e3, rootEquiv, shearE, LinearMap.mulLeft_apply, mul_comm]

private theorem e6n2_rootSL_map_eD :
    (rootSL F4 F4 F4).map e6n2_eD.toMonoidHom = SpecialLinear.rootSubgroup 2 F4 e6n2_h02 := by
  ext g
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hg
    obtain ⟨t, ht⟩ := mem_rootSL_iff.mp hg
    have hge : e6n2_eD.symm g = rootElt F4 F4 t := Subtype.ext ht
    have hg' : g = e6n2_eD (rootElt F4 F4 t) := by
      rw [← hge, MulEquiv.apply_symm_apply]
    rw [hg', e6n2_eD_rootElt]
    exact SpecialLinear.transvection_mem_rootSubgroup e6n2_h02 t
  · intro hg
    obtain ⟨t, ht⟩ := (SpecialLinear.mem_rootSubgroup e6n2_h02 g).mp hg
    have hge : e6n2_eD.symm g = rootElt F4 F4 t := by
      rw [← ht, ← e6n2_eD_rootElt t, MulEquiv.symm_apply_apply]
    simpa [hge] using rootElt_mem_rootSL t

private theorem e6n2_top_symm_map {E : Type*} [Group E] (R : Subgroup E) :
    R.map (Subgroup.topEquiv (G := E)).symm.toMonoidHom = R.subgroupOf (⊤ : Subgroup E) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Subgroup.mem_subgroupOf] using hy
  · intro hx
    exact ⟨x.1, Subgroup.mem_subgroupOf.mp hx, Subtype.ext rfl⟩

private lemma e6n2_finProdFinEquiv_blk (k : Fin 3) (j : Fin 2) :
    finProdFinEquiv (k, j) = blk k j := by
  apply Fin.ext
  rw [finProdFinEquiv_apply_val]
  show (j : ℕ) + 2 * (k : ℕ) = 2 * (k : ℕ) + (j : ℕ)
  omega

private lemma e6n2_blk_eq_blk_iff {k l : Fin 3} {j j' : Fin 2} :
    blk k j = blk l j' ↔ k = l ∧ j = j' := by
  constructor
  · intro h
    have hv : 2 * (k : ℕ) + (j : ℕ) = 2 * (l : ℕ) + (j' : ℕ) := by
      simpa [blk] using congrArg Fin.val h
    constructor
    · apply Fin.ext; omega
    · apply Fin.ext; omega
  · rintro ⟨rfl, rfl⟩
    rfl

private lemma e6n2_blk_ne_of_ne {k l : Fin 3} (h : k ≠ l) (j : Fin 2) : blk k j ≠ blk l j :=
  fun hh => h (e6n2_blk_eq_blk_iff.mp hh).1

private lemma e6n2_blk_ne_of_ne' {k l : Fin 3} (h : k ≠ l) (j j' : Fin 2) :
    blk k j ≠ blk l j' :=
  fun hh => h (e6n2_blk_eq_blk_iff.mp hh).1

private lemma e6n2_resMat_single (k l : Fin 3) (c : F4) :
    resMat 3 (Matrix.single k l c) =
      Matrix.single (blk k 0) (blk l 0) (f4Eps c 0 0) +
      Matrix.single (blk k 0) (blk l 1) (f4Eps c 0 1) +
      Matrix.single (blk k 1) (blk l 0) (f4Eps c 1 0) +
      Matrix.single (blk k 1) (blk l 1) (f4Eps c 1 1) := by
  ext r s
  obtain ⟨⟨i, j⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective r
  obtain ⟨⟨i', j'⟩, rfl⟩ := (finProdFinEquiv (m := 3) (n := 2)).surjective s
  rw [resMat_apply]
  simp only [Matrix.add_apply, Matrix.single_apply, e6n2_finProdFinEquiv_blk, e6n2_blk_eq_blk_iff]
  by_cases hk : k = i <;> by_cases hl : l = i'
  · fin_cases j <;> fin_cases j' <;> simp [hk, hl]
  · simp [hk, hl]
  · simp [hk, hl]
  · simp [hk, hl]

private lemma e6n2_resMat_single_one (k l : Fin 3) :
    resMat 3 (Matrix.single k l (1 : F4)) =
      Matrix.single (blk k 0) (blk l 0) (1 : F2) +
      Matrix.single (blk k 1) (blk l 1) (1 : F2) := by
  rw [e6n2_resMat_single, map_one]
  have h01 : (1 : Matrix (Fin 2) (Fin 2) F2) 0 1 = 0 := by
    rw [Matrix.one_apply]; exact if_neg (by decide)
  have h10 : (1 : Matrix (Fin 2) (Fin 2) F2) 1 0 = 0 := by
    rw [Matrix.one_apply]; exact if_neg (by decide)
  have h00 : (1 : Matrix (Fin 2) (Fin 2) F2) 0 0 = 1 := by
    rw [Matrix.one_apply]; exact if_pos rfl
  have h11 : (1 : Matrix (Fin 2) (Fin 2) F2) 1 1 = 1 := by
    rw [Matrix.one_apply]; exact if_pos rfl
  rw [h00, h01, h10, h11, Matrix.single_zero, Matrix.single_zero]
  abel

private lemma e6n2_resMat_single_omega (k l : Fin 3) :
    resMat 3 (Matrix.single k l f4Omega) =
      Matrix.single (blk k 0) (blk l 1) (1 : F2) +
      Matrix.single (blk k 1) (blk l 0) (1 : F2) +
      Matrix.single (blk k 1) (blk l 1) (1 : F2) := by
  rw [e6n2_resMat_single, f4Eps_omega]
  have h00 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 0 0 = 0 := by simp
  have h01 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 0 1 = 1 := by simp
  have h10 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 1 0 = 1 := by simp
  have h11 : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F2) 1 1 = 1 := by simp
  rw [h00, h01, h10, h11, Matrix.single_zero]
  abel

private lemma e6n2_one_add_mul_one_add {A B : Matrix (Fin 6) (Fin 6) F2} (h : A * B = 0) :
    ((1 : Matrix (Fin 6) (Fin 6) F2) + A) * (1 + B) = 1 + (A + B) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h, add_zero]
  abel

private lemma e6n2_one_add_single_mul_three {a b c d e f : Fin 6}
    (hbc : b ≠ c) (hbe : b ≠ e) (hde : d ≠ e) :
    ((1 + Matrix.single a b (1 : F2)) * (1 + Matrix.single c d (1 : F2))) *
        (1 + Matrix.single e f (1 : F2)) =
      1 + (Matrix.single a b (1 : F2) + Matrix.single c d (1 : F2) +
        Matrix.single e f (1 : F2)) := by
  have hAC : Matrix.single a b (1 : F2) * Matrix.single c d (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) a b c hbc (1 : F2)
  have hAE : Matrix.single a b (1 : F2) * Matrix.single e f (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) a b e hbe (1 : F2)
  have hCE : Matrix.single c d (1 : F2) * Matrix.single e f (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) c d e hde (1 : F2)
  have hACE : (Matrix.single a b (1 : F2) + Matrix.single c d (1 : F2)) *
      Matrix.single e f (1 : F2) = 0 := by
    rw [Matrix.add_mul, hAE, hCE, add_zero]
  rw [e6n2_one_add_mul_one_add hAC, e6n2_one_add_mul_one_add hACE]

private theorem e6n2_resSL_transvection_one (k l : Fin 3) (hkl : k ≠ l) :
    resSL 3 (Matrix.SpecialLinearGroup.transvection hkl (1 : F4)) =
      Matrix.SpecialLinearGroup.transvection (e6n2_blk_ne_of_ne hkl 0) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (e6n2_blk_ne_of_ne hkl 1) (1 : F2) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_resSL,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one, e6n2_resMat_single_one]
  have hAB : Matrix.single (blk k 0) (blk l 0) (1 : F2) *
      Matrix.single (blk k 1) (blk l 1) (1 : F2) = 0 :=
    Matrix.single_mul_single_of_ne (1 : F2) (blk k 0) (blk l 0) (blk k 1)
      (e6n2_blk_ne_of_ne' hkl.symm 0 1) (1 : F2)
  rw [e6n2_one_add_mul_one_add hAB]

private theorem e6n2_resSL_transvection_omega (k l : Fin 3) (hkl : k ≠ l) :
    resSL 3 (Matrix.SpecialLinearGroup.transvection hkl f4Omega) =
      Matrix.SpecialLinearGroup.transvection (e6n2_blk_ne_of_ne' hkl 0 1) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (e6n2_blk_ne_of_ne' hkl 1 0) (1 : F2) *
        Matrix.SpecialLinearGroup.transvection (e6n2_blk_ne_of_ne hkl 1) (1 : F2) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_resSL,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
      map_add, map_one, e6n2_resMat_single_omega]
  exact (e6n2_one_add_single_mul_three (a := blk k 0) (b := blk l 1) (c := blk k 1)
    (d := blk l 0) (e := blk k 1) (f := blk l 1)
    (e6n2_blk_ne_of_ne hkl.symm 1) (e6n2_blk_ne_of_ne hkl.symm 1)
    (e6n2_blk_ne_of_ne' hkl.symm 0 1)).symm

private lemma e6n2_f4Omega_sq_add_one : f4Omega ^ 2 = f4Omega + 1 := by
  have h : f4Omega ^ 2 + (f4Omega + 1) = 0 := by
    rw [← add_assoc]; exact f4Omega_sq
  have h2 : f4Omega ^ 2 = -(f4Omega + 1) := add_eq_zero_iff_eq_neg.mp h
  rw [h2, neg_add, CharTwo.neg_eq, CharTwo.neg_eq]

private lemma e6n2_Phi_transvection_one
   (k l : Fin 3) (hkl : k ≠ l) :
    (E6Pilot.slToAdjointE6 F2).comp (resSL 3)
        (Matrix.SpecialLinearGroup.transvection hkl (1 : F4)) = rOne k l := by
  rw [MonoidHom.comp_apply, e6n2_resSL_transvection_one k l hkl, map_mul,
      E6Pilot.slToAdjointE6_transvection, E6Pilot.slToAdjointE6_transvection]
  rfl

private lemma e6n2_Phi_transvection_omega
   (k l : Fin 3) (hkl : k ≠ l) :
    (E6Pilot.slToAdjointE6 F2).comp (resSL 3)
        (Matrix.SpecialLinearGroup.transvection hkl f4Omega) = rOmega k l := by
  rw [MonoidHom.comp_apply, e6n2_resSL_transvection_omega k l hkl, map_mul, map_mul,
      E6Pilot.slToAdjointE6_transvection, E6Pilot.slToAdjointE6_transvection,
      E6Pilot.slToAdjointE6_transvection]
  rfl

private theorem e6n2_rootSubgroup_map_phi :
    (SpecialLinear.rootSubgroup 2 F4 e6n2_h02).map
        ((E6Pilot.slToAdjointE6 F2).comp (resSL 3)) = rE := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup e6n2_h02 g).mp hg
    rcases f4_cases c with rfl | rfl | rfl | rfl
    · rw [Matrix.SpecialLinearGroup.transvection_coeff_zero e6n2_h02, map_one]
      exact rE.one_mem
    · rw [e6n2_Phi_transvection_one 0 2 e6n2_h02]
      exact Subgroup.subset_closure (Or.inl rfl)
    · rw [e6n2_Phi_transvection_omega 0 2 e6n2_h02]
      exact Subgroup.subset_closure (Or.inr rfl)
    · rw [e6n2_f4Omega_sq_add_one, Matrix.SpecialLinearGroup.transvection_add, map_mul,
        e6n2_Phi_transvection_omega 0 2 e6n2_h02, e6n2_Phi_transvection_one 0 2 e6n2_h02]
      exact rE.mul_mem (Subgroup.subset_closure (Or.inr rfl))
        (Subgroup.subset_closure (Or.inl rfl))
  · rw [rE, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [← e6n2_Phi_transvection_one 0 2 e6n2_h02]
      exact Subgroup.mem_map.mpr
        ⟨_, SpecialLinear.transvection_mem_rootSubgroup e6n2_h02 1, rfl⟩
    · rw [← e6n2_Phi_transvection_omega 0 2 e6n2_h02]
      exact Subgroup.mem_map.mpr
        ⟨_, SpecialLinear.transvection_mem_rootSubgroup e6n2_h02 f4Omega, rfl⟩

private theorem e6n2_noCentralAt_top_map_mulEquiv {U U' : Type} [Group U] [Group U']
    (e : U ≃* U') {R : Subgroup U} (h : GGRootNoCentralAt (⊤ : Subgroup U) R) :
    GGRootNoCentralAt (⊤ : Subgroup U') (R.map e.toMonoidHom) := by
  intro A B hRA hAB hB hNA hNB hc
  simp only [top_inf_eq] at hB hNA hNB hc
  refine ggRootNormNoCentral_map_mulEquiv e ?_ A B hRA hAB hB hNA hNB hc
  intro A' B' hRA' hAB' hB' hNA' hNB' hc'
  exact h A' B' hRA' hAB' (by simpa only [top_inf_eq] using hB')
    (by simpa only [top_inf_eq] using hNA') (by simpa only [top_inf_eq] using hNB')
    (by simpa only [top_inf_eq] using hc')

private theorem e6n2_isPGroup_rootSubgroup {F : Type} [Field F] [CharP F 2] {m : ℕ}
    {i j : Fin (m + 1)} (hij : i ≠ j) : IsPGroup 2 (SpecialLinear.rootSubgroup m F hij) := by
  rintro ⟨x, hx⟩
  obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij x).1 hx
  refine ⟨1, Subtype.ext ?_⟩
  change (Matrix.SpecialLinearGroup.transvection hij c) ^ 2 ^ 1 = 1
  rw [pow_one, pow_two, ← Matrix.SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

private theorem e6n2_noCentral_of_noCentralAt {G : Type} [Group G] {K R : Subgroup G}
    (hRK : R ≤ K) (h : GGRootNoCentralAt K R) :
    GGRootNormNoCentral (R.subgroupOf K) := by
  intro A B hRA hAB hBcore hNA hNB hcomm
  set N : Subgroup G := K ⊓ Subgroup.normalizer (R : Set G) with hNdef
  have hNK : Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) = N.subgroupOf K := by
    rw [hNdef, Subgroup.inf_subgroupOf_left]
    exact (Subgroup.subgroupOf_normalizer_eq hRK).symm
  have hcoreMap :
      (pCoreOf 2 (Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K))).map K.subtype =
        pCoreOf 2 N := by
    rw [hNK, GGRootNorm.pCoreOf_subgroupOf inf_le_left]
    exact Subgroup.map_subgroupOf_eq_of_le ((GGRootNorm.pCoreOf_le N).trans inf_le_left)
  have hnormMap : ∀ {S : Subgroup K},
      Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) ≤
        Subgroup.normalizer (S : Set K) →
      N ≤ Subgroup.normalizer ((S.map K.subtype : Subgroup G) : Set G) := by
    intro S hS
    rw [Subgroup.le_normalizer_iff]
    intro n hn x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    have hnK : (⟨n, hn.1⟩ : K) ∈
        Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K) := by
      rw [hNK]
      exact Subgroup.mem_subgroupOf.mpr hn
    have hs' : (⟨n, hn.1⟩ : K) * s * (⟨n, hn.1⟩ : K)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp (hS hnK) s).mp hs
    exact Subgroup.mem_map.mpr ⟨_, hs', by simp⟩
  have hcommMap : ⁅B.map K.subtype, N⁆ ≤ A.map K.subtype := by
    have h1 : (⁅B, Subgroup.normalizer ((R.subgroupOf K : Subgroup K) : Set K)⁆).map K.subtype ≤
        A.map K.subtype := Subgroup.map_mono hcomm
    rwa [Subgroup.map_commutator, hNK, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h1
  have key := h (A.map K.subtype) (B.map K.subtype)
    (by
      rw [← Subgroup.map_subgroupOf_eq_of_le hRK]
      exact Subgroup.map_mono hRA)
    (Subgroup.map_mono hAB) ((Subgroup.map_mono hBcore).trans (le_of_eq hcoreMap))
    (hnormMap hNA) (hnormMap hNB) hcommMap
  intro b hb
  exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp
    (key (Subgroup.mem_map_of_mem K.subtype hb))


theorem ggRootNormNoCentral_rE_jE :
    GGRootNormNoCentral (rE.subgroupOf jE) := by
  have hcard : 4 ≤ Nat.card F4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  let φ : Matrix.SpecialLinearGroup (Fin 3) F4 →* EC :=
    (E6Pilot.slToAdjointE6 F2).comp (resSL 3)
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact resSL_injective 3 (iota_injective hab)
  have hφker : φ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff φ).mpr hφinj
  have hNCtop : GGRootNoCentralAt
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F4))
      (SpecialLinear.rootSubgroup 2 F4 e6n2_h02) := by
    have hSL : GGRootNoCentralAt
        (⊤ : Subgroup (SpecialLinearGroup F4 (DSpace F4 F4))) (rootSL F4 F4 F4) :=
      LieKnownR2.SpecialLinearNC.ggRootNoCentralAt_top_rootSL (k := F4) (X := F4)
        (by simp [Module.finrank_self]) (Or.inl hcard)
    have h := e6n2_noCentralAt_top_map_mulEquiv e6n2_eD hSL
    rwa [e6n2_rootSL_map_eD] at h
  have hNC : GGRootNoCentralAt jE rE := by
    have hR2 : IsPGroup 2 (SpecialLinear.rootSubgroup 2 F4 e6n2_h02) :=
      e6n2_isPGroup_rootSubgroup e6n2_h02
    have h := LieKnownR2.SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker
      φ (by rw [hφker]; exact bot_le) (by rw [hφker]; simp) hR2 hNCtop
    rw [show φ.range = jE from ?_, e6n2_rootSubgroup_map_phi] at h
    exact h
    rw [show φ = (E6Pilot.slToAdjointE6 F2).comp (resSL 3) from rfl, MonoidHom.range_comp,
      show (resSL 3).range = sl3four from rfl]
    exact jE_eq.symm
  exact e6n2_noCentral_of_noCentralAt rE_le_jE hNC

theorem ggRootNormInner_rE_jE :
    GGRootNormInner (rE.subgroupOf jE) := by
  have hcard : 4 ≤ Nat.card F4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  let φ : Matrix.SpecialLinearGroup (Fin 3) F4 →* EC :=
    (E6Pilot.slToAdjointE6 F2).comp (resSL 3)
  have hφinj : Function.Injective φ := by
    intro a b hab
    exact resSL_injective 3 (iota_injective hab)
  let Φ : SpecialLinearGroup F4 (DSpace F4 F4) →* EC := φ.comp e6n2_eD.toMonoidHom
  have hΦinj : Function.Injective Φ := hφinj.comp e6n2_eD.injective
  have hK : (⊤ : Subgroup (SpecialLinearGroup F4 (DSpace F4 F4))).map Φ = jE := by
    rw [show Φ = φ.comp e6n2_eD.toMonoidHom from rfl]
    rw [Subgroup.map_top, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr e6n2_eD.surjective, Subgroup.map_top,
      show φ = (E6Pilot.slToAdjointE6 F2).comp (resSL 3) from rfl, MonoidHom.range_comp,
      show (resSL 3).range = sl3four from rfl]
    exact jE_eq.symm
  have hR : (rootSL F4 F4 F4).map Φ = rE := by
    rw [show Φ = φ.comp e6n2_eD.toMonoidHom from rfl, ← Subgroup.map_map,
      show (rootSL F4 F4 F4).map e6n2_eD.toMonoidHom =
        SpecialLinear.rootSubgroup 2 F4 e6n2_h02 from e6n2_rootSL_map_eD]
    exact e6n2_rootSubgroup_map_phi
  have hroot : GGRootNormInner ((rootSL F4 F4 F4).subgroupOf
      (⊤ : Subgroup (SpecialLinearGroup F4 (DSpace F4 F4)))) := by
    rw [← e6n2_top_symm_map (rootSL F4 F4 F4)]
    exact ggRootNormInner_map_mulEquiv
      (Subgroup.topEquiv (G := SpecialLinearGroup F4 (DSpace F4 F4))).symm
      (ggRootNormInner_rootSL_rankOne (k := F4) hcard)
  exact ggRootNormInner_of_map_injective Φ hΦinj hK hR hroot

end CFSG.StandardType.GGSixE6Two
