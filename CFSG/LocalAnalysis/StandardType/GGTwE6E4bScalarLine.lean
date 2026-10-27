module

public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bNormalizers
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bLift
public import CFSG.GroupTheory.IndexThreeCosets

public noncomputable section

namespace CFSG.StandardType.TwE6E4bScalarLine

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TwE6FixedA2SL3 CFSG.StandardType.TwE6FixedA2Type
open CFSG.StandardType.TableBExc.E6Three
open CFSG.StandardType.TwE6E4bFrame CFSG.StandardType.TwE6E4bFlag CFSG.StandardType.TwE6E4bTorus
open CFSG.StandardType.TwE6E4bNormalizers CFSG.StandardType.TwE6HyperplaneTypes
open CFSG.StandardType.E4bLift
open scoped MatrixGroups

local instance : NeZero Tag.E6.rank := ⟨by decide⟩

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem rootVec_mem_Vlong_of_mem_fixedA2E6 {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ fixedA2E6) :
    rootVec Tag.E6 L γ ∈ Vlong L := by
  rw [Vlong_eq_span_fixedA2E6]
  exact Submodule.subset_span ⟨γ, hγ, rfl⟩

theorem rootChar_diagTuple_gamma1_gen (s u : Lˣ) :
    rootChar (diagTuple s u) gamma1 = s ^ 2 * u⁻¹ := by
  rw [rootChar_gamma1, diagTuple_explicit]
  simp

theorem rootChar_diagTuple_gamma2_gen (s u : Lˣ) :
    rootChar (diagTuple s u) gamma2 = s⁻¹ * u ^ 2 := by
  rw [rootChar_gamma2]
  simp [diagTuple_explicit]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
    Units.val_pow_eq_pow_val]
  field_simp

theorem rootChar_diagTuple_gamma3_gen (s u : Lˣ) :
    rootChar (diagTuple s u) gamma3 = s * u := by
  rw [rootChar_gamma3]
  simp [diagTuple_explicit]
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
    Units.val_pow_eq_pow_val]
  field_simp

theorem fixedA2Scalar_frameOmega_pow (n : ℕ) :
    fixedA2Scalar (F := L) ((frameOmega (L := L)) ^ n) =
      (fixedA2Scalar (F := L) (frameOmega (L := L))) ^ n := by
  have hωn3 : ((frameOmega (L := L)) ^ n) ^ 3 = 1 := by
    rw [← pow_mul, show n * 3 = 3 * n by ring, pow_mul,
      frameOmega_pow_three, one_pow]
  rw [fixedA2Scalar_eq_scalarElement (F := L) hωn3,
    fixedA2Scalar_eq_scalarElement (F := L) (frameOmega_pow_three (L := L))]
  apply Subtype.ext
  change (Matrix.scalar (Fin 3) (((frameOmega (L := L)) ^ n : Lˣ) : L)) =
    ((Matrix.scalar (Fin 3) ((frameOmega (L := L) : Lˣ) : L)) ^ n)
  rw [← map_pow]
  exact congrArg (Matrix.scalar (Fin 3)) (Units.val_pow_eq_pow_val (frameOmega (L := L)) n)

theorem frameTorusTuple_frameExpA_eq_diagTuple :
    frameTorusTuple (L := L) frameExpA =
      diagTuple (frameOmega (L := L)) ((frameOmega (L := L)) ^ 2) := by
  exact rootDiagUnit_injective (by
    rw [← frameA_eq_rootDiagUnit, frameA_eq, frameRho0]
    change fixedA2Rho L (diagSL3 (frameOmega (L := L)) ((frameOmega (L := L)) ^ 2)) =
      rootDiagUnit Tag.E6 (diagTuple (frameOmega (L := L)) ((frameOmega (L := L)) ^ 2))
    rw [fixedA2Rho_diagSL3])

theorem frameA_mem_fixedA2Torus : frameA (L := L) ∈ fixedA2Torus L := by
  refine ⟨(frameOmega (L := L), (frameOmega (L := L)) ^ 2), ?_⟩
  rw [frameA_eq, frameRho0]
  change fixedA2Rho L (diagSL3 (frameOmega (L := L)) ((frameOmega (L := L)) ^ 2)) =
    fixedA2Rho L (frameScalar (L := L))
  rfl

theorem frameA_mem_VlongFixer : frameA (L := L) ∈ VlongFixer L := by
  rw [mem_VlongFixer_iff]
  intro v hv
  rw [Vlong_eq_span_fixedA2E6] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨γ, hγ, rfl⟩ := hx
      change (frameA (L := L) : Module.End L (RootModule .E6 L))
        (rootVec Tag.E6 L γ) = rootVec Tag.E6 L γ
      rw [frameA_eq_rootDiagUnit]
      change rootDiag (frameTorusTuple (L := L) frameExpA) (rootVec Tag.E6 L γ) =
        rootVec Tag.E6 L γ
      rw [rootDiag_rootVec _ (isRoot_of_mem_fixedA2E6 hγ)]
      have hchar : rootChar (frameTorusTuple (L := L) frameExpA) γ = 1 := by
        have hω : (frameOmega (L := L)) ^ 3 = 1 := frameOmega_pow_three (L := L)
        rw [Set.mem_setOf_eq] at hγ
        rw [frameTorusTuple_frameExpA_eq_diagTuple]
        rw [mem_fixedA2E6] at hγ
        rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [rootChar_diagTuple_gamma1_gen]
          simp
        · rw [rootChar_diagTuple_gamma2_gen]
          calc
            (frameOmega (L := L))⁻¹ * ((frameOmega (L := L)) ^ 2) ^ 2 =
                (frameOmega (L := L)) ^ 3 := by group
            _ = 1 := hω
        · rw [rootChar_diagTuple_gamma3_gen]
          calc
            frameOmega (L := L) * (frameOmega (L := L)) ^ 2 =
                (frameOmega (L := L)) ^ 3 := by group
            _ = 1 := hω
        · rw [rootChar_neg_eq_inv, rootChar_diagTuple_gamma1_gen]
          simp
        · rw [rootChar_neg_eq_inv, rootChar_diagTuple_gamma2_gen]
          have h : (frameOmega (L := L))⁻¹ * ((frameOmega (L := L)) ^ 2) ^ 2 =
              (frameOmega (L := L)) ^ 3 := by group
          rw [h, hω, inv_one]
        · rw [rootChar_neg_eq_inv, rootChar_diagTuple_gamma3_gen]
          have h : frameOmega (L := L) * (frameOmega (L := L)) ^ 2 =
              (frameOmega (L := L)) ^ 3 := by group
          rw [h, hω, inv_one]
      rw [hchar, Units.val_one, one_smul]
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add, ihx, ihy]
  | smul c x hx ih =>
      rw [map_smul, ih]

theorem frameX_mem_VlongFixer : frameX (L := L) ∈ VlongFixer L := by
  rw [mem_VlongFixer_iff]
  intro v hv
  rw [Vlong_eq_span_fixedA2E6] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨γ, hγ, rfl⟩ := hx
      change (frameX (L := L) : Module.End L (RootModule .E6 L))
        (rootVec Tag.E6 L γ) = rootVec Tag.E6 L γ
      rw [frameX_eq_rootDiagUnit]
      change rootDiag (frameTorusTuple (L := L) frameExpX) (rootVec Tag.E6 L γ) =
        rootVec Tag.E6 L γ
      rw [rootDiag_rootVec _ (isRoot_of_mem_fixedA2E6 hγ)]
      have hω : (frameOmega (L := L)) ^ 3 = 1 := frameOmega_pow_three (L := L)
      have hprod : (frameOmega (L := L)) * (frameOmega (L := L)) * (1 : Lˣ) *
          (frameOmega (L := L)) = 1 := by
        calc
          (frameOmega (L := L)) * (frameOmega (L := L)) * (1 : Lˣ) *
              (frameOmega (L := L)) =
              ((frameOmega (L := L)) * (frameOmega (L := L))) * (frameOmega (L := L)) := by
            group
          _ = (frameOmega (L := L)) ^ 3 := by rw [pow_three]; group
          _ = 1 := hω
      have hchar1 : rootChar (frameTorusTuple (L := L) frameExpX) gamma1 = 1 := by
        rw [rootChar_gamma1, frameTorusTuple_frameExpX_values.2.2.1]
      have hchar2 : rootChar (frameTorusTuple (L := L) frameExpX) gamma2 = 1 := by
        rw [rootChar_gamma2,
          frameTorusTuple_frameExpX_values.1,
          frameTorusTuple_frameExpX_values.2.1,
          frameTorusTuple_frameExpX_values.2.2.1,
          frameTorusTuple_frameExpX_values.2.2.2]
        exact hprod
      have hchar3 : rootChar (frameTorusTuple (L := L) frameExpX) gamma3 = 1 := by
        rw [rootChar_gamma3,
          frameTorusTuple_frameExpX_values.1,
          frameTorusTuple_frameExpX_values.2.1,
          frameTorusTuple_frameExpX_values.2.2.1,
          frameTorusTuple_frameExpX_values.2.2.2]
        simpa [one_pow] using hprod
      have hchar : rootChar (frameTorusTuple (L := L) frameExpX) γ = 1 := by
        rw [Set.mem_setOf_eq] at hγ
        rw [mem_fixedA2E6] at hγ
        rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hchar1
        · exact hchar2
        · exact hchar3
        · rw [rootChar_neg_eq_inv, hchar1, inv_one]
        · rw [rootChar_neg_eq_inv, hchar2, inv_one]
        · rw [rootChar_neg_eq_inv, hchar3, inv_one]
      rw [hchar, Units.val_one, one_smul]
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add, ihx, ihy]
  | smul c x hx ih =>
      rw [map_smul, ih]

theorem frame_actualW0_card
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup Tag.E6 L)
    (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4)
    (hWeyl : ∀ e (he : e ∈ E),
      weylQuotientHom Tag.E6 L ⟨e, hEM he⟩ ∈ Subgroup.zpowers cE6)
    {n1 : ModGL .E6 L} (hn1E : n1 ∈ E)
    (hn1c : weylQuotientHom Tag.E6 L ⟨n1, hEM hn1E⟩ = cE6) :
    Nat.card ↥(Subgroup.zpowers (frameA (L := L)) ⊔
      Subgroup.zpowers (frameX (L := L)) ⊔ Subgroup.zpowers n1) = 27 := by
  have hD : E ⊓ torusGroup Tag.E6 L = frameD (L := L) :=
    frame_actualE_torus_eq_frameD hEM hE hcard hWeyl hn1E hn1c
  have haD : frameA (L := L) ∈ frameD (L := L) := by
    rw [← frameCToralSubgroup_eq_frameD]
    exact frameA_mem_frameCToralSet (L := L)
  have hxD : frameX (L := L) ∈ frameD (L := L) := by
    rw [← frameCToralSubgroup_eq_frameD]
    exact frameX_mem_frameCToralSet (L := L)
  have haE : frameA (L := L) ∈ E := by
    have hmem : frameA (L := L) ∈ E ⊓ torusGroup Tag.E6 L := by
      rw [hD]
      exact haD
    exact (Subgroup.mem_inf.mp hmem).1
  have hxE : frameX (L := L) ∈ E := by
    have hmem : frameX (L := L) ∈ E ⊓ torusGroup Tag.E6 L := by
      rw [hD]
      exact hxD
    exact (Subgroup.mem_inf.mp hmem).1
  have hn1T : n1 ∉ torusGroup Tag.E6 L := by
    intro hn1T
    have h1 : weylQuotientHom Tag.E6 L ⟨n1, hEM hn1E⟩ = 1 :=
      weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hn1T)
    rw [hn1c] at h1
    exact cE6_ne_one h1
  have hsupT : Subgroup.zpowers (frameA (L := L)) ⊔
      Subgroup.zpowers (frameX (L := L)) ≤ torusGroup Tag.E6 L :=
    sup_le (Subgroup.zpowers_le.mpr (frameA_mem_torus (L := L)))
      (Subgroup.zpowers_le.mpr (frameX_mem_torus (L := L)))
  have hn1_sup : n1 ∉ Subgroup.zpowers (frameA (L := L)) ⊔
      Subgroup.zpowers (frameX (L := L)) := by
    intro h
    exact hn1T (hsupT h)
  have hx_not_a : frameX (L := L) ∉ Subgroup.zpowers (frameA (L := L)) := by
    intro h
    exact frameX_not_mem_sup_frameA_frameT (L := L) (Subgroup.mem_sup_left h)
  obtain ⟨_, hW0card⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.exists_isElemAbelian_card_three_of_independent
      (x := frameA (L := L)) (y := frameX (L := L)) (z := n1)
      (frameA_mul_frameX (L := L))
      (CFSG.Open.IsElemAbelian.comm hE haE hn1E)
      (CFSG.Open.IsElemAbelian.comm hE hxE hn1E)
      (frameA_pow_three (L := L))
      (frameX_pow_three (L := L))
      (hE.2 n1 hn1E)
      (frameA_ne_one (L := L))
      hx_not_a
      hn1_sup
  simpa using hW0card

theorem frame_actualW0_le_Wlong
    {E : Subgroup (ModGL .E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup Tag.E6 L)
    (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4)
    (hWeyl : ∀ e (he : e ∈ E),
      weylQuotientHom Tag.E6 L ⟨e, hEM he⟩ ∈ Subgroup.zpowers cE6)
    {n1 : ModGL .E6 L} (hn1E : n1 ∈ E)
    (hn1c : weylQuotientHom Tag.E6 L ⟨n1, hEM hn1E⟩ = cE6)
    (hn1F : n1 ∈ VlongFixer L) :
    (Subgroup.zpowers (frameA (L := L)) ⊔
      Subgroup.zpowers (frameX (L := L)) ⊔ Subgroup.zpowers n1) ≤ Wlong L E := by
  have hD : E ⊓ torusGroup Tag.E6 L = frameD (L := L) :=
    frame_actualE_torus_eq_frameD hEM hE hcard hWeyl hn1E hn1c
  have haD : frameA (L := L) ∈ frameD (L := L) := by
    rw [← frameCToralSubgroup_eq_frameD]
    exact frameA_mem_frameCToralSet (L := L)
  have hxD : frameX (L := L) ∈ frameD (L := L) := by
    rw [← frameCToralSubgroup_eq_frameD]
    exact frameX_mem_frameCToralSet (L := L)
  have haE : frameA (L := L) ∈ E := by
    have hmem : frameA (L := L) ∈ E ⊓ torusGroup Tag.E6 L := by
      rw [hD]
      exact haD
    exact (Subgroup.mem_inf.mp hmem).1
  have hxE : frameX (L := L) ∈ E := by
    have hmem : frameX (L := L) ∈ E ⊓ torusGroup Tag.E6 L := by
      rw [hD]
      exact hxD
    exact (Subgroup.mem_inf.mp hmem).1
  have hW0E : Subgroup.zpowers (frameA (L := L)) ⊔
      Subgroup.zpowers (frameX (L := L)) ⊔ Subgroup.zpowers n1 ≤ E :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr haE) (Subgroup.zpowers_le.mpr hxE))
      (Subgroup.zpowers_le.mpr hn1E)
  have hW0F : Subgroup.zpowers (frameA (L := L)) ⊔
      Subgroup.zpowers (frameX (L := L)) ⊔ Subgroup.zpowers n1 ≤ VlongFixer L :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr (frameA_mem_VlongFixer (L := L)))
      (Subgroup.zpowers_le.mpr (frameX_mem_VlongFixer (L := L))))
      (Subgroup.zpowers_le.mpr hn1F)
  simpa [Wlong] using le_inf hW0E hW0F

theorem frameA_sq_eq_fixedA2Scalar_frameOmega_sq :
    frameA (L := L) ^ 2 =
      fixedA2Rho L (fixedA2Scalar (F := L) ((frameOmega (L := L)) ^ 2)) := by
  calc
    frameA (L := L) ^ 2 = (fixedA2Rho L (frameScalar (L := L))) ^ 2 := by
      rw [frameA_eq, frameRho0]
    _ = fixedA2Rho L ((frameScalar (L := L)) ^ 2) := by rw [map_pow]
    _ = fixedA2Rho L (fixedA2Scalar (F := L) ((frameOmega (L := L)) ^ 2)) := by
      rw [fixedA2Scalar_frameOmega_pow]
      simp only [frameScalar, fixedA2Scalar]

theorem frameA_sq_mem_fixedA2Torus : frameA (L := L) ^ 2 ∈ fixedA2Torus L := by
  refine ⟨((frameOmega (L := L)) ^ 2, ((frameOmega (L := L)) ^ 2) ^ 2), ?_⟩
  rw [frameA_sq_eq_fixedA2Scalar_frameOmega_sq, fixedA2Scalar_eq_diagSL3]

theorem frameA_inv_eq_sq : (frameA (L := L))⁻¹ = frameA (L := L) ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', show 2 + 1 = 3 by norm_num, frameA_pow_three]

theorem fixedA2Torus_inter_VlongFixer_eq_zpowers_frameA :
    (fixedA2Torus L ∩ (VlongFixer L : Set (ModGL .E6 L))) =
      (Subgroup.zpowers (frameA (L := L)) : Set (ModGL .E6 L)) := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_inter_iff] at hz
    obtain ⟨hzS, hzF⟩ := hz
    obtain ⟨⟨s, u⟩, rfl⟩ := hzS
    change fixedA2Rho L (diagSL3 s u) ∈ Subgroup.zpowers (frameA (L := L))
    change fixedA2Rho L (diagSL3 s u) ∈ VlongFixer L at hzF
    rw [fixedA2Rho_diagSL3, mem_VlongFixer_iff] at hzF
    have hχ1 : rootChar (diagTuple s u) gamma1 = 1 := by
      have hfix := hzF (rootVec Tag.E6 L gamma1)
        (rootVec_mem_Vlong_of_mem_fixedA2E6 (mem_fixedA2E6.mpr (Or.inl rfl)))
      change rootDiag (diagTuple s u) (rootVec Tag.E6 L gamma1) =
        rootVec Tag.E6 L gamma1 at hfix
      rw [rootDiag_rootVec _ isRoot_gamma1] at hfix
      have hval : ((rootChar (diagTuple s u) gamma1 : Lˣ) : L) = 1 :=
        eq_of_smul_rootVec_eq_smul isRoot_gamma1 (by simpa using hfix)
      exact Units.ext (by simpa using hval)
    have hχ2 : rootChar (diagTuple s u) gamma2 = 1 := by
      have hfix := hzF (rootVec Tag.E6 L gamma2)
        (rootVec_mem_Vlong_of_mem_fixedA2E6 (mem_fixedA2E6.mpr (Or.inr (Or.inl rfl))))
      change rootDiag (diagTuple s u) (rootVec Tag.E6 L gamma2) =
        rootVec Tag.E6 L gamma2 at hfix
      rw [rootDiag_rootVec _ isRoot_gamma2] at hfix
      have hval : ((rootChar (diagTuple s u) gamma2 : Lˣ) : L) = 1 :=
        eq_of_smul_rootVec_eq_smul isRoot_gamma2 (by simpa using hfix)
      exact Units.ext (by simpa using hval)
    have h1 : s ^ 2 * u⁻¹ = 1 :=
      (rootChar_diagTuple_gamma1_gen s u).symm.trans hχ1
    have h2 : s⁻¹ * u ^ 2 = 1 :=
      (rootChar_diagTuple_gamma2_gen s u).symm.trans hχ2
    have hu : u = s ^ 2 := (eq_of_mul_inv_eq_one h1).symm
    have hs3 : s ^ 3 = 1 := by
      rw [hu] at h2
      have h : s⁻¹ * (s ^ 2) ^ 2 = s ^ 3 := by group
      rwa [h] at h2
    obtain ⟨i, hi⟩ := exists_fin3_eq_frameOmega_zpow (L := L) s hs3
    have hscalar : fixedA2Scalar (F := L) s =
        (fixedA2Scalar (F := L) (frameOmega (L := L))) ^ (i : ℕ) := by
      rw [hi]
      exact fixedA2Scalar_frameOmega_pow (i : ℕ)
    have hzpownat : fixedA2Rho L (diagSL3 s u) = frameA (L := L) ^ (i : ℕ) := by
      calc
        fixedA2Rho L (diagSL3 s u) = fixedA2Rho L (fixedA2Scalar (F := L) s) := by
          rw [hu]
          rfl
        _ = (fixedA2Rho L (fixedA2Scalar (F := L) (frameOmega (L := L)))) ^ (i : ℕ) := by
          rw [hscalar, map_pow]
        _ = frameA (L := L) ^ (i : ℕ) := by
          congr 1
          rw [frameA_eq, frameRho0]
          rfl
    refine Subgroup.mem_zpowers_iff.mpr ⟨(i : ℤ), ?_⟩
    simpa only [zpow_natCast] using hzpownat.symm
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← hk]
    by_cases h1 : frameA (L := L) ^ k = 1
    · rw [h1]
      refine ⟨?_, Subgroup.one_mem _⟩
      refine ⟨(1, 1), ?_⟩
      have hdiag : diagSL3 (1 : Lˣ) (1 : Lˣ) = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [diagSL3]
      change fixedA2Rho L (diagSL3 (1 : Lˣ) (1 : Lˣ)) = 1
      rw [hdiag, map_one]
    · have hmem : frameA (L := L) ^ k ∈ Subgroup.zpowers (frameA (L := L)) :=
        Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      have horder : orderOf (frameA (L := L)) = 3 :=
        orderOf_eq_prime (frameA_pow_three (L := L)) (frameA_ne_one (L := L))
      rcases CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
        horder hmem h1 with h | h
      · rw [h]
        exact ⟨frameA_mem_fixedA2Torus, frameA_mem_VlongFixer⟩
      · rw [h, frameA_inv_eq_sq]
        exact ⟨frameA_sq_mem_fixedA2Torus, pow_mem frameA_mem_VlongFixer 2⟩

theorem normalizer_fixedA2Torus_normalizes_VlongFixer
    (R : ModGL .E6 L) (hRS : R ∈ Subgroup.normalizer (fixedA2Torus L)) :
    R ∈ Subgroup.normalizer (VlongFixer L) := by
  have hRTop : R ∈ Subgroup.normalizer
      ((⊤ : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp
  have hRW : R ∈ Subgroup.normalizer
      (Wlong L (⊤ : Subgroup (ModGL .E6 L)) : Set (ModGL .E6 L)) :=
    normalizer_Wlong (E := (⊤ : Subgroup (ModGL .E6 L))) (R := R) hRTop hRS
  have hWtop : Wlong L (⊤ : Subgroup (ModGL .E6 L)) = VlongFixer L := by
    simp [Wlong]
  simpa [hWtop] using hRW

theorem normalizer_fixedA2Torus_normalizes_zpowers_frameA
    (R : ModGL .E6 L) (hRS : R ∈ Subgroup.normalizer (fixedA2Torus L)) :
    R ∈ Subgroup.normalizer (Subgroup.zpowers (frameA (L := L))) := by
  have hRF : R ∈ Subgroup.normalizer (VlongFixer L) :=
    normalizer_fixedA2Torus_normalizes_VlongFixer R hRS
  rw [← fixedA2Torus_inter_VlongFixer_eq_zpowers_frameA]
  refine Subgroup.mem_set_normalizer_iff.mpr fun x => ?_
  constructor
  · intro hx
    rw [Set.mem_inter_iff] at hx ⊢
    exact ⟨(Subgroup.mem_set_normalizer_iff.mp hRS x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp hRF x).mp hx.2⟩
  · intro hx
    rw [Set.mem_inter_iff] at hx ⊢
    exact ⟨(Subgroup.mem_set_normalizer_iff.mp hRS x).mpr hx.1,
      (Subgroup.mem_normalizer_iff.mp hRF x).mpr hx.2⟩

theorem normalizer_fixedA2Torus_conj_frameA_eq_or_eq_inv
    (R : ModGL .E6 L) (hRS : R ∈ Subgroup.normalizer (fixedA2Torus L)) :
    R * frameA (L := L) * R⁻¹ = frameA (L := L) ∨
      R * frameA (L := L) * R⁻¹ = (frameA (L := L))⁻¹ := by
  have hRZ := normalizer_fixedA2Torus_normalizes_zpowers_frameA R hRS
  have hmem : R * frameA (L := L) * R⁻¹ ∈ Subgroup.zpowers (frameA (L := L)) :=
    (Subgroup.mem_normalizer_iff.mp hRZ (frameA (L := L))).mp
      (Subgroup.mem_zpowers (frameA (L := L)))
  have hne : R * frameA (L := L) * R⁻¹ ≠ 1 := by
    intro h
    apply frameA_ne_one (L := L)
    have := congrArg (fun x => R⁻¹ * x * R) h
    simpa [mul_assoc] using this
  have horder : orderOf (frameA (L := L)) = 3 :=
    orderOf_eq_prime (frameA_pow_three (L := L)) (frameA_ne_one (L := L))
  exact CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
    horder hmem hne

theorem normalizer_involution_fixes_Wlong
    {E : Subgroup (ModGL .E6 L)} {R : ModGL .E6 L}
    (hE : CFSG.Open.IsElemAbelian 3 E)
    (hRE : R ∈ Subgroup.normalizer (E : Set (ModGL .E6 L)))
    (hRS : R ∈ Subgroup.normalizer (fixedA2Torus L))
    (hquot : ∀ e ∈ E, R * e * R⁻¹ * e⁻¹ ∈ fixedA2Torus L)
    (hR2 : ∀ e ∈ E, R * (R * e * R⁻¹) * R⁻¹ = e)
    (hRa : R * frameA (L := L) * R⁻¹ = frameA (L := L)) :
    ∀ w ∈ Wlong L E, R * w * R⁻¹ = w := by
  intro w hw
  rw [Wlong, Subgroup.mem_inf] at hw
  obtain ⟨hwE, hwF⟩ := hw
  let u : ModGL .E6 L := R * w * R⁻¹
  have huE : u ∈ E := (Subgroup.mem_normalizer_iff.mp hRE w).mp hwE
  have huR : R * u * R⁻¹ = w := hR2 w hwE
  have huInvR : R * u⁻¹ * R⁻¹ = w⁻¹ := by
    calc
      R * u⁻¹ * R⁻¹ = (R * u * R⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [huR]
  let δ : ModGL .E6 L := u * w⁻¹
  have hδS : δ ∈ fixedA2Torus L := by
    simpa [δ, u] using hquot w hwE
  have hRV : R ∈ Subgroup.normalizer (VlongFixer L) :=
    normalizer_fixedA2Torus_normalizes_VlongFixer R hRS
  have huF : u ∈ VlongFixer L :=
    (Subgroup.mem_normalizer_iff.mp hRV w).mp hwF
  have hδF : δ ∈ VlongFixer L :=
    Subgroup.mul_mem _ huF (Subgroup.inv_mem _ hwF)
  have hδZset : δ ∈ (Subgroup.zpowers (frameA (L := L)) : Set (ModGL .E6 L)) := by
    rw [← fixedA2Torus_inter_VlongFixer_eq_zpowers_frameA]
    exact ⟨hδS, hδF⟩
  have hδZ : δ ∈ Subgroup.zpowers (frameA (L := L)) := hδZset
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hδZ
  have hconjA : (MulAut.conj R) (frameA (L := L)) = frameA (L := L) := by
    simpa [MulAut.conj_apply] using hRa
  have hRδ : R * δ * R⁻¹ = δ := by
    rw [← hk]
    change (MulAut.conj R) (frameA (L := L) ^ k) = frameA (L := L) ^ k
    rw [map_zpow, hconjA]
  have hRδ_inv : R * δ * R⁻¹ = δ⁻¹ := by
    calc
      R * δ * R⁻¹ = (R * u * R⁻¹) * (R * w⁻¹ * R⁻¹) := by
        simp only [δ]
        group
      _ = w * (R * w * R⁻¹)⁻¹ := by
        rw [huR]
        have h : R * w⁻¹ * R⁻¹ = (R * w * R⁻¹)⁻¹ := by group
        rw [h]
      _ = w * u⁻¹ := rfl
      _ = δ⁻¹ := by
        simp only [δ]
        group
  have hδ2 : δ ^ 2 = 1 := by
    have h : δ = δ⁻¹ := by
      calc
        δ = R * δ * R⁻¹ := hRδ.symm
        _ = δ⁻¹ := hRδ_inv
    calc
      δ ^ 2 = δ * δ := by rw [pow_two]
      _ = δ * δ⁻¹ := by
        congr 1
      _ = 1 := mul_inv_cancel δ
  have hδ3 : δ ^ 3 = 1 := by
    have hcomm : Commute u w⁻¹ :=
      CFSG.Open.IsElemAbelian.comm hE huE (Subgroup.inv_mem E hwE)
    rw [show δ = u * w⁻¹ by rfl, hcomm.mul_pow 3]
    rw [hE.2 u huE, inv_pow, hE.2 w hwE, inv_one, mul_one]
  have hδ1 : δ = 1 := by
    have h : δ = δ ^ 3 * (δ ^ 2)⁻¹ := by group
    rwa [hδ3, hδ2, inv_one, mul_one] at h
  have huw : u * w⁻¹ = 1 := by simpa [δ] using hδ1
  have huwEq : u = w := mul_inv_eq_one.mp huw
  simpa [u] using huwEq

end CFSG.StandardType.TwE6E4bScalarLine
