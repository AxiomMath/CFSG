module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagBase
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoCard
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRootSubGeo

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

private lemma rckRPb1_neg_one_matrix_eq_one {ι F : Type} [DecidableEq ι] [Field F]
    [CharP F 2] : (-1 : Matrix ι ι F) = 1 := by
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

private lemma rckRPb1_J_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, zero_add,
    add_zero, Matrix.mul_neg, neg_zero]
  rw [rckRPb1_neg_one_matrix_eq_one, Matrix.fromBlocks_one]

private lemma rckRPb1_J_transpose {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, rckRPb1_neg_one_matrix_eq_one]

private lemma rckRPb1_J_alt {n f : ℕ} (x : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec x = 0 := by
  simp only [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]
  simp [Matrix.neg_mulVec, mul_comm]

private lemma rckRPb1_J_mulVec_ne_zero {n f : ℕ}
    {v : (Fin n ⊕ Fin n) → GaloisField 2 f} (hv : v ≠ 0) :
    (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v ≠ 0 := by
  intro h
  have hJJ : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      Matrix.fromBlocks 0 1 (-1) 0 = 1 :=
    rckRPb1_J_mul_self (n := n) (F := GaloisField 2 f)
  have h' := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) =>
    M.mulVec v) hJJ
  rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, Matrix.one_mulVec] at h'
  exact hv h'.symm

private lemma rckRPb1_J_det_ne_zero (n f : ℕ) :
    (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).det ≠ 0 :=
  isUnit_iff_ne_zero.mp
    (Matrix.isUnit_det_of_right_inverse
      (rckRPb1_J_mul_self (n := n) (F := GaloisField 2 f)))

private lemma rckRPb1_one_toMonoidHom {K : Type} [Group K] :
    ((1 : K ≃* K) : K →* K) = MonoidHom.id K := rfl

private lemma rckRPb1_glGeoFlag_matTransv {n f : ℕ}
    {v : (Fin n ⊕ Fin n) → GaloisField 2 f} (hv : v ≠ 0) :
    GLGeoFlag (spForm n (GaloisField 2 f))
      (matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v)) := by
  have hφ : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v ≠ 0 :=
    rckRPb1_J_mulVec_ne_zero hv
  have hvφ : ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v) ⬝ᵥ v = 0 := by
    rw [dotProduct_comm]
    exact rckRPb1_J_alt v
  exact glGeoFlag_matTransvGroup (spForm n (GaloisField 2 f)) hv hφ hvφ

private lemma rckRPb1_glGeoFlag_altSiegel {n f : ℕ}
    {a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (horth : a₁ ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec a₂ = 0) :
    GLGeoFlag (spForm n (GaloisField 2 f))
      (altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) := by
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).det :=
    isUnit_iff_ne_zero.mpr (rckRPb1_J_det_ne_zero n f)
  have hsymm : Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      Matrix.fromBlocks 0 1 (-1) 0 := rckRPb1_J_transpose
  have halt : ∀ x : (Fin n ⊕ Fin n) → GaloisField 2 f,
      x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec x = 0 :=
    rckRPb1_J_alt
  simpa [spForm] using glGeoFlag_altSiegelGroup hG hsymm halt hli horth

private lemma rckRPb1_two_le_of_card {f : ℕ} (hf : 1 ≤ f)
    (h4 : 4 ≤ Nat.card (GaloisField 2 f)) : 2 ≤ f := by
  have hc := GaloisField.card 2 f (Nat.one_le_iff_ne_zero.mp hf)
  have hpow : 4 ≤ 2 ^ f := by omega
  have hpow' : 2 ^ 2 ≤ 2 ^ f := by omega
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow'

private lemma rckRPb1_admissible_PSp {r f : ℕ} (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hfr : 4 ≤ Nat.card (GaloisField 2 f) ∨ 3 ≤ r) :
    CFSG.Open.StatedLieAdmissible .PSp r 2 f := by
  refine ⟨Nat.prime_two, hf, hr, ?_⟩
  intro h
  have h2 : 2 ^ f = 2 := congrArg Prod.snd h
  rcases hfr with h4 | h3
  · have hc := GaloisField.card 2 f (Nat.one_le_iff_ne_zero.mp hf)
    omega
  · have hr2 : r = 2 := congrArg Prod.fst h
    omega

private lemma rckRPb1_admissible_PSL {f : ℕ} (hf : 1 ≤ f)
    (h4 : 4 ≤ Nat.card (GaloisField 2 f)) :
    CFSG.Open.StatedLieAdmissible .PSL 2 2 f := by
  have hc := GaloisField.card 2 f (Nat.one_le_iff_ne_zero.mp hf)
  refine ⟨Nat.prime_two, hf, le_rfl, ?_, ?_⟩
  · intro h
    have h2 : 2 ^ f = 2 := congrArg Prod.snd h
    omega
  · intro h
    have h2 : 2 ^ f = 3 := congrArg Prod.snd h
    omega


private def rckRPb1_SpRootData
    {n f r : ℕ}
    (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) : Prop :=
  ∀ (β : Fin (ggU .PSp r f).D.rank → ℤ) (u : (ggU .PSp r f).K),
    β ∈ (ggU .PSp r f).D.roots →
      (GGLongRoot (ggU .PSp r f).D β →
        ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
          Subgroup.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
            (Subgroup.map ι (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u))
              ((ggU .PSp r f).D.rootGroup β))) =
            matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v)) ∧
      (¬ GGLongRoot (ggU .PSp r f).D β →
        ∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f,
          a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
            a₁ ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec a₂ = 0 ∧
            Subgroup.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
              (Subgroup.map ι (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj u))
                ((ggU .PSp r f).D.rootGroup β))) =
              altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
                Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)

private theorem rckRPb1_PSp_case_ge_two
    {n f r : ℕ} (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hfr : 4 ≤ Nat.card (GaloisField 2 f) ∨ 3 ≤ r)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSp r f).K)
    (hrange : ι.range = J') (hroot : rckRPb1_SpRootData ι) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  have hnorm : RCKNormalizedModel .PSp r f :=
    ⟨by simp [GGPosTag], rckRPb1_admissible_PSp hf hr hfr⟩
  have hflags : RCKRPRootFlags (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) ι := by
    intro β hβ _hclause u
    by_cases hlong : GGLongRoot (ggU .PSp r f).D β
    · obtain ⟨v, hv, hX⟩ := (hroot β u hβ).1 hlong
      have hX' : (ggRootSub (ggU .PSp r f).D ι β u).map
          (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v) := by
        simpa [ggRootSub] using hX
      rw [hX']
      exact rckRPb1_glGeoFlag_matTransv hv
    · obtain ⟨a₁, a₂, _ha₁, _ha₂, hli, horth, hX⟩ := (hroot β u hβ).2 hlong
      have hX' : (ggRootSub (ggU .PSp r f).D ι β u).map
          (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ := by
        simpa [ggRootSub] using hX
      rw [hX']
      exact rckRPb1_glGeoFlag_altSiegel hli horth
  exact ⟨.PSp, r, f, ι, hnorm, hrange, hcent, hflags⟩

private lemma rckRPb1_PSp_one_P0
    {n f : ℕ} (hf : 1 ≤ f)
    {ι : (ggU .PSp 1 f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hroot : rckRPb1_SpRootData ι) :
    ∃ P₀ : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      P₀ ≤ ι.range ∧ Nat.card P₀ = 2 ^ f ∧
        GLGeoFlag (spForm n (GaloisField 2 f))
          (Subgroup.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype P₀) := by
  have hrank1 : (ggU .PSp 1 f).D.rank = 1 := rfl
  obtain ⟨β₀, hβ₀, hmax₀⟩ :=
    CFSG.StandardType.exists_maxHeight (D := (ggU .PSp 1 f).D) (by rw [hrank1]; omega)
  have hlong₀ : GGLongRoot (ggU .PSp 1 f).D β₀ :=
    ⟨1, β₀, hβ₀, hmax₀, by rw [map_one, Module.End.one_apply]⟩
  obtain ⟨v, hv, hX₀⟩ := (hroot β₀ 1 hβ₀).1 hlong₀
  let P₀ : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) :=
    Subgroup.map ι ((ggU .PSp 1 f).D.rootGroup β₀)
  have hX₀' : Subgroup.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype P₀ =
      matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v) := by
    simpa [P₀, rckRPb1_one_toMonoidHom, Subgroup.map_id] using hX₀
  refine ⟨P₀, Subgroup.map_le_range ι _, ?_, ?_⟩
  · have hφ : (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v ≠ 0 :=
      rckRPb1_J_mulVec_ne_zero hv
    have hvφ : ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v) ⬝ᵥ v = 0 := by
      rw [dotProduct_comm]
      exact rckRPb1_J_alt v
    have hmap : Nat.card (Subgroup.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype P₀) =
        Nat.card P₀ :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [← hmap, hX₀', card_matTransvGroup hv hφ hvφ,
      GaloisField.card 2 f (Nat.one_le_iff_ne_zero.mp hf)]
  · rw [hX₀']
    exact rckRPb1_glGeoFlag_matTransv hv

private lemma rckRPb1_spForm_isometry_subtype (n f : ℕ) :
    ∀ y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      ∀ b ∈ spForm n (GaloisField 2 f), ∀ m m' : (Fin n ⊕ Fin n) → GaloisField 2 f,
        b (((y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec m)
          (((y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec m') = b m m' := by
  intro y
  exact spForm_isometry n (GaloisField 2 f) (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) y.2

private theorem rckRPb1_PSp_case_one
    {n f : ℕ} (hf : 1 ≤ f)
    (h4 : 4 ≤ Nat.card (GaloisField 2 f))
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (ι : (ggU .PSp 1 f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSp 1 f).K)
    (hrange : ι.range = J') (hroot : rckRPb1_SpRootData ι) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  have hf2 : 2 ≤ f := rckRPb1_two_le_of_card hf h4
  obtain ⟨e⟩ := rckRP_nonempty_mulEquiv_PSL_two_PSp_one (f := f) hf
  let κ : (ggU .PSL 2 f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) :=
    ι.comp (e : (ggU .PSL 2 f).K →* (ggU .PSp 1 f).K)
  have hcentκ : ∀ y, κ y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSL 2 f).K := by
    intro y hy
    have hy' : ι (e y) ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) := by
      simpa [κ] using hy
    exact (MulEquivClass.apply_mem_center_iff e).mp (hcent (e y) hy')
  have hrangeκ : κ.range = J' := by
    dsimp [κ]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
      hrange]
  have hnorm : RCKNormalizedModel .PSL 2 f :=
    ⟨by simp [GGPosTag], rckRPb1_admissible_PSL hf h4⟩
  obtain ⟨P₀, hP₀le, hcardP₀, hflagP₀⟩ := rckRPb1_PSp_one_P0 hf hroot
  have hP₀leκ : P₀ ≤ κ.range := by
    rw [hrangeκ, ← hrange]
    exact hP₀le
  have hflags : RCKRPRootFlags (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) κ := by
    refine rckRP_rootFlags_PSL_two (j := (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)
      (B := spForm n (GaloisField 2 f))
      (hiso := rckRPb1_spForm_isometry_subtype n f) (hf := hf2) (κ := κ)
      (P₀ := P₀) ?_ ?_ ?_ ?_
    · intro y hy
      have hy1 : κ y = 1 := hy
      exact hcentκ y (by rw [hy1]; exact Subgroup.one_mem _)
    · exact hP₀leκ
    · exact hcardP₀
    · exact hflagP₀
  exact ⟨.PSL, 2, f, κ, hnorm, hrangeκ, hcentκ, hflags⟩

theorem rckRP_flaggedModel_PSp_selfDual
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  obtain ⟨r, ι, _hrank, hr1, hfr, _hinj, hcent, hrange, hroot⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_blockModel_selfDual_PSp_explicitFwd
      n f S hS he hadj hdeg hJe hA6
  rcases eq_or_lt_of_le hr1 with hr | hr
  ·
    subst r
    have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      rcases hfr with h4 | h3
      · exact h4
      · omega
    exact rckRPb1_PSp_case_one hf h4 ι hcent hrange hroot
  ·
    exact rckRPb1_PSp_case_ge_two hf hr hfr ι hcent hrange hroot

private theorem rckRPb1m_case_f_one
    {n r : ℕ}
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 1))}
    (ι : (ggU .PSp r 1).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 1)))
    (hr3 : 3 ≤ r)
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 1)) →
      y ∈ Subgroup.center (ggU .PSp r 1).K)
    (hrange : ι.range = J') (hroot : rckRPb1_SpRootData ι) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n 1)) J' := by
  have hnorm : RCKNormalizedModel .PSp r 1 :=
    ⟨by simp [GGPosTag], rckRPb1_admissible_PSp le_rfl (by omega) (Or.inr hr3)⟩
  refine ⟨.PSp, r, 1, ι, hnorm, hrange, hcent, ?_⟩
  intro β hβ hclause u
  have hnot : ¬ (((.PSp : CFSG.Open.StatedLieTag) = .PSp ∧ r = 2) ∨
      (.PSp : CFSG.Open.StatedLieTag) = .F4) := by
    rintro (⟨-, h2⟩ | hF)
    · omega
    · cases hF
  have hlong : GGLongRoot (ggU .PSp r 1).D β := by
    rcases hclause with h | ⟨hshort, -⟩
    · exact h
    · exact absurd hshort hnot
  obtain ⟨v, hv, hX⟩ := (hroot β u hβ).1 hlong
  have hR : (ggRootSub (ggU .PSp r 1).D ι β u).map
      (CFSG.Open.StatedSp n (GaloisField 2 1)).subtype =
      matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)) v) := by
    rw [ggRootSub]
    exact hX
  exact Or.inl (rckRPRootSubOf_PSp_of_matTransv hv hR)

private theorem rckRPb1m_case_one
    {n f : ℕ} (hf : 1 ≤ f) (h4 : 4 ≤ Nat.card (GaloisField 2 f))
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (ι : (ggU .PSp 1 f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSp 1 f).K)
    (hrange : ι.range = J') (hroot : rckRPb1_SpRootData ι) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n f)) J' := by
  obtain ⟨e⟩ := rckRP_nonempty_mulEquiv_PSL_two_PSp_one (f := f) hf
  let κ : (ggU .PSL 2 f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) :=
    ι.comp (e : (ggU .PSL 2 f).K →* (ggU .PSp 1 f).K)
  have hcentκ : ∀ y, κ y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSL 2 f).K := by
    intro y hy
    have hy' : ι (e y) ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) := by
      simpa [κ] using hy
    exact (MulEquivClass.apply_mem_center_iff e).mp (hcent (e y) hy')
  have hrangeκ : κ.range = J' := by
    dsimp [κ]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top,
      hrange]
  exact rckRP_modelII_of_big _ (rckRP_modelBig_of_PSL (k := 1) (rckRPb1_two_le_of_card hf h4) κ
    ⟨by simp [GGPosTag], rckRPb1_admissible_PSL hf h4⟩ hrangeκ hcentκ)

private lemma rckRPb1m_card_rootGroup_PSp
    {n f r : ℕ} (hnorm : RCKNormalizedModel .PSp r f)
    (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSp r f).K)
    (hroot : rckRPb1_SpRootData ι)
    {β : Fin (ggU .PSp r f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp r f).D.roots) :
    Nat.card ((ggU .PSp r f).D.rootGroup β) = Nat.card (GaloisField 2 f) := by
  have hker : ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype.comp ι).ker ≤
      Subgroup.center (ggU .PSp r f).K := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hιy : ι y = 1 := Subtype.ext (by simpa using hy)
    exact hcent y (by rw [hιy]; exact Subgroup.one_mem _)
  rw [← rckRP_card_map_ggRootSub hnorm ι
    (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype hker hβ 1]
  by_cases hlong : GGLongRoot (ggU .PSp r f).D β
  · obtain ⟨v, hv, hX⟩ := (hroot β 1 hβ).1 hlong
    have hX' : (ggRootSub (ggU .PSp r f).D ι β 1).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec v) := by
      simpa [ggRootSub] using hX
    rw [hX']
    exact card_matTransvGroup hv (rckRPb1_J_mulVec_ne_zero hv)
      (by rw [dotProduct_comm]; exact rckRPb1_J_alt v)
  · obtain ⟨a₁, a₂, _ha₁, _ha₂, hli, horth, hX⟩ := (hroot β 1 hβ).2 hlong
    have hX' : (ggRootSub (ggU .PSp r f).D ι β 1).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ := by
      simpa [ggRootSub] using hX
    rw [hX']
    exact card_altSiegelGroup
      (isUnit_iff_ne_zero.mpr (rckRPb1_J_det_ne_zero n f))
      (rckRPb1_J_transpose (n := n) (F := GaloisField 2 f))
      (rckRPb1_J_alt (n := n) (f := f)) hli horth

private theorem rckRPb1m_case_ge_two
    {n f r : ℕ} (hf : 1 ≤ f) (h4 : 4 ≤ Nat.card (GaloisField 2 f)) (hr : 2 ≤ r)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (ι : (ggU .PSp r f).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSp r f).K)
    (hrange : ι.range = J') (hroot : rckRPb1_SpRootData ι) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n f)) J' := by
  have hnorm : RCKNormalizedModel .PSp r f :=
    ⟨by simp [GGPosTag], rckRPb1_admissible_PSp hf hr (Or.inl h4)⟩
  have hf2 : 2 ≤ f := rckRPb1_two_le_of_card hf h4
  refine ⟨.PSp, r, f, ι, hnorm, hrange, hcent, ?_⟩
  intro β hβ _hclause u
  refine Or.inr ?_
  rw [rckRPb1m_card_rootGroup_PSp hnorm ι hcent hroot hβ,
    GaloisField.card 2 f (by omega)]
  have hpow : 2 ^ 1 < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simpa using hpow

theorem rckRP_modelII_PSp_selfDual
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e) (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆)
    (hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6))) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n f)) J' := by
  obtain ⟨r, ι, _hrank, hr1, hfr, _hinj, hcent, hrange, hroot⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_blockModel_selfDual_PSp_explicitFwd
      n f S hS he hadj hdeg hJe hA6
  rcases eq_or_lt_of_le hf with hf1 | hf2
  ·
    subst f
    have hcardF : Nat.card (GaloisField 2 1) = 2 := by
      rw [GaloisField.card 2 1 (by norm_num)]
      norm_num
    have hr3 : 3 ≤ r := by
      rcases hfr with h4 | h3
      · omega
      · exact h3
    exact rckRPb1m_case_f_one ι hr3 hcent hrange hroot
  ·
    have hf1 : 1 ≤ f := by omega
    have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (by omega)
    have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      rw [hcardF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rcases eq_or_lt_of_le hr1 with hr | hr
    · subst r
      exact rckRPb1m_case_one hf1 h4 ι hcent hrange hroot
    · exact rckRPb1m_case_ge_two hf1 h4 (by omega) ι hcent hrange hroot

end CFSG.StandardType.RCKRP
