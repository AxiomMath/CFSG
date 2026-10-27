module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagBase
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoCard
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPSp
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRootSubGeo

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

private theorem rckRPb2_J_isUnit_det (n f : ℕ) :
    IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).det := by
  show IsUnit (CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f)).det
  exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero

private theorem rckRPb2_J_transpose (n f : ℕ) :
    Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  show Matrix.transpose (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) =
    CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)
  exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two

private theorem rckRPb2_J_alternating (n f : ℕ) :
    ∀ x : (Fin n ⊕ Fin n) → GaloisField 2 f,
      x ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) x = 0 := by
  intro x
  change x ⬝ᵥ Matrix.mulVec (CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f)) x = 0
  rw [← CFSG.ClassicalGroups.Symplectic.spForm_apply]
  exact CFSG.ClassicalGroups.Symplectic.spForm_self x

private theorem rckRPb2_linearIndependent_pair {n f : ℕ}
    {a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 1)
    (h₃ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 0) :
    LinearIndependent (GaloisField 2 f) ![a₁, a₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  constructor
  · have h := congrArg (fun x => x ⬝ᵥ Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁) hst
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      zero_dotProduct, h₁, h₃.2.2.2, mul_zero, mul_one, add_zero] at h
    exact h
  · have h := congrArg (fun x => x ⬝ᵥ Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂) hst
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      zero_dotProduct, h₃.2.2.1, h₂, mul_zero, mul_one, zero_add] at h
    exact h

private theorem rckRPb2_isometry (n f : ℕ) :
    ∀ y : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      ∀ b ∈ spForm n (GaloisField 2 f), ∀ m m' : (Fin n ⊕ Fin n) → GaloisField 2 f,
        b (((y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec m)
          (((y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).mulVec m') =
          b m m' :=
  fun y b hb m m' =>
    spForm_isometry n (GaloisField 2 f) (y : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) y.2
      b hb m m'

private theorem rckRPb2_flag_rootGroup {n f : ℕ} {U : Type} [Group U]
    (D : UniversalRootDatum U)
    {ι : U →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} {β₀ : Fin D.rank → ℤ}
    {a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 1)
    (h₃ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 0)
    (himg : (((D.rootGroup β₀).map ι).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) :
    GLGeoFlag (spForm n (GaloisField 2 f))
      (((D.rootGroup β₀).map ι).map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) := by
  have hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂] :=
    rckRPb2_linearIndependent_pair h₁ h₂ h₃
  have hflag := glGeoFlag_altSiegelGroup (rckRPb2_J_isUnit_det n f)
    (rckRPb2_J_transpose n f) (rckRPb2_J_alternating n f) hli h₃.1
  rw [himg]
  exact hflag

private theorem rckRPb2_card_rootGroup {n f : ℕ} {U : Type} [Group U]
    (D : UniversalRootDatum U)
    {ι : U →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} {β₀ : Fin D.rank → ℤ}
    {a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (hf1 : 1 ≤ f)
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 1)
    (h₃ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 0)
    (himg : (((D.rootGroup β₀).map ι).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) :
    Nat.card ((D.rootGroup β₀).map ι) = 2 ^ (max f 1) := by
  have hfg : max f 1 = f := max_eq_left hf1
  have hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂] :=
    rckRPb2_linearIndependent_pair h₁ h₂ h₃
  have h1 : Nat.card ((D.rootGroup β₀).map ι) =
      Nat.card (((D.rootGroup β₀).map ι).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) :=
    (Subgroup.card_map_of_injective
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype_injective).symm
  rw [h1, himg, card_altSiegelGroup (rckRPb2_J_isUnit_det n f)
    (rckRPb2_J_transpose n f) (rckRPb2_J_alternating n f) hli h₃.1,
    GaloisField.card 2 f (by omega : f ≠ 0), hfg]

private theorem rckRPb2_range_comp {X Y Z : Type} [Group X] [Group Y] [Group Z]
    (e : Y ≃* X) (ι : X →* Z) {J' : Subgroup Z} (hrange : ι.range = J') :
    (ι.comp e.toMonoidHom).range = J' := by
  rw [← hrange]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e y, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨e.symm z, by simp⟩

private theorem rckRPb2_center_comp {X Y Z : Type} [Group X] [Group Y] [Group Z]
    (e : Y ≃* X) (ι : X →* Z)
    (hcent : ∀ x, ι x ∈ Subgroup.center Z → x ∈ Subgroup.center X) :
    ∀ y, (ι.comp e.toMonoidHom) y ∈ Subgroup.center Z → y ∈ Subgroup.center Y := by
  intro y hy
  have h1 : e y ∈ Subgroup.center X := hcent (e y) hy
  have h2 : e.symm (e y) ∈ Subgroup.center Y := MulEquivClass.apply_mem_center e.symm h1
  simpa using h2

private theorem rckRPb2_ker_center_comp {X Y Z : Type} [Group X] [Group Y] [Group Z]
    (e : Y ≃* X) (ι : X →* Z)
    (hcent : ∀ x, ι x ∈ Subgroup.center Z → x ∈ Subgroup.center X) :
    (ι.comp e.toMonoidHom).ker ≤ Subgroup.center Y := by
  intro y hy
  exact rckRPb2_center_comp e ι hcent y (by
    rw [MonoidHom.mem_ker.mp hy]
    exact Subgroup.one_mem _)

private theorem rckRPb2_one_le_of_two_le_max {f : ℕ} (hg : 2 ≤ max f 1) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with hf0 | hfpos
  · subst hf0
    rw [show max 0 1 = 1 from max_eq_right (Nat.zero_le 1)] at hg
    omega
  · omega

private theorem rckRPb2_admissible_PSL {g : ℕ} (hg : 2 ≤ g) :
    CFSG.Open.StatedLieAdmissible .PSL 2 2 g := by
  have h4 : 4 ≤ 2 ^ g := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  refine ⟨by norm_num, by omega, le_refl 2, ?_, ?_⟩
  · intro h
    have hpow : 2 ^ g = 2 := congrArg Prod.snd h
    omega
  · intro h
    have hpow : 2 ^ g = 3 := congrArg Prod.snd h
    omega

private theorem rckRPb2_case_PSU
    {n f r : ℕ} {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {ι : (ggU .PSU r (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ}
    {a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (hadm : CFSG.Open.StatedLieAdmissible .PSU r 2 (max f 1))
    (hβroot : β₀ ∈ (ggU .PSU r (max f 1)).D.roots)
    (hlong : GGLongRoot (ggU .PSU r (max f 1)).D β₀)
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSU r (max f 1)).K)
    (hrange : ι.range = J')
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 1)
    (h₃ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 0)
    (himg₁ : (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  have hnorm : RCKNormalizedModel .PSU r (max f 1) := ⟨Or.inr (Or.inl rfl), hadm⟩
  refine ⟨.PSU, r, max f 1, ι, hnorm, hrange, hcent, ?_⟩
  refine rckRP_rootFlags_of_long (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
    (rckRPb2_isometry n f) hnorm ?_ ι hβroot hlong ?_
  · intro hcon
    rcases hcon with ⟨h, -⟩ | h
    · cases h
    · cases h
  · exact rckRPb2_flag_rootGroup (ggU .PSU r (max f 1)).D h₁ h₂ h₃ himg₁

private theorem rckRPb2_case_PSL
    {n f : ℕ} {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {ι : (ggU .PSU 2 (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {β₀ : Fin (ggU .PSU 2 (max f 1)).D.rank → ℤ}
    {a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (hg2 : 2 ≤ max f 1)
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSU 2 (max f 1)).K)
    (hrange : ι.range = J')
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 1)
    (h₃ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 0)
    (himg₁ : (((ggU .PSU 2 (max f 1)).D.rootGroup β₀).map ι).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  have hf1 : 1 ≤ f := rckRPb2_one_le_of_two_le_max hg2
  obtain ⟨e⟩ := rckRP_nonempty_mulEquiv_PSL_two_PSU_two (g := max f 1) (by omega)
  have hκcent : ∀ y, (ι.comp e.toMonoidHom) y ∈
      Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSL 2 (max f 1)).K :=
    rckRPb2_center_comp e ι hcent
  have hκker : (ι.comp e.toMonoidHom).ker ≤
      Subgroup.center (ggU .PSL 2 (max f 1)).K :=
    rckRPb2_ker_center_comp e ι hcent
  have hκrange : (ι.comp e.toMonoidHom).range = J' := rckRPb2_range_comp e ι hrange
  refine ⟨.PSL, 2, max f 1, ι.comp e.toMonoidHom,
    ⟨Or.inl rfl, rckRPb2_admissible_PSL hg2⟩, hκrange, hκcent, ?_⟩
  refine rckRP_rootFlags_PSL_two (P₀ := ((ggU .PSU 2 (max f 1)).D.rootGroup β₀).map ι)
    (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype (rckRPb2_isometry n f) hg2
    (ι.comp e.toMonoidHom) hκker ?_ ?_ ?_
  · rw [hκrange, ← hrange]
    exact Subgroup.map_le_range ι _
  · exact rckRPb2_card_rootGroup (ggU .PSU 2 (max f 1)).D hf1 h₁ h₂ h₃ himg₁
  · exact rckRPb2_flag_rootGroup (ggU .PSU 2 (max f 1)).D h₁ h₂ h₃ himg₁

theorem rckRP_flaggedModel_PSp_selfDualTwo
    (n f : ℕ) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    RCKRPFlaggedModel (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      (spForm n (GaloisField 2 f)) J' := by
  unfold RCKRPFlaggedModel
  obtain ⟨r, ι, β₀, _, hlong, hcent, hrange, a₁, a₂, b₁, b₂, h₁, h₂, h₃, himg₁, _⟩ :=
    exists_blockModel_selfDualTwo_PSp_explicit n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := hrange ▸ hJe.2.2
  have hβroot : β₀ ∈ (ggU .PSU r (max f 1)).D.roots := ggLongRoot_mem_roots hlong
  rcases rckRP_admissible_PSU_of_quasisimple_range (Nat.le_max_right f 1) ι hq with
    hadm | ⟨hr2, hg2⟩
  · exact rckRPb2_case_PSU hadm hβroot hlong hcent hrange h₁ h₂ h₃ himg₁
  · obtain rfl := hr2
    exact rckRPb2_case_PSL hg2 hcent hrange h₁ h₂ h₃ himg₁

private theorem rckRPb2m_case_PSU
    {n f r : ℕ} {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {ι : (ggU .PSU r (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ}
    (hadm : CFSG.Open.StatedLieAdmissible .PSU r 2 (max f 1))
    (hlong : GGLongRoot (ggU .PSU r (max f 1)).D β₀)
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSU r (max f 1)).K)
    (hrange : ι.range = J')
    (hP₀ : RCKRPRootSubOf (ggU .PSp n f)
      (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι)) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n f)) J' := by
  refine rckRP_modelII_of_long (t := .PSU) (k := r) (g := max f 1)
    (P := RCKRPRootSubOf (ggU .PSp n f)) (J' := J') (β₀ := β₀)
    ⟨Or.inr (Or.inl rfl), hadm⟩ ?_ ι hrange hcent ?_ hlong hP₀
  · rintro (⟨h, -⟩ | h)
    · cases h
    · cases h
  · intro R' y h
    exact rckRPRootSubOf_map_conj h (ι y)

private theorem rckRPb2m_case_PSL
    {n f : ℕ} {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {ι : (ggU .PSU 2 (max f 1)).K →* ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hg2 : 2 ≤ max f 1)
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) →
      y ∈ Subgroup.center (ggU .PSU 2 (max f 1)).K)
    (hrange : ι.range = J') :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n f)) J' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := rckRP_nonempty_mulEquiv_PSL_two_PSU_two (g := max f 1) (by omega)
  exact rckRP_modelII_of_big _ (rckRP_modelBig_of_PSL (k := 1) hg2 (ι.comp e.toMonoidHom)
    ⟨Or.inl rfl, rckRPb2_admissible_PSL hg2⟩ (rckRPb2_range_comp e ι hrange)
    (rckRPb2_center_comp e ι hcent))

theorem rckRP_modelII_PSp_selfDualTwo
    (n f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) e =
      e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e),
      glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) S (e)⁆) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSp n f)) J' := by
  obtain ⟨r, ι, β₀, _, hlong, hcent, hrange, a₁, a₂, b₁, b₂, h₁, h₂, h₃, himg₁, _⟩ :=
    exists_blockModel_selfDualTwo_PSp_explicit n f S hSU hS hodd he hadj hdeg₁ hdeg₂ hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := hrange ▸ hJe.2.2
  rcases rckRP_admissible_PSU_of_quasisimple_range (Nat.le_max_right f 1) ι hq with
    hadm | ⟨hr2, hg2⟩
  · exact rckRPb2m_case_PSU hadm hlong hcent hrange
      (rckRPRootSubOf_PSp_of_altSiegel (R' := (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι))
        h₁ h₂ h₃ himg₁)
  · obtain rfl := hr2
    exact rckRPb2m_case_PSL hg2 hcent hrange

end CFSG.StandardType.RCKRP
