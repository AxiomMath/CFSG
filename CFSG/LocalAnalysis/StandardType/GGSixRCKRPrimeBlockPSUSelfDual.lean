module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGStep
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlagBase
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoCard
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRootSubGeo

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition

private theorem rckRPb4_card_fixedField (g : ℕ) :
    Nat.card {c : GaloisField 2 (2 * (g + 1)) //
      (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) c = c} = 2 ^ (g + 1) := by
  have hFcard : Nat.card (GaloisField 2 (2 * (g + 1))) = (2 ^ (g + 1)) ^ 2 := by
    rw [GaloisField.card 2 (2 * (g + 1)) (by omega),
      show 2 * (g + 1) = (g + 1) * 2 by ring, pow_mul]
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (p := fun c : GaloisField 2 (2 * (g + 1)) =>
      (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) c = c)
    (q := fun c => c ∈ CFSG.LieType.Steinberg.fixedSubfield
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
    (fun c => (CFSG.LieType.Steinberg.mem_fixedSubfield
      (F := GaloisField 2 (2 * (g + 1))) (p := 2) (f := g + 1)).symm))]
  exact CFSG.LieType.Steinberg.card_fixedSubfield
    (F := GaloisField 2 (2 * (g + 1))) (p := 2) (f := g + 1) hFcard

private theorem rckRPb4_card_map_unitTransvGroup
    {F : Type} [Field F] [Finite F] {n : ℕ} (σ : F →+* F)
    {G : Type} [Group G] (j : G →* GL (Fin n) F) (hj : Function.Injective j)
    (P : Subgroup G) {v : Fin n → F}
    (hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) F).det) (hv : v ≠ 0)
    (hiso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hmap : P.map j = unitTransvGroup σ (Unitary.antidiag n) v) :
    Nat.card P = Nat.card {c : F // σ c = c} := by
  rw [← Subgroup.card_map_of_injective (K := P) (f := j) hj, hmap]
  exact card_unitTransvGroup σ hG hv hiso

private theorem rckRPb4_glGeoFlag_map_unitTransvGroup
    {F : Type} [Field F] {n : ℕ} (σ : F →+* F)
    {G : Type} [Group G] (j : G →* GL (Fin n) F)
    (P : Subgroup G) {v : Fin n → F}
    (hG : IsUnit (Unitary.antidiag n : Matrix (Fin n) (Fin n) F).det) (hv : v ≠ 0)
    (hiso : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hmap : P.map j = unitTransvGroup σ (Unitary.antidiag n) v) :
    GLGeoFlag none (P.map j) := by
  rw [hmap]
  exact glGeoFlag_unitTransvGroup σ hG hv hiso

private theorem rckRPb4_selfDual_flag_card
    (n g : ℕ) {G : Type} [Group G]
    (j : G →* GL (Fin n) (GaloisField 2 (2 * (g + 1))))
    (hj : Function.Injective j) (P : Subgroup G)
    {v w : Fin n → GaloisField 2 (2 * (g + 1))}
    (hv : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hvw : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1)
    (hmap : P.map j = unitTransvGroup
      (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) v) :
    GLGeoFlag none (P.map j) ∧ Nat.card P = 2 ^ (g + 1) := by
  let σ : GaloisField 2 (2 * (g + 1)) →+* GaloisField 2 (2 * (g + 1)) :=
    (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
  have hv0 : v ≠ 0 := by
    rintro rfl
    have hzero : (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        ((0 : Fin n → GaloisField 2 (2 * (g + 1))) i)) = 0 := by
      funext i
      simp
    have h := hvw
    rw [hzero, Matrix.zero_vecMul, zero_dotProduct] at h
    exact zero_ne_one h
  have hGdet : IsUnit (Unitary.antidiag n :
      Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))).det :=
    isUnit_iff_ne_zero.mpr
      (CFSG.LieType.Universal.Unitary.det_antidiag_ne_zero
        (F := GaloisField 2 (2 * (g + 1))) n)
  have hmapσ : P.map j = unitTransvGroup σ (Unitary.antidiag n) v := hmap
  constructor
  · exact rckRPb4_glGeoFlag_map_unitTransvGroup σ j P hGdet hv0 hv hmapσ
  · rw [rckRPb4_card_map_unitTransvGroup σ j hj P hGdet hv0 hv hmapσ]
    dsimp only [σ]
    exact rckRPb4_card_fixedField g

private theorem rckRPb4_PSL_two_admissible (g : ℕ) (hg2 : 2 ≤ g + 1) :
    CFSG.Open.StatedLieAdmissible .PSL 2 2 (g + 1) := by
  have h4 : 4 ≤ 2 ^ (g + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) hg2
  refine ⟨Nat.prime_two, by omega, le_refl 2, ?_, ?_⟩
  · intro h
    have := congrArg Prod.snd h
    omega
  · intro h
    have := congrArg Prod.snd h
    omega

private theorem rckRPb4_PSU_admissible
    (n g : ℕ) {G : Type} [Group G]
    (j : G →* GL (Fin n) (GaloisField 2 (2 * (g + 1))))
    (hj : Function.Injective j) {J' : Subgroup G} {r : ℕ}
    (ι : (ggU .PSU r (g + 1)).K →* G)
    {β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ}
    {v w : Fin n → GaloisField 2 (2 * (g + 1))}
    (hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots)
    (hlong : GGLongRoot (ggU .PSU r (g + 1)).D β₀)
    (hcenter : ∀ y, ι y ∈ Subgroup.center G →
      y ∈ Subgroup.center (ggU .PSU r (g + 1)).K)
    (hrange : ι.range = J')
    (hv : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hvw : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1)
    (h1 : ((((ggU .PSU r (g + 1)).D.rootGroup β₀).map ι).map j) =
      unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) v)
    (hadm : CFSG.Open.StatedLieAdmissible .PSU r 2 (g + 1)) :
    RCKRPFlaggedModel j none J' := by
  have hprep := rckRPb4_selfDual_flag_card n g j hj _ hv hvw h1
  refine ⟨.PSU, r, g + 1, ι, ⟨by simp [GGPosTag], hadm⟩, hrange, hcenter, ?_⟩
  refine rckRP_rootFlags_of_long (j := j) (B := none) ?_
    ⟨by simp [GGPosTag], hadm⟩ ?_ ι hβ₀ hlong hprep.1
  · intro y b hb
    simp at hb
  · simp

private theorem rckRPb4_PSU_two
    (n g : ℕ) {G : Type} [Group G] [Finite G]
    (j : G →* GL (Fin n) (GaloisField 2 (2 * (g + 1))))
    (hj : Function.Injective j) {J' : Subgroup G}
    (ι : (ggU .PSU 2 (g + 1)).K →* G)
    {β₀ : Fin (ggU .PSU 2 (g + 1)).D.rank → ℤ}
    {v w : Fin n → GaloisField 2 (2 * (g + 1))}
    (hβ₀ : β₀ ∈ (ggU .PSU 2 (g + 1)).D.roots)
    (hlong : GGLongRoot (ggU .PSU 2 (g + 1)).D β₀)
    (hcenter : ∀ y, ι y ∈ Subgroup.center G →
      y ∈ Subgroup.center (ggU .PSU 2 (g + 1)).K)
    (hrange : ι.range = J')
    (hv : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hvw : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1)
    (h1 : ((((ggU .PSU 2 (g + 1)).D.rootGroup β₀).map ι).map j) =
      unitTransvGroup
        (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
        (Unitary.antidiag n) v)
    (hg2 : 2 ≤ g + 1) :
    RCKRPFlaggedModel j none J' := by
  have hprep := rckRPb4_selfDual_flag_card n g j hj _ hv hvw h1
  obtain ⟨e⟩ := rckRP_nonempty_mulEquiv_PSL_two_PSU_two (g := g + 1) (by omega)
  let κ : (ggU .PSL 2 (g + 1)).K →* G := ι.comp e.toMonoidHom
  have hκrange : κ.range = J' := by
    change (ι.comp e.toMonoidHom).range = J'
    have hrangeE : e.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective
    rw [MonoidHom.range_comp, hrangeE, ← MonoidHom.range_eq_map, hrange]
  have hκcenter : ∀ y, κ y ∈ Subgroup.center G →
      y ∈ Subgroup.center (ggU .PSL 2 (g + 1)).K := by
    intro y hy
    have hy' : e y ∈ Subgroup.center (ggU .PSU 2 (g + 1)).K := by
      apply hcenter (e y)
      change ι (e y) ∈ Subgroup.center _
      exact hy
    have hcentermap : (Subgroup.center (ggU .PSL 2 (g + 1)).K).map
        (e : (ggU .PSL 2 (g + 1)).K →* (ggU .PSU 2 (g + 1)).K) =
        Subgroup.center (ggU .PSU 2 (g + 1)).K := Subgroup.map_center_eq e
    rw [← hcentermap] at hy'
    exact (Subgroup.mem_map_iff_mem e.injective).mp hy'
  have hκker : κ.ker ≤ Subgroup.center (ggU .PSL 2 (g + 1)).K := by
    intro y hy
    apply hκcenter y
    rw [MonoidHom.mem_ker.mp hy]
    exact Subgroup.one_mem _
  have hP₀ : ((((ggU .PSU 2 (g + 1)).D.rootGroup β₀).map ι)) ≤ κ.range := by
    rw [hκrange]
    exact (Subgroup.map_le_range ι _).trans_eq hrange
  refine ⟨.PSL, 2, g + 1, κ,
    ⟨by simp [GGPosTag], rckRPb4_PSL_two_admissible g hg2⟩, hκrange, hκcenter, ?_⟩
  exact rckRP_rootFlags_PSL_two (j := j) (B := none) (f := g + 1)
    (fun _ b hb => by simp at hb) hg2 κ hκker hP₀ hprep.2 hprep.1

theorem rckRP_flaggedModel_PSU_selfDual
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S (e)⁆) :
    RCKRPFlaggedModel
      (Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype
      none J' := by
  obtain ⟨r, ι, β₀, -, hlong, hcenter, hrange, v, w, hv, hw, hvw, h1, h2⟩ :=
    exists_blockModel_selfDual_PSU_explicit n g S hS he hadj hdeg hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  have hadm := rckRP_admissible_PSU_of_quasisimple_range
    (g := g + 1) (by omega : 1 ≤ g + 1) ι hq
  have hβ₀ : β₀ ∈ (ggU .PSU r (g + 1)).D.roots :=
    ggLongRoot_mem_roots hlong
  let j := (Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype
  have hj : Function.Injective j := Subgroup.subtype_injective _
  change RCKRPFlaggedModel j none J'
  rcases hadm with hadm | ⟨rfl, hg2⟩
  · exact rckRPb4_PSU_admissible n g j hj ι hβ₀ hlong hcenter hrange hv hvw h1 hadm
  · exact rckRPb4_PSU_two n g j hj ι hβ₀ hlong hcenter hrange hv hvw h1 hg2

private theorem rckRPb4m_case_PSU
    (n g r : ℕ)
    {J' : Subgroup ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (ι : (ggU .PSU r (g + 1)).K →* ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
    {β₀ : Fin (ggU .PSU r (g + 1)).D.rank → ℤ}
    {v w : Fin n → GaloisField 2 (2 * (g + 1))}
    (hlong : GGLongRoot (ggU .PSU r (g + 1)).D β₀)
    (hcenter : ∀ y, ι y ∈ Subgroup.center ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n) →
      y ∈ Subgroup.center (ggU .PSU r (g + 1)).K)
    (hrange : ι.range = J')
    (hv : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
      (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w i))
      (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul
      (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i))
      (Unitary.antidiag n) ⬝ᵥ w = 1)
    (h1 : (((ggU .PSU r (g + 1)).D.rootGroup β₀).map ι).map
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      n).subtype) = unitTransvGroup
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) v)
    (hadm : CFSG.Open.StatedLieAdmissible .PSU r 2 (g + 1)) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSU n (g + 1))) J' := by
  have hnorm : RCKNormalizedModel .PSU r (g + 1) := ⟨Or.inr (Or.inl rfl), hadm⟩
  have hnot : ¬ ((CFSG.Open.StatedLieTag.PSU = .PSp ∧ r = 2) ∨
      CFSG.Open.StatedLieTag.PSU = .F4) := by simp
  refine rckRP_modelII_of_long (J' := J') hnorm hnot ι hrange hcenter ?_ hlong ?_
  · intro R' y h
    change RCKRPRootSubOf (ggU .PSU n (g + 1))
      (R'.map (MulAut.conj (ι y)).toMonoidHom)
    exact rckRPRootSubOf_map_conj h (ι y)
  · exact rckRPRootSubOf_PSU_of_unitTransv
      (R' := ((ggU .PSU r (g + 1)).D.rootGroup β₀).map ι) hv hw hvw h1

private theorem rckRPb4m_case_PSL
    (n g : ℕ)
    {J' : Subgroup ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (ι : (ggU .PSU 2 (g + 1)).K →* ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n))
    (hcenter : ∀ y, ι y ∈ Subgroup.center ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n) →
      y ∈ Subgroup.center (ggU .PSU 2 (g + 1)).K)
    (hrange : ι.range = J')
    (hg2 : 2 ≤ g + 1) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSU n (g + 1))) J' := by
  obtain ⟨e⟩ := rckRP_nonempty_mulEquiv_PSL_two_PSU_two (g := g + 1) (by omega)
  let κ : (ggU .PSL 2 (g + 1)).K →* ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n) := ι.comp e.toMonoidHom
  have hκrange : κ.range = J' := by
    change (ι.comp e.toMonoidHom).range = J'
    have hrangeE : e.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective
    rw [MonoidHom.range_comp, hrangeE, ← MonoidHom.range_eq_map, hrange]
  have hκcenter : ∀ y, κ y ∈ Subgroup.center ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n) →
      y ∈ Subgroup.center (ggU .PSL 2 (g + 1)).K := by
    intro y hy
    have hy' : e y ∈ Subgroup.center (ggU .PSU 2 (g + 1)).K := by
      apply hcenter (e y)
      change ι (e y) ∈ Subgroup.center _
      exact hy
    have hcentermap : (Subgroup.center (ggU .PSL 2 (g + 1)).K).map
        (e : (ggU .PSL 2 (g + 1)).K →* (ggU .PSU 2 (g + 1)).K) =
        Subgroup.center (ggU .PSU 2 (g + 1)).K := Subgroup.map_center_eq e
    rw [← hcentermap] at hy'
    exact (Subgroup.mem_map_iff_mem e.injective).mp hy'
  exact rckRP_modelII_of_big _ (rckRP_modelBig_of_PSL (k := 1) hg2 κ
    ⟨Or.inl rfl, rckRPb4_PSL_two_admissible g hg2⟩ hκrange hκcenter)

theorem rckRP_modelII_PSU_selfDual
    (n g : ℕ) (S : Set (GL (Fin n) (GaloisField 2 (2 * (g + 1)))))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e)
    (hadj : formAdj
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom
      (Unitary.antidiag n) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2)
    {J' : Subgroup
      ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    (hJe : IsComponentOf J'
      ⁅glBlockCentralizer
      ((Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype)
      S (e),
      glBlockCentralizer
        ((Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
        n).subtype) S (e)⁆) :
    RCKRPModelII (RCKRPRootSubOf (ggU .PSU n (g + 1))) J' := by
  obtain ⟨r, ι, β₀, -, hlong, hcenter, hrange, v, w, hv, hw, hvw, h1, h2⟩ :=
    exists_blockModel_selfDual_PSU_explicit n g S hS he hadj hdeg hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  have hadm := rckRP_admissible_PSU_of_quasisimple_range
    (g := g + 1) (by omega : 1 ≤ g + 1) ι hq
  rcases hadm with hadm | ⟨rfl, hg2⟩
  · exact rckRPb4m_case_PSU n g r ι hlong hcenter hrange hv hw hvw h1 hadm
  · exact rckRPb4m_case_PSL n g ι hcenter hrange hg2

end CFSG.StandardType.RCKRP
