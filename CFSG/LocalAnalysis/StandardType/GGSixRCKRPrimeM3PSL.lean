module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3Deg1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3RSHom
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3RSFlag
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSL

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckM3as_range_mulVecLin_ne_bot {n : ℕ} {F : Type} [Field F]
    {e : Matrix (Fin n) (Fin n) F} (he : e ≠ 0) :
    LinearMap.range (Matrix.mulVecLin e) ≠ ⊥ := by
  intro hbot
  apply he
  have h0 : Matrix.mulVecLin e = 0 := LinearMap.range_eq_bot.mp hbot
  refine Matrix.mulVec_injective ?_
  rw [← Matrix.coe_mulVecLin (M := e),
    ← Matrix.coe_mulVecLin (M := (0 : Matrix (Fin n) (Fin n) F)), h0, Matrix.mulVecLin_zero]

private theorem rckM3as_mem_center_of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) {y : G}
    (hy : f y ∈ Subgroup.center H) : y ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hy ⊢
  intro z
  apply hf
  rw [map_mul, map_mul]
  exact hy (f z)

private theorem rckM3as_map_injective {R S : Type*} [CommRing R] [CommRing S]
    {n : Type*} [Fintype n] [DecidableEq n] (σ : R ≃+* S) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := n) σ.toRingHom) := by
  intro A B h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply σ.injective
  have h' := congrFun (congrFun (congrArg
    (fun M : Matrix.SpecialLinearGroup n S => (M : Matrix n n S)) h) i) j
  simpa [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.map_apply] using h'

private theorem rckM3as_map_surjective {R S : Type*} [CommRing R] [CommRing S]
    {n : Type*} [Fintype n] [DecidableEq n] (σ : R ≃+* S) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := n) σ.toRingHom) := by
  intro B
  refine ⟨⟨σ.symm.mapMatrix (B : Matrix n n S), ?_⟩, ?_⟩
  · rw [← RingEquiv.map_det σ.symm (B : Matrix n n S), B.2, map_one]
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      RingEquiv.mapMatrix_apply, Matrix.map_apply]
    exact σ.apply_symm_apply _

theorem rckM3_PSL
    (m g : ℕ) (hg : 1 ≤ g) (S : Set (GL (Fin (m + 1)) (GaloisField 2 g)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g))}
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) :
    ∃ (k : ℕ) (ι : (ggU .PSL (k + 1)
        (g * blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)).K →*
        (ggU .PSL (m + 1) g).K),
      (∀ y, ι y ∈ Subgroup.center (ggU .PSL (m + 1) g).K →
        y ∈ Subgroup.center (ggU .PSL (k + 1)
          (g * blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)).K) ∧
      ι.range = J' ∧
      ∀ β ∈ (ggU .PSL (k + 1)
          (g * blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)).D.roots,
        ∃ W H : Submodule (GaloisField 2 g) (Fin (m + 1) → GaloisField 2 g), W ≤ H ∧
          ∀ x ∈ (ggU .PSL (k + 1)
              (g * blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e)).D.rootGroup β,
            x ≠ 1 →
            LinearMap.range (Matrix.toLin'
              (((Matrix.SpecialLinearGroup.toGL (ι x) : GL (Fin (m + 1)) (GaloisField 2 g)) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1)) = W ∧
            LinearMap.ker (Matrix.toLin'
              (((Matrix.SpecialLinearGroup.toGL (ι x) : GL (Fin (m + 1)) (GaloisField 2 g)) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) - 1)) = H := by
  classical
  by_cases hdeg : blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e < 2
  · exact rckM3_PSL_deg1 m g hg S hS hodd he hJe hdeg
  · have hdeg2 : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e := by
      omega
    let a : ℕ := blockDegree (Algebra.adjoin (GaloisField 2 g) (Units.val '' S)) e
    obtain ⟨K, hKfield, hKfin, hKalg, hKmod, hKtower, π, hπ⟩ :=
      rckBlockCoord_exists S hS hodd he
    letI : Field K := hKfield
    letI : Finite K := hKfin
    letI : Algebra (GaloisField 2 g) K := hKalg
    letI : Module K (LinearMap.range (Matrix.mulVecLin e)) := hKmod
    letI : IsScalarTower (GaloisField 2 g) K (LinearMap.range (Matrix.mulVecLin e)) := hKtower
    have hKcard : Nat.card K = 2 ^ (g * a) := by
      rw [hπ.2.2, GaloisField.card 2 g (by omega), ← pow_mul]
    have hK4 : 4 ≤ Nat.card K := by
      have hga : 2 ≤ g * a := Nat.mul_le_mul hg hdeg2
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (g * a) := (pow_right_monotone (show (1 : ℕ) ≤ 2 by norm_num)) hga
        _ = Nat.card K := hKcard.symm
    haveI hWfin : Module.Finite K (LinearMap.range (Matrix.mulVecLin e)) :=
      Module.Finite.of_restrictScalars_finite (GaloisField 2 g) K
        (LinearMap.range (Matrix.mulVecLin e))
    have hWne : LinearMap.range (Matrix.mulVecLin e) ≠ ⊥ :=
      rckM3as_range_mulVecLin_ne_bot he.2.2.1
    haveI hWnt : Nontrivial (LinearMap.range (Matrix.mulVecLin e)) :=
      (Submodule.nontrivial_iff_ne_bot).mpr hWne
    have hfinpos : 0 < Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) :=
      Module.finrank_pos_iff.mpr hWnt
    let k : ℕ := Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) - 1
    have hk : Module.finrank K (LinearMap.range (Matrix.mulVecLin e)) = k + 1 := by
      dsimp only [k]
      omega
    let b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e)) :=
      Module.finBasisOfFinrankEq K (LinearMap.range (Matrix.mulVecLin e)) hk
    obtain ⟨ρ, hρmat, hρinj, hρle, hρcomm⟩ :=
      rckBlockRS_hom (K := K) (π := π) hS he hπ b
    have hcardGF : Nat.card (GaloisField 2 (g * a)) = 2 ^ (g * a) :=
      GaloisField.card 2 (g * a) (Nat.mul_ne_zero (by omega) (by omega))
    have hcard_eq : Nat.card (GaloisField 2 (g * a)) = Nat.card K := by
      rw [hcardGF, hKcard]
    obtain ⟨σ⟩ := CFSG.RankThree.PartOne.CTP.nonempty_ringEquiv_of_natCard_eq hcard_eq
    haveI hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (k + 1)) K) :=
      CFSG.SeitzReduction.LinearPilot.InvPlacement.isPerfect_specialLinearGroup_of_four_le hK4
        (Fin (k + 1))
    haveI hperfR : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    have hρrange : ρ.range = ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ := by
      apply le_antisymm
      · calc ρ.range = ⁅ρ.range, ρ.range⁆ := (Subgroup.commutator_eq_self (H := ρ.range)).symm
          _ ≤ ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
              glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :=
            Subgroup.commutator_mono hρle hρle
      · exact hρcomm
    obtain ⟨m', hm'2, hiso⟩ :=
      fePSL_dualPair_blockGroup_iso m g hg S hS hodd he hdeg2 hJe K hKcard
    have hJeq : J' = ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆ :=
      fePSL_component_eq m g S hJe hm'2 hK4 hiso
    let ι : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 (g * a)) →*
        Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g) :=
      ρ.comp (Matrix.SpecialLinearGroup.map σ.toRingHom)
    have hιinj : Function.Injective ι := hρinj.comp (rckM3as_map_injective σ)
    have hιrange : ι.range = J' := by
      have h1 : (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) σ.toRingHom).range = ⊤ :=
        MonoidHom.range_eq_top.mpr (rckM3as_map_surjective σ)
      have h2 : ι.range = ρ.range := by
        rw [← MonoidHom.map_range ρ
            (Matrix.SpecialLinearGroup.map (n := Fin (k + 1)) σ.toRingHom), h1,
          ← MonoidHom.range_eq_map ρ]
      rw [h2, hρrange, ← hJeq]
    refine ⟨k, ι, ?_, hιrange, ?_⟩
    · intro y hy
      exact rckM3as_mem_center_of_injective ι hιinj hy
    · intro β hβ
      have hβ' : β ∈ (SpecialLinear.rootDatum k (GaloisField 2 (g * a))).roots := hβ
      obtain ⟨hij, -⟩ := SpecialLinear.idx_spec k hβ'
      obtain ⟨W', H', hWH, hflag⟩ :=
        rckBlockRS_flag (m := m) (g := g) (k := k) (e := e) he.2.1.eq b
          (i := (SpecialLinear.idx k β).1) (j := (SpecialLinear.idx k β).2) hij
      refine ⟨W', H', hWH, ?_⟩
      intro x hx hxne
      have hx' : x ∈ SpecialLinear.rootGroup k (GaloisField 2 (g * a)) β := hx
      rw [SpecialLinear.rootGroup_eq_idx k (GaloisField 2 (g * a)) hβ'] at hx'
      obtain ⟨c, hc⟩ :=
        (SpecialLinear.mem_rootSubgroup (m := k) (F := GaloisField 2 (g * a)) hij x).mp hx'
      have hc0 : c ≠ 0 := by
        intro h0
        apply hxne
        rw [← hc, h0, Matrix.SpecialLinearGroup.transvection_coeff_zero]
        rfl
      have hσc : σ c ≠ 0 := by
        intro h
        exact hc0 (σ.injective (by simpa using h))
      have hmat : ((ι x : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) =
          rckBlockRSMat b (Matrix.SpecialLinearGroup.transvection hij (σ c)) := by
        calc ((ι x : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)) :
              Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g))
            = ((ρ (Matrix.SpecialLinearGroup.map σ.toRingHom x) :
                Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 g)) :
                Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) := rfl
          _ = rckBlockRSMat b ((Matrix.SpecialLinearGroup.map σ.toRingHom x :
                Matrix.SpecialLinearGroup (Fin (k + 1)) K) :
                Matrix (Fin (k + 1)) (Fin (k + 1)) K) := hρmat _
          _ = rckBlockRSMat b (Matrix.SpecialLinearGroup.transvection hij (σ c)) := by
              rw [← hc, Matrix.SpecialLinearGroup.map_transvection]
              rfl
      have hfin := hflag (σ c) hσc
      have hxmat : ((Matrix.SpecialLinearGroup.toGL (ι x) :
            GL (Fin (m + 1)) (GaloisField 2 g)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)) =
            rckBlockRSMat b (Matrix.SpecialLinearGroup.transvection hij (σ c)) :=
        (Matrix.SpecialLinearGroup.coe_GL_coe_matrix (ι x)).trans hmat
      constructor
      · erw [hxmat]
        exact hfin.1
      · erw [hxmat]
        exact hfin.2

end CFSG.StandardType.RCKRP
