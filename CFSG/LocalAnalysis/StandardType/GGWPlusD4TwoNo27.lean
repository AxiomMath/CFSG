module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityRank
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGenFrame
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoPieces
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoPlanes
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoAniso
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthTwoRot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Large
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthATwo
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSpSplitTorus

public section

namespace CFSG.StandardType

open Module CFSG.Assembly CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

private theorem card_two_eq_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {x : K} (hx : x ≠ 0) : x = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hunit : Fintype.card Kˣ = 1 := by rw [Fintype.card_units, hcard]
  haveI : Subsingleton Kˣ := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hunit)
  have h1 : Units.mk0 x hx = 1 := Subsingleton.elim _ _
  simpa using congrArg (fun u : Kˣ => (u : K)) h1

theorem genMax_card_ne_27 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hA : GenMax (polB (coordinateQuadPlus 4 K)) (matrixDerived (coordinateQuadPlus 4 K)) 3 A) :
    Nat.card A ≠ 27 := by
  intro hcard
  classical
  let Q : QuadraticForm K (Fin (2 * 4) → K) := coordinateQuadPlus 4 K
  let B : (Fin (2 * 4) → K) →ₗ[K] (Fin (2 * 4) → K) →ₗ[K] K := polB Q
  obtain ⟨S, hS, hterm⟩ := exists_terminal_genPieceSet hA
  obtain ⟨hScard, hSplanes, hV0fr⟩ := genMax_pieces_planes_of_card_27 hK hA hS hterm hcard
  let V0 : Submodule K (Fin (2 * 4) → K) := (genPieceSpan S).orthogonalBilin B
  have hV0finrank : finrank K V0 = 2 := hV0fr
  have hAniso := genMax_complement_anisotropic_of_card_27 hK hA hS hterm hcard
  have hX : SUTB.NondegOn B (genPieceSpan S) := (hS.nondegOn_card hA).1
  have hXA : ∀ a ∈ A, ∀ w ∈ genPieceSpan S, glin a w ∈ genPieceSpan S := by
    intro a ha w hw
    have hle : genPieceSpan S ≤ Submodule.comap (glin a) (genPieceSpan S) := by
      refine iSup₂_le fun y hy => ?_
      intro u hu
      exact le_iSup₂ (f := fun y _ => grng y) y hy (grng_inv hA (hS.mem y hy) ha u hu)
    exact hle hw
  have hp1 : 1 ≤ 3 := by norm_num
  have hV0A : ∀ a ∈ A, ∀ w ∈ V0, glin a w ∈ V0 := fun a ha w hw =>
    CFSG.RankThree.PartOne.OddIso.orth_invariantH (hA.iso a ha) (hA.lin_pow ha) hp1 (hXA a ha) hw
  have hV0nd : SUTB.NondegOn B V0 := by
    intro m hm horth
    apply hA.sep m
    intro v
    obtain ⟨x, hx, z, hz, rfl⟩ := SUTB.exists_add_orth hX v
    have h1 : B x m = 0 := (Submodule.mem_orthogonalBilin.mp hm) x hx
    have h2 : B z m = 0 := horth z hz
    have hxm : B m x = 0 := (hA.symm.eq m x).trans h1
    have hzm : B m z = 0 := (hA.symm.eq m z).trans h2
    calc B m (x + z) = B m x + B m z := map_add (B m) x z
      _ = 0 := by simp [hxm, hzm]
  have hXle : genPieceSpan S ≤ V0.orthogonalBilin B := by
    intro x hx
    rw [Submodule.mem_orthogonalBilin]
    intro z hz
    exact (hA.symm.eq x z) ▸ ((Submodule.mem_orthogonalBilin.mp hz) x hx)
  have hV0triv : ∀ c ∈ A, ∀ w ∈ V0, glin c w = w := by
    intro c hc w hw
    obtain ⟨g, hgA, hgw, hgoff⟩ := GenMax.exists_mem_restrict hA hV0nd hV0A hc
    have hgX : ∀ v ∈ genPieceSpan S, glin g v = v := fun v hv => hgoff v (hXle hv)
    have hg1 : g = 1 := hterm g hgA hgX
    rw [← hgw w hw, hg1, glin_one]
    rfl
  have hV0ne : V0 ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hV0finrank
    omega
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0ne
  have haQ : Q a = 1 := card_two_eq_one hK (hAniso a ha ha0)
  have hbex : ∃ b ∈ V0, B b a ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact ha0 (hV0nd a ha h)
  obtain ⟨b, hb, hba⟩ := hbex
  have hb0 : b ≠ 0 := fun h => hba (by rw [h]; simp)
  have hbQ : Q b = 1 := card_two_eq_one hK (hAniso b hb hb0)
  have hab : B a b ≠ 0 := fun h => hba ((hA.symm.eq a b).symm.trans h)
  have hab1 : B a b = 1 := card_two_eq_one hK hab
  have haa : Q.polarBilin a a = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, CharTwo.two_nsmul]
  let u : GL (Fin (2 * 4)) K :=
    CFSG.ComponentClassification.RankTwoClassical.anisoRotGL (Q := Q) (a := a) (b := b) hab1
  have hu_mat : (u : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
      = CFSG.ComponentClassification.RankTwoClassical.anisoRot Q a b :=
    CFSG.ComponentClassification.RankTwoClassical.coe_anisoRotGL hab1
  have hu3 : u ^ 3 = 1 :=
    CFSG.ComponentClassification.RankTwoClassical.anisoRotGL_pow_three hab1
  have hodd : Odd (orderOf u) :=
    Odd.of_dvd_nat (show Odd 3 by norm_num) (orderOf_dvd_of_pow_eq_one hu3)
  have huiso : u ∈ matrixIsometries Q := (mem_matrixIsometries_iff Q u).mpr fun v => by
    rw [matrixLinearEquiv_apply, hu_mat]
    exact CFSG.ComponentClassification.RankTwoClassical.anisoRot_isometry haQ hbQ hab1 v
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have huDer : u ∈ matrixDerived Q :=
    CFSG.ComponentClassification.HarrisLit.T1.P58b3D4.mem_matrixDerived_of_odd hnd hT huiso hodd
  have hV0Aorth : ∀ a ∈ A, ∀ z ∈ V0.orthogonalBilin B, glin a z ∈ V0.orthogonalBilin B :=
    fun a ha z hz =>
      CFSG.RankThree.PartOne.OddIso.orth_invariantH (hA.iso a ha) (hA.lin_pow ha) hp1 (hV0A a ha) hz
  have hu_orth : ∀ v ∈ V0.orthogonalBilin B, glin u v = v := by
    intro v hv
    rw [glin_apply, hu_mat, CFSG.ComponentClassification.RankTwoClassical.anisoRot_mulVec]
    have hva : Q.polarBilin v a = 0 := by
      have h := (Submodule.mem_orthogonalBilin.mp hv) a ha
      rwa [← hA.symm.eq v a] at h
    have hvb : Q.polarBilin v b = 0 := by
      have h := (Submodule.mem_orthogonalBilin.mp hv) b hb
      rwa [← hA.symm.eq v b] at h
    rw [hva, hvb, zero_smul, zero_smul, add_zero, add_zero]
  have huV0 : ∀ m ∈ V0, glin u m ∈ V0 := by
    intro m hm
    rw [glin_apply, hu_mat, CFSG.ComponentClassification.RankTwoClassical.anisoRot_mulVec]
    exact V0.add_mem (V0.add_mem hm (V0.smul_mem (Q.polarBilin m a) ha))
      (V0.smul_mem (Q.polarBilin m b) (V0.add_mem ha hb))
  have huX : ∀ v ∈ genPieceSpan S, glin u v = v := by
    intro v hv
    have hva : Q.polarBilin v a = 0 := by
      have h := (Submodule.mem_orthogonalBilin.mp (hXle hv)) a ha
      rwa [← hA.symm.eq v a] at h
    have hvb : Q.polarBilin v b = 0 := by
      have h := (Submodule.mem_orthogonalBilin.mp (hXle hv)) b hb
      rwa [← hA.symm.eq v b] at h
    rw [glin_apply, hu_mat, CFSG.ComponentClassification.RankTwoClassical.anisoRot_mulVec, hva,
      hvb, zero_smul, zero_smul, add_zero, add_zero]
  have hucomm : ∀ c ∈ A, u * c = c * u := by
    intro c hc
    apply glin_injective
    rw [glin_mul, glin_mul]
    refine LinearMap.ext fun v => ?_
    obtain ⟨m, hm, z, hz, rfl⟩ := SUTB.exists_add_orth hV0nd v
    have hcz : glin c z ∈ V0.orthogonalBilin B := hV0Aorth c hc z hz
    have hum : glin u m ∈ V0 := huV0 m hm
    have hL : (glin u * glin c) (m + z) = glin u m + glin c z := by
      rw [Module.End.mul_apply, map_add, hV0triv c hc m hm, map_add, hu_orth (glin c z) hcz]
    have hR : (glin c * glin u) (m + z) = glin u m + glin c z := by
      rw [Module.End.mul_apply, map_add, hu_orth z hz, map_add, hV0triv c hc (glin u m) hum]
    rw [hL, hR]
  have huA : u ∈ A := hA.max u huDer hu3 hucomm
  have hu1 : u = 1 := hterm u huA huX
  have hua : glin u a = b := by
    rw [glin_apply, hu_mat, CFSG.ComponentClassification.RankTwoClassical.anisoRot_mulVec, haa,
      hab1]
    simp only [zero_smul, one_smul, add_zero]
    rw [← add_assoc, CharTwo.add_self_eq_zero a, zero_add]
  have hne : b ≠ a := fun h => by
    have h1 : (1 : K) = 0 := by rw [← hab1, h, haa]
    exact one_ne_zero h1
  exact hne (by rw [← hua, hu1, glin_one]; rfl)

end CFSG.StandardType
