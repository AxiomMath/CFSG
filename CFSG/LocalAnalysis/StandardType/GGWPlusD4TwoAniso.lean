module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityRank
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaGenFrame
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoPieces
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4TwoPlanes
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MPlane
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.TwistedConfig

public section

namespace CFSG.StandardType

open Module CFSG.Assembly CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open QuadraticMap CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4
  CFSG.LocalAnalysis.GLTheoremA.H81Orth

private lemma isPlusType_coordinateQuadPlus_four (K : Type) [Field K] [Finite K] :
    IsPlusType (coordinateQuadPlus 4 K) :=
  (isPlusType_congr (coordinatePlusIsometry 4 K)).1 (isPlusType_quadPlus K 4)

private noncomputable def topIsometry {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) :
    (Q.comp (⊤ : Submodule K V).subtype).IsometryEquiv Q where
  toLinearEquiv := Submodule.topEquiv
  map_app' _ := rfl

private lemma nondeg_comp_of_nondegOn {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {S : Submodule K V}
    (h : SUTB.NondegOn (QuadraticMap.polarBilin Q) S) :
    (polarBilin (Q.comp S.subtype)).Nondegenerate := by
  refine nondeg_comp_subtype' (Q := Q) (S := S) ?_
  intro x hx hxy
  exact h x hx fun z hz => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hxy z hz

private lemma disjoint_of_orth_of_nondegOn {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A B : Submodule K V}
    (hA : SUTB.NondegOn (QuadraticMap.polarBilin Q) A)
    (horth : ∀ a ∈ A, ∀ b ∈ B, polar Q a b = 0) : Disjoint A B := by
  rw [Submodule.disjoint_def]
  intro z hzA hzB
  exact hA z hzA fun n hn => by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact horth n hn z hzB

private lemma no_root_sq_add_sq {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (h3 : (3 : K) ≠ 0) : ¬ ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  rintro ⟨ω, hω⟩
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  have hx : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr ((hu x hx0).trans (hu 1 one_ne_zero).symm)
  rcases hx ω with rfl | rfl
  · exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using hω)
  · exact h3 (by rw [show (3 : K) = 1 ^ 2 + 1 + 1 by norm_num]; exact hω)

private lemma not_isPlusType_grng {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hA : GenMax (polB (coordinateQuadPlus 4 K)) (matrixDerived (coordinateQuadPlus 4 K)) 3 A)
    {y : GL (Fin (2 * 4)) K} (hy : y ∈ A) (hW2 : finrank K (grng y) = 2) :
    ¬ IsPlusType ((coordinateQuadPlus 4 K).comp (grng y).subtype) := by
  let T : Module.End K (Fin (2 * 4) → K) := glin y
  have h3 : (3 : K) ≠ 0 := hA.natCast_ne_zero
  have hT : ∀ x ∈ grng y, T (T x) + T x + x = 0 := by
    intro x hx
    have hx1 : T x ∈ grng y := grng_inv hA hy hy x hx
    have hx2 : T (T x) ∈ grng y := grng_inv hA hy hy (T x) hx1
    let W : Module.End K (Fin (2 * 4) → K) := T ^ 2 + T + 1
    have hWx : W x = T (T x) + T x + x := by
      dsimp only [W]
      simp [pow_two, Module.End.mul_apply, Module.End.one_apply]
    have hw : W x ∈ grng y := by
      rw [hWx]
      exact Submodule.add_mem _ (Submodule.add_mem _ hx2 hx1) hx
    have hfix : T (W x) = W x := by
      have hTW : T * W = W := by
        have h3p : T ^ 3 = 1 := hA.lin_pow hy
        dsimp only [W]
        rw [mul_add, mul_add, mul_one, ← pow_succ', ← pow_two, h3p]
        abel
      have h2 : (T * W) x = W x := by rw [hTW]
      rwa [Module.End.mul_apply] at h2
    have h0 := eq_zero_of_mem_grng hA hy hw hfix
    rwa [hWx] at h0
  have hTQ : ∀ x : Fin (2 * 4) → K, coordinateQuadPlus 4 K (T x) = coordinateQuadPlus 4 K x := by
    intro x
    have hyI : y ∈ matrixIsometries (coordinateQuadPlus 4 K) :=
      matrixDerived_le_isometries (coordinateQuadPlus 4 K) (hA.le hy)
    change coordinateQuadPlus 4 K (glin y x) = coordinateQuadPlus 4 K x
    rw [glin_apply, ← matrixLinearEquiv_apply]
    exact (mem_matrixIsometries_iff (coordinateQuadPlus 4 K) y).mp hyI x
  have hnd : ∀ x ∈ grng y,
      (∀ z ∈ grng y, polar (coordinateQuadPlus 4 K) x z = 0) → x = 0 := by
    intro x hx h
    exact nondegOn_grng hA hy x hx fun z hz => by
      rw [polB_apply, QuadraticMap.polar_comm]
      exact h z hz
  have hiff := plane_plus_iff (Q := coordinateQuadPlus 4 K) (W := grng y) h3 hW2
    (T := T) (fun x hx => grng_inv hA hy hy x hx) hT hTQ hnd
  intro hplus
  exact no_root_sq_add_sq hK h3 (hiff.mp hplus)

theorem genMax_complement_anisotropic_of_card_27 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {A : Subgroup (GL (Fin (2 * 4)) K)}
    (hA : GenMax (polB (coordinateQuadPlus 4 K)) (matrixDerived (coordinateQuadPlus 4 K)) 3 A)
    {S : Finset (GL (Fin (2 * 4)) K)} (hS : GenPieceSet (polB (coordinateQuadPlus 4 K)) A S)
    (hterm : ∀ c ∈ A, (∀ v ∈ genPieceSpan S, glin c v = v) → c = 1) (hcard : Nat.card A = 27) :
    ∀ v ∈ (genPieceSpan S).orthogonalBilin (polB (coordinateQuadPlus 4 K)), v ≠ 0 →
      coordinateQuadPlus 4 K v ≠ 0 := by
  classical
  let Q : QuadraticForm K (Fin (2 * 4) → K) := coordinateQuadPlus 4 K
  let B : (Fin (2 * 4) → K) →ₛₗ[RingHom.id K] (Fin (2 * 4) → K) →ₗ[K] K := polB Q
  change ∀ v ∈ (genPieceSpan S).orthogonalBilin B, v ≠ 0 → Q v ≠ 0
  obtain ⟨hScard, hpieces, hV0fr⟩ := genMax_pieces_planes_of_card_27 hK hA hS hterm hcard
  obtain ⟨y₁, y₂, y₃, hy₁₂, hy₁₃, hy₂₃, hSeq⟩ := Finset.card_eq_three.mp hScard
  have hy₁ : y₁ ∈ S := by rw [hSeq]; simp
  have hy₂ : y₂ ∈ S := by rw [hSeq]; simp
  have hy₃ : y₃ ∈ S := by rw [hSeq]; simp
  have hy₁A : y₁ ∈ A := hS.mem y₁ hy₁
  have hy₂A : y₂ ∈ A := hS.mem y₂ hy₂
  have hy₃A : y₃ ∈ A := hS.mem y₃ hy₃
  have hspan : genPieceSpan S = grng y₁ ⊔ grng y₂ ⊔ grng y₃ := by
    rw [genPieceSpan, hSeq]
    rw [Finset.iSup_insert, Finset.iSup_insert, Finset.iSup_singleton]
    rw [sup_assoc]
  have hXnd : SUTB.NondegOn B (genPieceSpan S) := (GenPieceSet.nondegOn_card hA hS).1
  have hP₁d : finrank K (grng y₁) = 2 := hpieces y₁ hy₁
  have hP₂d : finrank K (grng y₂) = 2 := hpieces y₂ hy₂
  have hP₃d : finrank K (grng y₃) = 2 := hpieces y₃ hy₃
  have hnotP₁ : ¬ IsPlusType (Q.comp (grng y₁).subtype) :=
    not_isPlusType_grng hK hA hy₁A hP₁d
  have hnotP₂ : ¬ IsPlusType (Q.comp (grng y₂).subtype) :=
    not_isPlusType_grng hK hA hy₂A hP₂d
  have hnotP₃ : ¬ IsPlusType (Q.comp (grng y₃).subtype) :=
    not_isPlusType_grng hK hA hy₃A hP₃d
  have hP₁n : (polarBilin (Q.comp (grng y₁).subtype)).Nondegenerate :=
    nondeg_comp_of_nondegOn (nondegOn_grng hA hy₁A)
  have hP₂n : (polarBilin (Q.comp (grng y₂).subtype)).Nondegenerate :=
    nondeg_comp_of_nondegOn (nondegOn_grng hA hy₂A)
  have hP₃n : (polarBilin (Q.comp (grng y₃).subtype)).Nondegenerate :=
    nondeg_comp_of_nondegOn (nondegOn_grng hA hy₃A)
  have horth₁₂ : ∀ a ∈ grng y₁, ∀ b ∈ grng y₂, polar Q a b = 0 := by
    intro a ha b hb
    simpa [polB_apply] using hS.orth y₁ hy₁ y₂ hy₂ hy₁₂ a ha b hb
  have horth₁₃ : ∀ a ∈ grng y₁, ∀ b ∈ grng y₃, polar Q a b = 0 := by
    intro a ha b hb
    simpa [polB_apply] using hS.orth y₁ hy₁ y₃ hy₃ hy₁₃ a ha b hb
  have horth₂₃ : ∀ a ∈ grng y₂, ∀ b ∈ grng y₃, polar Q a b = 0 := by
    intro a ha b hb
    simpa [polB_apply] using hS.orth y₂ hy₂ y₃ hy₃ hy₂₃ a ha b hb
  have horth₂₁ : ∀ u ∈ grng y₂, ∀ v ∈ grng y₁, polB Q u v = 0 ∧ polB Q v u = 0 := by
    intro u hu v hv
    refine ⟨?_, ?_⟩
    · rw [polB_apply, QuadraticMap.polar_comm]
      exact horth₁₂ v hv u hu
    · rw [polB_apply]
      exact horth₁₂ v hv u hu
  have hdisj₁₂ : Disjoint (grng y₁) (grng y₂) :=
    disjoint_of_orth_of_nondegOn (nondegOn_grng hA hy₁A) horth₁₂
  have hplus₁₂ : IsPlusType (Q.comp (grng y₁ ⊔ grng y₂).subtype) := by
    rw [isPlusType_sup_iff' (Q := Q) hdisj₁₂ horth₁₂ hP₁n hP₂n (d₁ := 1) (d₂ := 1)
      le_rfl le_rfl (by simpa using hP₁d) (by simpa using hP₂d)]
    exact iff_of_false hnotP₁ hnotP₂
  have hP₁₂d : finrank K (grng y₁ ⊔ grng y₂ : Submodule K (Fin (2 * 4) → K)) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (grng y₁) (grng y₂)
    rw [hdisj₁₂.eq_bot, finrank_bot, add_zero] at h
    rw [h, hP₁d, hP₂d]
  have hP₁₂nd : SUTB.NondegOn B (grng y₁ ⊔ grng y₂) :=
    SUTB.nondegOn_sup (nondegOn_grng hA hy₁A) (nondegOn_grng hA hy₂A) horth₂₁
  have hP₁₂n : (polarBilin (Q.comp (grng y₁ ⊔ grng y₂).subtype)).Nondegenerate :=
    nondeg_comp_of_nondegOn hP₁₂nd
  have horth₁₂₃ : ∀ a ∈ grng y₁ ⊔ grng y₂, ∀ b ∈ grng y₃, polar Q a b = 0 := by
    intro a ha b hb
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp ha
    rw [QuadraticMap.polar_add_left, horth₁₃ a₁ ha₁ b hb, horth₂₃ a₂ ha₂ b hb, add_zero]
  have hdisj₁₂₃ : Disjoint (grng y₁ ⊔ grng y₂) (grng y₃) :=
    disjoint_of_orth_of_nondegOn hP₁₂nd horth₁₂₃
  have hnotP₁₂₃ : ¬ IsPlusType (Q.comp ((grng y₁ ⊔ grng y₂) ⊔ grng y₃).subtype) := by
    intro h
    rw [isPlusType_sup_iff' (Q := Q) hdisj₁₂₃ horth₁₂₃ hP₁₂n hP₃n (d₁ := 2) (d₂ := 1)
      (by norm_num) le_rfl (by simpa using hP₁₂d) (by simpa using hP₃d)] at h
    exact hnotP₃ (h.mp hplus₁₂)
  have hnotX : ¬ IsPlusType (Q.comp (genPieceSpan S).subtype) := by
    rw [hspan]
    exact hnotP₁₂₃
  have hXn : (polarBilin (Q.comp (genPieceSpan S).subtype)).Nondegenerate :=
    nondeg_comp_of_nondegOn hXnd
  have hXfr : finrank K (genPieceSpan S) = 6 := by
    have hcompl := CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hXnd
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq (genPieceSpan S)
      ((genPieceSpan S).orthogonalBilin B)
    rw [hcompl.inf_eq_bot, finrank_bot, add_zero, hcompl.sup_eq_top, finrank_top] at hfr
    have hV : finrank K (Fin (2 * 4) → K) = 8 := by simp
    rw [hV] at hfr
    have h2 : finrank K ((genPieceSpan S).orthogonalBilin B) = 2 := hV0fr
    omega
  have hV₀nd : SUTB.NondegOn B ((genPieceSpan S).orthogonalBilin B) := by
    have hsymm : ∀ x y : Fin (2 * 4) → K, B x y = B y x := fun x y => hA.symm.eq x y
    intro v hv h
    apply hA.sep
    intro w
    obtain ⟨m, hm, z, hz, rfl⟩ := SUTB.exists_add_orth hXnd w
    have hvm : B v m = 0 := by
      rw [hsymm]
      exact (Submodule.mem_orthogonalBilin.mp hv) m hm
    have hvz : B v z = 0 := by
      rw [hsymm]
      exact h z hz
    rw [map_add, hvm, hvz, add_zero]
  have hV₀n : (polarBilin (Q.comp ((genPieceSpan S).orthogonalBilin B).subtype)).Nondegenerate :=
    nondeg_comp_of_nondegOn hV₀nd
  have horthV₀X : ∀ a ∈ (genPieceSpan S).orthogonalBilin B, ∀ b ∈ genPieceSpan S,
      polar Q a b = 0 := by
    intro a ha b hb
    have h := (Submodule.mem_orthogonalBilin.mp ha) b hb
    rw [polB_apply] at h
    rwa [QuadraticMap.polar_comm]
  have hdisjV₀X : Disjoint ((genPieceSpan S).orthogonalBilin B) (genPieceSpan S) :=
    disjoint_of_orth_of_nondegOn hV₀nd horthV₀X
  have hnotV₀ : ¬ IsPlusType (Q.comp ((genPieceSpan S).orthogonalBilin B).subtype) := by
    have htop : IsPlusType (Q.comp (((genPieceSpan S).orthogonalBilin B) ⊔
        genPieceSpan S).subtype) := by
      have hcompl := CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hXnd
      have hsup : ((genPieceSpan S).orthogonalBilin B) ⊔ genPieceSpan S = ⊤ := by
        rw [sup_comm]
        exact hcompl.sup_eq_top
      rw [hsup]
      exact (isPlusType_congr (topIsometry Q)).2 (isPlusType_coordinateQuadPlus_four K)
    rw [isPlusType_sup_iff' (Q := Q) hdisjV₀X horthV₀X hV₀n hXn (d₁ := 1) (d₂ := 3)
      le_rfl (by norm_num) (by simpa using hV0fr) (by simpa using hXfr)] at htop
    intro h
    exact hnotX (htop.mp h)
  intro v hv hv0 hQv
  have hz : (⟨v, hv⟩ : ↥((genPieceSpan S).orthogonalBilin B)) = 0 :=
    eq_zero_of_not_isPlusType (K := K) (U := ↥((genPieceSpan S).orthogonalBilin B))
      (QU := Q.comp ((genPieceSpan S).orthogonalBilin B).subtype) hV0fr hnotV₀ hQv
  exact hv0 (congrArg Subtype.val hz)

end CFSG.StandardType
