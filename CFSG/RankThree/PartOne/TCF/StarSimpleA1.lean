module

public import CFSG.RankThree.PartOne.KLR.A1Twist
public import CFSG.RankThree.PartOne.TCF.Simple

public section

namespace CFSG.RankThree.PartOne.TCF

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLR

section Dyn

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] (D : ReeFrameData K L a)
  {i j : Fin ReeTag.F4.tag.rank}

open CFSG.RankThree.Classical (conjSL conjSL_one conjSL_mul)


theorem simpleOrBot_A1Pair [IsAlgClosed L] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (h : A1Pair i j) {n' : ModGL ReeTag.F4.tag L}
    (hn' : n' ∈ adjointGroup ReeTag.F4.tag L) {w' : WeylGroup ReeTag.F4.tag}
    (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) :
      Set (Fin ReeTag.F4.tag.rank)),
        w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag
          (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) :
    SimpleOrBot (rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n') := by
  classical
  have hα : IsRoot ReeTag.F4.tag (Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ i
  have hβ : IsRoot ReeTag.F4.tag (Pi.single j 1 : Fin ReeTag.F4.tag.rank → ℤ) :=
    isRoot_single _ j
  have hAB := h.commute_rankOne (L := L)
  have hdisj := h.disjoint (L := L)
  have hspan := h.rootSpan_eq (L := L)
  set A := rootRankOneGroup ReeTag.F4.tag L (Pi.single i 1) with hA
  set B := rootRankOneGroup ReeTag.F4.tag L (Pi.single j 1) with hB
  have hABle : A ⊔ B ≤ adjointGroup ReeTag.F4.tag L := by
    rw [← hspan]
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _
  have hmul : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B,
      twistMap D.F n' (x * y) = twistMap D.F n' x * twistMap D.F n' y :=
    fun x hx y hy => twistMap_mul n' (hABle hx) (hABle hy)
  have hφA := twistMap_mem_rankOne D hperm hα hβ (fun γ hγ => h.tau_long hstab hγ)
  have hφB := twistMap_mem_rankOne D hperm hβ hα (fun γ hγ => h.tau_short hstab hγ)
  obtain ⟨P₀, hX⟩ := h.exists_twist D hK hn' hperm hstab
  let R : Subgroup (SL2 L) :=
    (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P₀)
  let X : Subgroup (ModGL ReeTag.F4.tag L) :=
    R.map (rootSL2 ReeTag.F4.tag L (Pi.single i 1))
  have hρinj := rootSL2_injective_of_field (K := L) (τ := ReeTag.F4.tag) (Pi.single i 1)
  have hρadj : ∀ B₀ : SL2 L,
      rootSL2 ReeTag.F4.tag L (Pi.single i 1) B₀ ∈ adjointGroup ReeTag.F4.tag L := fun B₀ =>
    (hABle (Subgroup.mem_sup_left ⟨B₀, rfl⟩))
  have hXmem : ∀ x, x ∈ X ↔ x ∈ A ∧ twistMap D.F n' (twistMap D.F n' x) = x := by
    intro x
    constructor
    · rintro ⟨B₀, hB₀, rfl⟩
      refine ⟨⟨B₀, rfl⟩, ?_⟩
      rw [twistMap_twistMap D hn' (hρadj B₀)]
      exact (a1_hS1_of_action D.Frq D.Frq_pow P₀ hX B₀).2 hB₀
    · rintro ⟨⟨B₀, rfl⟩, hfix⟩
      refine ⟨B₀, ?_, rfl⟩
      rw [twistMap_twistMap D hn' (hρadj B₀)] at hfix
      exact (a1_hS1_of_action D.Frq D.Frq_pow P₀ hX B₀).1 hfix
  have hPmem : ∀ g, g ∈ rootSpan ReeTag.F4.tag L (parabolicRoots ReeTag.F4.tag
      (({i, j} : Finset (Fin ReeTag.F4.tag.rank)) : Set (Fin ReeTag.F4.tag.rank))) ⊓
        twistedFixed D.F n' ↔ g ∈ A ⊔ B ∧ twistMap D.F n' g = g := by
    intro g
    rw [hspan]
    constructor
    · rintro ⟨hg, -, hfix⟩
      exact ⟨hg, hfix⟩
    · rintro ⟨hg, hfix⟩
      exact ⟨hg, hABle hg, hfix⟩
  obtain ⟨Θ, hΘinj, hΘr⟩ := fixed_swap hAB hdisj (twistMap D.F n') hmul hφA hφB X hXmem _ hPmem
  have hsimple : IsSimpleGroup (SL2 K) :=
    CFSG.LieType.Ree.LargeReeInvolution.isSimpleGroup_SL2 ha hK
  have hns : ¬ Group.IsSolvable (SL2 K) := by
    obtain ⟨x, y, hxy⟩ := CFSG.LieType.Ree.LargeReeInvolution.exists_SL2_mul_ne_mul (K := K)
    intro hs
    exact hxy ((IsSimpleGroup.comm_iff_isSolvable.2 hs) x y)
  have hSLinj :
      Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap K L)) := by
    intro A₀ B₀ hAB₀
    ext i₀ j₀
    have h1 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) L =>
      (X : Matrix (Fin 2) (Fin 2) L) i₀ j₀) hAB₀
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K L).injective h1
  have hconjinj : Function.Injective (conjSL P₀) := fun A₀ B₀ hAB₀ => by
    have h1 := congrArg (conjSL P₀⁻¹) hAB₀
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  let e1 : SL2 K ≃* R := (MonoidHom.ofInjective hSLinj).trans
    (Subgroup.equivMapOfInjective _ (conjSL P₀) hconjinj)
  let e2 : R ≃* X := Subgroup.equivMapOfInjective R (rootSL2 ReeTag.F4.tag L (Pi.single i 1)) hρinj
  let e3 : X ≃* Θ.range := MonoidHom.ofInjective hΘinj
  let e4 := MulEquiv.subgroupCongr hΘr
  exact simpleOrBot_of_mulEquiv_simple hns (e1.trans (e2.trans (e3.trans e4)))


end Dyn

end CFSG.RankThree.PartOne.TCF
