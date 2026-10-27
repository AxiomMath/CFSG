module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofOneField
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldTransfer
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldGL3Twisted
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
import CFSG.RankThree.PartOne.AUTSL.Interface
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

namespace HeringOF

theorem ringEquiv_eq_one_of_prime_card {F : Type} [Field F] [Finite F]
    (hp : (Nat.card F).Prime) (σ : F ≃+* F) : σ = 1 := by
  haveI := Fintype.ofFinite F
  have hc : Fintype.card F = Nat.card F := Nat.card_eq_fintype_card.symm
  let e : F ≃+* ZMod (Nat.card F) := (ZMod.ringEquivOfPrime F hp hc).symm
  have h1 : (e.toRingHom.comp (σ.toRingHom.comp e.symm.toRingHom)) = RingHom.id _ :=
    RingHom.ext_zmod _ _
  ext x
  have h2 := congrArg (fun f : ZMod (Nat.card F) →+* ZMod (Nat.card F) => f (e x)) h1
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply, RingHom.id_apply] at h2
  exact e.injective h2

theorem conjAut_eq_one_of_scalar {F : Type} [Field F] (A : GL (Fin 3) F) {b : F}
    (hb : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = b • (1 : Matrix (Fin 3) (Fin 3) F)) :
    conjAut 3 F A = 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h1 : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hb, zero_smul, Matrix.zero_mul] at h1
    exact zero_ne_one (congrFun (congrFun h1 0) 0)
  have hA : A = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 b hb0) := by
    apply Units.ext
    rw [hb, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
    rfl
  rw [hA]
  exact conjAut_scalar _

section Certs


theorem not_isType419_of_conjAut_fixed {F : Type} [Field F] [Finite F] (A : GL (Fin 3) F)
    (hA1 : conjAut 3 F A ≠ 1) (hA3 : conjAut 3 F (A ^ 3) = 1) {K : Type} [Group K]
    (hK : IsType419 K) (hs : IsSimpleGroup K) (hZ : Subgroup.center K = ⊥)
    (T : Subgroup (SpecialLinearGroup (Fin 3) F)) (θ : T →* K) (hθ : Function.Surjective θ)
    (hker : ∀ t : T, θ t = 1 → (t : SpecialLinearGroup (Fin 3) F) ∈ scalars 3 F)
    (hfix : ∀ t : T, conjAut 3 F A (proj 3 F t) = proj 3 F t) : False := by
  obtain ⟨u, hu⟩ := (ProjectivePlane.conjAut_eq_one_iff (le_refl (3 : ℕ)) (A ^ 3)).mp hA3
  have hA3m : ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have h2 := congrArg Units.val hu
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at h2
    exact h2
  have hAn : ∀ b : F, ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠
      b • (1 : Matrix (Fin 3) (Fin 3) F) := fun b hb => hA1 (conjAut_eq_one_of_scalar A hb)
  let ρ : T →* GL (Fin 3) F := SpecialLinearGroup.toGL.comp T.subtype
  have hρ : Function.Injective ρ :=
    SpecialLinearGroup.toGL_injective.comp (Subgroup.subtype_injective _)
  refine HeringOF.not_isType419_of_twisted_gl3 ρ hρ hK hs hZ θ hθ ?_ A u hA3m hAn ?_
  · intro t ht
    obtain ⟨c', -, hc'⟩ := hker t ht
    refine ⟨c', Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hc'
  · intro t
    have h1 := hfix t
    rw [conjAut_proj] at h1
    obtain ⟨c', -, hc'⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h1)
    refine ⟨c'⁻¹, ?_⟩
    set X := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      (t : SpecialLinearGroup (Fin 3) F) with hX
    have hXgl : (SpecialLinearGroup.toGL X : GL (Fin 3) F) =
        A * SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 3) F) * A⁻¹ := by
      apply Units.ext
      rw [SpecialLinearGroup.coe_GL_coe_matrix, hX, coe_slConjugation, Units.val_mul,
        Units.val_mul]
      rfl
    have h2 : SpecialLinearGroup.toGL (X⁻¹ * (t : SpecialLinearGroup (Fin 3) F)) =
        Matrix.GeneralLinearGroup.scalar (Fin 3) c' := by
      apply Units.ext
      rw [SpecialLinearGroup.coe_GL_coe_matrix, hc', Matrix.GeneralLinearGroup.coe_scalar]
    rw [map_mul, map_inv, hXgl] at h2
    change A * SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 3) F) * A⁻¹ =
      SpecialLinearGroup.toGL (t : SpecialLinearGroup (Fin 3) F) *
        Matrix.GeneralLinearGroup.scalar (Fin 3) c'⁻¹
    rw [map_inv, ← h2]
    group

end Certs

end HeringOF

namespace HeringOF

theorem isInnerAut_descendAut {n : ℕ} {F : Type} [Field F]
    {τ : MulAut (SpecialLinearGroup (Fin n) F)} (h : IsInnerAut τ) :
    IsInnerAut (descendAut n F τ) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨proj n F g, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective n F x
  rw [descendAut_proj]
  change proj n F (g * y * g⁻¹) = proj n F g * proj n F y * (proj n F g)⁻¹
  rw [map_mul, map_mul, map_inv]

section Certs


theorem k419OneFieldPSL_three {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsComponent L) {F : Type} [Field F] [Finite F]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 F) {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G))
    (hdiag : ¬ InducesOuterTheta a L ∨ InducesKindPSL 3 F L a .diagonal) {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))))
    (ht : IsType419 K) : False := by
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  obtain ⟨e', A, hA⟩ : ∃ (e' : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 F)
      (A : GL (Fin 3) F), conjAut 3 F A = inducedAutHom L e' ⟨a, haL⟩ := by
    rcases hdiag with hin | ⟨e', hx', hd⟩
    · have hinner : IsInnerAut (inducedAutHom L e ⟨a, haL⟩) := by
        by_contra h
        exact hin ((not_isInnerAut_inducedAutHom_iff L e haL).mp h)
      obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp
        ((stdPinnedPSL 3 F).isInnerDiagonal_of_isInnerAut hinner)
      exact ⟨e, A, hA⟩
    · obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hd.1
      exact ⟨e', A, hA⟩
  have hτ3 := inducedAutHom_pow_eq_one L e' haL ha3'
  have hA3 : conjAut 3 F (A ^ 3) = 1 := by rw [map_pow, hA]; exact hτ3
  have hA1 : conjAut 3 F A ≠ 1 := by
    intro h1
    apply haC
    refine Item419Res3.mem_centralizer_of_inducedAutHom_eq_one hL e' haL ?_
    rw [← hA, h1]
  obtain ⟨hs, hZ, ι, hι, hfix⟩ := HeringOF.exists_injective_fixSub haL hKle hKc ht e'
  let T : Subgroup (SpecialLinearGroup (Fin 3) F) := ι.range.comap (proj 3 F)
  let eι : K ≃* ι.range := MonoidHom.ofInjective hι
  let θ : T →* K := (eι.symm : ι.range →* K).comp
    (((proj 3 F).comp T.subtype).codRestrict ι.range fun t => t.2)
  refine HeringOF.not_isType419_of_conjAut_fixed A hA1 hA3 ht hs hZ T θ ?_ ?_ ?_
  · intro k
    obtain ⟨g, hg⟩ := proj_surjective 3 F (ι k)
    refine ⟨⟨g, ⟨k, hg.symm⟩⟩, ?_⟩
    change eι.symm ⟨proj 3 F g, _⟩ = k
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hg
  · intro t ht1
    have h1 : (⟨proj 3 F (t : SpecialLinearGroup (Fin 3) F), t.2⟩ : ι.range) = 1 := by
      have : eι.symm ⟨proj 3 F (t : SpecialLinearGroup (Fin 3) F), t.2⟩ = 1 := ht1
      exact (MulEquiv.map_eq_one_iff eι.symm).mp this
    exact proj_eq_one_iff.mp (congrArg Subtype.val h1)
  · intro t
    obtain ⟨k, hk⟩ := Subgroup.mem_comap.mp t.2
    rw [← hk, hA]
    exact Item426.mem_fixSub.mp (hfix k)

theorem k419OneFieldSL_three {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsComponent L) {F : Type} [Field F] [Finite F]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin 3) F) {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G))
    (hdiag : ¬ InducesOuterTheta a L ∨ InducesKindSL 3 F L a .diagonal) {K : Subgroup G}
    (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))))
    (ht : IsType419 K) : False := by
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  obtain ⟨e', A, hA⟩ : ∃ (e' : L ⧸ aschbacherSolvableCore 3 L ≃*
      SpecialLinearGroup (Fin 3) F) (A : GL (Fin 3) F),
      conjAut 3 F A = descendAut 3 F (inducedAutHom L e' ⟨a, haL⟩) := by
    rcases hdiag with hin | ⟨e', hx', hd⟩
    · have hinner : IsInnerAut (inducedAutHom L e ⟨a, haL⟩) := by
        by_contra h
        exact hin ((not_isInnerAut_inducedAutHom_iff L e haL).mp h)
      obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp
        ((stdPinnedPSL 3 F).isInnerDiagonal_of_isInnerAut
          (HeringOF.isInnerAut_descendAut hinner))
      exact ⟨e, A, hA⟩
    · obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hd.1
      exact ⟨e', A, hA⟩
  set τ := inducedAutHom L e' ⟨a, haL⟩ with hτ
  have hτ3 : τ ^ 3 = 1 := inducedAutHom_pow_eq_one L e' haL ha3'
  have hA3 : conjAut 3 F (A ^ 3) = 1 := by
    rw [map_pow, hA, ← map_pow, hτ3, map_one]
  have hA1 : conjAut 3 F A ≠ 1 := by
    intro h1
    apply haC
    refine Item419Res3.mem_centralizer_of_inducedAutHom_eq_one hL e' haL ?_
    rw [h1] at hA
    exact (CFSG.RankThree.PartOne.AUTSL.descendAut_injective (n := 3) (K := F) (le_refl 3))
      (by rw [map_one]; exact hA.symm)
  obtain ⟨hs, hZ, ι, hι, hfix⟩ := HeringOF.exists_injective_fixSub haL hKle hKc ht e'
  let eι : K ≃* ι.range := MonoidHom.ofInjective hι
  refine HeringOF.not_isType419_of_conjAut_fixed A hA1 hA3 ht hs hZ ι.range
    (eι.symm : ι.range →* K) eι.symm.surjective ?_ ?_
  · intro t ht1
    have h1 : t = 1 := (MulEquiv.map_eq_one_iff eι.symm).mp ht1
    rw [h1]
    exact one_mem _
  · intro t
    obtain ⟨k, hk⟩ := t.2
    rw [hA, ← hk, descendAut_proj, Item426.mem_fixSub.mp (hfix k)]

end Certs

end HeringOF

@[expose] def K419PinPSL : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 4 ≤ n → IsList46 (projectiveSL n F) →
    (Nat.card F).Prime

@[expose] def K419PinSL : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 4 ≤ n →
    IsList46 (SpecialLinearGroup (Fin n) F) → (Nat.card F).Prime

section Final


theorem k419OneFieldPSL_of_pin (hpin : K419PinPSL) : K419OneFieldPSL := by
  intro G _ _ L hL h46 n F _ _ hn x a hx3 hxa hxk haL ha3 haC hdiag K hKle hKc ht
  by_cases h3 : n = 3
  · subst h3
    obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 F) := by
      rcases hxk with ⟨e, -⟩ | ⟨e, -⟩ <;> exact ⟨e⟩
    exact HeringOF.k419OneFieldPSL_three hL e haL ha3 haC hdiag hKle hKc ht
  · have hn4 : 4 ≤ n := by omega
    obtain ⟨e, σ, hσ⟩ : ∃ (e : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL n F)
        (σ : F ≃+* F), σ ≠ 1 := by
      rcases hxk with ⟨e, hx, hk⟩ | ⟨e, hx, hk⟩
      · obtain ⟨φ, ⟨σ, rfl⟩, h1, -⟩ := hk
        exact ⟨e, σ, fun h => h1 (by rw [h, map_one])⟩
      · obtain ⟨γ, -, -, φ, ⟨σ, rfl⟩, h1, -⟩ := hk
        exact ⟨e, σ, fun h => h1 (by rw [h, map_one])⟩
    have hlist : IsList46 (projectiveSL n F) :=
      CFSG.RankThree.PartTwo.Sec21.Item223PrintProof.isList46_of_mulEquiv e h46
    exact hσ (HeringOF.ringEquiv_eq_one_of_prime_card (hpin n F hn4 hlist) σ)

theorem k419OneFieldSL_of_pin (hpin : K419PinSL) : K419OneFieldSL := by
  intro G _ _ L hL h46 n F _ _ hn x a hx3 hxa hxk haL ha3 haC hdiag K hKle hKc ht
  by_cases h3 : n = 3
  · subst h3
    obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin 3) F) := by
      rcases hxk with ⟨e, -⟩ | ⟨e, -⟩ <;> exact ⟨e⟩
    exact HeringOF.k419OneFieldSL_three hL e haL ha3 haC hdiag hKle hKc ht
  · have hn4 : 4 ≤ n := by omega
    obtain ⟨e, σ, hσ⟩ : ∃ (e : L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin n) F)
        (σ : F ≃+* F), σ ≠ 1 := by
      rcases hxk with ⟨e, hx, hk⟩ | ⟨e, hx, hk⟩
      · obtain ⟨φ, ⟨σ, rfl⟩, h1, -⟩ := hk
        exact ⟨e, σ, fun h => h1 (by rw [h, map_one])⟩
      · obtain ⟨γ, -, -, φ, ⟨σ, rfl⟩, h1, -⟩ := hk
        exact ⟨e, σ, fun h => h1 (by rw [h, map_one])⟩
    have hlist : IsList46 (SpecialLinearGroup (Fin n) F) :=
      CFSG.RankThree.PartTwo.Sec21.Item223PrintProof.isList46_of_mulEquiv e h46
    exact hσ (HeringOF.ringEquiv_eq_one_of_prime_card (hpin n F hn4 hlist) σ)

end Final

end CFSG.RankThree.PartTwo.Sec4
