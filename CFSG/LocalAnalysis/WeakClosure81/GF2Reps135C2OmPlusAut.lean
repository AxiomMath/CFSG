module

public import CFSG.RankThree.GF2n.Smith81.S81QGraphCl
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutSim
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusModel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module
open CliffordAlgebra
open CFSG.LieType.Universal.Spin
open CFSG.RankThree.GF2n.Smith81.D6Spin (graphSpin swapLin swapLin_apply swapIso swapIso_apply
  swapIso_swapIso quadPlus_swapLin coe_spinAutOfInvol)
open CFSG.RankThree.OrthogonalInvolutions

theorem spinAction_graphSpin {n : ℕ} {K : Type} [Field K] (i₀ : Fin n)
    (g : spinGroup (quadPlus n K)) (v : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K) (graphSpin n K i₀ g) v =
      swapLin n K i₀ (spinAction (quadPlus n K) g (swapLin n K i₀ v)) := by
  apply ι_injective' (Q := quadPlus n K)
  rw [ι_spinAction]
  have hcoe : ((graphSpin n K i₀ g : spinGroup (quadPlus n K)) :
      CliffordAlgebra (quadPlus n K)) =
      CliffordAlgebra.map (swapIso n K i₀) (↑g : CliffordAlgebra (quadPlus n K)) := by
    simp only [graphSpin, coe_spinAutOfInvol]
  have hcoe_inv : (((graphSpin n K i₀ g)⁻¹ : spinGroup (quadPlus n K)) :
      CliffordAlgebra (quadPlus n K)) =
      CliffordAlgebra.map (swapIso n K i₀) (↑(g⁻¹) : CliffordAlgebra (quadPlus n K)) := by
    rw [(map_inv (graphSpin n K i₀) g).symm]
    simp only [graphSpin, coe_spinAutOfInvol]
  rw [hcoe, hcoe_inv]
  set w := spinAction (quadPlus n K) g (swapLin n K i₀ v)
  have hmap : CliffordAlgebra.map (swapIso n K i₀) (ι (quadPlus n K) w) =
      ι (quadPlus n K) (swapLin n K i₀ w) := by
    rw [CliffordAlgebra.map_apply_ι, swapIso_apply]
  rw [← hmap]
  rw [ι_spinAction]
  simp only [map_mul, CliffordAlgebra.map_apply_ι]
  rw [← swapIso_apply n K i₀ v, swapIso_swapIso]

private noncomputable def omPlusAutEquiv {n : ℕ} (hn : 3 ≤ n) (F : Type) [Field F] [CharP F 2] :
    spinGroup (quadPlus n F) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)) :=
  MulEquiv.ofBijective (spinToStatedProj (quadPlus n F) (range_spinMatrix_quadPlus hn))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
        rw [ker_spinToStatedProj_eq_center (quadPlus n F) (range_spinMatrix_quadPlus hn)
          (center_statedOmega_quadPlus hn)
          (exists_map_ne_zero_of_hypPair (quadPlus n F)
            (CFSG.ClassicalGroups.Orthogonal.plusPair F (⟨0, by omega⟩ : Fin n)))]
        exact CFSG.StandardType.RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo
          (n := n) (K := F) hn),
      spinToStatedProj_surjective _ _⟩

private theorem omPlusAutEquiv_coe {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [CharP F 2]
    (x : spinGroup (quadPlus n F)) :
    omPlusAutEquiv hn F x = QuotientGroup.mk (⟨spinMatrix (quadPlus n F) x,
      spinMatrix_mem_of_range_eq (quadPlus n F) (range_spinMatrix_quadPlus hn) x⟩ :
        CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)) := by
  rw [show omPlusAutEquiv hn F x =
      spinToStatedProj (quadPlus n F) (range_spinMatrix_quadPlus hn) x from rfl,
    spinToStatedProj_apply]

noncomputable def omPlusAutGlLin (ι : Type) [Fintype ι] [DecidableEq ι] (F : Type)
    [Field F] : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  (Matrix.GeneralLinearGroup.toLin).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))

theorem omPlusAutGlLin_apply {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (A : GL ι F) (v : ι → F) : omPlusAutGlLin ι F A v = A.val *ᵥ v := by
  simp [omPlusAutGlLin]

theorem omPlusAutGlLin_spinMatrix {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (Q : QuadraticForm F (ι → F)) (x : spinGroup Q) :
    omPlusAutGlLin ι F (spinMatrix Q x) = spinAction Q x := by
  ext v
  rw [omPlusAutGlLin_apply, spinMatrix_mulVec]

theorem omPlusAut_smul_swapLin_sub_eq {n : ℕ} (F : Type) [Field F] (i₀ : Fin n)
    (v : Fin n ⊕ Fin n → F) :
    (v (Sum.inr i₀) - v (Sum.inl i₀)) •
      (Pi.single (Sum.inl i₀) (1 : F) - Pi.single (Sum.inr i₀) (1 : F)) =
      swapLin n F i₀ v - v := by
  funext a
  rcases a with i | i
  · by_cases hi : i = i₀
    · subst hi
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, swapLin_apply, Equiv.swap_apply_left,
        Pi.single_eq_same, Pi.single_eq_of_ne Sum.inl_ne_inr, sub_zero, mul_one]
    · have h1 : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := fun h => hi (Sum.inl_injective h)
      have h3 : (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr i₀ := Sum.inl_ne_inr
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, swapLin_apply,
        Equiv.swap_apply_of_ne_of_ne h1 h3, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h3,
        sub_self, mul_zero]
  · by_cases hi : i = i₀
    · subst hi
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, swapLin_apply, Equiv.swap_apply_right,
        Pi.single_eq_same, Pi.single_eq_of_ne Sum.inr_ne_inl]
      ring
    · have h2 : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := Sum.inr_ne_inl
      have h4 : (Sum.inr i : Fin n ⊕ Fin n) ≠ Sum.inr i₀ := fun h => hi (Sum.inr_injective h)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, swapLin_apply,
        Equiv.swap_apply_of_ne_of_ne h2 h4, Pi.single_eq_of_ne h2, Pi.single_eq_of_ne h4,
        sub_self, mul_zero]

theorem omPlusAut_finrank_commSpace_swapLin {n : ℕ} (F : Type) [Field F] (i₀ : Fin n) :
    finrank F (commSpace (swapLin n F i₀)) = 1 := by
  set e : Fin n ⊕ Fin n → F :=
    Pi.single (Sum.inl i₀) (1 : F) - Pi.single (Sum.inr i₀) (1 : F) with he
  have he_ne : e ≠ 0 := by
    intro h
    have h1 : e (Sum.inl i₀) = 0 := by rw [h]; rfl
    rw [he] at h1
    simp at h1
  have hle : commSpace (swapLin n F i₀) ≤ F ∙ e := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    rw [Submodule.mem_span_singleton]
    refine ⟨v (Sum.inr i₀) - v (Sum.inl i₀), ?_⟩
    rw [he]
    exact omPlusAut_smul_swapLin_sub_eq F i₀ v
  have he_mem : e ∈ commSpace (swapLin n F i₀) := by
    have h := omPlusAut_smul_swapLin_sub_eq F i₀ (Pi.single (Sum.inr i₀) (1 : F))
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne Sum.inl_ne_inr, sub_zero, one_smul] at h
    rw [he, h]
    exact sub_mem_commSpace _ _
  have hspan : F ∙ e ≤ commSpace (swapLin n F i₀) :=
    (Submodule.span_singleton_le_iff_mem e _).mpr he_mem
  rw [le_antisymm hle hspan, finrank_span_singleton he_ne]

theorem omPlusAut_glFieldEquiv_refl {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (g : GL ι F) :
    CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
      ι (RingEquiv.refl F) g = g := by
  apply Units.ext
  ext i j
  exact CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv_entry
    ι (RingEquiv.refl F) g i j

private theorem omPlusAut_apply_eq_of_conj {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (hn3 : 3 ≤ n) {α : MulAut (spinGroup (quadPlus n F))}
    {E : spinGroup (quadPlus n F) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F))}
    {β : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)))}
    (hE : E = omPlusAutEquiv hn3 F)
    (hβ : ∀ x, β x = E (α (E.symm x)))
    {h g k : spinGroup (quadPlus n F)}
    {y : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)}
    (hy : (y : GL (Fin n ⊕ Fin n) F) = spinMatrix (quadPlus n F) (h * k * h⁻¹))
    (hybeta : β (QuotientGroup.mk ⟨spinMatrix (quadPlus n F) g,
      spinMatrix_mem_of_range_eq (quadPlus n F) (range_spinMatrix_quadPlus hn3) g⟩) =
      QuotientGroup.mk y) :
    α g = h * k * h⁻¹ := by
  have hmem : spinMatrix (quadPlus n F) g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F) :=
    spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn3) g
  have hEy : QuotientGroup.mk y = E (h * k * h⁻¹) := by
    rw [hE, omPlusAutEquiv_coe hn3]
    exact congrArg QuotientGroup.mk (Subtype.ext hy)
  have hEg : E g = QuotientGroup.mk ⟨spinMatrix (quadPlus n F) g, hmem⟩ := by
    rw [hE, omPlusAutEquiv_coe (F := F) hn3]
  have hβ' : β (E g) = E (α g) := by
    rw [hβ (E g), MulEquiv.symm_apply_apply]
  apply E.injective
  calc E (α g) = β (E g) := hβ'.symm
    _ = β (QuotientGroup.mk ⟨spinMatrix (quadPlus n F) g, hmem⟩) := congrArg β hEg
    _ = QuotientGroup.mk y := hybeta
    _ = E (h * k * h⁻¹) := hEy

private theorem omPlusAut_inner_case {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (hn3 : 3 ≤ n) {α : MulAut (spinGroup (quadPlus n F))}
    {E : spinGroup (quadPlus n F) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F))}
    {β : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)))}
    (hE : E = omPlusAutEquiv hn3 F)
    (hβ : ∀ x, β x = E (α (E.symm x)))
    {A : GL (Fin n ⊕ Fin n) F} {φ : F ≃+* F} (hφ : φ = RingEquiv.refl F)
    {h : spinGroup (quadPlus n F)}
    (hh : spinAction (quadPlus n F) h = omPlusAutGlLin (Fin n ⊕ Fin n) F A)
    (hconj : ∀ x : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F),
      ∃ y : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F),
        (y : GL (Fin n ⊕ Fin n) F) =
          A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
            (Fin n ⊕ Fin n) φ (x : GL (Fin n ⊕ Fin n) F) * A⁻¹ ∧
        β (QuotientGroup.mk x) = QuotientGroup.mk y) :
    ∀ g, α g = h * g * h⁻¹ := by
  intro g
  have hmem : spinMatrix (quadPlus n F) g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F) :=
    spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn3) g
  obtain ⟨y, hyval, hybeta⟩ := hconj ⟨spinMatrix (quadPlus n F) g, hmem⟩
  have hAeq : spinMatrix (quadPlus n F) h = A := by
    apply (omPlusAutGlLin (Fin n ⊕ Fin n) F).injective
    rw [omPlusAutGlLin_spinMatrix, hh]
  have hy : (y : GL (Fin n ⊕ Fin n) F) = spinMatrix (quadPlus n F) (h * g * h⁻¹) := by
    rw [hyval, hφ, omPlusAut_glFieldEquiv_refl, ← hAeq, ← map_inv, ← map_mul, ← map_mul]
  exact omPlusAut_apply_eq_of_conj hn3 hE hβ hy hybeta

private theorem omPlusAut_graph_case {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (hn3 : 3 ≤ n) {α : MulAut (spinGroup (quadPlus n F))}
    {E : spinGroup (quadPlus n F) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F))}
    {β : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)))}
    (hE : E = omPlusAutEquiv hn3 F)
    (hβ : ∀ x, β x = E (α (E.symm x)))
    {A : GL (Fin n ⊕ Fin n) F} {φ : F ≃+* F} (hφ : φ = RingEquiv.refl F)
    {h : spinGroup (quadPlus n F)} (i₀ : Fin n) {R : GL (Fin n ⊕ Fin n) F}
    (hAeq : A = spinMatrix (quadPlus n F) h * R)
    (hRg : ∀ g, R * spinMatrix (quadPlus n F) g * R =
      spinMatrix (quadPlus n F) (graphSpin n F i₀ g))
    (hRinv : R⁻¹ = R)
    (hconj : ∀ x : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F),
      ∃ y : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F),
        (y : GL (Fin n ⊕ Fin n) F) =
          A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
            (Fin n ⊕ Fin n) φ (x : GL (Fin n ⊕ Fin n) F) * A⁻¹ ∧
        β (QuotientGroup.mk x) = QuotientGroup.mk y) :
    ∀ g, α g = h * graphSpin n F i₀ g * h⁻¹ := by
  intro g
  have hmem : spinMatrix (quadPlus n F) g ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F) :=
    spinMatrix_mem_of_range_eq _ (range_spinMatrix_quadPlus hn3) g
  obtain ⟨y, hyval, hybeta⟩ := hconj ⟨spinMatrix (quadPlus n F) g, hmem⟩
  have hy : (y : GL (Fin n ⊕ Fin n) F) =
      spinMatrix (quadPlus n F) (h * graphSpin n F i₀ g * h⁻¹) := by
    calc (y : GL (Fin n ⊕ Fin n) F)
        = A * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldEquiv
            (Fin n ⊕ Fin n) φ (spinMatrix (quadPlus n F) g) * A⁻¹ := hyval
      _ = A * spinMatrix (quadPlus n F) g * A⁻¹ := by
            rw [hφ, omPlusAut_glFieldEquiv_refl]
      _ = (spinMatrix (quadPlus n F) h * R) * spinMatrix (quadPlus n F) g *
            (spinMatrix (quadPlus n F) h * R)⁻¹ := by rw [hAeq]
      _ = spinMatrix (quadPlus n F) h * (R * spinMatrix (quadPlus n F) g * R) *
            (spinMatrix (quadPlus n F) h)⁻¹ := by
            rw [_root_.mul_inv_rev, hRinv]; group
      _ = spinMatrix (quadPlus n F) h * spinMatrix (quadPlus n F) (graphSpin n F i₀ g) *
            (spinMatrix (quadPlus n F) h)⁻¹ := by rw [hRg g]
      _ = spinMatrix (quadPlus n F) (h * graphSpin n F i₀ g * h⁻¹) := by
            conv_lhs => rw [← map_mul]
            conv_rhs => rw [map_mul, map_inv]
  exact omPlusAut_apply_eq_of_conj hn3 hE hβ hy hybeta

theorem omPlusAut_field_triv {F : Type} [Field F] (hF : Nat.card F = 2) :
    (∀ x : F, x = 0 ∨ x = 1) ∧ (∀ μ : Fˣ, (μ : F) = 1) ∧
      (∀ φ : F ≃+* F, φ = RingEquiv.refl F) := by
  have hcard : ∀ x : F, x = 0 ∨ x = 1 := fun x => by
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr (by rw [huniq x hx, ← huniq 1 one_ne_zero])
  refine ⟨hcard, fun μ => ?_, fun φ => ?_⟩
  · rcases hcard (μ : F) with h | h
    · exact absurd h μ.ne_zero
    · exact h
  · refine RingEquiv.ext fun x => ?_
    rcases hcard x with h | h
    · rw [h, map_zero, RingEquiv.refl_apply]
    · rw [h, map_one, RingEquiv.refl_apply]

theorem omPlusAut_graph_swapGL {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {A : GL (Fin n ⊕ Fin n) F}
    {gA : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hgA : gA = omPlusAutGlLin (Fin n ⊕ Fin n) F A) {i₀ : Fin n}
    {h : spinGroup (quadPlus n F)} (hh : spinAction (quadPlus n F) h = gA * swapLin n F i₀)
    {r : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} (hr : r = swapLin n F i₀) :
    ∃ (R : GL (Fin n ⊕ Fin n) F),
      A = spinMatrix (quadPlus n F) h * R ∧
      (∀ g, R * spinMatrix (quadPlus n F) g * R =
        spinMatrix (quadPlus n F) (graphSpin n F i₀ g)) ∧
      R⁻¹ = R := by
  set R : GL (Fin n ⊕ Fin n) F := (omPlusAutGlLin (Fin n ⊕ Fin n) F).symm r with hR
  have hRr : omPlusAutGlLin (Fin n ⊕ Fin n) F R = r := by
    rw [hR]; exact MulEquiv.apply_symm_apply _ _
  have hrr : r * r = 1 := by
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, hr]
    exact swapIso_swapIso n F i₀ v
  have hRR : R * R = 1 := by
    apply (omPlusAutGlLin (Fin n ⊕ Fin n) F).injective
    rw [map_mul, hRr, hrr, map_one]
  have hRinv : R⁻¹ = R := inv_eq_of_mul_eq_one_right hRR
  have hAeq : A = spinMatrix (quadPlus n F) h * R := by
    have h1 : omPlusAutGlLin (Fin n ⊕ Fin n) F (spinMatrix (quadPlus n F) h) =
        omPlusAutGlLin (Fin n ⊕ Fin n) F (A * R) := by
      rw [map_mul, omPlusAutGlLin_spinMatrix, hh, ← hr, hRr, ← hgA]
    have h2 : spinMatrix (quadPlus n F) h = A * R :=
      (omPlusAutGlLin (Fin n ⊕ Fin n) F).injective h1
    rw [h2, mul_assoc, hRR, mul_one]
  have hRg : ∀ g, R * spinMatrix (quadPlus n F) g * R =
      spinMatrix (quadPlus n F) (graphSpin n F i₀ g) := by
    intro g
    apply (omPlusAutGlLin (Fin n ⊕ Fin n) F).injective
    rw [map_mul, map_mul, omPlusAutGlLin_spinMatrix, hRr, omPlusAutGlLin_spinMatrix]
    apply LinearEquiv.ext
    intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr]
    exact (spinAction_graphSpin i₀ g v).symm
  exact ⟨R, hAeq, hRg, hRinv⟩

theorem omPlusAut_graph_setup {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn3 : 3 ≤ n) {A : GL (Fin n ⊕ Fin n) F}
    {gA : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hgA : gA = omPlusAutGlLin (Fin n ⊕ Fin n) F A)
    (hA_orth : gA ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F))
    (hodd : Odd (finrank F (commSpace gA))) (i₀ : Fin n) :
    ∃ (h : spinGroup (quadPlus n F)) (R : GL (Fin n ⊕ Fin n) F),
      A = spinMatrix (quadPlus n F) h * R ∧
      (∀ g, R * spinMatrix (quadPlus n F) g * R =
        spinMatrix (quadPlus n F) (graphSpin n F i₀ g)) ∧
      R⁻¹ = R := by
  set r : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) := swapLin n F i₀ with hr
  have hr_orth : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hr]
    exact quadPlus_swapLin n F i₀ v
  have hgr_orth : gA * r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) :=
    mul_mem hA_orth hr_orth
  have hrfin : (finrank F (commSpace r) : ZMod 2) = 1 := by
    rw [hr, omPlusAut_finrank_commSpace_swapLin]
    norm_num
  have hgr_even : Even (finrank F (commSpace (gA * r))) := by
    rw [← ZMod.natCast_eq_zero_iff_even,
      natCast_finrank_commSpace_mul (nondegenerate_polarBilin_quadPlus n F) hA_orth hr_orth,
      ZMod.natCast_eq_one_iff_odd.mpr hodd, hrfin]
    decide
  have hgr : gA * r ∈ omegaGroup (quadPlus n F) (nondegenerate_polarBilin_quadPlus n F) :=
    mem_omegaGroup.mpr ⟨hgr_orth, hgr_even⟩
  obtain ⟨h, hh⟩ :=
    CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus hn3 hgr
  obtain ⟨R, hAeq, hRg, hRinv⟩ := omPlusAut_graph_swapGL hgA hh hr
  exact ⟨h, R, hAeq, hRg, hRinv⟩

theorem omPlus_two_aut_inner_or_graph {n : ℕ} (hn : 5 ≤ n) {F : Type} [Field F]
    (hF : Nat.card F = 2) (α : MulAut (spinGroup (quadPlus n F))) :
    ∃ h : spinGroup (quadPlus n F), (∀ g, α g = h * g * h⁻¹) ∨
      ∀ g, α g = h * graphSpin n F ⟨n - 1, by omega⟩ g * h⁻¹ := by
  have hFinite : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hFintype : Fintype F := Fintype.ofFinite F
  have hCharP : CharP F 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hcard, hμ1, hφr⟩ := omPlusAut_field_triv hF
  let E : spinGroup (quadPlus n F) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F)) :=
    omPlusAutEquiv hn3 F
  let β : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n F))) :=
    E.symm.trans (α.trans E)
  have hE : E = omPlusAutEquiv hn3 F := rfl
  have hβ : ∀ x, β x = E (α (E.symm x)) := fun x => by simp [β]
  have hadm : CFSG.Open.StatedLieAdmissible CFSG.Open.StatedLieTag.POmegaPlus n 2 1 :=
    ⟨Nat.prime_two, le_refl 1, by omega⟩
  obtain ⟨A, φ, μ, hsim, hconj⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.OrthAut.exists_similarity_plus (p := 2) (f := 1)
      hadm hn (by rw [pow_one]; exact hF) β
  have hφ : φ = RingEquiv.refl F := hφr φ
  have hμ : (μ : F) = 1 := hμ1 μ
  set gA : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F) :=
    omPlusAutGlLin (Fin n ⊕ Fin n) F A with hgA
  have hA_orth : gA ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n F) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    have h := hsim v
    rw [hφ] at h
    have hfun : (fun i => (RingEquiv.refl F) (v i)) = v := rfl
    rw [hfun, hμ, one_mul] at h
    simp only [RingEquiv.refl_apply] at h
    rw [hgA, omPlusAutGlLin_apply]
    exact h
  by_cases hEven : Even (finrank F (commSpace gA))
  · have hgAmem : gA ∈ omegaGroup (quadPlus n F) (nondegenerate_polarBilin_quadPlus n F) :=
      mem_omegaGroup.mpr ⟨hA_orth, hEven⟩
    obtain ⟨h, hh⟩ :=
      CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus hn3 hgAmem
    exact ⟨h, Or.inl (omPlusAut_inner_case hn3 hE hβ hφ (by rw [← hgA]; exact hh) hconj)⟩
  · obtain ⟨h, _, hAeq, hRg, hRinv⟩ :=
      omPlusAut_graph_setup hn3 hgA hA_orth (Nat.not_even_iff_odd.mp hEven)
        (⟨n - 1, by omega⟩ : Fin n)
    exact ⟨h, Or.inr (omPlusAut_graph_case hn3 hE hβ hφ ⟨n - 1, by omega⟩ hAeq hRg hRinv
      hconj)⟩

end CFSG.LocalAnalysis.WeakClosure81
