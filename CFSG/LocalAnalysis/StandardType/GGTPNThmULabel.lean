module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTPNThmULabelTransport
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MITransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.Adapters.RankTwoModelTransports

private theorem nonempty_mulEquiv_of_recipeLinear {d N : ℕ} {R R' : Type} [Group R] [Group R']
    (h : LargeEvenRecipeLinear d N fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeLinear d N fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  obtain ⟨e₁'⟩ := nonempty_proj_congr (ι := Fin d) (largeEvenSLGroup_eq_statedSL (K := K) d)
  obtain ⟨e₂'⟩ := nonempty_proj_congr (ι := Fin d) (largeEvenSLGroup_eq_statedSL (K := L) d)
  let eφ := statedProjCongr (glCongr (ι := Fin d) φ) (glCongr_statedSL φ d)
    (glCongr_statedScalars (ι := Fin d) φ)
  exact ⟨(e₁.trans e₁').trans (eφ.trans (e₂.trans e₂').symm)⟩

private theorem nonempty_mulEquiv_of_recipeUnitary {d q : ℕ} {R R' : Type} [Group R]
    [Group R'] (h : LargeEvenRecipeUnitary d q fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeUnitary d q fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  obtain ⟨e₁'⟩ := nonempty_proj_congr (ι := Fin d) (largeEvenSUGroup_eq_statedSU (K := K) d q)
  obtain ⟨e₂'⟩ := nonempty_proj_congr (ι := Fin d) (largeEvenSUGroup_eq_statedSU (K := L) d q)
  let eφ := statedProjCongr (glCongr (ι := Fin d) φ) (glCongr_statedSU φ d q)
    (glCongr_statedScalars (ι := Fin d) φ)
  exact ⟨(e₁.trans e₁').trans (eφ.trans (e₂.trans e₂').symm)⟩

private theorem nonempty_mulEquiv_of_recipeSymplectic {m q : ℕ} {R R' : Type} [Group R]
    [Group R'] (h : LargeEvenRecipeSymplectic m q false fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeSymplectic m q false fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  obtain ⟨e₁'⟩ := nonempty_proj_congr (ι := Fin m ⊕ Fin m)
    (largeEvenSpGroup_eq_statedSp (K := K) m)
  obtain ⟨e₂'⟩ := nonempty_proj_congr (ι := Fin m ⊕ Fin m)
    (largeEvenSpGroup_eq_statedSp (K := L) m)
  let eφ := statedProjCongr (glCongr (ι := Fin m ⊕ Fin m) φ) (glCongr_statedSp φ m)
    (glCongr_statedScalars (ι := Fin m ⊕ Fin m) φ)
  exact ⟨(e₁.trans e₁').trans (eφ.trans (e₂.trans e₂').symm)⟩

private theorem nonempty_mulEquiv_of_recipeSymplecticDerived {m q : ℕ} {R R' : Type}
    [Group R] [Group R']
    (h : LargeEvenRecipeSymplectic m q true fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeSymplectic m q true fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  have hS : ∀ (K' : Type) [Field K'],
      (⁅LargeEvenSpGroup K' m, LargeEvenSpGroup K' m⁆ : Subgroup (GL (Fin m ⊕ Fin m) K')) =
        ⁅StatedSp m K', StatedSp m K'⁆ := by
    intro K' _
    rw [largeEvenSpGroup_eq_statedSp]
  obtain ⟨e₁'⟩ := nonempty_proj_congr (ι := Fin m ⊕ Fin m) (hS K)
  obtain ⟨e₂'⟩ := nonempty_proj_congr (ι := Fin m ⊕ Fin m) (hS L)
  have hmap : (⁅StatedSp m K, StatedSp m K⁆).map
      (glCongr (ι := Fin m ⊕ Fin m) φ).toMonoidHom = ⁅StatedSp m L, StatedSp m L⁆ := by
    rw [Subgroup.map_commutator, glCongr_statedSp φ m]
  let eφ := statedProjCongr (glCongr (ι := Fin m ⊕ Fin m) φ) hmap
    (glCongr_statedScalars (ι := Fin m ⊕ Fin m) φ)
  exact ⟨(e₁.trans e₁').trans (eφ.trans (e₂.trans e₂').symm)⟩

private theorem nonempty_mulEquiv_of_recipeOmegaPlus {m q : ℕ} {R R' : Type} [Group R]
    [Group R'] (h : LargeEvenRecipeOmegaPlus m q fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeOmegaPlus m q fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  obtain ⟨e₁'⟩ := nonempty_proj_congr (ι := Fin m ⊕ Fin m)
    (largeEvenOmega_eq_statedOmega (K := K) (LargeEvenQPlus K m))
  obtain ⟨e₂'⟩ := nonempty_proj_congr (ι := Fin m ⊕ Fin m)
    (largeEvenOmega_eq_statedOmega (K := L) (LargeEvenQPlus L m))
  let eφ := statedProjCongr (glCongr (ι := Fin m ⊕ Fin m) φ)
    (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega φ
      (CFSG.Blueprint.EvenSource.statedQuadPlus_map φ m))
    (glCongr_statedScalars (ι := Fin m ⊕ Fin m) φ)
  exact ⟨(e₁.trans e₁').trans (eφ.trans (e₂.trans e₂').symm)⟩

private theorem nonempty_mulEquiv_of_recipeOmegaMinus {m q : ℕ} {R R' : Type} [Group R]
    [Group R'] (h : LargeEvenRecipeOmegaMinus m q fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeOmegaMinus m q fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, b', c', hirr', ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  let e₁' := omegaMinusProjEquiv (m + 1) b c
  let e₂' := omegaMinusProjEquiv (m + 1) b' c'
  have hmap : (StatedOmega (StatedQuadMinus (m + 1) K b c)).map
      (glCongr (ι := Fin m ⊕ Fin m ⊕ Fin 2) φ).toMonoidHom =
      StatedOmega (StatedQuadMinus (m + 1) L (φ b) (φ c)) :=
    CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega φ
      (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.statedQuadMinus_comp
        (n := m + 1) φ rfl rfl)
  let eφ := statedProjCongr (glCongr (ι := Fin m ⊕ Fin m ⊕ Fin 2) φ) hmap
    (glCongr_statedScalars (ι := Fin m ⊕ Fin m ⊕ Fin 2) φ)
  obtain ⟨e₃⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv
    (K := L) (n := m + 1) (by omega) (b := φ b) (c := φ c) (b' := b') (c' := c')
    (CFSG.Blueprint.EvenSource.irreducible_quadratic_map φ hirr) hirr'
  exact ⟨(e₁.trans e₁').trans (eφ.trans (e₃.trans (e₂.trans e₂').symm))⟩

private theorem nonempty_mulEquiv_of_recipeChevalley {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {q : ℕ} {der : Bool} {R R' : Type} [Group R] [Group R']
    (h : LargeEvenRecipeChevalley A q der fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeChevalley A q der fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  have hmap : (LargeEvenChevH A K der).map (MI.chevCongr A φ).toMonoidHom =
      LargeEvenChevH A L der := by
    cases der
    · simpa only [LargeEvenChevH, Bool.false_eq_true, if_false] using MI.chevGroup_map_eq A φ
    · simpa only [LargeEvenChevH, if_true] using MI.chevH_true_map_eq A φ
  exact ⟨e₁.trans ((MI.centerQuotCongr (MI.chevCongr A φ) hmap).trans e₂.symm)⟩

private theorem nonempty_mulEquiv_of_recipeTwisted {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {ρ : Equiv.Perm (Fin r)} {m n : ℕ} {R R' : Type} [Group R] [Group R']
    (h : LargeEvenRecipeTwisted A ρ m n fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeTwisted A ρ m n fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  exact ⟨e₁.trans ((MI.centerQuotCongr (MI.chevCongr A φ)
    (largeEvenTwistedH_map_chevCongr A ρ n φ)).trans e₂.symm)⟩

private theorem nonempty_mulEquiv_of_recipeSuzuki {a : ℕ} {R R' : Type} [Group R] [Group R']
    (h : LargeEvenRecipeSuzuki a fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeSuzuki a fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  exact ⟨e₁.trans ((MI.centerQuotCongr (CFSG.ShultStronglyClosedTI.glFieldEquiv (ι := Fin 4) φ)
    (CFSG.ShultStronglyClosedTI.map_glaSzGroup φ a)).trans e₂.symm)⟩

private theorem nonempty_mulEquiv_of_recipeTwF4 {a : ℕ} {R R' : Type} [Group R] [Group R']
    (h : LargeEvenRecipeTwF4 a fun S _ _ _ => Nonempty (R ≃* S))
    (h' : LargeEvenRecipeTwF4 a fun S _ _ _ => Nonempty (R' ≃* S)) :
    Nonempty (R ≃* R') := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := h
  obtain ⟨L, _, _, hL, ⟨e₂⟩⟩ := h'
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard (hK.trans hL.symm)
  exact ⟨e₁.trans ((MI.centerQuotCongr (MI.chevCongr LargeEvenCartanF4 φ)
    (MI.twF4H_map_eq a φ)).trans e₂.symm)⟩

theorem nonempty_mulEquiv_of_ggHasLabel {lab : LargeEvenLabel} {R R' : Type} [Group R]
    [Group R'] (h : GGHasLabel lab R) (h' : GGHasLabel lab R') : Nonempty (R ≃* R') := by
  rcases lab with ⟨tag, rank, n⟩
  cases tag
  all_goals dsimp only [GGHasLabel, LargeEvenRawDatum] at h h'
  case A => exact nonempty_mulEquiv_of_recipeLinear h h'
  case twA => exact nonempty_mulEquiv_of_recipeUnitary h h'
  case B => exact nonempty_mulEquiv_of_recipeSymplectic h h'
  case C => exact nonempty_mulEquiv_of_recipeSymplectic h h'
  case B2der => exact nonempty_mulEquiv_of_recipeSymplecticDerived h h'
  case D =>
    split_ifs at h h'
    · exact nonempty_mulEquiv_of_recipeLinear h h'
    · exact nonempty_mulEquiv_of_recipeOmegaPlus h h'
  case twD =>
    split_ifs at h h'
    · exact nonempty_mulEquiv_of_recipeLinear h h'
    · exact nonempty_mulEquiv_of_recipeUnitary h h'
    · exact nonempty_mulEquiv_of_recipeOmegaMinus h h'
  case G2 => exact nonempty_mulEquiv_of_recipeChevalley h h'
  case G2der => exact nonempty_mulEquiv_of_recipeChevalley h h'
  case F4 => exact nonempty_mulEquiv_of_recipeChevalley h h'
  case E6 => exact nonempty_mulEquiv_of_recipeChevalley h h'
  case E7 => exact nonempty_mulEquiv_of_recipeChevalley h h'
  case E8 => exact nonempty_mulEquiv_of_recipeChevalley h h'
  case twE6 => exact nonempty_mulEquiv_of_recipeTwisted h h'
  case triD4 => exact nonempty_mulEquiv_of_recipeTwisted h h'
  case twB2 => exact nonempty_mulEquiv_of_recipeSuzuki h h'
  case twF4 => exact nonempty_mulEquiv_of_recipeTwF4 h h'
  case twF4der => exact nonempty_mulEquiv_of_recipeTwF4 h h'

private theorem sup_center_eq_top_of_mulEquiv_quotient_center {X : Type} [Group X] [Finite X]
    {J : Subgroup X} (e : (↥J ⧸ Subgroup.center ↥J) ≃* (X ⧸ Subgroup.center X)) :
    J ⊔ Subgroup.center X = ⊤ := by
  let Z : Subgroup X := Subgroup.center X
  let CJ : Subgroup ↥J := Subgroup.center ↥J
  let ZJ : Subgroup ↥J := Z.subgroupOf J
  have hle : ZJ ≤ CJ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hx) (y : X)
  have hcard1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ↥J) ZJ
  have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ↥J) CJ
  have hZJle : Nat.card ZJ ≤ Nat.card CJ := Subgroup.card_le_of_le hle
  have hineq : Nat.card (↥J ⧸ CJ) ≤ Nat.card (↥J ⧸ ZJ) := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card CJ) ?_ Nat.card_pos
    calc Nat.card (↥J ⧸ CJ) * Nat.card CJ = Nat.card ↥J := hcard2.symm
      _ = Nat.card (↥J ⧸ ZJ) * Nat.card ZJ := hcard1
      _ ≤ Nat.card (↥J ⧸ ZJ) * Nat.card CJ := Nat.mul_le_mul_left _ hZJle
  have hX : Nat.card (X ⧸ Z) ≤ Nat.card (↥J ⧸ ZJ) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hineq
  have hiso : Nat.card (↥J ⧸ ZJ) =
      Nat.card (↥(J ⊔ Z) ⧸ Z.subgroupOf (J ⊔ Z)) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient J Z).toEquiv
  have hcardZ : Nat.card (Z.subgroupOf (J ⊔ Z)) = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := Z) (K := J ⊔ Z) le_sup_right).toEquiv
  have hcard3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := ↥(J ⊔ Z))
    (Z.subgroupOf (J ⊔ Z))
  have hcardX := Subgroup.card_eq_card_quotient_mul_card_subgroup (α := X) Z
  have htop : Nat.card X ≤ Nat.card ↥(J ⊔ Z) := by
    calc Nat.card X = Nat.card (X ⧸ Z) * Nat.card Z := hcardX
      _ ≤ Nat.card (↥J ⧸ ZJ) * Nat.card Z := Nat.mul_le_mul_right _ hX
      _ = Nat.card (↥(J ⊔ Z) ⧸ Z.subgroupOf (J ⊔ Z)) *
          Nat.card (Z.subgroupOf (J ⊔ Z)) := by rw [hiso, hcardZ]
      _ = Nat.card ↥(J ⊔ Z) := hcard3.symm
  exact Subgroup.eq_top_of_le_card (J ⊔ Z) htop

theorem eq_top_of_mulEquiv_quotient_center {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {J : Subgroup X}
    (e : (↥J ⧸ Subgroup.center ↥J) ≃* (X ⧸ Subgroup.center X)) : J = ⊤ :=
  CFSG.ComponentClassification.GrSLit.eq_top_of_sup_center_eq_top hX
    (sup_center_eq_top_of_mulEquiv_quotient_center e)

theorem not_ggHasLabel_of_le_ggAutFixedSubgroup {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {σ : MulAut X} (hσ : σ ≠ 1) {J : Subgroup X}
    (hJ : J ≤ ggAutFixedSubgroup σ) {lab : LargeEvenLabel}
    (hXl : GGHasLabel lab (X ⧸ Subgroup.center X)) :
    ¬ GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) := by
  intro hJlab
  obtain ⟨e⟩ := nonempty_mulEquiv_of_ggHasLabel hJlab hXl
  have hJtop : J = ⊤ := eq_top_of_mulEquiv_quotient_center hX e
  have hfix : ∀ x : X, σ x = x := by
    intro x
    have hx : x ∈ J := by rw [hJtop]; exact Subgroup.mem_top x
    exact (mem_ggAutFixedSubgroup σ x).mp (hJ hx)
  exact hσ (MulEquiv.ext hfix)

end CFSG.StandardType
