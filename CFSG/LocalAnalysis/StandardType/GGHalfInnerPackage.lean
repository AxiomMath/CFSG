module

public import CFSG.LocalAnalysis.StandardType.GGHalfEndNodes
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem ggHalfInnerCommA_threeDvdCardJ {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) : 3 ∣ Nat.card J := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  have hinj : Function.Injective (slLower2Hom m) :=
    (slLowerBlockHom_injective (n := m + 1 + 1) (F := F2)).comp
      (slLowerBlockHom_injective (n := m + 1) (F := F2))
  have hφ1inj : Function.Injective φ₁ := h.coords.inj₁
  have hω3 : (omegaBlock m ⟨0, by omega⟩) ^ 3 = 1 :=
    omegaBlock_pow_three m ⟨0, by omega⟩
  have hω1 : (omegaBlock m ⟨0, by omega⟩) ≠ 1 :=
    omegaBlock_ne_one m ⟨0, by omega⟩
  have hh3 : (slLower2Hom m (omegaBlock m ⟨0, by omega⟩)) ^ 3 = 1 := by
    rw [← map_pow, hω3, map_one]
  have hh1 : slLower2Hom m (omegaBlock m ⟨0, by omega⟩) ≠ 1 :=
    fun h1 => hω1 (hinj (by simpa using h1))
  have hmem : φ₁ (slLower2Hom m (omegaBlock m ⟨0, by omega⟩)) ∈ J := by
    rw [← h.coords.rangeJ]
    exact MonoidHom.mem_range.mpr ⟨omegaBlock m ⟨0, by omega⟩, rfl⟩
  have hg3 : (φ₁ (slLower2Hom m (omegaBlock m ⟨0, by omega⟩))) ^ 3 = 1 := by
    rw [← map_pow, hh3, map_one]
  have hg1 : φ₁ (slLower2Hom m (omegaBlock m ⟨0, by omega⟩)) ≠ 1 :=
    fun h1 => hh1 (hφ1inj (by simpa using h1))
  have horder : orderOf (φ₁ (slLower2Hom m (omegaBlock m ⟨0, by omega⟩))) = 3 :=
    orderOf_eq_prime hg3 hg1
  have := orderOf_dvd_natCard (G := J)
    (x := (⟨φ₁ (slLower2Hom m (omegaBlock m ⟨0, by omega⟩)), hmem⟩ : J))
  simpa [horder] using this

private theorem ggHalfInnerCommA_statedModel_of_equiv_sl {Y : Type} [Group Y] {N : ℕ}
    (hN : 3 ≤ N) (e : Y ≃* Matrix.SpecialLinearGroup (Fin N) F2) :
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL N 2 1 := by
  refine ⟨?_, F2, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · unfold StatedLieAdmissible
    refine ⟨Nat.prime_two, by norm_num, by omega, ?_, ?_⟩
    · intro h; have := congrArg Prod.fst h; omega
    · intro h; have := congrArg Prod.fst h; omega
  · exact GaloisField.card 2 1 (by norm_num)
  · exact (QuotientGroup.congr (Subgroup.center Y)
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin N) F2)) e
      (Subgroup.map_center_eq e)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj N F2)

private theorem ggHalfInnerCommA_labJ'_eq_of_iso {m : ℕ} (hm : 3 ≤ m) {labJ' : LargeEvenLabel}
    (hiso : GGLabelIso labJ' (⟨.A, m, 1⟩ : LargeEvenLabel)) :
    labJ' = ⟨.A, m, 1⟩ ∨ (m = 3 ∧ labJ' = ⟨.D, 3, 1⟩) := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact absurd (show LargeEvenLieTag.A = .B ∨ LargeEvenLieTag.A = .C from h.2.1) (by decide)
  · refine Or.inr ⟨?_, ?_⟩
    · exact show m = 3 from congrArg LargeEvenLabel.rank h.2
    · have hn : labJ'.n = 1 := (congrArg LargeEvenLabel.n h.2).symm
      rw [h.1, hn]
  · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.D from congrArg LargeEvenLabel.tag h.2)
      (by decide)
  · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twA from congrArg LargeEvenLabel.tag h.2)
      (by decide)
  · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twD from congrArg LargeEvenLabel.tag h.2)
      (by decide)
  · exact absurd (show m = 1 from congrArg LargeEvenLabel.rank h.2) (by omega)
  · exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twD from congrArg LargeEvenLabel.tag h.1)
      (by decide)

private theorem ggHalfInnerCommA_row_A {m : ℕ} (hm : 3 ≤ m) {lab : LargeEvenLabel}
    (hrow : GGTablePRow 3 (⟨.A, m, 1⟩ : LargeEvenLabel) lab) :
    lab = ⟨.A, m + 2, 1⟩ ∨ (m + 2 = 5 ∧ lab = ⟨.twD, 4, 1⟩) ∨
      (m + 2 = 7 ∧ lab = ⟨.E6, 0, 1⟩) := by
  unfold GGTablePRow at hrow
  rcases hrow with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exfalso; exact absurd (show (3 : ℕ) ∣ 2 ^ (1 : ℕ) - 1 from h.2.1) (by norm_num)
  · rcases h.2.2.2 with h' | h'
    · exact Or.inl (show lab = ⟨.A, m + 2, 1⟩ from h')
    · obtain ⟨hm5, hlab⟩ := h'
      change m = 5 at hm5
      exact Or.inr (Or.inr ⟨by omega, show lab = ⟨.E6, 0, 1⟩ from hlab⟩)
  · exfalso; exact absurd h.2.1 (by norm_num)
  · exfalso; exact absurd h.2.1 (by norm_num)
  · exfalso; exact absurd h.2.1 (by norm_num)
  · exfalso; exact absurd h.2.1 (by norm_num)
  · exfalso
    exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twA from h.1) (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twA from h.1) (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.B ∨ LargeEvenLieTag.A = LargeEvenLieTag.C
      from h.1) (by decide)
  · exfalso
    exact absurd
      (show LargeEvenLieTag.A = LargeEvenLieTag.B2der from congrArg LargeEvenLabel.tag h.1)
      (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.D from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.D from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twD from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twD from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.triD4 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.triD4 from h.1) (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.triD4 from h.1) (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.triD4 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.E6 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.E6 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.twE6 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.E7 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.A = LargeEvenLieTag.G2 from h.1) (by decide)

private theorem ggHalfInnerCommA_row_D {lab : LargeEvenLabel}
    (hrow : GGTablePRow 3 (⟨.D, 3, 1⟩ : LargeEvenLabel) lab) : lab = ⟨.twD, 4, 1⟩ := by
  unfold GGTablePRow at hrow
  rcases hrow with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.A from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.A from h.1) (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.A from congrArg LargeEvenLabel.tag h.1)
      (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.A from congrArg LargeEvenLabel.tag h.1)
      (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.A from congrArg LargeEvenLabel.tag h.1)
      (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.A from congrArg LargeEvenLabel.tag h.1)
      (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.twA from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.twA from h.1) (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.B ∨ LargeEvenLieTag.D = LargeEvenLieTag.C
      from h.1) (by decide)
  · exfalso
    exact absurd
      (show LargeEvenLieTag.D = LargeEvenLieTag.B2der from congrArg LargeEvenLabel.tag h.1)
      (by decide)
  · exfalso; exact absurd (show (3 : ℕ) ∣ 2 ^ (1 : ℕ) - 1 from h.2.1) (by norm_num)
  · rcases h.2.2 with h' | h' | h'
    · exact show lab = ⟨.twD, 4, 1⟩ from h'
    · exfalso; exact absurd (show (3 : ℕ) = 4 from h'.1) (by norm_num)
    · exfalso; exact absurd (show (3 : ℕ) = 6 from h'.1) (by norm_num)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.twD from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.twD from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.triD4 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.triD4 from h.1) (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.triD4 from h.1) (by decide)
  · exfalso
    exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.triD4 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.E6 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.E6 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.twE6 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.E7 from h.1) (by decide)
  · exfalso; exact absurd (show LargeEvenLieTag.D = LargeEvenLieTag.G2 from h.1) (by decide)

theorem nbr_package {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hRig : GGLabelRigidInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput) {y' : G} {K' : Subgroup G}
    (hnbr : GGNbr p B x D J y' K') :
    J ≤ K' ∧ CFSG.Assembly.IsComponentOf J (K' ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      CFSG.Assembly.IsQuasisimple ↥K' ∧ Bs ≤ Subgroup.normalizer (K' : Set G) ∧
      ∃ lab : LargeEvenLabel, GGHasLabel lab (↥K' ⧸ Subgroup.center ↥K') ∧
        (lab = ⟨.A, m + 2, 1⟩ ∨ (m + 2 = 5 ∧ lab = ⟨.twD, 4, 1⟩) ∨
          (m + 2 = 7 ∧ lab = ⟨.E6, 0, 1⟩)) := by
  have hp3 : p = 3 := h.nbr.2.1
  subst hp3
  have hJK : J ≤ K' :=
    le_of_ggNbr hLB h.cfg.1 h.cfg.2.2 (ggHalfInnerCommA_threeDvdCardJ h) hnbr
  have hinnK : GGInnerDiagOn Bs K' := h.inner.2 y' K' hnbr
  refine ⟨hJK, ?_, isQuasisimple_of_largeEvenMarking hinnK, ?_, ?_⟩
  ·
    have hS : LargeEvenSStar 3 B x L := h.cfg.1.2.2.2.2.2.2.1
    have hJD : CFSG.Assembly.IsComponentOf J
        (Subgroup.centralizer ({y'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
      isComponentOf_inf_centralizer_of_stdSub hS h.cfg.2.2.1 hnbr.2.1
    have hJCx : J ≤ Subgroup.centralizer ({x} : Set G) := hJD.1.trans inf_le_right
    have hK'C : K' ≤ Subgroup.centralizer ({y'} : Set G) := hnbr.1.2.2.2.1
    have hle : K' ⊓ Subgroup.centralizer ({x} : Set G) ≤
        Subgroup.centralizer ({y'} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
      inf_le_inf hK'C le_rfl
    exact ⟨le_inf hJK hJCx, ggIsSubnormal_of_le_of_le hJD.2.1 (le_inf hJK hJCx) hle, hJD.2.2⟩
  ·
    obtain ⟨-, lab, -, hraw⟩ := hinnK
    obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
    exact hP.1
  ·
    have hm3 : 3 ≤ m := by have := h.nbr.2.2.1; omega
    have hinj : Function.Injective (φ₁.comp (slLower2Hom m)) :=
      h.coords.inj₁.comp (slLower2Hom_injective m)
    have hmodJ : StatedClassicalModel ((φ₁.comp (slLower2Hom m)).range ⧸
        Subgroup.center (φ₁.comp (slLower2Hom m)).range) .PSL (m + 1) 2 1 :=
      ggHalfInnerCommA_statedModel_of_equiv_sl (by omega) (MonoidHom.ofInjective hinj).symm
    have hmodJ' : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL (m + 1) 2 1 := by
      rw [← h.coords.rangeJ]
      exact hmodJ
    have hhasJ : GGHasLabel ⟨.A, m, 1⟩ (J ⧸ Subgroup.center J) := ggHasLabel_typeA hmodJ'
    have hΛJ : LargeEvenInLambda2 (⟨.A, m, 1⟩ : LargeEvenLabel) := largeEvenInLambda2_typeA hmodJ'
    obtain ⟨labK, hΛK, hhasK, -⟩ := largeEvenMarking_exists_hasLabel hinnK
    have hregime : GGRegimeAm2 3 (Nat.card Bs) (⟨.A, m, 1⟩ : LargeEvenLabel) labK :=
      ⟨rfl, rfl, rfl, by omega⟩
    obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hhasJ', hhasK'⟩ :=
      hTP G 3 B Bs x L D J y' K' h.cfg h.inner.1 hinnK hnbr
        (⟨.A, m, 1⟩ : LargeEvenLabel) labK hΛJ hΛK hregime hhasJ hhasK
    have hiso : GGLabelIso labJ' (⟨.A, m, 1⟩ : LargeEvenLabel) :=
      hRig labJ' (⟨.A, m, 1⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) hΛJ' hΛJ hhasJ' hhasJ
    have hform : labK' = ⟨.A, m + 2, 1⟩ ∨ (m + 2 = 5 ∧ labK' = ⟨.twD, 4, 1⟩) ∨
        (m + 2 = 7 ∧ labK' = ⟨.E6, 0, 1⟩) := by
      rcases ggHalfInnerCommA_labJ'_eq_of_iso hm3 hiso with hA | ⟨hm3eq, hD⟩
      · rw [hA] at hrow
        exact ggHalfInnerCommA_row_A hm3 hrow
      · subst hm3eq
        rw [hD] at hrow
        exact Or.inr (Or.inl ⟨rfl, ggHalfInnerCommA_row_D hrow⟩)
    exact ⟨labK', hhasK', hform⟩

end GGHalfCtx

end CFSG.StandardType

end
