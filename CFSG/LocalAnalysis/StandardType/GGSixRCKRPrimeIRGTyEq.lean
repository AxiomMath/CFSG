module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelC
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelE
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGLabelDef
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

private def irgTE_inv : LargeEvenLieTag → StatedLieTag
  | .A => .PSL
  | .twA => .PSU
  | .C => .PSp
  | .D => .POmegaPlus
  | .twD => .POmegaMinus
  | .F4 => .F4
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8
  | .twE6 => .twistedE6
  | _ => .PSL

private theorem irgTE_inv_tag {t : StatedLieTag} {n g : ℕ} (ht : GGPosTag t) :
    irgTE_inv (irgLabel t n g).tag = t := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem irgTE_tag_ne {t : StatedLieTag} {n g : ℕ} (ht : GGPosTag t) :
    (irgLabel t n g).tag ≠ LargeEvenLieTag.B ∧ (irgLabel t n g).tag ≠ LargeEvenLieTag.triD4 := by
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨fun h => by simp [irgLabel] at h, fun h => by simp [irgLabel] at h⟩

private theorem irgTE_BC {t : StatedLieTag} {n g : ℕ} (hn : RCKNormalizedModel t n g)
    (h : (irgLabel t n g).tag = LargeEvenLieTag.B ∨ (irgLabel t n g).tag = LargeEvenLieTag.C) :
    t = .PSp := by
  rcases h with h | h
  · exact absurd h (irgTE_tag_ne hn.1).1
  · have e := irgTE_inv_tag (n := n) (g := g) hn.1
    rw [h] at e
    exact e.symm

private theorem irgTE_D {t : StatedLieTag} {n g : ℕ} (hn : RCKNormalizedModel t n g)
    (h : (irgLabel t n g).tag = LargeEvenLieTag.D) : 4 ≤ (irgLabel t n g).rank := by
  have e := irgTE_inv_tag (n := n) (g := g) hn.1
  rw [h] at e
  have ht : t = .POmegaPlus := e.symm
  subst ht
  exact hn.2.2.2

private theorem irgTE_twD {t : StatedLieTag} {n g : ℕ} (hn : RCKNormalizedModel t n g)
    (h : (irgLabel t n g).tag = LargeEvenLieTag.twD) : 4 ≤ (irgLabel t n g).rank := by
  have e := irgTE_inv_tag (n := n) (g := g) hn.1
  rw [h] at e
  have ht : t = .POmegaMinus := e.symm
  subst ht
  exact hn.2.2.2

private theorem irgTE_eq_params {t : StatedLieTag} {n g n' g' : ℕ}
    (hn : RCKNormalizedModel t n g) (hn' : RCKNormalizedModel t n' g')
    (h : irgLabel t n g = irgLabel t n' g') : n' = n ∧ g' = g := by
  obtain ⟨ht, hadm⟩ := hn
  obtain ⟨-, hadm'⟩ := hn'
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [irgLabel, LargeEvenLabel.mk.injEq] at h <;>
    simp only [StatedLieAdmissible] at hadm hadm' <;>
    (constructor <;> omega)

private theorem irgTE_lambda2 {t : StatedLieTag} {n g : ℕ} (hn : RCKNormalizedModel t n g) :
    LargeEvenInLambda2 (irgLabel t n g) := by
  obtain ⟨ht, hadm⟩ := hn
  have hg : 1 ≤ g := hadm.2.1
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h2, hne, -⟩ := hadm.2.2
    show 1 ≤ g ∧ (1 ≤ n - 1 ∧ (n - 1 = 1 → 2 ≤ g))
    refine ⟨hg, by omega, fun h1 => ?_⟩
    by_contra hlt
    have hn2 : n = 2 := by omega
    have hg1 : g = 1 := by omega
    subst hn2
    subst hg1
    exact hne rfl
  · obtain ⟨h3, hne⟩ := hadm.2.2
    show 1 ≤ g ∧ (2 ≤ n - 1 ∧ (n - 1 = 2 → 2 ≤ g))
    refine ⟨hg, by omega, fun h1 => ?_⟩
    by_contra hlt
    have hn3 : n = 3 := by omega
    have hg1 : g = 1 := by omega
    subst hn3
    subst hg1
    exact hne rfl
  · obtain ⟨h2, hne⟩ := hadm.2.2
    show 1 ≤ g ∧ (2 ≤ n ∧ (n = 2 → 2 ≤ g))
    refine ⟨hg, h2, fun h1 => ?_⟩
    by_contra hlt
    have hg1 : g = 1 := by omega
    subst h1
    subst hg1
    exact hne rfl
  · have h4 : 4 ≤ n := hadm.2.2
    show 1 ≤ g ∧ 3 ≤ n
    exact ⟨hg, by omega⟩
  · have h4 : 4 ≤ n := hadm.2.2
    show 1 ≤ g ∧ 2 ≤ n
    exact ⟨hg, by omega⟩
  · exact ⟨hg, rfl⟩
  · exact ⟨hg, rfl⟩
  · exact ⟨hg, rfl⟩
  · exact ⟨hg, rfl⟩
  · exact ⟨hg, rfl⟩

private theorem irgTE_hasLabel
    {X : Type} [Group X] {J : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    {t : StatedLieTag} {n g : ℕ} (hn : RCKNormalizedModel t n g) (φ : (ggU t n g).K →* X)
    (hr : φ.range = J) (hk : φ.ker ≤ Subgroup.center (ggU t n g).K) :
    GGHasLabel (irgLabel t n g) (↥J ⧸ Subgroup.center ↥J) := by
  rcases hn.1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact irg_hasLabel_classical hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_classical hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_classical hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_classical hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_classical hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_exc hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_exc hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_exc hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_exc hqs (by simp) hn φ hr hk
  · exact irg_hasLabel_exc hqs (by simp) hn φ hr hk

private theorem irgTE_param_eq {t t' : StatedLieTag} {n g n' g' : ℕ}
    (hn : RCKNormalizedModel t n g) (hn' : RCKNormalizedModel t' n' g')
    (h : GGLabelIso (irgLabel t n g) (irgLabel t' n' g')) : t' = t ∧ n' = n ∧ g' = g := by
  rcases h with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩
  · have htt : t' = t := by
      have e1 := irgTE_inv_tag (n := n) (g := g) hn.1
      have e2 := irgTE_inv_tag (n := n') (g := g') hn'.1
      calc t' = irgTE_inv (irgLabel t' n' g').tag := e2.symm
        _ = irgTE_inv (irgLabel t n g).tag := by rw [h]
        _ = t := e1
    subst htt
    obtain ⟨h1, h2⟩ := irgTE_eq_params hn hn' h
    exact ⟨rfl, h1, h2⟩
  · have ht : t = .PSp := irgTE_BC hn h1
    have ht' : t' = .PSp := irgTE_BC hn' h2
    subst ht
    subst ht'
    exact ⟨rfl, h3.symm, h4.symm⟩
  · have htag : (irgLabel t n g).tag = LargeEvenLieTag.D := congrArg LargeEvenLabel.tag h1
    have hrk : (irgLabel t n g).rank = 3 := congrArg LargeEvenLabel.rank h1
    have := irgTE_D hn htag
    omega
  · have htag : (irgLabel t' n' g').tag = LargeEvenLieTag.D := congrArg LargeEvenLabel.tag h2
    have hrk : (irgLabel t' n' g').rank = 3 := congrArg LargeEvenLabel.rank h2
    have := irgTE_D hn' htag
    omega
  · have htag : (irgLabel t n g).tag = LargeEvenLieTag.twD := congrArg LargeEvenLabel.tag h1
    have hrk : (irgLabel t n g).rank = 3 := congrArg LargeEvenLabel.rank h1
    have := irgTE_twD hn htag
    omega
  · have htag : (irgLabel t' n' g').tag = LargeEvenLieTag.twD := congrArg LargeEvenLabel.tag h2
    have hrk : (irgLabel t' n' g').rank = 3 := congrArg LargeEvenLabel.rank h2
    have := irgTE_twD hn' htag
    omega
  · have htag : (irgLabel t n g).tag = LargeEvenLieTag.twD := congrArg LargeEvenLabel.tag h1
    have hrk : (irgLabel t n g).rank = 2 := congrArg LargeEvenLabel.rank h1
    have := irgTE_twD hn htag
    omega
  · have htag : (irgLabel t' n' g').tag = LargeEvenLieTag.twD := congrArg LargeEvenLabel.tag h1
    have hrk : (irgLabel t' n' g').rank = 2 := congrArg LargeEvenLabel.rank h1
    have := irgTE_twD hn' htag
    omega

private theorem irgTE_not_tri {t : StatedLieTag} {n g g' : ℕ} (hn : RCKNormalizedModel t n g)
    (h : GGLabelIso (irgLabel t n g) ⟨.triD4, 0, g'⟩) : False := by
  rcases h with h | ⟨-, h2, -, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨h1, -⟩
  · exact (irgTE_tag_ne hn.1).2 (congrArg LargeEvenLabel.tag h)
  · rcases h2 with h2 | h2
    · have h3 : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.B := h2
      cases h3
    · have h3 : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.C := h2
      cases h3
  · have h3 : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.A :=
      congrArg LargeEvenLabel.tag h2
    cases h3
  · have h3 : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.D :=
      congrArg LargeEvenLabel.tag h2
    cases h3
  · have h3 : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.twA :=
      congrArg LargeEvenLabel.tag h2
    cases h3
  · have h3 : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.twD :=
      congrArg LargeEvenLabel.tag h2
    cases h3
  · have h3 : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.A :=
      congrArg LargeEvenLabel.tag h2
    cases h3
  · have h3 : (LargeEvenLieTag.triD4 : LargeEvenLieTag) = LargeEvenLieTag.twD :=
      congrArg LargeEvenLabel.tag h1
    cases h3

theorem irg_type_eq
    {X : Type} [Group X] {J : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    {t : StatedLieTag} {n g : ℕ} {t' : StatedLieTag} {n' g' : ℕ}
    (hn : RCKNormalizedModel t n g) (hn' : RCKNormalizedModel t' n' g')
    (φ : (ggU t n g).K →* X) (φ' : (ggU t' n' g').K →* X) (hr : φ.range = J)
    (hr' : φ'.range = J) (hk : φ.ker ≤ Subgroup.center (ggU t n g).K)
    (hk' : φ'.ker ≤ Subgroup.center (ggU t' n' g').K) : t' = t ∧ n' = n ∧ g' = g := by
  have hl := irgTE_hasLabel hqs hn φ hr hk
  have hl' := irgTE_hasLabel hqs hn' φ' hr' hk'
  have hiso := ggLabelRigidInput_holds (irgLabel t n g) (irgLabel t' n' g')
    (↥J ⧸ Subgroup.center ↥J) (irgTE_lambda2 hn) (irgTE_lambda2 hn') hl hl'
  exact irgTE_param_eq hn hn' hiso

theorem irg_tri_not_classical
    {X : Type} [Group X] {J : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    {t : StatedLieTag} {n g : ℕ} (hn : RCKNormalizedModel t n g) (φ : (ggU t n g).K →* X)
    (hr : φ.range = J) (hk : φ.ker ≤ Subgroup.center (ggU t n g).K)
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g' : ℕ} (hT : TriField F σ g')
    (φ' : (triD4Universal F σ).K →* X) (hr' : φ'.range = J)
    (hk' : φ'.ker ≤ Subgroup.center (triD4Universal F σ).K) : False := by
  have hl := irgTE_hasLabel hqs hn φ hr hk
  have hl' := irg_hasLabel_tri hqs hT φ' hr' hk'
  have hiso := ggLabelRigidInput_holds (irgLabel t n g) ⟨.triD4, 0, g'⟩
    (↥J ⧸ Subgroup.center ↥J) (irgTE_lambda2 hn) ⟨hT.1, rfl⟩ hl hl'
  exact irgTE_not_tri hn hiso

end CFSG.StandardType.RCKRP
