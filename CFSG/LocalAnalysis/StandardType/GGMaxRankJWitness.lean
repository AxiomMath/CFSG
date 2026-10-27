module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection
import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pjw_labelIso_maxRank_false {p : ℕ} {labJ labX : LargeEvenLabel}
    (hrow : ggRowMaxRank p labJ labX) (hiso : GGLabelIso labJ labX) : False := by
  have htJ : labJ.tag = .A ∨ labJ.tag = .twA := by
    have h := hrow
    rcases h with ⟨h, -, -, -⟩ | ⟨h, -, -, -⟩
    · exact Or.inl (congrArg LargeEvenLabel.tag h)
    · exact Or.inr (congrArg LargeEvenLabel.tag h)
  have hrJ : labJ.rank = 8 := by
    have h := hrow
    rcases h with ⟨h, -, -, -⟩ | ⟨h, -, -, -⟩
    · exact congrArg LargeEvenLabel.rank h
    · exact congrArg LargeEvenLabel.rank h
  have htX : labX.tag = .E8 := by
    have h := hrow
    rcases h with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩
    · rw [h]
    · rw [h]
  simp only [GGLabelIso] at hiso
  rcases hiso with h | ⟨h, -, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have h' : labJ.tag = .E8 := (congrArg LargeEvenLabel.tag h).trans htX
    rcases htJ with hA | hA <;> rw [hA] at h' <;> exact absurd h' (by decide)
  · rcases h with hB | hB <;> rcases htJ with hA | hA <;> rw [hA] at hB <;>
      exact absurd hB (by decide)
  · have h' : labJ.tag = .D := congrArg LargeEvenLabel.tag h
    rcases htJ with hA | hA <;> rw [hA] at h' <;> exact absurd h' (by decide)
  · have hr : labJ.rank = 3 := congrArg LargeEvenLabel.rank h
    omega
  · have h' : labJ.tag = .twD := congrArg LargeEvenLabel.tag h
    rcases htJ with hA | hA <;> rw [hA] at h' <;> exact absurd h' (by decide)
  · have hr : labJ.rank = 3 := congrArg LargeEvenLabel.rank h
    omega
  · have h' : labJ.tag = .twD := congrArg LargeEvenLabel.tag h
    rcases htJ with hA | hA <;> rw [hA] at h' <;> exact absurd h' (by decide)
  · have h' : labX.tag = .twD := congrArg LargeEvenLabel.tag h
    rw [htX] at h'
    exact absurd h' (by decide)

theorem ggMaxRank_witness {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hLab : GGLabelRigidInput) (hrow : GGResRowAt ggRowMaxRank p J L) :
    ∃ z ∈ Bs, z ∉ Subgroup.centralizer (L : Set G) ∧
      IsComponentOf J (L ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hNbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hBleBs : B ≤ Bs := hH.1.2.1.1
  have hStdSubPre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
  have hD : D = Subgroup.closure {x, y} := hNbr.2.1
  have hJc : IsComponentOf J
      (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_stdSub hS hStdSubPre hD
  have hJcL : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hStdSubPre.2.2.2.2.2.1
  have hLc : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) :=
    hJc.of_le_of_le (le_inf (hJcL.1.trans inf_le_left) (hJc.1.trans inf_le_left))
      (le_inf inf_le_right (inf_le_left.trans hLc.1))
  have hyB : y ∈ B := hNbr.1.2.1
  refine ⟨y, hBleBs hyB, ?_, hJcomp⟩
  intro hy
  have hLy : L ≤ Subgroup.centralizer ({y} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hy l hl
  have hLeq : L ⊓ Subgroup.centralizer ({y} : Set G) = L := inf_eq_left.mpr hLy
  have hJcompL : IsComponentOf J L := by rw [← hLeq]; exact hJcomp
  have hLq : CFSG.Open.IsQuasisimple L :=
    ((CFSG.Assembly.isComponentOf_iff_open).mp hLc).2.2
  have hJL : J = L :=
    CFSG.Fischer.Classification.Recognition.IsComponentOf.eq_of_isQuasisimple
      ((CFSG.Assembly.isComponentOf_iff_open).mp hJcompL) hLq
  obtain ⟨labJ, labX, hInJ, hInX, hHasJ, hHasX, hrowlab⟩ := hrow
  have hHasJ' : GGHasLabel labJ (↥L ⧸ Subgroup.center ↥L) := by
    rw [← hJL]; exact hHasJ
  have hiso : GGLabelIso labJ labX :=
    hLab labJ labX (↥L ⧸ Subgroup.center ↥L) hInJ hInX hHasJ' hHasX
  exact pjw_labelIso_maxRank_false hrowlab hiso

theorem ggMaxRank_witnessK {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hJK : J ≤ K) :
    ∃ z ∈ Bs, z ∉ Subgroup.centralizer (K : Set G) ∧
      IsComponentOf J (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hNbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBleBs : B ≤ Bs := hH.1.2.1.1
  have hxK : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hS hDJ hNbr hJK
  refine ⟨x, hBleBs hS.2.1, ?_, hxK⟩
  intro hx
  have hKle : K ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    exact Subgroup.zpowers_le.mpr hx
  have hbot : ⁅K, Subgroup.zpowers x⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKle
  exact hNbr.2.2.2 (hbot.le.trans bot_le)

end CFSG.StandardType

end
