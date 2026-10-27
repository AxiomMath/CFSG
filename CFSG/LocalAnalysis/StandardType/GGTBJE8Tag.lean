module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LangGlue
public import CFSG.LocalAnalysis.StandardType.GGTBJMaxRankRow
public import CFSG.LocalAnalysis.StandardType.GGTBJLabelJ
public import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
public import CFSG.LocalAnalysis.StandardType.GGNbrHalfSplitArith

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Cells

@[expose] def GGTBJE8LeviL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8) p Bs L → GGResXDatum p Bs L →
    ∀ n : ℕ, LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel) →
      GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L) →
      (p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → n ∣ labJ.n →
        ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8) →
          GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J

@[expose] def GGTBJE8LeviK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → J ≤ K → ∀ [Fact p.Prime],
    GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8) p Bs K → GGResXDatum p Bs K →
    ∀ n : ℕ, LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel) →
      GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) →
      (p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) →
      ∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → n ∣ labJ.n →
        ¬ ((labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8) →
          GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J

end Cells

section Arith

private theorem e8tag_dvd_of_dvd_sq_sub_one {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (h : p ∣ m ^ 2 - 1) : p ∣ m - 1 ∨ p ∣ m + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hfac : (k + 1) ^ 2 - 1 = k * (k + 2) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [hfac] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h2
  · left
    simpa using h1
  · right
    simpa [add_assoc] using h2

private theorem e8tag_four_pow_eq (n : ℕ) : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num

private theorem e8tag_rank_zero {r n : ℕ} (h : LargeEvenInLambda2 (⟨.E8, r, n⟩ : LargeEvenLabel)) :
    r = 0 := h.2

private theorem e8tag_rowAt_nonLevi {G : Type} [Group G] {p : ℕ} {J X : Subgroup G}
    (h : GGResRowAt ggRowMaxRank p J X) : GGResRowAt ggRowNonLevi p J X := by
  obtain ⟨a, c, ha, hc, hJ, hX, hr⟩ := h
  exact ⟨a, c, ha, hc, hJ, hX, Or.inr (Or.inl hr)⟩

end Arith

section Dispatch

theorem ggTBJLeftOnLab_e8
    (hRig : GGLabelRigidInput) (hSign : GGTCJE8A8Sign)
    (hLevi : GGTBJE8LeviL) : GGTBJLeftOnLab fun _ lab => lab.tag = .E8 := by
  intro G _ _ p B Bs x L D J y K hH hp hL hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  have ht : t = .E8 := hS
  subst ht
  have hr : r = 0 := e8tag_rank_zero hΛ
  subst hr
  have hpp : p.Prime := hp.out
  have hreg : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
    obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
    have heq : labs = (⟨.E8, 0, n⟩ : LargeEvenLabel) :=
      eq_of_ggLabelIso_of_excTag (Or.inr (Or.inr (Or.inl rfl)))
        (hRig ⟨.E8, 0, n⟩ labs _ hΛ hlabs hhas hhass)
    have hs : LargeEvenSplit p (⟨.E8, 0, n⟩ : LargeEvenLabel) := by
      have h := hPs.1
      rwa [heq] at h
    have h4 : p ∣ 4 ^ n - 1 := ggLabPhiOneTwo_of_largeEvenSplit hs
    rw [e8tag_four_pow_eq] at h4
    exact e8tag_dvd_of_dvd_sq_sub_one hpp Nat.one_le_two_pow h4
  by_cases hA8 : (labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8
  · obtain ⟨htag, hrank⟩ := hA8
    have hW := ggE8LangWitness_L_of_resHyp hRig hH hΛ hhas hreg
    exact Or.inr (Or.inr (e8tag_rowAt_nonLevi
      (ggTBJ_maxRank_row_L hSign hH hΛ hhas hΛJ hhasJ htag hrank hdvd hW)))
  · exact (hLevi G p B Bs x L D J y K hH hL hX n hΛ hhas hreg labJ hΛJ hhasJ hdvd hA8).imp id Or.inl

theorem ggTBJNbrOnLab_e8
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hSign : GGTCJE8A8Sign)
    (hLevi : GGTBJE8LeviK) : GGTBJNbrOnLab fun _ lab => lab.tag = .E8 := by
  intro G _ _ p B Bs x L D J y K hH hp hK hX lab labJ hΛ hΛJ hS hhas hhasJ hdvd
  obtain ⟨t, r, n⟩ := lab
  have ht : t = .E8 := hS
  subst ht
  have hr : r = 0 := e8tag_rank_zero hΛ
  subst hr
  have hpp : p.Prime := hp.out
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hreg : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 := by
    have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnb
    have hHS := ggNbr_halfSplit_of_hyp hraw hiso hH.1 hnb hInnK
    obtain ⟨labh, hlabh, hhash, _, _, _, _, _, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
    have heq : labh = (⟨.E8, 0, n⟩ : LargeEvenLabel) :=
      eq_of_ggLabelIso_of_excTag (Or.inr (Or.inr (Or.inl rfl)))
        (hRig ⟨.E8, 0, n⟩ labh _ hΛ hlabh hhas hhash)
    have hd := largeEvenHalfSplit_dvd hlabh hHSlab
    rw [heq] at hd
    rcases hd with h4 | ⟨-, hex⟩
    · exact e8tag_dvd_of_dvd_sq_sub_one hpp Nat.one_le_two_pow h4
    · exfalso
      rcases hex with h | h <;> simp at h
  by_cases hA8 : (labJ.tag = .A ∨ labJ.tag = .twA) ∧ labJ.rank = 8
  · obtain ⟨htag, hrank⟩ := hA8
    have hW := ggE8LangWitness_K_of_resHyp hRig hI3 hH hΛ hhas hreg
    exact Or.inr (Or.inr (e8tag_rowAt_nonLevi
      (ggTBJ_maxRank_row_K hSign hI3 hH hΛ hhas hΛJ hhasJ htag hrank hdvd hW)))
  · exact (hLevi G p B Bs x L D J y K hH (hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb) hK hX n hΛ hhas
      hreg labJ hΛJ hhasJ hdvd hA8).imp id Or.inl

theorem ggTBJLeftOn_e8
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hSign : GGTCJE8A8Sign)
    (hLevi : GGTBJE8LeviL) : GGTBJLeftOn fun _ lab => lab.tag = .E8 :=
  (ggTBJLeftOnLab_e8 hRig hSign hLevi).toLeftOn hTCJ

theorem ggTBJNbrOn_e8
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hI3 : GGNbrSubcomponentInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hSign : GGTCJE8A8Sign) (hLevi : GGTBJE8LeviK) :
    GGTBJNbrOn fun _ lab => lab.tag = .E8 :=
  (ggTBJNbrOnLab_e8 hRig hI3 hraw hiso hSign hLevi).toNbrOn hTCJ hI3

end Dispatch

end CFSG.StandardType

end
