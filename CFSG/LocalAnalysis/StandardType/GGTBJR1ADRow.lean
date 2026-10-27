module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGTBJLinearCorank
import CFSG.LocalAnalysis.StandardType.GGTBJR1LinCount
import CFSG.LocalAnalysis.StandardType.GGTBJR1LinRefl
import CFSG.LocalAnalysis.StandardType.GGTBJR1OmPlusRow
import CFSG.LocalAnalysis.StandardType.GGTBJRowR4Narrow
import CFSG.LocalAnalysis.StandardType.GGTBRowR1Parity
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTBJR1Lin_naWeylAt
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {r f : ℕ} (hpq : p ∣ 2 ^ f - 1)
    (hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, f⟩) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ a ∈ ggTorusReflSetIn p J (ggGamma L hN).range,
      ∃ b ∈ ggTorusReflSetIn p J (ggGamma L hN).range, a * b ≠ b * a := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have : Fact p.Prime := ⟨hp⟩
  have hr : 3 ≤ r := hcfg.three_le_rank_of_typeA_marking hmark hpq
  obtain ⟨F, hField, hFinite, hCharP, hN', φ, S, hF, hφs, hker, hdiag, hcard, hS2, hJ⟩ :=
    exists_block_of_large_linear_L_of_marking_with_card hcfg hpq hmark
  obtain rfl : hN' = hN := Subsingleton.elim hN' hN
  let : Field F := hField
  let : Finite F := hFinite
  let : CharP F 2 := hCharP
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p (ggGamma L hN').range := isElemAbelian_range hBc hBp _
  have hsc : GGTorusSelfCent p (ggGamma L hN').range :=
    ggTorusSelfCent_ggGamma hN' hcfg.2.1.2.2.2
  have hcount : p ^ 2 * Nat.card ↥(ggFixingJ L J (ggGamma L hN').range) ≤
      Nat.card ↥(ggGamma L hN').range := ggTBJ_card_fixingJ_mul_le hcfg hN'
  have hS3 : 3 ≤ S.card :=
    ggTBJR1Lin_three_le_card hp hker hA.2 hdiag hS2 hJ hcount
  exact ggTBJR1Lin_noncomm hp (by omega) (by rw [hF]; exact hpq) hφs hker hA hsc hdiag hS3 hJ

private theorem ggR1ADRow_labelIso {p : ℕ} {lab lab' : LargeEvenLabel}
    (ht : GGTBRowR1A p lab ∨ GGTBRowR1D p lab) (h : GGLabelIso lab lab') :
    lab'.n = lab.n ∧ (GGTBRowR1A p lab' ∨ GGTBRowR1D p lab') := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  unfold GGTBRowR1A GGTBRowR1D at ht ⊢
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · injection h with h1 h2 h3
    subst h1; subst h2; subst h3
    exact ⟨rfl, ht⟩
  · obtain ⟨hb, -⟩ := h
    rcases hb with hb | hb <;> simp_all
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    injection h2 with h2a h2b h2c
    subst h1a; subst h2a; subst h2b; subst h2c
    exact ⟨rfl, Or.inl ⟨rfl, le_rfl⟩⟩
  · obtain ⟨h1, h2⟩ := h
    injection h1 with h1a h1b h1c
    injection h2 with h2a h2b h2c
    subst h1a; subst h2a; subst h2b; subst h2c
    exact ⟨rfl, Or.inr rfl⟩
  · obtain ⟨h1, -⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, -⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨h1, -⟩ := h
    injection h1 with h1a h1b h1c
    subst h1a
    simp_all
  · obtain ⟨-, h2⟩ := h
    injection h2 with h2a h2b h2c
    subst h2a; subst h2b
    simp_all

theorem ggTBJNaWeylQFourOn_rowR1AD
    (hRig : GGLabelRigidInput) :
    GGTBJRowTarget (fun p lab => GGTBRowR1A p lab ∨ GGTBRowR1D p lab) := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL hN
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hpar : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧
      (GGTBRowR1A p lab ∨ GGTBRowR1D p lab) ∧ p ∣ 2 ^ lab.n - 1) p Bs L :=
    ggInnerDiagOnLabel_r1Par_of_closed
      (P := fun p lab => GGTBRowR1A p lab ∨ GGTBRowR1D p lab) hRig
      (fun h => h.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
      ggR1ADRow_labelIso hHyp hL
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hpar
  obtain ⟨⟨hq4, hrow, hpn⟩, hBsN, hInd⟩ := hP
  obtain ⟨t, r, n⟩ := lab
  simp only [GGLabQFour] at hq4
  have hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = ⟨t, r, n⟩) p Bs L :=
    ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hΛ hhas
  simp only [GGTBRowR1A, GGTBRowR1D] at hrow
  rcases hrow with ⟨rfl, h3⟩ | rfl
  · exact ggTBJR1Lin_naWeylAt hcfg hpn hmark hN
  · have h3r : 3 ≤ r := hΛ.2
    by_cases hr3 : r = 3
    · subst hr3
      have hΛA : LargeEvenInLambda2 (⟨.A, 3, n⟩ : LargeEvenLabel) :=
        ⟨hΛ.1, by norm_num, fun h => by omega⟩
      have hhasA : GGHasLabel (⟨.A, 3, n⟩ : LargeEvenLabel)
          (↥L ⧸ Subgroup.center ↥L) :=
        ggHasLabel_D3_iff_A3.mp hhas
      have hmarkA : GGInnerDiagOnLabel (fun _ lab' => lab' = ⟨.A, 3, n⟩) p Bs L :=
        ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hΛA hhasA
      exact ggTBJR1Lin_naWeylAt hcfg hpn hmarkA hN
    · have hr4 : 4 ≤ r := by omega
      have hLD : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ lab.tag = .D ∧
          4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) p Bs L := by
        refine largeEvenMarking_mono ?_ hmark
        rintro lab' R' _ I' F' θ' ⟨hlab', hBsN', hInd'⟩
        subst hlab'
        exact ⟨⟨hq4, rfl, hr4, hpn⟩, hBsN', hInd'⟩
      exact ggTBJTorusReflSetIn_noncomm_of_at hcfg hN
        (ggTBJTorusNoncommAt_of_rowR1OmPlus hcfg hLD hN)

theorem ggTBJNoncommReflOn_of_rowR1AD
    (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGTBJNoncommReflOn fun p lab => S p lab ∧ ¬ (GGTBRowR1A p lab ∨ GGTBRowR1D p lab)) :
    GGTBJNoncommReflOn S :=
  ggTBJNoncommReflOn_of_split S (fun p lab => GGTBRowR1A p lab ∨ GGTBRowR1D p lab)
    ((ggTBJNoncommReflOn_of_naWeyl (ggTBJNaWeylQFourOn_rowR1AD hRig)).mono
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
