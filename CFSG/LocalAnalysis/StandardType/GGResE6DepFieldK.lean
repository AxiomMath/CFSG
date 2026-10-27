module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGResAssembly
public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrders

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nL4k_unique_A5 (hRig : GGLabelRigidInput) {R : Type} [Group R]
    {lab lab' : LargeEvenLabel} (hA : GGA5Label lab) (h2 : LargeEvenInLambda2 lab)
    (h2' : LargeEvenInLambda2 lab') (hl : GGHasLabel lab R) (hl' : GGHasLabel lab' R) :
    lab' = lab := by
  have h := hRig lab lab' R h2 h2' hl hl'
  have hr : lab.rank = 5 := hA.1
  have ht : lab.tag = .A ∨ lab.tag = .twA := by
    rcases hA.2 with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h.symm
  · rcases h with ⟨hbc, -⟩
    rcases hbc with hbc | hbc <;> rw [hbc] at ht <;> exact absurd ht (by decide)
  · rcases h with ⟨heq, -⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)
  · rcases h with ⟨heq, -⟩
    have hrank := congrArg LargeEvenLabel.rank heq
    simp at hrank
    omega
  · rcases h with ⟨heq, -⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)
  · rcases h with ⟨heq, -⟩
    have hrank := congrArg LargeEvenLabel.rank heq
    simp at hrank
    omega
  · rcases h with ⟨heq, -⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)
  · rcases h with ⟨-, heq⟩
    have hrank := congrArg LargeEvenLabel.rank heq
    simp at hrank
    omega

private theorem l05nL4k_unique_E6 (hRig : GGLabelRigidInput) {R : Type} [Group R]
    {lab lab' : LargeEvenLabel} (hK : GGE6DepLabel lab) (h2 : LargeEvenInLambda2 lab)
    (h2' : LargeEvenInLambda2 lab') (hl : GGHasLabel lab R) (hl' : GGHasLabel lab' R) :
    lab' = lab := by
  have h := hRig lab lab' R h2 h2' hl hl'
  have ht : lab.tag = .E6 ∨ lab.tag = .twE6 := by
    rcases hK with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h.symm
  · rcases h with ⟨hbc, -⟩
    rcases hbc with hbc | hbc <;> rw [hbc] at ht <;> exact absurd ht (by decide)
  · rcases h with ⟨heq, -⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)
  · rcases h with ⟨heq, -⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)
  · rcases h with ⟨heq, -⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)
  · rcases h with ⟨heq, -⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)
  · rcases h with ⟨heq, -⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)
  · rcases h with ⟨-, heq⟩
    have htag := congrArg LargeEvenLabel.tag heq
    simp at htag
    rw [htag] at ht
    exact absurd ht (by decide)

theorem ggResE6Dep_K_field_of_tablePRow
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hRig : GGLabelRigidInput) (hT3 : GGSchurDvdInput) (hH : GGResHyp p B Bs x L D J y K)
    {labJ labK : LargeEvenLabel} (hJ2 : LargeEvenInLambda2 labJ) (hK2 : LargeEvenInLambda2 labK)
    (hJ : GGA5Label labJ) (hK : GGE6DepLabel labK)
    (hlJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hlK : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K))
    (hJK : J ≤ K)
    (hrowData : ∃ labJ' labK' : LargeEvenLabel, LargeEvenInLambda2 labJ' ∧
      LargeEvenInLambda2 labK' ∧ GGTablePRow p labJ' labK' ∧
      GGHasLabel labJ' (J ⧸ Subgroup.center J) ∧ GGHasLabel labK' (K ⧸ Subgroup.center K)) :
    labK.n = labJ.n := by
  have hDJ : LargeEvenStdSub p B x L D J := hH.1.2.2
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  have hKcomp : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hnbr)).1
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hDJ.1.2.2.2.2.2.1.2.2
  have hKq : CFSG.Assembly.IsQuasisimple ↥K := hKcomp.2.2
  have hJperf : commutator ↥J = ⊤ := hJq.1
  have hKperf : commutator ↥K = ⊤ := hKq.1
  have hJnt : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJq.2.toNontrivial
  have hKnt : Nontrivial (↥K ⧸ Subgroup.center ↥K) := hKq.2.toNontrivial
  obtain ⟨labJ', labK', hJ2', hK2', hrow, hlJ', hlK'⟩ :=
    hrowData
  have hJ'eq : labJ' = labJ := l05nL4k_unique_A5 hRig hJ hJ2 hJ2' hlJ hlJ'
  have hK'eq : labK' = labK := l05nL4k_unique_E6 hRig hK hK2 hK2' hlK hlK'
  rw [hJ'eq, hK'eq] at hrow
  have htagJ : labJ.tag = .A ∨ labJ.tag = .twA := by
    rcases hJ.2 with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have htagK : labK.tag = .E6 ∨ labK.tag = .twE6 := by
    rcases hK with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hfield := tablePRow_E6_field hrow htagJ hJ.1 htagK
  rcases hfield with hEq | ⟨-, -, h3⟩
  · exact hEq
  · exfalso
    have hge : 15 * labJ.n ≤ (Nat.card ↥J).factorization 2 :=
      ggResE6Dep_two_part_ge_A5 hJperf hJnt hJ2 hJ hlJ
    have hle : (Nat.card ↥K).factorization 2 ≤ 36 * labK.n + 2 :=
      ggResE6Dep_two_part_le_E6 hT3 hKperf hKnt hK2 hK hlK
    have hdvd : Nat.card ↥J ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hJK
    haveI : Nonempty ↥J := ⟨1, J.one_mem⟩
    haveI : Nonempty ↥K := ⟨1, K.one_mem⟩
    have hJne : Nat.card ↥J ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    have hKne : Nat.card ↥K ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    have hfac : (Nat.card ↥J).factorization 2 ≤ (Nat.card ↥K).factorization 2 :=
      (Nat.factorization_le_iff_dvd hJne hKne).2 hdvd 2
    have hn1 : 1 ≤ labK.n := hK2.1
    omega

theorem ggResE6Dep_K_field
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hTP : GGNbrTablePConfig p B Bs x L D J) (hI3 : GGNbrSubcomponentInput)
    (hRig : GGLabelRigidInput) (hT3 : GGSchurDvdInput) (hH : GGResHyp p B Bs x L D J y K)
    {labJ labK : LargeEvenLabel} (hJ2 : LargeEvenInLambda2 labJ) (hK2 : LargeEvenInLambda2 labK)
    (hJ : GGA5Label labJ) (hK : GGE6DepLabel labK)
    (hlJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hlK : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K)) : labK.n = labJ.n := by
  exact ggResE6Dep_K_field_of_tablePRow hRig hT3 hH hJ2 hK2 hJ hK hlJ hlK
    (hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hH.2.2.2.2.1)
    (tablePRow_of_resHyp hTP hH hJ2 hK2 hlJ hlK)

end CFSG.StandardType
