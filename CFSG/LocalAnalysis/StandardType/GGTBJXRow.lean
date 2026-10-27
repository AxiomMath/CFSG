module

public import CFSG.LocalAnalysis.StandardType.GGTBJXTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExc
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR4Narrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley

theorem GGTorusTBGroup.inn_of_outdiagPrime {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : GGOutdiagPrime p R I) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    {A : Subgroup (MulAut L')} (h : GGTorusTBGroup p r R I L' ψ A) :
    GGTorusTBGroup p r R (Set.range (MulAut.conj : R →* MulAut R)) L' ψ A := by
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := h
  refine ⟨hψ, hker, hperf, hA, fun a ha => ?_, hr, h3, hsc⟩
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  have hpow : ∀ (k : ℕ) (l : L'), (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; rfl
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
  have hφp : φ ^ p = 1 := by
    ext z
    obtain ⟨l, rfl⟩ := hψ z
    rw [hpow p l, hA.2 a ha]
    rfl
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hI φ hφ hφp)
  exact ⟨φ, ⟨g, hg⟩, hφa⟩

theorem ggInnerDiagOnLabel_excSplit_of_rowR1Exc (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧
      (GGTBRowR1E7 p lab ∨ GGTBRowR1E8 p lab ∨ (GGTBRowR1E6 p lab ∧ p ≠ 3))) p Bs L) :
    GGInnerDiagOnLabel (fun p lab => GGTableBE7E8Label p lab ∨ GGTableBE6LabelNotThree p lab)
      p Bs L := by
  have hst : LargeEvenStandardType p B x L := hHyp.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  obtain ⟨lab1, hlab1, hhas1, _, _, _, _, _, hP1⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨hQ4, hrow⟩ := hP1.1
  unfold GGLabQFour at hQ4
  unfold GGTBRowR1E7 GGTBRowR1E8 GGTBRowR1E6 at hrow
  have hexc : GGRootGenExcTag lab1 := by
    unfold GGRootGenExcTag
    rcases hrow with h | h | ⟨h, -⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
  have heq : labs = lab1 :=
    eq_of_ggLabelIso_of_excTag hexc (hRig lab1 labs _ hlab1 hlabs hhas1 hhass)
  have hs : LargeEvenSplit p lab1 := by
    have h := hPs.1
    rwa [heq] at h
  have hpn : p ∣ 2 ^ lab1.n - 1 := by
    have hn1 : lab1.n ≠ 1 := by omega
    obtain ⟨t, l, n⟩ := lab1
    dsimp only at hrow hn1 hs ⊢
    rcases hrow with h | h | ⟨h, -⟩ <;> subst h <;>
      simpa [LargeEvenSplit, LargeEvenUntwisted, hn1] using hs
  have hbad : GGTableBE7E8Label p lab1 ∨ GGTableBE6LabelNotThree p lab1 := by
    rcases hrow with h | h | ⟨h, h3⟩
    · exact Or.inl ⟨Or.inl h, hpn⟩
    · exact Or.inl ⟨Or.inr h, hpn⟩
    · exact Or.inr ⟨h, hpn, h3⟩
  have hmark := ggInnerDiagOn_relabel hRig hHyp.2.2.1.1 hlab1 hhas1
  refine largeEvenMarking_mono ?_ hmark
  intro lab' _ _ _ _ _ hP'
  obtain ⟨hlab', hBN, hBI⟩ := hP'
  exact ⟨by rw [hlab']; exact hbad, hBN, hBI⟩

theorem ggR1ExcRow_labelAll_adjoint
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : GGTableBE7E8Label p lab ∨ GGTableBE6LabelNotThree p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (τ : Tag) (_ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (_ : τ = .E6 → p ≠ 3) (K : Type) (_ : Field K)
        (_ : Finite K) (_ : CharP K 2) (_ : R ≃* ↥(adjointGroup τ K)),
        GGTorusLift p τ.rank R ∧ p ∣ Nat.card K - 1 ∧ GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  rcases h with ⟨htag | htag, hpn⟩ | ⟨htag, hpn, hp3⟩ <;> dsimp only at htag hpn <;> subst htag <;>
    intro Q hQ <;> obtain ⟨K, _, _, hK, hQ⟩ := hQ
  · have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by
      rw [hK]
      exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ, .E7, Or.inr (Or.inl rfl),
      (fun h => by cases h), K, inferInstance, inferInstance, this, TableBExc.recipeEquiv .E7 K,
      TableBExc.ggTorusLift_E7 hp hp2 hpq, hpq,
      fun φ hφ _ => MonoidHom.mem_range.mpr (TableBExc.idImage_subset_inn_E7 K hφ)⟩
  · have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by
      rw [hK]
      exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ, .E8, Or.inr (Or.inr rfl),
      (fun h => by cases h), K, inferInstance, inferInstance, this, TableBExc.recipeEquiv .E8 K,
      TableBExc.ggTorusLift_E8 hp hp2 hpq, hpq,
      fun φ hφ _ => MonoidHom.mem_range.mpr (TableBExc.idImage_subset_inn_E8 K hφ)⟩
  · have : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by
      rw [hK]
      exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ, .E6, Or.inl rfl, fun _ => hp3, K,
      inferInstance, inferInstance, this, TableBExc.recipeEquiv .E6 K,
      TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq, hpq, TableBExc.ggOutdiagPrime_E6 (K := K) hp hp3⟩

theorem ggTBJTorusNoncomm_rowR1Exc
    (hRig : GGLabelRigidInput) :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧
      (GGTBRowR1E7 p lab ∨ GGTBRowR1E8 p lab ∨ (GGTBRowR1E6 p lab ∧ p ≠ 3)) := by
  intro G _ _ p B Bs x L D J hHyp hq hok hL hN y hy hy1 J' hJ' _ hcount
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hLE : GGInnerDiagOnLabel
      (fun p lab => GGTableBE7E8Label p lab ∨ GGTableBE6LabelNotThree p lab) p Bs L :=
    ggInnerDiagOnLabel_excSplit_of_rowR1Exc hRig hHyp hL
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGTableBE7E8Label p lab ∨ GGTableBE6LabelNotThree p lab)
    (fun lab _ hs => nbrC_labelAll_guard (ggR1ExcRow_labelAll_adjoint hp hp2 hs))
    (fun _ _ _ _ _ _ hP => hP.1) hLE
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, τ, hτ, hp3, K, _, _, _, e, hlift, hpq, hIp⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := GGTorusTBGroup.inn_of_outdiagPrime hIp
    (ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3)
  have hTB' := GGTorusTBGroup.mulEquiv (I' := Set.range (MulAut.conj :
      ↥(adjointGroup τ K) →* MulAut ↥(adjointGroup τ K))) e (fun φ hφ => by
    obtain ⟨g, rfl⟩ := hφ
    exact ⟨e g, by
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  obtain ⟨hdet, hV, hT, hfullp⟩ := ggTBJX_typeFacts hτ hp hp2 hp3 hpq
  exact ggTBJX_torusJNoncomm hτ hp hp2 hpq hdet hV hT hfullp (e.toMonoidHom.comp (ggQuotHom θ)) _
    hTB' y hy hJ' hcount

theorem ggTBJNaWeylQFourOn_rowR1Exc
    (hRig : GGLabelRigidInput) :
    GGTBJRowTarget fun p lab =>
      GGTBRowR1E7 p lab ∨ GGTBRowR1E8 p lab ∨ (GGTBRowR1E6 p lab ∧ p ≠ 3) :=
  ggTBJNaWeylQFourOn_of_torusNoncomm (ggTBJTorusNoncomm_rowR1Exc hRig)

theorem ggTBJNoncommReflOn_of_rowR1Exc
    (hRig : GGLabelRigidInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGTBJNoncommReflOn fun p lab => S p lab ∧
      ¬ (GGTBRowR1E7 p lab ∨ GGTBRowR1E8 p lab ∨ (GGTBRowR1E6 p lab ∧ p ≠ 3))) :
    GGTBJNoncommReflOn S :=
  ggTBJNoncommReflOn_of_split S
    (fun p lab => GGTBRowR1E7 p lab ∨ GGTBRowR1E8 p lab ∨ (GGTBRowR1E6 p lab ∧ p ≠ 3))
    ((ggTBJNoncommReflOn_of_naWeyl (ggTBJNaWeylQFourOn_rowR1Exc hRig)).mono
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
