module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4EIn
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Five614Hyp {Γ : Type} [Group Γ] [Finite Γ] (H K T X : Subgroup Γ) : Prop :=
  SQTKGroup ↥H ∧ K ∈ cComp H ∧ CFSG.IsQuasisimple (ModO2 K) ∧
    T ≤ H ∧ IsPGroup 2 ↥T ∧ T ≤ Subgroup.normalizer (K : Set Γ) ∧ IsSylowTwoOf (T ⊓ K) K ∧
    X ≤ H ∧ X = oTwoUpper X ∧ (X ⊓ T).relIndex X = 5 ∧ ((X ⊓ T).subgroupOf X).Normal ∧
    T ≤ Subgroup.normalizer (X : Set Γ) ∧ X ≤ Subgroup.normalizer (K : Set Γ) ∧
    X ≤ K ⊔ centralizerMod (pCoreOf 2 K) H K ∧ ¬ ⁅X, K⁆ ≤ pCoreOf 2 K

@[expose] def Five614Concl {Γ : Type} [Group Γ] (K T X : Subgroup Γ) : Prop :=
  X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) ∨
    (X ≤ K ∧ ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e (ModO2 K)) ∨
      ∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧
        IsPSLEps3 δ p 1 (ModO2 K ⧸ Subgroup.center (ModO2 K)))) ∨
    IsTits (ModO2 K)

@[expose] def KG614FiveL2 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H K T X : Subgroup Γ), Five614Hyp H K T X →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ (f = 1 ∨ f = 2) ∧
      Assembly.LowTwoRank.StatedClassicalModel (ModO2 K ⧸ Subgroup.center (ModO2 K))
        Assembly.LowTwoRank.StatedLieTag.PSL 2 p f) →
    Five614Concl K T X

@[expose] def KG614FiveL3 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H K T X : Subgroup Γ), Five614Hyp H K T X →
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      (Assembly.LowTwoRank.StatedClassicalModel (ModO2 K ⧸ Subgroup.center (ModO2 K))
          Assembly.LowTwoRank.StatedLieTag.PSL 3 p 1 ∨
        Assembly.LowTwoRank.StatedClassicalModel (ModO2 K ⧸ Subgroup.center (ModO2 K))
          Assembly.LowTwoRank.StatedLieTag.PSU 3 p 1)) →
    Five614Concl K T X

@[expose] def KG614FiveChar2 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H K T X : Subgroup Γ), Five614Hyp H K T X →
    Ch1.SQTKCharTwoLie (ModO2 K ⧸ Subgroup.center (ModO2 K)) →
    Five614Concl K T X

@[expose] def KG614FiveSpor : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H K T X : Subgroup Γ), Five614Hyp H K T X →
    (Ch1.AltList (ModO2 K ⧸ Subgroup.center (ModO2 K)) ∨
      Ch1.SporadicList (ModO2 K ⧸ Subgroup.center (ModO2 K))) →
    Five614Concl K T X

theorem sqtkSimpleList_lStar614 (hlist : A23SQTKListFact) {Γ : Type} [Group Γ] [Finite Γ]
    {H K : Subgroup Γ} (hH : SQTKGroup ↥H) (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (ModO2 K)) :
    CFSG.Milestones.SQTKSimpleList (ModO2 K ⧸ Subgroup.center (ModO2 K)) := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hK
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  let eK : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  let ψ : ↥K' →* ModO2 K ⧸ Subgroup.center (ModO2 K) :=
    ((QuotientGroup.mk' (Subgroup.center (ModO2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).comp eK.toMonoidHom
  have hψ : Function.Surjective ψ :=
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)).comp eK.surjective
  let e : ↥K' ⧸ ψ.ker ≃* ModO2 K ⧸ Subgroup.center (ModO2 K) :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have hsimple : IsSimpleGroup (ModO2 K ⧸ Subgroup.center (ModO2 K)) := hKq.2.1
  have hnonab : ∃ a b : ModO2 K ⧸ Subgroup.center (ModO2 K), a * b ≠ b * a := hKq.2.2
  have hs' : IsSimpleGroup (↥K' ⧸ ψ.ker) := e.isSimpleGroup
  have hn' : ∃ a b : ↥K' ⧸ ψ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have := hlist ↥H hH K' ψ.ker hs' hn'
  exact Ch1.sqtkSimpleList_of_mulEquiv e.symm this

theorem kg614Five_of (hlist : A23SQTKListFact) (h2 : KG614FiveL2) (h3 : KG614FiveL3)
    (hc : KG614FiveChar2) (hs : KG614FiveSpor) : KG614Five := by
  intro Γ _ _ H K T X hH hK hKq hTH hT2 hTK hTs hXH hXO hX5 hXn hTX hXK hXinn hXnt
  have hyp : Five614Hyp H K T X :=
    ⟨hH, hK, hKq, hTH, hT2, hTK, hTs, hXH, hXO, hX5, hXn, hTX, hXK, hXinn, hXnt⟩
  have hl := sqtkSimpleList_lStar614 hlist hH hK hKq
  rw [Ch1.sqtkSimpleList_iff] at hl
  rcases hl with halt | ⟨p, hp, hp2, ⟨f, hf, hL2⟩ | hL3 | hU3⟩ | hc2 | hspor
  · exact hs Γ H K T X hyp (Or.inl halt)
  · exact h2 Γ H K T X hyp ⟨p, f, hp, hp2, hf, hL2⟩
  · exact h3 Γ H K T X hyp ⟨p, hp, hp2, Or.inl hL3⟩
  · exact h3 Γ H K T X hyp ⟨p, hp, hp2, Or.inr hU3⟩
  · exact hc Γ H K T X hyp hc2
  · exact hs Γ H K T X hyp (Or.inr hspor)

end CFSG.Quasithin.H13
