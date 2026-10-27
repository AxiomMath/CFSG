module

public import CFSG.RankThree.PartOne.CTP.StrongPAssembly
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)

theorem bridgeTuple_of_classical {S : Type} [Group S] {d : TauCeti.LieTypeIndex}
    {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ CFSG.Blueprint.classicalTags)
    (hp : p = d.characteristic) (h : StatedClassicalModel S t n p f) : BridgeTuple S d := by
  refine ⟨t, n, p, f, h.1, Or.inl ⟨ht, h⟩, hp, fun hh => ?_, fun hh => ?_⟩
  · rw [hh.1] at ht
    simp [CFSG.Blueprint.classicalTags] at ht
  · rw [hh.1] at ht
    simp [CFSG.Blueprint.classicalTags] at ht

theorem bridgeTuple_A {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    BridgeTuple S (.A r q) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hmodel : StatedClassicalModel S .PSL (r + 1) q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (r + 1) _)⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      have := hrange.2 (by omega)
      simp only [TauCeti.PrimePower.card_def] at this
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      have := hrange.2 (by omega)
      simp only [TauCeti.PrimePower.card_def] at this
      omega
  exact bridgeTuple_of_classical (by simp [CFSG.Blueprint.classicalTags]) (by simp) hmodel

theorem bridgeTuple_twistedA {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    BridgeTuple S (.twistedA r q) :=
  bridgeTuple_of_classical (by simp [CFSG.Blueprint.classicalTags]) (by simp)
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)

theorem bridgeTuple_B2 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) : BridgeTuple S (.B 2 q) :=
  bridgeTuple_of_classical (by simp [CFSG.Blueprint.classicalTags]) (by simp)
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)

theorem bridgeTuple_C {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.C r q, hv⟩) : BridgeTuple S (.C r q) :=
  bridgeTuple_of_classical (by simp [CFSG.Blueprint.classicalTags]) (by simp)
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)

@[expose] def IsEasyIndex : TauCeti.LieTypeIndex → Prop
  | .A _ _ => True
  | .twistedA _ _ => True
  | .B r _ => r = 2
  | .C _ _ => True
  | _ => False

@[expose] def SeitzBridgeRest : Prop :=
  ∀ (S : Type) [Group S] (d : TauCeti.LieTypeIndex), IsoLie S d → ¬ IsEasyIndex d →
    BridgeTuple S d

theorem seitzBridge_of_rest (h : SeitzBridgeRest) : SeitzBridge := by
  intro S _ d hiso
  by_cases hd : IsEasyIndex d
  · obtain ⟨hv, ⟨e⟩⟩ := hiso
    cases d with
    | A r q => exact bridgeTuple_A r q hv e
    | twistedA r q => exact bridgeTuple_twistedA r q hv e
    | B r q =>
      have hr : r = 2 := hd
      subst hr
      exact bridgeTuple_B2 q hv e
    | C r q => exact bridgeTuple_C r q hv e
    | _ => exact absurd hd (by simp [IsEasyIndex])
  · exact h S d hiso hd

end CFSG.RankThree.PartOne.CTP
