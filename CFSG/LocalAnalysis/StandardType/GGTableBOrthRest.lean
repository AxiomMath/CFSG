module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace OrthRest

section Data

variable {p r : ℕ} {R : Type} [Group R]

theorem ggOutdiagPrime_inn : GGOutdiagPrime p R (LargeEvenInnSet R) :=
  fun _ hφ _ => hφ

theorem bstar_data (hp : p.Prime) (hZ : Subgroup.center R = ⊥) (hZp : GGCenterPrime p R)
    (hT : GGTorusLift p r R) (hB : GGBstarBoundInnR p r R (LargeEvenInnSet R)) :
    GGOutdiagOdd p R (LargeEvenInnSet R) ∧ ∃ r, GGTorusLift p r R ∧
      GGBstarBoundInn p r R (LargeEvenInnSet R) ∧
      (GGDeltaLocal p r R (LargeEvenInnSet R) ∨ GGBstarBoundDelta p r R (LargeEvenInnSet R)) :=
  ⟨ggOutdiagOdd_of_prime ggOutdiagPrime_inn, r, hT, ggBstarBoundInn_of_R hp hZ hB,
    Or.inl (ggDeltaLocal_of_prime ggOutdiagPrime_inn hZp)⟩

theorem endNode_data (hZ : Subgroup.center R = ⊥) (hZp : GGCenterPrime p R)
    (hT : GGTorusLift p r R) (hE : TableBUR.GGEndNodeEltAdm p r R) :
    ∃ r, GGTorusLift p r R ∧ GGEndNodeAdm p r R (LargeEvenInnSet R) := by
  refine ⟨r, hT, TableBUR.ggEndNodeAdm_of_eltAdm (fun _ hφ => hφ) hZ ?_ hE⟩
  intro L' _ _ ψ hψ hker hperf
  rw [TableBUR.ker_eq_center_of_surjective hψ hker hZ]
  exact hZp L' ψ hψ hker hperf

end Data

theorem labelAll {P : ℕ → ℕ → (R : Type) → [Group R] → Prop} (hP : GGOrthRestAll P) {p : ℕ}
    (hp : p.Prime) {lab : LargeEvenLabel} (h : GGOrthRestLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => I = LargeEvenInnSet R ∧ P p (lab.rank - 1) R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hl, ⟨ht, hpn⟩ | ⟨ht, hn, hp3⟩⟩ := h
  · dsimp only at ht hl hpn ⊢
    subst ht
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, b, c, hbc, hq, rfl, hP.1 K n (l - 1) p b c hK (by omega) hp hpn hbc⟩
  · dsimp only at ht hl hn hp3 ⊢
    subst ht hn hp3
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3
    · omega
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
    exact ⟨K, i1, i2, hK, hq, rfl, hP.2 K l (hK.trans (pow_one 2)) hl⟩

end OrthRest

theorem ggBstarInputOn_orthRestLabel (ha₀ : GGLNoncyclicInput) (hT : GGOrthRestTorusLiftInput)
    (hB : GGOrthRestBstarInput) (hZ : GGOrthRestCenterInput) : GGBstarInputOn GGOrthRestLabel :=
  ggBstarInputOn_of_labels_delta ha₀ fun _ _ hp _ h _ =>
    (((OrthRest.labelAll hT hp h).and (OrthRest.labelAll hB hp h)).and
      (OrthRest.labelAll hZ hp h)).mono fun R _ I _ ⟨⟨⟨hI, hT'⟩, _, hB'⟩, _, hZ1, hZp⟩ => by
        subst hI
        exact OrthRest.bstar_data hp hZ1 hZp hT' hB'

theorem ggStdSubPreInputOn_orthRestLabel (ha₀ : GGLNoncyclicInput)
    (hT : GGOrthRestTorusLiftInput) (hE : GGOrthRestEndNodeInput) (hZ : GGOrthRestCenterInput) :
    GGStdSubPreInputOn GGOrthRestLabel :=
  ggStdSubPreInputOn_of_labels_adm ha₀ fun _ _ hp _ h =>
    (((OrthRest.labelAll hT hp h).and (OrthRest.labelAll hE hp h)).and
      (OrthRest.labelAll hZ hp h)).mono fun R _ I _ ⟨⟨⟨hI, hT'⟩, _, hE'⟩, _, hZ1, hZp⟩ => by
        subst hI
        exact OrthRest.endNode_data hZ1 hZp hT' hE'

theorem ggBstarInputOn_orthRest_of_inputs (ha₀ : GGLNoncyclicInput)
    (hT : GGOrthRestTorusLiftInput) (hB : GGOrthRestBstarInput) (hZ : GGOrthRestCenterInput) :
    GGBstarInputOn (GGTableBRest3 GGTableBOrthLabel) :=
  (ggBstarInputOn_orthRestLabel ha₀ hT hB hZ).mono fun _ _ hlab hs h =>
    ggOrthRestLabel_of_rest3 hlab hs h

theorem ggStdSubPreInputOn_orthRest_of_inputs (ha₀ : GGLNoncyclicInput)
    (hT : GGOrthRestTorusLiftInput) (hE : GGOrthRestEndNodeInput) (hZ : GGOrthRestCenterInput) :
    GGStdSubPreInputOn (GGTableBRest3 GGTableBOrthLabel) :=
  (ggStdSubPreInputOn_orthRestLabel ha₀ hT hE hZ).mono fun _ _ hlab hs h =>
    ggOrthRestLabel_of_rest3 hlab hs h

end CFSG.StandardType
