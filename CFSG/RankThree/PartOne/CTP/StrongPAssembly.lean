module

public import CFSG.RankThree.PartOne.CTP.StrongPSeitz
public import CFSG.RankThree.PartOne.CTP.StrongPL2
public import CFSG.RankThree.PartOne.CTP.StrongPLinear
public import CFSG.RankThree.PartOne.CTP.StrongPInspection
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded IsSylowOf omegaOne ExtSeitz ExtSPE)
open CFSG.RankThree.PartOne.Census3 (IsoLie TheoremThreeList)
open CFSG.RankThree.PartOne.StrongP
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def SPEConclusion (p : ℕ) (S : Type) [Group S] : Prop :=
  (∃ q : TauCeti.PrimePower, q.p = p ∧ (q.exponent = 2 ∨ q.exponent = 3) ∧
      IsoLie S (.A 1 q)) ∨
    (p = 5 ∧ (Nonempty (S ≃* alternatingGroup (Fin 10)) ∨ IsoLie S .tits ∨
      IsoLie S (.suzuki 2)))

@[expose] def BridgeTuple (S : Type) [Group S] (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ (t : StatedLieTag) (n r f : ℕ), StatedLieAdmissible t n r f ∧
    CFSG.Blueprint.LieModel S t n r f ∧ r = d.characteristic ∧
    ((t = .Tits ∧ n = 0 ∧ r = 2 ∧ f = 1) → d = .tits) ∧
    ((t = .twistedB2 ∧ n = 0 ∧ r = 2 ∧ f = 5) → d = .suzuki 2)

@[expose] def SeitzBridge : Prop :=
  ∀ (S : Type) [Group S] (d : TauCeti.LieTypeIndex), IsoLie S d → BridgeTuple S d

@[expose] def ThreeCatalog : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Census3.TheoremThreeHyp G → TheoremThreeList G

@[expose] def CharPNoncommInput : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] (q : TauCeti.PrimePower), q.p = p →
    (IsoLie S (.twistedA 2 q) ∨ IsoLie S (.twistedA 3 q) ∨ IsoLie S (.B 2 q) ∨
      IsoLie S (.G2 q)) → HasNoncommPair p S

@[expose] def SporadicStrongPInput : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → IsSimpleGroup ↥S →
      (∃ a b : ↥S, a * b ≠ b * a) →
      (∃ s ∈ Census3.sporadicsThm3, Nonempty (↥S ≃* (TauCeti.CFSGIndex.sporadic s).Group)) →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ Y : Subgroup H, IsStronglyPEmbedded p Y →
        ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
          (Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3) → False

section Cases

variable {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H]

theorem exists_pair_le {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) {P : Subgroup H}
    (hP : IsSylowOf p P ⊤) (hab : IsElementaryAbelian p (omegaOne p P))
    (hcard : Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3) :
    ∃ Y' E : Subgroup H, IsStronglyPEmbedded p Y' ∧ E ≤ Y' ∧ IsElementaryAbelian p E ∧
      Nat.card E = p ^ 2 := by
  obtain ⟨g, hg⟩ := hY.exists_conj_ge hP
  have hdvd : p ^ 2 ∣ Nat.card (omegaOne p P) := by
    rcases hcard with h | h <;> rw [h]
    exact pow_dvd_pow p (by norm_num)
  obtain ⟨E, hEA, hEab, hEc⟩ := exists_elementaryAbelian_sq_le (A := omegaOne p P) hdvd
  exact ⟨StrongP.conjSub g Y, E, hY.conj g, hEA.trans ((omegaOne_le P).trans hg), hEab, hEc⟩

theorem false_of_hasNoncommPair (S : Subgroup H) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hab : IsElementaryAbelian p (omegaOne p P)) (hpair : HasNoncommPair p ↥S) : False := by
  have h : HasNoncommPair p H := hpair.map S.subtype S.subtype_injective
  obtain ⟨x, y, hx, hy, hxy, hQ⟩ := h
  exact not_isMulCommutative_omegaOne hP hx hy hxy hQ hab.toIsMulCommutative

theorem hasNoncommPair_of_isoLie_A (hp5 : 5 ≤ p) {r : ℕ} (hr : 2 ≤ r) {S : Type} [Group S]
    {q : TauCeti.PrimePower} (hq : q.p = p) (h : IsoLie S (.A r q)) : HasNoncommPair p S := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  subst hq
  have e' := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)
  exact (hasNoncommPair_psl q.p (r + 1) (by omega) (by omega)).map e'.symm.toMonoidHom
    e'.symm.injective

theorem spe_conclusion_A1 (hp5 : 5 ≤ p) (S : Subgroup H) [S.Normal]
    (hSc : Subgroup.centralizer (S : Set H) = ⊥) {P : Subgroup H} (hP : IsSylowOf p P ⊤)
    (hcard : Nat.card (omegaOne p P) = p ^ 2 ∨ Nat.card (omegaOne p P) = p ^ 3)
    {q : TauCeti.PrimePower} (hq : q.p = p) (h : IsoLie ↥S (.A 1 q)) : SPEConclusion p ↥S := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  subst hq
  have e' := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have := l2_charP hp5 q.exponent_pos.ne' S e' hSc hP hcard
  exact Or.inl ⟨q, rfl, this, hv, ⟨e⟩⟩

theorem spe_conclusion_of_seitz (hSeitz : ExtSeitz) (hBridge : SeitzBridge)
    (hSchr : SchreierFor CFSG.Assembly.InCatalog) (hp5 : 5 ≤ p) (S : Subgroup H) [S.Normal]
    (hhyp : Census3.TheoremThreeHyp ↥S) (hSc : Subgroup.centralizer (S : Set H) = ⊥)
    {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) {E : Subgroup H} (hEY : E ≤ Y)
    [IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) {d : TauCeti.LieTypeIndex}
    (hiso : IsoLie ↥S d) (hne : d.characteristic ≠ p) : SPEConclusion p ↥S := by
  obtain ⟨t, n, r, f, hadm, hmodel, hr, hT, hSz⟩ := hBridge ↥S d hiso
  have := hhyp.isSimpleGroup
  have : Group.IsSolvable (Outer ↥S) := hSchr ↥S hhyp.nonabelian hhyp.exists_index
  obtain ⟨hp5', hexc⟩ := seitz_stronglyPEmbedded hSeitz hp5 S hadm hmodel
    (fun h => hne (hr ▸ h.symm)) hSc hY hEY hE
  refine Or.inr ⟨hp5', ?_⟩
  rcases hexc with h | h
  · exact Or.inr (Or.inl (hT h ▸ hiso))
  · exact Or.inr (Or.inr (hSz h ▸ hiso))

end Cases

end CFSG.RankThree.PartOne.CTP
