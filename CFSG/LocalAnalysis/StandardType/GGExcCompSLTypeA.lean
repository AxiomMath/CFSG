module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate3951
public import Certificates.Certificate13659

import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.Adapters.CatalogueFieldBridges.UnitarySU
import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.GLTheoremA.RationalModel
open scoped MatrixGroups

private theorem langRatFASL_rankOne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hr1 : compRank (componentRoots (rootCharHom a) i) = 1)
    (hn : (componentRoots (rootCharHom a) i).ncard = 2)
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, hring, hK4, g, hgsurj, hgker⟩ :=
    exists_slCover_rationalComponent_rankOne S hT i hr1 hn hq
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have hK2 : Nat.card K = 2 ^ f := by rw [hKcard, h2]
  have hperf : commutator (SL(2, K)) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds K 2 (by norm_num)
      (fun _ => by rw [← Nat.card_eq_fintype_card]; exact hK4)).perfect
  obtain ⟨e_quot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hgsurj hgker
  have hmodel : StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL 2 2 f := by
    refine ⟨⟨Nat.prime_two, hf1, by norm_num, ?_, ?_⟩, K, hfield, hfinite, hK2, ⟨?_⟩⟩
    · intro hcon
      exact absurd (congrArg Prod.snd hcon) (by omega)
    · intro hcon
      exact absurd (congrArg Prod.snd hcon) (by omega)
    · exact e_quot.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)
  have hlie : LieModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL 2 2 f :=
    Or.inl ⟨by simp [classicalTags], hmodel⟩
  have hqO : CFSG.Open.IsQuasisimple
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hgg := ggCompFieldAtSL_of_lieModel hqO hlie (by decide)
  have h2f : 2 ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [← h2, hfeq]
  rw [h2f] at hgg
  exact hgg

private theorem langRatFASL_splitFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, hring, g, hgsurj, hgker⟩ :=
    exists_slCover_rationalComponent_splitFrame S hT i hν hψ hΨ π hπ
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have hK2 : Nat.card K = 2 ^ f := by rw [hKcard, h2]
  have hperf : commutator (SL(ν, K)) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds K ν (by omega)
      (fun h => by omega)).perfect
  obtain ⟨e_quot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hgsurj hgker
  have hmodel : StatedClassicalModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL ν 2 f := by
    refine ⟨⟨Nat.prime_two, hf1, by omega, ?_, ?_⟩, K, hfield, hfinite, hK2, ⟨?_⟩⟩
    · intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
    · intro hcon
      exact absurd (congrArg Prod.fst hcon) (by omega)
    · exact e_quot.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj ν K)
  have hlie : LieModel
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSL ν 2 f :=
    Or.inl ⟨by simp [classicalTags], hmodel⟩
  have hqO : CFSG.Open.IsQuasisimple
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hgg := ggCompFieldAtSL_of_lieModel hqO hlie (by decide)
  have h2f : 2 ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [← h2, hfeq]
  rw [h2f] at hgg
  exact hgg

private theorem slb_lieModel_twistedA
    {G : Type} [Group G] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hd : (TauCeti.LieTypeIndex.twistedA r q).characteristic = 2)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩) :
    ∃ n f : ℕ, CFSG.Blueprint.LieModel G .PSU n 2 f ∧
      CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize
        (TauCeti.LieTypeIndex.twistedA r q) = 2 ^ f := by
  have hp : q.p = 2 := by simpa using hd
  have h := CFSG.Models.lieModel_twistedA r q hv e
  have hc : TauCeti.ValidLieTypeIndex.characteristic
      ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = 2 := hd
  rw [hc] at h
  exact ⟨_, _,
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [CFSG.Blueprint.classicalTags]) h,
    by
      show q.card = _
      rw [TauCeti.PrimePower.card_def, hp, TauCeti.ValidLieTypeIndex.fieldExponent,
        TauCeti.LieTypeIndex.fieldExponent_twistedA]⟩

private theorem langRatFASL_unitaryFrame
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨K, hfield, hfinite, f, hf1, hKcard, hfeq, hring, h32, g, hgsurj, hgker⟩ :=
    exists_suCover_rationalComponent_unitaryFrame S hT i hν hψ hΨ π hπ hq
  letI : Field K := hfield
  letI : Finite K := hfinite
  letI : Fintype K := Fintype.ofFinite K
  have h2 : ringChar L = 2 := ringChar.eq L 2
  have hK' : Fintype.card K = (ringChar L ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  have hperf : commutator ↥(StatedSU ν (ringChar L ^ f) K) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds K ν (ringChar L ^ f)
      hK' hν h32).perfect
  obtain ⟨e_quot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hgsurj hgker
  obtain ⟨q', hv, hq'p, hq'card, ⟨e'⟩⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.exists_twistedA_mulEquiv_centerQuotient_statedSU
      hK' hν h32
  have hch : (TauCeti.LieTypeIndex.twistedA (ν - 1) q').characteristic = 2 := by
    rw [TauCeti.LieTypeIndex.characteristic_twistedA, hq'p, hring, h2]
  obtain ⟨n, f', hlie, hfs⟩ :=
    slb_lieModel_twistedA (ν - 1) q' hv hch (e_quot.symm.trans e')
  have hqO : CFSG.Open.IsQuasisimple
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hgg : GGCompFieldAtSL (2 ^ f') (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    ggCompFieldAtSL_of_lieModel hqO hlie (Or.inr (Or.inl rfl))
  have h2f : 2 ^ f' = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    rw [← hfs]
    show q'.card = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    rw [hq'card, hfeq]
  rw [h2f] at hgg
  exact hgg

theorem langRatFieldSL_typeA
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  rcases typeA_frame_cases S hp hT hap h1 i hA with ⟨hr1, hn⟩ | h | h
  · exact langRatFASL_rankOne S hT i hr1 hn hq
  · obtain ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩ := h
    exact langRatFASL_splitFrame S hT i hν hψ hΨ π hπ hq
  · obtain ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩ := h
    exact langRatFASL_unitaryFrame S hT i hν hψ hΨ π hπ hq

end CFSG.StandardType.LangRat
