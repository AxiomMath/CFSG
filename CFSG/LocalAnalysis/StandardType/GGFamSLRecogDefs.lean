module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLInner
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLTypeA
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups commutatorElement

@[expose] def GGStrongRecogIn (P : StatedLieTag → ℕ → Prop) (p Q : ℕ) (C : Type) [Group C] : Prop :=
  commutator C = ⊤ ∧ ∃ (t : StatedLieTag) (n f : ℕ),
    LieModel (C ⧸ Subgroup.center C) t n p f ∧ p ^ f = Q ∧ P t n

@[expose] def GGStrongRecog (p Q : ℕ) (C : Type) [Group C] : Prop :=
  GGStrongRecogIn (fun t _ => t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨
    t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨ t = .trialityD4) p Q C

theorem GGStrongRecogIn.mono {P P' : StatedLieTag → ℕ → Prop} (hPP : ∀ t n, P t n → P' t n)
    {p Q : ℕ} {C : Type} [Group C] (h : GGStrongRecogIn P p Q C) : GGStrongRecogIn P' p Q C :=
  ⟨h.1, by
    obtain ⟨t, n, f, hmodel, hpow, hP⟩ := h.2
    exact ⟨t, n, f, hmodel, hpow, hPP t n hP⟩⟩

theorem ggStrongRecog_open_isQuasisimple {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q := by
  exact ⟨Group.isPerfect_def.1 h.1, h.2.1⟩

theorem ggStrongRecogIn_of_range {P : StatedLieTag → ℕ → Prop} {p Q : ℕ} {X G : Type} [Group X]
    [Group G] (h : GGStrongRecogIn P p Q X) (Ψ : X →* G) (hker : Ψ.ker ≤ Subgroup.center X)
    {H : Subgroup G} (hrange : Ψ.range = H) : GGStrongRecogIn P p Q ↥H := by
  have hmem : ∀ x, Ψ x ∈ H := fun x => hrange ▸ ⟨x, rfl⟩
  let g : X →* ↥H := Ψ.codRestrict H hmem
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ Ψ.range := hrange ▸ hy
    exact ⟨x, Subtype.ext hx⟩
  have hgk : g.ker ≤ Subgroup.center X := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  have hperfH : commutator ↥H = ⊤ := by
    have h1 := congrArg (Subgroup.map g) h.1
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective g hg] at h1
    rw [commutator_def]
    exact h1
  obtain ⟨t, n, f, hmodel, hpow, ht⟩ := h.2
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      h.1 g hg hgk
  exact ⟨hperfH, ⟨t, n, f, LieModel.of_mulEquiv e hmodel, hpow, ht⟩⟩

theorem lieModel_of_slCover
    {G : Type} [Group G] {X : Subgroup G}
    {K : Type} [Field K] [Finite K] {ν f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hν : 2 ≤ ν)
    (hK4 : ν = 2 → 4 ≤ Nat.card K)
    (g : SL(ν, K) →* ↥X)
    (hgsurj : Function.Surjective g) (hgker : g.ker ≤ Subgroup.center SL(ν, K)) :
    LieModel (↥X ⧸ Subgroup.center ↥X) .PSL ν 2 f := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have h4 : ν = 2 → 4 ≤ Fintype.card K := fun h => by
    rw [hcard, ← hK]; exact hK4 h
  have hperf : commutator (SL(ν, K)) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds K ν hν h4).perfect
  obtain ⟨e_quot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hgsurj hgker
  have hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL ν 2 f := by
    refine ⟨⟨Nat.prime_two, hf, hν, ?_, ?_⟩, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
    · intro hcon
      have h2f : 2 ^ f = 2 := congrArg Prod.snd hcon
      have h4' : 4 ≤ 2 ^ f := by rw [← hK]; exact hK4 (congrArg Prod.fst hcon)
      omega
    · intro hcon
      have h2f : 2 ^ f = 3 := congrArg Prod.snd hcon
      have h4' : 4 ≤ 2 ^ f := by rw [← hK]; exact hK4 (congrArg Prod.fst hcon)
      omega
    · exact e_quot.symm.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj ν K)
  exact Or.inl ⟨by simp [classicalTags], hmodel⟩

theorem ggCompFieldAtSL_of_slCover
    {G : Type} [Group G] {X : Subgroup G}
    {K : Type} [Field K] [Finite K] {ν f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hν : 2 ≤ ν)
    (hK4 : ν = 2 → 4 ≤ Nat.card K)
    (hq : CFSG.IsQuasisimple ↥X) (g : SL(ν, K) →* ↥X)
    (hgsurj : Function.Surjective g) (hgker : g.ker ≤ Subgroup.center SL(ν, K)) :
    CFSG.StandardType.GGCompFieldAtSL (2 ^ f) X :=
  ggCompFieldAtSL_of_lieModel (ggStrongRecog_open_isQuasisimple hq)
    (lieModel_of_slCover hf hK hν hK4 g hgsurj hgker) (by decide)

theorem lieModel_of_suCover
    {G : Type} [Group G] {X : Subgroup G}
    {K : Type} [Field K] [Finite K] {ν f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (hν : 3 ≤ ν)
    (h32 : (ν, 2 ^ f) ≠ (3, 2)) (g : ↥(StatedSU ν (2 ^ f) K) →* ↥X)
    (hgsurj : Function.Surjective g)
    (hgker : g.ker ≤ Subgroup.center ↥(StatedSU ν (2 ^ f) K)) :
    LieModel (↥X ⧸ Subgroup.center ↥X) .PSU ν 2 f := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card K = (2 ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have hperf : commutator ↥(StatedSU ν (2 ^ f) K) = ⊤ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      K ν (2 ^ f) hcard hν h32).perfect
  obtain ⟨e_quot⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
      hperf g hgsurj hgker
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := K) (p := 2) (f := f) hK hν h32).2
  have hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU ν 2 f :=
    ⟨⟨Nat.prime_two, hf, hν, h32⟩, K, inferInstance, inferInstance, hK,
      ⟨e_quot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ)⟩⟩
  exact Or.inl ⟨by simp [classicalTags], hmodel⟩

theorem ggCompFieldAtSL_of_suCover
    {G : Type} [Group G] {X : Subgroup G}
    {K : Type} [Field K] [Finite K] {ν f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) (hν : 3 ≤ ν)
    (h32 : (ν, 2 ^ f) ≠ (3, 2))
    (hq : CFSG.IsQuasisimple ↥X) (g : ↥(StatedSU ν (2 ^ f) K) →* ↥X)
    (hgsurj : Function.Surjective g)
    (hgker : g.ker ≤ Subgroup.center ↥(StatedSU ν (2 ^ f) K)) :
    CFSG.StandardType.GGCompFieldAtSL (2 ^ f) X :=
  ggCompFieldAtSL_of_lieModel (ggStrongRecog_open_isQuasisimple hq)
    (lieModel_of_suCover hf hK hν h32 g hgsurj hgker) (by decide)

end CFSG.StandardType.TableCRes
