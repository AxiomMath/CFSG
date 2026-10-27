module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenAltProofBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Cases

variable {G : Type} [Group G]

@[expose] def GGSixLSevenA3Case (J : Subgroup G) : Prop :=
  LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 1

@[expose] def GGSixLSevenE6Case (p : ℕ) (L J : Subgroup G) (t : StatedLieTag) (f : ℕ) : Prop :=
  p = 3 ∧ t = .E6 ∧ f = 1 ∧ LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 6 2 1 ∧
    LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 2

end Cases

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.perD_pOne_of_inner (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    {R : Subgroup G} (hRJ : R ≤ J) {d : G} (hd : d ∈ D)
    (hZ : Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))))
    (hin : ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
      ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G)) :
    ggSR p B x L D J R ⊓ Subgroup.centralizer {d} ≤
      pCoreOf 2 (ggKd p B x L D J d ⊓ Subgroup.normalizer (R : Set G)) ⊔
        Subgroup.centralizer (ggKd p B x L D J d : Set G) := by
  refine ggLe_pCoreOf_sup_centralizer_of_le_sup (hRJ.trans (le_ggKd p B x L D J d))
    ((ggPCoreOf_two_isPGroup _).to_le (inf_le_left.trans inf_le_left))
    ((inf_le_left.trans inf_le_left).trans (ggPR_le_normalizer R)) ?_ hZ hin
  intro m hm
  obtain ⟨hmK, hmR⟩ := Subgroup.mem_inf.mp hm
  have hmP : m ∈ Subgroup.normalizer (ggPR R : Set G) := mem_normalizer_pCoreOf hmR
  have hmN₀ : m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) :=
    Subgroup.mem_inf.mpr ⟨h.ggKd_le_ggG0 hd hmK, hmR⟩
  have hmQ : m ∈ Subgroup.normalizer (ggQR p B x L D J R : Set G) :=
    mem_normalizer_pCoreOf hmN₀
  have hmS : m ∈ Subgroup.normalizer (ggSR p B x L D J R : Set G) :=
    mem_normalizer_inf hmP (Subgroup.le_normalizer hmQ)
  exact mem_normalizer_inf hmS (Subgroup.le_normalizer (h.ggKd_le_centralizer hd hmK))

theorem GGSixCtxV2.sQC_of_inner (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {R : Subgroup G}
    (hRJ : R ≤ J) (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    (hin : ggSR p B x L D J R ≤
      ggG0 p B x L D J ⊔ Subgroup.centralizer (ggG0 p B x L D J : Set G)) :
    ggSR p B x L D J R ≤
      ggQR p B x L D J R ⊔ Subgroup.centralizer (ggG0 p B x L D J : Set G) := by
  have hZ : Odd (Nat.card (Subgroup.center ↥(ggG0 p B x L D J))) := by
    rw [← Subgroup.card_map_of_injective (ggG0 p B x L D J).subtype_injective]
    refine Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le ?_)
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  refine ggLe_pCoreOf_sup_centralizer_of_le_sup (hRJ.trans h.le_ggG0)
    ((ggPCoreOf_two_isPGroup _).to_le inf_le_left) (inf_le_left.trans (ggPR_le_normalizer R))
    ?_ hZ hin
  intro m hm
  have hmP : m ∈ Subgroup.normalizer (ggPR R : Set G) :=
    mem_normalizer_pCoreOf (Subgroup.mem_inf.mp hm).2
  have hmQ : m ∈ Subgroup.normalizer (ggQR p B x L D J R : Set G) := mem_normalizer_pCoreOf hm
  exact mem_normalizer_inf hmP (Subgroup.le_normalizer hmQ)

theorem ggSixLSevenItemFour_of_alt (p : ℕ) (B : Subgroup G) (x : G) (L D J R : Subgroup G)
    (h4 : (⁅ggQR p B x L D J R, ggQR p B x L D J R⁆ ≤ R ∧
        ggQR p B x L D J R ≤ Subgroup.centralizer (R : Set G)) ∨
      ∀ U : Subgroup G, ggCenterOf (ggQR p B x L D J R) ≤ U → U ≤ ggQR p B x L D J R →
        U ≠ ggCenterOf (ggQR p B x L D J R) → U ≠ ggQR p B x L D J R →
        ggG0 p B x L D J ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (U : Set G) →
        J ⊔ U = ggG0 p B x L D J) :
    ggCenterOf (ggQR p B x L D J R) ≤ ggPR R → ggPR R ≤ ggQR p B x L D J R →
      ggPR R ≠ ggQR p B x L D J R →
      ¬ ggQR p B x L D J R ≤ Subgroup.centralizer (ggPR R : Set G) →
        (⁅ggQR p B x L D J R, ggQR p B x L D J R⁆ ≤ R ∧
          ggQR p B x L D J R ≤ Subgroup.centralizer (R : Set G)) ∨
        J ⊔ ggPR R = ggG0 p B x L D J := by
  intro hZP hPQ hne hnc
  rcases h4 with h | h
  · exact Or.inl h
  refine Or.inr (h _ hZP hPQ ?_ hne fun m hm => mem_normalizer_pCoreOf (Subgroup.mem_inf.mp hm).2)
  intro heq
  apply hnc
  rw [heq]
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨q, hq⟩)).symm

end Ctx

section Inputs

@[expose] def GGSixLSixSevenConjA3Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    GGSixLSevenA3Case J →
      ∃ g ∈ ggG0 p B x L D J, D.map (MulAut.conj g).toMonoidHom ≤ J

end Inputs

end CFSG.StandardType
