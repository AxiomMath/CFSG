module

public import CFSG.Quasithin.H13.NQRigidAsmPair
public import CFSG.Quasithin.H13.NQBlockStmt1317Setup
public import CFSG.Quasithin.H13.NQRigidAsmSingle

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem rigidEscape_normal_of_irreducible (hcen : FactCenterOddPart) (houter : FactOuterPrime)
    (hB2 : StmtOuterRankContainment) {T L M : Subgroup G} {p : ℕ} {X : Subgroup G} {v : G}
    {K : Subgroup (centralizer ({v} : Set G))} (E : RigidEscape T L M p X v K)
    (hirr0 : IsFrattiniIrreducible (X.subgroupOf (centralizer ({v} : Set G)))
      ((M ⊓ centralizer {v}).subgroupOf (centralizer ({v} : Set G)) ⊓
        normalizer (K : Set (centralizer ({v} : Set G))))) :
    K.Normal ∧ X.subgroupOf (centralizer ({v} : Set G)) ≤ K := by
  classical
  have h := E.qtnq
  have hp := E.prime
  have hp5 := E.five_le
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hXH : X ≤ centralizer ({v} : Set G) := E.le_h
  let H := centralizer ({v} : Set G)
  have hH : H = centralizer ({v} : Set G) := rfl
  set A := (M ⊓ H).subgroupOf H with hA
  set X' := X.subgroupOf H with hX'
  set C := CFSG.pCore 2 H with hC
  set π := QuotientGroup.mk' C with hπ
  have hC2 : IsPGroup 2 C := CFSG.pCore_isPGroup
  have hCn : C.Normal := CFSG.pCore_normal
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_of_exponent E.exponent_eq
  obtain ⟨hX'2, hexp', -, -⟩ :=
    subgroupOf_transport hXH (inf_le_right : M ⊓ H ≤ H) E.no_quot E.exponent_eq E.rank_eq
      hp.one_lt E.irr_a
  have hW' : Nat.card ((X' ⧸ CFSG.pCore 2 X') ⧸ frattini (X' ⧸ CFSG.pCore 2 X')) = p ^ 2 := by
    rw [card_frattini_subgroupOf hXH, E.card_w]
  have hMX : M ≤ normalizer (X : Set G) := E.normalizer_eq.ge
  have hXM : X ≤ M := E.le_l.trans h.l_le
  have hX'A' : X' ≤ A := fun x hx => mem_subgroupOf.mpr ⟨hXM (mem_subgroupOf.mp hx), x.2⟩
  have hAN : A ≤ normalizer (X' : Set H) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    simp only [hX', mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hMX (mem_inf.mp (mem_subgroupOf.mp ha)).1) y
  have hX'Cn : (CFSG.pCore 2 X').Normal := CFSG.pCore_normal
  set A₀ := A ⊓ normalizer (K : Set H) with hA₀
  have hX'A₀ : X' ≤ A₀ := le_inf hX'A' E.x_normalizes
  have hA₀N : A₀ ≤ normalizer (X' : Set H) := inf_le_left.trans hAN
  have hA₀Q : A₀ ≤ normalizer (((CFSG.pCore 2 X').map X'.subtype : Subgroup H) : Set H) :=
    hA₀N.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hlat := isFrattiniLatticeIrreducible_of hirr0
  have hHSQ := isSQTKCat_centralizer h E.mem_u E.ne_one
  have hESQ := isSQTKCat_quotient_pCore hHSQ
  have hJSQ : CFSG.SectionRank.IsSQTKCat (K.map π) := hESQ.subgroup _
  have hZJ : ¬ p ∣ Nat.card (center (K.map π)) := hcen _ E.comp_e.1 hJSQ p hp hp5
  have hOuter := houter _ E.comp_e.1 hJSQ p hp hp5
  have hSQT := isStronglyQuasithin_centralizer h E.mem_u E.ne_one
  have hJX : ⁅K.map π, X'.map π⁆ ≠ ⊥ := by
    intro h1
    apply E.escapes_e
    rw [commutator_eq_bot_iff_le_centralizer] at h1
    exact h1.trans (centralizer_le_normalizer _)
  obtain ⟨-, -, hKn, hXK⟩ :=
    hB2 H p hp hp2 (hSQT p hp hp2) C hC2 K E.ccomp E.comp_e hZJ hOuter X' A₀ (CFSG.pCore 2 X')
      hX'A₀ inf_le_right hA₀Q hA₀N CFSG.pCore_isPGroup (pow_mem_pCore_of_exponent hexp') hX'2
      hW'.ge hlat hJX
  exact ⟨hKn, hXK⟩

theorem rigidEscape_false (hcen : FactCenterOddPart)
    (houter : FactOuterPrime) (hsect : FactSimpleQuotientSQT) (hnonsc : FactNonscalarG2Triality)
    (hree : FactLargeRee) (hthin : FactThinCentralQuotient) (hquad : FactQuadraticOffender)
    (hQTE : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hB2 : StmtOuterRankContainment)
    (hB3 : StmtPairContainment) (hB4 : StmtOrdinaryEvenSymplecticFour)
    (hB5 : StmtNoncyclicLocalSylowFourEven) (hB6 : StmtFourDivisibilityFields)
    (hB8 : StmtCPUOffenderSection) (hB9 : StmtCPUShortBlock) (hJ4 : StmtJ4SingleComponent)
    (hTits : StmtTitsSylowProduct) (hOD : StmtOuterDerivedCoprime)
    (hR2a : OblRigidCPUEvenLinearThreeParabolic) (hR2b : OblRigidCPUSymplecticFourDeleted)
    {T L M : Subgroup G} {p : ℕ} {X : Subgroup G} {v : G}
    {K : Subgroup (centralizer ({v} : Set G))} (E : RigidEscape T L M p X v K) : False := by
  by_cases hirr0 : IsFrattiniIrreducible (X.subgroupOf (centralizer ({v} : Set G)))
      ((M ⊓ centralizer {v}).subgroupOf (centralizer ({v} : Set G)) ⊓
        normalizer (K : Set (centralizer ({v} : Set G))))
  · obtain ⟨hKn, hXK⟩ := rigidEscape_normal_of_irreducible hcen houter hB2 E hirr0
    exact rigidSingle_false hcen hsect hnonsc hree hQTE hB4 hB5 hB6 hB8 hJ4 hTits hR2a hR2b
      ⟨E, hKn, hXK⟩
  · exact rigidPair_false hcen hsect hthin hquad hOD hB3 hB8 hB9 E hirr0

theorem internal_centralizer_le_of_explicit_module
    (hsing : FactWitnessSingleton) (hcen : FactCenterOddPart) (houter : FactOuterPrime)
    (hsect : FactSimpleQuotientSQT) (hnonsc : FactNonscalarG2Triality) (hree : FactLargeRee)
    (hthin : FactThinCentralQuotient) (hquad : FactQuadraticOffender)
    (hQTE : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hB1 : StmtEscapingComponentAction)
    (hB2 : StmtOuterRankContainment) (hB3 : StmtPairContainment)
    (hB4 : StmtOrdinaryEvenSymplecticFour) (hB5 : StmtNoncyclicLocalSylowFourEven)
    (hB6 : StmtFourDivisibilityFields) (hB8 : StmtCPUOffenderSection) (hB9 : StmtCPUShortBlock)
    (hJ4 : StmtJ4SingleComponent) (hTits : StmtTitsSylowProduct) (hOD : StmtOuterDerivedCoprime)
    (hR2a : OblRigidCPUEvenLinearThreeParabolic) (hR2b : OblRigidCPUSymplecticFourDeleted)
    {T L M : Subgroup G} (h : QTNQ T L M) (hmod : QTNQExplicitModule L M) {u : G}
    (hu : u ∈ qtnqU L M) (hu1 : u ≠ 1) : centralizer ({u} : Set G) ≤ M := by
  by_contra hCu
  obtain ⟨p, X, m, -, K, E⟩ := exists_rigidEscape hsing hB1 h hmod hu hu1 hCu
  exact rigidEscape_false hcen houter hsect hnonsc hree hthin hquad hQTE hB2 hB3 hB4 hB5 hB6 hB8
    hB9 hJ4 hTits hOD hR2a hR2b E

theorem nonquasisimpleInternalCentralizerRigidity_of_facts
    (hsing : FactWitnessSingleton) (hcen : FactCenterOddPart) (houter : FactOuterPrime)
    (hsect : FactSimpleQuotientSQT) (hnonsc : FactNonscalarG2Triality) (hree : FactLargeRee)
    (hthin : FactThinCentralQuotient) (hquad : FactQuadraticOffender)
    (hQTE : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hB1 : StmtEscapingComponentAction)
    (hB2 : StmtOuterRankContainment) (hB3 : StmtPairContainment)
    (hB4 : StmtOrdinaryEvenSymplecticFour) (hB5 : StmtNoncyclicLocalSylowFourEven)
    (hB6 : StmtFourDivisibilityFields) (hB8 : StmtCPUOffenderSection) (hB9 : StmtCPUShortBlock)
    (hJ4 : StmtJ4SingleComponent) (hTits : StmtTitsSylowProduct) (hOD : StmtOuterDerivedCoprime)
    (hR1 : OblRigidWholeModule) (hR2a : OblRigidCPUEvenLinearThreeParabolic)
    (hR2b : OblRigidCPUSymplecticFourDeleted) :
    NQBlock.NonquasisimpleInternalCentralizerRigidity := by
  intro G _ _ T L M h u hu hu1
  have hmod := hR1 G T L M h
  refine ⟨internal_centralizer_le_of_explicit_module hsing hcen houter hsect hnonsc hree hthin
    hquad hQTE hB1 hB2 hB3 hB4 hB5 hB6 hB8 hB9 hJ4 hTits hOD hR2a hR2b h hmod hu hu1,
    fun g hg => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hconj⟩ :=
    explicit_module_centralizer_irreducibility h hmod
  exact (hconj u hu g hg).2

end CFSG.Quasithin.H13.NQRigid
