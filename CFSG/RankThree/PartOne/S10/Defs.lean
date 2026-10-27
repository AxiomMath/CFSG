module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.RankThree.GroupTheory.SteinbergCESectionTenStrata
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.GroupTheory.SteinbergBMSectionTenSetup
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.GH74.EvenRank
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement Pointwise

@[expose] noncomputable def oddThetaCore {G : Type} [Group G] (p : ℕ) (L : Subgroup G) :
    Subgroup G :=
  inSubgroup oddCore (inSubgroup (aschbacherSolvableCore p) L)

@[expose] def fiveActorPlane {G : Type} [Group G] (a b : G) : Subgroup G :=
  Subgroup.zpowers a ⊔ Subgroup.zpowers b

@[expose] def fiveResidual {G : Type} [Group G] (L : Subgroup G) (x : G) : Subgroup G :=
  inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G))

structure FiveCriticalData {G : Type} [Group G] [Finite G] (A L : Subgroup G) (c : G) (q : ℕ)
    (D R : Subgroup G) : Prop where
  setup : SteinbergBM.SectionTenSetup G 5 A
  c_mem : c ∈ A
  c_ne_one : c ≠ 1
  mem_family : L ∈ sectionTenAt 5 (sectionTenZero 5 A) c
  nonquasisimple : ¬ CFSG.IsQuasisimple L
  A_normalizes : A ≤ Subgroup.normalizer (L : Set G)
  q_prime : q.Prime
  q_ne_two : q ≠ 2
  q_ne_five : q ≠ 5
  D_le_L : D ≤ L
  D_char : (D.subgroupOf L).Characteristic
  D_ne_bot : D ≠ ⊥
  D_le_O : D ≤ oddThetaCore 5 L
  D_exponent : ∀ x ∈ D, x ^ q = 1
  D_class : ⁅⁅D, D⁆, D⁆ = ⊥
  R_two : IsPGroup 2 R
  R_le_L : R ≤ L
  R_invariant : A ≤ Subgroup.normalizer (R : Set G)
  R_comm : ⁅R, A⁆ = R
  R_ne_bot : R ≠ ⊥
  R_acts : ⁅R, D⁆ ≠ ⊥
  kernel_R : A ⊓ Subgroup.centralizer (R : Set G) = thetaQuotientCentralizer 5 A L
  fixed_rank : ∀ r ∈ R, r ≠ 1 →
    CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3
  relative_minimal : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) →
    ⁅U, A⁆ = U → ⁅U, D⁆ = ⊥
  E_card : Nat.card (thetaQuotientCentralizer 5 A L) = 25
  c_mem_E : c ∈ thetaQuotientCentralizer 5 A L
  odd_normal : ((oddThetaCore 5 L).subgroupOf L).Normal
  odd_quotient_quasisimple :
    haveI := odd_normal
    CFSG.IsQuasisimple (L ⧸ (oddThetaCore 5 L).subgroupOf L)
  E_trivial_mod_O : ∀ e ∈ thetaQuotientCentralizer 5 A L, ∀ l ∈ L,
    e * l * e⁻¹ * l⁻¹ ∈ oddThetaCore 5 L
  E_scalar : ∀ e ∈ thetaQuotientCentralizer 5 A L,
    ∃ k : ℕ, ∀ d ∈ D, (e * d * e⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D
  residual_theta : ∀ x ∈ thetaQuotientCentralizer 5 A L, x ≠ 1 →
    (fiveResidual L x).subgroupOf (L ⊓ Subgroup.centralizer ({x} : Set G)) ∈
      thetaComponents 5 ↥(L ⊓ Subgroup.centralizer ({x} : Set G))
  residual_supplement : ∀ x ∈ thetaQuotientCentralizer 5 A L, x ≠ 1 →
    L = oddThetaCore 5 L ⊔ fiveResidual L x
  residual_fixed : ∀ x ∈ thetaQuotientCentralizer 5 A L, x ≠ 1 →
    L ⊓ Subgroup.centralizer ({x} : Set G) =
      (oddThetaCore 5 L ⊓ Subgroup.centralizer ({x} : Set G)) ⊔ fiveResidual L x
  R_le_residual : ∀ x ∈ thetaQuotientCentralizer 5 A L, x ≠ 1 → R ≤ fiveResidual L x
  branch_central : ⁅thetaQuotientCentralizer 5 A L, D⁆ = ⊥ →
    ∀ x ∈ thetaQuotientCentralizer 5 A L, x ≠ 1 → ¬ CFSG.IsQuasisimple (fiveResidual L x)
  branch_noncentral : ⁅thetaQuotientCentralizer 5 A L, D⁆ ≠ ⊥ →
    q % 5 = 1 ∧ localRank q G ≤ 2 ∧ Nonempty (R ≃* QD32) ∧
    R ⊓ Subgroup.centralizer (D : Set G) = ⊥ ∧
    (∀ r ∈ R, (∀ d ∈ D, (r * d * r⁻¹)⁻¹ * d ∈ inSubgroup frattini D) → r = 1) ∧
    ⁅D, R⁆ = D ∧ ⁅D, thetaQuotientCentralizer 5 A L⁆ = D ∧ IsQDShape q D ∧
    (inSubgroup frattini D).relIndex D = q ^ 4 ∧
    (∃ χ : ↥(thetaQuotientCentralizer 5 A L) →* (ZMod q)ˣ,
      (∀ (t : thetaQuotientCentralizer 5 A L) (d : G), d ∈ D →
        ((t : G) * d * (t : G)⁻¹)⁻¹ * d ^ ((χ t : ZMod q).val) ∈ inSubgroup frattini D) ∧
      Nat.card χ.range = 5 ∧
      χ.ker.map (thetaQuotientCentralizer 5 A L).subtype = Subgroup.zpowers c ∧
      thetaQuotientCentralizer 5 A L ⊓ Subgroup.centralizer (D : Set G) =
        Subgroup.zpowers c) ∧
    ∃ z ∈ R, z ≠ 1 ∧ z ^ 2 = 1 ∧ inSubgroup Subgroup.center R = Subgroup.zpowers z ∧
      A ≤ Subgroup.centralizer ({z} : Set G) ∧
      (∀ d ∈ D, z * d * z⁻¹ * d ∈ inSubgroup frattini D) ∧
      ∀ x ∈ thetaQuotientCentralizer 5 A L, x ≠ 1 → CFSG.IsQuasisimple (fiveResidual L x) →
        x ∉ Subgroup.zpowers c ∧ z ∈ fiveResidual L x ∧
          z ∈ Subgroup.centralizer (fiveResidual L x : Set G)
  actors : ∀ a ∈ A, a ∉ thetaQuotientCentralizer 5 A L →
    ∀ b ∈ thetaQuotientCentralizer 5 A L, b ∉ Subgroup.zpowers c →
      Nat.card (Subgroup.zpowers a) = 5 ∧ Nat.card ↥(fiveActorPlane a b) = 25 ∧
      Subgroup.zpowers a ≤ fiveActorPlane a b ∧ fiveActorPlane a b ≤ A ∧
      fiveActorPlane a b ≤ Subgroup.normalizer (R : Set G) ⊓ Subgroup.normalizer (D : Set G) ∧
      ⁅R, Subgroup.zpowers a⁆ = R ∧ ⁅R, fiveActorPlane a b⁆ = R ∧
      fiveActorPlane a b ⊓ Subgroup.centralizer (R : Set G) = Subgroup.zpowers b ∧
      ∀ U : Subgroup G, U ≤ R →
        (A ≤ Subgroup.normalizer (U : Set G) ↔
          fiveActorPlane a b ≤ Subgroup.normalizer (U : Set G)) ∧
        (A ≤ Subgroup.normalizer (U : Set G) ↔
          Subgroup.zpowers a ≤ Subgroup.normalizer (U : Set G)) ∧
        (A ≤ Subgroup.normalizer (U : Set G) →
          ⁅U, A⁆ = ⁅U, fiveActorPlane a b⁆ ∧ ⁅U, A⁆ = ⁅U, Subgroup.zpowers a⁆)

structure FiveSuccessorData {G : Type} [Group G] [Finite G] (A L : Subgroup G) (c : G) (q : ℕ)
    (D R : Subgroup G) (e : G) (K : Subgroup G) : Prop where
  critical : FiveCriticalData A L c q D R
  maximal : ∀ Y ∈ sectionTenZero 5 A, ¬ CFSG.IsQuasisimple Y →
    sectionTenRel 5 L Y → sectionTenRel 5 Y L
  e_mem : e ∈ thetaQuotientCentralizer 5 A L
  e_notMem : e ∉ Subgroup.zpowers c
  K_mem : K ∈ sectionTenAt 5 (sectionTenZero 5 A) e
  L_le_K : sectionTenRel 5 L K
  not_K_le_L : ¬ sectionTenRel 5 K L
  K_quasisimple : CFSG.IsQuasisimple K
  R_le_P : R ≤ fiveResidual L e
  P_le : fiveResidual L e ≤ L ⊓ K
  L_eq : L = oddThetaCore 5 L ⊔ fiveResidual L e
  P_mem : (fiveResidual L e).subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G)) ∈
    thetaComponents 5 ↥(K ⊓ Subgroup.centralizer ({c} : Set G))
  A_normalizes_K : A ≤ Subgroup.normalizer (K : Set G)
  E_eq : thetaQuotientCentralizer 5 A L = Subgroup.zpowers c ⊔ Subgroup.zpowers e
  CA_K : A ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers e
  c_order : ∀ hc : c ∈ Subgroup.normalizer (K : Set G),
    orderOf (K.normalizerMonoidHom ⟨c, hc⟩) = 5
  K_normal_J : (K.subgroupOf (K ⊔ A)).Normal
  J_le : K ⊔ A ≤ Subgroup.centralizer ({e} : Set G)
  centralizer_proper : Subgroup.centralizer ({e} : Set G) ≠ ⊤
  J_kGroup : CFSG.IsKGroup ↥(K ⊔ A)
  J_evenRank : evenRank ↥(K ⊔ A) ≤ 3

theorem sectionTenSetup_prime {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) : p.Prime :=
  h.2.2.2.2.2.1.1

theorem sectionTenSetup_three_lt {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) : 3 < p :=
  h.2.2.2.2.2.1.2.1

theorem sectionTenSetup_mem_sigmaA {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) : p ∈ sigmaA G :=
  h.2.2.2.2.2.1.2.2.1

theorem sectionTenSetup_vanishing {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) : AschVanishing G p :=
  h.2.2.2.2.2.1.2.2.2.1

theorem sectionTenSetup_evenRank_eq {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) : evenRank G = 3 :=
  (CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G).trans h.2.2.2.2.1

theorem sectionTenSetup_kProper {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) : KProper InCatalog G :=
  (CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper).mp h.2.2.1

theorem sectionTenSetup_charTwo {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) : IsCharTwoType G :=
  (CFSG.GH74.isCharTwoType_iff.mpr h.2.2.2.1)

theorem sectionTenSetup_sec9Hyp {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    (h : SteinbergBM.SectionTenSetup G p A) : Sec9Hyp G p where
  simple := h.1
  nonabelian := h.2.1
  kProper := sectionTenSetup_kProper h
  charTwo := sectionTenSetup_charTwo h
  evenRank_eq := sectionTenSetup_evenRank_eq h
  prime := sectionTenSetup_prime h
  three_lt := sectionTenSetup_three_lt h
  mem_sigma := sectionTenSetup_mem_sigmaA h

end CFSG.RankThree.PartOne
