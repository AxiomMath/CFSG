module

public import CFSG.Quasithin.H13.NQBlockXTProducer
public import CFSG.Quasithin.H13.NQBlockOriginalTwoCore
public import CFSG.Quasithin.H13.NQBlockOddRankOne
public import CFSG.Quasithin.H13.NQTermShortCcomponent
public import CFSG.Quasithin.SteinbergCDSwappedFactorsCoreSupports
public import CFSG.Quasithin.SteinbergCDPermutableIntersection
public import CFSG.Quasithin.Background.C2Nine
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj coreQuotConj coreQuotConj_mk)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise MatrixGroups commutatorElement

@[expose] def OriginalXTOrbitPlacement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup G, X ≤ (CFSG.solvableRadical L).map L.subtype →
      (X.subgroupOf L).Characteristic → CFSG.pCore 2 X ≠ ⊥ →
      CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X →
      IsPGroup p (X ⧸ CFSG.pCore 2 X) → Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
      CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 →
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      (∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
        (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤) →
      ∀ P : Subgroup G, IsSylowOf p P X →
      ∀ H : Subgroup G, X ⊔ T ≤ H → pCoreOf 2 H ≠ ⊥ → ¬ H ≤ M →
      pCoreOf 2 (H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T) ∧
      (∀ D : Subgroup G, D ≠ ⊥ → D ≤ pCoreOf 2 (X ⊔ T) →
        (D.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic →
        H ⊓ normalizer (D : Set G) ≤ H ⊓ M) ∧
      ∃ K : Subgroup G, K ∈ cComp H ∧ quasithinIsLocal T K ∧ ¬ K ≤ M ∧
        quasithinGenFitting K = pCoreOf 2 K ∧ CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) ∧
        (Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 1 ∨
          Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 3) ∧
        X ≤ normalizer (K : Set G) ∧ ⁅K, X⁆ = K ∧ pCoreOf 2 (X ⊔ T) ≤ normalizer (K : Set G) ∧
        (((K.subgroupOf H).Normal ∧ X ≤ K ∧ CFSG.pRank p (K ⧸ CFSG.pCore 2 K) = 2) ∨
          ∃ t ∈ T, t ∈ normalizer (P : Set G) ∧ CFSG.conjugate K t ≠ K ∧
            (∀ g ∈ H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K t) ∧
            (K.subgroupOf (K ⊔ CFSG.conjugate K t)).Normal ∧
            ((CFSG.conjugate K t).subgroupOf (K ⊔ CFSG.conjugate K t)).Normal ∧
            ((K ⊔ CFSG.conjugate K t).subgroupOf H).Normal ∧ X ≤ K ⊔ CFSG.conjugate K t ∧
            (∀ r : ℕ, r.Prime → r ≠ 2 →
              CFSG.pRank r ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≤ 1) ∧
            Nat.card (P ⊓ K : Subgroup G) = p ∧
            Nat.card (P ⊓ CFSG.conjugate K t : Subgroup G) = p ∧
            (P ⊓ K) ⊔ (P ⊓ CFSG.conjugate K t) = P ∧
            (P ⊓ K) ⊓ (P ⊓ CFSG.conjugate K t) = ⊥ ∧
            CFSG.IsElementaryAbelian p (X ⧸ CFSG.pCore 2 X) ∧
            Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2)

@[expose] def EvenLinearCPUShortBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H R K M : Subgroup G), R ≤ H → IsPGroup 2 R →
    pCoreOf 2 (H ⊓ normalizer (R : Set G)) = R → K ∈ cComp H →
    quasithinGenFitting K = pCoreOf 2 K → CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) →
    R ≤ normalizer (K : Set G) → M ≤ H → ¬ K ≤ M →
    (∀ D : Subgroup G, D ≠ ⊥ → D ≤ R → (D.subgroupOf R).Characteristic →
      H ⊓ normalizer (D : Set G) ≤ M) →
    ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 2 ^ n →
      Nonempty (((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* SL(2, F)) →
      CFSG.QuasithinUnique.IsShort2 (K.subgroupOf H)

section Helpers

variable {G : Type} [Group G]

theorem map_mul_comm_of_mul_comm {A B : Type*} [Group A] [Group B] (f : A →* B)
    {X Y : Subgroup A} (h : (X : Set A) * (Y : Set A) = (Y : Set A) * (X : Set A)) :
    ((X.map f : Subgroup B) : Set B) * ((Y.map f : Subgroup B) : Set B) =
      ((Y.map f : Subgroup B) : Set B) * ((X.map f : Subgroup B) : Set B) := by
  simp only [Subgroup.coe_map]
  rw [← Set.image_mul, h, Set.image_mul]

theorem subgroupOf_mul_comm_of_mul_comm {K X Y : Subgroup G} (hX : X ≤ K) (hY : Y ≤ K)
    (h : (X : Set G) * (Y : Set G) = (Y : Set G) * (X : Set G)) :
    ((X.subgroupOf K : Subgroup K) : Set K) * ((Y.subgroupOf K : Subgroup K) : Set K) =
      ((Y.subgroupOf K : Subgroup K) : Set K) * ((X.subgroupOf K : Subgroup K) : Set K) := by
  apply Set.image_injective.mpr K.subtype_injective
  simp only [Set.image_mul]
  rw [← Subgroup.coe_map, ← Subgroup.coe_map, map_subgroupOf_eq_of_le hX,
    map_subgroupOf_eq_of_le hY]
  exact h

theorem isElementaryAbelian_of_mulEquiv_symm {p : ℕ} {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.IsElementaryAbelian p B) : CFSG.IsElementaryAbelian p A :=
  CFSG.IsElementaryAbelian.of_mulEquiv e.symm h

theorem quotient_injective_of_isPGroup {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K))) {Q : Subgroup K}
    (hQ : IsPGroup p Q) :
    Function.Injective (((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K))).comp Q.subtype) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) y
  rw [← Subgroup.orderOf_coe] at hk
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 K) (y : K) ∈ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.eq_one_iff _).mp hy
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 K) (y : K) = 1 :=
    NQTerm.eq_one_of_orderOf_dvd_prime_pow hp hZ h1 ((orderOf_map_dvd _ _).trans hk.dvd)
  have h3 : (y : K) ∈ CFSG.pCore 2 K := (QuotientGroup.eq_one_iff _).mp h2
  have h4 : ¬ p ∣ Nat.card (CFSG.pCore 2 K) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)).exists_card_eq
    rw [hm]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  exact Subtype.ext (NQTerm.eq_one_of_orderOf_dvd_prime_pow hp h4 h3 hk.dvd)

theorem conjugate_conjugate_eq_of_orbit {H K : Subgroup G} {t : G} (htH : t ∈ H)
    (hKt : CFSG.conjugate K t ≠ K)
    (horb : ∀ g ∈ H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K t) :
    CFSG.conjugate (CFSG.conjugate K t) t = K := by
  rw [CFSG.LocalAnalysis.GorensteinLyons.conjugate_conjugate]
  rcases horb (t * t) (mul_mem htH htH) with h1 | h1
  · exact h1
  · exfalso
    apply hKt
    apply CFSG.LocalAnalysis.GorensteinLyons.conjugate_injective t
    change CFSG.conjugate (CFSG.conjugate K t) t = CFSG.conjugate K t
    rw [CFSG.LocalAnalysis.GorensteinLyons.conjugate_conjugate, h1]

variable [Finite G]

theorem sylow_mul_comm_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime)
    {X : Subgroup G} (hXL : X ≤ L) (hXc : (X.subgroupOf L).Characteristic)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) {P : Subgroup G} (hP : IsSylowOf p P X) :
    T ≤ normalizer (X : Set G) ∧ (CFSG.pCore 2 X).map X.subtype ≤ T ∧
      (CFSG.pCore 2 X).map X.subtype ⊔ P = X ∧
      (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPX, -, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hLN : normalizer (L : Set G) ≤ normalizer (X : Set G) :=
    NQSetup.normalizer_le_normalizer_of_characteristic hXL hXc
  have hTN : T ≤ normalizer (X : Set G) := (h.t_le.trans h.eq_normalizer.le).trans hLN
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, h.sylow.1, h.sylow.2⟩
  obtain ⟨AX, hAXdef⟩ : ∃ AX : Subgroup G, AX = (CFSG.pCore 2 X).map X.subtype := ⟨_, rfl⟩
  have hAX2 : IsPGroup 2 AX := hAXdef ▸ CFSG.pCore_isPGroup.map _
  have hmemA : ∀ x : X, (x : G) ∈ AX ↔ x ∈ CFSG.pCore 2 X := fun x => by
    rw [hAXdef]
    exact mem_map_iff_mem (subtype_injective X)
  have hNAX : normalizer (X : Set G) ≤ normalizer (AX : Set G) := by
    rw [hAXdef]
    exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hNA : ∀ g ∈ normalizer (X : Set G), ∀ a ∈ AX, g * a * g⁻¹ ∈ AX := fun g hg a ha =>
    (mem_normalizer_iff.mp (hNAX hg) a).mp ha
  have hAXT : AX ≤ T := by
    have h1 := hTtop.eq_of_le le_sup_left le_top
      (h.sylow.1.to_sup_of_normal_right' hAX2 (hTN.trans hNAX))
    rw [← h1]
    exact le_sup_right
  have hAXX : AX ≤ X := by
    rw [hAXdef]
    exact map_subtype_le _
  have hπP : (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) = ⊤ := by
    obtain ⟨S₁, hS₁⟩ := hP.exists_sylow_eq_subgroupOf
    have h1 := (S₁.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
      (hXA.to_subgroup ⊤) le_top
    rw [h1, Sylow.coe_mapSurjective, hS₁]
  have hXPA : ∀ x ∈ X, ∃ y ∈ P, y⁻¹ * x ∈ AX := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) ⟨x, hx⟩ ∈
        (P.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := hπP ▸ mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    exact ⟨y, mem_subgroupOf.mp hy, (hmemA _).mpr (QuotientGroup.eq.mp hyx)⟩
  have hsup : AX ⊔ P = X := by
    refine le_antisymm (sup_le hAXX hPX) fun x hx => ?_
    obtain ⟨y, hy, hya⟩ := hXPA x hx
    have hx' : x = y * (y⁻¹ * x) := by group
    rw [hx', sup_comm]
    exact mul_mem_sup hy hya
  have hPT : ∀ y ∈ P, ∀ q ∈ T, ∃ q' ∈ T, ∃ y' ∈ P, y * q = q' * y' := by
    intro y hy q hq
    have hx : q⁻¹ * y * q⁻¹⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (hTN (inv_mem hq)) y).mp (hPX hy)
    rw [inv_inv] at hx
    obtain ⟨y', hy', hya⟩ := hXPA _ hx
    refine ⟨q * (y' * (y'⁻¹ * (q⁻¹ * y * q)) * y'⁻¹),
      mul_mem hq (hAXT (hNA y' (le_normalizer (hPX hy')) _ hya)), y', hy', by group⟩
  have hTP : ∀ q ∈ T, ∀ y ∈ P, ∃ y' ∈ P, ∃ q' ∈ T, q * y = y' * q' := by
    intro q hq y hy
    obtain ⟨y', hy', hya⟩ := hXPA _ ((mem_normalizer_iff.mp (hTN hq) y).mp (hPX hy))
    exact ⟨y', hy', y'⁻¹ * (q * y * q⁻¹) * q, mul_mem (hAXT hya) hq, by group⟩
  refine ⟨hTN, hAXdef ▸ hAXT, hAXdef ▸ hsup, ?_⟩
  ext z
  constructor
  · rintro ⟨y, hy, q, hq, rfl⟩
    obtain ⟨q', hq', y', hy', he⟩ := hPT y hy q hq
    exact ⟨q', hq', y', hy', he.symm⟩
  · rintro ⟨q, hq, y, hy, rfl⟩
    obtain ⟨y', hy', q', hq', he⟩ := hTP q hq y hy
    exact ⟨y', hy', q', hq', he.symm⟩

theorem coreQuot_irreducible_subgroupOf {L X : Subgroup G} (hXL : X ≤ L)
    [(X.subgroupOf L).Normal] {p : ℕ} (hXc2 : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
      V = ⊥ ∨ V = ⊤) :
    ∀ U : Subgroup (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)),
      (∀ l : L, ∀ u ∈ U, coreQuotConj (X.subgroupOf L) l u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  classical
  intro U hU
  let e₁ : X.subgroupOf L ≃* X := subgroupOfEquivOfLe hXL
  let e₂ : X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L) ≃* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.congr (CFSG.pCore 2 (X.subgroupOf L)) (CFSG.pCore 2 X) e₁
      (CFSG.pCore_map_iso 2 e₁)
  have hbij : Function.Bijective (QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))) :=
    (QuotientGroup.mk'_surjective _).bijective_of_nat_card_le (by rw [hXc2, hW])
  let φ : X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L) →*
      (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) :=
    (QuotientGroup.mk' _).comp e₂.toMonoidHom
  have hφinj : Function.Injective φ := hbij.1.comp e₂.injective
  have hcomp : ∀ (l : normalizer (X : Set G)) (hl : (l : G) ∈ L)
      (u : X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)),
      normalizerFrattiniConj X l (φ u) = φ (coreQuotConj (X.subgroupOf L) ⟨l, hl⟩ u) := by
    intro l hl u
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    rw [coreQuotConj_mk]
    rfl
  have hV : ∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ U.map φ,
      normalizerFrattiniConj X l w ∈ U.map φ := by
    rintro l hl _ ⟨u, hu, rfl⟩
    exact ⟨_, hU ⟨l, hl⟩ u hu, (hcomp l hl u).symm⟩
  rcases hirr _ hV with h0 | h1
  · exact Or.inl ((map_eq_bot_iff_of_injective U hφinj).mp h0)
  · refine Or.inr (eq_top_iff.mpr fun u _ => ?_)
    have hu : φ u ∈ U.map φ := h1 ▸ mem_top _
    obtain ⟨u', hu', hu'u⟩ := hu
    rwa [← hφinj hu'u]

theorem terminal_supports_subgroupOf {L X P P₁ P₂ A₁ A₂ : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hXL : X ≤ L) (hP : IsSylowOf p P X) (hP1P : P₁ ≤ P) (hP2P : P₂ ≤ P)
    (hP1c : Nat.card P₁ = p) (hP2c : Nat.card P₂ = p) (hPsup : P₁ ⊔ P₂ = P) (hPinf : P₁ ⊓ P₂ = ⊥)
    (hP12 : ⁅P₁, P₂⁆ = ⊥) (hA1 : A₁ ≤ (CFSG.pCore 2 X).map X.subtype)
    (hA2 : A₂ ≤ (CFSG.pCore 2 X).map X.subtype) (hPA1 : P ≤ normalizer (A₁ : Set G))
    (hPA2 : P ≤ normalizer (A₂ : Set G))
    (hQA : (((CFSG.pCore 2 X).map X.subtype : Subgroup G) : Set G) = (A₁ : Set G) * (A₂ : Set G))
    (hA12 : ⁅A₁, A₂⁆ = ⊥) (hA1P2 : ⁅A₁, P₂⁆ = ⊥) (hA2P1 : ⁅A₂, P₁⁆ = ⊥) (hA1P1 : ⁅A₁, P₁⁆ ≠ ⊥)
    (hA2P2 : ⁅A₂, P₂⁆ ≠ ⊥) :
    ∃ P' P₁' P₂' A₁' A₂' : Subgroup L, IsSylowOf p P' (X.subgroupOf L) ∧
      P₁' ≤ P' ∧ P₂' ≤ P' ∧ Nat.card P₁' = p ∧ Nat.card P₂' = p ∧
      P₁' ⊔ P₂' = P' ∧ P₁' ⊓ P₂' = ⊥ ∧ ⁅P₁', P₂'⁆ = ⊥ ∧
      A₁' ≤ (CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype ∧
      A₂' ≤ (CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype ∧
      P' ≤ normalizer (A₁' : Set L) ∧ P' ≤ normalizer (A₂' : Set L) ∧
      (((CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype : Subgroup L) : Set L) =
        (A₁' : Set L) * (A₂' : Set L) ∧
      ⁅A₁', A₂'⁆ = ⊥ ∧ ⁅A₁', P₂'⁆ = ⊥ ∧ ⁅A₂', P₁'⁆ = ⊥ ∧ ⁅A₁', P₁'⁆ ≠ ⊥ ∧ ⁅A₂', P₂'⁆ ≠ ⊥ := by
  classical
  have hinj := L.subtype_injective
  obtain ⟨hPX, -, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  have hQX : (CFSG.pCore 2 X).map X.subtype ≤ X := map_subtype_le _
  have hPL : P ≤ L := hPX.trans hXL
  have hP1L : P₁ ≤ L := hP1P.trans hPL
  have hP2L : P₂ ≤ L := hP2P.trans hPL
  have hA1L : A₁ ≤ L := (hA1.trans hQX).trans hXL
  have hA2L : A₂ ≤ L := (hA2.trans hQX).trans hXL
  have hQmap : ((CFSG.pCore 2 (X.subgroupOf L)).map (X.subgroupOf L).subtype).map L.subtype =
      (CFSG.pCore 2 X).map X.subtype := by
    have h1 := map_inSubgroup_pCore (X.subgroupOf L) 2
    rw [map_subgroupOf_eq_of_le hXL] at h1
    change (inSubgroup (CFSG.pCore 2) (X.subgroupOf L)).map L.subtype = _
    rw [h1]
    show (CFSG.Open.pCore 2 X).map X.subtype = _
    try with_reducible rfl
  have hm : ∀ {Z : Subgroup G}, Z ≤ L → (Z.subgroupOf L).map L.subtype = Z := fun hZ =>
    map_subgroupOf_eq_of_le hZ
  have hcomm : ∀ {Y Z : Subgroup G}, Y ≤ L → Z ≤ L →
      (⁅Y.subgroupOf L, Z.subgroupOf L⁆ = ⊥ ↔ ⁅Y, Z⁆ = ⊥) := fun hY hZ => by
    rw [← map_eq_bot_iff_of_injective _ hinj, map_commutator, hm hY, hm hZ]
  have hnorm : ∀ {Y Z : Subgroup G}, Y ≤ normalizer (Z : Set G) →
      Y.subgroupOf L ≤ normalizer ((Z.subgroupOf L : Subgroup L) : Set L) := by
    intro Y Z hYZ x hx
    rw [mem_normalizer_iff]
    intro a
    rw [mem_subgroupOf, mem_subgroupOf]
    simpa using mem_normalizer_iff.mp (hYZ (mem_subgroupOf.mp hx)) (a : G)
  refine ⟨P.subgroupOf L, P₁.subgroupOf L, P₂.subgroupOf L, A₁.subgroupOf L, A₂.subgroupOf L,
    ?_, fun x hx => mem_subgroupOf.mpr (hP1P (mem_subgroupOf.mp hx)),
    fun x hx => mem_subgroupOf.mpr (hP2P (mem_subgroupOf.mp hx)),
    (Nat.card_congr (subgroupOfEquivOfLe hP1L).toEquiv).trans hP1c,
    (Nat.card_congr (subgroupOfEquivOfLe hP2L).toEquiv).trans hP2c, ?_, ?_,
    (hcomm hP1L hP2L).mpr hP12, ?_, ?_, hnorm hPA1, hnorm hPA2, ?_, (hcomm hA1L hA2L).mpr hA12,
    (hcomm hA1L hP2L).mpr hA1P2, (hcomm hA2L hP1L).mpr hA2P1,
    fun h0 => hA1P1 ((hcomm hA1L hP1L).mp h0), fun h0 => hA2P2 ((hcomm hA2L hP2L).mp h0)⟩
  · rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L, hm hPL, hm hXL]
    exact hP
  · apply map_injective hinj
    rw [Subgroup.map_sup, hm hP1L, hm hP2L, hm hPL]
    exact hPsup
  · apply map_injective hinj
    rw [Subgroup.map_inf_eq _ _ _ hinj, hm hP1L, hm hP2L, Subgroup.map_bot]
    exact hPinf
  · rw [← map_le_map_iff_of_injective hinj, hm hA1L, hQmap]
    exact hA1
  · rw [← map_le_map_iff_of_injective hinj, hm hA2L, hQmap]
    exact hA2
  · apply Set.image_injective.mpr hinj
    rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map, hQmap,
      hm hA1L, hm hA2L]
    exact hQA

end Helpers

section Pair

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonempty_coreQuot_subgroupOf_equiv {L X : Subgroup G} (hXL : X ≤ L) :
    Nonempty (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L) ≃* X ⧸ CFSG.pCore 2 X) :=
  ⟨QuotientGroup.congr (CFSG.pCore 2 (X.subgroupOf L)) (CFSG.pCore 2 X)
    (subgroupOfEquivOfLe hXL) (CFSG.pCore_map_iso 2 (subgroupOfEquivOfLe hXL))⟩

theorem orbit_pair_short
    (hCPU : CPUOffenderSection) (hE : EvenLinearCPUShortBlock) {T L M : Subgroup G}
    (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    {P : Subgroup G} (hP : IsSylowOf p P X) {H : Subgroup G} (hXTH : X ⊔ T ≤ H)
    (hH2 : pCoreOf 2 H ≠ ⊥)
    (hRXN : pCoreOf 2 (H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T))
    (hND : ∀ D : Subgroup G, D ≠ ⊥ → D ≤ pCoreOf 2 (X ⊔ T) →
      (D.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic → H ⊓ normalizer (D : Set G) ≤ H ⊓ M)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hKM : ¬ K ≤ M)
    (hKF : quasithinGenFitting K = pCoreOf 2 K) (hJq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)))
    (hXNK : X ≤ normalizer (K : Set G)) (hRXK : pCoreOf 2 (X ⊔ T) ≤ normalizer (K : Set G))
    {K₀ : Subgroup G} (hKK₀ : K ≤ K₀) (hKn₀ : (K.subgroupOf K₀).Normal) (hK₀H : K₀ ≤ H)
    (hK₀n : (K₀.subgroupOf H).Normal)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.pRank r ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≤ 1)
    (hPK : Nat.card (P ⊓ K : Subgroup G) = p) :
    CFSG.QuasithinUnique.IsShort2 (K.subgroupOf H) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := h.simple
  have hp2 : p ≠ 2 := by omega
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := le_sup_right.trans hXTH
  obtain ⟨hPX, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hP
  obtain ⟨-, -, -, hPT⟩ := sylow_mul_comm_of_qtnq h hp hXL hXc hXA hP
  have hRXH : pCoreOf 2 (X ⊔ T) ≤ H := (map_subtype_le _).trans hXTH
  have hRX2 : IsPGroup 2 (pCoreOf 2 (X ⊔ T)) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  obtain ⟨W₁, _, _, _, _, L₁, B₁, hL₁q, hL₁irr, hB₁N, hB₁ne, hB₁el, hquad, hineq, ⟨eS⟩⟩ :=
    hCPU G H (pCoreOf 2 (X ⊔ T)) K (H ⊓ M) hRXH hRX2 hRXN hKc hKF hJq hRXK inf_le_left
      (fun hle => hKM (hle.trans inf_le_right)) hND
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, h.sylow.1, h.sylow.2⟩
  have hHK₀ : H ≤ normalizer (K₀ : Set G) := (normal_subgroupOf_iff_le_normalizer hK₀H).mp hK₀n
  have hK₀K : K₀ ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKK₀).mp hKn₀
  have hTK : IsSylowOf 2 (T ⊓ K) K := by
    have h1 := ((hTtop.of_le hTH le_top).inf_of_le_normalizer hK₀H hHK₀).inf_of_le_normalizer
      hKK₀ hK₀K
    rwa [inf_assoc, inf_eq_right.mpr hKK₀] at h1
  let σ : K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
  have hσs : Function.Surjective σ := fun z => by
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (center (K ⧸ CFSG.pCore 2 K)) z
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) j
    exact ⟨k, rfl⟩
  have hPKp : IsPGroup p ((P ⊓ K).subgroupOf K) := (hPp.to_le inf_le_left).comap_subtype
  have hσinj : Function.Injective (σ.comp ((P ⊓ K).subgroupOf K).subtype) :=
    quotient_injective_of_isPGroup hp hp2 hZ hPKp
  have hD₁ : Nat.card (((P ⊓ K).subgroupOf K).map σ) = p := by
    have h1 : ((P ⊓ K).subgroupOf K).map σ = (σ.comp ((P ⊓ K).subgroupOf K).subtype).range := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hσinj).toEquiv]
    exact (Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : P ⊓ K ≤ K)).toEquiv).trans hPK
  obtain ⟨S₁, hS₁⟩ := hTK.exists_sylow_eq_subgroupOf
  have hU' : ((S₁.mapSurjective hσs : Sylow 2 _) : Subgroup _) =
      ((T ⊓ K).subgroupOf K).map σ := by
    rw [Sylow.coe_mapSurjective, hS₁]
  have hcop : Nat.Coprime (Nat.card P) (Nat.card T) := by
    obtain ⟨a, ha⟩ := hPp.exists_card_eq
    obtain ⟨b, hb⟩ := h.sylow.1.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hDT := (SteinbergCD.coprime_permutable_product_normalized_subgroup_intersection hcop hPT
    (hPX.trans hXNK)).2.2
  have hDTS := map_mul_comm_of_mul_comm σ
    (subgroupOf_mul_comm_of_mul_comm inf_le_right inf_le_right hDT)
  have hD : Nat.card ((((P ⊓ K).subgroupOf K).map σ).map eS.symm.toMonoidHom) = p := by
    rw [card_map_of_injective eS.symm.injective]
    exact hD₁
  obtain ⟨T', hT'⟩ : ∃ T' : Sylow 2 (L₁ ⧸ center L₁),
      (T' : Subgroup _) = (((T ⊓ K).subgroupOf K).map σ).map eS.symm.toMonoidHom :=
    ⟨(S₁.mapSurjective hσs).mapSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective,
      (Sylow.coe_mapSurjective _ _).trans (congrArg (Subgroup.map eS.symm.toMonoidHom) hU')⟩
  have hDT' : (((((P ⊓ K).subgroupOf K).map σ).map eS.symm.toMonoidHom : Subgroup _) :
      Set (L₁ ⧸ center L₁)) * (T' : Set (L₁ ⧸ center L₁)) =
      (T' : Set (L₁ ⧸ center L₁)) *
        (((((P ⊓ K).subgroupOf K).map σ).map eS.symm.toMonoidHom : Subgroup _) :
          Set (L₁ ⧸ center L₁)) := by
    have h1 := map_mul_comm_of_mul_comm eS.symm.toMonoidHom hDTS
    rw [← hT'] at h1
    exact h1
  have hHsqtk : CFSG.SectionRank.IsSQTKCat H :=
    ⟨QuasithinUnique.isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank h.qtke.2.2 hH2,
      QuasithinUnique.isKGroupCat_of_kProper h.qtke.1
        (QuasithinUnique.ne_top_of_pCoreOf_ne_bot_of_simple h.nonabelian hH2)⟩
  obtain ⟨-, hSs, hSnab⟩ := id hJq
  obtain ⟨-, hScat⟩ := sqt_catalog_of_surjective hHsqtk (K.subgroupOf H) hSnab
    (σ.comp (subgroupOfEquivOfLe hKH).toMonoidHom) (hσs.comp (subgroupOfEquivOfLe hKH).surjective)
  have hcat' : CFSG.Blueprint.Catalog (L₁ ⧸ center L₁) :=
    CFSG.SectionRank.catalog_of_mulEquiv eS hScat
  have hodd' : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (L₁ ⧸ center L₁) ≤ 1 :=
    fun r hr hr2 => by
      rw [CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv eS r]
      exact hodd r hr hr2
  obtain ⟨-, f, hf3, F, _, _, hF, -, -, -, -, -, -, -, -, θbar, -⟩ :=
    odd_rank_one_catalog_quadratic_offender_forces_even_linear_natural_module L₁ hL₁q hL₁irr
      hcat' hodd' hp hp5 _ hD T' hDT' B₁ hB₁el hB₁ne hB₁N hquad hineq
  exact hE G H (pCoreOf 2 (X ⊔ T)) K (H ⊓ M) hRXH hRX2 hRXN hKc hKF hJq hRXK inf_le_left
    (fun hle => hKM (hle.trans inf_le_right)) hND f hf3 F hF ⟨eS.symm.trans θbar⟩

theorem orbit_pair_impossible
    (hCPU : CPUOffenderSection) (hE : EvenLinearCPUShortBlock) {T L M : Subgroup G}
    (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype) (hXc : (X.subgroupOf L).Characteristic)
    (hX2 : CFSG.pCore 2 X ≠ ⊥) (hXno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirr : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
      V = ⊥ ∨ V = ⊤)
    {P : Subgroup G} (hP : IsSylowOf p P X) {H : Subgroup G} (hXTH : X ⊔ T ≤ H)
    (hH2 : pCoreOf 2 H ≠ ⊥)
    (hRXN : pCoreOf 2 (H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T))
    (hND : ∀ D : Subgroup G, D ≠ ⊥ → D ≤ pCoreOf 2 (X ⊔ T) →
      (D.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic → H ⊓ normalizer (D : Set G) ≤ H ⊓ M)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hKM : ¬ K ≤ M)
    (hKF : quasithinGenFitting K = pCoreOf 2 K) (hJq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    (hZ13 : Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 1 ∨
      Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 3)
    (hXNK : X ≤ normalizer (K : Set G)) (hRXK : pCoreOf 2 (X ⊔ T) ≤ normalizer (K : Set G))
    {t : G} (htT : t ∈ T) (hKt : CFSG.conjugate K t ≠ K)
    (horb : ∀ g ∈ H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K t)
    (hKn₁ : (K.subgroupOf (K ⊔ CFSG.conjugate K t)).Normal)
    (hK₀n : ((K ⊔ CFSG.conjugate K t).subgroupOf H).Normal)
    (hXK₀ : X ≤ K ⊔ CFSG.conjugate K t)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.pRank r ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≤ 1)
    (hPK₁ : Nat.card (P ⊓ K : Subgroup G) = p)
    (hPK₂ : Nat.card (P ⊓ CFSG.conjugate K t : Subgroup G) = p)
    (hPsup : (P ⊓ K) ⊔ (P ⊓ CFSG.conjugate K t) = P)
    (hPinf : (P ⊓ K) ⊓ (P ⊓ CFSG.conjugate K t) = ⊥)
    (hXe : CFSG.IsElementaryAbelian p (X ⧸ CFSG.pCore 2 X))
    (hXc2 : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hXL : X ≤ L := hXR.trans (map_subtype_le _)
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := le_sup_right.trans hXTH
  have htH : t ∈ H := hTH htT
  have hpZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := by
    rcases hZ13 with hZ | hZ <;> rw [hZ] <;> intro hd
    · exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
    · have := Nat.le_of_dvd (by norm_num) hd
      omega
  have hK₂c : CFSG.conjugate K t ∈ cComp H :=
    C2Nine.conjByElt_mem_cComp hKc (le_normalizer (inv_mem htH))
  have hK₂H : CFSG.conjugate K t ≤ H := le_of_mem_cComp hK₂c
  have hShort := orbit_pair_short hCPU hE h hp hp5 hXL hXc hXA hP hXTH hH2 hRXN hND hKc hKM hKF
    hJq hpZ hXNK hRXK le_sup_left hKn₁ (sup_le hKH hK₂H) hK₀n hodd hPK₁
  have hKK₂ : ⁅K, CFSG.conjugate K t⁆ = ⊥ := by
    have hne : K.subgroupOf H ≠ (CFSG.conjugate K t).subgroupOf H := fun he => by
      have h1 := congrArg (Subgroup.map H.subtype) he
      rw [map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hK₂H] at h1
      exact hKt h1.symm
    have h1 := NQTerm.short_Ccomponent_centralizes_every_distinct_Ccomponent
      (mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hKc))
      (mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hK₂c)) hne hShort
    rw [← map_eq_bot_iff_of_injective _ H.subtype_injective, map_commutator,
      map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hK₂H] at h1
    exact h1
  obtain ⟨hTN, -, hXQP, -⟩ := sylow_mul_comm_of_qtnq h hp hXL hXc hXA hP
  have hK₂K : CFSG.conjugate (CFSG.conjugate K t) t = K :=
    conjugate_conjugate_eq_of_orbit htH hKt horb
  have hQ1 : inSubgroup (CFSG.pCore 2) X ≠ ⊥ := fun h0 =>
    hX2 ((map_eq_bot_iff_of_injective _ X.subtype_injective).mp h0)
  obtain ⟨hA1, hA2, hPA1, hPA2, hQA, hA12, hA1P2, hA2P1, hA1P1, hA2P2, -⟩ :=
    SteinbergCD.commuting_swapped_factors_produce_full_core_supports Nat.prime_two hp
      (by omega) hKK₂ hXK₀ hQ1 hXno hP hXQP hPK₁ hPK₂ hPsup (hTN htT) rfl hK₂K
  have hP12 : ⁅P ⊓ K, P ⊓ CFSG.conjugate K t⁆ = ⊥ :=
    eq_bot_iff.mpr ((commutator_mono inf_le_right inf_le_right).trans hKK₂.le)
  have := hXc
  have hLperf : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr h.maximal_local.1.2.1.2.1
  obtain ⟨e₂⟩ := nonempty_coreQuot_subgroupOf_equiv hXL
  have hXe' : CFSG.IsElementaryAbelian p (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) :=
    isElementaryAbelian_of_mulEquiv_symm e₂ hXe
  have hXc' : Nat.card (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) = p ^ 2 :=
    (Nat.card_congr e₂.toEquiv).trans hXc2
  exact (NQTerm.perfect_odd_plane_excludes_terminal_support_models hLperf hp hp5 hXe' hXc'
    (coreQuot_irreducible_subgroupOf hXL hXc2 hW hirr)).1
    (terminal_supports_subgroupOf hXL hP inf_le_left inf_le_left hPK₁ hPK₂ hPsup hPinf hP12
      (hA1.trans inf_le_left) (hA2.trans inf_le_left) hPA1 hPA2 hQA hA12 hA1P2 hA2P1 hA1P1 hA2P2)

end Pair

theorem originalXTPlacement_of
    (hO : OriginalXTOrbitPlacement) (hCPU : CPUOffenderSection) (hE : EvenLinearCPUShortBlock) :
    OriginalXTPlacement := by
  intro G _ _ T L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr H hXTH hH2 hHM
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  obtain ⟨hRXN, hND, K, hKc, hKloc, hKM, hKF, hJq, hZ13, hXNK, hKX, hRXK, halt⟩ :=
    hO G T L M h p hp hp5 X hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr P hP H hXTH hH2 hHM
  rcases halt with ⟨hKn, hXK, hJrk⟩ |
      ⟨t, htT, -, hKt, horb, hKn₁, -, hK₀n, hXK₀, hodd, hPK₁, hPK₂, hPsup, hPinf, hXe, hXc2⟩
  · exact ⟨K, hKc, hKloc, le_of_mem_cComp hKc, hKn, hXK, hKM, hKF, hJq, hZ13, hJrk, hKX, hRXK,
      hRXN, hND⟩
  · exact (orbit_pair_impossible hCPU hE h hp hp5 hXR hXc hX2 hXno hXA hW hirr hP hXTH hH2 hRXN
      hND hKc hKM hKF hJq hZ13 hXNK hRXK htT hKt horb hKn₁ hK₀n hXK₀ hodd hPK₁ hPK₂ hPsup hPinf
      hXe hXc2).elim

theorem original_characteristic_witness_singleton_of_orbit
    (hO : OriginalXTOrbitPlacement) (hCPU : CPUOffenderSection) (hE : EvenLinearCPUShortBlock)
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hSp4 : OriginalWitnessExcludesEvenSymplecticFour)
    {G : Type} [Group G] [Finite G] {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {X : Subgroup G}
    (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype) (hXc : (X.subgroupOf L).Characteristic)
    (hX2 : CFSG.pCore 2 X ≠ ⊥) (hXno : CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient 2 X)
    (hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
      V = ⊥ ∨ V = ⊤) :
    quasithinIsMaxTwoLocal M ∧ X ⊔ T ≤ M ∧
      ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ⊔ T ≤ M' → M' = M :=
  original_characteristic_witness_singleton_of_placement (originalXTPlacement_of hO hCPU hE) hCPU
    hCat hSp4 h hp hp5 hXR hXc hX2 hXno hXA hexp hrk hW hLW hirr

end CFSG.Quasithin.H13.NQBlock
