module

public import CFSG.Quasithin.H13.LocDblMatrix
public import CFSG.Quasithin.H13.NQBlockCcommNilpotent

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup
open scoped commutatorElement

theorem pCore_map_le_of_isSubnormal {G : Type*} [Group G] {p : ℕ} {X : Subgroup G}
    (hX : X.IsSubnormal) : (CFSG.pCore p X).map X.subtype ≤ CFSG.pCore p G := by
  have key : ∀ {X Y : Subgroup G}, X ≤ Y → Y ≤ normalizer (X : Set G) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (map_subtype_le _).trans hXY
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [mem_subgroupOf] at hl ⊢
        have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          (CFSG.pCore p X) (hYN y.2)
        simpa using (mem_normalizer_iff.mp h1 _).mp hl
      · exact ((CFSG.pCore_isPGroup).map X.subtype).of_equiv (subgroupOfEquivOfLe hLY).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pCore p Y).map Y.subtype := map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => ?_⟩, (CFSG.pCore_isPGroup).map _⟩
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore p (⊤ : Subgroup G))
      (show g ∈ normalizer ((⊤ : Subgroup G) : Set G) by
        rw [normalizer_eq_top_iff.mpr inferInstance]
        exact mem_top g)
    exact (mem_normalizer_iff.mp h1 l).mp hl
  | step X Y hXY hY hN ih =>
    exact (key hXY ((normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

theorem sylow_fitting_map_eq_pCore {L : Type*} [Group L] [Finite L] {r : ℕ} [Fact r.Prime]
    (S : Sylow r (CFSG.fittingSubgroup L)) :
    (S : Subgroup (CFSG.fittingSubgroup L)).map (CFSG.fittingSubgroup L).subtype =
      CFSG.pCore r L := by
  have hnil : Group.IsNilpotent (CFSG.fittingSubgroup L) := CFSG.fittingSubgroup_nilpotent
  have hall : ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p (CFSG.fittingSubgroup L)),
      (P : Subgroup (CFSG.fittingSubgroup L)).Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := CFSG.fittingSubgroup L)).out 1 4).mp hnil
  have hSn : (S : Subgroup (CFSG.fittingSubgroup L)).Normal := hall r inferInstance S
  have hSc := Sylow.characteristic_of_normal S hSn
  apply le_antisymm
  · apply le_sSup
    refine ⟨⟨fun x hx g => ?_⟩, S.isPGroup'.map _⟩
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (S : Subgroup (CFSG.fittingSubgroup L))
      (show g ∈ normalizer ((CFSG.fittingSubgroup L : Subgroup L) : Set L) by
        rw [normalizer_eq_top_iff.mpr inferInstance]
        exact mem_top g)
    exact (mem_normalizer_iff.mp h1 x).mp hx
  · have hle : CFSG.pCore r L ≤ CFSG.fittingSubgroup L := CFSG.pCore_le_fitting L r
    have hp : IsPGroup r ((CFSG.pCore r L).subgroupOf (CFSG.fittingSubgroup L)) :=
      CFSG.pCore_isPGroup.of_equiv (subgroupOfEquivOfLe hle).symm
    obtain ⟨S', hS'⟩ := hp.exists_le_sylow
    have hSS' : S' = S := by
      have := Sylow.unique_of_normal S hSn
      exact Subsingleton.elim _ _
    rw [hSS'] at hS'
    intro x hx
    exact ⟨⟨x, hle hx⟩, hS' (mem_subgroupOf.mpr hx), rfl⟩

theorem odd_Fitting_cores {G : Type*} [Group G] [Finite G] (hSQT : CFSG.IsStronglyQuasithin G)
    (hO2 : CFSG.pCore 2 G = ⊥) {L : Subgroup G} (hL : CFSG.IsCComponent L)
    (hq : ¬ CFSG.IsQuasisimple L) :
    CFSG.generalizedFitting L = CFSG.fittingSubgroup L ∧ CFSG.fittingSubgroup L ≠ ⊥ ∧
      Group.IsNilpotent (CFSG.fittingSubgroup L) ∧ Odd (Nat.card (CFSG.fittingSubgroup L)) ∧
      ⁅(⊤ : Subgroup L), CFSG.fittingSubgroup L⁆ ≠ ⊥ ∧
      (Nat.card (CFSG.fittingSubgroup L)).primeFactors.Nonempty ∧
      (∃ e : ((r : (Nat.card (CFSG.fittingSubgroup L)).primeFactors) →
          CFSG.pCore (r : ℕ) L) ≃* CFSG.fittingSubgroup L,
        ∀ (r : (Nat.card (CFSG.fittingSubgroup L)).primeFactors)
          (x : (q : (Nat.card (CFSG.fittingSubgroup L)).primeFactors) → CFSG.pCore (q : ℕ) L),
          (∀ q, q ≠ r → x q = 1) → ((e x : L) = x r)) ∧
      ∀ r ∈ (Nat.card (CFSG.fittingSubgroup L)).primeFactors,
        CFSG.pCore r L ≠ ⊥ ∧ (CFSG.pCore r L).Characteristic ∧
        (∀ S : Sylow r (CFSG.fittingSubgroup L),
          (S : Subgroup (CFSG.fittingSubgroup L)).map (CFSG.fittingSubgroup L).subtype =
            CFSG.pCore r L) ∧
        CFSG.pRank r (CFSG.pCore r L) ≤ 2 := by
  classical
  have hLc : L ∈ CFSG.Quasithin.cComp (⊤ : Subgroup G) :=
    CFSG.Quasithin.mem_cComp_top_iff_isCComponent.mpr hL
  obtain ⟨-, hFstar, hFne, hnil, hcomm⟩ :=
    CFSG.Quasithin.H13.LocDbl.Ccomm_structure_nonquasisimple_Fitting hLc hq
  set F := CFSG.fittingSubgroup L with hFdef
  have hO2L : CFSG.pCore 2 L = ⊥ := by
    have h1 := pCore_map_le_of_isSubnormal (p := 2) hL.2.2.1
    rwa [hO2, le_bot_iff, map_eq_bot_iff_of_injective _ L.subtype_injective] at h1
  have hodd : Odd (Nat.card F) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 F) := inferInstance
    have h1 := sylow_fitting_map_eq_pCore S
    rw [hO2L, map_eq_bot_iff_of_injective _ F.subtype_injective] at h1
    have h2 := S.card_eq_multiplicity
    rw [h1, card_bot] at h2
    have h3 : (Nat.card F).factorization 2 = 0 := by
      by_contra hk
      have := Nat.one_lt_two_pow hk
      omega
    rw [Nat.factorization_eq_zero_iff] at h3
    rcases h3 with h3 | h3 | h3
    · exact absurd Nat.prime_two h3
    · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)
    · exact absurd h3 Nat.card_pos.ne'
  have hFcard : 1 < Nat.card F := (one_lt_card_iff_ne_bot F).mpr hFne
  let H : (Nat.card F).primeFactors → Subgroup L := fun p => CFSG.pCore (p : ℕ) L
  have hcommP : Pairwise fun p q => ∀ x y : L, x ∈ H p → y ∈ H q → Commute x y := by
    intro p q hpq x y hx hy
    have hne : (p : ℕ) ≠ q := fun h => hpq (Subtype.ext h)
    have hc := (CFSG.LocalCores.distinct_prime_cores_commute (G := L)
      (Nat.prime_of_mem_primeFactors p.2) (Nat.prime_of_mem_primeFactors q.2) hne).2
    have hmem : ⁅x, y⁆ ∈ ⁅CFSG.pCore (p : ℕ) L, CFSG.pCore (q : ℕ) L⁆ :=
      commutator_mem_commutator hx hy
    rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have : ∀ p, Fintype (H p) := fun p => Fintype.ofFinite _
  have hcop : Pairwise fun p q => Nat.Coprime (Fintype.card (H p)) (Fintype.card (H q)) := by
    intro p q hpq
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    exact IsPGroup.coprime_card_of_ne _ _ (fun h => hpq (Subtype.ext h)) _ _ CFSG.pCore_isPGroup
      CFSG.pCore_isPGroup
  have hind : iSupIndep H := Subgroup.independent_of_coprime_order hcommP hcop
  let ϕ := Subgroup.noncommPiCoprod hcommP
  have hrange : ϕ.range = F := by
    rw [Subgroup.noncommPiCoprod_range]
    apply le_antisymm
    · refine iSup_le fun p => ?_
      have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
      exact CFSG.pCore_le_fitting L p
    · intro x hx
      have hK : (⨆ p, H p).subgroupOf F = ⊤ := eq_top_of_forall_sylow_le _ fun r _ S => by
        by_cases hr : r ∣ Nat.card F
        · intro y hy
          rw [mem_subgroupOf]
          have hyr : (y : L) ∈ CFSG.pCore r L := by
            rw [← sylow_fitting_map_eq_pCore S]
            exact ⟨y, hy, rfl⟩
          have hrmem : r ∈ (Nat.card F).primeFactors :=
            Nat.mem_primeFactors.mpr ⟨Fact.out, hr, Nat.card_pos.ne'⟩
          exact le_iSup H ⟨r, hrmem⟩ hyr
        · have h1 : (S : Subgroup F) = ⊥ := by
            rw [← card_eq_one, S.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hr,
              pow_zero]
          rw [h1]
          exact bot_le
      have h1 : (⟨x, hx⟩ : F) ∈ (⨆ p, H p).subgroupOf F := by
        rw [hK]
        exact mem_top _
      exact h1
  have hmemF : ∀ x, ϕ x ∈ F := fun x => hrange.le ⟨x, rfl⟩
  let ϕ' := ϕ.codRestrict F hmemF
  have hinj : Function.Injective ϕ' := fun x y h =>
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hind (congrArg Subtype.val h)
  have hsurj : Function.Surjective ϕ' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hrange.ge hy
    exact ⟨x, rfl⟩
  refine ⟨hFstar, hFne, hnil, hodd, hcomm, Nat.nonempty_primeFactors.mpr hFcard,
    ⟨MulEquiv.ofBijective ϕ' ⟨hinj, hsurj⟩, fun p x hx => ?_⟩, fun r hr => ?_⟩
  · have hx' : x = Pi.mulSingle p (x p) := by
      funext q
      by_cases hq : q = p
      · subst hq
        simp
      · rw [hx q hq, Pi.mulSingle_eq_of_ne hq]
    change ϕ x = x p
    rw [hx']
    simp only [ϕ, Subgroup.noncommPiCoprod_mulSingle, Pi.mulSingle_eq_same]
  · have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have : Fact r.Prime := ⟨hrp⟩
    have hrF : r ∣ Nat.card F := Nat.dvd_of_mem_primeFactors hr
    have hsylr : ∀ S : Sylow r F, (S : Subgroup F).map F.subtype = CFSG.pCore r L :=
      fun S => sylow_fitting_map_eq_pCore S
    have hne : CFSG.pCore r L ≠ ⊥ := by
      obtain ⟨S⟩ : Nonempty (Sylow r F) := inferInstance
      rw [← hsylr S]
      intro h
      rw [map_eq_bot_iff_of_injective _ F.subtype_injective] at h
      have h2 := S.card_eq_multiplicity
      rw [h, card_bot] at h2
      have h3 := hrp.factorization_pos_of_dvd Nat.card_pos.ne' hrF
      have h4 : 1 < r ^ (Nat.card F).factorization r := Nat.one_lt_pow h3.ne' hrp.one_lt
      omega
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact hne hO2L
    refine ⟨hne, inferInstance, hsylr, ?_⟩
    have h1 : CFSG.pRank r (CFSG.pCore r L) ≤ CFSG.pRank r G := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.pRank_top_le_of_injective hrp.one_lt
        (L.subtype.comp (CFSG.pCore r L).subtype)
        (L.subtype_injective.comp (CFSG.pCore r L).subtype_injective)
    exact h1.trans (hSQT r hrp hr2)

end CFSG.Quasithin.H13.NQBlock
