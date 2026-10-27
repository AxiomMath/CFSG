module

public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux
public import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Basic
public import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.RankThree.PartTwo.Sec16.CTrick
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Open.GilmanSolomonDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private theorem isSylowOf_inf_oTwoPrimeTwo {T S : Subgroup G} (hST : S ≤ T)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex T) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ oTwoPrimeTwo T) (oTwoPrimeTwo T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
    (CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hST, hS2, hSidx⟩)
    (Lemma85Aux.oTwoPrimeTwo_le T) (Lemma85Aux.le_normalizer_oTwoPrimeTwo (X := T))

private theorem oTwoPrimeTwo_eq_sup_inf {T S : Subgroup G} (hST : S ≤ T)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex T) :
    oTwoPrimeTwo T = pPrimeCoreOf 2 T ⊔ (S ⊓ oTwoPrimeTwo T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylR : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ oTwoPrimeTwo T) (oTwoPrimeTwo T) :=
    isSylowOf_inf_oTwoPrimeTwo hST hS2 hSidx
  have hmax : ∀ Q : Subgroup G, S ⊓ oTwoPrimeTwo T ≤ Q → Q ≤ oTwoPrimeTwo T →
      IsPGroup 2 Q → Q = S ⊓ oTwoPrimeTwo T := fun Q h1 h2 h3 => hSylR.eq_of_le h1 h2 h3
  have h := Lemma85Aux.oTwoPrimeTwo_eq_sup (X := T) (Q := S ⊓ oTwoPrimeTwo T) inf_le_right
    hS2.to_inf_left hmax
  rwa [show CFSG.Open.GLAPPrimeCoreOf 2 T = pPrimeCoreOf 2 T from rfl] at h

private theorem pCore_quotient_eq_map {T S : Subgroup G} (hST : S ≤ T)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex T) :
    CFSG.pCore 2 (↥T ⧸ CFSG.Open.GLAPPrimeCore 2 ↥T) =
      ((S ⊓ oTwoPrimeTwo T).subgroupOf T).map
        (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUR : oTwoPrimeTwo T = pPrimeCoreOf 2 T ⊔ (S ⊓ oTwoPrimeTwo T) :=
    oTwoPrimeTwo_eq_sup_inf hST hS2 hSidx
  have hmap : ((oTwoPrimeTwo T).subgroupOf T).map
        (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) =
      CFSG.pCore 2 (↥T ⧸ CFSG.Open.GLAPPrimeCore 2 ↥T) := by
    show Subgroup.map _ (Subgroup.comap T.subtype (oTwoPrimeTwo T)) = _
    unfold oTwoPrimeTwo
    rw [Subgroup.comap_map_eq_self_of_injective T.subtype_injective]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.Open.GLAPPrimeCore 2 ↥T)) _
  have hOsub : (pPrimeCoreOf 2 T).subgroupOf T = CFSG.Open.GLAPPrimeCore 2 ↥T :=
    Subgroup.comap_map_eq_self_of_injective T.subtype_injective _
  have hsup : (oTwoPrimeTwo T).subgroupOf T =
      (pPrimeCoreOf 2 T).subgroupOf T ⊔ (S ⊓ oTwoPrimeTwo T).subgroupOf T := by
    nth_rewrite 1 [hUR]
    exact Subgroup.subgroupOf_sup (pPrimeCoreOf_le 2 T) (inf_le_left.trans hST)
  have hker : (CFSG.Open.GLAPPrimeCore 2 ↥T).map
      (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  calc CFSG.pCore 2 (↥T ⧸ CFSG.Open.GLAPPrimeCore 2 ↥T)
      = ((oTwoPrimeTwo T).subgroupOf T).map
          (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) := hmap.symm
    _ = ((pPrimeCoreOf 2 T).subgroupOf T ⊔ (S ⊓ oTwoPrimeTwo T).subgroupOf T).map
          (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) := by rw [hsup]
    _ = ((pPrimeCoreOf 2 T).subgroupOf T).map
          (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) ⊔
        ((S ⊓ oTwoPrimeTwo T).subgroupOf T).map
          (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) := by
        rw [Subgroup.map_sup]
    _ = ⊥ ⊔ ((S ⊓ oTwoPrimeTwo T).subgroupOf T).map
          (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) := by rw [hOsub, hker]
    _ = ((S ⊓ oTwoPrimeTwo T).subgroupOf T).map
          (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)) := bot_sup_eq _

private theorem omegaOneZ_le_oTwoPrimeTwo {T S : Subgroup G} (hST : S ≤ T)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex T)
    (hsol : Group.IsSolvable ↥T) :
    omegaOneZ S ≤ oTwoPrimeTwo T := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥T →* (↥T ⧸ CFSG.Open.GLAPPrimeCore 2 ↥T) :=
    QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore 2 ↥T)
  haveI : Group.IsSolvable (↥T ⧸ CFSG.Open.GLAPPrimeCore 2 ↥T) := inferInstance
  have hcent := CFSG.centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot
    (G := ↥T ⧸ CFSG.Open.GLAPPrimeCore 2 ↥T) inferInstance
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_two)
  have hpc := pCore_quotient_eq_map (T := T) (S := S) hST hS2 hSidx
  intro x hx
  have hxS : x ∈ S := Sec7.omegaOneZ_le S hx
  have hxT : x ∈ T := hST hxS
  have hxc : x ∈ Subgroup.centralizer (S : Set G) :=
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1.omegaOneZ_le_centralizer S hx
  have hmem : π ⟨x, hxT⟩ ∈
      Subgroup.centralizer (CFSG.pCore 2 (↥T ⧸ CFSG.Open.GLAPPrimeCore 2 ↥T) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hpc] at hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    have huS : (u : G) ∈ S := (Subgroup.mem_subgroupOf.mp hu).1
    have hux : (u : G) * x = x * (u : G) :=
      Subgroup.mem_centralizer_iff.mp hxc (u : G) huS
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hux)
  exact (Lemma85Aux.mem_oTwoPrimeTwo (X := T)).mpr ⟨⟨x, hxT⟩, rfl, hcent hmem⟩

private theorem le_normalizer_inf_oTwoPrimeTwo {T S : Subgroup G} (hTQ : T ∈ scriptQ A (lB A))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    A ≤ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) := by
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hTQ.1.2.2
  have hAU : A ≤ Subgroup.normalizer (oTwoPrimeTwo T : Set G) :=
    Lemma85Aux.normalizer_le_oTwoPrimeTwo (X := T) (M := A) hAT
  exact (le_inf hAS hAU).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem le_normalizer_inf_normalizer {T S : Subgroup G}
    (hTQ : T ∈ scriptQ A (lB A)) (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    A ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G)) : Set G) := by
  have hASR : A ≤ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) :=
    le_normalizer_inf_oTwoPrimeTwo (T := T) (S := S) hTQ hAS
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hTQ.1.2.2
  have hANN : A ≤ Subgroup.normalizer
      (Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) : Set G) := by
    intro a ha
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hai : a⁻¹ ∈ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) :=
      (Subgroup.normalizer _).inv_mem (hASR ha)
    have hya : a⁻¹ * y * a ∈ S ⊓ oTwoPrimeTwo T := by
      have h := (Subgroup.mem_normalizer_iff (H := S ⊓ oTwoPrimeTwo T) (g := a⁻¹)).mp
        hai y
      simpa using h.mp hy
    have hx' : x * (a⁻¹ * y * a) * x⁻¹ ∈ S ⊓ oTwoPrimeTwo T := by
      have h := (Subgroup.mem_normalizer_iff (H := S ⊓ oTwoPrimeTwo T) (g := x)).mp
        hx (a⁻¹ * y * a)
      exact h.mp hya
    have heq : a * x * a⁻¹ * y * (a * x * a⁻¹)⁻¹ =
        a * (x * (a⁻¹ * y * a) * x⁻¹) * a⁻¹ := by group
    rw [heq]
    have h := (Subgroup.mem_normalizer_iff (H := S ⊓ oTwoPrimeTwo T) (g := a)).mp
      (hASR ha) (x * (a⁻¹ * y * a) * x⁻¹)
    exact h.mp hx'
  exact (le_inf hAT hANN).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem le_sup_inf_normalizer {T S : Subgroup G} (hST : S ≤ T)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex T) :
    T ≤ oTwoPrimeTwo T ⊔
      (T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylST : CFSG.ABGLocalTools.IsSylowOf 2 S T :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hST, hS2, hSidx⟩
  have hSylUT : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ oTwoPrimeTwo T) (oTwoPrimeTwo T) :=
    isSylowOf_inf_oTwoPrimeTwo hST hS2 hSidx
  have hmax : ∀ Q : Subgroup G, S ⊓ oTwoPrimeTwo T ≤ Q → Q ≤ oTwoPrimeTwo T →
      IsPGroup 2 Q → Q = S ⊓ oTwoPrimeTwo T := fun Q h1 h2 h3 => hSylUT.eq_of_le h1 h2 h3
  intro t ht
  have htN : t ∈ Subgroup.normalizer (oTwoPrimeTwo T : Set G) :=
    Lemma85Aux.le_normalizer_oTwoPrimeTwo ht
  obtain ⟨g, hgU, hgk⟩ :=
    Lemma85Aux.exists_mem_mul_normalizer_of_sylow inf_le_right hS2.to_inf_left hmax htN
  have hgk' : g⁻¹ * t ∈
      T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) :=
    ⟨T.mul_mem (T.inv_mem ((Lemma85Aux.oTwoPrimeTwo_le T) hgU)) ht, hgk⟩
  have ht' : t = g * (g⁻¹ * t) := by group
  rw [ht']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgU) (Subgroup.mem_sup_right hgk')

private theorem le_M_of_mem_scriptQ_two (h : Sec17Std G A c L Y₀) {T S : Subgroup G}
    (hTQ : T ∈ scriptQ A (lB A)) (hST : S ≤ T) (hS2 : IsPGroup 2 S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ Subgroup.normalizer (Y₀ : Set G) :=
  CFSG.RankThree.PartTwo.Sec17.HeadProof.le_M_of_mem_scriptQPi_two h
    ⟨⟨mem_scriptQ_of_le hTQ hST hAS, le_top⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩

private theorem le_M_of_commutator_le (h : Sec17Std G A c L Y₀) {P : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp3 : p ≠ 3) (hPp : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hcomm : ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.normalizer (Y₀ : Set G)) :
    P ≤ Subgroup.normalizer (Y₀ : Set G) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA : c ∈ A :=
    (CFSG.RankThree.PartTwo.Sec13.zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).1
  have hR3 : IsPGroup 3 (Subgroup.zpowers c) := by
    have hcard : Nat.card (Subgroup.zpowers c) = 3 :=
      (CFSG.RankThree.PartTwo.Sec13.zpowers_mem_omegaA_iff.mp h.zpowers_mem_omegaA).2.1
    exact IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hRX : Subgroup.zpowers c ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr (hAP hcA)
  let N : Subgroup G := ⁅P, Subgroup.zpowers c⁆
  have hNX : N ≤ P := (Subgroup.le_normalizer_iff_commutator_le_left).mp hRX
  have hRN : Subgroup.zpowers c ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hN3 : ¬ 3 ∣ Nat.card N := by
    intro h3
    have h3P : 3 ∣ Nat.card P := h3.trans (Subgroup.card_dvd_of_le hNX)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    rw [hn] at h3P
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3P)).symm
  have hdec := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le (p := 3)
    (X := P) (N := N) (R := Subgroup.zpowers c) hNX hRX hRN hR3 hN3 le_rfl
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hdec
  rw [← hdec]
  exact sup_le
    (inf_le_right.trans (CFSG.RankThree.PartTwo.Sec16.CTrick.centralizer_le_normalizer_y0 h))
    hcomm

private theorem exists_invariant_sylow_inf (h : Sec17Std G A c L Y₀) {T₁ : Subgroup G}
    (hT₁3 : ¬ 3 ∣ Nat.card T₁) (hAT₁ : A ≤ Subgroup.normalizer (T₁ : Set G)) :
    ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2), ∃ P : Subgroup G,
      CFSG.Open.fusionIsSylowIn p P T₁ ∧ ⊥ ≤ P ∧
        A ≤ Subgroup.normalizer (P : Set G) := by
  intro p hp hp2
  exact CFSG.Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three hp
    h.isE27.isPGroup hT₁3 hAT₁ bot_le (IsPGroup.of_bot (p := p) (G := G))
    (by
      intro a _
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hx1 : x = 1 := Subgroup.mem_bot.mp hx
      refine Subgroup.mem_bot.mpr ?_
      rw [hx1]
      group)

private theorem eq_bot_of_fusionIsSylowIn_three {T₁ P : Subgroup G} {p : ℕ} (hp3 : p = 3)
    (hT₁3 : ¬ 3 ∣ Nat.card T₁) (hP : CFSG.Open.fusionIsSylowIn p P T₁) : P = ⊥ := by
  subst hp3
  refine Subgroup.eq_bot_of_card_eq _ ?_
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP.2.1
  have hdvd : Nat.card P ∣ Nat.card T₁ := Subgroup.card_dvd_of_le hP.1
  have hcop : Nat.Coprime (3 ^ n) (Nat.card T₁) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT₁3).pow_left n
  exact Nat.eq_one_of_dvd_coprimes hcop (by rw [hn]) hdvd

private theorem le_sup_iSup_sylow {T T₁ S : Subgroup G}
    {Pp : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3} → Subgroup G}
    (hST : S ≤ T) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex T)
    (hST₁ : S ≤ T₁) (hT₁T : T₁ ≤ T) (hT₁3 : ¬ 3 ∣ Nat.card T₁)
    (hPp : ∀ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3}, CFSG.Open.fusionIsSylowIn q.1 (Pp q) T₁)
    (hq : ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3),
      ∃ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3}, q.1 = p)
    (hex : ∀ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2), ∃ P : Subgroup G,
      CFSG.Open.fusionIsSylowIn p P T₁ ∧ ⊥ ≤ P ∧ A ≤ Subgroup.normalizer (P : Set G)) :
    T₁ ≤ S ⊔ ⨆ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3}, Pp q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSylST : CFSG.ABGLocalTools.IsSylowOf 2 S T :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hST, hS2, hSidx⟩
  have htop : (S ⊔ ⨆ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3}, Pp q).subgroupOf T₁ =
      ⊤ := by
    apply CFSG.GroupTheory.WielandtProduct.eq_top_of_forall_sylow_le
    intro p hp
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨Q, hQ⟩ := (hSylST.of_le hST₁ hT₁T).exists_sylow_eq_subgroupOf
      exact ⟨Q, hQ ▸ Subgroup.subgroupOf_mono _ le_sup_left⟩
    · by_cases hp3 : p = 3
      · obtain ⟨P, hSylP, -, -⟩ := hex p hp hp2
        obtain ⟨-, Q, hQ⟩ := CFSG.Open.fusionIsSylowIn_iff.mp hSylP
        refine ⟨Q, ?_⟩
        rw [hQ, eq_bot_of_fusionIsSylowIn_three hp3 hT₁3 hSylP,
          Subgroup.bot_subgroupOf]
        exact bot_le
      · obtain ⟨q, hq'⟩ := hq p hp hp2 hp3
        have hSyl : CFSG.Open.fusionIsSylowIn p (Pp q) T₁ := hq' ▸ hPp q
        obtain ⟨-, Q, hQ⟩ := CFSG.Open.fusionIsSylowIn_iff.mp hSyl
        refine ⟨Q, ?_⟩
        rw [hQ]
        exact Subgroup.subgroupOf_mono _ ((le_iSup Pp q).trans le_sup_right)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥T₁) ∈
      (S ⊔ ⨆ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3}, Pp q).subgroupOf T₁ := by
    rw [htop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hx'

private theorem sup_iSup_le_M (h : Sec17Std G A c L Y₀) {T T₁ S : Subgroup G}
    {Pp : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3} → Subgroup G}
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hT₁T : T₁ ≤ T)
    (hT₁N : T₁ ≤ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G))
    (hPp : ∀ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3}, CFSG.Open.fusionIsSylowIn q.1 (Pp q) T₁ ∧
        A ≤ Subgroup.normalizer (Pp q : Set G))
    (hK : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ P : Subgroup G, P ≤ T → IsPGroup p P →
      A ≤ Subgroup.normalizer (P : Set G) →
      P ≤ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) →
      ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.normalizer (Y₀ : Set G)) :
    S ⊔ ⨆ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3}, Pp q ≤
      Subgroup.normalizer (Y₀ : Set G) := by
  refine sup_le hSM (iSup_le fun q => ?_)
  obtain ⟨hSyl, hAP⟩ := hPp q
  exact le_M_of_commutator_le h q.2.1 q.2.2.2 hSyl.2.1 hAP
    (hK q.1 q.2.1 q.2.2.1 q.2.2.2 (Pp q) (hSyl.1.trans hT₁T) hSyl.2.1 hAP
      (hSyl.1.trans hT₁N))

private theorem le_M_inf_normalizer (h : Sec17Std G A c L Y₀) {T S : Subgroup G}
    (hTQ : T ∈ scriptQ A (lB A)) (hST : S ≤ T) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex T) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hAT₁ : A ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G)) : Set G))
    (hK : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ P : Subgroup G, P ≤ T → IsPGroup p P →
      A ≤ Subgroup.normalizer (P : Set G) →
      P ≤ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) →
      ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.normalizer (Y₀ : Set G)) :
    T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) ≤
      Subgroup.normalizer (Y₀ : Set G) := by
  have hSM : S ≤ Subgroup.normalizer (Y₀ : Set G) :=
    le_M_of_mem_scriptQ_two h hTQ hST hS2 hAS
  have hT₁T : T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) ≤ T := inf_le_left
  have hT₁N : T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) ≤
      Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) := inf_le_right
  have hSR : S ≤ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) :=
    (le_inf Subgroup.le_normalizer
      (hST.trans (Lemma85Aux.le_normalizer_oTwoPrimeTwo (X := T)))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hT3 : ¬ 3 ∣ Nat.card T := (isPiSubgroup_piCompl_iff Nat.prime_three T).mp hTQ.1.2.1
  have hT₁3 : ¬ 3 ∣ Nat.card
      ((T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G)) : Subgroup G) :=
    fun hd => hT3 (hd.trans (Subgroup.card_dvd_of_le hT₁T))
  let Pp : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3} → Subgroup G := fun q =>
    Classical.choose (exists_invariant_sylow_inf h hT₁3 hAT₁ q.1 q.2.1 q.2.2.1)
  have hPp : ∀ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3},
      CFSG.Open.fusionIsSylowIn q.1 (Pp q)
        (T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G)) ∧
      A ≤ Subgroup.normalizer (Pp q : Set G) := by
    intro q
    obtain ⟨hSyl, -, hAP⟩ := Classical.choose_spec
      (exists_invariant_sylow_inf h hT₁3 hAT₁ q.1 q.2.1 q.2.2.1)
    exact ⟨hSyl, hAP⟩
  have hgen : T ⊓ Subgroup.normalizer ((S ⊓ oTwoPrimeTwo T) : Set G) ≤
      S ⊔ ⨆ q : {p : ℕ // p.Prime ∧ p ≠ 2 ∧ p ≠ 3}, Pp q :=
    le_sup_iSup_sylow hST hS2 hSidx (le_inf hST hSR) hT₁T hT₁3 (fun q => (hPp q).1)
      (fun p hp hp2 hp3 => ⟨⟨p, hp, hp2, hp3⟩, rfl⟩)
      (exists_invariant_sylow_inf h hT₁3 hAT₁)
  exact hgen.trans (sup_iSup_le_M h hSM hT₁T hT₁N hPp hK)

theorem exists_le_M_of_commutator_le (h : Sec17Std G A c L Y₀) {T S : Subgroup G}
    (hTQ : T ∈ scriptQ A (lB A)) (hsol : Group.IsSolvable ↥T) (hST : S ≤ T)
    (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex T)
    (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hO : pPrimeCoreOf 2 T ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ∃ R₂ : Subgroup G, R₂ ≤ S ∧
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.omegaOneZ S ≤ R₂ ∧
      A ≤ Subgroup.normalizer (R₂ : Set G) ∧
      ((∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → ∀ P : Subgroup G, P ≤ T → IsPGroup p P →
          A ≤ Subgroup.normalizer (P : Set G) → P ≤ Subgroup.normalizer (R₂ : Set G) →
          ⁅P, Subgroup.zpowers c⁆ ≤ Subgroup.normalizer (Y₀ : Set G)) →
        T ≤ Subgroup.normalizer (Y₀ : Set G)) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨S ⊓ oTwoPrimeTwo T, inf_le_left, ?_, ?_, ?_⟩
  · exact le_inf (Sec7.omegaOneZ_le S) (omegaOneZ_le_oTwoPrimeTwo hST hS2 hSidx hsol)
  · exact le_normalizer_inf_oTwoPrimeTwo (T := T) (S := S) hTQ hAS
  · intro hK
    have hAT₁ := le_normalizer_inf_normalizer (T := T) (S := S) hTQ hAS
    have hT₁M := le_M_inf_normalizer h hTQ hST hS2 hSidx hAS hAT₁ hK
    have hFR := le_sup_inf_normalizer hST hS2 hSidx
    have hSM := le_M_of_mem_scriptQ_two h hTQ hST hS2 hAS
    have hUM : oTwoPrimeTwo T ≤ Subgroup.normalizer (Y₀ : Set G) := by
      rw [oTwoPrimeTwo_eq_sup_inf hST hS2 hSidx]
      exact sup_le hO (inf_le_left.trans hSM)
    exact hFR.trans (sup_le hUM hT₁M)

end CFSG.RankThree.PartTwo.Sec16.Ctr166
