module

public import CFSG.RankThree.PartTwo.Sec15.Item152StepsConf
import CFSG.CharacterTheory.Burnside
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem layer_eq_bot_of_isSolvable_152 {H : Type*} [Group H] (hH : Group.IsSolvable H) :
    layer H = ⊥ :=
  CFSG.WholeGroup.layer_eq_bot_of_isSolvable

omit [Finite G] in
theorem card_sup_dvd_of_coe_sup_eq_mul {P S : Subgroup G}
    (hPS : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G)) :
    Nat.card ↥(P ⊔ S) ∣ Nat.card P * Nat.card S := by
  have hidx := card_quotient_dvd_of_coe_sup_eq_mul hPS
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (S.subgroupOf (P ⊔ S)),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ P ⊔ S)).toEquiv]
  exact mul_dvd_mul_right hidx _

theorem generalizedFitting_eq_pCore_of_faithful {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P S : Subgroup G} (hP : IsPGroup p P) (hS : IsPGroup 2 S)
    (hPS : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G))
    (hF : P ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (P ⊔ S) : Set G) = ⊥) :
    generalizedFitting ↥(P ⊔ S) = CFSG.pCore 2 ↥(P ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  set H := P ⊔ S with hH
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  obtain ⟨b, hb⟩ := hS.exists_card_eq
  have hcard : Nat.card H ∣ p ^ a * 2 ^ b := ha ▸ hb ▸ card_sup_dvd_of_coe_sup_eq_mul hPS
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.mp hcard
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hy
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hz
  have hsolv : Group.IsSolvable H := by
    have : Fintype H := Fintype.ofFinite H
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp
      Nat.prime_two hp2 (a := i) (b := j) ?_
    rw [← Nat.card_eq_fintype_card, hyz]
  have hlayer : layer H = ⊥ := layer_eq_bot_of_isSolvable_152 hsolv
  have hcore : CFSG.pPrimeCore 2 H = ⊥ := by
    set N := CFSG.pPrimeCore 2 H with hN
    have hNn : N.Normal := CFSG.pPrimeCore_normal (p := 2) (G := H)
    have hNcop : Nat.Coprime 2 (Nat.card N) := CFSG.pPrimeCore_coprime_card (p := 2) (G := H)
    have hNdvd : Nat.card N ∣ p ^ a := by
      have h1 : Nat.card N ∣ p ^ a * 2 ^ b := (Subgroup.card_subgroup_dvd_card N).trans hcard
      exact (Nat.Coprime.pow_left b hNcop).symm.dvd_of_dvd_mul_right h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hNdvd
    have hNp : IsPGroup p N := IsPGroup.of_card hk
    set P' := P.subgroupOf H with hP'
    have hP'card : Nat.card P' = p ^ a := by
      rw [hP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : P ≤ H)).toEquiv, ha]
    have hP'p : IsPGroup p P' := IsPGroup.of_card hP'card
    have hNP' : N ≤ P' := by
      have hsup : IsPGroup p (N ⊔ P' : Subgroup H) := IsPGroup.to_sup_of_normal_left hNp hP'p
      obtain ⟨m, hm⟩ := hsup.exists_card_eq
      have hle : P' ≤ N ⊔ P' := le_sup_right
      have hma : m ≤ a := by
        have h1 : p ^ m ∣ p ^ a * 2 ^ b := hm ▸ (Subgroup.card_subgroup_dvd_card _).trans hcard
        have h2 : p ^ m ∣ p ^ a :=
          (Nat.Coprime.pow m b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).dvd_of_dvd_mul_right
            h1
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
      have heq : N ⊔ P' = P' := by
        refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
        rw [hm, hP'card]
        exact Nat.pow_le_pow_right hp.pos hma
      exact heq ▸ le_sup_left
    have hdis : Disjoint N (CFSG.pCore 2 H) :=
      IsPGroup.disjoint_of_ne p 2 hp2 N _ hNp (CFSG.pCore_isPGroup (p := 2) (G := H))
    rw [eq_bot_iff]
    intro n hn
    have hnP : ((n : H) : G) ∈ P := Subgroup.mem_subgroupOf.mp (hNP' hn)
    have hnC : ((n : H) : G) ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      rw [CFSG.Open.pCoreOf] at ho
      obtain ⟨o', ho', rfl⟩ := ho
      have hc := Subgroup.commute_of_normal_of_disjoint N (CFSG.pCore 2 H) hNn
        (CFSG.pCore_normal (p := 2) (G := H)) hdis n o' hn ho'
      exact (congrArg Subtype.val hc).symm
    have h1 : ((n : H) : G) ∈ (⊥ : Subgroup G) := hF ▸ ⟨hnP, hnC⟩
    rw [Subgroup.mem_bot] at h1 ⊢
    exact Subtype.ext h1
  rw [generalizedFitting, hlayer, sup_bot_eq, Fitting_eq_pcore H 2 hcore]

@[expose] def Step152ConfPSProd (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T → KData152 A LB P T K S →
      P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
      ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal →
        ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G)

@[expose] def Step152ConfPSFaith (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ (Y M X : Subgroup G) (c' : G) (L' : Subgroup G) (p : ℕ) (P T K S : Subgroup G),
    Pt152 A LB Y M X c' L' → PData152 A X p P → TData152 A LB X P T → KData152 A LB P T K S →
      P ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype →
      ((P ⊔ CFSG.Open.pCoreOf 2 K).subgroupOf K).Normal →
      ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) →
        P ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 (P ⊔ S) : Set G) = ⊥

@[expose] noncomputable def Step152ConfPSProdR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfPSProd A (lB A)

@[expose] noncomputable def Step152ConfPSFaithR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step152ConfPSFaith A (lB A)

omit [Finite G] in
theorem isPGroup_of_pData {A X : Subgroup G} {p : ℕ} {P : Subgroup G} (hP : PData152 A X p P) :
    IsPGroup p P := by
  have : Fact p.Prime := ⟨hP.prime⟩
  rcases hP.type_p with ⟨-, h⟩ | ⟨-, h⟩
  · exact IsPGroup.of_card h
  · exact IsPGroup.of_card h

theorem step152ConfPS_of_split {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hprod : Step152ConfPSProd A LB) (hfaith : Step152ConfPSFaith A LB) :
    Step152ConfPS A LB := by
  intro Y M X c' L' p P T K S hpt hP hT hK hθ hn
  have : Fact p.Prime := ⟨hP.prime⟩
  have hps := hprod Y M X c' L' p P T K S hpt hP hT hK hθ hn
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hK.mem_sk.prop
  exact ⟨hps, generalizedFitting_eq_pCore_of_faithful hP.odd (isPGroup_of_pData hP) hS2 hps
    (hfaith Y M X c' L' p P T K S hpt hP hT hK hθ hn hps)⟩

theorem step152ConfPSR_of (hprod : Step152ConfPSProdR) (hfaith : Step152ConfPSFaithR) :
    Step152ConfPSR :=
  fun G _ _ A c L hR => step152ConfPS_of_split (hprod G A c L hR) (hfaith G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
