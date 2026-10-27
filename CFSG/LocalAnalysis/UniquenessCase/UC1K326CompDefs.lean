module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Amb
public import CFSG.Walter.J1Props.Transfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

@[expose] def IsSL3pi (L : Type) [Group L] : Prop :=
  (∃ p f : ℕ, p ^ f % 3 = 1 ∧ CFSG.Open.IsQuasisimple L ∧ Nat.card (Subgroup.center L) = 3 ∧
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSL 3 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ CFSG.Open.IsQuasisimple L ∧ Nat.card (Subgroup.center L) = 3 ∧
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 3 p f)

theorem IsSL3pi.isQuasisimple {L : Type} [Group L] (h : IsSL3pi L) :
    CFSG.Open.IsQuasisimple L := by
  rcases h with ⟨_, _, _, h, _⟩ | ⟨_, _, _, h, _⟩ <;> exact h

theorem IsSL3pi.card_center {L : Type} [Group L] (h : IsSL3pi L) :
    Nat.card (Subgroup.center L) = 3 := by
  rcases h with ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ <;> exact h

@[expose] def zOf {G : Type} [Group G] (L : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥L).map L.subtype

@[expose] def SL3Out : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSL3pi L →
    ∃ S : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer L),
      S.Normal ∧ IsPGroup 3 S ∧ ¬ 3 ∣ S.index

@[expose] def SL3Gen : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L T : Subgroup H) (a : H),
    IsSL3pi ↥L → L.Normal → IsSylowOf 3 T L → a ∈ Subgroup.normalizer (T : Set H) →
    a ^ 3 ∈ Subgroup.centralizer (L : Set H) → (∃ t ∈ T, ⁅t, a⁆ ∉ zOf L) →
    (Subgroup.centralizer ({a} : Set H)).relIndex T = 3 →
    IsMulCommutative ↥(T ⊓ Subgroup.centralizer ({a} : Set H)) →
    T ⊔ (L ⊓ Subgroup.centralizer ({a} : Set H)) = L

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

theorem not_isMulCommutative_of_isSylowOf {L T : Subgroup G} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hz : Nat.card (Subgroup.center ↥L) = 3) (hT : IsSylowOf 3 T L) :
    ¬ IsMulCommutative ↥T := by
  intro hcomm
  obtain ⟨Q, hQ⟩ := hT
  haveI hTcomm : IsMulCommutative ↥T := hcomm
  haveI hQcomm : IsMulCommutative (Q : Subgroup ↥L) := by
    have hQc : IsMulCommutative (T.comap L.subtype) :=
      Subgroup.comap_injective_isMulCommutative T L.subtype_injective
    rw [← hQ, Subgroup.comap_map_eq_self_of_injective L.subtype_injective
      (Q : Subgroup ↥L)] at hQc
    exact hQc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hno : ∀ H : Subgroup ↥L, H.Normal → H.index ≠ 3 := by
    intro H hHn hHidx
    haveI : H.Normal := hHn
    have hcard : Nat.card (↥L ⧸ H) = 3 := by
      rw [← Subgroup.index_eq_card, hHidx]
    haveI : IsCyclic (↥L ⧸ H) := isCyclic_of_prime_card hcard
    have hle : commutator ↥L ≤ H :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    have htop : H = ⊤ := by
      rw [← top_le_iff, ← hL.1]
      exact hle
    rw [htop, Subgroup.index_top] at hHidx
    norm_num at hHidx
  have hcent_ne_bot : Subgroup.center ↥L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hz
    norm_num at hz
  obtain ⟨z₀, hz₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcent_ne_bot
  let z : ↥L := (z₀ : ↥L)
  have hz1 : z ≠ 1 := fun h => hz₀ (Subtype.ext h)
  have hzQ : z ∈ (Q : Subgroup ↥L) := by
    have hcard3 : IsPGroup 3 (Subgroup.center ↥L) :=
      IsPGroup.of_card (n := 1) (by rw [hz, pow_one])
    exact hcard3.le_sylow_of_normal Q z₀.2
  have hzcent : ∀ m : ↥L, m * z = z * m := fun m =>
    Subgroup.mem_center_iff.mp z₀.2 m
  exact hz1 (CFSG.Walter.J1Props.eq_one_of_mem_sylow_of_commute_normalizer hno Q hzQ
    (fun m _ => hzcent m))

theorem zOf_le_center (h : Hyp326 G n P) {L : Subgroup G} (hLn : L.Normal)
    (hz : Nat.card (Subgroup.center ↥L) = 3) :
    zOf L ≤ P ∧ zOf L ≤ Subgroup.centralizer (P : Set G) := by
  haveI : L.Normal := hLn
  haveI : (Subgroup.center ↥L).Characteristic := Subgroup.centerCharacteristic
  haveI hzn : (zOf L).Normal := ConjAct.normal_of_characteristic_of_normal
  have hzcard : Nat.card (zOf L) = 3 := by
    rw [zOf, Subgroup.card_map_of_injective L.subtype_injective, hz]
  have hzp : IsPGroup 3 (zOf L) := IsPGroup.of_card (n := 1) (by rw [hzcard, pow_one])
  have hleCore : zOf L ≤ CFSG.pCore 3 G := by
    rw [CFSG.pCore]
    exact le_sSup ⟨hzn, hzp⟩
  have hleP : zOf L ≤ P := hleCore.trans (pCore_le_sylow h.sylow)
  refine ⟨hleP, ?_⟩
  haveI hNn : ((zOf L).subgroupOf P).Normal := inferInstance
  have hNcard : Nat.card ((zOf L).subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleP).toEquiv, hzcard]
  have hNne : (zOf L).subgroupOf P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hNcard
    norm_num at hNcard
  obtain ⟨e⟩ := h.wr
  obtain ⟨-, -, hcent⟩ := zwr_card_center h.one_le e
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card (Subgroup.center ↥P) := by
    rw [hcent]
    simpa only [pow_one] using pow_dvd_pow 3 h.one_le
  obtain ⟨z₀, hz₀ord⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  have hz₀3c : z₀ ^ 3 = 1 := by
    have hpow := pow_orderOf_eq_one z₀
    rwa [hz₀ord] at hpow
  have hz₀1 : z₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz₀ord
    norm_num at hz₀ord
  have hz₀3 : ((z₀ : ↥P)) ^ 3 = 1 := by
    simpa using congrArg (fun x : Subgroup.center ↥P => (x : ↥P)) hz₀3c
  have hz₀mem : (z₀ : ↥P) ∈ (zOf L).subgroupOf P :=
    zwr_normal_contains_omega_center h.one_le e hNn hNne (z₀ : ↥P) z₀.2 hz₀3
  have hNle : (zOf L).subgroupOf P ≤ Subgroup.center ↥P := by
    have hzp_le : Subgroup.zpowers ((z₀ : ↥P)) ≤ (zOf L).subgroupOf P :=
      Subgroup.zpowers_le.mpr hz₀mem
    have hz₀1' : (z₀ : ↥P) ≠ 1 := fun hh => hz₀1 (Subtype.ext hh)
    have hcardzp : Nat.card (Subgroup.zpowers ((z₀ : ↥P))) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hz₀3 hz₀1'
    have heq : Subgroup.zpowers ((z₀ : ↥P)) = (zOf L).subgroupOf P :=
      Subgroup.eq_of_le_of_card_ge hzp_le (by rw [hNcard, hcardzp])
    rw [← heq]
    exact Subgroup.zpowers_le.mpr z₀.2
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hgP : g ∈ P := hleP hg
  have hgN : (⟨g, hgP⟩ : ↥P) ∈ (zOf L).subgroupOf P := by
    rw [Subgroup.mem_subgroupOf]
    exact hg
  have hcen : (⟨g, hgP⟩ : ↥P) ∈ Subgroup.center ↥P := hNle hgN
  have hcomm := Subgroup.mem_center_iff.mp hcen ⟨p, hp⟩
  exact congrArg (fun x : ↥P => (x : G)) hcomm

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
