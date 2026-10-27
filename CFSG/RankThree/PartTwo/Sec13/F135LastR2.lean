module

public import CFSG.RankThree.PartTwo.Sec13.F135LastGlueA
public import CFSG.RankThree.PartTwo.Sec13.F135LastGlueB
public import CFSG.RankThree.PartTwo.Sec13.F135LastR2Plane
public import CFSG.RankThree.PartTwo.Sec13.F135LastR2Hyperplane

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
open CritProof
open scoped commutatorElement

theorem exists_Y_U {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Dp : Subgroup G) (hDp : IsPGroup p Dp) (hexp : ∀ x ∈ Dp, x ^ p = 1)
    (hΦc : ∀ x ∈ (frattini ↥Dp).map Dp.subtype, ∀ d ∈ Dp, x * d = d * x)
    (u : G) (hu : u * u = 1) (hu1 : u ≠ 1)
    (hPmap : p ^ 2 ≤ ((frattini ↥Dp).map Dp.subtype).relIndex
      ((Dp ⊓ Subgroup.centralizer ({u} : Set G)) ⊔ (frattini ↥Dp).map Dp.subtype))
    (hchar2 : CFSG.Open.IsCharTwoType G) :
    ∃ Y : Subgroup G, Y ≤ Dp ⊓ Subgroup.centralizer ({u} : Set G) ∧ Nat.card Y = p ∧
      ¬ Y ≤ (frattini ↥Dp).map Dp.subtype ∧
      ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ⊓ Subgroup.centralizer (Y : Set G),
        Dp ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G)⁆ ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := Dp ⊓ Subgroup.centralizer ({u} : Set G) with hP
  set Φ : Subgroup G := (frattini ↥Dp).map Dp.subtype with hΦ
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G) with hH
  obtain ⟨A, hAP, hAab, hAcard, hAΦ⟩ := exists_E_two hp Dp hDp hexp hΦc P inf_le_left hPmap
  set R : Subgroup G := CFSG.Open.pCoreOf 2 H with hR
  have hAH : A ≤ H := hAP.trans inf_le_right
  have hRp : ¬ p ∣ Nat.card R := by
    intro hdvd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 (isPGroup_pCoreOf 2 H))
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact mem_pCoreOf_conj 2 H (hAH ha) x
  have hfaith : ∀ Z : Subgroup G, Z ≤ A → Z ≠ ⊥ → ¬ Z ≤ Subgroup.centralizer (R : Set G) := by
    intro Z hZA hZ1 hZc
    have hH2 : CFSG.Open.IsTwoLocal H := gb_isTwoLocal_centralizer hu1 hu
    have hZR : Z ≤ R := fun z hz => hchar2 H hH2 ⟨hAH (hZA hz), hZc hz⟩
    have hZp : IsPGroup p Z := hDp.to_le ((hZA.trans hAP).trans inf_le_left)
    have hZ2 : IsPGroup 2 Z := (isPGroup_pCoreOf 2 H).to_le hZR
    apply hZ1
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hZp
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hZ2
    have hc : Nat.card Z = 1 := by
      have h1 : Nat.card Z ∣ p ^ a := ⟨1, by rw [ha, mul_one]⟩
      have h2 : Nat.card Z ∣ 2 ^ b := ⟨1, by rw [hb, mul_one]⟩
      have hcop : Nat.Coprime (p ^ a) (2 ^ b) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
      exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact Subgroup.eq_bot_of_card_eq Z hc
  obtain ⟨Y, hYA, hYc, hYΦ, hYnc⟩ :=
    exists_hyperplane_not_in_frattini A Φ R hAab hAcard hAΦ hAR hRp hfaith
  refine ⟨Y, hYA.trans hAP, hYc, hYΦ, ?_⟩
  intro hbot
  apply hYnc
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have haD : a ∈ Dp := (hAP ha).1
  have haC : a ∈ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ Y ⊔ Subgroup.zpowers u := hy
    have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) := by
      intro y hyY
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hyA : y ∈ A := hYA hyY
      have h := hAab.1.is_comm.comm (⟨a, ha⟩ : A) (⟨y, hyA⟩ : A)
      exact (congrArg Subtype.val h).symm
    have hua : Subgroup.zpowers u ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_iff.1 (hAH ha) u rfl
      exact this
    have := sup_le hYa hua hy'
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hcomm : ⁅x, a⁆ ∈ ⁅R ⊓ Subgroup.centralizer (Y : Set G),
      Dp ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers u : Subgroup G) : Set G)⁆ :=
    Subgroup.commutator_mem_commutator hx ⟨haD, haC⟩
  rw [hbot, Subgroup.mem_bot] at hcomm
  exact commutatorElement_eq_one_iff_mul_comm.1 hcomm


section Cfg

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {p : ℕ}
  {C : Subgroup (CFSG.pCore p L)}

theorem dPrime_exp (hcrit : Crit135 L p C) {z : G} (hz : z ∈ L) :
    ∀ x ∈ dPrime L p C z, x ^ p = 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := ga_mem_dOf.1 (dPrime_le_dOf hcrit hz hx)
  have h := hcrit.criticalAt.exp y hy
  rw [← Subgroup.coe_pow, h, Subgroup.coe_one]

theorem dPrime_frattini_central (hcrit : Crit135 L p C) {z : G} (hz : z ∈ L) :
    ∀ x ∈ (frattini ↥(dPrime L p C z)).map (dPrime L p C z).subtype,
      ∀ d ∈ dPrime L p C z, x * d = d * x := by
  haveI : Fact p.Prime := ⟨hcrit.prime⟩
  set Dp := dPrime L p C z with hDp
  have hexp' : ∀ y : ↥Dp, y ^ p = 1 := fun y =>
    Subtype.ext (by simpa using dPrime_exp hcrit hz y y.2)
  have hfr := CFSG.RankThree.PartTwo.frattini_eq_commutator (isPGroup_dPrime hcrit hz) hexp'
  have hcomm_le : ⁅Dp, Dp⁆ ≤ Subgroup.centralizer (Dp : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨ya, hya, rfl⟩ := ga_mem_dOf.1 (dPrime_le_dOf hcrit hz ha)
    obtain ⟨yb, hyb, rfl⟩ := ga_mem_dOf.1 (dPrime_le_dOf hcrit hz hb)
    obtain ⟨yd, hyd, rfl⟩ := ga_mem_dOf.1 (dPrime_le_dOf hcrit hz hd)
    have hle : omegaOneCore p C ≤ CFSG.pCore p L := by
      unfold omegaOneCore
      exact Subgroup.map_subtype_le _
    have h := (hcrit.criticalAt.comm ya hya yb (hle hyb)).2 yd hyd
    have h' := congrArg (fun w : ↥L => (w : G)) h
    simpa [commutatorElement_def] using h'.symm
  intro x hx d hd
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  rw [hfr] at hy
  have hmem : (y : G) ∈ ⁅Dp, Dp⁆ := by
    have h := Subgroup.mem_map_of_mem Dp.subtype hy
    rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h
  exact ((Subgroup.mem_centralizer_iff.1 (hcomm_le hmem)) d hd).symm

theorem r2_holds : R2 := by
  intro G _ _ A c L p C c2
  have hcrit := c2.crit
  have hp := hcrit.prime
  have hp2 : p ≠ 2 := by have := c2.p_ge_seven; omega
  have hzL := c2.z_mem
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := exists_Y_U hp hp2 (dPrime L p C c2.z)
    (isPGroup_dPrime hcrit hzL) (dPrime_exp hcrit hzL) (dPrime_frattini_central hcrit hzL)
    c2.u c2.u_sq c2.u_ne c2.Cu_rank c2.data.charTwoType
  exact ⟨{ c2 with
    Y := Y
    U := ⁅CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c2.u} : Set G)) ⊓
        Subgroup.centralizer (Y : Set G),
      dPrime L p C c2.z ⊓ Subgroup.centralizer ((Y ⊔ Subgroup.zpowers c2.u : Subgroup G) : Set G)⁆
    Y_le := hY1
    Y_card := hY2
    Y_not_frattini := hY3
    U_eq := rfl
    U_ne := hY4 }⟩

end Cfg

end CFSG.RankThree.PartTwo.Sec13.F135Last
