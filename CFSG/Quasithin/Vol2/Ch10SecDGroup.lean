module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open

variable {G : Type} [Group G]

theorem conjAct_eq_one_iff {V : Subgroup G} (g : Subgroup.normalizer (V : Set G)) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

theorem mem_centralizer_of_orderOf {V : Subgroup G} {b p : G}
    (hb : b ∈ Subgroup.normalizer (V : Set G)) (hp : p ∈ Subgroup.normalizer (V : Set G))
    (hbp : conjAct V ⟨b, hb⟩ = conjAct V ⟨p, hp⟩) (hbo : Odd (orderOf b))
    (hpo : ∃ k : ℕ, p ^ 2 ^ k = 1) : b ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨k, hk⟩ := hpo
  have h1 : orderOf (conjAct V ⟨b, hb⟩) ∣ orderOf b := by
    have := orderOf_map_dvd (conjAct V) (⟨b, hb⟩ : Subgroup.normalizer (V : Set G))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (conjAct V ⟨p, hp⟩) ∣ 2 ^ k := by
    refine (orderOf_map_dvd (conjAct V) (⟨p, hp⟩ : Subgroup.normalizer (V : Set G))).trans ?_
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one hk
  rw [hbp] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hodd : Odd (orderOf (conjAct V ⟨p, hp⟩)) := Odd.of_dvd_nat hbo h1
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  rw [← hbp] at hj
  exact (conjAct_eq_one_iff ⟨b, hb⟩).mp hj

theorem conj_mem_centralizer {V : Subgroup G} {y c : G}
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    y * c * y⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hw : y⁻¹ * v * y⁻¹⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hyV) v).mp hv
  have hcw := (Subgroup.mem_centralizer_iff.mp hc) _ hw
  simp only [inv_inv] at hcw
  calc v * (y * c * y⁻¹) = y * ((y⁻¹ * v * y) * c) * y⁻¹ := by group
    _ = y * (c * (y⁻¹ * v * y)) * y⁻¹ := by rw [hcw]
    _ = y * c * y⁻¹ * v := by group

theorem le_normalizer_inf_centralizer {X V : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) :
    X ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => ⟨X.mul_mem (X.mul_mem hx hc.1) (X.inv_mem hx),
    conj_mem_centralizer (hXV hx) hc.2⟩, fun hc => ?_⟩
  have h1 : x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ ∈ X ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨X.mul_mem (X.mul_mem (X.inv_mem hx) hc.1) (X.inv_mem (X.inv_mem hx)),
      conj_mem_centralizer ((Subgroup.normalizer _).inv_mem (hXV hx)) hc.2⟩
  simpa [mul_assoc] using h1

variable [Finite G]

theorem exists_relIndex_oTwoUpper_eq_two_pow {X H : Subgroup G} (hXH : X ≤ H) :
    ∃ k : ℕ, (X ⊓ oTwoUpper H).relIndex X = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ((oTwoUpper H).subgroupOf X).Normal := ⟨fun n hn x => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H (hXH x.2)) n).mp hn
    simpa using this⟩
  have hp : IsPGroup 2 (↥X ⧸ (oTwoUpper H).subgroupOf X) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H (hXH x.2)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  refine ⟨k, ?_⟩
  have h1 : (X ⊓ oTwoUpper H).subgroupOf X = (oTwoUpper H).subgroupOf X := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [Subgroup.relIndex, h1, Subgroup.index_eq_card, hk]

theorem isPGroup_inf_centralizer {X N V L0 : Subgroup G} (hNX : N ≤ X)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hL0 : L0 ≤ Subgroup.normalizer (V : Set G))
    (hN2 : E1.IsTwoClosed N) (hodd : ∀ x ∈ X, Odd (orderOf x) → x ∈ N)
    (hidx : ∃ k : ℕ, N.relIndex X = 2 ^ k)
    (hB : ∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B X → ∀ b ∈ B,
      (∀ l ∈ L0, b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G)) → b = 1) :
    IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨P, ⟨hPN, hP2, hPodd⟩, hPn⟩ := hN2
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hP2
  have hcop : Nat.Coprime (Nat.card (P.subgroupOf N)) (P.subgroupOf N).index := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv, ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hPodd)
  obtain ⟨B', hB'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set D := B'.map N.subtype with hD
  have hDN : D ≤ N := Subgroup.map_subtype_le B'
  have hcardD : Nat.card D = P.relIndex N := by
    rw [hD, Nat.card_congr (B'.equivMapOfInjective _ (Subgroup.subtype_injective N)).toEquiv.symm,
      ← hB'.symm.index_eq_card]
    rfl
  have hDodd : Odd (Nat.card D) := by
    rw [hcardD]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hPodd)
  have hDidx : D.relIndex N = 2 ^ a := by
    have h1 : D.subgroupOf N = B' :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective N) B'
    rw [Subgroup.relIndex, h1, hB'.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv, ha]
  obtain ⟨k, hk⟩ := hidx
  have hHall : QuasithinUnique.Lin2.IsHallTwoPrimeOf D X :=
    ⟨hDN.trans hNX, hDodd, a + k, by
      rw [← Subgroup.relIndex_mul_relIndex D N X hDN hNX, hDidx, hk, pow_add]⟩
  have key : ∀ d ∈ X ⊓ Subgroup.centralizer (V : Set G), Odd (orderOf d) → d = 1 := by
    intro d hd hdo
    have hdN : d ∈ N := hodd d hd.1 hdo
    obtain ⟨⟨⟨p, hp⟩, ⟨b, hb⟩⟩, hpb, -⟩ := hB'.existsUnique ⟨d, hdN⟩
    have hpb' : (p : G) * (b : G) = d := congrArg Subtype.val hpb
    have hpP : (p : G) ∈ P := hp
    have hbD : (b : G) ∈ D := ⟨b, hb, rfl⟩
    have hbV : (b : G) ∈ Subgroup.normalizer (V : Set G) := hXV (hNX b.2)
    have hpV : ((p : G))⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer _).inv_mem (hXV (hNX p.2))
    have hdV : d ∈ Subgroup.normalizer (V : Set G) := hXV hd.1
    have hbeq : (b : G) = ((p : G))⁻¹ * d := by rw [← hpb']; group
    have hact : conjAct V ⟨(b : G), hbV⟩ = conjAct V ⟨((p : G))⁻¹, hpV⟩ := by
      have h1 : (⟨(b : G), hbV⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨((p : G))⁻¹, hpV⟩ * ⟨d, hdV⟩ := Subtype.ext hbeq
      rw [h1, map_mul, (conjAct_eq_one_iff ⟨d, hdV⟩).mpr hd.2, mul_one]
    have hbo : Odd (orderOf (b : G)) :=
      Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard D hbD)
    have hpo : ∃ j : ℕ, ((p : G))⁻¹ ^ 2 ^ j = 1 := by
      obtain ⟨j, hj⟩ := hP2 ⟨(p : G), hpP⟩
      exact ⟨j, by rw [inv_pow, (by simpa using congrArg Subtype.val hj : (p : G) ^ 2 ^ j = 1),
        inv_one]⟩
    have hbC := mem_centralizer_of_orderOf hbV hpV hact hbo hpo
    have hb1 : (b : G) = 1 := by
      refine hB D hHall (b : G) hbD fun l hl => ?_
      have hlV : l ∈ Subgroup.normalizer (V : Set G) := hL0 hl
      have hmem : (b : G) * l * (b : G)⁻¹ * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
        (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
          ((Subgroup.normalizer _).mul_mem hbV hlV) ((Subgroup.normalizer _).inv_mem hbV))
          ((Subgroup.normalizer _).inv_mem hlV)
      refine (conjAct_eq_one_iff ⟨_, hmem⟩).mp ?_
      have h1 : (⟨(b : G) * l * (b : G)⁻¹ * l⁻¹, hmem⟩ : Subgroup.normalizer (V : Set G)) =
          ⟨(b : G), hbV⟩ * ⟨l, hlV⟩ * (⟨(b : G), hbV⟩)⁻¹ * (⟨l, hlV⟩)⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv,
        (conjAct_eq_one_iff ⟨(b : G), hbV⟩).mpr hbC]
      group
    have hdp : d = (p : G) := by rw [← hpb', hb1, mul_one]
    obtain ⟨j, hj⟩ := hP2 ⟨(p : G), hpP⟩
    have hpj : (p : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hdvd : orderOf d ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one (hdp ▸ hpj)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hi] at hdo
    have hi0 : i = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hdo) ((Nat.even_pow' hne).mpr even_two)
    rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
    exact hi
  intro c
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (c : G)).ne'
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  refine key _ ((X ⊓ Subgroup.centralizer (V : Set G)).pow_mem c.2 _) ?_
  rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hkm, Nat.gcd_mul_right_left]
  · simpa [hkm, Nat.mul_div_cancel_left _ (pow_pos two_pos k)] using hm

end CFSG.Quasithin.Vol2.Ch10.SecD
