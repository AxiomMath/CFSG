module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZI
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.KF

open Subgroup

theorem gwQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.GorensteinWalter.IsQuasisimple A) : CFSG.GorensteinWalter.IsQuasisimple B := by
  obtain ⟨hnt, hcomm, hsimp⟩ := h
  have hc : (center A).map (e : A →* B) = center B := Subgroup.map_center_eq e
  let e' : A ⧸ center A ≃* B ⧸ center B := QuotientGroup.congr _ _ e hc
  refine ⟨e.symm.toEquiv.nontrivial, ?_, e'.symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hcomm ⊢
  rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator,
    hcomm]

variable {G : Type} [Group G]

theorem isComponentOf_map_conj {H J : Subgroup G}
    (hJ : CFSG.GorensteinWalter.IsComponentOf J H) {n : G} (hn : n ∈ H) :
    CFSG.GorensteinWalter.IsComponentOf (J.map (MulAut.conj n).toMonoidHom) H := by
  obtain ⟨hJH, hsub, hq⟩ := hJ
  refine ⟨?_, ?_, gwQuasisimple_of_mulEquiv
    (J.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective) hq⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hn (hJH hx)) (H.inv_mem hn)
  · have heq : (J.map (MulAut.conj n).toMonoidHom).subgroupOf H =
        (J.subgroupOf H).map (MulAut.conj (⟨n, hn⟩ : H)).toMonoidHom := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨⟨x, hJH hx⟩, hx, Subtype.ext ?_⟩
        simpa using hxy
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by simp⟩
    rw [heq]
    exact hsub.map (MulAut.conj (⟨n, hn⟩ : H)).surjective

theorem mul_comm_of_ne [Finite G] {H K K' : Subgroup G}
    (hK : CFSG.GorensteinWalter.IsComponentOf K H)
    (hK' : CFSG.GorensteinWalter.IsComponentOf K' H) (hne : K ≠ K') {a b : G} (ha : a ∈ K)
    (hb : b ∈ K') : a * b = b * a := by
  have h := C11AmS.S12.commutator_eq_bot_of_ne hK hK' hne
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at hmem
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hmem, one_mul]

theorem two_dvd_card_of_gwQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (h : CFSG.GorensteinWalter.IsQuasisimple Q) : 2 ∣ Nat.card Q := by
  obtain ⟨hnt, hcomm, -⟩ := h
  have : Group.IsPerfect Q := Group.isPerfect_def.mpr hcomm
  by_contra hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard (G := Q)
    (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
  exact Group.IsPerfect.not_isSolvable Q hsolv

theorem exists_odd_prime_dvd_card {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    [Group.IsPerfect Q] : ∃ p, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card Q := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 Q := IsPGroup.of_card (n := (Nat.card Q).primeFactorsList.length)
    (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdQ => by
      by_contra hd2
      exact hcon d hd hd2 hdQ)
  exact Group.IsPerfect.not_isNilpotent (G := Q) h2.isNilpotent

theorem p_mul_card_le_of_lt [Finite G] {p : ℕ} [hp : Fact p.Prime] {A B : Subgroup G}
    (hA : IsPGroup p A) (hB : IsPGroup p B) (hAB : A ≤ B) (hne : A ≠ B) :
    p * Nat.card A ≤ Nat.card B := by
  obtain ⟨a, ha⟩ := hA.exists_card_eq
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  have hle : Nat.card A ≤ Nat.card B := Subgroup.card_le_of_le hAB
  have hlt : Nat.card A < Nat.card B := lt_of_le_of_ne hle fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hAB h.ge)
  rw [ha, hb] at hlt ⊢
  have hab : a < b := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 hlt
  calc p * p ^ a = p ^ (a + 1) := by ring
    _ ≤ p ^ b := Nat.pow_le_pow_right hp.out.pos hab

theorem le_two_of_evenRank [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2) {t : G}
    (ht : orderOf t = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : CFSG.Assembly.IsElemAbelian p E) (hEt : E ≤ Subgroup.centralizer ({t} : Set G))
    {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ 2 := by
  set H := Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) with hH
  have hEH : E ≤ H := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxt : Commute t x := (Subgroup.mem_centralizer_singleton_iff.mp (hEt hx)).symm
    exact (Commute.zpow_left hxt i).eq
  have h2loc : CFSG.Assembly.IsTwoLocal H := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨Subgroup.zpowers t, ?_, IsPGroup.of_card (n := 1) ?_, rfl⟩
    · intro hbot
      rw [Subgroup.zpowers_eq_bot] at hbot
      rw [hbot, orderOf_one] at ht
      omega
    · rw [Nat.card_zpowers, ht, pow_one]
  have hbound : ∀ (q : ℕ) (K : Subgroup G), q.Prime → CFSG.Assembly.pRank q K ≤ Nat.card G := by
    intro q K hq
    refine csSup_le' fun j hj => ?_
    obtain ⟨F, -, -, hF⟩ := hj
    have h1 : j < q ^ j := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  have hk1 : k ≤ CFSG.Assembly.pRank p H := by
    refine le_csSup ⟨Nat.card G, fun j hj => ?_⟩ ⟨E, hEH, hE, hk⟩
    obtain ⟨F, -, -, hF⟩ := hj
    have h1 : j < p ^ j := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card F ≤ Nat.card G := Subgroup.card_le_card_group F
    omega
  have hk2 : CFSG.Assembly.pRank p H ≤ CFSG.Assembly.evenRank G := by
    refine le_csSup ⟨Nat.card G, fun j hj => ?_⟩ ⟨p, H, hp, hp2, h2loc, rfl⟩
    obtain ⟨q, K, hq, -, -, rfl⟩ := hj
    exact hbound q K hq
  omega

end CFSG.Quasithin.Vol2.Ch11.SecS.KF
