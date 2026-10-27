module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecFAct
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecA02Recog
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open CFSG.Quasithin.Vol2.Ch11.SecA (oSL2 BarData)

theorem isPSL_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {k p f : ℕ}
    (h : IsPSL k p f B) : IsPSL k p f A := by
  obtain ⟨hadm, K, hF, hfin, hK, ⟨g⟩⟩ := h
  exact ⟨hadm, K, hF, hfin, hK, ⟨e.trans g⟩⟩

theorem isSL3_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {q : ℕ}
    (h : IsSL3 q B) : IsSL3 q A := by
  obtain ⟨K, hK, hKf, hq, ⟨g⟩⟩ := h
  exact ⟨K, hK, hKf, hq, ⟨e.trans g⟩⟩

variable {G : Type} [Group G] [Finite G] {L X : Subgroup G} {n : ℕ}

noncomputable def equivOfPCoreEqBot (h : CFSG.pCore 2 ↥L = ⊥) :
    ↥L ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)

theorem card_dvd_of_sl3 {Y : Type} [Group Y] [Finite Y]
    (hY : IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y) :
    Nat.card Y ∣ 2 ^ (3 * n) * (oSL2 n * (2 ^ (3 * n) - 1)) := by
  have e1 : (2 ^ n) ^ 3 = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
  have e2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  rcases hY with hY | ⟨K, _, _, hK, ⟨e⟩⟩
  · rw [Ch11.SecA.card_of_isPSL (by norm_num) hY, hI, Finset.prod_insert (by decide),
      Finset.prod_singleton, show 3 * (3 - 1) / 2 = 3 by norm_num, e1, e2]
    refine Nat.div_dvd_of_dvd ?_
    have h1 : 2 ^ n - 1 ∣ 2 ^ (2 * n) - 1 :=
      ⟨2 ^ n + 1, Ch11.SecA.two_pow_two_mul_sub_one n⟩
    exact ((Nat.gcd_dvd_right _ _).trans h1).trans
      (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  · rw [Nat.card_congr (e.trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm).toEquiv,
      CFSG.OrderReductions.LinearOrders.card_specialLinear K 3 (by norm_num), hK, hI,
      Finset.prod_insert (by decide), Finset.prod_singleton,
      show 3 * (3 - 1) / 2 = 3 by norm_num, e1, e2]

theorem index_odd_of_sl3 {Y : Type} [Group Y] [Finite Y] (hn : 1 ≤ n)
    (hY : IsPSL 3 2 n Y ∨ IsSL3 (2 ^ n) Y) {B : Subgroup Y}
    (hB : Nat.card ↥B = 2 ^ (3 * n) * oSL2 n) : ¬ 2 ∣ B.index := by
  have hdvd := card_dvd_of_sl3 hY
  rw [← Subgroup.card_mul_index B, hB, mul_assoc] at hdvd
  have hpos : 0 < 2 ^ (3 * n) := by positivity
  have h1 := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
  have hpos' : 0 < oSL2 n := (Ch11.SecA.odd_oSL2 hn).pos
  have h2 := Nat.dvd_of_mul_dvd_mul_left hpos' h1
  have hodd : Odd (2 ^ (3 * n) - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  intro h3
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h3.trans h2))

omit [Finite G] in
theorem commutator_eq_top_of_perfect {K : Subgroup G} (h : ⁅K, K⁆ = K) :
    _root_.commutator ↥K = ⊤ := by
  have hmap : (_root_.commutator ↥K).map K.subtype = K := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, h]
  apply Subgroup.map_injective K.subtype_injective
  rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_E9 {E : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card ↥E = 3 ^ 2) :
    ∃ E' : Subgroup G, E' ≤ L ∧ IsElemAbelian 3 E' ∧ Nat.card ↥E' = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ
  set Et := E.comap φ with hEt
  have h9 : 3 ^ 2 ∣ Nat.card ↥Et := by
    have hs : Function.Surjective ((φ.comp Et.subtype).codRestrict E fun x => x.2) := by
      intro y
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) (y : _)
      exact ⟨⟨x, show φ x ∈ E from hx ▸ y.2⟩, Subtype.ext hx⟩
    rw [← hEc]
    exact Subgroup.card_dvd_of_surjective hs
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Et) 3 h9
  set K : Subgroup ↥L := P.map Et.subtype with hK
  have hKc : Nat.card ↥K = 3 ^ 2 := by
    rw [hK, Subgroup.card_map_of_injective Et.subtype_injective, hP]
  have hKE : ∀ x ∈ K, φ x ∈ E := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hinj : ∀ x ∈ K, φ x = 1 → x = 1 := by
    intro x hx h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, h1⟩
    have h2 : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : x ^ 3 ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥K) (x := ⟨x, hx⟩)
      rw [hKc] at this
      exact congrArg Subtype.val this
    have h4 : orderOf x ∣ Nat.gcd (2 ^ k) (3 ^ 2) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow k 2 (by norm_num)), Nat.dvd_one,
      orderOf_eq_one_iff] at h4
    exact h4
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have h1 : φ a * φ b = φ b * φ a := by
      have := hE.1
      have h := mul_comm' (⟨φ a, hKE a ha⟩ : ↥E) ⟨φ b, hKE b hb⟩
      exact congrArg Subtype.val h
    have h2 := hinj (a * b * a⁻¹ * b⁻¹) (K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha))
      (K.inv_mem hb)) (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]; group)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  have hcube : ∀ a ∈ K, a ^ 3 = 1 := fun a ha =>
    hinj _ (K.pow_mem ha 3) (by rw [map_pow]; exact hE.2 _ (hKE a ha))
  refine ⟨K.map L.subtype, Subgroup.map_subtype_le K, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨x, ⟨a, ha, rfl⟩⟩ := x
    obtain ⟨y, ⟨b, hb, rfl⟩⟩ := y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, hcube a ha, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hKc]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
