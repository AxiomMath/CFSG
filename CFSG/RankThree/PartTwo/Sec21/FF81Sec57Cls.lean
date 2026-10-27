module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57KDefs
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6RefS
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
public import CFSG.Quasithin.H13.GoldschmidtSp62Base
public import Certificates.Certificate899111
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Cls

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U

theorem all_getD {p : List ℕ → Bool} {es : Array (List ℕ)} (h : es.all p = true) {t : ℕ}
    (ht : t < es.size) : p (es.getD t []) = true := by
  rw [Array.all_eq_true] at h
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]
  exact h t ht

theorem getD_mem {es : Array (List ℕ)} {t : ℕ} (ht : t < es.size) : es.getD t [] ∈ es := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some]
  exact Array.getElem_mem ht

theorem mul6_self_eq {x : H6} {c : List ℕ} (hc : dec6 c = mat6 x) (h2 : x * x = 1) :
    mul6 c c = one6 :=
  dec6_injective (canon6_mul6 _ _) canon6_one6
    (by rw [dec6_mul6, hc, ← map_mul, h2, map_one, dec6_one6])

theorem ne_one6 {x : H6} {c : List ℕ} (hc : dec6 c = mat6 x) (h1 : x ≠ 1) : c ≠ one6 := by
  rintro rfl
  exact h1 (mat6_injective (by rw [← hc, dec6_one6, map_one]))

theorem sq_eq_one_of_orderOf {G : Type*} [Monoid G] {x : G} (h : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem ne_one_of_orderOf {G : Type*} [Monoid G] {x : G} {n : ℕ} (h : orderOf x = n)
    (hn : n ≠ 1) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  exact hn h.symm

theorem orderOf_conj {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

theorem conj_comm_iff {G : Type*} [Group G] (g x y : G) :
    g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) ↔ x * y = y * x := by
  constructor
  · intro h
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using h'
  · intro h
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

section Three

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS


noncomputable def rep3 : Fin 3 → H6 := ![zH 1, zH 0 * zH 1, vecElt zH ![1, 1, 1]]

def cOrd3 : Fin 3 → ℕ := ![2160, 108, 648]

theorem aElt1 : aElt 1 = zH 1 := by
  show zH 0 ^ 0 * zH 1 ^ 1 * zH 2 ^ 0 = zH 1
  rw [pow_zero, pow_zero, pow_one, one_mul, mul_one]

theorem aElt3 : aElt 3 = zH 0 * zH 1 := by
  show zH 0 ^ 1 * zH 1 ^ 1 * zH 2 ^ 0 = zH 0 * zH 1
  rw [pow_zero, pow_one, pow_one, mul_one]

theorem card_c7 : Nat.card c7Sub = 648 :=
  card_closure_genSet _ _ _ c7_ok107

theorem card_cen_rep3 (j : Fin 3) : Nat.card (Cen (rep3 j)) = cOrd3 j := by
  fin_cases j
  · show Nat.card (Subgroup.centralizer {zH 1}) = 2160
    rw [← aElt1, ← centSub_eq, card_centSub]; rfl
  · show Nat.card (Subgroup.centralizer {zH 0 * zH 1}) = 108
    rw [← aElt3, ← centSub_eq, card_centSub]; rfl
  · show Nat.card (Subgroup.centralizer {vecElt zH ![1, 1, 1]}) = 648
    rw [← c7Sub_eq, card_c7]

theorem exists_conj_rep3 {x : H6} (hx : orderOf x = 3) :
    ∃ j : Fin 3, ∃ m : H6, x = m * rep3 j * m⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := wreathW zH CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH) (by rw [card_wreathW_zH, factorization_card_H6]; norm_num) hp
  obtain ⟨w, hw, hgw⟩ := hg (Subgroup.mem_zpowers x)
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgw
  obtain ⟨v, j, rfl⟩ := mem_wreathW wreathFacts_zH hw
  have hw3 : orderOf (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) = 3 := by
    have e := orderOf_conj g (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))
    rw [hgw, hx] at e
    exact e.symm
  have hw3' : (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) ^ 3 = 1 := by
    have e := pow_orderOf_eq_one (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ))
    rwa [hw3] at e
  have key : ∀ k : Fin 3, (∃ h : H6, vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ) = h * rep3 k * h⁻¹) →
      ∃ m : H6, g * (vecElt zH v * CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.tH ^ (j : ℕ)) * g⁻¹ = m * rep3 k * m⁻¹ := by
    rintro k ⟨h, hh⟩
    exact ⟨g * h, by rw [hh]; group⟩
  rw [← hgw]
  rcases conj_rep_of_wreath hw3' (ne_one_of_orderOf hw3 (by norm_num)) with h | h | h
  · exact ⟨0, key 0 h⟩
  · exact ⟨1, key 1 h⟩
  · exact ⟨2, key 2 h⟩

theorem exists_card_rep3 {x : H6} (hx : orderOf x = 3) :
    ∃ j : Fin 3, Nat.card (Cen x) = cOrd3 j ∧ ∃ m : H6, x = m * rep3 j * m⁻¹ := by
  obtain ⟨j, m, rfl⟩ := exists_conj_rep3 hx
  exact ⟨j, by rw [Cen, card_cen_conj, ← card_cen_rep3, Cen], m, rfl⟩

theorem cOrd3_injective : Function.Injective cOrd3 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)

theorem h6_card3 {x : H6} (hx : orderOf x = 3) :
    Nat.card (Cen x) = 2160 ∨ Nat.card (Cen x) = 648 ∨ Nat.card (Cen x) = 108 := by
  obtain ⟨j, hj, -⟩ := exists_card_rep3 hx
  rw [hj]
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)

theorem h6_conj3 {x y : H6} (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hc : Nat.card (Cen x) = Nat.card (Cen y)) : ∃ m : H6, m * x * m⁻¹ = y := by
  obtain ⟨j, hj, m, rfl⟩ := exists_card_rep3 hx
  obtain ⟨j', hj', m', rfl⟩ := exists_card_rep3 hy
  have e : j = j' := cOrd3_injective (hj.symm.trans (hc.trans hj'))
  subst e
  exact ⟨m' * m⁻¹, by group⟩

end Three


section Inv

open CFSG.Quasithin.H13.U3 (centralizer_tH_eq exists_orbElt_of_isConj mem_closure_of_mem_table
  card_centralizer_conj)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH mat6_zH)


theorem card_cen_tH (i : Fin 4) : Nat.card (Cen (CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH i)) = centSize i := by
  rw [Cen, centralizer_tH_eq, card_XH]

theorem exists_conj_tH {s : H6} (hs : orderOf s = 2) : ∃ i : Fin 4, ∃ g, s = g * CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH i * g⁻¹ :=
  exists_conj_of_sylow_classes SH_isPGroup SH_index exists_conj_of_mem_SH hs

theorem exists_conj_t0 {s : H6} (hs : orderOf s = 2) (h5 : 5 ∣ Nat.card (Cen s)) :
    ∃ g, s = g * CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH 0 * g⁻¹ := by
  obtain ⟨i, g, rfl⟩ := exists_conj_tH hs
  rw [Cen, card_centralizer_conj, ← Cen, card_cen_tH] at h5
  have hi : i = 0 := by
    fin_cases i
    · rfl
    all_goals exact absurd h5 (by decide)
  subst hi
  exact ⟨g, rfl⟩

theorem contains_orbit0 {y : H6} {c : List ℕ} (hc : dec6 c = mat6 y) (hcan : canon6 c = true)
    (hy : IsConj (CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH 0) y) : orbit0.contains c = true := by
  obtain ⟨k, rfl⟩ := exists_orbElt_of_isConj hy
  have h := orbitsOK_parts 0
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hsize, -⟩, hcanon⟩ := h
  have hk : (k : ℕ) < (orbTab 0).size := by rw [hsize]; exact k.2
  have e : c = (orbTab 0).getD k [] :=
    dec6_injective hcan (allCheck_spec hcanon hk) (by rw [hc, mat6_orbElt 0 hk])
  rw [Array.contains_iff_mem, e]
  exact getD_mem hk

theorem contains_orbit0_of_five {y : H6} {c : List ℕ} (hc : dec6 c = mat6 y)
    (hcan : canon6 c = true) (hy : orderOf y = 2) (h5 : 5 ∣ Nat.card (Cen y)) :
    orbit0.contains c = true := by
  obtain ⟨g, rfl⟩ := exists_conj_t0 hy h5
  exact contains_orbit0 hc hcan (isConj_iff.mpr ⟨g, rfl⟩)


theorem cert_parts111 : pairsChk899111 = true ∧ c7Chk899111 = true ∧ witChk899111 = true ∧
    sylChk899111 = true :=
  Certificates.certificate899111

theorem clsPairs_ok {cc : List ℕ × List ℕ} (h : cc ∈ clsPairs) : pairCheck cc = true :=
  List.all_eq_true.mp cert_parts111.1 cc h

section C7

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS (c7Sub c7Sub_eq pairs107 c7_ok107)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

theorem not_five_of_mem_c7 {s : H6} (hs : s ∈ Cen (vecElt zH ![1, 1, 1])) (h2 : orderOf s = 2) :
    ¬ 5 ∣ Nat.card (Cen s) := by
  intro h5
  rw [Cen, ← c7Sub_eq] at hs
  obtain ⟨t, ht, hc, hcan⟩ := exists_code_closure _ pairs107.2 648 c7_ok107 hs
  have h := all_getD cert_parts111.2.1 ht
  rw [mul6_self_eq hc (sq_eq_one_of_orderOf h2), beq_self_eq_true,
    beq_eq_false_iff_ne.mpr (ne_one6 hc (ne_one_of_orderOf h2 (by norm_num))),
    contains_orbit0_of_five hc hcan h2 h5] at h
  exact absurd h (by decide)

theorem h6_not648 {s g : H6} (hs : orderOf s = 2) (h5 : 5 ∣ Nat.card (Cen s))
    (hgs : g * s = s * g) (hg : orderOf g = 3) : Nat.card (Cen g) ≠ 648 := by
  intro h648
  obtain ⟨j, hj, m, rfl⟩ := exists_card_rep3 hg
  have hj2 : j = 2 := cOrd3_injective (hj.symm.trans h648)
  subst hj2
  refine not_five_of_mem_c7 (s := m⁻¹ * s * m) ?_ ?_ ?_
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have e := (conj_comm_iff m (m⁻¹ * s * m) (rep3 2)).mp
    have hh : m * (m⁻¹ * s * m) * m⁻¹ = s := by group
    rw [hh] at e
    exact e hgs.symm
  · have e := orderOf_conj m⁻¹ s
    rwa [inv_inv, hs] at e
  · have e := card_centralizer_conj s m⁻¹
    rw [inv_inv] at e
    rwa [Cen, e]

end C7

noncomputable def gamE (i : Fin 4) : H6 :=
  ofCode (gamP i) (clsPairs_ok (by fin_cases i <;> simp [gamP, clsPairs]))

theorem kPair_ok (i : Fin 4) : pairCheck (kC i, kC i) = true :=
  clsPairs_ok (by fin_cases i <;> simp [kC, clsPairs])

noncomputable def kE (i : Fin 4) : H6 :=
  ofCode (kC i, kC i) (kPair_ok i)

noncomputable def repE (i : Fin 4) : H6 := ![zH 1, zH 1, zH 1, zH 0 * zH 1] i

noncomputable def gamW (i : Fin 4) : H6 := gamE i * repE i * (gamE i)⁻¹

theorem mat6_repE (i : Fin 4) : mat6 (repE i) = dec6 (repC i) := by
  fin_cases i
  · exact mat6_zH 1
  · exact mat6_zH 1
  · exact mat6_zH 1
  · show mat6 (zH 0 * zH 1) = dec6 (mul6 (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.zCode 0)
      (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.zCode 1))
    rw [map_mul, mat6_zH, mat6_zH, dec6_mul6]

theorem mat6_gamW (i : Fin 4) : mat6 (gamW i) = dec6 (gamC i) := by
  rw [gamW, map_mul, map_mul, gamE, mat6_ofCode, mat6_ofCode_inv, mat6_repE, gamC, dec6_mul6,
    dec6_mul6]

theorem mat6_kE (i : Fin 4) : mat6 (kE i) = dec6 (kC i) := by
  rw [kE, mat6_ofCode]

theorem mat6_tH_inv (i : Fin 4) : mat6 (CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH i) = dec6 (invC i) := by
  rw [CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH, mat6_ofCode]
  fin_cases i <;> rfl

theorem wit_spec (i : Fin 4) :
    commutes6 (gamC i) (invC i) = true ∧ commutes6 (kC i) (invC i) = true ∧
      mul6 (kC i) (kC i) = one6 ∧ kC i ≠ one6 ∧
      mul6 (mul6 (kC i) (gamC i)) (kC i) = mul6 (gamC i) (gamC i) := by
  have h := cert_parts111.2.2.1
  simp only [witChk899111, List.all_eq_true] at h
  have hi := h i (List.mem_finRange i)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hi
  exact ⟨hi.1.1.1.1, hi.1.1.1.2, hi.1.1.2, hi.1.2, hi.2⟩

section Witness

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH_pow_three zH_comm aElt aVec wreathFacts_zH)

theorem repE_pow_three (i : Fin 4) : repE i ^ 3 = 1 := by
  fin_cases i
  · exact zH_pow_three 1
  · exact zH_pow_three 1
  · exact zH_pow_three 1
  · show (zH 0 * zH 1) ^ 3 = 1
    rw [(show Commute (zH 0) (zH 1) from zH_comm 0 1).mul_pow, zH_pow_three, zH_pow_three,
      one_mul]

theorem repE_ne_one (i : Fin 4) : repE i ≠ 1 := by
  have h : ∀ j, aVec j ≠ 0 → aElt j ≠ 1 := fun j hj e => hj (wreathFacts_zH.inj _ e)
  fin_cases i
  · show zH 1 ≠ 1
    rw [← aElt1]; exact h 1 (by decide)
  · show zH 1 ≠ 1
    rw [← aElt1]; exact h 1 (by decide)
  · show zH 1 ≠ 1
    rw [← aElt1]; exact h 1 (by decide)
  · show zH 0 * zH 1 ≠ 1
    rw [← aElt3]; exact h 3 (by decide)

theorem orderOf_repE (i : Fin 4) : orderOf (repE i) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (repE_pow_three i) (repE_ne_one i)

end Witness

theorem card_cen_repE (i : Fin 4) :
    Nat.card (Cen (repE i)) = 108 ∨ Nat.card (Cen (repE i)) = 2160 := by
  fin_cases i
  · exact Or.inr (card_cen_rep3 0)
  · exact Or.inr (card_cen_rep3 0)
  · exact Or.inr (card_cen_rep3 0)
  · exact Or.inl (card_cen_rep3 1)

theorem wit_tH (i : Fin 4) :
    gamW i * CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH i = CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH i * gamW i ∧ orderOf (gamW i) = 3 ∧
      (Nat.card (Cen (gamW i)) = 108 ∨ Nat.card (Cen (gamW i)) = 2160) ∧
      kE i * CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH i = CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH i * kE i ∧ orderOf (kE i) = 2 ∧
      kE i * gamW i * (kE i)⁻¹ = (gamW i)⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := wit_spec i
  have hk2 : kE i * kE i = 1 := mat6_injective (by
    rw [map_mul, mat6_kE, ← dec6_mul6, h3, dec6_one6, map_one])
  have hk1 : kE i ≠ 1 := fun e => h4 (dec6_injective (pairCheck_spec (kPair_ok i)).1
    canon6_one6 (by rw [← mat6_kE, e, map_one, dec6_one6]))
  have hγ3 : orderOf (gamW i) = 3 := by rw [gamW, orderOf_conj, orderOf_repE]
  refine ⟨commute_of_commutes6 (mat6_gamW i) (mat6_tH_inv i) h1, hγ3, ?_,
    commute_of_commutes6 (mat6_kE i) (mat6_tH_inv i) h2, ?_, ?_⟩
  · rw [gamW, Cen, card_centralizer_conj, ← Cen]
    exact card_cen_repE i
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hk2) hk1
  · have hkγ : kE i * gamW i * kE i = gamW i * gamW i := mat6_injective (by
      rw [map_mul, map_mul, map_mul, mat6_kE, mat6_gamW, ← dec6_mul6, ← dec6_mul6,
        ← dec6_mul6, h5])
    have hkinv : (kE i)⁻¹ = kE i := inv_eq_of_mul_eq_one_right hk2
    have hγ : gamW i ^ 3 = 1 := by
      have e := pow_orderOf_eq_one (gamW i)
      rwa [hγ3] at e
    rw [hkinv, hkγ, eq_inv_iff_mul_eq_one, ← pow_three']
    exact hγ

theorem h6_wit {τ : H6} (hτ : orderOf τ = 2) :
    ∃ γ : H6, γ * τ = τ * γ ∧ orderOf γ = 3 ∧
      (Nat.card (Cen γ) = 108 ∨ Nat.card (Cen γ) = 2160) ∧
      ∃ k : H6, k * τ = τ * k ∧ orderOf k = 2 ∧ k * γ * k⁻¹ = γ⁻¹ := by
  obtain ⟨i, g, rfl⟩ := exists_conj_tH hτ
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := wit_tH i
  refine ⟨g * gamW i * g⁻¹, (conj_comm_iff _ _ _).mpr c1, by rw [orderOf_conj, c2], ?_,
    g * kE i * g⁻¹, (conj_comm_iff _ _ _).mpr c4, by rw [orderOf_conj, c5], ?_⟩
  · rw [Cen, card_centralizer_conj, ← Cen]; exact c3
  · calc g * kE i * g⁻¹ * (g * gamW i * g⁻¹) * (g * kE i * g⁻¹)⁻¹
        = g * (kE i * gamW i * (kE i)⁻¹) * g⁻¹ := by group
      _ = (g * gamW i * g⁻¹)⁻¹ := by rw [c6]; group

noncomputable def hE : H6 := ofCode (hCode, hInv) (clsPairs_ok (by simp [clsPairs]))

noncomputable def t0p : H6 := hE⁻¹ * CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH 0 * hE

theorem mat6_t0p : mat6 t0p = dec6 t0pC := by
  rw [t0p, map_mul, map_mul, hE, mat6_ofCode, mat6_ofCode_inv, mat6_tH_inv, t0pC, dec6_mul6,
    dec6_mul6]
  rfl

theorem syl_spec111 : sylowP.all (fun p => commutes6 p.1 t0pC) = true ∧
    sylowT.contains t0pC = true ∧
    sylowT.all (fun y => !(sylowP.all fun p => commutes6 y p.1) || !(mul6 y y == one6) ||
      y == one6 || !(orbit0.contains y) || y == t0pC) = true := by
  have h := cert_parts111.2.2.2
  simp only [sylChk899111, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem SH_le_cen_t0p : SH ≤ Cen t0p := by
  rw [SH, Subgroup.closure_le]
  rintro _ ⟨cc, hm, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact commute_of_commutes6 (mat6_ofCode _ _) mat6_t0p
    (List.all_eq_true.mp syl_spec111.1 cc hm)

theorem t0p_mem_SH : t0p ∈ SH :=
  mem_closure_of_mem_table sylowP sylowP_check 512 sylowOK_parts.1
    (Array.mem_of_contains_eq_true syl_spec111.2.1) mat6_t0p

theorem eq_t0p {y : H6} (hy : y ∈ SH) (hc : ∀ z ∈ SH, y * z = z * y) (h2 : orderOf y = 2)
    (h5 : 5 ∣ Nat.card (Cen y)) : y = t0p := by
  obtain ⟨t, ht, hcode, hcan⟩ := exists_code_closure sylowP sylowP_check 512 sylowOK_parts.1 hy
  have h := all_getD syl_spec111.2.2 ht
  have hcomm : (sylowP.all fun p => commutes6 ((closureT (sylowP.map Prod.fst)).getD t []) p.1) =
      true := List.all_eq_true.mpr fun cc hm =>
    commutes6_of_commute hcode.symm (mat6_ofCode _ _) (hc _ (ofCode_mem_closure _ hm))
  rw [hcomm, mul6_self_eq hcode (sq_eq_one_of_orderOf h2), beq_self_eq_true,
    beq_eq_false_iff_ne.mpr (ne_one6 hcode (ne_one_of_orderOf h2 (by norm_num))),
    contains_orbit0_of_five hcode hcan h2 h5] at h
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h
  exact mat6_injective (by rw [← hcode, h, mat6_t0p])

theorem h6_syl {s : H6} (hs : orderOf s = 2) (h5 : 5 ∣ Nat.card (Cen s)) :
    Nat.card (Cen s) = 23040 ∧ ∃ T : Subgroup H6, T ≤ Cen s ∧ Nat.card T = 512 ∧ s ∈ T ∧
      ∀ y ∈ T, (∀ t ∈ T, y * t = t * y) → orderOf y = 2 → 5 ∣ Nat.card (Cen y) → y = s := by
  obtain ⟨g, rfl⟩ := exists_conj_t0 hs h5
  set c := g * hE with hc
  have hs' : c * t0p * c⁻¹ = g * CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.tH 0 * g⁻¹ := by rw [hc, t0p]; group
  refine ⟨by rw [Cen, card_centralizer_conj, ← Cen, card_cen_tH]; rfl,
    SH.map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hs', Subgroup.mem_centralizer_singleton_iff,
      conj_comm_iff]
    exact Subgroup.mem_centralizer_singleton_iff.mp (SH_le_cen_t0p hx)
  · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, card_SH]
  · exact ⟨t0p, t0p_mem_SH, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs']⟩
  · rintro _ ⟨y, hy, rfl⟩ hcent hy2 hy5
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcent hy2 hy5 ⊢
    rw [orderOf_conj] at hy2
    rw [Cen, card_centralizer_conj, ← Cen] at hy5
    rw [← hs', eq_t0p hy (fun z hz => (conj_comm_iff c y z).mp
      (hcent _ ⟨z, hz, rfl⟩)) hy2 hy5]

theorem kf_sp6Cls : KF_Sp6Cls := by
  intro X _ _ M hM
  obtain ⟨θ⟩ := nonempty_mulEquiv_H6_of_stated hM
  set f : H6 →* X := M.subtype.comp θ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.symm.injective
  have hfM : ∀ x, f x ∈ M := fun x => (θ.symm x).2
  have hfL : (⊤ : Subgroup H6).map f = M := by
    ext y
    exact ⟨by rintro ⟨x, -, rfl⟩; exact hfM x,
      fun hy => ⟨θ ⟨y, hy⟩, Subgroup.mem_top _, by simp [hfdef]⟩⟩
  have hpre : ∀ g ∈ M, ∃ x, f x = g := fun g hg => ⟨θ ⟨g, hg⟩, by simp [hfdef]⟩
  have hcard : ∀ x, Nat.card ↥(M ⊓ Cen (f x)) = Nat.card (Cen x) := fun x => by
    rw [← hfL, Sp6Transv.card_map_inf_cen hf, top_inf_eq]
  have hord : ∀ x, orderOf (f x) = orderOf x := fun x => orderOf_injective f hf x
  have hcomm : ∀ x y, f x * f y = f y * f x ↔ x * y = y * x := fun x y =>
    ⟨fun h => hf (by rw [map_mul, map_mul, h]), fun h => by rw [← map_mul, h, map_mul]⟩
  have hmemC : ∀ x y, f x ∈ M ⊓ Cen (f y) ↔ x * y = y * x := fun x y => by
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, hcomm]
    exact ⟨fun h => h.2, fun h => ⟨hfM x, h⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg h3
    obtain ⟨x, rfl⟩ := hpre g hg
    rw [hcard]
    rw [hord] at h3
    exact h6_card3 h3
  · intro g hg g' hg' h3 h3' hc
    obtain ⟨x, rfl⟩ := hpre g hg
    obtain ⟨x', rfl⟩ := hpre g' hg'
    rw [hcard, hcard] at hc
    rw [hord] at h3 h3'
    obtain ⟨m, hm⟩ := h6_conj3 h3 h3' hc
    exact ⟨f m, hfM m, by rw [← map_inv, ← map_mul, ← map_mul, hm]⟩
  · intro s hs h2 h5 g hg h3
    obtain ⟨x, rfl⟩ := hpre s hs
    obtain ⟨y, rfl⟩ := hpre g (Subgroup.mem_inf.mp hg).1
    rw [hcard]
    rw [hord] at h2 h3
    rw [hcard] at h5
    exact h6_not648 h2 h5 ((hmemC y x).mp hg) h3
  · intro τ hτ h2
    obtain ⟨x, rfl⟩ := hpre τ hτ
    rw [hord] at h2
    obtain ⟨γ, hγ, h3, hc, k, hk, hk2, hkγ⟩ := h6_wit h2
    refine ⟨f γ, (hmemC γ x).mpr hγ, by rw [hord, h3], by rw [hcard]; exact hc, f k,
      (hmemC k x).mpr hk, by rw [hord, hk2], ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, hkγ, map_inv]
  · intro s hs h2 h5
    obtain ⟨x, rfl⟩ := hpre s hs
    rw [hord] at h2
    rw [hcard] at h5 ⊢
    obtain ⟨hc, T, hT, hT512, hxT, huniq⟩ := h6_syl h2 h5
    refine ⟨hc, T.map f, ?_, by rw [Subgroup.card_map_of_injective hf, hT512], ⟨x, hxT, rfl⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hmemC y x).mpr (Subgroup.mem_centralizer_singleton_iff.mp (hT hy))
    · rintro _ ⟨y, hy, rfl⟩ hcent hy2 hy5
      rw [hord] at hy2
      rw [hcard] at hy5
      rw [huniq y hy (fun t ht => (hcomm y t).mp (hcent _ ⟨t, ht, rfl⟩)) hy2 hy5]

end Inv

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Cls
