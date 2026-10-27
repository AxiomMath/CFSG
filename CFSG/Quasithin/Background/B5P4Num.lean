module

public import CFSG.Quasithin.Background.B5NonA
public import CFSG.Quasithin.Background.B5Bot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

namespace B5

section General

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_isFFStarMin_ffLe {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    ∃ B, IsFFStarMin X B ∧ FFLe X B A := by
  classical
  let S : Set (Subgroup (MulAut V)) := {B | FFLe X B A}
  have hSne : S.Nonempty := ⟨A, hA.isA2, hA.isA2, le_rfl, rfl⟩
  obtain ⟨B, hB, hmin⟩ := Set.exists_min_image S (fun B => Nat.card B) (Set.toFinite S) hSne
  have hBP : IsFFStarOffender X B := B1_4_2 hA hB
  refine ⟨B, ⟨hBP, fun B' hB' hB'B => ?_⟩, hB⟩
  have hB'A : FFLe X B' A :=
    ⟨hB'B.1, hA.isA2, hB'B.2.2.1.trans hB.2.2.1, hB'B.2.2.2.trans hB.2.2.2⟩
  have hcard : Nat.card B ≤ Nat.card B' := hmin B' hB'A
  exact Subgroup.eq_of_le_of_card_ge hB'B.2.2.1 hcard

theorem rAV_le_of_ffLe (hV : ∀ v : V, v ^ 2 = 1) {X A B : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hBA : FFLe X B A) : rAV B ≤ rAV A := by
  obtain ⟨hB2, -, hBle, hcard⟩ := hBA
  have hbpos : 0 < rk B := hB2.rk_pos
  have hapos : 0 < rk A := (hA.isA2).rk_pos
  have hba : rk B ≤ rk A := rk_mono hBle
  have hxa : rkIdx (fixV A) ≤ rk A := rkIdx_fixV_le_rk hV hA
  have hBp : Nat.card B = 2 ^ rk B := card_eq_two_pow_of_isPGroup hB2.2.2.isPGroup
  have hAp : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA.2.2.1.isPGroup
  have hBf : Nat.card (fixV B) = 2 ^ rk (fixV B) := card_eq_two_pow hV _
  have hAf : Nat.card (fixV A) = 2 ^ rk (fixV A) := card_eq_two_pow hV _
  rw [hBp, hAp, hBf, hAf, ← pow_add, ← pow_add] at hcard
  have hrk : rk B + rk (fixV B) = rk A + rk (fixV A) := Nat.pow_right_injective (le_refl 2) hcard
  have h1 := rk_add_rkIdx (fixV A)
  have h2 := rk_add_rkIdx (fixV B)
  unfold rAV
  rw [div_le_div_iff₀ (by exact_mod_cast hbpos) (by exact_mod_cast hapos)]
  have hx : rkIdx (fixV B) + rk A = rkIdx (fixV A) + rk B := by omega
  have : ((rkIdx (fixV B) : ℚ) + rk A) = rkIdx (fixV A) + rk B := by exact_mod_cast hx
  have hba' : (rk B : ℚ) ≤ rk A := by exact_mod_cast hba
  have hxa' : (rkIdx (fixV A) : ℚ) ≤ rk A := by exact_mod_cast hxa
  nlinarith [mul_nonneg (sub_nonneg.2 hba') (sub_nonneg.2 hxa')]

theorem qOf_le_rAV_of_offender (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) : qOf X ≤ ((rAV A : ℚ) : WithTop ℚ) := by
  obtain ⟨B, hBmin, hBA⟩ := exists_isFFStarMin_ffLe hA
  have hquad : IsQuadratic B := B1_4_3 hV hBmin
  refine le_trans (qOf_le_iff.2 ⟨B, hBA.1, hquad, le_rfl⟩) ?_
  exact_mod_cast rAV_le_of_ffLe hV hA hBA

end General

section Direct

variable {V : Type} [CommGroup V] [Finite V] {A : Subgroup (MulAut V)} {U W : Subgroup V}

omit [Finite V] in
theorem fixV_eq_sup_of_direct (hD : U ⊔ W = ⊤) (hI : U ⊓ W = ⊥) (hAU : A ≤ stabSub U)
    (hAW : A ≤ stabSub W) : fixV A = (U ⊓ fixV A) ⊔ (W ⊓ fixV A) := by
  refine le_antisymm (fun v hv => ?_) (sup_le inf_le_right inf_le_right)
  have hvt : v ∈ U ⊔ W := by rw [hD]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hvt
  have key : ∀ a ∈ A, a y = y ∧ a z = z := by
    intro a ha
    have h1 : a (y * z) = y * z := hv a ha
    rw [map_mul] at h1
    have hay : a y ∈ U := (hAU ha y).2 hy
    have haz : a z ∈ W := (hAW ha z).2 hz
    have h2 : a y / y = z / a z := by
      rw [div_eq_div_iff_mul_eq_mul, h1, mul_comm]
    have h3 : a y / y ∈ U ⊓ W := ⟨U.div_mem hay hy, h2 ▸ W.div_mem hz haz⟩
    rw [hI, Subgroup.mem_bot, div_eq_one] at h3
    refine ⟨h3, ?_⟩
    rw [h3] at h1
    exact mul_left_cancel h1
  exact Subgroup.mul_mem_sup ⟨hy, fun a ha => (key a ha).1⟩ ⟨hz, fun a ha => (key a ha).2⟩

theorem rk_fixV_of_direct (hD : U ⊔ W = ⊤) (hI : U ⊓ W = ⊥) (hAU : A ≤ stabSub U)
    (hAW : A ≤ stabSub W) : rk ↥(fixV A) = rk ↥(U ⊓ fixV A) + rk ↥(W ⊓ fixV A) := by
  have h := rk_sup_add_rk_inf (U ⊓ fixV A) (W ⊓ fixV A)
  have hbot : (U ⊓ fixV A) ⊓ (W ⊓ fixV A) = ⊥ := by
    rw [eq_bot_iff, ← hI]
    exact inf_le_inf inf_le_left inf_le_left
  rw [hbot, rk_bot, add_zero, ← fixV_eq_sup_of_direct hD hI hAU hAW] at h
  exact h

theorem rk_eq_of_direct (hD : U ⊔ W = ⊤) (hI : U ⊓ W = ⊥) : rk V = rk U + rk W := by
  have h := rk_sup_add_rk_inf U W
  rw [hD, hI, rk_bot, add_zero, rk_top] at h
  exact h

theorem rk_sec_bot' (W : Subgroup V) : rk (Sec W ⊥) = rk W := by
  have h := rk_sec_add (bot_le : (⊥ : Subgroup V) ≤ W)
  rw [rk_bot, add_zero] at h
  exact h

theorem rkIdx_autSec_bot (hAW : A ≤ stabSub W) :
    rkIdx (fixV (autSec A W ⊥)) = rk W - rk ↥(W ⊓ fixV A) := by
  have h1 := rk_add_rkIdx (fixV (autSec A W ⊥))
  have h2 : rk ↥(fixV (autSec A W ⊥)) = rk ↥(W ⊓ fixV A) := by
    unfold rk
    rw [card_fixV_autSec_bot hAW]
  rw [h2, rk_sec_bot'] at h1
  omega

theorem rkIdx_split (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) (hD : U ⊔ W = ⊤) (hI : U ⊓ W = ⊥) (hAU : A ≤ stabSub U)
    (hAW : A ≤ stabSub W) :
    (rk U - rk ↥(U ⊓ fixV A)) + (rk W - rk ↥(W ⊓ fixV A)) ≤ rk A := by
  have h1 := rkIdx_fixV_le_rk hV hA
  have h2 := rk_add_rkIdx (fixV A)
  have h3 := rk_fixV_of_direct hD hI hAU hAW
  have h4 := rk_eq_of_direct hD hI
  have h5 : rk ↥(U ⊓ fixV A) ≤ rk U := rk_mono inf_le_left
  have h6 : rk ↥(W ⊓ fixV A) ≤ rk W := rk_mono inf_le_left
  omega

end Direct

section Sym

variable {Ω : Type*} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem index_commutator_dvd_two {M : Subgroup Ω} (n : ℕ) (hn : 5 ≤ n)
    (π : Equiv.Perm (Fin n) →* ↥M) (hπ : Function.Surjective π) :
    (⁅M, M⁆.subgroupOf M).index ∣ 2 := by
  have h1 : ⁅M, M⁆.subgroupOf M = commutator ↥M := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  have h2 : commutator ↥M = (commutator (Equiv.Perm (Fin n))).map π := by
    rw [commutator, commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ]
  rw [h1, h2]
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h3 := Subgroup.index_map_dvd (commutator (Equiv.Perm (Fin n))) hπ
  have h4 : (commutator (Equiv.Perm (Fin n))).index = 2 := by
    rw [alternatingGroup.commutator_perm_eq (by simpa using hn)]
    exact alternatingGroup.index_eq_two
  rwa [h4] at h3

theorem sup_eq_of_index_dvd_two {M L A : Subgroup Ω} (hLM : L ≤ M) (hAM : A ≤ M)
    (hidx : (L.subgroupOf M).index ∣ 2) (hAL : ¬ A ≤ L) : L ⊔ A = M := by
  have hK : L ⊔ A ≤ M := sup_le hLM hAM
  have hLK : L ≤ L ⊔ A := le_sup_left
  have hcardM : Nat.card ↥M = (L.subgroupOf M).index * Nat.card ↥L := by
    rw [← (L.subgroupOf M).index_mul_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hLK
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hK
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    have hEq : L = L ⊔ A := Subgroup.eq_of_le_of_card_ge hLK hk.le
    exact hAL (hEq ▸ le_sup_right)
  have hkm : (L.subgroupOf M).index = k * m := by
    have : Nat.card ↥L * (L.subgroupOf M).index = Nat.card ↥L * (k * m) := by
      rw [mul_comm, ← hcardM, hm, hk]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hk2 : k = 2 := by
    rw [hkm] at hidx
    have hkd : k ∣ 2 := (Dvd.intro m rfl).trans hidx
    rcases (Nat.dvd_prime Nat.prime_two).1 hkd with h | h
    · exact absurd h hk1
    · exact h
  have hm1 : m = 1 := by
    have h2 : (L.subgroupOf M).index ∣ 2 := hidx
    rw [hkm, hk2] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hkm
        have := (L.subgroupOf M).index_ne_zero_of_finite
        exact absurd hkm this
      · exact h0
    omega
  have hcard : Nat.card ↥M ≤ Nat.card ↥(L ⊔ A) := by
    rw [hm, hm1, mul_one]
  exact Subgroup.eq_of_le_of_card_ge hK hcard

theorem rk_le_of_card_dvd {A : Subgroup Ω} (hA : IsPGroup 2 A) {N n : ℕ}
    (hdvd : Nat.card ↥A ∣ n) (h : ¬ 2 ^ (N + 1) ∣ n) : rk A ≤ N := by
  by_contra hlt
  push Not at hlt
  have h1 : Nat.card ↥A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA
  have h2 : 2 ^ (N + 1) ∣ 2 ^ rk A := pow_dvd_pow 2 hlt
  rw [← h1] at h2
  exact h (h2.trans hdvd)

end Sym

theorem card_perm_fin (n : ℕ) : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

end B5

end CFSG.Quasithin
