module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34D38Pair
public import CFSG.Quasithin.Background.B5Models

public section

namespace CFSG.Quasithin.RonanD38

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA

section B45

variable {V : Type} [CommGroup V] [Finite V]

theorem binaryNaturalSz_autSec_of_suzuki (hB45 : AsB45)
    (hF : Facts10_1) (hV : ∀ v : V, v ^ 2 = 1) {X K : Subgroup (MulAut V)} {C : Subgroup V}
    (hQ : InternalSec.QSec X K C) (hS : SQTKGroup ↥K) (hsimp : IsSimpleGroup ↥K)
    (hsz : ∃ n, CFSG.Blueprint.SuzukiModel ↥K 2 n) (hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)) :
    ∃ f, BinaryNaturalSz (autSec K ⊤ C) ⊤ ⊥ f := by
  have hb4 := hQ.b4Hyp hV hS
  have hsv : ∀ v : Sec (⊤ : Subgroup V) C, v ^ 2 = 1 := Bridge.sec_sq_eq_one hV ⊤ C
  have hqsec : qhatOf (autSec X ⊤ C) ≤ ((2 : ℚ) : WithTop ℚ) := (hQ.qhatOf_autSec_le hV).trans hq
  let e : ↥K ≃* ↥(autSec K ⊤ C) :=
    B5.secEquiv K (InternalSec.le_stabSub_top K) hQ.stabKC hQ.faithful
  have : IsSimpleGroup ↥(autSec K ⊤ C) := e.symm.isSimpleGroup
  have hsz' : ∃ n, CFSG.Blueprint.SuzukiModel ↥(autSec K ⊤ C) 2 n := by
    obtain ⟨n, hn⟩ := hsz
    exact ⟨n, H13.suzukiModel_congr e.symm hn⟩
  have hsh : IsShapeGroup ↥(autSec K ⊤ C) := Or.inr (Or.inl hsz')
  have h3 : ¬ 3 ∣ Nat.card ↥(autSec K ⊤ C) := by
    obtain ⟨n, hn⟩ := hsz'
    exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hn
  rcases hB45 _ hsv _ _ hb4 hqsec with ⟨-, ⟨A, hA'⟩, hall⟩ | ⟨-, ht⟩ | h3'
  · exfalso
    rcases b42_of_isShapeGroup hF hsv hb4 hA' (hall A hA') hsh with ⟨m, -, hn⟩ | hn3 | halt
    · exact h3 (H13.three_dvd_card_of_binaryNaturalSL_two hn)
    · exact h3 (H13.three_dvd_card_of_binaryNaturalSL_three hn3)
    · exact h3 (H13.three_dvd_card_of_alternatingNatural_five halt)
  · rcases table_of_isShapeGroup hF hb4 ht hsh with ⟨m, -, horth⟩ | hszf
    · exact (h3 (H13.three_dvd_card_of_binaryOrthogonalFour horth)).elim
    · exact hszf
  · exact (not_part3_of_isShapeGroup hF h3' hsh).elim

end B45

section Degree

private theorem sz_order_lt {x y : ℕ} (hx : 2 ≤ x) (hxy : x < y) :
    x ^ 2 * (x - 1) * (x ^ 2 + 1) < y ^ 2 * (y - 1) * (y ^ 2 + 1) := by
  have h1 : x ^ 2 < y ^ 2 := Nat.pow_lt_pow_left hxy two_ne_zero
  have h2 : x - 1 < y - 1 := by omega
  have h3 : x ^ 2 + 1 < y ^ 2 + 1 := by omega
  exact mul_lt_mul'' (mul_lt_mul'' h1 h2 (Nat.zero_le _) (Nat.zero_le _)) h3 (Nat.zero_le _)
    (Nat.zero_le _)

theorem eq_of_binaryNaturalSz_of_suzukiModel {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} {f n : ℕ} (h : BinaryNaturalSz H ⊤ ⊥ f)
    (hn : CFSG.Blueprint.SuzukiModel ↥H 2 n) : f = n := by
  obtain ⟨a, K, _, _, -, hfa, hK, ⟨e⟩⟩ := BinaryNaturalSz.exists_equiv h
  obtain ⟨-, b, -, K', _, _, hnb, hK', ⟨e'⟩⟩ := hn
  have hc1 := CFSG.LieType.Ree.suzuki_order (a := a) (K := K) (by rw [hK, hfa])
  have hc2 := CFSG.LieType.Ree.suzuki_order (a := b) (K := K') (by rw [hK', hnb])
  have hcard : Nat.card ↥(CFSG.Blueprint.suzukiGroup a K) =
      Nat.card ↥(CFSG.Blueprint.suzukiGroup b K') :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_congr e'.toEquiv)
  rw [hc1, hc2] at hcard
  have hx : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
  have hy : 2 ≤ 2 ^ (2 * b + 1) := Nat.le_self_pow (by omega) 2
  have hq : 2 ^ (2 * a + 1) = 2 ^ (2 * b + 1) := by
    rcases lt_trichotomy (2 ^ (2 * a + 1)) (2 ^ (2 * b + 1)) with hlt | heq | hgt
    · exact absurd hcard (sz_order_lt hx hlt).ne
    · exact heq
    · exact absurd hcard (sz_order_lt hy hgt).ne'
  have := Nat.pow_right_injective (le_refl 2) hq
  omega

theorem card_eq_of_binaryNaturalSz {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {f : ℕ} (hZU : Z ≤ U) (h : BinaryNaturalSz L U Z f) :
    Nat.card ↥U = Nat.card ↥Z * 2 ^ (4 * f) := by
  obtain ⟨a, -, -, K, _, _, hK, π, hπ⟩ := h
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hβk u
  have hQ : Nat.card (↥(FFModel.nat (CFSG.Blueprint.suzukiGroup a K)).sec ⧸
      (FFModel.nat (CFSG.Blueprint.suzukiGroup a K)).ker.subgroupOf
        (FFModel.nat (CFSG.Blueprint.suzukiGroup a K)).sec) = 2 ^ (4 * f) := by
    show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 4 → K))).subgroupOf ⊤) = 2 ^ (4 * f)
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, hK,
      ← pow_mul, mul_comm]
  have h1 := Subgroup.card_ker_mul_card_range β
  rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top, hker, hQ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv] at h1
  exact h1.symm

theorem three_add_rk_le_of_binaryNaturalSz {W : Type*} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {f : ℕ} (hZU : Z ≤ U)
    (h : BinaryNaturalSz L U Z f) : 3 + rk ↥Z ≤ rk ↥U := by
  have hf : 3 ≤ f := by
    obtain ⟨a, ha, hfa, -⟩ := h
    omega
  have hc := card_eq_of_binaryNaturalSz hZU h
  have : rk ↥U = rk ↥Z + 4 * f := by
    unfold rk
    rw [hc, padicValNat.mul Nat.card_pos.ne' (by positivity), padicValNat.prime_pow]
  omega

end Degree

section Transport

variable {W : Type} [CommGroup W]

theorem binaryNaturalSz_of_qsec {L : Subgroup (MulAut W)} {V Z : Subgroup W}
    (hLV : L ≤ stabSub V) (hLZ : L ≤ stabSub Z) (hZV : Z ≤ V) (hfaith : L ⊓ centSub V = ⊥)
    {Y : Subgroup (MulAut ↥V)} (hQ : InternalSec.QSec Y (autSub L V) (Z.subgroupOf V)) {f : ℕ}
    (h : BinaryNaturalSz (autSec (autSub L V) ⊤ (Z.subgroupOf V)) ⊤ ⊥ f) :
    BinaryNaturalSz L V Z f := by
  obtain ⟨a, ha, hfa, K, hK, hf, hc, hr⟩ := h
  exact binaryNaturalSz_of_autSub hLV hLZ hZV hfaith ⟨a, ha, hfa, K, hK, hf, hc,
    B5.realizes_of_autSec le_top (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful hr⟩

end Transport

end CFSG.Quasithin.RonanD38
