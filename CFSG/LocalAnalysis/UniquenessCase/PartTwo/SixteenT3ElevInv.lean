module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase11
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {T : Type} [CommGroup T] [Finite T]

theorem s16t_elev_fix_block (hT : ∀ v : T, v ^ 2 = 1) {Y : Subgroup T} (hY : Nat.card Y = 8)
    {L : Subgroup (MulAut T)} (hL : L ≤ stabSub Y) (hL7 : Nat.card (autSub L Y) = 7)
    {t : MulAut T} (ht : t ∈ stabSub Y) (ht2 : t ^ 2 = 1)
    (hNL : L.map (MulAut.conj t).toMonoidHom = L) : ∀ y ∈ Y, t y = y := by
  have hN : Subgroup.zpowers t ≤ stabSub Y := Subgroup.zpowers_le.2 ht
  have htn : t ∈ normalizer (L : Set (MulAut T)) := Subgroup.mem_normalizer_iff_map_conj_eq.2 hNL
  have hNL' : ∀ n ∈ Subgroup.zpowers t, L.map (MulAut.conj n).toMonoidHom = L := fun n hn =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 ((Subgroup.zpowers_le.2 htn) hn)
  have h21 := s16e_d3_card_autSub_dvd hT hY hN hL hNL' hL7
  have h2 : Nat.card (autSub (Subgroup.zpowers t) Y) ∣ 2 := by
    have hd : Nat.card (autSub (Subgroup.zpowers t) Y) ∣ Nat.card (Subgroup.zpowers t) :=
      Dvd.intro _ (card_autSub_mul hN)
    rw [Nat.card_zpowers] at hd
    exact hd.trans (orderOf_dvd_of_pow_eq_one ht2)
  have h1 : Nat.card (autSub (Subgroup.zpowers t) Y) = 1 :=
    Nat.dvd_one.1 (by simpa using Nat.dvd_gcd h21 h2)
  intro y hy
  have hmem : resHom Y ⟨t, ht⟩ ∈ autSub (Subgroup.zpowers t) Y :=
    mem_autSub.2 ⟨⟨t, ht⟩, Subgroup.mem_zpowers t, rfl⟩
  rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot] at hmem
  have h3 := congrArg (fun φ : MulAut ↥Y => ((φ ⟨y, hy⟩ : ↥Y) : T)) hmem
  simpa [resHom_apply] using h3

theorem s16t_elev_card_autSub {Y : Subgroup T} {A : Subgroup (MulAut T)} (hA : A ≤ stabSub Y)
    (hfaith : ∀ a ∈ A, (∀ y ∈ Y, a y = y) → a = 1) : Nat.card (autSub A Y) = Nat.card A := by
  have h := card_autSub_mul hA
  have hbot : A ⊓ centSub Y = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haA, hac⟩
    exact Subgroup.mem_bot.2 (hfaith a haA (mem_centSub.1 hac))
  rw [hbot, Subgroup.card_bot, mul_one] at h
  exact h

theorem s16t_elev_le_stabSub_commSub (A : Subgroup (MulAut T)) : A ≤ stabSub (commSub ⊤ A) := by
  intro a ha
  have hn : A.map (MulAut.conj a).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer ha)
  apply s16n9b_mem_stabSub_of_map_eq
  rw [← s15_Infra_commSub_top_map_conj A a, hn]

theorem s16t_elev_eq_one_of_normalizes (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3) (hA7 : Nat.card A = 7)
    {t : MulAut T} (htM : t ∈ M) (ht2 : t ^ 2 = 1)
    (hA : A.map (MulAut.conj t).toMonoidHom = A) : t = 1 := by
  have hW8 : Nat.card (commSub ⊤ A) = 8 := by
    rw [card_eq_two_pow hT (commSub ⊤ A), hrk]
    norm_num
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ A).map g.toMonoidHom :=
    s15_Infra_commSub_top_map_conj A g
  have hW8' : Nat.card ((commSub ⊤ A).map g.toMonoidHom) = 8 := by
    rw [card_eq_two_pow hT _, s16n9b_rk_map, hrk]
    norm_num
  have hB := s16n9b_two_normalizes_conj h htM hA
  have hstW : t ∈ stabSub (commSub ⊤ A) :=
    s16n9b_mem_stabSub_of_map_eq (by rw [← s15_Infra_commSub_top_map_conj A t, hA])
  have hstW' : t ∈ stabSub ((commSub ⊤ A).map g.toMonoidHom) :=
    s16n9b_mem_stabSub_of_map_eq (by rw [← hgB, ← s15_Infra_commSub_top_map_conj _ t, hB])
  have hAW : A ≤ stabSub (commSub ⊤ A) := s16t_elev_le_stabSub_commSub A
  have hBW' : A.map (MulAut.conj g).toMonoidHom ≤ stabSub ((commSub ⊤ A).map g.toMonoidHom) := by
    rw [← hgB]
    exact s16t_elev_le_stabSub_commSub _
  have hcard7 : Nat.card (A.map (MulAut.conj g).toMonoidHom) = 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA7]
  have hallfix : ∀ a : MulAut T, (∀ y ∈ commSub ⊤ A, a y = y) →
      (∀ y ∈ (commSub ⊤ A).map g.toMonoidHom, a y = y) → a = 1 := by
    intro a h1 h2
    apply MulEquiv.ext
    intro x
    have hx : x ∈ commSub ⊤ A ⊔ (commSub ⊤ A).map g.toMonoidHom := by
      rw [h.sup]
      exact Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    rw [map_mul, h1 y hy, h2 z hz]
    rfl
  have hfixW : ∀ y ∈ commSub ⊤ A, t y = y := by
    refine s16t_elev_fix_block hT hW8 hAW ?_ hstW ht2 hA
    rw [s16t_elev_card_autSub hAW fun a ha hfix => hallfix a hfix (h.fixA a ha), hA7]
  have hfixW' : ∀ y ∈ (commSub ⊤ A).map g.toMonoidHom, t y = y := by
    refine s16t_elev_fix_block hT hW8' hBW' ?_ hstW' ht2 hB
    rw [s16t_elev_card_autSub hBW' fun a ha hfix => hallfix a (h.fixB a ha) hfix, hcard7]
  exact hallfix t hfixW hfixW'

theorem s16t_elev_map_conj_eq_of_ne_one (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3) (hA7 : Nat.card A = 7)
    {t : MulAut T} (htM : t ∈ M) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    A.map (MulAut.conj t).toMonoidHom = A.map (MulAut.conj g).toMonoidHom :=
  (h.conj t htM).resolve_left fun hA =>
    ht1 (s16t_elev_eq_one_of_normalizes hT h hrk hA7 htM ht2 hA)

theorem s16t_elev_three_le_rkIdx_fixV (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3) (hA7 : Nat.card A = 7)
    {t : MulAut T} (htM : t ∈ M) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    3 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hB := s16t_elev_map_conj_eq_of_ne_one hT h hrk hA7 htM ht2 ht1
  have hgB : commSub ⊤ (A.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ A).map g.toMonoidHom :=
    s15_Infra_commSub_top_map_conj A g
  have hWt : (commSub ⊤ A).map t.toMonoidHom = (commSub ⊤ A).map g.toMonoidHom := by
    rw [← s15_Infra_commSub_top_map_conj A t, hB, hgB]
  have hinj : ∀ w ∈ commSub ⊤ A, t w = w → w = 1 := by
    intro w hw hfix
    have h1 : t w ∈ (commSub ⊤ A).map g.toMonoidHom := by
      rw [← hWt]
      exact Subgroup.mem_map.2 ⟨w, hw, rfl⟩
    rw [hfix] at h1
    have h2 : w ∈ commSub ⊤ A ⊓ (commSub ⊤ A).map g.toMonoidHom := ⟨hw, h1⟩
    rw [h.inf] at h2
    exact Subgroup.mem_bot.1 h2
  have := s16n9b_rk_le_commV hinj
  rw [rkIdx_fixV_zpowers t]
  omega

theorem s16t_elev_three_le_mParam (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3) (hA7 : Nat.card A = 7) :
    3 ≤ E3.mParam M := by
  haveI : Finite (MulAut T) := MulEquiv.finite_left
  unfold E3.mParam
  split_ifs with hev
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 2 (even_iff_two_dvd.mp hev)
    refine le_csInf ⟨_, (t : MulAut T), t.2, (Subgroup.orderOf_coe t).trans ht, rfl⟩ ?_
    rintro _ ⟨s, hsM, hs2, rfl⟩
    have hs2' : s ^ 2 = 1 := by
      rw [← hs2]
      exact pow_orderOf_eq_one s
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hs2
      omega
    exact s16t_elev_three_le_rkIdx_fixV hT h hrk hA7 hsM hs2' hs1
  · have := rk_mono (le_top : commSub ⊤ A ≤ ⊤)
    rw [rk_top] at this
    omega

theorem s16t_elev_card_le_two (hT : ∀ v : T, v ^ 2 = 1) {M A : Subgroup (MulAut T)}
    {g : MulAut T} (h : S16n9bTwo M A g) (hrk : rk ↥(commSub ⊤ A) = 3) (hA7 : Nat.card A = 7)
    {B : Subgroup (MulAut T)} (hBM : B ≤ M) (hB2 : IsElemAbelian2 B) : Nat.card B ≤ 2 := by
  haveI : Finite (MulAut T) := MulEquiv.finite_left
  have hkey : ∀ x y : ↥B, x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy
    have hx1 : (x : MulAut T) ≠ 1 := fun h1 => hx (Subtype.ext h1)
    have hy1 : (y : MulAut T) ≠ 1 := fun h1 => hy (Subtype.ext h1)
    have e1 := s16t_elev_map_conj_eq_of_ne_one hT h hrk hA7 (hBM x.2) (hB2.2 _ x.2) hx1
    have e2 := s16t_elev_map_conj_eq_of_ne_one hT h hrk hA7 (hBM y.2) (hB2.2 _ y.2) hy1
    have hA : A.map (MulAut.conj ((y : MulAut T)⁻¹ * x)).toMonoidHom = A := by
      rw [← s16n9b_map_conj_map_conj A x (y : MulAut T)⁻¹, e1, ← e2, s16n9b_map_conj_map_conj,
        inv_mul_cancel, s16n9b_map_conj_one]
    have hmem : (y : MulAut T)⁻¹ * x ∈ B := B.mul_mem (B.inv_mem y.2) x.2
    have h1 := s16t_elev_eq_one_of_normalizes hT h hrk hA7 (hBM hmem) (hB2.2 _ hmem) hA
    exact Subtype.ext (inv_mul_eq_one.1 h1).symm
  by_contra hlt
  push Not at hlt
  haveI := Fintype.ofFinite ↥B
  rw [Nat.card_eq_fintype_card] at hlt
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 hlt
  by_cases ha : a = 1
  · exact hbc (hkey b c (fun h1 => hab (ha.trans h1.symm)) (fun h1 => hac (ha.trans h1.symm)))
  · by_cases hb : b = 1
    · exact hac (hkey a c ha (fun h1 => hbc (hb.trans h1.symm)))
    · exact hab (hkey a b ha hb)

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
