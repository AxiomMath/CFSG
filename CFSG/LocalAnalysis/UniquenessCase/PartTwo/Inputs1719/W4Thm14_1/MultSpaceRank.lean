module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceCount
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceHomog
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceInvol
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.MultSpaceL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

private theorem rk_of_card_two {H : Subgroup W} (h : Nat.card ↥H = 2) : rk ↥H = 1 := by
  unfold rk
  rw [h, padicValNat_self]

private theorem stableUnder_fixV_zpowers_of_mem_centralizer {L : Subgroup (MulAut W)}
    {b : MulAut W} (hb : b ∈ Subgroup.centralizer (L : Set (MulAut W))) :
    StableUnder L (fixV (Subgroup.zpowers b)) := by
  intro l hl u hu
  rw [mem_fixV] at hu ⊢
  intro x hx
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  have hcomm : l * b = b * l := Subgroup.mem_centralizer_iff.mp hb l hl
  have hcomm' : Commute l b := hcomm
  have hbk : Commute l (b ^ k) := hcomm'.zpow_right k
  calc (b ^ k) (l u) = ((b ^ k) * l) u := rfl
    _ = (l * (b ^ k)) u := by rw [← hbk.eq]
    _ = l ((b ^ k) u) := rfl
    _ = l u := by rw [hu (b ^ k) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)]

private theorem rk_fixV_mul_rk_eq [Finite W] {L : Subgroup (MulAut W)} {J : Subgroup W}
    {T : Subgroup (MulAut W)} (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I) (hTL : T ≤ L)
    (hJ : J ∈ irrSet L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2) :
    rk ↥(fixV T) * rk ↥J = rk W := by
  have hmain := rk_inf_fixV_mul_rk hfix hspan
    (CFSG.LocalAnalysis.WeakClosure81.stableUnder_of_mem_irrSet hJ) hhom hTL (S := ⊤)
    fun _ _ _ _ => Subgroup.mem_top _
  rw [top_inf_eq, rk_top, rk_of_card_two (hT J hJ), one_mul] at hmain
  exact hmain

private theorem rkIdx_fixV_zpowers_eq [Finite W] {L : Subgroup (MulAut W)} {J : Subgroup W}
    {T : Subgroup (MulAut W)} (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I) (hTL : T ≤ L)
    (hJ : J ∈ irrSet L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {a : MulAut W} (ha : a ∈ L) {r s : ℕ} (hr : rk ↥J = r) (hr0 : 0 < r)
    (hs : rk ↥(J ⊓ fixV (Subgroup.zpowers a)) = s) :
    rkIdx (fixV (Subgroup.zpowers a)) + s * rk ↥(fixV T) = r * rk ↥(fixV T) := by
  have hnr := rk_fixV_mul_rk_eq hfix hspan hhom hTL hJ hT
  have hza := rk_inf_fixV_mul_rk hfix hspan
    (CFSG.LocalAnalysis.WeakClosure81.stableUnder_of_mem_irrSet hJ) hhom
    (Subgroup.zpowers_le.mpr ha) (S := ⊤) fun _ _ _ _ => Subgroup.mem_top _
  rw [top_inf_eq, rk_top, hs, hr] at hza
  rw [hr] at hnr
  have hfa : rk ↥(fixV (Subgroup.zpowers a)) = s * rk ↥(fixV T) := by
    apply Nat.eq_of_mul_eq_mul_right hr0
    rw [hza, ← hnr, mul_assoc]
  have hw : r * rk ↥(fixV T) = rk W := by rw [mul_comm]; exact hnr
  have h_add := rk_add_rkIdx (fixV (Subgroup.zpowers a))
  rw [hw, ← hfa]
  omega

private theorem step2_rkIdx_eq_n [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) {J : Subgroup W} {T : Subgroup (MulAut W)}
    (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    (hTL : T ≤ L) (hJ : J ∈ irrSet L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {a : MulAut W} (ha : a ∈ L) (ha2 : orderOf a = 2) (h3 : rk ↥J = 3) :
    rkIdx (fixV (Subgroup.zpowers a)) = rk ↥(fixV T) := by
  rcases rk_inf_fixV_zpowers_of_mem_irrSet hW hL3 hfix hJ ha ha2 with ⟨_, h2⟩ | ⟨h8, _⟩
  · have h := rkIdx_fixV_zpowers_eq hfix hspan hhom hTL hJ hT ha h3 (by norm_num) h2
    omega
  · omega

private theorem step2_rkIdx_eq_four_n [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) {J : Subgroup W} {T : Subgroup (MulAut W)}
    (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    (hTL : T ≤ L) (hJ : J ∈ irrSet L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {a : MulAut W} (ha : a ∈ L) (ha2 : orderOf a = 2) (h8 : rk ↥J = 8) :
    rkIdx (fixV (Subgroup.zpowers a)) = 4 * rk ↥(fixV T) := by
  rcases rk_inf_fixV_zpowers_of_mem_irrSet hW hL3 hfix hJ ha ha2 with ⟨h3, _⟩ | ⟨_, h4⟩
  · omega
  · have h := rkIdx_fixV_zpowers_eq hfix hspan hhom hTL hJ hT ha h8 (by norm_num) h4
    omega

private theorem step3_r_dvd_rkIdx [Finite W]
    {L : Subgroup (MulAut W)} {J : Subgroup W} {T : Subgroup (MulAut W)}
    (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    (hTL : T ≤ L) (hJ : J ∈ irrSet L)
    (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {b : MulAut W} (hb_cent : b ∈ Subgroup.centralizer (L : Set (MulAut W))) :
    rk ↥J ∣ rkIdx (fixV (Subgroup.zpowers b)) := by
  have hS_stab : StableUnder L (fixV (Subgroup.zpowers b)) :=
    stableUnder_fixV_zpowers_of_mem_centralizer hb_cent
  have hJinf : Nat.card ↥(J ⊓ fixV T) = 2 := hT J hJ
  have hrk_inf : rk ↥(J ⊓ fixV T) = 1 := rk_of_card_two hJinf
  have hS_eq : rk ↥((fixV (Subgroup.zpowers b)) ⊓ fixV T) * rk ↥J =
      rk ↥(fixV (Subgroup.zpowers b)) := by
    have hmain := rk_inf_fixV_mul_rk hfix hspan
      (CFSG.LocalAnalysis.WeakClosure81.stableUnder_of_mem_irrSet hJ) hhom hTL hS_stab
    rw [hrk_inf, one_mul] at hmain
    exact hmain
  have hJS : rk ↥J ∣ rk ↥(fixV (Subgroup.zpowers b)) := by
    refine ⟨rk ↥((fixV (Subgroup.zpowers b)) ⊓ fixV T), ?_⟩
    rw [mul_comm]
    exact hS_eq.symm
  have hnr := rk_fixV_mul_rk_eq hfix hspan hhom hTL hJ hT
  have hJW : rk ↥J ∣ rk W := by
    refine ⟨rk ↥(fixV T), ?_⟩
    rw [mul_comm]
    exact hnr.symm
  have hsub : rkIdx (fixV (Subgroup.zpowers b)) =
      rk W - rk ↥(fixV (Subgroup.zpowers b)) := by
    have h := rk_add_rkIdx (fixV (Subgroup.zpowers b))
    omega
  rw [hsub]
  exact Nat.dvd_sub hJW hJS

private theorem step3_pos_rkIdx [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {b : MulAut W} (hb1 : b ≠ 1) :
    0 < rkIdx (fixV (Subgroup.zpowers b)) := by
  have hS_ne_top : fixV (Subgroup.zpowers b) ≠ ⊤ := by
    intro hS
    apply hb1
    apply MulEquiv.ext
    intro w
    have hw : w ∈ fixV (Subgroup.zpowers b) := by rw [hS]; exact Subgroup.mem_top w
    rw [mem_fixV] at hw
    exact hw b (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hP : IsPGroup 2 (⊤ : Subgroup W) := (isPGroup_two_of_sq_eq_one hW).to_subgroup ⊤
  have hmq : CFSG.Quasithin.E3.mQuot (⊤ : Subgroup W) (fixV (Subgroup.zpowers b)) =
      rkIdx (fixV (Subgroup.zpowers b)) := by
    unfold CFSG.Quasithin.E3.mQuot rkIdx
    rw [Subgroup.relIndex_top_right]
  have hne : CFSG.Quasithin.E3.mQuot (⊤ : Subgroup W) (fixV (Subgroup.zpowers b)) ≠ 0 := by
    intro h0
    apply hS_ne_top
    exact (CFSG.Quasithin.E3.mQuot_eq_zero_iff hP le_top).mp h0
  rw [hmq] at hne
  exact Nat.pos_of_ne_zero hne

private theorem step4_rkIdx_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hfix : fixV L = ⊥) (hspan : (⨆ I ∈ irrSet L, I) = ⊤)
    {a b t : MulAut W} (ha : a ∈ L)
    (hb : b ∈ Subgroup.centralizer (L : Set (MulAut W))) (hb2 : b ^ 2 = 1)
    (ht : t = a * b) :
    rkIdx (fixV (Subgroup.zpowers a)) ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have hcard := card_fixV_zpowers_mul_le (W := W) hW hfix hspan (a := a) (b := b) ha hb hb2
  rw [← ht] at hcard
  have hpow_t := card_eq_two_pow hW (fixV (Subgroup.zpowers t))
  have hpow_a := card_eq_two_pow hW (fixV (Subgroup.zpowers a))
  have hrk_le : rk ↥(fixV (Subgroup.zpowers t)) ≤ rk ↥(fixV (Subgroup.zpowers a)) := by
    rw [hpow_t, hpow_a] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  have h_add_t := rk_add_rkIdx (fixV (Subgroup.zpowers t))
  have h_add_a := rk_add_rkIdx (fixV (Subgroup.zpowers a))
  omega

private theorem case_r3 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L M : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) (hM : M = centGroupIn Y L) (hY : Y = L ⊔ M)
    (hfix : fixV L = ⊥) (htr : IrrSpanTrans Y L)
    {T : Subgroup (MulAut W)} (hTL : T ≤ L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {J : Subgroup W} (hJ : J ∈ irrSet L)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    {a : MulAut W} (haL : a ∈ L) (ha2 : orderOf a = 2)
    (h3 : rk ↥J = 3) (h4_le_a : 4 ≤ rkIdx (fixV (Subgroup.zpowers a)))
    {t0 : MulAut W} (ht0Y : t0 ∈ Y) (ht02 : orderOf t0 = 2)
    (ht0rk : rkIdx (fixV (Subgroup.zpowers t0)) = 4) :
    (∀ I ∈ irrSet L, rk ↥I = 3) ∧ Nat.card ↥(fixV T) = 16 := by
  have hspan : (⨆ I ∈ irrSet L, I) = ⊤ := htr.1
  have hIdx_a : rkIdx (fixV (Subgroup.zpowers a)) = rk ↥(fixV T) :=
    step2_rkIdx_eq_n hW hL3 hfix hspan hhom hTL hJ hT haL ha2 h3
  have h4_le_n : 4 ≤ rk ↥(fixV T) := by
    have := h4_le_a
    rwa [hIdx_a] at this
  have ht0_sq : t0 ^ 2 = 1 := (orderOf_eq_prime_iff.mp ht02).1
  obtain ⟨a', ha'L, b', hb'M, ht0_eq, ha'2, hb'2⟩ :=
    exists_mul_of_sq_eq_one hL3 hM hY ht0Y ht0_sq
  have hb'_cent : b' ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [hM] at hb'M
    exact hb'M.2
  have hn_le_four : rk ↥(fixV T) ≤ 4 := by
    by_cases ha'1 : a' = 1
    · have ht0_eq_b' : t0 = b' := by rw [ht0_eq, ha'1, one_mul]
      have hb'1 : b' ≠ 1 := by
        intro hb'1
        rw [ht0_eq_b', hb'1] at ht02
        simp at ht02
      have h3dvd : 3 ∣ rkIdx (fixV (Subgroup.zpowers t0)) := by
        have h := step3_r_dvd_rkIdx hfix hspan hhom hTL hJ hT hb'_cent
        rw [h3] at h
        rwa [← ht0_eq_b'] at h
      rw [ht0rk] at h3dvd
      norm_num at h3dvd
    · have ha'2' : orderOf a' = 2 := orderOf_eq_prime_iff.mpr ⟨ha'2, ha'1⟩
      have hIdx_a' : rkIdx (fixV (Subgroup.zpowers a')) = rk ↥(fixV T) :=
        step2_rkIdx_eq_n hW hL3 hfix hspan hhom hTL hJ hT ha'L ha'2' h3
      have hle : rkIdx (fixV (Subgroup.zpowers a')) ≤ rkIdx (fixV (Subgroup.zpowers t0)) :=
        step4_rkIdx_le hW hfix hspan ha'L hb'_cent hb'2 ht0_eq
      rwa [hIdx_a', ht0rk] at hle
  have hn4 : rk ↥(fixV T) = 4 := by omega
  have hCard16 : Nat.card ↥(fixV T) = 16 := by
    have h := card_eq_two_pow hW (fixV T)
    rw [h, hn4]
    norm_num
  have hAllRank3 : ∀ I ∈ irrSet L, rk ↥I = 3 := by
    intro I hI
    obtain ⟨e, _⟩ := hhom I hI
    have hcard : Nat.card ↥I = Nat.card ↥J := Nat.card_congr e.toEquiv.symm
    calc rk ↥I = rk ↥J := by unfold rk; rw [hcard]
      _ = 3 := h3
  exact ⟨hAllRank3, hCard16⟩

private theorem case_r8 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L M : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) (hM : M = centGroupIn Y L) (hY : Y = L ⊔ M)
    (hfix : fixV L = ⊥) (htr : IrrSpanTrans Y L)
    {T : Subgroup (MulAut W)} (hTL : T ≤ L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2)
    {J : Subgroup W} (hJ : J ∈ irrSet L)
    (hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I)
    (h8 : rk ↥J = 8)
    {t0 : MulAut W} (ht0Y : t0 ∈ Y) (ht02 : orderOf t0 = 2)
    (ht0rk : rkIdx (fixV (Subgroup.zpowers t0)) = 4) :
    Nat.card ↥(fixV T) = 2 := by
  have hspan : (⨆ I ∈ irrSet L, I) = ⊤ := htr.1
  have hn_pos : 0 < rk ↥(fixV T) := by
    have hcard_dvd : Nat.card ↥(J ⊓ fixV T) ∣ Nat.card ↥(fixV T) :=
      Subgroup.card_dvd_of_le (inf_le_right : J ⊓ fixV T ≤ fixV T)
    rw [hT J hJ] at hcard_dvd
    have hcard_ge : 2 ≤ Nat.card ↥(fixV T) := Nat.le_of_dvd (by norm_num) hcard_dvd
    by_contra h0
    have h0' : rk ↥(fixV T) = 0 := Nat.eq_zero_of_not_pos h0
    have hbot : fixV T = ⊥ := (rk_eq_zero_iff hW).mp h0'
    rw [hbot] at hcard_ge
    simp at hcard_ge
  have hn_eq_one : rk ↥(fixV T) = 1 := by
    by_contra hne
    have hn_ge_two : 2 ≤ rk ↥(fixV T) := by omega
    have ht0_sq : t0 ^ 2 = 1 := (orderOf_eq_prime_iff.mp ht02).1
    obtain ⟨a', ha'L, b', hb'M, ht0_eq, ha'2, hb'2⟩ :=
      exists_mul_of_sq_eq_one hL3 hM hY ht0Y ht0_sq
    have hb'_cent : b' ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [hM] at hb'M
      exact hb'M.2
    have ht0_ge_eight : 8 ≤ rkIdx (fixV (Subgroup.zpowers t0)) := by
      by_cases ha'1 : a' = 1
      · have ht0_eq_b' : t0 = b' := by rw [ht0_eq, ha'1, one_mul]
        have hb'1 : b' ≠ 1 := by
          intro hb'1
          rw [ht0_eq_b', hb'1] at ht02
          simp at ht02
        have hpos : 0 < rkIdx (fixV (Subgroup.zpowers t0)) := by
          have h := step3_pos_rkIdx hW hb'1
          rwa [← ht0_eq_b'] at h
        have h8dvd : 8 ∣ rkIdx (fixV (Subgroup.zpowers t0)) := by
          have h := step3_r_dvd_rkIdx hfix hspan hhom hTL hJ hT hb'_cent
          rw [h8] at h
          rwa [← ht0_eq_b'] at h
        exact Nat.le_of_dvd hpos h8dvd
      · have ha'2' : orderOf a' = 2 := orderOf_eq_prime_iff.mpr ⟨ha'2, ha'1⟩
        have hIdx_a' : rkIdx (fixV (Subgroup.zpowers a')) = 4 * rk ↥(fixV T) :=
          step2_rkIdx_eq_four_n hW hL3 hfix hspan hhom hTL hJ hT ha'L ha'2' h8
        have hle : rkIdx (fixV (Subgroup.zpowers a')) ≤ rkIdx (fixV (Subgroup.zpowers t0)) :=
          step4_rkIdx_le hW hfix hspan ha'L hb'_cent hb'2 ht0_eq
        rw [hIdx_a'] at hle
        omega
    rw [ht0rk] at ht0_ge_eight
    omega
  have h := card_eq_two_pow hW (fixV T)
  rw [h, hn_eq_one]
  norm_num

theorem rk_eq_three_and_card_fixV_or [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L M : Subgroup (MulAut W)} (hL3 : IsL3 ↥L 1) (hM : M = centGroupIn Y L) (hY : Y = L ⊔ M)
    (hfix : fixV L = ⊥) (htr : IrrSpanTrans Y L) (hm : E3.mParam Y = 4)
    {T : Subgroup (MulAut W)} (hTL : T ≤ L) (hT : ∀ I ∈ irrSet L, Nat.card ↥(I ⊓ fixV T) = 2) :
    (∀ I ∈ irrSet L, rk ↥I = 3) ∧ Nat.card ↥(fixV T) = 16 ∨ Nat.card ↥(fixV T) = 2 := by
  have hne : (irrSet L).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hbot : (⨆ I ∈ irrSet L, I) = ⊥ := by simp [h]
    have htop : (⊤ : Subgroup W) = ⊥ := by rw [← htr.1, hbot]
    have hsub : Subsingleton W := by
      refine ⟨fun x y => ?_⟩
      have hx : x = 1 := by
        have : x ∈ (⊥ : Subgroup W) := by rw [← htop]; exact Subgroup.mem_top x
        exact Subgroup.mem_bot.mp this
      have hy : y = 1 := by
        have : y ∈ (⊥ : Subgroup W) := by rw [← htop]; exact Subgroup.mem_top y
        exact Subgroup.mem_bot.mp this
      rw [hx, hy]
    obtain ⟨a, haL, ha2⟩ := exists_mem_orderOf_eq_two hL3
    have ha1 : a = 1 := MulEquiv.ext fun w => Subsingleton.elim (a w) w
    rw [ha1] at ha2
    simp at ha2
  obtain ⟨J, hJ⟩ := hne
  have hspan : (⨆ I ∈ irrSet L, I) = ⊤ := htr.1
  have hhom : ∀ I ∈ irrSet L, CFSG.Quasithin.H.Pair.IsoMod L J I := fun I hI =>
    isoMod_of_mem_irrSet hM hY hfix htr hJ hI
  obtain ⟨a, haL, ha2⟩ := exists_mem_orderOf_eq_two hL3
  have haY : a ∈ Y := by rw [hY]; exact Subgroup.mem_sup_left haL
  have hEven : Even (Nat.card Y) := by
    have hzaY : Subgroup.zpowers a ≤ Y := Subgroup.zpowers_le.mpr haY
    have hdvd : Nat.card ↥(Subgroup.zpowers a) ∣ Nat.card Y := Subgroup.card_dvd_of_le hzaY
    rw [Nat.card_zpowers, ha2] at hdvd
    rw [even_iff_two_dvd]
    exact hdvd
  let S0 : Set ℕ := {n | ∃ t ∈ Y, orderOf t = 2 ∧ n = rkIdx (fixV (Subgroup.zpowers t))}
  have hmParam : E3.mParam Y = sInf S0 := by
    unfold E3.mParam
    rw [if_pos hEven]
  have hsInf : sInf S0 = 4 := by rw [← hmParam, hm]
  have hS0_nonempty : S0.Nonempty := by
    refine ⟨rkIdx (fixV (Subgroup.zpowers a)), ?_⟩
    exact ⟨a, haY, ha2, rfl⟩
  have h4mem : 4 ∈ S0 := by
    have h := Nat.sInf_mem hS0_nonempty
    rwa [hsInf] at h
  have h4_le_a : 4 ≤ rkIdx (fixV (Subgroup.zpowers a)) := by
    have hmem : rkIdx (fixV (Subgroup.zpowers a)) ∈ S0 := ⟨a, haY, ha2, rfl⟩
    have h := Nat.sInf_le hmem
    rwa [hsInf] at h
  have h3_or_8 : rk ↥J = 3 ∨ rk ↥J = 8 := by
    have h := rk_inf_fixV_zpowers_of_mem_irrSet hW hL3 hfix hJ haL ha2
    rcases h with ⟨h3, _⟩ | ⟨h8, _⟩
    · exact Or.inl h3
    · exact Or.inr h8
  obtain ⟨t0, ht0Y, ht02, ht0rk_eq⟩ := h4mem
  have ht0rk : rkIdx (fixV (Subgroup.zpowers t0)) = 4 := ht0rk_eq.symm
  rcases h3_or_8 with h3 | h8
  · exact Or.inl (case_r3 hW hL3 hM hY hfix htr hTL hT hJ hhom haL ha2 h3 h4_le_a ht0Y ht02 ht0rk)
  · exact Or.inr (case_r8 hW hL3 hM hY hfix htr hTL hT hJ hhom h8 ht0Y ht02 ht0rk)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultSpace
