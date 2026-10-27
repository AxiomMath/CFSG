module

public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge
public import CFSG.Quasithin.EmptyFaithful.LRed3A6
public import CFSG.Quasithin.Background.F918C6
public import CFSG.Quasithin.Background.F918C12
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.Vol2.Ch10SecAShapeB45

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
  CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

private theorem lred3_one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : 1 ≤ n := by
  by_contra h
  have h0 : n = 0 := by omega
  have := Finite.one_lt_card (α := K)
  rw [hK, h0] at this
  norm_num at this

section Core

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem lred3_l32_of_stab (hA21 : AsA21SQTKSection) (hF : Facts10_1)
    (h45 : AsB45) (hD : D3Std M Mp T L V) (hMp : Mp = L) (hT : T ≤ stabSub V)
    (hL : IsPSL 3 2 1 ↥L) : BinaryNaturalSL L V (V ⊓ fixV L) 3 1 := by
  subst hMp
  have hLs : Mp ≤ stabSub V := insp5a_le_stabSub hD.hyp
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQ := lred3_qsec hD.hyp rfl hO2
  have hb4 := lred3_b4Hyp hA21 hD.hyp rfl hO2
  have hq := lred3_qhatOf_autSec hD rfl hT
  have hsv : ∀ v : Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V), v ^ 2 = 1 :=
    sec_sq_eq_one hexp ⊤ _
  have hsh0 : IsShapeGroup ↥Mp :=
    Or.inr (Or.inr (nonempty_mulEquiv_slThree_of_isPSL hL))
  have hsimp : IsSimpleGroup ↥Mp := isSimpleGroup_of_isShapeGroup hsh0
  have hne : ¬ Mp ≤ centSub V := fun h => by
    obtain ⟨l, hl, v, hv, hlv⟩ := lred3_exists_ne hD.hyp rfl
    exact hlv (h hl v hv)
  have hfaith : Mp ⊓ centSub V = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hsimp hLs hne
  let eL : ↥Mp ≃* ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
    (autSubEquivOfFaithful hLs hfaith).trans
      (B5.secEquiv (autSub Mp V) (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful)
  have hL' := isPSL_congr eL hL
  have hsh : IsShapeGroup ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
    Or.inr (Or.inr (nonempty_mulEquiv_slThree_of_isPSL hL'))
  have : IsSimpleGroup ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
    isSimpleGroup_of_isShapeGroup hsh
  have hcard : Nat.card ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) = 168 := by
    have := CFSG.Quasithin.Vol2.Ch11.SecA.card_L32 hL'
    omega
  have hnat : BinaryNaturalSL (autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) ⊤ ⊥ 3 1 := by
    rcases h45 _ hsv _ _ hb4 hq with ⟨-, ⟨A, hA'⟩, hall⟩ | ⟨-, ht⟩ | h3
    · rcases b42_of_isShapeGroup hF hsv hb4 hA' (hall A hA') hsh with ⟨m, -, hn⟩ | hn3 | halt
      · exact (not_binaryNaturalSL_two_l32 hcard hn).elim
      · exact hn3
      · exact (not_alternatingNatural_five_l32 hcard halt).elim
    · rcases table_of_isShapeGroup hF hb4 ht hsh with ⟨m, -, horth⟩ | ⟨f, hsz⟩
      · exact (not_binaryOrthogonalFour_l32 hcard horth).elim
      · exact (not_binaryNaturalSz_l32 hcard hsz).elim
    · exact (not_part3_of_isShapeGroup hF h3 hsh).elim
  have hLZ : Mp ≤ stabSub (V ⊓ fixV Mp) :=
    le_stabSub_of_le_fixV (inf_le_right.trans (fixV_anti le_rfl))
  exact binaryNaturalSL_of_autSub hLs hLZ inf_le_left hfaith
    (InternalSec.binaryNaturalSL_of_autSec hQ.stabKC hQ.faithful hnat)

theorem lred3_alt6_of_stab (hA21 : AsA21SQTKSection) (hF : Facts10_1) (hFA : FactsA6)
    (h45 : AsB45) (hD : D3Std M Mp T L V) (hMp : Mp = L) (hT : T ≤ stabSub V)
    (hL : IsAlt 6 ↥L) : AlternatingNatural L V (V ⊓ fixV L) 6 := by
  subst hMp
  have hLs : Mp ≤ stabSub V := insp5a_le_stabSub hD.hyp
  have hexp : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hD.hyp.exp])
  have hO2 := lred3_pCoreOf_autSub_sup_eq_bot hD.hyp hT
  have hQ := lred3_qsec hD.hyp rfl hO2
  have hb4 := lred3_b4Hyp hA21 hD.hyp rfl hO2
  have hq := lred3_qhatOf_autSec hD rfl hT
  have hsv : ∀ v : Sec (⊤ : Subgroup ↥V) ((V ⊓ fixV Mp).subgroupOf V), v ^ 2 = 1 :=
    sec_sq_eq_one hexp ⊤ _
  have hA6 := A6Target.of_isAlt hL
  have hne : ¬ Mp ≤ centSub V := fun h => by
    obtain ⟨l, hl, v, hv, hlv⟩ := lred3_exists_ne hD.hyp rfl
    exact hlv (h hl v hv)
  have hfaith : Mp ⊓ centSub V = ⊥ :=
    have := hA6.isSimple
    inf_centSub_eq_bot_of_isSimpleGroup hA6.isSimple hLs hne
  let eL : ↥Mp ≃* ↥(autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) :=
    (autSubEquivOfFaithful hLs hfaith).trans
      (B5.secEquiv (autSub Mp V) (InternalSec.le_stabSub_top _) hQ.stabKC hQ.faithful)
  have hL' := isAlt_congr eL hL
  have hnat : AlternatingNatural (autSec (autSub Mp V) ⊤ ((V ⊓ fixV Mp).subgroupOf V)) ⊤ ⊥ 6 := by
    rcases h45 _ hsv _ _ hb4 hq with ⟨-, ⟨A, hA'⟩, hall⟩ | ⟨-, ht⟩ | h3
    · exact lred3_b42_alt6 hF hsv hb4 hA' (hall A hA') hL'
    · exact (lred3_table_alt6 hFA ht hL').elim
    · exact (lred3_part3_alt6 hFA h3 hL').elim
  have hLZ : Mp ≤ stabSub (V ⊓ fixV Mp) :=
    le_stabSub_of_le_fixV (inf_le_right.trans (fixV_anti le_rfl))
  exact alternatingNatural_of_autSub hLs hLZ inf_le_left hfaith
    (InternalSec.alternatingNatural_of_autSec hQ.stabKC hQ.faithful hnat)

end Core

section First

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {U C : Subgroup W}

theorem lred3_l32_of_first (hcard : Nat.card ↥L = 168)
    (h : (∃ n, BinaryNaturalSL L U C 3 n) ∨ (∃ n, BinaryNaturalSp4 L U C n) ∨
      AlternatingNatural L U C 6 ∨ BinaryNaturalSL L U C 4 1 ∨ BinaryNaturalSL L U C 5 1 ∨
      A7Four L U C) : BinaryNaturalSL L U C 3 1 := by
  have hfin : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial ↥L := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨π, hπ⟩ | h4 | h5 | ⟨α, π, hπ⟩
  ·
    obtain ⟨K, _, _, hKc, π, hπ⟩ := hn
    have hcL : Nat.card ↥L = Nat.card ↥(StatedSL 3 K) :=
      card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
    rw [card_statedSL, card_SL_three_pow hKc, hcard] at hcL
    have hodd : Odd ((2 ^ (3 * n) - 1) * (2 ^ (2 * n) - 1)) :=
      (odd_two_pow_sub_one (by have := lred3_one_le_of_card hKc; omega)).mul
        (odd_two_pow_sub_one (by have := lred3_one_le_of_card hKc; omega))
    obtain ⟨h3n, -⟩ := two_pow_mul_odd_inj hodd (by decide : Odd 21)
      (hcL.symm.trans (by norm_num : (168 : ℕ) = 2 ^ 3 * 21))
    have hn1 : n = 1 := by omega
    subst hn1
    exact ⟨K, inferInstance, inferInstance, hKc, π, hπ⟩
  ·
    obtain ⟨K, _, _, hKc, π, hπ⟩ := hn
    have hcL : Nat.card ↥L = Nat.card ↥(StatedSp 2 K) :=
      card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
    rw [card_Sp4_pow hKc, hcard] at hcL
    have hodd : Odd ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) :=
      (odd_two_pow_sub_one (by have := lred3_one_le_of_card hKc; omega)).mul
        (odd_two_pow_sub_one (by have := lred3_one_le_of_card hKc; omega))
    obtain ⟨h4n, -⟩ := two_pow_mul_odd_inj hodd (by decide : Odd 21)
      (hcL.symm.trans (by norm_num : (168 : ℕ) = 2 ^ 3 * 21))
    have := lred3_one_le_of_card hKc
    omega
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 6) (by norm_num)) π hπ.1
    have h360 := hcard
    rw [← Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)] at h360
    norm_num [Nat.factorial] at h360
  ·
    obtain ⟨K, _, _, hKc, π, hπ⟩ := h4
    have hcL : Nat.card ↥L = Nat.card ↥(StatedSL 4 K) :=
      card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
    rw [card_statedSL, card_SL_four_of_two (by simpa using hKc), hcard] at hcL
    norm_num at hcL
  ·
    obtain ⟨K, _, _, hKc, π, hπ⟩ := h5
    have hcL : Nat.card ↥L = Nat.card ↥(StatedSL 5 K) :=
      card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
    rw [card_statedSL, card_SL_five_of_two (by simpa using hKc), hcard] at hcL
    norm_num at hcL
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π hπ.1
    have h360 := hcard
    rw [← Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)] at h360
    norm_num [Nat.factorial] at h360

theorem lred3_alt6_of_first (hcard : Nat.card ↥L = 360)
    (h : (∃ n, BinaryNaturalSL L U C 3 n) ∨ (∃ n, BinaryNaturalSp4 L U C n) ∨
      AlternatingNatural L U C 6 ∨ BinaryNaturalSL L U C 4 1 ∨ BinaryNaturalSL L U C 5 1 ∨
      A7Four L U C) : AlternatingNatural L U C 6 := by
  have hfin : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Nontrivial ↥L := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | h6 | h4 | h5 | ⟨α, π, hπ⟩
  · obtain ⟨K, _, _, hKc, π, hπ⟩ := hn
    have hcL : Nat.card ↥L = Nat.card ↥(StatedSL 3 K) :=
      card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
    rw [card_statedSL, card_SL_three_pow hKc] at hcL
    exact (lred3_sl3_ne_360 (lred3_one_le_of_card hKc) (hcL.symm.trans hcard)).elim
  · obtain ⟨K, _, _, hKc, π, hπ⟩ := hn
    have hcL : Nat.card ↥L = Nat.card ↥(StatedSp 2 K) :=
      card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
    rw [card_Sp4_pow hKc] at hcL
    exact (lred3_sp4_ne_360 (lred3_one_le_of_card hKc) (hcL.symm.trans hcard)).elim
  · exact h6
  · obtain ⟨K, _, _, hKc, π, hπ⟩ := h4
    have hcL : Nat.card ↥L = Nat.card ↥(StatedSL 4 K) :=
      card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
    rw [card_statedSL, card_SL_four_of_two (by simpa using hKc), hcard] at hcL
    norm_num at hcL
  · obtain ⟨K, _, _, hKc, π, hπ⟩ := h5
    have hcL : Nat.card ↥L = Nat.card ↥(StatedSL 5 K) :=
      card_eq_of_realizesVia_faithful_sec (FFModel.nat_faithful _) hπ
    rw [card_statedSL, card_SL_five_of_two (by simpa using hKc), hcard] at hcL
    norm_num at hcL
  · obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π hπ.1
    have h360 := hcard
    rw [← Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)] at h360
    norm_num [Nat.factorial] at h360

end First

section Main

theorem insp14622Nat_of_inputs (hA21 : AsA21SQTKSection)
    (hF : Facts10_1) (hFA : FactsA6) (h45 : AsB45) (hD310 : D310) : Insp14622Nat := by
  intro W _ _ M Mp T L V hD hMp hqM
  have hcases := hD310 W M Mp T L V hD hMp hqM
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  ·
    rcases hcases with hT | ⟨hfirst, -, -⟩
    · exact lred3_l32_of_stab hA21 hF h45 hD hMp (fun t ht => hT t ht) hL
    · exact lred3_l32_of_first (CFSG.Quasithin.Vol2.Ch11.SecA.card_L32 hL ▸ by norm_num) hfirst
  ·
    rcases hcases with hT | ⟨hfirst, -, -⟩
    · exact lred3_alt6_of_stab hA21 hF hFA h45 hD hMp (fun t ht => hT t ht) hL
    · exact lred3_alt6_of_first (A6Target.of_isAlt hL).card hfirst

end Main

end CFSG.Quasithin
