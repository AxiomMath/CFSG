module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198List
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowG2Outer
public import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG.RankThree.PartTwo

private theorem lt_card_sl_of_ge {N B q g : ℕ} (hB : 12 * N < B ^ 8) (hq : B ≤ q) (hB2 : 2 ≤ B)
    (hg : g ≤ 3) : N * g < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have hq2 : 2 ≤ q := hB2.trans hq
  have h2 : q ^ 2 ≤ 2 * (q ^ 2 - 1) := by
    have : 4 ≤ q ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq2 2
    omega
  have h3 : q ^ 3 ≤ 2 * (q ^ 3 - 1) := by
    have : 8 ≤ q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq2 3
    omega
  have h8 : q ^ 8 ≤ 4 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) := by
    calc q ^ 8 = q ^ 3 * (q ^ 2 * q ^ 3) := by ring
      _ ≤ q ^ 3 * ((2 * (q ^ 2 - 1)) * (2 * (q ^ 3 - 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3)
      _ = 4 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) := by ring
  have h9 : B ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hq 8
  have h10 : N * g ≤ N * 3 := Nat.mul_le_mul_left N hg
  omega

private theorem lt_card_su_of_ge {N B q g : ℕ} (hB : 12 * N < B ^ 8) (hq : B ≤ q) (hB2 : 2 ≤ B)
    (hg : g ≤ 3) : N * g < q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  have hq2 : 2 ≤ q := hB2.trans hq
  have h2 : q ^ 2 ≤ 2 * (q ^ 2 - 1) := by
    have : 4 ≤ q ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq2 2
    omega
  have h3 : q ^ 3 ≤ q ^ 3 + 1 := Nat.le_succ _
  have h8 : q ^ 8 ≤ 2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) := by
    calc q ^ 8 = q ^ 3 * (q ^ 2 * q ^ 3) := by ring
      _ ≤ q ^ 3 * ((2 * (q ^ 2 - 1)) * (q ^ 3 + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3)
      _ = 2 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) := by ring
  have h9 : B ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hq 8
  have h10 : N * g ≤ N * 3 := Nat.mul_le_mul_left N hg
  omega

private theorem checkSL : ∀ N : ℕ, (N = 51765179004000000 ∨ N = 448345497600 ∨ N = 495766656000 ∨
      N = 42305421312000 ∨ N = 273030912000000 ∨ N = 90745943887872000) →
    ∀ q < 190, 2 ≤ q → q ^ 3 ∣ N →
      N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  intro N hN q hq
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl <;> (interval_cases q <;> norm_num)

private theorem checkSU : ∀ N : ℕ, (N = 51765179004000000 ∨ N = 448345497600 ∨ N = 495766656000 ∨
      N = 42305421312000 ∨ N = 273030912000000 ∨ N = 90745943887872000) →
    ∀ q < 190, 2 ≤ q → q ^ 3 ∣ N →
      N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  intro N hN q hq
  rcases hN with rfl | rfl | rfl | rfl | rfl | rfl <;> (interval_cases q <;> norm_num)

private theorem not_isoLThreePi_of_card_spor {X : Type} [Group X] {N : ℕ}
    (hN : Nat.card X = N)
    (hNs : N = 51765179004000000 ∨ N = 448345497600 ∨ N = 495766656000 ∨ N = 42305421312000 ∨
      N = 273030912000000 ∨ N = 90745943887872000)
    (p e : ℕ) [Fact p.Prime] : ¬ Sec4.IsoLThreePi X p e := by
  have hB : 12 * N < 190 ^ 8 := by rcases hNs with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  refine KFacts.KS14.not_isoLThreePi_of_card hN (fun q hq hd => ?_) (fun q hq hd => ?_) p e
  · by_cases hqB : q < 190
    · exact checkSL N hNs q hqB hq hd
    · exact (lt_card_sl_of_ge hB (not_lt.mp hqB) (by norm_num)
        (Nat.gcd_le_left _ (by norm_num))).ne
  · by_cases hqB : q < 190
    · exact checkSU N hNs q hqB hq hd
    · exact (lt_card_su_of_ge hB (not_lt.mp hqB) (by norm_num)
        (Nat.gcd_le_left _ (by norm_num))).ne

private theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
  decide

private theorem ordG2_three : CFSG.Open.ordG2 (3 ^ 1) = 4245696 := by
  unfold CFSG.Open.ordG2
  norm_num

private theorem four_le_pRank_spor {T G : Type} [Group T] [Group G] [Finite G] {E : Subgroup T}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 4) (b : T ≃* G) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  refine CFSG.SectionRank.le_pRank (by norm_num) (le_top : E.map b.toMonoidHom ≤ ⊤)
    (CFSG.SectionRank.isElemAbelian_map hE b.toMonoidHom) ?_
  rw [Subgroup.card_map_of_injective b.injective, hc]

section Certificates


private theorem false_of_item43 {X : Type} [Group X] [Finite X] (h : RankHyp X) {N : ℕ}
    (hN : Nat.card (X ⧸ Subgroup.center X) = N)
    (hNs : N = 51765179004000000 ∨ N = 448345497600 ∨ N = 495766656000 ∨ N = 42305421312000 ∨
      N = 273030912000000 ∨ N = 90745943887872000)
    (h3 : 3 ∣ Nat.card (Subgroup.center X)) : False := by
  rcases Sec4.diag_item43_holds X (sectionFourHyp_of_rankHyp h) h.quasisimple h3 with
    ⟨p, e, hp, -, hL⟩ | e | e | hG | e | e | e | e | e
  · haveI := hp
    exact not_isoLThreePi_of_card_spor hN hNs p e hL
  · obtain ⟨e⟩ := e
    have h6 : N = 360 := hN.symm.trans ((Nat.card_congr e.toEquiv).trans card_alt_six)
    omega
  · obtain ⟨e⟩ := e
    have h7 : N = 2520 := hN.symm.trans ((Nat.card_congr e.toEquiv).trans
      KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1)
    omega
  · have hG2 : N = 4245696 := hN.symm.trans
      ((Sec4.RonanK432.card_of_chevalleyExceptionalModel_G2 hG).trans ordG2_three)
    omega
  · obtain ⟨e⟩ := e
    have hU : N = 3265920 := hN.symm.trans
      ((Nat.card_congr e.toEquiv).trans CFSG.PGLModel.card_projSU_four_three)
    omega
  · obtain ⟨e⟩ := e
    have hM : N = 443520 := hN.symm.trans
      ((Nat.card_congr e.toEquiv).trans KFacts.KS14.card_nativeM22)
    omega
  · obtain ⟨e⟩ := e
    have hJ : N = 50232960 := hN.symm.trans
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3)
    omega
  · obtain ⟨e⟩ := e
    have hMc : N = 898128000 := hN.symm.trans
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.McL.card_McL)
    omega
  · obtain ⟨e⟩ := e
    have hO : N = 460815505920 := hN.symm.trans
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.ON.card_ON)
    omega

private theorem false_of_spor {X : Type} [Group X] [Finite X] (h : RankHyp X) {G : Type}
    [Group G] [Finite G] (e : X ⧸ Subgroup.center X ≃* G) {N : ℕ} (hN : Nat.card G = N)
    (hNs : N = 51765179004000000 ∨ N = 448345497600 ∨ N = 495766656000 ∨ N = 42305421312000 ∨
      N = 273030912000000 ∨ N = 90745943887872000)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) : False := by
  have hN' : Nat.card (X ⧸ Subgroup.center X) = N := (Nat.card_congr e.toEquiv).trans hN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center X) := fun h3 => false_of_item43 h hN' hNs h3
  have hq := CFSG.SectionRank.pRank_quotient_eq (p := 3) (Subgroup.center X) hZ
  have he := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  have h3 := h.rank_three
  omega

theorem false_of_rankHyp_spor {X : Type} [Group X] [Finite X] (h : RankHyp X)
    {s : TauCeti.SporadicName}
    (hs : s = .Ly ∨ s = .Suz ∨ s = .Co3 ∨ s = .Co2 ∨ s = .HN ∨ s = .Th)
    (e : X ⧸ Subgroup.center X ≃* CFSG.RankThree.PartTwo.Sec4.Spor s) : False := by
  haveI : Finite (Sec4.Spor s) := Finite.of_equiv _ e.toEquiv
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
    obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Ly_elementary_three_rank_four
    exact false_of_spor h e ((Nat.card_congr b.toEquiv).symm.trans CFSG.Sporadic.Ly.card_Ly)
      (Or.inl rfl) (four_le_pRank_spor hE hc b)
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
    obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Suz_elementary_three_rank_four
    exact false_of_spor h e ((Nat.card_congr b.toEquiv).symm.trans CFSG.Sporadic.Suz.card_Suz)
      (Or.inr (Or.inl rfl)) (four_le_pRank_spor hE hc b)
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
    obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Co3_elementary_three_rank_four
    exact false_of_spor h e ((Nat.card_congr b.toEquiv).symm.trans CFSG.Sporadic.Co3.card_Co3)
      (Or.inr (Or.inr (Or.inl rfl))) (four_le_pRank_spor hE hc b)
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
    obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Co2_elementary_three_rank_four
    exact false_of_spor h e ((Nat.card_congr b.toEquiv).symm.trans CFSG.Sporadic.Co2.card_Co2)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (four_le_pRank_spor hE hc b)
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
    obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.HN_elementary_three_rank_four
    exact false_of_spor h e ((Nat.card_congr b.toEquiv).symm.trans CFSG.Sporadic.HN.card_HN)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (four_le_pRank_spor hE hc b)
  · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
    obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Th_elementary_three_rank_four
    exact false_of_spor h e
      ((Nat.card_congr b.toEquiv).symm.trans CFSG.RankThree.PartOne.CTP.card_Th)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (four_le_pRank_spor hE hc b)

end Certificates

end CFSG.RankThree.PartTwo.Sec19.SimsC198
