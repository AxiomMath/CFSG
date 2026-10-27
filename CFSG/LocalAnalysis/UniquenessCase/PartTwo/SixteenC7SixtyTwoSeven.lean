module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoKer
public import CFSG.Quasithin.Background.HL3WrNPrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13 CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

section Normalizer

theorem s16c7_card_normalizer {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H) :
    Nat.card ↥(Subgroup.normalizer (H : Set (MulAut W))) = 2 * 168 ^ 2 := by
  obtain ⟨e, he⟩ := exists_model hreal
  have h3 : (Subgroup.normalizer (H : Set (MulAut W))).map (congrHom e) =
      Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut WMod)) :
        Set (MulAut WMod)) :=
    Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
  have h4 : (H.map (congrHom e) : Subgroup (MulAut WMod)) = img := he
  rw [← card_map_congrHom e, h3, h4]
  exact card_norm

theorem s16c7_card_le_of_isPGroup_seven {W : Type*} [CommGroup W] [Finite W]
    {H Q : Subgroup (MulAut W)} (hreal : (tensorPairModel SL32 SL32).RealizesMod H)
    (hQ : IsPGroup 7 Q) (hQN : Q ≤ Subgroup.normalizer (H : Set (MulAut W))) :
    Nat.card Q ≤ 49 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card ↥(Subgroup.normalizer (H : Set (MulAut W))) :=
    Subgroup.card_dvd_of_le hQN
  rw [s16c7_card_normalizer hreal, hn] at hdvd
  have hn2 : n ≤ 2 := by
    by_contra hlt
    have h3 : 7 ^ 3 ∣ 7 ^ n := pow_dvd_pow 7 (by omega)
    have h4 := h3.trans hdvd
    norm_num at h4
  rw [hn]
  calc 7 ^ n ≤ 7 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 49 := by norm_num

end Normalizer

section Kernel

variable {G : Type} [Group G] [Finite G]

theorem s16c7_card_barSub_le {V E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hE : E ≤ stabTil ⊥ V) (hp : IsPGroup 7 E) {A : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod A)
    (hEA : barSub ⊥ V hV E ≤ Subgroup.normalizer (A : Set (MulAut (Vtil ⊥ V hV)))) :
    Nat.card (barSub ⊥ V hV E) ≤ 49 := by
  have h0 : IsPGroup 7 (E.subgroupOf (stabTil ⊥ V)) := hp.comap_subtype
  exact s16c7_card_le_of_isPGroup_seven hreal (h0.map (actTil ⊥ V hV)) hEA

theorem s16c7_seven_dvd_card_inf_centralizer {V E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hE : E ≤ stabTil ⊥ V) (hcard : Nat.card E = 7 ^ 3) (hbar : Nat.card (barSub ⊥ V hV E) ≤ 49) :
    7 ∣ Nat.card ↥(E ⊓ centralizer (V : Set G)) := by
  have h := s16c7_card_eq_inf_centralizer_mul V hV hE
  by_contra hndvd
  have hcop : Nat.Coprime (Nat.card ↥(E ⊓ centralizer (V : Set G))) (7 ^ 3) :=
    Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hndvd).symm
  have hdvd : Nat.card ↥(E ⊓ centralizer (V : Set G)) ∣ 7 ^ 3 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h1 : Nat.card ↥(E ⊓ centralizer (V : Set G)) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [hcard, h1, one_mul] at h
  omega

theorem s16c7_pRank_seven_le_three {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil ⊥ V) {A : Subgroup (MulAut (Vtil ⊥ V hV))}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod A)
    (hMA : barSub ⊥ V hV M ≤ Subgroup.normalizer (A : Set (MulAut (Vtil ⊥ V hV))))
    (hC : CFSG.Open.pRank 7 (F11.CTilde M ⊥ V) ≤ 1) : CFSG.Open.pRank 7 M ≤ 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E hEM hEel
  have hEs : E ≤ stabTil ⊥ V := hEM.trans hMs
  have h := s16c7_card_eq_inf_centralizer_mul V hV hEs
  have hbar : Nat.card (barSub ⊥ V hV E) ≤ 49 :=
    s16c7_card_barSub_le hV hEs hEel.isPGroup hreal ((barSub_mono ⊥ V hV hEM).trans hMA)
  have hCle : E ⊓ centralizer (V : Set G) ≤ F11.CTilde M ⊥ V := by
    intro g hg
    obtain ⟨hgE, hgc⟩ := Subgroup.mem_inf.1 hg
    exact (mem_cTilde_iff hV (hMs.trans (stabTil_le_normalizer ⊥ V))).2
      ⟨hEM hgE, hEs hgE, (s16c7_actTil_eq_one_iff_mem_centralizer V hV ⟨g, hEs hgE⟩).2 hgc⟩
  have hCel : IsElemAbelian 7 (E ⊓ centralizer (V : Set G)) := hEel.mono inf_le_left
  obtain ⟨j, hj⟩ := hCel.isPGroup.exists_card_eq
  have hj1 : j ≤ 1 := (CFSG.SectionRank.le_pRank (by norm_num) hCle hCel hj).trans hC
  have hc : Nat.card ↥(E ⊓ centralizer (V : Set G)) ≤ 7 := by
    rw [hj]
    calc 7 ^ j ≤ 7 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 7 := by norm_num
  rw [h]
  calc Nat.card ↥(E ⊓ centralizer (V : Set G)) * Nat.card (barSub ⊥ V hV E) ≤ 7 * 49 :=
        Nat.mul_le_mul hc hbar
    _ = 7 ^ 3 := by norm_num

end Kernel

section EvenRank

variable {G : Type} [Group G] [Finite G]

theorem s16c7_evenRank_eq_three (D : Data G) (hx : DataExt D) (hsig : D.sig = {7})
    (h : CFSG.Open.pRank 7 D.M ≤ 3) : CFSG.Open.evenRank G = 3 := by
  have h3 := D.standing.rank
  by_contra hne
  have hlt : 3 < CFSG.Open.evenRank G := lt_of_le_of_ne h3 (Ne.symm hne)
  have h4 := hx.four_le hlt 7 (by rw [hsig]; exact Set.mem_singleton 7)
  omega

end EvenRank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
