module

public import CFSG.Quasithin.MS93.FFOrders
public import CFSG.Quasithin.Background.SmithC27RTypeI
public import CFSG.Quasithin.Background.SmithC27RTypeRank2
public import CFSG.Quasithin.Vol2.Ch10SecASL2Over
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.Quasithin.Background.SmithB51LnSec

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Timmesfeld
open CFSG.Open (quasithinG2)

section Center

variable {P Q : Type} [Group P] [Group Q]

theorem card_quot_center_eq (hZ : Subgroup.center P = ⊥) :
    Nat.card (P ⧸ Subgroup.center P) = Nat.card P :=
  Nat.card_congr (SmithC27.quotCenterEquivSelf hZ).toEquiv

theorem center_eq_bot_of_mulEquiv (e : P ≃* Q) (h : Subgroup.center P = ⊥) :
    Subgroup.center Q = ⊥ := by
  rw [← SmithC27.map_center_of_mulEquiv e, h, Subgroup.map_bot]

theorem card_quot_of_equiv_alt6 (e : ↥(alternatingGroup (Fin 6)) ≃* P) :
    Nat.card (P ⧸ Subgroup.center P) = 360 := by
  rw [card_quot_center_eq (center_eq_bot_of_mulEquiv e
      (SmithC27.center_alternatingGroup_eq_bot' (Or.inr (Or.inl rfl)))),
    ← Nat.card_congr e.toEquiv, H13.card_alternatingGroup_fin 6 (by norm_num)]
  decide

theorem card_quot_of_isHat (h : IsHat P ↥(alternatingGroup (Fin 6))) :
    Nat.card (P ⧸ Subgroup.center P) = 360 := by
  obtain ⟨e⟩ := h.2.2
  rw [Nat.card_congr e.toEquiv, H13.card_alternatingGroup_fin 6 (by norm_num)]
  decide

end Center

section Models

variable {P : Type} [Group P] {F : Type} [Field F] [Finite F] {n : ℕ}

theorem isPSL_quot_of_equiv_statedSL_three (hF : Nat.card F = 2 ^ n)
    (e : ↥(StatedSL 3 F) ≃* P) :
    1 ≤ n ∧ IsPSL 3 2 n (P ⧸ Subgroup.center P) ∧
      Nat.card (P ⧸ Subgroup.center P) = CFSG.Open.ordA 2 (2 ^ n) := by
  have hn := R3c2.one_le_of_natCard_eq_two_pow hF
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by rw [Fintype.card_eq_nat_card, hF]
  have hP : IsPSL 3 2 n (P ⧸ Subgroup.center P) :=
    IsPSL.of_mulEquiv (SmithC27.quotCenterCongr e) (SmithC27.isPSL_statedSL_three hn hF')
  exact ⟨hn, hP, (card_statedClassicalModel_two hP).1 rfl⟩

theorem card_quot_of_equiv_statedSp (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (e : ↥(StatedSp 2 F) ≃* P) :
    Nat.card (P ⧸ Subgroup.center P) = CFSG.Open.ordBC 2 (2 ^ n) := by
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by rw [Fintype.card_eq_nat_card, hF]
  have hP : IsPSp4 2 n (P ⧸ Subgroup.center P) :=
    IsPSp4.of_mulEquiv (SmithC27.quotCenterCongr e) (SmithC27.isPSp4_statedSp_two hn hF')
  exact (card_statedClassicalModel_two hP).2.2.1 rfl

theorem card_quot_of_equiv_quasithinG2
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (e : ↥(quasithinG2 F) ≃* P) :
    Nat.card (P ⧸ Subgroup.center P) = CFSG.Open.ordG2 (2 ^ n) := by
  have := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by rw [Fintype.card_eq_nat_card, hF]
  have hP : IsG2 2 n (P ⧸ Subgroup.center P) :=
    IsG2.of_mulEquiv (SmithC27.quotCenterCongr e) (SmithC27.isG2_quasithinG2 hn hF')
  exact card_chevalleyExceptionalModel_two hP

theorem card_quot_of_equiv_g2Derived
    (hF : Nat.card F = 2)
    (e : ↥⁅quasithinG2 F, quasithinG2 F⁆ ≃* P) :
    B42TypeU33 P ∧ Nat.card (P ⧸ Subgroup.center P) = 6048 := by
  have hT : B42TypeU33 P := SmithC27.b42TypeU33_of_equiv hF e.symm
  refine ⟨hT, ?_⟩
  rw [card_quot_center_eq hT.1]
  exact H13.card_of_statedClassicalModel_psu_three_three
    (SmithC27.isPSU_of_equiv_g2Derived hF e.symm)

end Models

section Excluded


variable {P : Type} [Group P]

theorem false_of_equiv_statedSL_two (hq : CFSG.IsQuasisimple P)
    (hR : IsRankTwoLie2Derived (P ⧸ Subgroup.center P)) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (e : ↥(StatedSL 2 F) ≃* P) : False := by
  have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
  have hn2 : 2 ≤ n := by
    by_contra hlt
    rw [show n = 1 by omega] at hF
    exact SmithC27.not_isQuasisimple_statedSL_two_two (hF.trans (pow_one 2)) e.symm hq
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  have hZ0 : Subgroup.center ↥(StatedSL 2 F) = ⊥ :=
    center_eq_bot_of_mulEquiv (specialLinearGroupEquivStatedSL 2 F)
      (Vol2.Ch10.SecA.center_SL_two_eq_bot F)
  have hc : Nat.card (P ⧸ Subgroup.center P) = CFSG.Open.ordA 1 (2 ^ n) := by
    rw [card_quot_center_eq (center_eq_bot_of_mulEquiv e hZ0), ← Nat.card_congr e.toEquiv,
      C124.card_statedSL_two_pow hF, H13.VolI.ordA_one_two_pow hn1, ← pow_mul, mul_comm n 2]
  exact card_ne_ordA_one hR hn2 hc

theorem false_of_equiv_alt (hR : IsRankTwoLie2Derived (P ⧸ Subgroup.center P)) {m : ℕ}
    (hm : m = 5 ∨ m = 7) (e : ↥(alternatingGroup (Fin m)) ≃* P) : False := by
  have hc : Nat.card (P ⧸ Subgroup.center P) = m.factorial / 2 := by
    rw [card_quot_center_eq (center_eq_bot_of_mulEquiv e
        (SmithC27.center_alternatingGroup_eq_bot' (by omega))),
      ← Nat.card_congr e.toEquiv, H13.card_alternatingGroup_fin m (by omega)]
  rcases hm with rfl | rfl
  · exact card_ne_ordA_one hR (n := 2) le_rfl (by rw [hc]; decide)
  · exact card_ne_2520 hR (by rw [hc]; decide)

theorem false_of_equiv_statedSL_zmod
    (hR : IsRankTwoLie2Derived (P ⧸ Subgroup.center P)) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : ↥(StatedSL d (ZMod 2)) ≃* P) : False := by
  have hL : IsPSL d 2 1 P := R3c2.isPSL_two_of_statedSL (by omega) e.symm
  have hZ : Subgroup.center P = ⊥ :=
    B5.Ln.center_eq_bot_of_equiv (by simp : Nat.card (ZMod 2) = 2) e.symm
  have hc : Nat.card (P ⧸ Subgroup.center P) = CFSG.Open.ordA (d - 1) (2 ^ 1) := by
    rw [card_quot_center_eq hZ]
    exact (card_statedClassicalModel_two hL).1 rfl
  rcases hd with rfl | rfl
  · have h20 : Nat.card (P ⧸ Subgroup.center P) = 20160 := by rw [hc]; decide
    have hP3 := isPSL_three_two_two_of_card hR h20
    obtain ⟨θ⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
      (Or.inl ⟨by decide, hL⟩)
    have hE := (CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated
      (P ⧸ Subgroup.center P) hP3).2.2 (Fin 8) (by simp)
    exact hE.false ((SmithC27.quotCenterEquivSelf hZ).trans θ)
  · exact card_ne_9999360 hR (by rw [hc]; decide)

end Excluded

section U33

variable {V : Type} [CommGroup V] {X K : Subgroup (MulAut V)}

theorem card_le_of_b42TypeU33
    [Finite V] (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hC : ∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → c = 1) (hP : B42TypeU33 ↥K) :
    Nat.card X ≤ 12096 := by
  have hK'n : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hXN
  obtain ⟨θ⟩ := B42U33.nonempty_equiv_g2Derived hP
  let θ' : ↥(K.subgroupOf X) ≃* ↥(H13.g2Derived (ZMod 2)) :=
    (Subgroup.subgroupOfEquivOfLe hKX).trans θ
  have hinj : Function.Injective (B42U33.embG B42U33.conjNormal_bijective θ') := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc := B42U33.embG_eq_one B42U33.conjNormal_bijective θ' hg
    have hcomm : ∀ k ∈ K, (g : MulAut V) * k = k * g := by
      intro k hk
      have h1 := congrArg Subtype.val (hc ⟨k, hKX hk⟩ hk)
      change (g : MulAut V) * k * (g : MulAut V)⁻¹ = k at h1
      calc (g : MulAut V) * k = (g : MulAut V) * k * (g : MulAut V)⁻¹ * g := by group
        _ = k * g := by rw [h1]
    exact Subtype.ext (hC g g.2 hcomm)
  calc Nat.card X ≤ Nat.card ↥(quasithinG2 (ZMod 2)) := Nat.card_le_card_of_injective _ hinj
    _ = 12096 := H13.Orbit.card_g2Two

end U33

end CFSG.Quasithin.MS93
