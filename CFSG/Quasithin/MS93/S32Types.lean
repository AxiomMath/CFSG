module

public import CFSG.Quasithin.MS93.FFTypes
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.MS93.S32Dict

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.VolI
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G]

theorem card_autI_le [Finite G] {U X K : Subgroup G} (hU : IsElemAbelian 2 U)
    (hX : IsElemAbelian 2 X) (hUX : U ≤ X) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) :
    Nat.card (autI hU K) ≤ Nat.card (autI hX K) := by
  rw [← range_convHom hU K hKU, ← range_convHom hX K hKX,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (convHom hU K hKU)).toEquiv.symm,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (convHom hX K hKX)).toEquiv.symm,
    ← Subgroup.index, ← Subgroup.index]
  have hle : (convHom hX K hKX).ker ≤ (convHom hU K hKU).ker := by
    rw [ker_convHom, ker_convHom]
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    refine ⟨hk.1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hk.2 u (hUX hu)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
    (Subgroup.index_dvd_of_le hle)

section Lstar

variable [Finite G] {M T L W : Subgroup G}

abbrev Lstar (L : Subgroup G) : Type :=
  (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)

theorem card_quot_center_autI (hs : IsSecW M L W) (h : PUHyp M T L) :
    Nat.card (↥(autI (hs.isElemAbelian h) L) ⧸
      Subgroup.center ↥(autI (hs.isElemAbelian h) L)) = Nat.card (Lstar L) :=
  (Nat.card_congr (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple
    (hs.quotHom_surjective h) (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      h.quasisimple (hs.quotHom_ne_one h))).toEquiv).symm

structure TypeFacts : Prop where
  g2 : ∀ (P : Type) [Group P] (F : Type) [Field F] [Finite F] (n : ℕ), Nat.card F = 2 ^ n →
    2 ≤ n → (↥(quasithinG2 F) ≃* P) → Nat.card (P ⧸ Subgroup.center P) = ordG2 (2 ^ n)
  g2two : ∀ (P : Type) [Group P] (F : Type) [Field F] [Finite F], Nat.card F = 2 →
    (P ≃* ↥(quasithinG2 F)) → ¬ CFSG.IsQuasisimple P
  g2d : ∀ (P : Type) [Group P] (F : Type) [Field F] [Finite F], Nat.card F = 2 →
    (↥⁅quasithinG2 F, quasithinG2 F⁆ ≃* P) → Nat.card (P ⧸ Subgroup.center P) = 6048
  alt8 : ∀ (P : Type) [Group P], IsRankTwoLie2Derived (P ⧸ Subgroup.center P) →
    (↥(alternatingGroup (Fin 8)) ≃* P) → False
  sl2 : ∀ (P : Type) [Group P], CFSG.IsQuasisimple P →
    IsRankTwoLie2Derived (P ⧸ Subgroup.center P) → ∀ (F : Type) [Field F] [Finite F] (n : ℕ),
    Nat.card F = 2 ^ n → (↥(StatedSL 2 F) ≃* P) → False
  alt57 : ∀ (P : Type) [Group P], IsRankTwoLie2Derived (P ⧸ Subgroup.center P) → ∀ m : ℕ,
    (m = 5 ∨ m = 7) → (↥(alternatingGroup (Fin m)) ≃* P) → False
  u33 : ∀ (P : Type) [Group P] (F : Type) [Field F] [Finite F], Nat.card F = 2 →
    (P ≃* ↥⁅quasithinG2 F, quasithinG2 F⁆) → B42TypeU33 P
  u33aut : ∀ (V : Type) [CommGroup V] [Finite V] (X K : Subgroup (MulAut V)), K ≤ X →
    X ≤ Subgroup.normalizer (K : Set (MulAut V)) → (∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → c = 1) →
    B42TypeU33 ↥K → Nat.card X ≤ 12096

variable (hs : IsSecW M L W) (h : PUHyp M T L)
include hs h

theorem card_lstar_of_sl3 {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    {π : ↥(StatedSL 3 F) →* ↥(autI (hs.isElemAbelian h) L)}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (autI (hs.isElemAbelian h) L) U Z π) :
    1 ≤ n ∧ Nat.card (Lstar L) = ordA 2 (2 ^ n) := by
  obtain ⟨hn, -, hc⟩ :=
    isPSL_quot_of_equiv_statedSL_three hF (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)
  exact ⟨hn, (card_quot_center_autI hs h).symm.trans hc⟩

theorem card_lstar_of_sp4 {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    {π : ↥(StatedSp 2 F) →* ↥(autI (hs.isElemAbelian h) L)}
    (hπ : (FFModel.nat (StatedSp 2 F)).RealizesVia (autI (hs.isElemAbelian h) L) U Z π) :
    2 ≤ n ∧ Nat.card (Lstar L) = ordBC 2 (2 ^ n) := by
  let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
  have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
  have hn2 : 2 ≤ n := by
    by_contra hlt
    rw [show n = 1 by omega] at hF
    exact R3c2.not_isQuasisimple_statedSp_two (hF.trans (pow_one 2)) e.symm (hs.quasisimple h)
  exact ⟨hn2, (card_quot_center_autI hs h).symm.trans (card_quot_of_equiv_statedSp hF hn2 e)⟩

theorem card_lstar_of_g2 (hT : TypeFacts) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    {π : ↥(quasithinG2 F) →* ↥(autI (hs.isElemAbelian h) L)}
    (hπ : (FFModel.zornQ (quasithinG2 F)).RealizesVia (autI (hs.isElemAbelian h) L) U Z π) :
    2 ≤ n ∧ Nat.card (Lstar L) = ordG2 (2 ^ n) := by
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  let e := FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ
  have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
  have hn2 : 2 ≤ n := by
    by_contra hlt
    rw [show n = 1 by omega] at hF
    exact hT.g2two _ F (hF.trans (pow_one 2)) e.symm (hs.quasisimple h)
  exact ⟨hn2, (card_quot_center_autI hs h).symm.trans (hT.g2 _ F n hF hn2 e)⟩

theorem card_lstar_of_g2d (hT : TypeFacts) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 1) {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    {π : ↥⁅quasithinG2 F, quasithinG2 F⁆ →* ↥(autI (hs.isElemAbelian h) L)}
    (hπ : (FFModel.zornQ ⁅quasithinG2 F, quasithinG2 F⁆).RealizesVia
      (autI (hs.isElemAbelian h) L) U Z π) :
    Nat.card (Lstar L) = 6048 := by
  have : CharP F 2 := FFC.charP_two_of_card_pow hF
  let e := FFC.equivOfRealizes (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ
  exact (card_quot_center_autI hs h).symm.trans (hT.g2d _ F (hF.trans (pow_one 2)) e)

theorem card_lstar_of_alt6 {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥(autI (hs.isElemAbelian h) L)}
    (hπ : (FFModel.altDn 6).RealizesVia (autI (hs.isElemAbelian h) L) U Z π) :
    Nat.card (Lstar L) = 360 :=
  (card_quot_center_autI hs h).symm.trans
    (card_quot_of_equiv_alt6 (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ))

theorem card_lstar_of_hat {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    (hhat : TripleA6Six (autI (hs.isElemAbelian h) L) U Z) : Nat.card (Lstar L) = 360 := by
  obtain ⟨Kf, iK, fK, Γ₀, -, -, hH, -, π, hπ⟩ := hhat
  exact (card_quot_center_autI hs h).symm.trans (card_quot_of_isHat
    (IsHat.of_mulEquiv (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ) hH))

theorem false_of_alt8 (hT : TypeFacts) {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    {π : ↥(alternatingGroup (Fin 8)) →* ↥(autI (hs.isElemAbelian h) L)}
    (hπ : (FFModel.altDn 8).RealizesVia (autI (hs.isElemAbelian h) L) U Z π) : False :=
  hT.alt8 _ (hs.rankTwo h) (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)

theorem false_of_sl2 (hT : TypeFacts) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {U Z : Subgroup (IntMod W (hs.isElemAbelian h))}
    {π : ↥(StatedSL 2 F) →* ↥(autI (hs.isElemAbelian h) L)}
    (hπ : (FFModel.nat (StatedSL 2 F)).RealizesVia (autI (hs.isElemAbelian h) L) U Z π) :
    False :=
  hT.sl2 _ (hs.quasisimple h) (hs.rankTwo h) F n hF
    (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)

end Lstar

section Orders

theorem ordA_two_ne_360 {n : ℕ} (hn : 1 ≤ n) : ordA 2 (2 ^ n) ≠ 360 := by
  intro he
  by_cases h1 : n = 1
  · subst h1
    revert he
    decide
  · exact ne_of_two_part (two_part_ordA_two hn) ⟨45, by decide, by norm_num⟩
      (N' := 3) (by omega) he

theorem ordA_two_ne_6048 {n : ℕ} (hn : 1 ≤ n) : ordA 2 (2 ^ n) ≠ 6048 :=
  ne_of_two_part (two_part_ordA_two hn) ⟨189, by decide, by norm_num⟩ (N' := 5) (by omega)

theorem eq_one_of_ordA_two {n : ℕ} (hn : 1 ≤ n) (he : ordA 2 (2 ^ n) = ordA 2 (2 ^ 1)) :
    n = 1 := by
  by_contra hne
  exact ne_of_two_part (two_part_ordA_two hn) (two_part_ordA_two le_rfl) (by omega) he

theorem ordBC_two_ne {n : ℕ} (hn : 1 ≤ n) :
    ordBC 2 (2 ^ n) ≠ ordA 2 (2 ^ 1) ∧ ordBC 2 (2 ^ n) ≠ 360 ∧ ordBC 2 (2 ^ n) ≠ 6048 :=
  ⟨ne_of_two_part (two_part_ordBC_two hn) (two_part_ordA_two le_rfl) (by omega),
    ne_of_two_part (two_part_ordBC_two hn) ⟨45, by decide, by norm_num⟩ (N' := 3) (by omega),
    ne_of_two_part (two_part_ordBC_two hn) ⟨189, by decide, by norm_num⟩ (N' := 5) (by omega)⟩

theorem ordG2_ne {n : ℕ} (hn : 1 ≤ n) :
    ordG2 (2 ^ n) ≠ ordA 2 (2 ^ 1) ∧ ordG2 (2 ^ n) ≠ 360 ∧ ordG2 (2 ^ n) ≠ 6048 :=
  ⟨ne_of_two_part (two_part_ordG2 hn) (two_part_ordA_two le_rfl) (by omega),
    ne_of_two_part (two_part_ordG2 hn) ⟨45, by decide, by norm_num⟩ (N' := 3) (by omega),
    ne_of_two_part (two_part_ordG2 hn) ⟨189, by decide, by norm_num⟩ (N' := 5) (by omega)⟩

end Orders

end CFSG.Quasithin.MS93.S32
