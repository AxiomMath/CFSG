module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G]

theorem mem_fixV_zpowers {W : Type*} [CommGroup W] (t : MulAut W) (q : W) :
    q ∈ fixV (Subgroup.zpowers t) ↔ t q = q := by
  have key : ∀ X : Subgroup (MulAut W), q ∈ fixV X ↔ X ≤ MulAction.stabilizer (MulAut W) q := by
    intro X
    simp only [mem_fixV, SetLike.le_def, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  rw [key, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]

theorem two_pow_mul_le_iff {b c n : ℕ} (hb : ∃ e, b = 2 ^ e) (hc : 0 < c) :
    2 ^ (n + 1) * c ≤ c * b ↔ n < padicValNat 2 b := by
  obtain ⟨e, rfl⟩ := hb
  rw [padicValNat.prime_pow, mul_comm c, Nat.mul_le_mul_right_iff hc,
    Nat.pow_le_pow_iff_right (by norm_num)]
  omega

section Card

variable [Finite G]

theorem card_IntMod (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Nat.card (IntMod V hV) = Nat.card V := rfl

theorem exists_pow_card (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    ∃ a, Nat.card (IntMod V hV) = 2 ^ a := by
  have h2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (IsPGroup.iff_card).1 h2

theorem exists_pow_index (V : Subgroup G) (hV : IsElemAbelian 2 V) (H : Subgroup (IntMod V hV)) :
    ∃ e, H.index = 2 ^ e := by
  obtain ⟨a, ha⟩ := exists_pow_card V hV
  have h1 : H.index ∣ 2 ^ a := ha ▸ Subgroup.index_dvd_card H
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact ⟨k, hk⟩

theorem centMod_eq_image (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : stabTil V₀ V) :
    centMod V₀ V g = IntMod.val '' (((fixV (Subgroup.zpowers (actTil V₀ V hV g))).comap
      (mkTil V₀ V hV) : Subgroup (IntMod V hV)) : Set (IntMod V hV)) := by
  ext v
  constructor
  · rintro ⟨hv, hc⟩
    refine ⟨IntMod.mk hV ⟨v, hv⟩, ?_, rfl⟩
    show mkTil V₀ V hV _ ∈ fixV _
    rw [mem_fixV_zpowers, actTil_mk, mkTil_eq_iff, actStab_apply_val]
    exact hc
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.val_mem, ?_⟩
    have hx' : mkTil V₀ V hV x ∈ fixV (Subgroup.zpowers (actTil V₀ V hV g)) := hx
    rw [mem_fixV_zpowers, actTil_mk, mkTil_eq_iff, actStab_apply_val] at hx'
    exact hx'

theorem centMod_card_iff (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : stabTil V₀ V) (n : ℕ) :
    2 ^ (n + 1) * Nat.card (centMod V₀ V g) ≤ Nat.card V ↔
      n < rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV g))) := by
  set S := fixV (Subgroup.zpowers (actTil V₀ V hV g)) with hS
  set C : Subgroup (IntMod V hV) := S.comap (mkTil V₀ V hV) with hC
  have hidx : C.index = S.index := Subgroup.index_comap_of_surjective S (mkTil_surjective V₀ V hV)
  have hcard : Nat.card C * C.index = Nat.card (IntMod V hV) := Subgroup.card_mul_index C
  have hcm : Nat.card (centMod V₀ V g) = Nat.card C := by
    rw [centMod_eq_image V₀ V hV g]
    exact Nat.card_image_of_injective IntMod.val_injective _
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hpow : ∃ e, S.index = 2 ^ e := hidx ▸ exists_pow_index V hV C
  rw [hcm, ← card_IntMod V hV, ← hcard, hidx]
  exact two_pow_mul_le_iff hpow hpos


theorem card_Vtil_eq (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) :
    Nat.card V = Nat.card V₀ * Nat.card (Vtil V₀ V hV) := by
  have h1 : Nat.card (modNull V₀ V hV) * (modNull V₀ V hV).index = Nat.card (IntMod V hV) :=
    Subgroup.card_mul_index _
  have h2 : (modNull V₀ V hV).index = Nat.card (Vtil V₀ V hV) := Subgroup.index_eq_card _
  have h3 : Nat.card (modNull V₀ V hV) = Nat.card V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₀).toEquiv
  rw [← h2, ← h3, h1]
  rfl

theorem exists_pow_card_Vtil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    ∃ e, Nat.card (Vtil V₀ V hV) = 2 ^ e := by
  have h2 : (modNull V₀ V hV).index = Nat.card (Vtil V₀ V hV) := Subgroup.index_eq_card _
  rw [← h2]
  exact exists_pow_index V hV _

theorem two_pow_card_iff (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V) (n : ℕ) :
    2 ^ (n + 1) * Nat.card V₀ ≤ Nat.card V ↔ n < rk (Vtil V₀ V hV) := by
  rw [card_Vtil_eq V₀ V hV hV₀]
  exact two_pow_mul_le_iff (exists_pow_card_Vtil V₀ V hV) Nat.card_pos

end Card

section Bridge

variable [Finite G]

theorem even_card_barSub_iff (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (hMs : M ≤ stabTil V₀ V) :
    Even (Nat.card (Mbar M V₀ V hV)) ↔
      ∃ m ∈ M, ¬ CentralizesMod V₀ V m ∧ CentralizesMod V₀ V (m * m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hev
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Mbar M V₀ V hV) 2 (even_iff_two_dvd.1 hev)
    have hxo : orderOf (x : MulAut (Vtil V₀ V hV)) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    obtain ⟨g, hgM, hg⟩ := (mem_barSub V₀ V hV M _).1 x.2
    obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.1 hxo
    refine ⟨g, hgM, ?_, ?_⟩
    · intro hc
      exact hne (hg ▸ (actTil_eq_one_iff V₀ V hV g).2 hc)
    · have h1 : actTil V₀ V hV (g * g) = 1 := by
        rw [map_mul, hg, ← pow_two]; exact hsq
      exact (actTil_eq_one_iff V₀ V hV (g * g)).1 h1
  · rintro ⟨m, hm, hC, hC2⟩
    set g : stabTil V₀ V := ⟨m, hMs hm⟩ with hgdef
    have ht : actTil V₀ V hV g ∈ Mbar M V₀ V hV := actTil_mem_barSub V₀ V hV hm (hMs hm)
    have ho : orderOf (actTil V₀ V hV g) = 2 := by
      refine orderOf_eq_prime_iff.2 ⟨?_, ?_⟩
      · rw [pow_two, ← map_mul]
        exact (actTil_eq_one_iff V₀ V hV (g * g)).2 hC2
      · intro h1
        exact hC ((actTil_eq_one_iff V₀ V hV g).1 h1)
    have hdvd : orderOf (⟨actTil V₀ V hV g, ht⟩ : Mbar M V₀ V hV) ∣ Nat.card (Mbar M V₀ V hV) :=
      orderOf_dvd_natCard _
    have hoo : orderOf (⟨actTil V₀ V hV g, ht⟩ : Mbar M V₀ V hV) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact ho
    exact even_iff_two_dvd.2 (hoo ▸ hdvd)

end Bridge


section BridgeMain

variable [Finite G]

theorem mBarGT_iff_lt_mParam (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) (n : ℕ) :
    MBarGT M V₀ V n ↔ n < E3.mParam (Mbar M V₀ V hV) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMs : M ≤ stabTil V₀ V := le_inf hM hM₀
  have hA : (∀ m ∈ M, ¬ CentralizesMod V₀ V m → CentralizesMod V₀ V (m * m) →
        2 ^ (n + 1) * Nat.card (centMod V₀ V m) ≤ Nat.card V) ↔
      ∀ k ∈ {k : ℕ | ∃ t ∈ Mbar M V₀ V hV, orderOf t = 2 ∧
        k = rkIdx (fixV (Subgroup.zpowers t))}, n < k := by
    constructor
    · rintro h k ⟨t, ht, ho, rfl⟩
      obtain ⟨g, hgM, rfl⟩ := (mem_barSub V₀ V hV M t).1 ht
      obtain ⟨hsq, hne⟩ := orderOf_eq_prime_iff.1 ho
      have hC : ¬ CentralizesMod V₀ V g := fun hc => hne ((actTil_eq_one_iff V₀ V hV g).2 hc)
      have hC2 : CentralizesMod V₀ V ((g : G) * g) := by
        have h1 : actTil V₀ V hV (g * g) = 1 := by rw [map_mul, ← pow_two]; exact hsq
        exact (actTil_eq_one_iff V₀ V hV (g * g)).1 h1
      exact (centMod_card_iff V₀ V hV g n).1 (h g hgM hC hC2)
    · intro h m hm hC hC2
      set g : stabTil V₀ V := ⟨m, hMs hm⟩ with hgdef
      have ht : actTil V₀ V hV g ∈ Mbar M V₀ V hV := actTil_mem_barSub V₀ V hV hm (hMs hm)
      have ho : orderOf (actTil V₀ V hV g) = 2 := by
        refine orderOf_eq_prime_iff.2 ⟨?_, ?_⟩
        · rw [pow_two, ← map_mul]
          exact (actTil_eq_one_iff V₀ V hV (g * g)).2 hC2
        · intro h1
          exact hC ((actTil_eq_one_iff V₀ V hV g).1 h1)
      exact (centMod_card_iff V₀ V hV g n).2 (h _ ⟨_, ht, ho, rfl⟩)
  unfold E3.mParam MBarGT
  by_cases hev : Even (Nat.card (Mbar M V₀ V hV))
  · rw [if_pos hev]
    obtain ⟨m0, hm0, hn0, hn1⟩ := (even_card_barSub_iff M V₀ V hV hMs).1 hev
    have hne : {k : ℕ | ∃ t ∈ Mbar M V₀ V hV, orderOf t = 2 ∧
        k = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty := by
      set g : stabTil V₀ V := ⟨m0, hMs hm0⟩ with hgdef
      have ht : actTil V₀ V hV g ∈ Mbar M V₀ V hV := actTil_mem_barSub V₀ V hV hm0 (hMs hm0)
      have ho : orderOf (actTil V₀ V hV g) = 2 := by
        refine orderOf_eq_prime_iff.2 ⟨?_, ?_⟩
        · rw [pow_two, ← map_mul]
          exact (actTil_eq_one_iff V₀ V hV (g * g)).2 hn1
        · intro h1
          exact hn0 ((actTil_eq_one_iff V₀ V hV g).1 h1)
      exact ⟨_, _, ht, ho, rfl⟩
    constructor
    · rintro ⟨h1, -⟩
      exact (hA.1 h1) _ (Nat.sInf_mem hne)
    · intro hlt
      refine ⟨hA.2 fun k hk => lt_of_lt_of_le hlt (Nat.sInf_le hk), fun h => absurd (h m0 hm0 hn1) hn0⟩
  · rw [if_neg hev]
    have hno : ∀ m ∈ M, CentralizesMod V₀ V (m * m) → CentralizesMod V₀ V m := by
      intro m hm hC2
      by_contra hC
      exact hev ((even_card_barSub_iff M V₀ V hV hMs).2 ⟨m, hm, hC, hC2⟩)
    constructor
    · rintro ⟨-, h2⟩
      exact (two_pow_card_iff V₀ V hV hV₀ n).1 (h2 hno)
    · intro hlt
      exact ⟨fun m hm hC hC2 => absurd (hno m hm hC2) hC,
        fun _ => (two_pow_card_iff V₀ V hV hV₀ n).2 hlt⟩

theorem mBarGT_iff_lt_mBar (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) (n : ℕ) :
    MBarGT M V₀ V n ↔ n < mBar M V₀ V hV :=
  mBarGT_iff_lt_mParam M V₀ V hV hV₀ hM hM₀ n

theorem PairFacts.mBarGT_iff_lt_mBar {M V₀ V : Subgroup G} (h : PairFacts M V₀ V) (n : ℕ) :
    MBarGT M V₀ V n ↔ n < mBar M V₀ V h.elemAbelian :=
  PartTwo.mBarGT_iff_lt_mBar M V₀ V h.elemAbelian h.le h.le_normalizer h.le_normalizer₀ n

end BridgeMain

section Hyp125Facts

variable [Finite G]

theorem Hyp125.pairFacts {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    PairFacts D.M V₀ V :=
  hyp123_pairFacts h.1

theorem Hyp125.isElemAbelian {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    IsElemAbelian 2 V :=
  h.pairFacts.elemAbelian

theorem Hyp125.inCalV {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) : InCalV D.M V :=
  hyp123_inCalV h.1

theorem Hyp125.normalizer_eq {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    normalizer (V : Set G) = D.M :=
  normalizer_eq_of_inCalV D h.inCalV

theorem Hyp125.mBarGT_iff_lt_mBar {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (n : ℕ) :
    MBarGT D.M V₀ V n ↔ n < mBar D.M V₀ V h.isElemAbelian :=
  h.pairFacts.mBarGT_iff_lt_mBar n

end Hyp125Facts

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
