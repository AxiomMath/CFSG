module

public import CFSG.Quasithin.Background.B69Mod
public import CFSG.Quasithin.Background.B69Asm

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

noncomputable abbrev wtLA {V : Type} [CommGroup V] (A L : Subgroup (MulAut V)) (W : Subgroup V) :
    Subgroup (MulAut (Sec W (W ⊓ fixV L))) :=
  autSec (L ⊔ A) W (W ⊓ fixV L)

noncomputable abbrev wtL {V : Type} [CommGroup V] (L : Subgroup (MulAut V)) (W : Subgroup V) :
    Subgroup (MulAut (Sec W (W ⊓ fixV L))) :=
  autSec L W (W ⊓ fixV L)

@[expose] def AsB69SectionB42 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ∃ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) ∧
          IsFFStarOffender (wtLA A L W) B ∧ B42Conclusion (wtLA A L W) (wtL L W) B

@[expose] def AsB69NoRankTwoSL3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) → ¬ B42Case2 (wtLA A L W) (wtL L W)

@[expose] def AsB69NoRankTwoSp4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) → ¬ B42Case3 (wtLA A L W) (wtL L W)

@[expose] def AsB69NoRankTwoA6 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ∀ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) →
          IsFFStarOffender (wtLA A L W) B → ¬ B42Case6 (wtLA A L W) (wtL L W) B

@[expose] def AsB69NoRankTwoTripleA6 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ∀ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) →
          IsFFStarOffender (wtLA A L W) B → ¬ B42Case8 (wtLA A L W) (wtL L W) B

@[expose] def AsB69NoG2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ∀ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) →
          IsFFStarOffender (wtLA A L W) B → ¬ B42Case4 (wtLA A L W) (wtL L W) B

@[expose] def AsB69NoA7 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ∀ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) →
          IsFFStarOffender (wtLA A L W) B → ¬ B42Case7 (wtLA A L W) (wtL L W) B

@[expose] def AsB69RankOneSylow : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        (∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e) →
          CFSG.QuasithinUnique.IsSylowTwoOf A L

@[expose] def AsB69RankOneBorel : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        (∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e) →
          M ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V))

@[expose] def AsB69AltCase : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), CompHyp X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        ∀ B : Subgroup (MulAut (Sec W (W ⊓ fixV L))), B ≤ autSec A W (W ⊓ fixV L) →
          IsFFStarOffender (wtLA A L W) B → B42Case5 (wtLA A L W) B → AltShape M A L W

@[expose] def AsB69NoOddCoverSL2 : Prop :=
  ∀ (L H : Type) [Group L] [Group H] [Finite L], CFSG.Open.IsQuasisimple L →
    ∀ f : L →* H, Function.Surjective f → (∀ x ∈ f.ker, Odd (orderOf x)) →
      (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (H ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K))) → Function.Injective f

structure AsB69DeepInputs : Prop where
  sp4 : AsB69NoRankTwoSp4
  a6 : AsB69NoRankTwoA6
  tripleA6 : AsB69NoRankTwoTripleA6
  g2 : AsB69NoG2
  oneSylow : AsB69RankOneSylow
  oneBorel : AsB69RankOneBorel
  alt : AsB69AltCase

section Section

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_surj_autSec {L : Subgroup (MulAut V)} {W U : Subgroup V} (hLW : L ≤ stabSub W)
    (hLU : L ≤ stabSub U) :
    ∃ f : ↥L →* ↥(autSec L W U), Function.Surjective f ∧
      ∀ x : ↥L, f x = 1 ↔ (x : MulAut V) ∈ centSec W U := by
  refine ⟨(MulEquiv.subgroupCongr (B5.range_secHom L hLW hLU)).toMonoidHom.comp
    (B5.secHom L hLW hLU).rangeRestrict, ?_, fun x => ?_⟩
  · exact (MulEquiv.subgroupCongr (B5.range_secHom L hLW hLU)).surjective.comp
      (B5.secHom L hLW hLU).rangeRestrict_surjective
  · rw [← B5.mem_ker_secHom L hLW hLU x, MonoidHom.mem_ker, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

omit [Finite V] in
theorem nontrivial_autSec {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) : Nontrivial ↥(autSec L W (W ⊓ fixV L)) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  obtain ⟨hinv, hcomm, hlt, -⟩ := mem_irrPlus_top_iff.1 hW
  have hLW : L ≤ stabSub W := B1.le_stabSub_of_invariant hinv
  have hLZ : L ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hinv (isInv_fixV L))
  have hgens : commSub W L ≤ W ⊓ fixV L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    have hmem : B5.secHom L hLW hLZ ⟨x, hx⟩ ∈ autSec L W (W ⊓ fixV L) := by
      rw [← B5.range_secHom L hLW hLZ]
      exact ⟨⟨x, hx⟩, rfl⟩
    have h1 : B5.secHom L hLW hLZ ⟨x, hx⟩ = 1 := by
      have : (⟨B5.secHom L hLW hLZ ⟨x, hx⟩, hmem⟩ : ↥(autSec L W (W ⊓ fixV L))) =
          ⟨1, (autSec L W (W ⊓ fixV L)).one_mem⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val this
    exact (B5.mem_ker_secHom L hLW hLZ ⟨x, hx⟩).1 (MonoidHom.mem_ker.2 h1) |>.2 w hw
  rw [hcomm] at hgens
  exact absurd (le_antisymm inf_le_left hgens ▸ hlt) (lt_irrefl _)

theorem odd_orderOf_of_mem_center_comp {X L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 X = ⊥)
    (hL : CFSG.Open.IsComponentOf L X) {z : ↥L} (hz : z ∈ Subgroup.center ↥L) :
    Odd (orderOf z) := by
  by_contra hev
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
  have hne : orderOf z ≠ 0 := (orderOf_pos z).ne'
  set y : ↥L := z ^ (orderOf z / 2) with hy
  have hyord : orderOf y = 2 := orderOf_pow_orderOf_div hne hev
  have hyc : y ∈ Subgroup.center ↥L := Subgroup.pow_mem _ hz _
  set Y : Subgroup (MulAut V) := Subgroup.zpowers ((y : ↥L) : MulAut V) with hYdef
  have hYL : Y ≤ L := Subgroup.zpowers_le.2 y.2
  have hLY : L ≤ Subgroup.normalizer (Y : Set (MulAut V)) := by
    intro l hl
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun g' hg' => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'
    have hcomm : Commute ((y : ↥L) : MulAut V) l :=
      (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hyc) ⟨l, hl⟩)).symm
    exact (hcomm.zpow_left k).eq
  have hY2 : IsPGroup 2 Y :=
    IsPGroup.of_card (n := 1) (by rw [hYdef, Nat.card_zpowers, Subgroup.orderOf_coe, hyord]; norm_num)
  have h1 : Y ≤ pCoreOf 2 L := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYL hLY hY2
  have h2 : pCoreOf 2 L ≤ pCoreOf 2 X := A4.pCoreOf_le_of_subnormal 2 hL.2.1
  have h3 : ((y : ↥L) : MulAut V) ∈ pCoreOf 2 X := h2 (h1 (Subgroup.mem_zpowers _))
  rw [hO2, Subgroup.mem_bot] at h3
  have : y = 1 := Subtype.ext h3
  rw [this, orderOf_one] at hyord
  omega

omit [Finite V] in
theorem stab_of_irr {L : Subgroup (MulAut V)} {W : Subgroup V} (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) :
    L ≤ stabSub W ∧ L ≤ stabSub (W ⊓ fixV L) := by
  obtain ⟨hinv, -, -, -⟩ := mem_irrPlus_top_iff.1 hW
  exact ⟨B1.le_stabSub_of_invariant hinv,
    B1.le_stabSub_of_invariant (isInv_inf hinv (isInv_fixV L))⟩

theorem binaryNaturalSL_of_case1 (hD3 : AsB69NoOddCoverSL2) {X L : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 X = ⊥) (hL : CFSG.Open.IsComponentOf L X) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) (h : ∃ n : ℕ, BinaryNaturalSL (wtL L W) ⊤ ⊥ 2 n) :
    ∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e := by
  obtain ⟨n, K, hKf, hKfin, hK, π₀, hπ₀⟩ := h
  obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
  obtain ⟨ℓ, hℓs, hℓk⟩ := exists_surj_autSec hLW hLZ
  have hinj : Function.Injective π₀ := natRealizes_injective hπ₀
  have e : ↥(wtL L W) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) := (MulEquiv.ofBijective π₀ ⟨hinj, hπ₀.1⟩).symm
  have hnt : Nontrivial ↥(wtL L W) := nontrivial_autSec hW
  have hne : ℓ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    obtain ⟨x, rfl⟩ := hℓs a
    obtain ⟨y, rfl⟩ := hℓs b
    apply hab
    have hx : x ∈ ℓ.ker := by rw [htop]; trivial
    have hy : y ∈ ℓ.ker := by rw [htop]; trivial
    rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
  have hcent : ℓ.ker ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL.2.2 ℓ.ker hne
  have hodd : ∀ x ∈ ℓ.ker, Odd (orderOf x) := fun x hx => odd_orderOf_of_mem_center_comp hO2 hL (hcent hx)
  have hℓinj : Function.Injective ℓ :=
    hD3 ↥L ↥(wtL L W) hL.2.2 ℓ hℓs hodd ⟨n, K, hKf, hKfin, hK, ⟨e⟩⟩
  have hfaith : L ⊓ centSec W (W ⊓ fixV L) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxc⟩
    have h1 : ℓ ⟨x, hxL⟩ = 1 := (hℓk ⟨x, hxL⟩).2 hxc
    have h2 : (⟨x, hxL⟩ : ↥L) = 1 := hℓinj (h1.trans (map_one ℓ).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  have hreal := B5.realizesVia_of_autSec (inf_le_left : W ⊓ fixV L ≤ W) hLW hLZ hfaith hπ₀
  have hKn : 1 < Nat.card K := Finite.one_lt_card
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at hK; omega
    · exact h
  exact ⟨n, hn1, K, hKf, hKfin, hK, _, hreal⟩

end Section

end B69

end CFSG.Quasithin
