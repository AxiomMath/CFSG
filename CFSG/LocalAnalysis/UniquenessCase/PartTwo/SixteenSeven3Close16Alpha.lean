module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Zc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem close16_barSub_opp {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {Z : Subgroup G}
    (hZ : Z ≤ stabTil V₀ V) :
    barSub V₀ V hV (Opp 3 Z) = Opp 3 (barSub V₀ V hV Z) := by
  have h3 : Nat.Prime 3 := by norm_num
  have hOpp : (Opp 3 Z).subgroupOf (stabTil V₀ V) =
      CFSG.RankThree.PartOne.pElementSubgroup 3 (Z.subgroupOf (stabTil V₀ V)) := by
    have h1 := s13_pElementSubgroup_map h3 (stabTil V₀ V).subtype (Z.subgroupOf (stabTil V₀ V))
    rw [Subgroup.map_subgroupOf_eq_of_le hZ] at h1
    show (CFSG.RankThree.PartOne.pElementSubgroup 3 Z).subgroupOf (stabTil V₀ V) = _
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective (stabTil V₀ V).subtype_injective _
  unfold barSub
  rw [hOpp, s13_pElementSubgroup_map h3 (actTil V₀ V hV)]
  rfl

theorem close16_barSub_le_normalizer {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {X B : Subgroup G} (hB : B ≤ stabTil V₀ V) (hXB : X ≤ normalizer (B : Set G)) :
    barSub V₀ V hV X ≤
      normalizer ((barSub V₀ V hV B : Subgroup (MulAut (Vtil V₀ V hV))) :
        Set (MulAut (Vtil V₀ V hV))) := by
  unfold barSub
  refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map (actTil V₀ V hV))
  rw [← Subgroup.subgroupOf_normalizer_eq hB]
  exact fun x hx => hXB hx

theorem close16_card_barSub_dvd {V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil ⊥ V) {B : Subgroup G} (hB : B ≤ D.M) :
    Nat.card ↥(barSub ⊥ V hV B) ∣ Nat.card ↥B := by
  obtain ⟨φ, hφs, -⟩ := close16_exists_hom_barSub (hV := hV) hM hB
  exact Subgroup.card_dvd_of_surjective hφs

theorem close16_isPGroup_of_barSub (hM : D.M ≤ stabTil ⊥ V) {Y : Subgroup G}
    (hY : Close16Pack D V L hV Y) {B : Subgroup G} (hBY : B ≤ Y)
    (hB : IsPGroup 2 ↥(barSub ⊥ V hV B)) : IsPGroup 2 ↥B := by
  obtain ⟨φ, -, hφk⟩ := close16_exists_hom_barSub (hV := hV) hM (hBY.trans hY.le)
  have hk2 : IsPGroup 2 ↥φ.ker := by
    rw [hφk]
    refine IsPGroup.of_equiv (G := ↥(B ⊓ F11.CTilde D.M ⊥ V)) ?_
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
    exact IsPGroup.to_le (close16_inf_cTilde_isPGroup hY) (inf_le_inf hBY le_rfl)
  have h1 : IsPGroup 2 ↥(⊤ : Subgroup ↥(barSub ⊥ V hV B)) := hB.of_equiv Subgroup.topEquiv.symm
  have h2 := IsPGroup.comap_of_ker_isPGroup h1 φ hk2
  rw [Subgroup.comap_top] at h2
  exact h2.of_equiv Subgroup.topEquiv

theorem close16_inf_le_pCoreOf {M A Y : Subgroup G} (hAM : A ≤ M) (hYn : (Y.subgroupOf M).Normal)
    (h2 : IsPGroup 2 ↥(A ⊓ Y)) : A ⊓ Y ≤ pCoreOf 2 A := by
  have hconj : ∀ a ∈ A, ∀ y ∈ A ⊓ Y, a * y * a⁻¹ ∈ A ⊓ Y := by
    intro a ha y hy
    refine ⟨A.mul_mem (A.mul_mem ha hy.1) (A.inv_mem ha), ?_⟩
    exact hYn.conj_mem ⟨y, hAM hy.1⟩ hy.2 ⟨a, hAM ha⟩
  have hN : ((A ⊓ Y).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hconj a ha y, fun hy => ?_⟩
    have := hconj a⁻¹ (A.inv_mem ha) _ hy
    simpa [mul_assoc] using this
  have hp : IsPGroup 2 ↥((A ⊓ Y).subgroupOf A) :=
    h2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hle : (A ⊓ Y).subgroupOf A ≤ CFSG.pCore 2 ↥A := le_sSup ⟨hN, hp⟩
  intro x hx
  have hxA : x ∈ A := hx.1
  have hxA' : (⟨x, hxA⟩ : ↥A) ∈ (A ⊓ Y).subgroupOf A := hx
  exact ⟨⟨x, hxA⟩, hle hxA', rfl⟩

theorem close16_threePrime_normalized {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {w : W}
    (hpt : Close16PtStab H w) (hH : IsSimpleGroup ↥H) {B : Subgroup (MulAut W)} (hBH : B ≤ H)
    (h3 : ¬ 3 ∣ Nat.card ↥B)
    (hN : H ⊓ MulAction.stabilizer (MulAut W) w ≤ normalizer (B : Set (MulAut W))) :
    IsPGroup 2 ↥B := by
  classical
  haveI := hH
  have hSH : H ⊓ MulAction.stabilizer (MulAut W) w ≤ H := inf_le_left
  have h3S : 3 ∣ Nat.card ↥(H ⊓ MulAction.stabilizer (MulAut W) w) := by
    rw [hpt.card]
    norm_num
  have h3H : 3 ∣ Nat.card ↥H := h3S.trans (Subgroup.card_dvd_of_le hSH)
  rcases hpt.maximal (normalizer (B : Set (MulAut W)) ⊓ H) (le_inf hN hSH) inf_le_right with
    hJS | hJH
  · have hBS : B ≤ H ⊓ MulAction.stabilizer (MulAut W) w := by
      intro b hb
      have : b ∈ normalizer (B : Set (MulAut W)) ⊓ H := ⟨Subgroup.le_normalizer hb, hBH hb⟩
      rw [hJS] at this
      exact this
    have hnormS : (B.subgroupOf (H ⊓ MulAction.stabilizer (MulAut W) w)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).2 hN
    obtain ⟨f, hfs, hf2, -⟩ := hpt.quot
    haveI := GoldS146P.sl_simple 3 le_rfl
    haveI himgN := hnormS.map f hfs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((B.subgroupOf (H ⊓ MulAction.stabilizer (MulAut W) w)).map f) with hbot | htop
    · have hle : B.subgroupOf (H ⊓ MulAction.stabilizer (MulAut W) w) ≤ f.ker := by
        intro x hx
        have : f x ∈ (B.subgroupOf (H ⊓ MulAction.stabilizer (MulAut W) w)).map f :=
          Subgroup.mem_map_of_mem f hx
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      exact (IsPGroup.to_le hf2 hle).of_equiv (Subgroup.subgroupOfEquivOfLe hBS)
    · exfalso
      apply h3
      have hcard : Nat.card ↥((B.subgroupOf (H ⊓ MulAction.stabilizer (MulAut W) w)).map f) =
          168 := by
        rw [htop, Subgroup.card_top, close16_card_sl_three_two]
      have hdvd := Subgroup.card_dvd_of_surjective
        (f.subgroupMap_surjective (B.subgroupOf (H ⊓ MulAction.stabilizer (MulAut W) w)))
      rw [hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv] at hdvd
      exact (show 3 ∣ 168 by norm_num).trans hdvd
  · have hHN : H ≤ normalizer (B : Set (MulAut W)) := by
      intro h hh
      have : h ∈ normalizer (B : Set (MulAut W)) ⊓ H := by
        rw [hJH]
        exact hh
      exact this.1
    have hnormH : (B.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).2 hHN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.subgroupOf H) with hb | ht
    · have hB : B = ⊥ := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hBH, hb, Subgroup.map_bot]
      exact IsPGroup.of_card (n := 0) (by rw [hB, Subgroup.card_bot]; rfl)
    · exfalso
      apply h3
      have hBeq : B = H := le_antisymm hBH (Subgroup.subgroupOf_eq_top.1 ht)
      rw [hBeq]
      exact h3H

theorem close16_normalized_three_prime (hS : Close16Setting D V L hV) {Y : Subgroup G}
    (hY : Close16Pack D V L hV Y) {z : G} (hz : z ∈ V ⊓ centralizer (D.T : Set G))
    (hz1 : z ≠ 1) {B : Subgroup G} (hBY : B ≤ Y) (h3 : ¬ 3 ∣ Nat.card ↥B)
    (hXB : Opp 3 (Y ⊓ centralizer ({z} : Set G)) ≤ normalizer (B : Set G)) :
    IsPGroup 2 ↥B := by
  have hM := close16_le_stabTil hS
  have hZM : Y ⊓ centralizer ({z} : Set G) ≤ D.M := inf_le_left.trans hY.le
  have hBs : B ≤ stabTil ⊥ V := hBY.trans (hY.le.trans hM)
  have hpt := close16_ptStab_central hS hz hz1
  have hX : barSub ⊥ V hV (Opp 3 (Y ⊓ centralizer ({z} : Set G))) =
      lBar ⊥ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil ⊥ V hV))
        (close16Vec V hV z (Subgroup.mem_inf.1 hz).1) := by
    rw [close16_barSub_opp (hZM.trans hM),
      close16_barSub_cent_eq hS hY (Subgroup.mem_inf.1 hz).1, hpt.opp]
  have hnorm : lBar ⊥ V hV L ⊓ MulAction.stabilizer (MulAut (Vtil ⊥ V hV))
        (close16Vec V hV z (Subgroup.mem_inf.1 hz).1) ≤
      normalizer ((barSub ⊥ V hV B : Subgroup (MulAut (Vtil ⊥ V hV))) :
        Set (MulAut (Vtil ⊥ V hV))) := by
    rw [← hX]
    exact close16_barSub_le_normalizer hBs hXB
  have hBL : barSub ⊥ V hV B ≤ lBar ⊥ V hV L :=
    (barSub_mono ⊥ V hV hBY).trans hY.bar_eq.le
  have h3' : ¬ 3 ∣ Nat.card ↥(barSub ⊥ V hV B) := fun h =>
    h3 (h.trans (close16_card_barSub_dvd hM (hBY.trans hY.le)))
  exact close16_isPGroup_of_barSub hM hY hBY
    (close16_threePrime_normalized hpt (close16_lbar_simple hS) hBL h3' hnorm)

theorem close16_alpha (hS : Close16Setting D V L hV) {Y : Subgroup G}
    (hY : Close16Pack D V L hV Y) {z : G} (hz : z ∈ V ⊓ centralizer (D.T : Set G))
    (hz1 : z ≠ 1) :
    ∀ A ∈ F09.Inv9' D.M (Opp 3 (Y ⊓ centralizer ({z} : Set G))) 3,
      ⁅A, Opp 3 (Y ⊓ centralizer ({z} : Set G))⁆ ≤ pCoreOf 2 A := by
  intro A hA
  obtain ⟨hAM, h3, hXA⟩ := hA
  have hXY : Opp 3 (Y ⊓ centralizer ({z} : Set G)) ≤ Y :=
    (close16_opp_le 3 _).trans inf_le_left
  have hcomm : ⁅A, Opp 3 (Y ⊓ centralizer ({z} : Set G))⁆ ≤ A ⊓ Y := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    have hxY : x ∈ Y := hXY hx
    have hxA : x * a⁻¹ * x⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.1 (hXA hx) a⁻¹).1 (A.inv_mem ha)
    have hax : a * x * a⁻¹ ∈ Y :=
      hY.normal.conj_mem ⟨x, hY.le hxY⟩ hxY ⟨a, hAM ha⟩
    refine ⟨?_, ?_⟩
    · have : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by group
      rw [this]
      exact A.mul_mem ha hxA
    · have : ⁅a, x⁆ = (a * x * a⁻¹) * x⁻¹ := by group
      rw [this]
      exact Y.mul_mem hax (Y.inv_mem hxY)
  have hXB : Opp 3 (Y ⊓ centralizer ({z} : Set G)) ≤ normalizer ((A ⊓ Y : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.1 (hXA hx) y
    have h2 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (hXY hx)) y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  have h3B : ¬ 3 ∣ Nat.card ↥(A ⊓ Y) := fun h =>
    h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have h2 := close16_normalized_three_prime hS hY hz hz1 inf_le_right h3B hXB
  exact hcomm.trans (close16_inf_le_pCoreOf hAM hY.normal h2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
