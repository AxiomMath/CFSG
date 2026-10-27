module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteen
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.UC22P22so
import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyNine
import CFSG.LocalAnalysis.UniquenessCase.UC22K108Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem quot_transfer_of_star {H M T B : Subgroup G} (Q : Subgroup ↥H) [Q.Normal]
    (hQM : ∀ h : ↥H, h ∈ Q → (h : G) ∈ M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T H)
    (hBH : B ≤ H) (hBT : B ≤ normalizer (T : Set G)) {p : ℕ} (hp : p.Prime)
    (hBp : Nat.card B = p) (hBQ : ¬ B.subgroupOf H ≤ Q) (hTM : T ≤ M) (hBM : B ≤ M)
    (hstar : ∀ g ∈ H, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((T.subgroupOf H).map (QuotientGroup.mk' Q)) ⊤ ∧
      (B.subgroupOf H).map (QuotientGroup.mk' Q) ≤
        normalizer (((T.subgroupOf H).map (QuotientGroup.mk' Q) : Subgroup (↥H ⧸ Q)) :
          Set (↥H ⧸ Q)) ∧
      Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' Q)) = p ∧
      (T.subgroupOf H).map (QuotientGroup.mk' Q) ≤ (M.subgroupOf H).map (QuotientGroup.mk' Q) ∧
      (B.subgroupOf H).map (QuotientGroup.mk' Q) ≤ (M.subgroupOf H).map (QuotientGroup.mk' Q) ∧
      ∀ g : ↥H ⧸ Q, (∀ b ∈ (B.subgroupOf H).map (QuotientGroup.mk' Q),
        g⁻¹ * b * g ∈ (M.subgroupOf H).map (QuotientGroup.mk' Q)) →
          g ∈ (M.subgroupOf H).map (QuotientGroup.mk' Q) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπs : Function.Surjective (QuotientGroup.mk' Q) := QuotientGroup.mk'_surjective _
  have hmemM : ∀ h : ↥H, QuotientGroup.mk' Q h ∈ (M.subgroupOf H).map (QuotientGroup.mk' Q) ↔
      (h : G) ∈ M := by
    intro h
    have hker : (QuotientGroup.mk' Q).ker ≤ M.subgroupOf H := by
      rw [QuotientGroup.ker_mk']
      exact fun x hx => Subgroup.mem_subgroupOf.2 (hQM x hx)
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self (f := QuotientGroup.mk' Q) hker,
      Subgroup.mem_subgroupOf]
  have hTH : T ≤ H := hT.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf H) ⊤ := by
      rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H]
      have htopH : (⊤ : Subgroup ↥H).map H.subtype = H := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
      rw [htopH, Subgroup.map_subgroupOf_eq_of_le hTH]
      exact hT
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_isSylowOf_map_top hπs hT'
  · have hBT' : B.subgroupOf H ≤ normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro t
      have hbN := Subgroup.mem_normalizer_iff.1 (hBT (Subgroup.mem_subgroupOf.1 hb)) (t : G)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hbN
    exact (Subgroup.map_mono hBT').trans (Subgroup.le_normalizer_map _)
  · obtain ⟨b₀, hb₀B, hb₀Q⟩ := SetLike.not_le_iff_exists.1 hBQ
    have hcard : Nat.card (B.subgroupOf H) = p := by
      rw [← hBp]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
    have hdvd' : Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' Q)) ∣ p := by
      have := Subgroup.card_map_dvd (B.subgroupOf H) (QuotientGroup.mk' Q)
      rwa [hcard] at this
    rcases (Nat.dvd_prime hp).1 hdvd' with h1 | h1
    · exfalso
      have hmem : QuotientGroup.mk' Q b₀ ∈ (B.subgroupOf H).map (QuotientGroup.mk' Q) :=
        ⟨b₀, hb₀B, rfl⟩
      rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot] at hmem
      exact hb₀Q ((QuotientGroup.eq_one_iff b₀).1 hmem)
    · exact h1
  · exact Subgroup.map_mono fun t ht =>
      Subgroup.mem_subgroupOf.2 (hTM (Subgroup.mem_subgroupOf.1 ht))
  · exact Subgroup.map_mono fun b hb =>
      Subgroup.mem_subgroupOf.2 (hBM (Subgroup.mem_subgroupOf.1 hb))
  · intro g hg
    obtain ⟨h, rfl⟩ := hπs g
    refine (hmemM h).2 (hstar (h : G) h.2 fun b hb => ?_)
    have hbH : b ∈ H := hBH hb
    have h1 := hg (QuotientGroup.mk' Q ⟨b, hbH⟩) ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
    have h2 : QuotientGroup.mk' Q (h⁻¹ * ⟨b, hbH⟩ * h) ∈
        (M.subgroupOf H).map (QuotientGroup.mk' Q) := by
      rw [map_mul, map_mul, map_inv]
      exact h1
    exact (hmemM _).1 h2

theorem uc2_10_7w_of_c (h7c : UC2_10_7c) : UC2_10_7w G := by
  intro hK s p H M T B X Y hs hp hdvd hHtop hTsyl hBH hBT hBp hTM hBM hYM _hYmax hstar hYX hXH
    hYn hXn hXM hHMX hXmin hab
  classical
  have hYH : Y ≤ H := hYX.trans hXH
  have hTH : T ≤ H := hTsyl.le
  have hYN : (Y.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).2 hYn
  have hXN : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).2 hXn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥H →* ↥H ⧸ Y.subgroupOf H := QuotientGroup.mk' (Y.subgroupOf H)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπ1 : ∀ h : ↥H, π h = 1 ↔ (h : G) ∈ Y := fun h => by
    show QuotientGroup.mk' (Y.subgroupOf H) h = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmemM : ∀ h : ↥H, π h ∈ (M.subgroupOf H).map π ↔ (h : G) ∈ M := by
    intro h
    have hker : (QuotientGroup.mk' (Y.subgroupOf H)).ker ≤ M.subgroupOf H := by
      rw [QuotientGroup.ker_mk']
      exact fun x hx => Subgroup.mem_subgroupOf.2 (hYM (Subgroup.mem_subgroupOf.1 hx))
    show QuotientGroup.mk' (Y.subgroupOf H) h ∈
      (M.subgroupOf H).map (QuotientGroup.mk' (Y.subgroupOf H)) ↔ (h : G) ∈ M
    rw [← Subgroup.mem_comap,
      Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (Y.subgroupOf H)) hker,
      Subgroup.mem_subgroupOf]
  let Mb : Subgroup (↥H ⧸ Y.subgroupOf H) := (M.subgroupOf H).map π
  let Tb : Subgroup (↥H ⧸ Y.subgroupOf H) := (T.subgroupOf H).map π
  let Bb : Subgroup (↥H ⧸ Y.subgroupOf H) := (B.subgroupOf H).map π
  let Xb : Subgroup (↥H ⧸ Y.subgroupOf H) := (X.subgroupOf H).map π
  have hBY : ¬ B ≤ Y := by
    intro hBY
    apply hXM
    intro x hx
    refine hstar x (hXH hx) fun b hb => hYM ?_
    have hxinv : x⁻¹ ∈ normalizer (Y : Set G) := hYn (H.inv_mem (hXH hx))
    have := (Subgroup.mem_normalizer_iff.1 hxinv b).1 (hBY hb)
    simpa using this
  have hBQ : ¬ B.subgroupOf H ≤ Y.subgroupOf H := by
    intro hle
    apply hBY
    intro b hb
    have hmem : (⟨b, hBH hb⟩ : ↥H) ∈ B.subgroupOf H := hb
    exact Subgroup.mem_subgroupOf.mp (hle hmem)
  obtain ⟨hTb, hBTb, hBbp, hTMb, hBMb, hstarb⟩ :=
    quot_transfer_of_star (Y.subgroupOf H) (fun h hh => hYM (Subgroup.mem_subgroupOf.1 hh))
      hTsyl hBH hBT hp hBp hBQ hTM hBM hstar
  have hXbN : Xb.Normal := hXN.map π hπs
  have hXbmin : ∀ W : Subgroup (↥H ⧸ Y.subgroupOf H), W.Normal → W ≤ Xb →
      W = ⊥ ∨ W = Xb := by
    intro W hWn hWX
    let W' : Subgroup G := (W.comap π).map H.subtype
    have hW'H : W' ≤ H := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hW'sub : W'.subgroupOf H = W.comap π :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hYW' : Y ≤ W' := by
      intro y hy
      refine ⟨⟨y, hYH hy⟩, ?_, rfl⟩
      show π ⟨y, hYH hy⟩ ∈ W
      rw [(hπ1 _).2 hy]
      exact W.one_mem
    have hW'X : W' ≤ X := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨x, hx, hxw⟩ := hWX hw
      have h1 : π (x⁻¹ * w) = 1 := by rw [map_mul, map_inv, hxw, inv_mul_cancel]
      have h2 : (x : G)⁻¹ * (w : G) ∈ Y := (hπ1 _).1 h1
      have h3 : (x : G) ∈ X := Subgroup.mem_subgroupOf.1 hx
      have h4 := X.mul_mem h3 (hYX h2)
      rwa [mul_inv_cancel_left] at h4
    have hW'n : H ≤ normalizer (W' : Set G) := by
      have : (W'.subgroupOf H).Normal := by
        rw [hW'sub]
        exact hWn.comap π
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hW'H).1 this
    rcases hXmin W' hYW' hW'X hW'n with hW | hW
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨h, rfl⟩ := hπs w
      have hhW : (h : G) ∈ W' := ⟨h, hw, rfl⟩
      rw [hW] at hhW
      exact Subgroup.mem_bot.2 ((hπ1 h).2 hhW)
    · right
      refine le_antisymm hWX ?_
      rintro _ ⟨x, hx, rfl⟩
      have hxW' : (x : G) ∈ W' := by
        rw [hW]
        exact Subgroup.mem_subgroupOf.1 hx
      obtain ⟨w, hw, hwx⟩ := hxW'
      have hwx' : w = x := Subtype.ext hwx
      rw [← hwx']
      exact hw
  have hXbM : ¬ Xb ≤ Mb := by
    intro hle
    apply hXM
    intro x hx
    exact (hmemM ⟨x, hXH hx⟩).1 (hle ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩)
  have hsup : Mb ⊔ Xb = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨h, rfl⟩ := hπs q
    have hHM : H ⊓ M ≤ normalizer (X : Set G) := inf_le_left.trans hXn
    have hh : (h : G) ∈ (((H ⊓ M) ⊔ X : Subgroup G) : Set G) := hHMX h.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHM] at hh
    obtain ⟨m, hm, x, hx, hmx⟩ := hh
    have hmH : m ∈ H := hm.1
    have hxH : x ∈ H := hXH hx
    have hhmx : h = ⟨m, hmH⟩ * ⟨x, hxH⟩ := Subtype.ext hmx.symm
    rw [hhmx, map_mul]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ⟨⟨m, hmH⟩, Subgroup.mem_subgroupOf.2 hm.2, rfl⟩)
      (Subgroup.mem_sup_right ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩)
  have hXbab : ⁅Xb, Xb⁆ ≠ ⊥ := by
    intro hbot
    apply hab
    rw [Subgroup.commutator_le]
    intro x hx x' hx'
    have h1 : π ⁅(⟨x, hXH hx⟩ : ↥H), ⟨x', hXH hx'⟩⁆ ∈ ⁅Xb, Xb⁆ := by
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ⟨_, Subgroup.mem_subgroupOf.2 hx, rfl⟩
        ⟨_, Subgroup.mem_subgroupOf.2 hx', rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (hπ1 _).1 h1
  have key := h7c (↥H ⧸ Y.subgroupOf H) ((hK.isKGroup H hHtop).quotient (Y.subgroupOf H)) s p
    Mb Tb Bb Xb hs hp hdvd hTb hBTb hBbp hTMb hBMb hstarb hXbN hXbmin hXbM hsup hXbab
  intro c hc x hx
  have hcomm : ⁅T, B⁆ = ⁅T.subgroupOf H, B.subgroupOf H⁆.map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hTH,
      Subgroup.map_subgroupOf_eq_of_le hBH]
  rw [hcomm] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  have hc'b : π c' ∈ ⁅Tb, Bb⁆ := by
    show π c' ∈ ⁅(T.subgroupOf H).map π, (B.subgroupOf H).map π⁆
    rw [← Subgroup.map_commutator]
    exact ⟨c', hc', rfl⟩
  have hcent := key hc'b
  rw [Subgroup.mem_centralizer_iff] at hcent
  have h1 := hcent (π ⟨x, hXH hx⟩) ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have h2 : π ⁅(⟨x, hXH hx⟩ : ↥H), c'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h1
  exact (hπ1 _).1 h2

theorem not_le_of_minimal_normal {M X L : Subgroup G} (hXn : X.Normal)
    (hXmin : ∀ W : Subgroup G, W.Normal → W ≤ X → W = ⊥ ∨ W = X) (hXM : ¬ X ≤ M)
    (hMX : M ⊔ X = ⊤) (hLX : L ≤ X) (hXL : X ≤ normalizer (L : Set G)) (hL : L ≠ ⊥) :
    ¬ L ≤ M := by
  intro hLM
  have := hXn
  have hLcore : L ≤ M.normalCore := by
    intro l hl
    show ∀ g : G, g * l * g⁻¹ ∈ M
    intro g
    have hg : g ∈ ((M ⊔ X : Subgroup G) : Set G) := by
      rw [hMX]
      exact Subgroup.mem_top g
    rw [Subgroup.mul_normal M X] at hg
    obtain ⟨m, hm, x, hx, rfl⟩ := hg
    have hxl : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hXL hx) l).1 hl
    have e : m * x * l * (m * x)⁻¹ = m * (x * l * x⁻¹) * m⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hm (hLM hxl)) (M.inv_mem hm)
  have : M.normalCore.Normal := Subgroup.normalCore_normal M
  rcases hXmin (M.normalCore ⊓ X) (Subgroup.normal_inf_normal _ _) inf_le_right with h | h
  · apply hL
    rw [eq_bot_iff]
    intro l hl
    rw [← h]
    exact Subgroup.mem_inf.2 ⟨hLcore hl, hLX hl⟩
  · apply hXM
    rw [← h]
    exact inf_le_left.trans (Subgroup.normalCore_le M)

theorem isComponentOf_top_of_simple {X L : Subgroup G} (hXn : X.Normal) (hLX : L ≤ X)
    (hXL : X ≤ normalizer (L : Set G)) (hLs : IsSimpleGroup ↥L)
    (hLnab : ∃ a b : ↥L, a * b ≠ b * a) : CFSG.Open.IsComponentOf L ⊤ := by
  have := hLs
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hLnab).1
  refine ⟨le_top, ?_, ⟨hq.1.commutator_eq_top, hq.2.1⟩⟩
  have hLXn : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hXL
  have hXtop : (X.subgroupOf ⊤).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2
      (Subgroup.normalizer_eq_top_iff.2 hXn).ge
  exact CFSG.Open.IsSubnormal.step hLX hLXn
    (CFSG.Open.IsSubnormal.step le_top hXtop (CFSG.Open.IsSubnormal.refl ⊤))

theorem isSylowOf_inf_normalizer_sup {T X L B : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hXn : X.Normal) (hLX : L ≤ X)
    (hXL : X ≤ normalizer (L : Set G)) (hBL : B ≤ normalizer (L : Set G))
    (hBT : B ≤ normalizer (T : Set G)) (hBodd : Odd (Nat.card B)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ normalizer (L : Set G))
      (L ⊔ (T ⊓ normalizer (L : Set G)) ⊔ B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTX := hT.inf_of_le_normalizer (le_top : X ≤ ⊤) (Subgroup.normalizer_eq_top_iff.2 hXn).ge
  have hTXL := hTX.inf_of_le_normalizer hLX hXL
  have hidxL := (CFSG.ABGLocalTools.isSylowOf_iff.1 hTXL).2.2
  have e2 : T ⊓ normalizer (L : Set G) ⊓ L = T ⊓ X ⊓ L := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxT, -⟩, hxL⟩
      exact ⟨⟨hxT, hLX hxL⟩, hxL⟩
    · rintro ⟨⟨hxT, -⟩, hxL⟩
      exact ⟨⟨hxT, Subgroup.le_normalizer hxL⟩, hxL⟩
  have hTLL : T ⊓ normalizer (L : Set G) ≤ normalizer (L : Set G) := inf_le_right
  have hBTL : B ≤ normalizer ((T ⊓ normalizer (L : Set G) : Subgroup G) : Set G) :=
    (le_inf hBT (hBL.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hBP : B ≤ normalizer ((L ⊔ (T ⊓ normalizer (L : Set G)) : Subgroup G) : Set G) :=
    (le_inf hBL hBTL).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_sup_right.trans le_sup_left, hT.isPGroup.to_le inf_le_left, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right le_sup_left]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
  · have hP : L.relIndex (L ⊔ (T ⊓ normalizer (L : Set G))) =
        L.relIndex (T ⊓ normalizer (L : Set G)) := by
      rw [sup_comm]
      exact CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hTLL
    have h3 := Subgroup.relIndex_mul_relIndex (T ⊓ normalizer (L : Set G) ⊓ L)
      (T ⊓ normalizer (L : Set G)) (L ⊔ (T ⊓ normalizer (L : Set G))) inf_le_left le_sup_right
    have h4 := Subgroup.relIndex_mul_relIndex (T ⊓ normalizer (L : Set G) ⊓ L) L
      (L ⊔ (T ⊓ normalizer (L : Set G))) inf_le_right le_sup_left
    rw [Subgroup.inf_relIndex_left] at h3
    rw [hP] at h4
    have hne : L.relIndex (T ⊓ normalizer (L : Set G)) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h5 : (T ⊓ normalizer (L : Set G)).relIndex (L ⊔ (T ⊓ normalizer (L : Set G))) =
        (T ⊓ normalizer (L : Set G) ⊓ L).relIndex L := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne)
      rw [h3, ← h4, mul_comm]
    rw [h5, e2] at h
    exact hidxL h
  · rw [sup_comm (L ⊔ (T ⊓ normalizer (L : Set G))) B,
      CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hBP] at h
    exact (Nat.not_even_iff_odd.2 hBodd)
      (even_iff_two_dvd.2 (h.trans (Subgroup.relIndex_dvd_card _ _)))

theorem centralizer_inf_le_of_star {M T L B : Subgroup G} (hLs : IsSimpleGroup ↥L)
    (hLnab : ∃ a b : ↥L, a * b ≠ b * a) (hTL : T ≤ normalizer (L : Set G))
    (hBL : B ≤ normalizer (L : Set G)) (hBT : B ≤ normalizer (T : Set G))
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (L ⊔ T ⊔ B)) (hTM : T ≤ M) (hBM : B ≤ M)
    (hstar : ∀ g : G, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) :
    centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hLs
  have hNL : L ⊔ T ⊔ B ≤ normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hTL) hBL
  have hBP : B ≤ normalizer ((L ⊔ T : Subgroup G) : Set G) :=
    (le_inf hBL hBT).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPN : L ⊔ T ⊔ B ≤ normalizer ((L ⊔ T : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer hBP
  have hCN : L ⊔ T ⊔ B ≤
      normalizer ((centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) : Subgroup G) : Set G) :=
    (le_inf (fun g hg => UC22.P22so.mem_normalizer_centralizer_of (hNL hg))
      Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hZ : Subgroup.center ↥L = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hLnab).2
  have hCL : ∀ x ∈ centralizer (L : Set G), x ∈ L → x = 1 := by
    intro x hxC hxL
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hC₀L : L ⊓ (centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, ⟨hxC, -⟩, -⟩ := hx
    exact Subgroup.mem_bot.2 (hCL x hxC hxL)
  have hC₀n : centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T) ≤ normalizer (L : Set G) :=
    inf_le_left.trans (inf_le_right.trans hNL)
  have hC₀p : IsPGroup 2 ↥(centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T)) := by
    have e1 : L.relIndex (centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T)) =
        Nat.card ↥(centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T)) := by
      have := Subgroup.relIndex_mul_card (H := L)
        (K := centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T))
      rwa [hC₀L, Subgroup.card_bot, mul_one] at this
    have e2 := CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hC₀n
    have e3 : L.relIndex (L ⊔ T) = L.relIndex T := by
      rw [sup_comm]
      exact CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hTL
    have e4 := Subgroup.relIndex_mul_relIndex L
      (centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T) ⊔ L) (L ⊔ T) le_sup_right
      (sup_le inf_le_right le_sup_left)
    have hdvd : Nat.card ↥(centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T)) ∣ Nat.card ↥T := by
      rw [← e1, ← e2]
      refine (Dvd.intro _ e4).trans ?_
      rw [e3]
      exact Subgroup.relIndex_dvd_card _ _
    obtain ⟨k, hk⟩ := hTsyl.isPGroup.exists_card_eq
    rw [hk] at hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card hm
  have hC₀T : centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T) ≤ T :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.le_of_normal_isPGroup_of_isSylowOf hTsyl
      (inf_le_left.trans inf_le_right)
      ((le_inf hCN hPN).trans Subgroup.inf_normalizer_le_normalizer_inf) hC₀p
  intro c hc
  refine hstar c fun b hb => ?_
  have hmul : c⁻¹ ∈ (((L ⊔ T) ⊔ B : Subgroup G) : Set G) :=
    (L ⊔ T ⊔ B).inv_mem (Subgroup.mem_inf.1 hc).2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (L ⊔ T) B hBP] at hmul
  obtain ⟨x, hx, b', hb', hxb⟩ := hmul
  have hcomm : c⁻¹ * b * c * b⁻¹ ∈ centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ⊓ (L ⊔ T) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hc' : c⁻¹ ∈ centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) := Subgroup.inv_mem _ hc
      have hbN := hCN (Subgroup.mem_sup_right hb)
      have hbc : b * c * b⁻¹ ∈ centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) :=
        (Subgroup.mem_normalizer_iff.1 hbN c).1 hc
      have e : c⁻¹ * b * c * b⁻¹ = c⁻¹ * (b * c * b⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hc' hbc
    · have hc_eq : c = b'⁻¹ * x⁻¹ := by rw [← inv_inv c, ← hxb, mul_inv_rev]
      have hbb : b' * b * b'⁻¹ = b := by rw [hBc b' hb' b hb, mul_inv_cancel_right]
      have e : c⁻¹ * b * c * b⁻¹ = x * (b' * b * b'⁻¹) * x⁻¹ * b⁻¹ := by rw [hc_eq]; group
      rw [e, hbb]
      have hbx : b * x⁻¹ * b⁻¹ ∈ L ⊔ T :=
        (Subgroup.mem_normalizer_iff.1 (hBP hb) x⁻¹).1 ((L ⊔ T).inv_mem hx)
      have e' : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
      rw [e']
      exact (L ⊔ T).mul_mem hx hbx
  have e : c⁻¹ * b * c = (c⁻¹ * b * c * b⁻¹) * b := by group
  rw [e]
  exact M.mul_mem (hTM (hC₀T hcomm)) (hBM hb)

theorem commutator_le_centralizer_of_as (has : UC2_10_7as) (hK : CFSG.Open.IsKGroup G)
    {s p : ℕ} (hs : Odd s) (hp : p.Prime) (hdvd : p ∣ 2 ^ s - 1)
    {M T L B : Subgroup G} (hLs : IsSimpleGroup ↥L) (hLnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hLM : ¬ L ≤ M) (hTL : T ≤ normalizer (L : Set G)) (hBL : B ≤ normalizer (L : Set G))
    (hBT : B ≤ normalizer (T : Set G)) (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T (L ⊔ T ⊔ B))
    (hBp : Nat.card B = p) (hBC : ¬ B ≤ centralizer (L : Set G))
    (hCM : centralizer (L : Set G) ⊓ (L ⊔ T ⊔ B) ≤ M) (hTM : T ≤ M) (hBM : B ≤ M)
    (hstar : ∀ g : G, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) :
    ⁅T, B⁆ ≤ centralizer (L : Set G) := by
  classical
  have := hLs
  have hLN : L ≤ L ⊔ T ⊔ B := le_sup_left.trans le_sup_left
  have hTN : T ≤ L ⊔ T ⊔ B := le_sup_right.trans le_sup_left
  have hBN : B ≤ L ⊔ T ⊔ B := le_sup_right
  have hNL : L ⊔ T ⊔ B ≤ normalizer (L : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hTL) hBL
  have hLq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hLnab).1
  have hQn := CFSG.GroupTheory.quasisimpleActionKernel_normal (L ⊔ T ⊔ B) L hNL
  have hQeq := CFSG.GroupTheory.quasisimpleActionKernel_eq_centralizer (L ⊔ T ⊔ B) L hNL
  have hQM : ∀ h : ↥(L ⊔ T ⊔ B),
      h ∈ CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL → (h : G) ∈ M := by
    intro h hh
    rw [hQeq, Subgroup.mem_subgroupOf] at hh
    exact hCM ⟨hh, h.2⟩
  have hmemM : ∀ h : ↥(L ⊔ T ⊔ B), QuotientGroup.mk' (CFSG.GroupTheory.quasisimpleActionKernel
      (L ⊔ T ⊔ B) L hNL) h ∈ (M.subgroupOf (L ⊔ T ⊔ B)).map (QuotientGroup.mk'
      (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL)) ↔ (h : G) ∈ M := by
    intro h
    have hker : (QuotientGroup.mk' (CFSG.GroupTheory.quasisimpleActionKernel
        (L ⊔ T ⊔ B) L hNL)).ker ≤ M.subgroupOf (L ⊔ T ⊔ B) := by
      rw [QuotientGroup.ker_mk']
      exact fun x hx => Subgroup.mem_subgroupOf.2 (hQM x hx)
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq_self (f := QuotientGroup.mk'
      (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL)) hker,
      Subgroup.mem_subgroupOf]
  have hBQ : ¬ B.subgroupOf (L ⊔ T ⊔ B) ≤
      CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL := by
    intro hle
    apply hBC
    intro b hb
    have h1 := hle (show (⟨b, hBN hb⟩ : ↥(L ⊔ T ⊔ B)) ∈ B.subgroupOf (L ⊔ T ⊔ B) from hb)
    rw [hQeq, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨hTb, hBTb, hBbp, hTMb, hBMb, hstarb⟩ :=
    quot_transfer_of_star _ hQM hTsyl hBN hBT hp hBp hBQ hTM hBM (fun g _ => hstar g)
  have hLbn := CFSG.GroupTheory.quasisimple_normal_image (L ⊔ T ⊔ B) L hLN hNL
  have hLbs := CFSG.GroupTheory.quasisimple_isSimpleGroup_image (L ⊔ T ⊔ B) L hLN hNL hLq
  have hLbnab := CFSG.GroupTheory.quasisimple_nonabelian_image (L ⊔ T ⊔ B) L hLN hNL hLq
  have hLbC := CFSG.GroupTheory.quasisimple_centralizer_image_eq_bot (L ⊔ T ⊔ B) L hLN hNL hLq
  have := hLbs
  have hcat : CFSG.Open.IsCatalogGroup ↥((L.subgroupOf (L ⊔ T ⊔ B)).map
      (QuotientGroup.mk' (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL))) :=
    hK.isCatalogGroup_of_surjective L hLbnab
      (((QuotientGroup.mk' _).subgroupMap (L.subgroupOf (L ⊔ T ⊔ B))).comp
        (Subgroup.subgroupOfEquivOfLe hLN).symm.toMonoidHom)
      ((MonoidHom.subgroupMap_surjective _ _).comp
        (Subgroup.subgroupOfEquivOfLe hLN).symm.surjective)
  have hsup : (L.subgroupOf (L ⊔ T ⊔ B)).map (QuotientGroup.mk'
        (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL)) ⊔
      (T.subgroupOf (L ⊔ T ⊔ B)).map (QuotientGroup.mk'
        (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL)) ⊔
      (B.subgroupOf (L ⊔ T ⊔ B)).map (QuotientGroup.mk'
        (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL)) = ⊤ := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hLN hTN,
      ← Subgroup.subgroupOf_sup (sup_le hLN hTN) hBN, Subgroup.subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rcases has _ _ hLbn hLbs hLbnab hLbC hcat s p _ _ _ hs hp hdvd hTb hBTb hBbp hsup hTMb hBMb
    hstarb with h | h
  · exfalso
    apply hLM
    intro l hl
    have hmem := h ⟨⟨l, hLN hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
    exact (hmemM _).1 hmem
  · rw [Subgroup.commutator_le]
    intro t ht b hb
    have hmem : QuotientGroup.mk' (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL)
        ⁅(⟨t, hTN ht⟩ : ↥(L ⊔ T ⊔ B)), ⟨b, hBN hb⟩⁆ ∈
        ⁅(T.subgroupOf (L ⊔ T ⊔ B)).map (QuotientGroup.mk'
            (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL)),
          (B.subgroupOf (L ⊔ T ⊔ B)).map (QuotientGroup.mk'
            (CFSG.GroupTheory.quasisimpleActionKernel (L ⊔ T ⊔ B) L hNL))⁆ := by
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ⟨_, Subgroup.mem_subgroupOf.2 ht, rfl⟩
        ⟨_, Subgroup.mem_subgroupOf.2 hb, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hQ := (QuotientGroup.eq_one_iff _).1 hmem
    rw [hQeq, Subgroup.mem_subgroupOf] at hQ
    exact hQ

theorem uc2_10_7c_of_as (has : UC2_10_7as) : UC2_10_7c := by
  intro A _ _ hK s p M T B X hs hp hdvd hT hBT hBp hTM hBM hstar hXn hXmin hXM hMX hXab
  classical
  have := hXn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := PartTwo.s13_seven_le_of_dvd hs hp hdvd
  have hp2 : p ≠ 2 := by omega
  have hBcyc : IsCyclic ↥B := isCyclic_of_prime_card hBp
  obtain ⟨⟨b, hbB⟩, hgen⟩ := hBcyc.exists_generator
  have hBz : B = Subgroup.zpowers b := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨x, hx⟩)
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · exact (Subgroup.zpowers_le).2 hbB
  have hob : orderOf b = p := by
    rw [← hBp, hBz, Nat.card_zpowers]
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    rw [hBz] at hx hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_add, ← zpow_add, add_comm]
  have hCb : centralizer ({b} : Set A) ≤ M := by
    intro g hg
    refine hstar g fun b' hb' => ?_
    have hgb : Commute g b := (Subgroup.mem_centralizer_iff.1 hg b rfl).symm
    have hcomm : Commute g b' := by
      rw [hBz] at hb'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb'
      exact hgb.zpow_right k
    have e : g⁻¹ * b' * g = b' := by rw [mul_assoc, ← hcomm.eq, inv_mul_cancel_left]
    rw [e]
    exact hBM hb'
  have hconj : ∀ (L : Subgroup A) (g : A), L ≤ X → X ≤ normalizer (L : Set A) →
      IsSimpleGroup ↥L → (∃ a c : ↥L, a * c ≠ c * a) →
      L.map (MulAut.conj g).toMonoidHom ≤ X ∧
        X ≤ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup A) : Set A) ∧
        IsSimpleGroup ↥(L.map (MulAut.conj g).toMonoidHom) ∧
        ∃ a c : ↥(L.map (MulAut.conj g).toMonoidHom), a * c ≠ c * a := by
    intro L g hLX hXL hLs hLnab
    let e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
      L.equivMapOfInjective _ (MulAut.conj g).injective
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro _ ⟨l, hl, rfl⟩
      show g * l * g⁻¹ ∈ X
      exact hXn.conj_mem l (hLX hl) g
    · have hXX : X ≤ X.map (MulAut.conj g).toMonoidHom := by
        intro x hx
        refine ⟨g⁻¹ * x * g, by simpa using hXn.conj_mem x hx g⁻¹, ?_⟩
        show g * (g⁻¹ * x * g) * g⁻¹ = x
        group
      exact hXX.trans ((Subgroup.map_mono hXL).trans (Subgroup.le_normalizer_map _))
    · have := hLs
      exact MulEquiv.isSimpleGroup e.symm
    · obtain ⟨a, c, hac⟩ := hLnab
      exact ⟨e a, e c, fun h => hac (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hBN : ∀ L : Subgroup A, L ≤ X → X ≤ normalizer (L : Set A) → IsSimpleGroup ↥L →
      (∃ a c : ↥L, a * c ≠ c * a) → ¬ L ≤ M ∧ B ≤ normalizer (L : Set A) := by
    intro L hLX hXL hLs hLnab
    have hL1 : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).1 (by have := hLs; infer_instance)
    have hLM := not_le_of_minimal_normal hXn hXmin hXM hMX hLX hXL hL1
    refine ⟨hLM, ?_⟩
    have hcomp := isComponentOf_top_of_simple hXn hLX hXL hLs hLnab
    have hb := UC22.uc22p22r_free_orbit hp b hob hT hTM (hBM hbB) hCb hcomp hLM
    rw [hBz]
    exact (Subgroup.zpowers_le).2 hb
  have hRN : ∀ L : Subgroup A, L ≤ X → X ≤ normalizer (L : Set A) → IsSimpleGroup ↥L →
      (∃ a c : ↥L, a * c ≠ c * a) → ⁅T, B⁆ ≤ normalizer (L : Set A) := by
    intro L hLX hXL hLs hLnab
    rw [Subgroup.commutator_le]
    intro t _ b' hb'
    rw [commutatorElement_def]
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ ((hBN L hLX hXL hLs hLnab).2 hb'))
    obtain ⟨h1, h2, h3, h4⟩ := hconj L t⁻¹ hLX hXL hLs hLnab
    have hb'' := (hBN _ h1 h2 h3 h4).2 hb'
    have hmem : ∀ z, z ∈ L.map (MulAut.conj t⁻¹).toMonoidHom ↔ t * z * t⁻¹ ∈ L := by
      intro z
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e1 : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
    have e2 : t * (b' * (t⁻¹ * y * t) * b'⁻¹) * t⁻¹ = t * b' * t⁻¹ * y * (t * b' * t⁻¹)⁻¹ := by
      group
    calc y ∈ L ↔ t⁻¹ * y * t ∈ L.map (MulAut.conj t⁻¹).toMonoidHom := by rw [hmem, e1]
      _ ↔ b' * (t⁻¹ * y * t) * b'⁻¹ ∈ L.map (MulAut.conj t⁻¹).toMonoidHom :=
          Subgroup.mem_normalizer_iff.1 hb'' _
      _ ↔ t * b' * t⁻¹ * y * (t * b' * t⁻¹)⁻¹ ∈ L := by rw [hmem, e2]
  have hkey : ∀ L : Subgroup A, L ≤ X → X ≤ normalizer (L : Set A) → IsSimpleGroup ↥L →
      (∃ a c : ↥L, a * c ≠ c * a) → ⁅T, B⁆ ≤ centralizer (L : Set A) := by
    intro L hLX hXL hLs hLnab
    obtain ⟨hLM, hBL⟩ := hBN L hLX hXL hLs hLnab
    have hBodd : Odd (Nat.card B) := hBp ▸ hp.odd_of_ne_two hp2
    have hsyl := isSylowOf_inf_normalizer_sup hT hXn hLX hXL hBL hBT hBodd
    have hBTL : B ≤ normalizer ((T ⊓ normalizer (L : Set A) : Subgroup A) : Set A) :=
      (le_inf hBT (hBL.trans Subgroup.le_normalizer)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hTLM : T ⊓ normalizer (L : Set A) ≤ M := inf_le_left.trans hTM
    have hCM := centralizer_inf_le_of_star hLs hLnab inf_le_right hBL hBTL hBc hsyl hTLM hBM
      hstar
    have hBC : ¬ B ≤ centralizer (L : Set A) := by
      intro h
      apply hLM
      intro l hl
      apply hCb
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.1 (h hbB) l hl).symm
    have h1 := commutator_le_centralizer_of_as has hK hs hp hdvd hLs hLnab hLM inf_le_right hBL
      hBTL hsyl hBp hBC hCM hTLM hBM hstar
    have hRT : ⁅T, B⁆ ≤ T ⊓ normalizer (L : Set A) :=
      le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hBT) (hRN L hLX hXL hLs hLnab)
    have hBpg : IsPGroup p ↥B := IsPGroup.of_card (n := 1) (by rw [hBp, pow_one])
    have hT2 : ¬ p ∣ Nat.card T := by
      intro hdv
      obtain ⟨k, hk⟩ := hT.isPGroup.exists_card_eq
      rw [hk] at hdv
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdv))
    have hcc := CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq hp hBpg hBT hT2
    rw [← hcc]
    exact (Subgroup.commutator_mono hRT le_rfl).trans h1
  have hX1 : X ≠ ⊥ := by
    intro h
    apply hXab
    rw [h]
    exact Subgroup.commutator_bot_left _
  obtain ⟨r, S, hr, hSX, hSs, hSconj, hSn, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hXn hX1 hXmin
  have hXS : X ≤ normalizer ((S ⟨0, hr⟩ : Subgroup A) : Set A) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hSX ⟨0, hr⟩)).1 (hSn ⟨0, hr⟩)
  have hSnab : ∃ a c : ↥(S ⟨0, hr⟩), a * c ≠ c * a := by
    by_contra hcon
    push Not at hcon
    apply hXab
    have hSc : ∀ i, ∀ a c : ↥(S i), a * c = c * a := by
      rintro i ⟨a, ha⟩ ⟨c, hc⟩
      obtain ⟨g, hg⟩ := hSconj ⟨0, hr⟩ i
      rw [hg, CFSG.conjugate] at ha hc
      obtain ⟨a₀, ha₀, rfl⟩ := ha
      obtain ⟨c₀, hc₀, rfl⟩ := hc
      apply Subtype.ext
      show (MulAut.conj g⁻¹).toMonoidHom a₀ * (MulAut.conj g⁻¹).toMonoidHom c₀ =
        (MulAut.conj g⁻¹).toMonoidHom c₀ * (MulAut.conj g⁻¹).toMonoidHom a₀
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hcon ⟨a₀, ha₀⟩ ⟨c₀, hc₀⟩)
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hxy : (⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      apply e.symm.injective
      rw [map_mul, map_mul]
      funext i
      exact hSc i _ _
    exact congrArg Subtype.val hxy
  have hXcl : X = Subgroup.normalClosure ((S ⟨0, hr⟩ : Subgroup A) : Set A) := by
    have : (Subgroup.normalClosure ((S ⟨0, hr⟩ : Subgroup A) : Set A)).Normal :=
      Subgroup.normalClosure_normal
    rcases hXmin _ inferInstance (Subgroup.normalClosure_le_normal fun x hx => hSX ⟨0, hr⟩ hx)
      with h | h
    · exfalso
      have := hSs ⟨0, hr⟩
      have hne : S ⟨0, hr⟩ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
      apply hne
      rw [eq_bot_iff]
      intro x hx
      rw [← h]
      exact Subgroup.subset_normalClosure hx
    · exact h.symm
  rw [Subgroup.le_centralizer_iff, hXcl]
  show Subgroup.closure (Group.conjugatesOfSet _) ≤ _
  rw [Subgroup.closure_le]
  intro y hy
  rw [Group.mem_conjugatesOfSet_iff] at hy
  obtain ⟨x, hx, hc⟩ := hy
  rw [isConj_iff] at hc
  obtain ⟨c, rfl⟩ := hc
  obtain ⟨h1, h2, h3, h4⟩ := hconj (S ⟨0, hr⟩) c (hSX ⟨0, hr⟩) hXS (hSs ⟨0, hr⟩) hSnab
  have hR := hkey _ h1 h2 h3 h4
  rw [Subgroup.le_centralizer_iff] at hR
  exact hR ⟨x, hx, rfl⟩

section Assembly



theorem uc2_10_7as_of_inputs (hK101 : UC22.F10.K101) (hK105 : UC22.F10.K105)
    (hcat : S19.K_CatalogModels) (hTits : S19.K_TitsOddPrimes)
    (hKA : UC22.KLieBorelAutPrime) (hKA2 : KLieBorelAutPrimeRank2) (hJ1 : UC2_10_7J1)
    (hOdd : UC2_10_7Odd) : UC2_10_7as := by
  intro A _ _ L hLn hLs hLnab hCL hLcat s p T B M hs hp hdvd hT hBT hBp hsup hTM hBM hstar
  classical
  have := hLn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp7 : 7 ≤ p := PartTwo.s13_seven_le_of_dvd hs hp hdvd
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hBprime : (Nat.card B).Prime := hBp ▸ hp
  have hBodd : Odd (Nat.card B) := hBp ▸ hpodd
  have hFstar : CFSG.Open.genFittingFStar A = L := UC22.uc22p22r_fstar_eq hLs hLnab hCL
  have hperm : UC22.Permutes B T := by
    show (B : Set A) * (T : Set A) = (T : Set A) * (B : Set A)
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B T hBT,
      ← Subgroup.coe_mul_of_right_le_normalizer_left T B hBT, sup_comm]
  have : Fact (Nat.card B).Prime := ⟨hBprime⟩
  have hcyc : IsCyclic ↥B := isCyclic_of_prime_card (p := Nat.card B) rfl
  have hHyp : UC22.F10.Hyp10 T B := ⟨hT, inferInstance, hBodd, hperm, fun q hq _ =>
    (CFSG.SectionRank.pRank_le_one_of_isCyclic hq hcyc).trans (by norm_num)⟩
  have hB3 : ¬ IsPGroup 3 ↥B := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := h3.exists_card_eq
    rw [hBp] at hk
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact hp.one_lt.ne' hk
    · have h3p : 3 ∣ p := hk ▸ dvd_pow_self 3 (Nat.succ_ne_zero k)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p
      omega
  rcases CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm.catalog_trichotomy hLcat hLnab
    with halt | ⟨rL, hLie⟩ | ⟨sp, hSpor⟩
  ·
    obtain ⟨n, hn, ⟨e⟩⟩ := halt
    exact (hB3 (hK101 A T B hHyp (by rw [hFstar]; exact ⟨n, ⟨e⟩⟩))).elim
  · have hchev : UC22.IsChev ↥L rL := hcat.1 ↥L rL hLie
    have hprime : rL.Prime := by
      obtain ⟨idx, -, hidx⟩ := hLie
      exact hidx ▸ idx.1.characteristic_prime
    by_cases hr2 : rL = 2
    · subst hr2
      obtain ⟨t, m, f, hadm, hmod⟩ := hchev
      by_cases hf : 2 ≤ f
      ·
        exact Or.inl (UC22.F10.k108Norm_holds A L hLn hLs (Or.inl ⟨f, hf, t, m, hadm, hmod⟩)
          T B M hT hBprime hBodd hBT hTM hBM hstar)
      have hf1 : f = 1 := by have := hadm.2.1; omega
      subst hf1
      by_cases htits : t = .Tits
      ·
        subst htits
        exfalso
        have hm0 : m = 0 := hadm.2.2.1
        subst hm0
        have hT' : UC22.F10.IsTits10 ↥(CFSG.Open.genFittingFStar A) := by
          rw [hFstar]
          exact hmod
        have hCstar : centralizer (CFSG.Open.genFittingFStar A : Set A) = ⊥ := by
          rw [hFstar]
          exact hCL
        have hpA : p ∣ Nat.card A := hBp ▸ Subgroup.card_subgroup_dvd_card B
        rcases hTits A hT' hCstar p hp (by omega) hpA with h | h | h
        · omega
        · omega
        · subst h
          exact S19.not_thirteen_dvd_two_pow_sub_one_of_odd hs hdvd
      by_cases hd4 : t = .trialityD4
      ·
        subst hd4
        have hm0 : m = 0 := hadm.2.2
        subst hm0
        exact Or.inl (UC22.F10.k108Norm_holds A L hLn hLs (Or.inr hmod) T B M hT hBprime
          hBodd hBT hTM hBM hstar)
      exfalso
      have hBne : B ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hBp
        omega
      obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := (Subgroup.bot_or_exists_ne_one B).resolve_left hBne
      let α : MulAut ↥L := MulAut.conjNormal b
      have hα1 : α ≠ 1 := by
        intro h1
        apply hb1
        have hbC : b ∈ centralizer (L : Set A) := by
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : A)) h1
          simp only [α, MulAut.conjNormal_apply, MulAut.one_apply] at h2
          rw [mul_inv_eq_iff_eq_mul] at h2
          exact h2.symm
        rw [hCL] at hbC
        exact Subgroup.mem_bot.1 hbC
      have hαp : α ^ p = 1 := by
        have hbp : b ^ p = 1 := by
          have h := pow_card_eq_one' (G := ↥B) (x := ⟨b, hbB⟩)
          rw [hBp] at h
          have h' := congrArg Subtype.val h
          simpa using h'
        show (MulAut.conjNormal b) ^ p = 1
        rw [← map_pow, hbp, map_one]
      let U : Subgroup ↥L := T.subgroupOf L
      have hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ := by
        have hTL := hT.inf_of_le_normalizer (le_top : L ≤ ⊤)
          (Subgroup.normalizer_eq_top (H := L)).ge
        obtain ⟨-, -, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hTL
        refine ⟨le_top, hT.isPGroup.comap_subtype, ?_⟩
        rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right U]
        rw [Subgroup.inf_relIndex_right] at hidx
        exact hidx
      have hUle : U.map α.toMonoidHom ≤ U := by
        rintro _ ⟨u, hu, rfl⟩
        have hu' : (u : A) ∈ T := hu
        show ((MulAut.conjNormal b u : ↥L) : A) ∈ T
        rw [MulAut.conjNormal_apply]
        exact (Subgroup.mem_normalizer_iff.1 (hBT hbB) u).1 hu'
      have hUα : U.map α.toMonoidHom = U :=
        Subgroup.eq_of_le_of_card_ge hUle
          (Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective).ge
      by_cases hrk : 3 ≤ PartTwo.S17.CS17LieRank t m
      ·
        have h := (hKA ↥L t m 1 hadm hmod hrk U hU p hp (by omega)
          (fun h => by have := Nat.le_of_dvd one_pos h; omega) α hα1 hαp hUα).1
        norm_num at h
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
        omega
      ·
        exact hα1 (hKA2 ↥L t m hadm hmod (by omega) hd4 htits U hU s p hs hp hp7 hdvd α hαp hUα)
    ·
      exact hOdd A L hLn hLs hCL rL hprime hr2 hchev s p T B M hs hp hdvd hT hBT hBp hsup hTM
        hBM hstar
  ·
    rcases hK105 A T B hHyp (by rw [hFstar]; exact ⟨sp, hcat.2 ↥L sp hSpor⟩) with h3 | ⟨hJ, h7⟩
    · exact (hB3 h3).elim
    · left
      rw [hJ1 A hJ T B M hT hBT h7 hTM hBM hstar]
      exact le_top

theorem uc2_10_7w_of_inputs (hK101 : UC22.F10.K101) (hK105 : UC22.F10.K105)
    (hcat : S19.K_CatalogModels) (hTits : S19.K_TitsOddPrimes)
    (hKA : UC22.KLieBorelAutPrime) (hKA2 : KLieBorelAutPrimeRank2) (hJ1 : UC2_10_7J1)
    (hOdd : UC2_10_7Odd) : UC2_10_7w G :=
  uc2_10_7w_of_c (uc2_10_7c_of_as
    (uc2_10_7as_of_inputs hK101 hK105 hcat hTits hKA hKA2 hJ1 hOdd))

end Assembly

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
