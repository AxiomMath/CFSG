module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDQT
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def yConj (V H : Subgroup G) {X : Type} [Group X] (φ : ↥(conjClosure V H) →* X)
    (x : ↥(conjClosure V H)) : Subgroup X :=
  conjSubgroup (SevenK.barSub (conjClosure V H) φ V) (φ x)

@[expose] def conjPairSub (V₀ : Subgroup G) (x y : G) : Subgroup G :=
  conjSubgroup V₀ x ⊔ conjSubgroup V₀ y

private theorem w16q_conjSubgroup_comm {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (x : G) :
    ∀ a ∈ conjSubgroup A x, ∀ b ∈ conjSubgroup B x, a * b = b * a := by
  intro a ha b hb
  have ha' : x * a * x⁻¹ ∈ A := mem_conjSubgroup_iff.mp ha
  have hb' : x * b * x⁻¹ ∈ B := mem_conjSubgroup_iff.mp hb
  have hcomm := h (x * a * x⁻¹) ha' (x * b * x⁻¹) hb'
  calc a * b = x⁻¹ * ((x * a * x⁻¹) * (x * b * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * b * x⁻¹) * (x * a * x⁻¹)) * x := by rw [hcomm]
    _ = b * a := by group

private theorem w16q_barSub_comm {K : Subgroup G} {X : Type} [Group X] (φ : ↥K →* X)
    {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    ∀ a ∈ SevenK.barSub K φ A, ∀ b ∈ SevenK.barSub K φ B, a * b = b * a := by
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := SevenK.mem_barSub.mp ha
  obtain ⟨b', hb', rfl⟩ := SevenK.mem_barSub.mp hb
  have hcomm : (a' : G) * (b' : G) = (b' : G) * (a' : G) := h (a' : G) ha' (b' : G) hb'
  calc φ a' * φ b' = φ (a' * b') := (map_mul φ a' b').symm
    _ = φ (b' * a') := by rw [show a' * b' = b' * a' from Subtype.ext hcomm]
    _ = φ b' * φ a' := map_mul φ b' a'

namespace DichCfg

variable {M V₀ V U S H : Subgroup G} {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}

theorem conj_V₀_eq_iff (d : DichCfg M V₀ V U S H φ) (x y : ↥(conjClosure V H)) :
    conjSubgroup V₀ (x : G) = conjSubgroup V₀ (y : G) ↔ yConj V H φ x = yConj V H φ y := by
  constructor
  · intro hxy
    have hV0g : conjSubgroup V₀ ((x : G) * (y : G)⁻¹) = V₀ := by
      calc conjSubgroup V₀ ((x : G) * (y : G)⁻¹)
          = conjSubgroup (conjSubgroup V₀ (x : G)) ((y : G)⁻¹) :=
            (conjSubgroup_conjSubgroup V₀ (x : G) ((y : G)⁻¹)).symm
        _ = conjSubgroup (conjSubgroup V₀ (y : G)) ((y : G)⁻¹) := by rw [hxy]
        _ = V₀ := conjSubgroup_conjSubgroup_inv V₀ (y : G)
    have hxyM : (x : G) * (y : G)⁻¹ ∈ M := by
      have hN : (x : G) * (y : G)⁻¹ ∈ normalizer (V₀ : Set G) :=
        conjSubgroup_eq_iff_mem_normalizer.1 hV0g
      rwa [d.cfg.cex.hyp.normalizer₀] at hN
    have hVg : conjSubgroup V ((x : G) * (y : G)⁻¹) = V := by
      apply conjSubgroup_eq_iff_mem_normalizer.2
      rw [d.cfg.cex.hyp.h6.normalizer_eq]
      exact hxyM
    have hVxy : conjSubgroup V (x : G) = conjSubgroup V (y : G) := by
      calc conjSubgroup V (x : G)
          = conjSubgroup V (((x : G) * (y : G)⁻¹) * (y : G)) := by
            rw [show ((x : G) * (y : G)⁻¹) * (y : G) = (x : G) by group]
        _ = conjSubgroup (conjSubgroup V ((x : G) * (y : G)⁻¹)) (y : G) :=
            (conjSubgroup_conjSubgroup V ((x : G) * (y : G)⁻¹) (y : G)).symm
        _ = conjSubgroup V (y : G) := by rw [hVg]
    have h1 : yConj V H φ x =
        SevenK.barSub (conjClosure V H) φ (conjSubgroup V (x : G)) :=
      (barSub_conjSubgroup φ V x).symm
    have h2 : yConj V H φ y =
        SevenK.barSub (conjClosure V H) φ (conjSubgroup V (y : G)) :=
      (barSub_conjSubgroup φ V y).symm
    rw [h1, h2, hVxy]
  · intro hy
    have hYxy : conjSubgroup (SevenK.barSub (conjClosure V H) φ V) (φ x) =
        conjSubgroup (SevenK.barSub (conjClosure V H) φ V) (φ y) := hy
    have hYg : conjSubgroup (SevenK.barSub (conjClosure V H) φ V) (φ x * (φ y)⁻¹) =
        SevenK.barSub (conjClosure V H) φ V := by
      calc conjSubgroup (SevenK.barSub (conjClosure V H) φ V) (φ x * (φ y)⁻¹)
          = conjSubgroup
              (conjSubgroup (SevenK.barSub (conjClosure V H) φ V) (φ x)) ((φ y)⁻¹) :=
            (conjSubgroup_conjSubgroup _ (φ x) ((φ y)⁻¹)).symm
        _ = conjSubgroup
              (conjSubgroup (SevenK.barSub (conjClosure V H) φ V) (φ y)) ((φ y)⁻¹) := by
            rw [hYxy]
        _ = SevenK.barSub (conjClosure V H) φ V :=
            conjSubgroup_conjSubgroup_inv _ (φ y)
    have hφN : φ x * (φ y)⁻¹ ∈ normalizer
        ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) :=
      conjSubgroup_eq_iff_mem_normalizer.1 hYg
    have hφN' : φ (x * y⁻¹) ∈ normalizer
        ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) := by
      rwa [map_mul, map_inv]
    have hxyM : ((x * y⁻¹ : ↥(conjClosure V H)) : G) ∈ M :=
      d.mem_M_of_map_mem_normalizer hφN'
    have hxyM' : (x : G) * (y : G)⁻¹ ∈ M := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hxyM
    have hV0g : conjSubgroup V₀ ((x : G) * (y : G)⁻¹) = V₀ := by
      apply conjSubgroup_eq_iff_mem_normalizer.2
      rwa [d.cfg.cex.hyp.normalizer₀]
    calc conjSubgroup V₀ (x : G)
        = conjSubgroup V₀ (((x : G) * (y : G)⁻¹) * (y : G)) := by
          rw [show ((x : G) * (y : G)⁻¹) * (y : G) = (x : G) by group]
      _ = conjSubgroup (conjSubgroup V₀ ((x : G) * (y : G)⁻¹)) (y : G) :=
          (conjSubgroup_conjSubgroup V₀ ((x : G) * (y : G)⁻¹) (y : G)).symm
      _ = conjSubgroup V₀ (y : G) := by rw [hV0g]

theorem inf_conj_V₀_eq_bot (d : DichCfg M V₀ V U S H φ) {x y : G}
    (hxy : conjSubgroup V₀ x ≠ conjSubgroup V₀ y) : conjSubgroup V₀ x ⊓ conjSubgroup V₀ y = ⊥ := by
  let g : G := y * x⁻¹
  have hgM : g ∉ M := by
    intro hgM
    apply hxy
    have hgN : g ∈ normalizer (V₀ : Set G) := by
      rwa [d.cfg.cex.hyp.normalizer₀]
    have hgconj : conjSubgroup V₀ g = V₀ := conjSubgroup_eq_iff_mem_normalizer.2 hgN
    have hgx : g * x = y := by simp only [g]; group
    have h : conjSubgroup V₀ y = conjSubgroup V₀ x := by
      calc conjSubgroup V₀ y = conjSubgroup V₀ (g * x) := by rw [hgx]
        _ = conjSubgroup (conjSubgroup V₀ g) x := (conjSubgroup_conjSubgroup V₀ g x).symm
        _ = conjSubgroup V₀ x := by rw [hgconj]
    exact h.symm
  rw [← le_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := Subgroup.mem_inf.mp hw
  have huV₀ : x * w * x⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hw1
  have huV₀g : x * w * x⁻¹ ∈ conjSubgroup V₀ g := by
    rw [mem_conjSubgroup_iff]
    have h : g * (x * w * x⁻¹) * g⁻¹ = y * w * y⁻¹ := by simp only [g]; group
    rw [h]
    exact mem_conjSubgroup_iff.mp hw2
  have hu_bot : x * w * x⁻¹ ∈ (⊥ : Subgroup G) := by
    rw [← d.cfg.cex.hyp.conj_inf_eq_bot hgM]
    exact ⟨huV₀g, huV₀⟩
  have hw_eq : w = 1 := by
    have h : x * w * x⁻¹ = 1 := Subgroup.mem_bot.mp hu_bot
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = x⁻¹ * 1 * x := by rw [h]
      _ = 1 := by group
  exact Subgroup.mem_bot.2 hw_eq

theorem ncard_conj_V₀ (d : DichCfg M V₀ V U S H φ) :
    Set.ncard {A : Subgroup G | ∃ z : ↥(conjClosure V H), A = conjSubgroup V₀ (z : G)} =
      Set.ncard {A : Subgroup X | ∃ x : X,
        A = conjSubgroup (SevenK.barSub (conjClosure V H) φ V) x} := by
  refine Set.ncard_congr (fun A hA => yConj V H φ (Classical.choose hA)) ?_ ?_ ?_
  · intro A hA
    exact ⟨φ (Classical.choose hA), rfl⟩
  · intro A B hA hB hAB
    have hA' := Classical.choose_spec hA
    have hB' := Classical.choose_spec hB
    have hiff := (conj_V₀_eq_iff d (Classical.choose hA) (Classical.choose hB)).2 hAB
    rw [hA', hB']
    exact hiff
  · intro B hB
    obtain ⟨x, rfl⟩ := hB
    obtain ⟨z, rfl⟩ := d.bar.surjective x
    have hzmem : ∃ z' : ↥(conjClosure V H),
        conjSubgroup V₀ (z : G) = conjSubgroup V₀ (z' : G) := ⟨z, rfl⟩
    refine ⟨conjSubgroup V₀ (z : G), hzmem, ?_⟩
    exact (conj_V₀_eq_iff d (Classical.choose hzmem) z).1
      (Classical.choose_spec hzmem).symm

theorem eq_one_of_comm (d : DichCfg M V₀ V U S H φ) {x y u : ↥(conjClosure V H)}
    (hxy : ¬ ∀ a ∈ yConj V H φ x, ∀ b ∈ yConj V H φ y, a * b = b * a)
    (hu : (u : G) ∈ conjSubgroup V (x : G)) (hu1 : φ u ≠ 1) {w : G}
    (hw : w ∈ conjSubgroup V₀ (y : G)) (hcomm : (u : G) * w = w * (u : G)) : w = 1 := by
  by_contra hw1
  have hw'V : (y : G) * w * (y : G)⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hw
  have hw'1 : (y : G) * w * (y : G)⁻¹ ≠ 1 := by
    intro h
    apply hw1
    calc w = (y : G)⁻¹ * ((y : G) * w * (y : G)⁻¹) * (y : G) := by group
      _ = (y : G)⁻¹ * 1 * (y : G) := by rw [h]
      _ = 1 := by group
  have hcomm' : ((y : G) * (u : G) * (y : G)⁻¹) * ((y : G) * w * (y : G)⁻¹) =
      ((y : G) * w * (y : G)⁻¹) * ((y : G) * (u : G) * (y : G)⁻¹) := by
    calc ((y : G) * (u : G) * (y : G)⁻¹) * ((y : G) * w * (y : G)⁻¹)
        = (y : G) * ((u : G) * w) * (y : G)⁻¹ := by group
      _ = (y : G) * (w * (u : G)) * (y : G)⁻¹ := by rw [hcomm]
      _ = ((y : G) * w * (y : G)⁻¹) * ((y : G) * (u : G) * (y : G)⁻¹) := by group
  have hyuM : (y : G) * (u : G) * (y : G)⁻¹ ∈ M :=
    d.cfg.cex.hyp.centralizer_le hw'V hw'1 (Subgroup.mem_centralizer_singleton_iff.2 hcomm')
  have huM : (u : G) ∈ conjSubgroup M (y : G) := mem_conjSubgroup_iff.2 hyuM
  let g : G := (y : G) * (x : G)⁻¹
  have hgK : g ∈ conjClosure V H :=
    (conjClosure V H).mul_mem y.2 ((conjClosure V H).inv_mem x.2)
  have hgH : g ∈ H := d.cfg.conjClosure_le_H hgK
  have hnotcommV : ¬ ∀ a ∈ V, ∀ b ∈ conjSubgroup V g, a * b = b * a := by
    intro hcv
    apply hxy
    have hconj_comm : ∀ a ∈ conjSubgroup V (x : G),
        ∀ b ∈ conjSubgroup (conjSubgroup V g) (x : G), a * b = b * a :=
      w16q_conjSubgroup_comm hcv (x : G)
    have hgx : g * (x : G) = (y : G) := by simp only [g]; group
    have hVy : conjSubgroup V (y : G) = conjSubgroup (conjSubgroup V g) (x : G) := by
      rw [conjSubgroup_conjSubgroup, hgx]
    have hcommConj : ∀ a ∈ conjSubgroup V (x : G),
        ∀ b ∈ conjSubgroup V (y : G), a * b = b * a := by
      intro a ha b hb
      exact hconj_comm a ha b (hVy ▸ hb)
    have hcommY : ∀ a ∈ yConj V H φ x, ∀ b ∈ yConj V H φ y, a * b = b * a := by
      have h := w16q_barSub_comm φ hcommConj
      rw [barSub_conjSubgroup φ V x, barSub_conjSubgroup φ V y] at h
      exact h
    exact hcommY
  have hfive := d.cfg.five d.cfg.std d.cfg.cex d.cfg.min.fam16 d.cfg.not_le g hgH hnotcommV
  have hxuV : (x : G) * (u : G) * (x : G)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hu
  have hxuM : (x : G) * (u : G) * (x : G)⁻¹ ∈ conjSubgroup M g := by
    have hgx : g * (x : G) = (y : G) := by simp only [g]; group
    have hMy : conjSubgroup M (y : G) = conjSubgroup (conjSubgroup M g) (x : G) := by
      rw [conjSubgroup_conjSubgroup, hgx]
    exact mem_conjSubgroup_iff.mp (hMy ▸ huM)
  have hxuI : (x : G) * (u : G) * (x : G)⁻¹ ∈ iSub16 V H := by
    have hmem : (x : G) * (u : G) * (x : G)⁻¹ ∈ V ⊓ conjSubgroup M g := ⟨hxuV, hxuM⟩
    rw [hfive] at hmem
    exact d.cfg.le_iSub16 hmem
  have hxH : (x : G) ∈ H := d.cfg.conjClosure_le_H x.2
  have hxN : (x : G) ∈ normalizer (iSub16 V H : Set G) :=
    le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H hxH
  have huI : (u : G) ∈ iSub16 V H :=
    (Subgroup.mem_normalizer_iff.mp hxN (u : G)).2 hxuI
  exact hu1 ((d.bar.ker_iff u).2 huI)

theorem comm_mem_conj_V₀ (d : DichCfg M V₀ V U S H φ) {x : G} (hx : x ∈ conjClosure V H) {u i : G}
    (hu : u ∈ conjSubgroup V x) (hi : i ∈ iSub16 V H) :
    u * i * u⁻¹ * i⁻¹ ∈ conjSubgroup V₀ x := by
  have hu' : x * u * x⁻¹ ∈ V := mem_conjSubgroup_iff.mp hu
  have hxH : x ∈ H := d.cfg.conjClosure_le_H hx
  have hxN : x ∈ normalizer (iSub16 V H : Set G) :=
    le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H hxH
  have hi' : x * i * x⁻¹ ∈ iSub16 V H := (Subgroup.mem_normalizer_iff.mp hxN i).1 hi
  have hi'S : x * i * x⁻¹ ∈ S := (d.cfg.iSub16_le_tSub16 hi').1
  have hcomm := d.cfg.cex.comm_mem_V₀ hi'S hu'
  refine mem_conjSubgroup_iff.2 ?_
  have h := V₀.inv_mem hcomm
  rwa [show ((x * i * x⁻¹) * (x * u * x⁻¹) * (x * i * x⁻¹)⁻¹ * (x * u * x⁻¹)⁻¹)⁻¹ =
      x * (u * i * u⁻¹ * i⁻¹) * x⁻¹ by group] at h

theorem conj_V₀_le_iSub16 (d : DichCfg M V₀ V U S H φ) (z : ↥(conjClosure V H)) :
    conjSubgroup V₀ (z : G) ≤ iSub16 V H := by
  have hV0I : V₀ ≤ iSub16 V H := le_sup_right.trans d.cfg.le_iSub16
  have hzH : (z : G) ∈ H := d.cfg.conjClosure_le_H z.2
  have hzN : (z : G) ∈ normalizer (iSub16 V H : Set G) :=
    le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H hzH
  calc conjSubgroup V₀ (z : G) ≤ conjSubgroup (iSub16 V H) (z : G) :=
        conjSubgroup_mono hV0I (z : G)
    _ = iSub16 V H := conjSubgroup_eq_iff_mem_normalizer.2 hzN

end DichCfg

end CFSG.LocalAnalysis.WeakClosure81

end
