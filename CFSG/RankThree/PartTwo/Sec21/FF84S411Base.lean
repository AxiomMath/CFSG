module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Core
public import CFSG.RankThree.PartTwo.Sec21.FF84S410DataB
public import CFSG.RankThree.PartTwo.Sec21.FF84S4OmP5

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {e : ↥S ≃* Multiplicative F6}
  {ψ : ↥(Nor S) →* OmG} {t : ↥S}

theorem S_comm (e : ↥S ≃* Multiplicative F6) (x y : ↥S) : x * y = y * x := by
  apply e.injective
  rw [map_mul, map_mul, mul_comm]

theorem S_comm' (e : ↥S ≃* Multiplicative F6) {x y : G} (hx : x ∈ S) (hy : y ∈ S) :
    x * y = y * x :=
  congrArg Subtype.val (S_comm e ⟨x, hx⟩ ⟨y, hy⟩)

theorem orderOf_t (e : ↥S ≃* Multiplicative F6) (ht1 : (t : G) ≠ 1) : orderOf (t : G) = 2 := by
  have h : (t : G) ^ 2 = 1 := by
    have := congrArg Subtype.val (sq_S e t)
    rw [pow_two]
    exact this
  exact orderOf_eq_prime h ht1

theorem t_mem_T (e : ↥S ≃* Multiplicative F6) (ht1 : (t : G) ≠ 1) :
    (t : G) ∈ Op 2 (Cen (t : G)) := by
  have hord := orderOf_t e ht1
  have hP : IsPGroup 2 (Subgroup.zpowers (t : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  have hle : Subgroup.zpowers (t : G) ≤ Op 2 (Cen (t : G)) := by
    refine S3.le_Op_of_normal 2 (Cen (t : G)) _ ?_ hP ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · intro h hh m hm
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
      have hc : Commute h (t : G) := Subgroup.mem_centralizer_singleton_iff.1 hh
      rw [(hc.zpow_right k).mul_inv_cancel]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  exact hle (Subgroup.mem_zpowers _)

theorem R_conj_mem {y r : G} (hyS : y ∈ Nor S) (hyt : y ∈ Cen (t : G))
    (hr : r ∈ S ⊓ Op 2 (Cen (t : G))) : y * r * y⁻¹ ∈ S ⊓ Op 2 (Cen (t : G)) := by
  obtain ⟨hrS, hrT⟩ := Subgroup.mem_inf.1 hr
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyS r).1 hrS,
    S3.Op_conj_mem 2 (Subgroup.le_normalizer hyt) hrT⟩

theorem wsub_R_inv (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0) (g : OmG)
    (hg : g • tau0 = tau0) (v : F6) (hv : v ∈ wsub e (S ⊓ Op 2 (Cen (t : G)))) :
    g • v ∈ wsub e (S ⊓ Op 2 (Cen (t : G))) := by
  obtain ⟨y, hy⟩ := psiY_surj H het ⟨g, MulAction.mem_stabilizer_iff.2 hg⟩
  have hyg : ψ ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩ = g := by
    have := congrArg Subtype.val hy
    exact this
  obtain ⟨w, hw, rfl⟩ := hv
  have hyS := (Subgroup.mem_inf.1 y.2).1
  have hyt := (Subgroup.mem_inf.1 y.2).2
  have hR := R_conj_mem (t := t) hyS hyt hw
  refine ⟨⟨(y : G) * (w : G) * (y : G)⁻¹, (Subgroup.mem_inf.1 hR).1⟩, hR, ?_⟩
  rw [← hyg, H.smul_eq]

theorem R_cases (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0) (ht1 : (t : G) ≠ 1) :
    wsub e (S ⊓ Op 2 (Cen (t : G))) = Submodule.span (ZMod 2) {tau0} ∨
      (∀ x, x ∈ wsub e (S ⊓ Op 2 (Cen (t : G))) ↔ polarMinus x tau0 = 0) ∨
      wsub e (S ⊓ Op 2 (Cen (t : G))) = ⊤ :=
  stab_inv_subspace ⟨t, Subgroup.mem_inf.2 ⟨t.2, t_mem_T e ht1⟩, het⟩
    (fun g hg w hw => wsub_R_inv H het g hg w hw)

theorem claim1_core (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0)
    (ht1 : (t : G) ≠ 1) {b : G} (hbt : b ∈ Cen (t : G))
    (hnotCen : ¬ ∀ x ∈ S ⊓ Op 2 (Cen (t : G)), x ∈ Cen b) (hnotS : ¬ S ≤ Op 2 (Cen (t : G))) :
    ∀ x : ↥S, (x : G) ∈ Op 2 (Cen (t : G)) ↔ polarMinus (Multiplicative.toAdd (e x)) tau0 = 0 := by
  rcases R_cases H het ht1 with h | h | h
  · exfalso
    apply hnotCen
    intro x hx
    have hv : Multiplicative.toAdd (e ⟨x, (Subgroup.mem_inf.1 hx).1⟩) ∈
        wsub e (S ⊓ Op 2 (Cen (t : G))) := ⟨⟨x, (Subgroup.mem_inf.1 hx).1⟩, hx, rfl⟩
    rw [h, Submodule.mem_span_singleton] at hv
    obtain ⟨c, hc⟩ := hv
    have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc2 c with rfl | rfl
    · rw [zero_smul] at hc
      have := eq_one_of_toAdd_e_zero (e := e) hc.symm
      have h1 : x = 1 := congrArg Subtype.val this
      rw [h1]
      exact Subgroup.one_mem _
    · rw [one_smul, ← het] at hc
      have := (toAdd_e_eq_iff (e := e) _ t).1 hc.symm
      have h1 : x = (t : G) := congrArg Subtype.val this
      rw [h1]
      exact (Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hbt).symm)
  · intro x
    constructor
    · intro hx
      exact (h _).1 ⟨x, Subgroup.mem_inf.2 ⟨x.2, hx⟩, rfl⟩
    · intro hx
      obtain ⟨w, hw, hwx⟩ := (h _).2 hx
      have : w = x := (toAdd_e_eq_iff (e := e) w x).1 hwx
      rw [← this]
      exact (Subgroup.mem_inf.1 hw).2
  · exfalso
    apply hnotS
    intro x hx
    have hv : Multiplicative.toAdd (e ⟨x, hx⟩) ∈ wsub e (S ⊓ Op 2 (Cen (t : G))) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨w, hw, hwx⟩ := hv
    have : w = ⟨x, hx⟩ := (toAdd_e_eq_iff (e := e) w ⟨x, hx⟩).1 hwx
    have h2 : (w : G) = x := congrArg Subtype.val this
    rw [← h2]
    exact (Subgroup.mem_inf.1 hw).2

theorem claim2_core (H : OmSet S e ψ) (het : Multiplicative.toAdd (e t) = tau0)
    (hPar : HypOmParabolic)
    (hperp : ∀ x : ↥S, (x : G) ∈ Op 2 (Cen (t : G)) ↔
      polarMinus (Multiplicative.toAdd (e x)) tau0 = 0) :
    CenS (S ⊓ Op 2 (Cen (t : G))) = S := by
  apply le_antisymm
  · intro x hx
    obtain ⟨v, hvq, hvp⟩ := exists_nonsing_perp
    let s' : ↥S := e.symm (Multiplicative.ofAdd v)
    have hs'v : Multiplicative.toAdd (e s') = v := by simp [s']
    have hs'1 : (s' : G) ≠ 1 := by
      intro h
      have : s' = 1 := Subtype.ext h
      rw [this] at hs'v
      rw [map_one, toAdd_one] at hs'v
      rw [← hs'v, qMinus_zero] at hvq
      exact absurd hvq (by decide)
    have hs'T : (s' : G) ∈ Op 2 (Cen (t : G)) := (hperp s').2 (by rw [hs'v]; exact hvp)
    have hxs : x ∈ Cen (s' : G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx s' (Subgroup.mem_inf.2 ⟨s'.2, hs'T⟩)).symm
    have hO : Op 2 (Cen (s' : G)) = S := (H.hq s' hs'1).1 (by rw [hs'v]; exact hvq)
    have hxN : x ∈ Nor S := by
      have := le_nor_op2 (Cen (s' : G)) hxs
      rwa [hO] at this
    have hψ : ψ ⟨x, hxN⟩ = 1 := by
      refine (hPar qMinus_tau0 tau0_ne_zero).2.2.1 _ (fun z hz => ?_)
      obtain ⟨w, hw⟩ : ∃ w : ↥S, Multiplicative.toAdd (e w) = z :=
        ⟨e.symm (Multiplicative.ofAdd z), by simp⟩
      have hwT : (w : G) ∈ Op 2 (Cen (t : G)) := (hperp w).2 (by rw [hw]; exact hz)
      have hcomm : x * (w : G) = (w : G) * x :=
        (Subgroup.mem_centralizer_iff.1 hx w (Subgroup.mem_inf.2 ⟨w.2, hwT⟩)).symm
      have := (H.comm_iff ⟨x, hxN⟩ w).1 hcomm
      rw [hw] at this
      exact this
    exact (H.psi_eq_one_iff _).1 hψ
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact S_comm' e (Subgroup.mem_inf.1 hr).1 hx

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
