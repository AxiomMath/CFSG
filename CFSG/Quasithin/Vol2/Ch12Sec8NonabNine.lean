module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabMod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

namespace Hyp1281Two

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g)

include h hU hg

theorem sup_le_normalizer_inf_rconj_wOfU :
    L ⊔ uOfL22 T M ≤ Subgroup.normalizer ((wOfU T M ⊓ rconj (wOfU T M) g : Subgroup G) : Set G) := by
  rw [h.wOfU_inf_rconj_eq hU hg]
  exact h.sup_le_normalizer_inf_rconj hU hg

theorem exists_mul_of_mem_pCoreOf_sup {s : G} (hs : s ∈ pCoreOf 2 (L ⊔ uOfL22 T M)) :
    ∃ w ∈ wOfU T M, ∃ x ∈ rconj (wOfU T M) g, s = w * x := by
  have : s ∈ (wOfU T M : Set G) * (rconj (wOfU T M) g : Set G) := by
    rw [← (h.pCoreOf_sup_uOfL22_eq_wOfU_sup hU hg).2]
    exact hs
  obtain ⟨w, hw, x, hx, hwx⟩ := this
  exact ⟨w, hw, x, hx, hwx.symm⟩

theorem lemma_12_8_9_three {u : G} (hu : u ∈ uOfL22 T M) (huW : u ∉ wOfU T M) :
    (∀ s ∈ pCoreOf 2 (L ⊔ uOfL22 T M),
        (s * u * s⁻¹ * u⁻¹ ∈ wOfU T M ⊓ rconj (wOfU T M) g ↔ s ∈ wOfU T M)) ∧
      (∀ s ∈ pCoreOf 2 (L ⊔ uOfL22 T M), s * u * s⁻¹ * u⁻¹ ∈ wOfU T M) ∧
      (∀ s ∈ pCoreOf 2 (L ⊔ uOfL22 T M), ∃ x ∈ rconj (wOfU T M) g,
        (s * u * s⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹)⁻¹ ∈ wOfU T M ⊓ rconj (wOfU T M) g) ∧
      (∀ w ∈ wOfU T M, ∃ x ∈ rconj (wOfU T M) g,
        x * u * x⁻¹ * u⁻¹ * w⁻¹ ∈ wOfU T M ⊓ rconj (wOfU T M) g) := by
  set U := uOfL22 T M with hUdef
  set W := wOfU T M with hWdef
  set X := rconj W g with hXdef
  set E := W ⊓ X with hEdef
  set I := L ⊔ U with hIdef
  set Sg := pCoreOf 2 I with hSdef
  have hEN : I ≤ Subgroup.normalizer (E : Set G) := h.sup_le_normalizer_inf_rconj_wOfU hU hg
  have hZE : quasithinOmegaOneCenter T ≤ E := h.omegaOneCenter_le_inf_rconj hU hg
  have hWU : W ≤ U := wOfU_le_uOfL22 T M
  have hEW : E ≤ W := inf_le_left
  have hWI : W ≤ I := hWU.trans le_sup_right
  have hSI : Sg ≤ I := pCoreOf_le 2 I
  have huI : u ∈ I := Subgroup.mem_sup_right hu
  have hsuW : ∀ s ∈ Sg, s * u * s⁻¹ * u⁻¹ ∈ W := by
    intro s hs
    have h1 : u * s * u⁻¹ * s⁻¹ ∈ W := by
      rw [hWdef, h.wOfU_eq_inf_pCoreOf hU hg]
      refine ⟨?_, ?_⟩
      · have hau : s * u⁻¹ * s⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp
            (h.pCoreOf_sup_uOfL22_le_normalizer_U hU hg hs) _).mp (U.inv_mem hu)
        have e3 : u * s * u⁻¹ * s⁻¹ = u * (s * u⁻¹ * s⁻¹) := by group
        rw [e3]
        exact U.mul_mem hu hau
      · have hua : u * s * u⁻¹ ∈ Sg :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I huI) _).mp hs
        exact Sg.mul_mem hua (Sg.inv_mem hs)
    have e : s * u * s⁻¹ * u⁻¹ = (u * s * u⁻¹ * s⁻¹)⁻¹ := by group
    rw [e]
    exact W.inv_mem h1
  have hwuE : ∀ w ∈ W, w * u * w⁻¹ * u⁻¹ ∈ E := fun w hw =>
    hZE (h.commutator_mem_omegaOneCenter (hWU hw) hu)
  refine ⟨fun s hs => ⟨fun hsE => ?_, fun hsW => hwuE s hsW⟩, hsuW, fun s hs => ?_, fun w hw => ?_⟩
  ·
    obtain ⟨w, hw, x, hx, rfl⟩ := h.exists_mul_of_mem_pCoreOf_sup hU hg hs
    have e : (w * x) * u * (w * x)⁻¹ * u⁻¹ =
        (w * (x * u * x⁻¹ * u⁻¹) * w⁻¹) * (w * u * w⁻¹ * u⁻¹) := by group
    rw [e] at hsE
    have h1 : w * (x * u * x⁻¹ * u⁻¹) * w⁻¹ ∈ E := by
      have := E.mul_mem hsE (E.inv_mem (hwuE w hw))
      rwa [mul_inv_cancel_right] at this
    have h2 : x * u * x⁻¹ * u⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hEN (hWI hw)) _).mpr h1
    have h3 : x ∈ E := h.mem_inf_of_commutator_mem hU hg hu huW hx h2
    exact W.mul_mem hw (hEW h3)
  ·
    obtain ⟨w, hw, x, hx, rfl⟩ := h.exists_mul_of_mem_pCoreOf_sup hU hg hs
    refine ⟨x, hx, ?_⟩
    have hc : x * u * x⁻¹ * u⁻¹ ∈ W := hsuW x (h.rconj_wOfU_le_pCoreOf hU hg hx)
    have e : (w * x) * u * (w * x)⁻¹ * u⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ =
        (w * (x * u * x⁻¹ * u⁻¹) * w⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹) *
          ((x * u * x⁻¹ * u⁻¹) * (w * u * w⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹)⁻¹) := by group
    rw [e]
    refine E.mul_mem ?_ ?_
    · have := h.commutator_mem_omegaOneCenter (x := w) (y := x * u * x⁻¹ * u⁻¹)
        (hWU hw) (hWU hc)
      have e2 : w * (x * u * x⁻¹ * u⁻¹) * w⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ =
          w * (x * u * x⁻¹ * u⁻¹) * w⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ := rfl
      exact hZE this
    · have hcI : x * u * x⁻¹ * u⁻¹ ∈ I := hWI hc
      have := (Subgroup.mem_normalizer_iff.mp (hEN hcI) _).mp (hwuE w hw)
      exact this
  ·
    refine ⟨g⁻¹ * w * g, ?_, ?_⟩
    · rw [hXdef, mem_rconj]
      have e : g * (g⁻¹ * w * g) * g⁻¹ = w := by group
      rw [e]
      exact hw
    · exact (h.module_relations hU hg hu huW).2.1 w hw

theorem lemma_12_8_9_six {u : G} (hu : u ∈ uOfL22 T M) (huW : u ∉ wOfU T M) {x : G}
    (hx : x ∈ rconj (wOfU T M) g)
    (hxu : x * u * x⁻¹ * u⁻¹ ∈ centerOf (uOfL22 T M)) :
    x ∈ rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g) := by
  set ζ := u * x * u⁻¹ * x⁻¹ with hζ
  have hζZ : ζ ∈ centerOf (uOfL22 T M) := by
    have e : ζ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by rw [hζ]; group
    rw [e]
    exact (centerOf (uOfL22 T M)).inv_mem hxu
  have hζW : ζ ∈ wOfU T M := centerOf_uOfL22_le_wOfU T M hζZ
  have h1 := (h.module_relations hU hg hu huW).2.2.1 x hx ζ hζW (by
    have : (u * x * u⁻¹ * x⁻¹)⁻¹ * ζ = 1 := by rw [← hζ]; group
    rw [this]
    exact Subgroup.one_mem _)
  have hyZg : g⁻¹ * ζ * g ∈ rconj (centerOf (uOfL22 T M)) g := inv_mul_mul_mem_rconj hζZ
  have e : x = (g⁻¹ * ζ * g) * (x⁻¹ * (g⁻¹ * ζ * g))⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem_sup hyZg ((wOfU T M ⊓ rconj (wOfU T M) g).inv_mem h1)

end Hyp1281Two

namespace Hyp1281Two

theorem oTwoUpper_sup_eq (h : Hyp1281Two G T M L) : oTwoUpper (L ⊔ T) = L := by
  apply le_antisymm
  · exact oTwoUpper_le_of_pow_mem fun x hx =>
      exists_pow_two_pow_mem_of_le_normalizer (h.inM.2.trans h.normal) h.sylow.1 hx
  · calc L = oTwoUpper L := h.residual.symm
      _ ≤ oTwoUpper (L ⊔ T) := oTwoUpper_mono le_sup_left

theorem exists_goodElt_L (h : Hyp1281Two G T M L) : ∃ g : G, GoodElt128 T L g := by
  obtain ⟨l, hlL, hlodd, hlC⟩ := h.exists_odd_not_mem_centralizer
  refine ⟨l, hlL, fun hlN => hlC ?_⟩
  exact h.mem_centralizer_of_odd (h.isTwoReducedIn.1.2.1 (h.le hlL)) hlN hlodd

theorem LT_le_normalizer_sup_uOfL22 (h : Hyp1281Two G T M L) :
    L ⊔ T ≤ Subgroup.normalizer ((L ⊔ uOfL22 T M : Subgroup G) : Set G) := by
  refine sup_le ((le_sup_left : L ≤ L ⊔ uOfL22 T M).trans Subgroup.le_normalizer) ?_
  intro t ht
  exact Subgroup.inf_normalizer_le_normalizer_sup L (uOfL22 T M)
    ⟨h.inM.2.trans h.normal ht, h.T_le_normalizer_uOfL22 ht⟩

theorem conjClosure_uOfL22_sup_eq (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    conjClosure (uOfL22 T M) (L ⊔ T) = L ⊔ uOfL22 T M := by
  apply le_antisymm
  · refine conjClosure_le fun p hp u hu => ?_
    have := (Subgroup.mem_normalizer_iff.mp (h.LT_le_normalizer_sup_uOfL22 hp) u).mp
      (Subgroup.mem_sup_right hu)
    exact this
  · obtain ⟨g, hg⟩ := h.exists_goodElt_L
    rw [← h.sup_rconj_uOfL22_eq hU hg]
    refine sup_le (le_conjClosure _ _) ?_
    intro y hy
    rw [mem_rconj] at hy
    have h1 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ ∈ conjClosure (uOfL22 T M) (L ⊔ T) :=
      mem_conjClosure (Subgroup.inv_mem _ (Subgroup.mem_sup_left hg.mem)) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h1

theorem normalizer_VZ_le_normalizer_sup_uOfL22 (h : Hyp1281Two G T M L) :
    Subgroup.normalizer (VZ T M : Set G) ≤
      Subgroup.normalizer ((L ⊔ uOfL22 T M : Subgroup G) : Set G) := by
  intro m hm
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) := hm
  have hM : m ∈ M := by rw [h.normalizer_VZ] at hm; exact hm
  have htop := h.autOn_LT_eq_top
  have hmem : conjAct (VZ T M) ⟨m, hmN⟩ ∈ autOn (L ⊔ T) (VZ T M) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨p, hp, hpm⟩ := Subgroup.mem_map.mp hmem
  have hpLT : (p : G) ∈ L ⊔ T := hp
  have hpm' : (p : G)⁻¹ * m ∈ Subgroup.centralizer (VZ T M : Set G) := by
    have h1 : conjAct (VZ T M) (p⁻¹ * ⟨m, hmN⟩) = 1 := by
      rw [map_mul, map_inv, hpm, inv_mul_cancel]
    exact conjAct_eq_one_iff_mem_centralizer.mp h1
  set c := (p : G)⁻¹ * m with hc
  have hcM : c ∈ M := Subgroup.mul_mem _ (Subgroup.inv_mem _ ((sup_le h.le h.inM.2) hpLT)) hM
  have hcU : c ∈ Subgroup.normalizer (uOfL22 T M : Set G) := by
    have hcH : c ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.centralizer_le (omegaOneCenter_le_VZ T M) hpm'
    exact h.g1_le_normalizer_uOfL22 hcH
  have hcL : c ∈ Subgroup.normalizer (L : Set G) := h.normal hcM
  have hc' : c ∈ Subgroup.normalizer ((L ⊔ uOfL22 T M : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup L (uOfL22 T M) ⟨hcL, hcU⟩
  have hp' : (p : G) ∈ Subgroup.normalizer ((L ⊔ uOfL22 T M : Subgroup G) : Set G) :=
    h.LT_le_normalizer_sup_uOfL22 hpLT
  have e : m = (p : G) * c := by rw [hc]; group
  rw [e]
  exact Subgroup.mul_mem _ hp' hc'

theorem lemma_12_8_9_one (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    conjClosure (uOfL22 T M) (L ⊔ T) = oTwoUpper (L ⊔ T) ⊔ uOfL22 T M ∧
      (∀ g : G, g ∈ L ⊔ T → g ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) →
        conjClosure (uOfL22 T M) (L ⊔ T) = uOfL22 T M ⊔ rconj (uOfL22 T M) g) ∧
      conjClosure (uOfL22 T M) (L ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) =
        pCoreOf 2 (conjClosure (uOfL22 T M) (L ⊔ T)) ∧
      Subgroup.normalizer (VZ T M : Set G) ≤ Subgroup.normalizer (oTwoUpper (L ⊔ T) : Set G) ∧
      Subgroup.normalizer (VZ T M : Set G) ≤
        Subgroup.normalizer (conjClosure (uOfL22 T M) (L ⊔ T) : Set G) := by
  have hI := h.conjClosure_uOfL22_sup_eq hU
  refine ⟨by rw [hI, h.oTwoUpper_sup_eq], ?_, ?_, ?_, ?_⟩
  · intro g hg hgH
    obtain ⟨t, ht, l, hl, rfl⟩ := h.exists_goodElt hg hgH
    rw [hI, rconj_mul_eq_of_mem_normalizer (h.T_le_normalizer_uOfL22 ht) l,
      h.sup_rconj_uOfL22_eq hU hl]
  · obtain ⟨g, hg⟩ := h.exists_goodElt_L
    rw [hI]
    exact (h.pCoreOf_sup_uOfL22_eq hU hg).symm
  · rw [h.oTwoUpper_sup_eq, h.normalizer_VZ]
    exact h.normal
  · rw [hI]
    exact h.normalizer_VZ_le_normalizer_sup_uOfL22

end Hyp1281Two

end CFSG.Quasithin
