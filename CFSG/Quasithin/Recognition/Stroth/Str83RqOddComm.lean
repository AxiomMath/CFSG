module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackVertex
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackMove
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexL2
import CFSG.Quasithin.EmptyFaithful.GoldschmidtEmbedLocA7Core
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoResT0Basic

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem oddC_Lv_zero_le_centralizer
    (hZL : L1 ≤ centralizer (t.Zv 0 : Set G)) :
    t.Lv 0 ≤ centralizer (t.Zv 0 : Set G) := by
  rw [t.Lv_zero]
  refine sup_le hZL ?_
  rw [← t.Qv_zero]
  exact (Subgroup.le_centralizer_iff).mpr (t.Zv_le_centralizer 0)

private theorem oddC_mem_Zv_neg_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b : ℤ} (hb : 2 ≤ b) (hZ0 : t.Zv 0 ≤ t.Gw (-b) b)
    (hZL : L1 ≤ centralizer (t.Zv 0 : Set G)) {x : G} (hx : x ∈ t.Zv 0) :
    x ∈ t.Zv (-1) := by
  have hxQ : x ∈ t.Qv (-1) :=
    t.le_Qv_of_le_Gw hfr (u := -b) (w := b) (j := -1) (by omega) (by omega)
      (t.isPGroup_Zv 0) hZ0 hx
  have hx2 : x ^ 2 = 1 :=
    A4.sq_eq_one_of_mem_omegaOneCenterOf (R := t.Qv 0) (by simpa only [t.Zv_eq] using hx)
  have hQ0 : t.Qv (-1) ≤ t.Lv 0 :=
    t.le_Lv hfr (t.isPGroup_Qv (-1)) (t.Qv_le_Gv hfr (-1)).2
  have hL0 : t.Lv 0 ≤ centralizer ({x} : Set G) :=
    (t.oddC_Lv_zero_le_centralizer hZL).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx))
  have hxc : x ∈ centralizer (t.Qv (-1) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hL0 (hQ0 hq))
  rw [t.Zv_eq]
  exact Subgroup.subset_closure ⟨⟨hxQ, hxc⟩, hx2⟩

private theorem oddC_commutator_mem_Zv_and_commute {b : ℤ} (hb : 2 ≤ b)
    (hZ0 : t.Zv 0 ≤ t.Gw (-b) b) {x y : G} (hx : x ∈ t.Zv 0)
    (hy : y ∈ t.Zv (-b)) :
    ⁅x, y⁆ ∈ t.Zv (-b) ∧ ⁅x, y⁆ * x = x * ⁅x, y⁆ := by
  have hxGv : x ∈ t.Gv (-b) := hZ0.trans (win_le_qv (a := -b) (b := b) (i := -b)
    (by omega) (by omega)) hx
  have hx2 : x * x = 1 := by
    have h := A4.sq_eq_one_of_mem_omegaOneCenterOf (R := t.Qv 0) (by simpa only [t.Zv_eq] using hx)
    simpa [pow_two] using h
  have hZel : IsElemAbelian 2 (t.Zv (-b)) := by
    rw [t.Zv_eq]
    exact SmithC27.isElemAbelian_omegaOneCenterOf _
  have hN : ∀ z ∈ t.Zv (-b), x * z * x⁻¹ ∈ t.Zv (-b) := by
    intro z hz
    exact (Subgroup.mem_normalizer_iff.mp (t.Gv_le_normalizer_Zv (-b) hxGv) z).mp hz
  have hmem : ⁅y, x⁆ ∈ t.Zv (-b) ⊓ centralizer ({x} : Set G) :=
    (Subgroup.commutator_le.mp
      (CFSG.ComponentClassification.GMS78.commutator_zpowers_le_inf_centralizer hZel hx2 hN))
      y hy x (Subgroup.mem_zpowers x)
  have hinv : ⁅x, y⁆ = (⁅y, x⁆)⁻¹ := (commutatorElement_inv y x).symm
  have hc : ⁅y, x⁆ * x = x * ⁅y, x⁆ :=
    Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  refine ⟨?_, ?_⟩
  · rw [hinv]
    exact Subgroup.inv_mem _ hmem.1
  · rw [hinv]
    exact (show Commute ⁅y, x⁆ x from hc).inv_left.eq

private theorem oddC_pCoreOf_Gw_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZL : L1 ≤ centralizer (t.Zv 0 : Set G)) :
    pCoreOf 2 (t.Gw (-1) 0) ≤ centralizer (t.Zv 0 : Set G) := by
  have hG0 : pCoreOf 2 (t.Gw (-1) 0) ≤ t.Gv 0 :=
    (pCoreOf_le 2 _).trans (win_le_qv (a := -1) (b := 0) (i := 0) (by omega) le_rfl)
  exact (t.le_Lv hfr (pCoreOf_isPGroup 2 _) hG0).trans
    (t.oddC_Lv_zero_le_centralizer hZL)

private theorem oddC_Zv_neg_one_inf_centralizer {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hC0 : t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥) :
    t.Zv (-1) ⊓ centralizer (t.Lv (-1) : Set G) = ⊥ := by
  have hP1 : P1 L1 L2 S ≤ normalizer ((L1 ⊔ Q1 L1 L2 S : Subgroup G) : Set G) := by
    have h := t.Gv_le_normalizer_Lv hfr 0
    rwa [t.Gv_zero, t.Lv_zero] at h
  have hP2 : P2 L1 L2 S ≤ normalizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
    have h := t.Gv_le_normalizer_Lv hfr 1
    rwa [t.Gv_one, t.Lv_one] at h
  have hZmap : (t.Zv (-1)).map (MulAut.conj (t.edgeElt 2)).toMonoidHom = t.Zv 1 := by
    have h := t.map_Zv_edgeElt 2 (-1)
    rw [if_pos (by norm_num : Even (2 : ℤ)), show (2 : ℤ) + (-1) = 1 by norm_num] at h
    exact h
  have hLmap : (t.Lv (-1)).map (MulAut.conj (t.edgeElt 2)).toMonoidHom = t.Lv 1 := by
    have h := t.map_qv_edgeElt (F₁ := L1 ⊔ Q1 L1 L2 S) (F₂ := L2 ⊔ Q2 L1 L2 S) hP1 hP2 2 (-1)
    rw [if_pos (by norm_num : Even (2 : ℤ)), show (2 : ℤ) + (-1) = 1 by norm_num] at h
    exact h
  have hle : (t.Zv (-1) ⊓ centralizer (t.Lv (-1) : Set G)).map
      (MulAut.conj (t.edgeElt 2)).toMonoidHom ≤ ⊥ := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (t.edgeElt 2)).injective, hZmap]
    have hcent := Subgroup.map_centralizer_le_centralizer_image
      (s := (t.Lv (-1) : Set G)) (f := (MulAut.conj (t.edgeElt 2)).toMonoidHom)
    have hset : (MulAut.conj (t.edgeElt 2)).toMonoidHom '' (t.Lv (-1) : Set G) =
        (t.Lv 1 : Set G) := by
      rw [← Subgroup.coe_map, hLmap]
    rw [hset] at hcent
    have hL2le : L2 ≤ t.Lv 1 := by
      rw [t.Lv_one]
      exact (le_sup_left : L2 ≤ L2 ⊔ Q2 L1 L2 S)
    have hc2 : centralizer (t.Lv 1 : Set G) ≤ centralizer (L2 : Set G) :=
      Subgroup.centralizer_le hL2le
    have hstep : t.Zv 1 ⊓ (centralizer (t.Lv (-1) : Set G)).map
        (MulAut.conj (t.edgeElt 2)).toMonoidHom ≤ t.Zv 1 ⊓ centralizer (L2 : Set G) :=
      le_inf inf_le_left (inf_le_right.trans (hcent.trans hc2))
    exact hstep.trans (le_of_eq hC0)
  have hmap : (t.Zv (-1) ⊓ centralizer (t.Lv (-1) : Set G)).map
      (MulAut.conj (t.edgeElt 2)).toMonoidHom = ⊥ := le_bot_iff.mp hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).mp hmap

private theorem oddC_commutator_mem_pCoreOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b : ℤ} (hb : 2 ≤ b) (hZ0 : t.Zv 0 ≤ t.Gw (-b) b)
    (hR : ⁅t.Zv 0, t.Zv (-b)⁆ ≤ t.Qv (-2))
    (hZL : L1 ≤ centralizer (t.Zv 0 : Set G))
    (hC0 : t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥) {x y : G} (hx : x ∈ t.Zv 0)
    (hy : y ∈ t.Zv (-b)) : ⁅x, y⁆ ∈ pCoreOf 2 (t.Gw (-1) 0) := by
  obtain ⟨-, hgx⟩ := t.oddC_commutator_mem_Zv_and_commute hb hZ0 hx hy
  have hgQ : ⁅x, y⁆ ∈ t.Qv (-2) := hR (Subgroup.commutator_mem_commutator hx hy)
  have hgL : ⁅x, y⁆ ∈ t.Lv (-1) :=
    (t.le_Lv hfr (t.isPGroup_Qv (-2)) (t.Qv_le_Gv hfr (-2)).2) hgQ
  have hTsyl : IsSylowTwoOf (pCoreOf 2 (t.Gw (-1) 0)) (t.Lv (-1)) := by
    simpa using t.isSylowTwoOf_Lv hfr (-1)
  by_contra hgT
  have hT' : IsSylowTwoOf ((pCoreOf 2 (t.Gw (-1) 0)).map
      (MulAut.conj ⁅x, y⁆).toMonoidHom) (t.Lv (-1)) := by
    have h := IsSylowTwoOf.map_equiv (MulAut.conj ⁅x, y⁆) hTsyl
    rwa [show (t.Lv (-1)).map (MulAut.conj ⁅x, y⁆).toMonoidHom = t.Lv (-1) from
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgL)] at h
  have hne : (pCoreOf 2 (t.Gw (-1) 0)) ≠ (pCoreOf 2 (t.Gw (-1) 0)).map
      (MulAut.conj ⁅x, y⁆).toMonoidHom := by
    intro heq
    apply hgT
    have hgN : ⁅x, y⁆ ∈ normalizer (pCoreOf 2 (t.Gw (-1) 0) : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
    have hg2 : ∃ k : ℕ, ⁅x, y⁆ ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (t.isPGroup_Qv (-2)) ⟨⁅x, y⁆, hgQ⟩
      rw [Subgroup.orderOf_mk] at hk
      exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one _⟩
    exact CFSG.Quasithin.EmbedLoc.mem_of_two_element_normalizer hTsyl hgL hgN hg2
  have hTcent := t.oddC_pCoreOf_Gw_le_centralizer hfr hZL
  have hTZ : pCoreOf 2 (t.Gw (-1) 0) ≤ centralizer ({x} : Set G) :=
    hTcent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx))
  have hxconj : (MulAut.conj ⁅x, y⁆) x = x := by
    rw [MulAut.conj_apply]
    calc ⁅x, y⁆ * x * ⁅x, y⁆⁻¹ = x * ⁅x, y⁆ * ⁅x, y⁆⁻¹ := by rw [hgx]
      _ = x := by group
  have hT'Z : (pCoreOf 2 (t.Gw (-1) 0)).map (MulAut.conj ⁅x, y⁆).toMonoidHom ≤
      centralizer ({x} : Set G) := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    change (MulAut.conj ⁅x, y⁆) w * x = x * (MulAut.conj ⁅x, y⁆) w
    have hwx : w * x = x * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (hTZ hw)
    have hconj := congrArg (MulAut.conj ⁅x, y⁆) hwx
    simpa only [map_mul, hxconj] using hconj
  have hGen := le_sup_pCoreOf_of_sylow_ne_of_l2 hfr.hf
    (t.isL2Quot_Lv hfr (by decide : Odd (-1))) hTsyl hT' hne
    (hTZ.trans le_sup_left) (hT'Z.trans le_sup_left)
  rw [t.pCoreOf_Lv hfr (-1)] at hGen
  have hL0Z : t.Lv 0 ≤ centralizer ({x} : Set G) :=
    (t.oddC_Lv_zero_le_centralizer hZL).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx))
  have hQZ : t.Qv (-1) ≤ centralizer ({x} : Set G) :=
    (t.le_Lv hfr (t.isPGroup_Qv (-1)) (t.Qv_le_Gv hfr (-1)).2).trans hL0Z
  have hLZ : t.Lv (-1) ≤ centralizer ({x} : Set G) := by
    rwa [sup_eq_left.mpr hQZ] at hGen
  have hxCent : x ∈ centralizer (t.Lv (-1) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLZ hl)
  have hxZ : x ∈ t.Zv (-1) := t.oddC_mem_Zv_neg_one hfr hb hZ0 hZL hx
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← t.oddC_Zv_neg_one_inf_centralizer hfr hC0]
    exact ⟨hxZ, hxCent⟩
  have hx1 : x = 1 := by simpa using hxbot
  exact hgT (by simp [hx1])

theorem commutator_Zv_zero_Zv_neg_le_Qv_neg_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b : ℤ} (hb : 3 ≤ b) (hZ0 : t.Zv 0 ≤ t.Gw (-b) b)
    (hZb : t.Zv (-b) ≤ t.Gv (-2)) : ⁅t.Zv 0, t.Zv (-b)⁆ ≤ t.Qv (-2) := by
  have hA : t.Zv 0 ≤ t.Qv (-2) :=
    t.le_Qv_of_le_Gw hfr (u := -b) (w := b) (j := -2) (by omega) (by omega)
      (t.isPGroup_Zv 0) hZ0
  have hB : t.Zv (-b) ≤ normalizer (t.Qv (-2) : Set G) :=
    hZb.trans (t.Gv_le_normalizer_Qv (-2))
  exact (Subgroup.commutator_mono hA le_rfl).trans
    ((Subgroup.le_normalizer_iff_commutator_le_left (H := t.Zv (-b))
      (K := t.Qv (-2))).mp hB)

theorem commutator_commutator_Zv_zero_Zv_neg_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {b : ℤ} (hb : 2 ≤ b) (hZ0 : t.Zv 0 ≤ t.Gw (-b) b)
    (hR : ⁅t.Zv 0, t.Zv (-b)⁆ ≤ t.Qv (-2)) (hZL : L1 ≤ centralizer (t.Zv 0 : Set G))
    (hC0 : t.Zv 1 ⊓ centralizer (L2 : Set G) = ⊥) :
    ⁅⁅t.Zv 0, t.Zv (-b)⁆, t.Zv 0⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [Subgroup.commutator_le]
  intro x hx y hy
  exact t.oddC_pCoreOf_Gw_le_centralizer hfr hZL
    (t.oddC_commutator_mem_pCoreOf hfr hb hZ0 hR hZL hC0 hx hy)

end Track

end CFSG.Quasithin.Stroth.Rq
