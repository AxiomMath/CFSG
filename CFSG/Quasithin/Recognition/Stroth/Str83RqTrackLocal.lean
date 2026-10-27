module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
public import CFSG.Quasithin.Recognition.Stroth.Str83RqRoot
public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackVertex
public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackMove
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexL2
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexSz
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzModule
import CFSG.Quasithin.Recognition.St84.Gen.L2SecFaithful

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

include t in
private theorem P1_le_normalizer_sup {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    P1 L1 L2 S ≤ normalizer (((L1 ⊔ Q1 L1 L2 S) : Subgroup G) : Set G) := by
  have h := t.Gv_le_normalizer_Lv hfr 0
  rwa [t.Gv_zero, t.Lv_zero] at h

include t in
private theorem P2_le_normalizer_sup {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    P2 L1 L2 S ≤ normalizer (((L2 ⊔ Q2 L1 L2 S) : Subgroup G) : Set G) := by
  have h := t.Gv_le_normalizer_Lv hfr 1
  rwa [t.Gv_one, t.Lv_one] at h

private theorem pCoreOf_Gw_ne {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) :
    pCoreOf 2 (t.Gw v (v + 1)) ≠ pCoreOf 2 (t.Gw (v - 1) v) := by
  intro heq
  have hR : pCoreOf 2 (t.Gw v (v + 1)) ≤ t.Gw (v - 1) v := by
    rw [heq]
    exact pCoreOf_le 2 _
  have hR' : pCoreOf 2 (t.Gw (v - 1) v) ≤ t.Gw v (v + 1) := by
    rw [← heq]
    exact pCoreOf_le 2 _
  have hRleft : pCoreOf 2 (t.Gw (v - 1) v) ≤ t.Gw (v - 1) v := by
    rw [← heq]
    exact hR
  have hXw : pCoreOf 2 (t.Gw (v - 1) v) ≤ t.Gw (v - 1) (v + 1) := by
    intro x hx
    have hleft := hRleft hx
    have hright := hR' hx
    have hleft' : ∀ i, v - 1 ≤ i → i ≤ v →
        x ∈ qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ i :=
      (mem_win_iff (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        (x₁ := t.x₁) (x₂ := t.x₂) (a := v - 1) (b := v)).mp hleft
    have hright' : ∀ i, v ≤ i → i ≤ v + 1 →
        x ∈ qv (P1 L1 L2 S) (P2 L1 L2 S) t.x₁ t.x₂ i :=
      (mem_win_iff (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
        (x₁ := t.x₁) (x₂ := t.x₂) (a := v) (b := v + 1)).mp hright
    refine (mem_win_iff (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S)
      (x₁ := t.x₁) (x₂ := t.x₂) (a := v - 1) (b := v + 1)).mpr ?_
    intro i hi1 hi2
    rcases le_total i v with hiv | hvi
    · exact hleft' i hi1 hiv
    · exact hright' i hvi hi2
  have hQ : pCoreOf 2 (t.Gw (v - 1) v) ≤ t.Qv v :=
    t.le_Qv_of_le_Gw hfr (by omega) (by omega) (pCoreOf_isPGroup 2 _) hXw
  have hrel := (t.relIndex_Qv_pCoreOf hfr v).1
  have hone : (t.Qv v).relIndex (pCoreOf 2 (t.Gw (v - 1) v)) = 1 :=
    Subgroup.relIndex_eq_one.mpr hQ
  rw [hone] at hrel
  have hb : 1 < (if Even v then (2 ^ (2 * a + 1)) ^ 2 else 2 ^ f) := by
    split_ifs with hv
    · rw [← pow_mul]
      exact Nat.one_lt_two_pow (by omega)
    · exact Nat.one_lt_two_pow (by have := hfr.hf; omega)
  omega

private theorem sq_mem_Qv_of_mem_pCoreOf_of_odd {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : Odd v) {x : G}
    (hx : x ∈ pCoreOf 2 (t.Gw v (v + 1))) : x ^ 2 ∈ t.Qv v := by
  have hnot : ¬ Even v := by
    rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hv
    omega
  have hroot : t.rootOmega v ≤ pCoreOf 2 (t.Gw v (v + 1)) :=
    fun y hy => ((t.mem_rootOmega_iff hfr v).mp hy).1
  have hQroot : t.Qv v ≤ t.rootOmega v := t.Qv_le_rootOmega hfr v
  have hrel : (t.Qv v).relIndex (t.rootOmega v) =
      (t.Qv v).relIndex (pCoreOf 2 (t.Gw v (v + 1))) := by
    rw [t.relIndex_rootOmega hfr v, (t.relIndex_Qv_pCoreOf hfr v).2, if_neg hnot, if_neg hnot]
  have hmul := Subgroup.relIndex_mul_relIndex (t.Qv v) (t.rootOmega v)
    (pCoreOf 2 (t.Gw v (v + 1))) hQroot hroot
  rw [← hrel] at hmul
  have hne : (t.Qv v).relIndex (t.rootOmega v) ≠ 0 := by
    rw [t.relIndex_rootOmega hfr v, if_neg hnot]
    exact pow_ne_zero _ (by norm_num)
  have hone : (t.rootOmega v).relIndex (pCoreOf 2 (t.Gw v (v + 1))) = 1 := by
    have h : (t.Qv v).relIndex (t.rootOmega v) *
        (t.rootOmega v).relIndex (pCoreOf 2 (t.Gw v (v + 1))) =
        (t.Qv v).relIndex (t.rootOmega v) := hmul
    have h2 : (t.Qv v).relIndex (t.rootOmega v) *
        (t.rootOmega v).relIndex (pCoreOf 2 (t.Gw v (v + 1))) =
        (t.Qv v).relIndex (t.rootOmega v) * 1 := by
      rw [mul_one]
      exact h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h2
  have hEq : pCoreOf 2 (t.Gw v (v + 1)) = t.rootOmega v :=
    le_antisymm (Subgroup.relIndex_eq_one.mp hone) hroot
  rw [hEq] at hx
  exact ((t.mem_rootOmega_iff hfr v).mp hx).2

private theorem sq_mem_Qv_of_mem_pCoreOf_left_of_odd {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} (hv : Odd v) {x : G}
    (hx : x ∈ pCoreOf 2 (t.Gw (v - 1) v)) : x ^ 2 ∈ t.Qv v := by
  obtain ⟨y, -, -, hGw, hQv, -⟩ := t.exists_reflection v
  have hGw' : (t.Gw (v - 1) v).map (MulAut.conj y).toMonoidHom = t.Gw v (v + 1) := by
    have h := hGw (v - 1) v
    rw [show 2 * v - v = v by ring, show 2 * v - (v - 1) = v + 1 by ring] at h
    exact h
  have hQ' : (t.Qv v).map (MulAut.conj y).toMonoidHom = t.Qv v := by
    have h := hQv v
    rwa [show 2 * v - v = v by ring] at h
  have hx' : (MulAut.conj y) x ∈ pCoreOf 2 (t.Gw v (v + 1)) := by
    rw [← hGw', pCoreOf_map_mulEquiv]
    exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hx
  have hsq : ((MulAut.conj y) x) ^ 2 ∈ t.Qv v := sq_mem_Qv_of_mem_pCoreOf_of_odd t hfr hv hx'
  have hsq' : (MulAut.conj y⁻¹) (((MulAut.conj y) x) ^ 2) ∈ t.Qv v := by
    have hmem : (MulAut.conj y⁻¹) (((MulAut.conj y) x) ^ 2) ∈
        (t.Qv v).map (MulAut.conj y⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj y⁻¹).toMonoidHom hsq
    rwa [(CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQ').symm] at hmem
  have hx2eq : (MulAut.conj y⁻¹) (((MulAut.conj y) x) ^ 2) = x ^ 2 := by
    simp only [MulAut.conj_apply, inv_inv, pow_two]
    group
  rwa [hx2eq] at hsq'

private theorem inf_centralizer_le_of_map_conj {i v : ℤ} {g : G}
    (hGv : (t.Gv i).map (MulAut.conj g).toMonoidHom = t.Gv v)
    (hQv : (t.Qv i).map (MulAut.conj g).toMonoidHom = t.Qv v)
    (hbase : t.Gv i ⊓ centralizer (t.Qv i : Set G) ≤ t.Qv i) :
    t.Gv v ⊓ centralizer (t.Qv v : Set G) ≤ t.Qv v := by
  intro x hx
  obtain ⟨hxG, hxC⟩ := Subgroup.mem_inf.mp hx
  have hx'G : g⁻¹ * x * g ∈ t.Gv i :=
    (mem_map_conj_iff (K := t.Gv i) (g := g)).mp (hGv.symm ▸ hxG)
  have hx'C : g⁻¹ * x * g ∈ centralizer (t.Qv i : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hxC ⊢
    intro q hq
    have hq' : g * q * g⁻¹ ∈ t.Qv v := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hq
      rwa [hQv] at h
    have hcomm := hxC (g * q * g⁻¹) hq'
    calc
      q * (g⁻¹ * x * g) = g⁻¹ * ((g * q * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * q * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * x * g) * q := by group
  have hx'Q : g⁻¹ * x * g ∈ t.Qv i :=
    hbase (Subgroup.mem_inf.mpr ⟨hx'G, hx'C⟩)
  have hxmem : x ∈ (t.Qv i).map (MulAut.conj g).toMonoidHom :=
    (mem_map_conj_iff (K := t.Qv i) (g := g)).mpr hx'Q
  rwa [hQv] at hxmem

private theorem D1_ne_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.D1 ≠ ⊥ := by
  have hcard := t.card_D1 hfr
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have hgt : 2 < 2 ^ (2 * a + 1) := by
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num)
        (by have : 1 ≤ a := hfr.ha; omega)
  omega

private theorem D2_ne_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.D2 ≠ ⊥ := by
  have hcard := t.card_D2 hfr
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have hgt : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  omega

theorem mem_sup_Qv_of_le_pCoreOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {X : Subgroup G} (hX : X ≤ pCoreOf 2 (t.Gw v (v + 1)))
    (hXK : t.K ≤ normalizer (X : Set G)) (hXQ : ¬ X ≤ t.Qv v) {x : G}
    (hx : x ∈ pCoreOf 2 (t.Gw v (v + 1))) (hx2 : x ^ 2 ∈ t.Qv v) : x ∈ X ⊔ t.Qv v :=
  t.rootOmega_le_sup hfr v hX hXK hXQ ((t.mem_rootOmega_iff hfr v).mpr ⟨hx, hx2⟩)

theorem mem_sup_Qv_of_le_pCoreOf_left {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {X : Subgroup G} (hX : X ≤ pCoreOf 2 (t.Gw (v - 1) v))
    (hXK : t.K ≤ normalizer (X : Set G)) (hXQ : ¬ X ≤ t.Qv v) {x : G}
    (hx : x ∈ pCoreOf 2 (t.Gw (v - 1) v)) (hx2 : x ^ 2 ∈ t.Qv v) : x ∈ X ⊔ t.Qv v := by
  obtain ⟨y, -, hyK, hGw, hQv, -⟩ := t.exists_reflection v
  have hGw' : (t.Gw (v - 1) v).map (MulAut.conj y).toMonoidHom = t.Gw v (v + 1) := by
    have h := hGw (v - 1) v
    rw [show 2 * v - v = v by ring, show 2 * v - (v - 1) = v + 1 by ring] at h
    exact h
  have hQ' : (t.Qv v).map (MulAut.conj y).toMonoidHom = t.Qv v := by
    have h := hQv v
    rwa [show 2 * v - v = v by ring] at h
  have hX'R : X.map (MulAut.conj y).toMonoidHom ≤ pCoreOf 2 (t.Gw v (v + 1)) := by
    rw [← hGw', pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hX
  have hX'K : t.K ≤ normalizer ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
    have h := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hXK
    rw [show t.K.map (MulAut.conj y).toMonoidHom = t.K from
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyK,
      Subgroup.map_equiv_normalizer_eq] at h
    exact h
  have hX'Q : ¬ X.map (MulAut.conj y).toMonoidHom ≤ t.Qv v := by
    intro hle
    apply hXQ
    have h := Subgroup.map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hle
    rw [CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj X y,
      (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQ').symm] at h
    exact h
  have hx' : (MulAut.conj y) x ∈ pCoreOf 2 (t.Gw v (v + 1)) := by
    rw [← hGw', pCoreOf_map_mulEquiv]
    exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hx
  have hx'2 : ((MulAut.conj y) x) ^ 2 ∈ t.Qv v := by
    have hmem : (MulAut.conj y).toMonoidHom (x ^ 2) ∈
        (t.Qv v).map (MulAut.conj y).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hx2
    rw [hQ'] at hmem
    simpa only [map_pow, MulEquiv.coe_toMonoidHom] using hmem
  have hmem := t.mem_sup_Qv_of_le_pCoreOf hfr v (X := X.map (MulAut.conj y).toMonoidHom)
    hX'R hX'K hX'Q hx' hx'2
  have hback := Subgroup.mem_map_of_mem (MulAut.conj y⁻¹).toMonoidHom hmem
  rw [Subgroup.map_sup, CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj X y,
    (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQ').symm] at hback
  have hxeq : (MulAut.conj y⁻¹).toMonoidHom ((MulAut.conj y) x) = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rwa [hxeq] at hback

theorem Lv_le_sup {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {X : Subgroup G}
    (h₁ : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x ^ 2 ∈ t.Qv v → x ∈ X ⊔ t.Qv v)
    (h₂ : ∀ x ∈ pCoreOf 2 (t.Gw (v - 1) v), x ^ 2 ∈ t.Qv v → x ∈ X ⊔ t.Qv v) :
    t.Lv v ≤ X ⊔ t.Qv v := by
  by_cases hv : Even v
  · have hT : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x * x ∈ pCoreOf 2 (t.Lv v) →
        x ∈ X ⊔ pCoreOf 2 (t.Lv v) := by
      intro x hx hx2
      rw [t.pCoreOf_Lv hfr v] at hx2 ⊢
      exact h₁ x hx (by simpa [pow_two] using hx2)
    have hT' : ∀ x ∈ pCoreOf 2 (t.Gw (v - 1) v), x * x ∈ pCoreOf 2 (t.Lv v) →
        x ∈ X ⊔ pCoreOf 2 (t.Lv v) := by
      intro x hx hx2
      rw [t.pCoreOf_Lv hfr v] at hx2 ⊢
      exact h₂ x hx (by simpa [pow_two] using hx2)
    have h := le_sup_pCoreOf_of_sylow_ne_of_sz (L := t.Lv v)
      (T := pCoreOf 2 (t.Gw v (v + 1))) (T' := pCoreOf 2 (t.Gw (v - 1) v))
      (X := X) hfr.ha (t.nonempty_mulEquiv_sz_Lv hfr hv)
      (t.isSylowTwoOf_Lv hfr v) (t.isSylowTwoOf_Lv_left hfr v)
      (pCoreOf_Gw_ne t hfr v) hT hT'
    rwa [t.pCoreOf_Lv hfr v] at h
  · have hvodd : Odd v := by
      rcases Int.even_or_odd v with he | ho
      · exact absurd he hv
      · exact ho
    have hT : pCoreOf 2 (t.Gw v (v + 1)) ≤ X ⊔ pCoreOf 2 (t.Lv v) := by
      rw [t.pCoreOf_Lv hfr v]
      intro x hx
      exact h₁ x hx (sq_mem_Qv_of_mem_pCoreOf_of_odd t hfr hvodd hx)
    have hT' : pCoreOf 2 (t.Gw (v - 1) v) ≤ X ⊔ pCoreOf 2 (t.Lv v) := by
      rw [t.pCoreOf_Lv hfr v]
      intro x hx
      exact h₂ x hx (sq_mem_Qv_of_mem_pCoreOf_left_of_odd t hfr hvodd hx)
    have h := le_sup_pCoreOf_of_sylow_ne_of_l2 (L := t.Lv v)
      (T := pCoreOf 2 (t.Gw v (v + 1))) (T' := pCoreOf 2 (t.Gw (v - 1) v))
      (X := X) hfr.hf (t.isL2Quot_Lv hfr hvodd) (t.isSylowTwoOf_Lv hfr v)
      (t.isSylowTwoOf_Lv_left hfr v) (pCoreOf_Gw_ne t hfr v) hT hT'
    rwa [t.pCoreOf_Lv hfr v] at h

theorem Lv_le_centralizer_of_le_pCoreOf
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (v : ℤ)
    {X Y Z : Subgroup G} (hX : X ≤ pCoreOf 2 (t.Gw v (v + 1)))
    (hY : Y ≤ pCoreOf 2 (t.Gw (v - 1) v)) (hXK : t.K ≤ normalizer (X : Set G))
    (hYK : t.K ≤ normalizer (Y : Set G)) (hXQ : ¬ X ≤ t.Qv v) (hYQ : ¬ Y ≤ t.Qv v)
    (hXZ : X ≤ centralizer (Z : Set G)) (hYZ : Y ≤ centralizer (Z : Set G))
    (hQZ : t.Qv v ≤ centralizer (Z : Set G)) : t.Lv v ≤ centralizer (Z : Set G) := by
  have h₁' : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x ^ 2 ∈ t.Qv v →
      x ∈ (X ⊔ Y) ⊔ t.Qv v := by
    intro x hx hx2
    have hle : X ⊔ t.Qv v ≤ (X ⊔ Y) ⊔ t.Qv v :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    exact hle (t.mem_sup_Qv_of_le_pCoreOf hfr v hX hXK hXQ hx hx2)
  have h₂' : ∀ x ∈ pCoreOf 2 (t.Gw (v - 1) v), x ^ 2 ∈ t.Qv v →
      x ∈ (X ⊔ Y) ⊔ t.Qv v := by
    intro x hx hx2
    have hle : Y ⊔ t.Qv v ≤ (X ⊔ Y) ⊔ t.Qv v :=
      sup_le (le_sup_right.trans le_sup_left) le_sup_right
    exact hle (t.mem_sup_Qv_of_le_pCoreOf_left hfr v hY hYK hYQ hx hx2)
  have h := t.Lv_le_sup hfr v (X := X ⊔ Y) h₁' h₂'
  exact h.trans (sup_le (sup_le hXZ hYZ) hQZ)

theorem Gv_inf_centralizer_le_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) : t.Gv v ⊓ centralizer (t.Qv v : Set G) ≤ t.Qv v := by
  have hchar1 : CharTwo (P1 L1 L2 S) := by
    rw [P1, F1.parabolic_eq]
    exact hfr.hF.1.h1.charTwo
  have hchar2 : CharTwo (P2 L1 L2 S) := by
    rw [P2]
    have h := hfr.hF.1.h2.charTwo
    rw [← F1.parabolic_eq L2 L1 S, bigB_comm L1 L2 S] at h
    exact h
  have hbase0 : t.Gv 0 ⊓ centralizer (t.Qv 0 : Set G) ≤ t.Qv 0 := by
    rw [t.Gv_zero, t.Qv_zero]
    exact hchar1
  have hbase1 : t.Gv 1 ⊓ centralizer (t.Qv 1 : Set G) ≤ t.Qv 1 := by
    rw [t.Gv_one, t.Qv_one]
    exact hchar2
  by_cases hv : Even v
  · have hGv : (t.Gv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Gv v := by
      simpa [hv] using t.map_Gv_edgeElt v 0
    have hQv : (t.Qv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Qv v := by
      simpa [hv] using t.map_Qv_edgeElt v 0
    exact inf_centralizer_le_of_map_conj t hGv hQv hbase0
  · have hGv : (t.Gv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Gv v := by
      have h := t.map_Gv_edgeElt v 1
      rw [if_neg hv] at h
      rwa [show v + 1 - 1 = v by omega] at h
    have hQv : (t.Qv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Qv v := by
      have h := t.map_Qv_edgeElt v 1
      rw [if_neg hv] at h
      rwa [show v + 1 - 1 = v by omega] at h
    exact inf_centralizer_le_of_map_conj t hGv hQv hbase1

theorem eq_bot_of_le_Gw {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) {X : Subgroup G} (hX : X ≤ t.Gw v (v + 1))
    (h₀ : t.Lv v ≤ (t.Gv v ⊓ normalizer (X : Set G)) ⊔ t.Qv v)
    (h₁ : t.Lv (v + 1) ≤ (t.Gv (v + 1) ⊓ normalizer (X : Set G)) ⊔ t.Qv (v + 1)) :
    X = ⊥ := by
  let X' : Subgroup G := X.map (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom
  have hX'def : X' = X.map (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom := rfl
  have hX'le : X' ≤ bigB L1 L2 S := by
    have hXgw : X ≤ (t.Gw 0 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom := by
      rw [t.map_Gw_zero_one_edgeElt v]
      exact hX
    have hm := Subgroup.map_mono (f := (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom) hXgw
    rw [← hX'def, t.map_Gw_zero_one_edgeElt v,
      (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp
        (t.map_Gw_zero_one_edgeElt v)).symm, t.Gw_zero_one hfr.hF] at hm
    exact hm
  have hX'bot : X' = ⊥ := by
    by_cases hv : Even v
    · have hLv0 : (t.Lv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Lv v := by
        have h := t.map_qv_edgeElt (F₁ := L1 ⊔ Q1 L1 L2 S) (F₂ := L2 ⊔ Q2 L1 L2 S)
          (t.P1_le_normalizer_sup hfr) (t.P2_le_normalizer_sup hfr) v 0
        rw [if_pos hv] at h
        rwa [show v + 0 = v by omega] at h
      have hLv1 : (t.Lv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Lv (v + 1) := by
        have h := t.map_qv_edgeElt (F₁ := L1 ⊔ Q1 L1 L2 S) (F₂ := L2 ⊔ Q2 L1 L2 S)
          (t.P1_le_normalizer_sup hfr) (t.P2_le_normalizer_sup hfr) v 1
        rwa [if_pos hv] at h
      have hGv0 : (t.Gv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Gv v := by
        simpa [hv] using t.map_Gv_edgeElt v 0
      have hGv1 : (t.Gv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Gv (v + 1) := by
        simpa [hv] using t.map_Gv_edgeElt v 1
      have hQv0 : (t.Qv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Qv v := by
        simpa [hv] using t.map_Qv_edgeElt v 0
      have hQv1 : (t.Qv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Qv (v + 1) := by
        simpa [hv] using t.map_Qv_edgeElt v 1
      have hinf : (t.Gv v ⊓ normalizer (X : Set G)).map
          (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom =
          t.Gv 0 ⊓ normalizer (X' : Set G) := by
        rw [Subgroup.map_inf (t.Gv v) (normalizer (X : Set G))
          (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom
          (MulAut.conj (t.edgeElt v)⁻¹).injective,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hGv0).symm,
          Subgroup.map_equiv_normalizer_eq, ← hX'def]
      have h1' : L1 ≤ (P1 L1 L2 S ⊓ normalizer (X' : Set G)) ⊔ Q1 L1 L2 S := by
        have hm := Subgroup.map_mono
          (f := (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom) h₀
        rw [Subgroup.map_sup, hinf,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQv0).symm,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hLv0).symm] at hm
        rw [Lv_zero t, t.Gv_zero, t.Qv_zero] at hm
        exact le_sup_left.trans hm
      have hinf' : (t.Gv (v + 1) ⊓ normalizer (X : Set G)).map
          (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom =
          t.Gv 1 ⊓ normalizer (X' : Set G) := by
        rw [Subgroup.map_inf (t.Gv (v + 1)) (normalizer (X : Set G))
          (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom
          (MulAut.conj (t.edgeElt v)⁻¹).injective,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hGv1).symm,
          Subgroup.map_equiv_normalizer_eq, ← hX'def]
      have h2' : L2 ≤ (P2 L1 L2 S ⊓ normalizer (X' : Set G)) ⊔ Q2 L1 L2 S := by
        have hm := Subgroup.map_mono
          (f := (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom) h₁
        rw [Subgroup.map_sup, hinf',
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQv1).symm,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hLv1).symm] at hm
        rw [Lv_one t, t.Gv_one, t.Qv_one] at hm
        exact le_sup_left.trans hm
      exact eq_bot_of_le_bigB hfr.hF.1 hX'le h1' h2'
    · have hLv0 : (t.Lv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Lv (v + 1) := by
        have h := t.map_qv_edgeElt (F₁ := L1 ⊔ Q1 L1 L2 S) (F₂ := L2 ⊔ Q2 L1 L2 S)
          (t.P1_le_normalizer_sup hfr) (t.P2_le_normalizer_sup hfr) v 0
        rw [if_neg hv] at h
        simpa using h
      have hLv1 : (t.Lv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Lv v := by
        have h := t.map_qv_edgeElt (F₁ := L1 ⊔ Q1 L1 L2 S) (F₂ := L2 ⊔ Q2 L1 L2 S)
          (t.P1_le_normalizer_sup hfr) (t.P2_le_normalizer_sup hfr) v 1
        rw [if_neg hv] at h
        rwa [show v + 1 - 1 = v by omega] at h
      have hGv0 : (t.Gv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Gv (v + 1) := by
        have h := t.map_Gv_edgeElt v 0
        rw [if_neg hv] at h
        simpa using h
      have hGv1 : (t.Gv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Gv v := by
        have h := t.map_Gv_edgeElt v 1
        rw [if_neg hv] at h
        rwa [show v + 1 - 1 = v by omega] at h
      have hQv0 : (t.Qv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Qv (v + 1) := by
        have h := t.map_Qv_edgeElt v 0
        rw [if_neg hv] at h
        simpa using h
      have hQv1 : (t.Qv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Qv v := by
        have h := t.map_Qv_edgeElt v 1
        rw [if_neg hv] at h
        rwa [show v + 1 - 1 = v by omega] at h
      have hinf : (t.Gv (v + 1) ⊓ normalizer (X : Set G)).map
          (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom =
          t.Gv 0 ⊓ normalizer (X' : Set G) := by
        rw [Subgroup.map_inf (t.Gv (v + 1)) (normalizer (X : Set G))
          (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom
          (MulAut.conj (t.edgeElt v)⁻¹).injective,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hGv0).symm,
          Subgroup.map_equiv_normalizer_eq, ← hX'def]
      have h1' : L1 ≤ (P1 L1 L2 S ⊓ normalizer (X' : Set G)) ⊔ Q1 L1 L2 S := by
        have hm := Subgroup.map_mono
          (f := (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom) h₁
        rw [Subgroup.map_sup, hinf,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQv0).symm,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hLv0).symm] at hm
        rw [Lv_zero t, t.Gv_zero, t.Qv_zero] at hm
        exact le_sup_left.trans hm
      have hinf' : (t.Gv v ⊓ normalizer (X : Set G)).map
          (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom =
          t.Gv 1 ⊓ normalizer (X' : Set G) := by
        rw [Subgroup.map_inf (t.Gv v) (normalizer (X : Set G))
          (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom
          (MulAut.conj (t.edgeElt v)⁻¹).injective,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hGv1).symm,
          Subgroup.map_equiv_normalizer_eq, ← hX'def]
      have h2' : L2 ≤ (P2 L1 L2 S ⊓ normalizer (X' : Set G)) ⊔ Q2 L1 L2 S := by
        have hm := Subgroup.map_mono
          (f := (MulAut.conj (t.edgeElt v)⁻¹).toMonoidHom) h₀
        rw [Subgroup.map_sup, hinf',
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQv1).symm,
          (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hLv1).symm] at hm
        rw [Lv_one t, t.Gv_one, t.Qv_one] at hm
        exact le_sup_left.trans hm
      exact eq_bot_of_le_bigB hfr.hF.1 hX'le h1' h2'
  have hXeq : X = X'.map (MulAut.conj (t.edgeElt v)).toMonoidHom := by
    rw [hX'def]
    simpa using (CFSG.Timmesfeld.RankOne.map_conj_map_conj_inv X (t.edgeElt v)).symm
  rw [hXeq, hX'bot, Subgroup.map_bot]

theorem false_of_Zv_le_of_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {u v : ℤ} (huv : u = v + 1 ∨ u + 1 = v) (hZ : t.Zv u ≤ t.Zv v)
    (hC : t.Lv v ≤ centralizer (t.Zv v : Set G)) : False := by
  have hC' : t.Lv v ≤ normalizer (t.Zv u : Set G) :=
    hC.trans ((Subgroup.centralizer_le (fun z hz => hZ hz)).trans
      (Subgroup.centralizer_le_normalizer (t.Zv u : Set G)))
  rcases huv with rfl | h
  · have hNu : t.Lv (v + 1) ≤ normalizer (t.Zv (v + 1) : Set G) :=
      (t.Lv_le_Gv (v + 1)).trans (t.Gv_le_normalizer_Zv (v + 1))
    have hleft : t.Qv (v + 1) ≤ t.Gv v := by
      simpa using (t.Qv_le_Gv hfr (v + 1)).1
    have hX : t.Zv (v + 1) ≤ t.Gw v (v + 1) := by
      rw [t.Gw_add_one v]
      exact le_inf ((t.Zv_le_Qv (v + 1)).trans hleft)
        ((t.Zv_le_Qv (v + 1)).trans (t.Qv_le_Gv_self (v + 1)))
    have h0 : t.Lv v ≤ (t.Gv v ⊓ normalizer (t.Zv (v + 1) : Set G)) ⊔ t.Qv v :=
      (le_inf (t.Lv_le_Gv v) hC').trans le_sup_left
    have h1 : t.Lv (v + 1) ≤
        (t.Gv (v + 1) ⊓ normalizer (t.Zv (v + 1) : Set G)) ⊔ t.Qv (v + 1) :=
      (le_inf (t.Lv_le_Gv (v + 1)) hNu).trans le_sup_left
    exact t.Zv_ne_bot hfr.hF (v + 1) (t.eq_bot_of_le_Gw hfr v hX h0 h1)
  · subst v
    have hNu : t.Lv u ≤ normalizer (t.Zv u : Set G) :=
      (t.Lv_le_Gv u).trans (t.Gv_le_normalizer_Zv u)
    have hX : t.Zv u ≤ t.Gw u (u + 1) := by
      rw [t.Gw_add_one u]
      exact le_inf ((t.Zv_le_Qv u).trans (t.Qv_le_Gv_self u))
        ((t.Zv_le_Qv u).trans (t.Qv_le_Gv hfr u).2)
    have h0 : t.Lv u ≤ (t.Gv u ⊓ normalizer (t.Zv u : Set G)) ⊔ t.Qv u :=
      (le_inf (t.Lv_le_Gv u) hNu).trans le_sup_left
    have h1 : t.Lv (u + 1) ≤
        (t.Gv (u + 1) ⊓ normalizer (t.Zv u : Set G)) ⊔ t.Qv (u + 1) :=
      (le_inf (t.Lv_le_Gv (u + 1)) hC').trans le_sup_left
    exact t.Zv_ne_bot hfr.hF u (t.eq_bot_of_le_Gw hfr u hX h0 h1)

theorem K_inf_Lv_ne_bot {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (v : ℤ) : t.K ⊓ t.Lv v ≠ ⊥ := by
  have hD1ne := D1_ne_bot t hfr
  have hD2ne := D2_ne_bot t hfr
  have hD1K : t.D1 ≤ t.K := le_sup_left
  have hD2K : t.D2 ≤ t.K := le_sup_right
  have hD1Lv : t.D1 ≤ t.Lv 0 := by
    rw [Lv_zero t]
    exact (t.hD1hall.1.trans (F1.borelOf_le L1 S)).trans le_sup_left
  have hD2Lv : t.D2 ≤ t.Lv 1 := by
    rw [Lv_one t]
    exact (t.hD2hall.1.trans (F1.borelOf_le L2 S)).trans le_sup_left
  have hbase0 : t.K ⊓ t.Lv 0 ≠ ⊥ := by
    intro hbot
    exact hD1ne (le_bot_iff.mp (hbot ▸ le_inf hD1K hD1Lv))
  have hbase1 : t.K ⊓ t.Lv 1 ≠ ⊥ := by
    intro hbot
    exact hD2ne (le_bot_iff.mp (hbot ▸ le_inf hD2K hD2Lv))
  by_cases hv : Even v
  · have hK : t.K.map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.edgeElt_mem_normalizer v)
    have hLv : (t.Lv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Lv v := by
      have h := t.map_qv_edgeElt (F₁ := L1 ⊔ Q1 L1 L2 S) (F₂ := L2 ⊔ Q2 L1 L2 S)
        (t.P1_le_normalizer_sup hfr) (t.P2_le_normalizer_sup hfr) v 0
      rw [if_pos hv] at h
      rwa [show v + 0 = v by omega] at h
    have hmap : (t.K ⊓ t.Lv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
        t.K ⊓ t.Lv v := by
      rw [Subgroup.map_inf t.K (t.Lv 0) (MulAut.conj (t.edgeElt v)).toMonoidHom
        (MulAut.conj (t.edgeElt v)).injective, hK, hLv]
    intro hbot
    apply hbase0
    have hzero : (t.K ⊓ t.Lv 0).map (MulAut.conj (t.edgeElt v)).toMonoidHom = ⊥ := by
      rw [hmap, hbot]
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (MulAut.conj (t.edgeElt v)).injective).mp hzero
  · have hK : t.K.map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (t.edgeElt_mem_normalizer v)
    have hLv : (t.Lv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = t.Lv v := by
      have h := t.map_qv_edgeElt (F₁ := L1 ⊔ Q1 L1 L2 S) (F₂ := L2 ⊔ Q2 L1 L2 S)
        (t.P1_le_normalizer_sup hfr) (t.P2_le_normalizer_sup hfr) v 1
      rw [if_neg hv] at h
      rwa [show v + 1 - 1 = v by omega] at h
    have hmap : (t.K ⊓ t.Lv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
        t.K ⊓ t.Lv v := by
      rw [Subgroup.map_inf t.K (t.Lv 1) (MulAut.conj (t.edgeElt v)).toMonoidHom
        (MulAut.conj (t.edgeElt v)).injective, hK, hLv]
    intro hbot
    apply hbase1
    have hzero : (t.K ⊓ t.Lv 1).map (MulAut.conj (t.edgeElt v)).toMonoidHom = ⊥ := by
      rw [hmap, hbot]
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (MulAut.conj (t.edgeElt v)).injective).mp hzero

theorem commutator_mem_Qv_of_odd {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {k : G} (hk : k ∈ normalizer (t.Lv v : Set G))
    (hodd : Odd (orderOf k))
    (hcent : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x ^ 2 ∈ t.Qv v → ⁅k, x⁆ ∈ t.Qv v) :
    ∀ l ∈ t.Lv v, ⁅k, l⁆ ∈ t.Qv v := by
  by_cases hv : Even v
  · have hT : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x * x ∈ pCoreOf 2 (t.Lv v) →
        ⁅k, x⁆ ∈ pCoreOf 2 (t.Lv v) := by
      intro x hx hx2
      rw [t.pCoreOf_Lv hfr v] at hx2 ⊢
      exact hcent x hx (by simpa [pow_two] using hx2)
    have h := commutator_mem_pCoreOf_of_odd_of_sz (L := t.Lv v)
      (T := pCoreOf 2 (t.Gw v (v + 1))) hfr.ha (t.nonempty_mulEquiv_sz_Lv hfr hv)
      (t.isSylowTwoOf_Lv hfr v) hk hodd hT
    intro l hl
    have hl' := h l hl
    rwa [t.pCoreOf_Lv hfr v] at hl'
  · have hvodd : Odd v := by
      rcases Int.even_or_odd v with he | ho
      · exact absurd he hv
      · exact ho
    have hT : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), ⁅k, x⁆ ∈ pCoreOf 2 (t.Lv v) := by
      intro x hx
      rw [t.pCoreOf_Lv hfr v]
      exact hcent x hx (sq_mem_Qv_of_mem_pCoreOf_of_odd t hfr hvodd hx)
    have h := commutator_mem_pCoreOf_of_odd_of_l2 (L := t.Lv v)
      (T := pCoreOf 2 (t.Gw v (v + 1))) hfr.hf (t.isL2Quot_Lv hfr hvodd)
      (t.isSylowTwoOf_Lv hfr v) hk hodd hT
    intro l hl
    have hl' := h l hl
    rwa [t.pCoreOf_Lv hfr v] at hl'

theorem map_Lv_edgeElt {a f : ℕ} (hfr : Frame L1 L2 S a f) (v i : ℤ) :
    (t.Lv i).map (MulAut.conj (t.edgeElt v)).toMonoidHom =
      t.Lv (if Even v then v + i else v + 1 - i) :=
  t.map_qv_edgeElt (F₁ := L1 ⊔ Q1 L1 L2 S) (F₂ := L2 ⊔ Q2 L1 L2 S)
    (t.P1_le_normalizer_sup hfr) (t.P2_le_normalizer_sup hfr) v i

theorem Lv_le_centralizer_of_even_sub {a f : ℕ} (hfr : Frame L1 L2 S a f) {u v : ℤ}
    (huv : Even (u - v)) (hC : t.Lv u ≤ centralizer (t.Zv u : Set G)) :
    t.Lv v ≤ centralizer (t.Zv v : Set G) := by
  have hvu : Even (v - u) := by
    have h := Even.neg huv
    rwa [show -(u - v) = v - u by ring] at h
  let g : G := t.edgeElt (v - u)
  have hLv : (t.Lv u).map (MulAut.conj g).toMonoidHom = t.Lv v := by
    have h := t.map_Lv_edgeElt hfr (v - u) u
    rw [if_pos hvu] at h
    rwa [show v - u + u = v by ring] at h
  have hZv : (t.Zv u).map (MulAut.conj g).toMonoidHom = t.Zv v := by
    have h := t.map_Zv_edgeElt (v - u) u
    rw [if_pos hvu] at h
    rwa [show v - u + u = v by ring] at h
  have hcent : (centralizer (t.Zv u : Set G)).map (MulAut.conj g).toMonoidHom ≤
      centralizer (t.Zv v : Set G) := by
    have h := Subgroup.map_centralizer_le_centralizer_image (s := (t.Zv u : Set G))
      (f := (MulAut.conj g).toMonoidHom)
    have hset : (MulAut.conj g).toMonoidHom '' (t.Zv u : Set G) = (t.Zv v : Set G) := by
      rw [← Subgroup.coe_map, hZv]
    rwa [hset] at h
  calc
    t.Lv v = (t.Lv u).map (MulAut.conj g).toMonoidHom := hLv.symm
    _ ≤ (centralizer (t.Zv u : Set G)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hC
    _ ≤ centralizer (t.Zv v : Set G) := hcent

theorem Zv_le_of_Lv_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {u v : ℤ} (huv : u = v + 1 ∨ u + 1 = v)
    (hC : t.Lv u ≤ centralizer (t.Zv u : Set G)) : t.Zv u ≤ t.Zv v := by
  have hQvGv : t.Qv v ≤ t.Gv u := by
    rcases huv with h | h
    · subst u
      simpa using (t.Qv_le_Gv hfr v).2
    · subst v
      simpa using (t.Qv_le_Gv hfr (u + 1)).1
  have hQvL : t.Qv v ≤ t.Lv u := t.le_Lv hfr (t.isPGroup_Qv v) hQvGv
  have hZuGv : t.Zv u ≤ t.Gv v := by
    refine (t.Zv_le_Qv u).trans ?_
    rcases huv with h | h
    · subst u
      simpa using (t.Qv_le_Gv hfr (v + 1)).1
    · subst v
      simpa using (t.Qv_le_Gv hfr u).2
  have hZuC : t.Zv u ≤ centralizer (t.Qv v : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hC (hQvL hq)) z hz).symm
  have hZuQv : t.Zv u ≤ t.Qv v :=
    (le_inf hZuGv hZuC).trans (t.Gv_inf_centralizer_le_Qv hfr v)
  intro x hx
  rw [t.Zv_eq v]
  refine Subgroup.subset_closure ⟨⟨hZuQv hx, hZuC hx⟩, ?_⟩
  rw [t.Zv_eq u] at hx
  exact A4.sq_eq_one_of_mem_omegaOneCenterOf hx

theorem relIndex_Qv_le_of_sq_mem {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {A : Subgroup G}
    (hA : A ≤ pCoreOf 2 (t.Gw v (v + 1))) (hsq : ∀ x ∈ A, x ^ 2 ∈ t.Qv v) :
    (t.Qv v).relIndex A ≤ if Even v then 2 ^ (2 * a + 1) else 2 ^ f := by
  have hAroot : A ≤ t.rootOmega v := by
    intro x hx
    exact (t.mem_rootOmega_iff hfr v).mpr ⟨hA hx, hsq x hx⟩
  have hne : (t.Qv v).relIndex (t.rootOmega v) ≠ 0 := by
    rw [t.relIndex_rootOmega hfr v]
    split_ifs <;> positivity
  exact (Subgroup.relIndex_le_of_le_right hAroot hne).trans_eq (t.relIndex_rootOmega hfr v)

theorem relIndex_Qv_le_of_sq_mem_left {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {A : Subgroup G}
    (hA : A ≤ pCoreOf 2 (t.Gw (v - 1) v)) (hsq : ∀ x ∈ A, x ^ 2 ∈ t.Qv v) :
    (t.Qv v).relIndex A ≤ if Even v then 2 ^ (2 * a + 1) else 2 ^ f := by
  obtain ⟨y, -, -, hGw, hQv, -⟩ := t.exists_reflection v
  have hGw' : (t.Gw (v - 1) v).map (MulAut.conj y).toMonoidHom = t.Gw v (v + 1) := by
    have h := hGw (v - 1) v
    rw [show 2 * v - v = v by ring, show 2 * v - (v - 1) = v + 1 by ring] at h
    exact h
  have hQ' : (t.Qv v).map (MulAut.conj y).toMonoidHom = t.Qv v := by
    have h := hQv v
    rwa [show 2 * v - v = v by ring] at h
  have hA' : A.map (MulAut.conj y).toMonoidHom ≤ pCoreOf 2 (t.Gw v (v + 1)) := by
    rw [← hGw', pCoreOf_map_mulEquiv]
    exact Subgroup.map_mono hA
  have hsq' : ∀ x ∈ A.map (MulAut.conj y).toMonoidHom, x ^ 2 ∈ t.Qv v := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : (MulAut.conj y).toMonoidHom (b ^ 2) ∈
        (t.Qv v).map (MulAut.conj y).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom (hsq b hb)
    rw [hQ'] at hmem
    simpa only [map_pow, MulEquiv.coe_toMonoidHom] using hmem
  have h := t.relIndex_Qv_le_of_sq_mem hfr v hA' hsq'
  have hrel : (t.Qv v).relIndex (A.map (MulAut.conj y).toMonoidHom) =
      (t.Qv v).relIndex A := by
    conv_lhs => rw [← hQ']
    exact Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj y).injective
  rwa [hrel] at h

theorem le_card_Zv_of_not_le_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) (hC : ¬ t.Lv v ≤ centralizer (t.Zv v : Set G)) :
    (if Even v then (2 ^ (2 * a + 1)) ^ 4 else (2 ^ f) ^ 2) ≤ Nat.card (t.Zv v) := by
  have hsec : CFSG.GH74.QTGen4.DSGen4.IsElemSec (⊥ : Subgroup G) (t.Zv v) := by
    refine ⟨bot_le, ?_, ?_⟩
    · rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer v hx) w (t.Zv_le_Qv v hw)
    · intro e he
      rw [Subgroup.mem_bot]
      rw [t.Zv_eq v] at he
      exact A4.sq_eq_one_of_mem_omegaOneCenterOf he
  have hbot : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro n
    simp
  have hL : t.Lv v ≤ Subgroup.normalizer (t.Zv v : Set G) ⊓
      Subgroup.normalizer (⊥ : Subgroup G) :=
    le_inf ((t.Lv_le_Gv v).trans (t.Gv_le_normalizer_Zv v)) (hbot ▸ le_top)
  have hQ : ∀ p ∈ pCoreOf 2 (t.Lv v), ∀ w ∈ t.Zv v, ⁅p, w⁆ ∈ (⊥ : Subgroup G) := by
    intro p hp w hw
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have hp' : p ∈ t.Qv v := by rwa [t.pCoreOf_Lv hfr v] at hp
    exact Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer v hw) p hp'
  have hnt : ∃ l ∈ t.Lv v, ∃ w ∈ t.Zv v, ⁅l, w⁆ ∉ (⊥ : Subgroup G) := by
    by_contra h
    push Not at h
    apply hC
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : ⁅l, w⁆ = 1 := by simpa using h l hl w hw
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  by_cases hv : Even v
  · rw [if_pos hv]
    have h := two_pow_le_relIndex_of_nontrivial_of_sz (L := t.Lv v) (V := t.Zv v)
      (Z := ⊥) hfr.ha (t.nonempty_mulEquiv_sz_Lv hfr hv) hsec hL hQ hnt
    have h2 : (2 ^ (2 * a + 1)) ^ 4 = 2 ^ (4 * (2 * a + 1)) := by
      conv_lhs => rw [← pow_mul, Nat.mul_comm (2 * a + 1) 4]
    rwa [Subgroup.relIndex_bot_left, ← h2] at h
  · rw [if_neg hv]
    have hodd : Odd v := by
      rcases Int.even_or_odd v with he | ho
      · exact absurd he hv
      · exact ho
    have h := CFSG.Quasithin.St84.two_pow_le_relIndex_of_nontrivial (L := t.Lv v)
      (V := t.Zv v) (Z := ⊥) (m := f) (by have := hfr.hf; omega) (t.isL2Quot_Lv hfr hodd)
      hsec hL hQ hnt
    have h2 : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by
      conv_lhs => rw [← pow_mul, Nat.mul_comm f 2]
    rwa [Subgroup.relIndex_bot_left, ← h2] at h

theorem commutator_mem_Qv_of_mem_centralizer {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (v : ℤ) {X : Subgroup G}
    (hX : X ≤ pCoreOf 2 (t.Gw v (v + 1))) (hXK : t.K ≤ normalizer (X : Set G))
    (hXQ : ¬ X ≤ t.Qv v) {k : G} (hkK : k ∈ t.K) (hkX : k ∈ centralizer (X : Set G)) :
    ∀ l ∈ t.Lv v, ⁅k, l⁆ ∈ t.Qv v := by
  have hcent : ∀ x ∈ pCoreOf 2 (t.Gw v (v + 1)), x ^ 2 ∈ t.Qv v → ⁅k, x⁆ ∈ t.Qv v := by
    intro x hx hx2
    have hXN : X ≤ normalizer (t.Qv v : Set G) :=
      hX.trans ((pCoreOf_le 2 _).trans ((win_le_qv (a := v) (b := v + 1) (i := v) le_rfl
        (by omega)).trans (t.Gv_le_normalizer_Qv v)))
    have hxsup : x ∈ X ⊔ t.Qv v :=
      t.mem_sup_Qv_of_le_pCoreOf hfr v hX hXK hXQ hx hx2
    change x ∈ ((X ⊔ t.Qv v : Subgroup G) : Set G) at hxsup
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X (t.Qv v) hXN] at hxsup
    obtain ⟨y, hyX, q, hqQ, hxeq⟩ := Set.mem_mul.mp hxsup
    have hkQ : k ∈ normalizer (t.Qv v : Set G) :=
      (t.K_le_Gv v).trans (t.Gv_le_normalizer_Qv v) hkK
    have hky : k * y = y * k :=
      (Subgroup.mem_centralizer_iff.mp hkX y hyX).symm
    have hcommq : ⁅k, q⁆ ∈ t.Qv v :=
      (t.Qv v).mul_mem ((Subgroup.mem_normalizer_iff.mp hkQ q).mp hqQ)
        ((t.Qv v).inv_mem hqQ)
    have hyN : y ∈ normalizer (t.Qv v : Set G) := hXN hyX
    have hcommy : y * ⁅k, q⁆ * y⁻¹ ∈ t.Qv v :=
      (Subgroup.mem_normalizer_iff.mp hyN ⁅k, q⁆).mp hcommq
    have hkey : ⁅k, x⁆ = y * ⁅k, q⁆ * y⁻¹ := by
      rw [← hxeq]
      simp only [commutatorElement_def]
      rw [show k * (y * q) = y * (k * q) by rw [← mul_assoc, hky, mul_assoc], mul_inv_rev]
      group
    rw [hkey]
    exact hcommy
  have hkN : k ∈ normalizer (t.Lv v : Set G) :=
    t.Gv_le_normalizer_Lv hfr v ((t.K_le_Gv v) hkK)
  have hodd : Odd (orderOf k) := by
    have hdvd : orderOf k ∣ Nat.card t.K := by
      rw [← Subgroup.orderOf_mk (H := t.K) k hkK]
      exact orderOf_dvd_natCard (⟨k, hkK⟩ : t.K)
    exact Odd.of_dvd_nat t.hHall.2.1 hdvd
  exact t.commutator_mem_Qv_of_odd hfr v hkN hodd hcent

theorem mem_Qv_of_forall_commutator_mem {a f : ℕ} (hfr : Frame L1 L2 S a f) (v : ℤ) {k : G}
    (hk : k ∈ t.Lv v) (hc : ∀ l ∈ t.Lv v, ⁅k, l⁆ ∈ t.Qv v) : k ∈ t.Qv v := by
  let L : Subgroup G := t.Lv v
  let N : Subgroup ↥L := CFSG.pCore 2 ↥L
  haveI : N.Normal := CFSG.pCore_normal
  have hN : N.map L.subtype = t.Qv v := by
    have h := t.pCoreOf_Lv hfr v
    simpa only [N, L, CFSG.Open.pCoreOf] using h
  have hk' : ∀ l : ↥L, ⁅(⟨k, hk⟩ : ↥L), l⁆ ∈ N := by
    intro l
    rw [← Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective, hN,
      map_commutatorElement]
    exact hc (l : G) l.2
  have hkcent : (QuotientGroup.mk' N (⟨k, hk⟩ : ↥L)) ∈
      Subgroup.center (oTwoQuot ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hone : ⁅QuotientGroup.mk' N (⟨k, hk⟩ : ↥L), QuotientGroup.mk' N l⁆ = 1 := by
      rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk' l
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  have hZ : Subgroup.center (oTwoQuot ↥L) = ⊥ := by
    by_cases hv : Even v
    · obtain ⟨e⟩ := t.nonempty_mulEquiv_sz_Lv hfr hv
      have hmap := Subgroup.map_center_eq e
      rw [CFSG.Quasithin.Stroth.center_sz a hfr.ha] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
    · have hodd : Odd v := by
        rcases Int.even_or_odd v with he | ho
        · exact absurd he hv
        · exact ho
      obtain ⟨e⟩ := t.isL2Quot_Lv hfr hodd
      have hmap := Subgroup.map_center_eq e
      rw [CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 2 f)] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  have hk1 : QuotientGroup.mk' N (⟨k, hk⟩ : ↥L) = 1 := by
    have h := hkcent
    rw [hZ] at h
    exact Subgroup.mem_bot.mp h
  have hk'N : (⟨k, hk⟩ : ↥L) ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact hk1
  have hmem : L.subtype ⟨k, hk⟩ ∈ t.Qv v := by
    rw [← hN]
    exact Subgroup.mem_map_of_mem L.subtype hk'N
  simpa using hmem

end Track

end CFSG.Quasithin.Stroth.Rq

end
