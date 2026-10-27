module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackBasic
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackMove
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackVertex
import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.Str83RqRoot
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzNatSub
import CFSG.Quasithin.Recognition.Stroth.Str83RqSzNatCount
import CFSG.ClassicalInvolution.SubnormalCommutator
import CFSG.Goldschmidt.Steps.G54
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits
open CFSG.Timmesfeld.RankOne
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem szE1_le_normalizer_map_conj {X : Subgroup G} {g : G}
    (hXK : t.K ≤ normalizer (X : Set G)) (hgK : g ∈ normalizer (t.K : Set G)) :
    t.K ≤ normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hmap := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hXK
  have hKmap : t.K.map (MulAut.conj g).toMonoidHom = t.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgK
  calc t.K = t.K.map (MulAut.conj g).toMonoidHom := hKmap.symm
    _ ≤ (normalizer (X : Set G)).map (MulAut.conj g).toMonoidHom := hmap
    _ ≤ normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map (H := X) (f := (MulAut.conj g).toMonoidHom)

private theorem szE1_reflect_Gw {h : ℤ} {y : G}
    (hyGw : ∀ u w : ℤ, (t.Gw u w).map (MulAut.conj y).toMonoidHom =
      t.Gw (2 * h - w) (2 * h - u)) :
    (t.Gw (h - 1) h).map (MulAut.conj y).toMonoidHom = t.Gw h (h + 1) := by
  rw [hyGw (h - 1) h, show 2 * h - h = h from by ring,
    show 2 * h - (h - 1) = h + 1 from by ring]

private theorem szE1_reflect_Qv {h : ℤ} {y : G}
    (hyQ : ∀ i : ℤ, (t.Qv i).map (MulAut.conj y).toMonoidHom = t.Qv (2 * h - i)) :
    (t.Qv h).map (MulAut.conj y).toMonoidHom = t.Qv h := by
  rw [hyQ h, show 2 * h - h = h from by ring]

private theorem szE4_card_inf_centralizer {a : ℕ} {h : ℤ}
    {U : Subgroup G} {a0 : G} (hnat : IsSzNaturalSection (t.Lv h) U ⊥ a)
    (hUL : t.Lv h ≤ normalizer (U : Set G)) (ha0L : a0 ∈ t.Lv h)
    (ha0sq : a0 * a0 ∈ pCoreOf 2 (t.Lv h)) (ha0Q : a0 ∉ pCoreOf 2 (t.Lv h)) :
    Nat.card (U ⊓ Subgroup.centralizer ({a0} : Set G) : Subgroup G) =
      (2 ^ (2 * a + 1)) ^ 2 :=
  natCard_inf_centralizer_of_isSzNaturalSection hnat hUL ha0L ha0sq ha0Q

private theorem szE4_card_image {a : ℕ} {U : Subgroup G} {a0 : G}
    (φ : ↥U →* ↥U)
    (hker : φ.ker = (U ⊓ Subgroup.centralizer ({a0} : Set G)).subgroupOf U)
    (hcardker : Nat.card (U ⊓ Subgroup.centralizer ({a0} : Set G) : Subgroup G) =
      (2 ^ (2 * a + 1)) ^ 2)
    (hcardU : Nat.card U = (2 ^ (2 * a + 1)) ^ 4) :
    Nat.card (φ.range.map U.subtype : Subgroup G) = (2 ^ (2 * a + 1)) ^ 2 := by
  have hmap : Nat.card (φ.range.map U.subtype : Subgroup G) = Nat.card φ.range :=
    Subgroup.card_map_of_injective (K := φ.range) (f := U.subtype) U.subtype_injective
  have hker' : Nat.card φ.ker = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      U ⊓ Subgroup.centralizer ({a0} : Set G) ≤ U)).toEquiv).trans hcardker
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker', hcardU] at h
  have h' : (2 ^ (2 * a + 1)) ^ 2 * Nat.card φ.range =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1)) ^ 2 := by
    rw [h]
    ring
  have hpos : 0 < (2 ^ (2 * a + 1)) ^ 2 := by positivity
  rw [hmap, Nat.eq_of_mul_eq_mul_left hpos h']

private theorem szE2_commutator_commute {z x w : G} (hx2 : x ^ 2 = 1)
    (hz2 : z ^ 2 = 1) (hw : w = ⁅z, x⁆) (hzw : z * w = w * z) : w * x = x * w := by
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hxinv : x⁻¹ = x := by
    calc x⁻¹ = x⁻¹ * (x * x) := by rw [hxx, mul_one]
      _ = x := by group
  have hzinv : z⁻¹ = z := by
    calc z⁻¹ = z⁻¹ * (z * z) := by rw [hzz, mul_one]
      _ = z := by group
  have hzx : x * z * x = z * x * z * x * z := by
    have h := hzw
    rw [hw, commutatorElement_def, hzinv, hxinv] at h
    calc x * z * x = z * (z * x * z * x) := by
          rw [show z * (z * x * z * x) = (z * z) * x * z * x by group, hzz, one_mul]
      _ = (z * x * z * x) * z := h
  have hxwx : x * w * x⁻¹ = w := by
    rw [hxinv, hw, commutatorElement_def, hzinv, hxinv]
    calc x * (z * x * z * x) * x = (x * z * x) * (z * x * x) := by group
      _ = (x * z * x) * z := by
        rw [show z * x * x = z * (x * x) by group, hxx, mul_one]
      _ = ((z * x * z * x) * z) * z := by rw [hzx]
      _ = z * x * z * x := by rw [mul_assoc, hzz, mul_one]
  have hxwx' : x * w * x = w := by
    have h := hxwx
    rwa [hxinv] at h
  calc w * x = (x * w * x) * x := by rw [hxwx']
    _ = x * w := by
      rw [show (x * w * x) * x = x * (w * (x * x)) by group, hxx, mul_one]

variable [Finite G]

private theorem szEnd_Zv_le_Gw_shift {i a b : ℤ} (h : t.Zv i ≤ t.Gw a b) (k : ℤ) :
    t.Zv (i + 2 * k) ≤ t.Gw (a + 2 * k) (b + 2 * k) := by
  have hZ : (t.Zv i).map (MulAut.conj (t.edgeElt (2 * k))).toMonoidHom =
      t.Zv (i + 2 * k) := by
    rw [t.map_Zv_edgeElt (2 * k) i, if_pos (even_two_mul k)]
    rw [show 2 * k + i = i + 2 * k by ring]
  have hG : (t.Gw a b).map (MulAut.conj (t.edgeElt (2 * k))).toMonoidHom =
      t.Gw (a + 2 * k) (b + 2 * k) := by
    rw [t.map_Gw_edgeElt (2 * k) a b, if_pos (even_two_mul k)]
    rw [show 2 * k + a = a + 2 * k by ring, show 2 * k + b = b + 2 * k by ring]
  rw [← hZ, ← hG]
  exact Subgroup.map_mono h

private theorem szEnd_not_Zv_le_Gv_shift {i j : ℤ} (h : ¬ t.Zv i ≤ t.Gv j) (k : ℤ) :
    ¬ t.Zv (i + 2 * k) ≤ t.Gv (j + 2 * k) := by
  intro hle
  apply h
  have hZ : (t.Zv (i + 2 * k)).map (MulAut.conj (t.edgeElt (2 * (-k)))).toMonoidHom =
      t.Zv i := by
    rw [t.map_Zv_edgeElt (2 * (-k)) (i + 2 * k), if_pos (even_two_mul (-k))]
    rw [show 2 * (-k) + (i + 2 * k) = i by ring]
  have hG : (t.Gv (j + 2 * k)).map (MulAut.conj (t.edgeElt (2 * (-k)))).toMonoidHom =
      t.Gv j := by
    rw [t.map_Gv_edgeElt (2 * (-k)) (j + 2 * k), if_pos (even_two_mul (-k))]
    rw [show 2 * (-k) + (j + 2 * k) = j by ring]
  have hmap := Subgroup.map_mono
    (f := (MulAut.conj (t.edgeElt (2 * (-k)))).toMonoidHom) hle
  rwa [hZ, hG] at hmap

private theorem szEnd_card_Zv_shift (i k : ℤ) :
    Nat.card (t.Zv (i + 2 * k)) = Nat.card (t.Zv i) := by
  have hZ : (t.Zv i).map (MulAut.conj (t.edgeElt (2 * k))).toMonoidHom =
      t.Zv (i + 2 * k) := by
    rw [t.map_Zv_edgeElt (2 * k) i, if_pos (even_two_mul k)]
    rw [show 2 * k + i = i + 2 * k by ring]
  rw [← hZ, Subgroup.card_map_of_injective (MulAut.conj (t.edgeElt (2 * k))).injective]

private theorem szEnd_Lv_le_centralizer_Zv (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) {v : ℤ}
    (hv : Odd v) : t.Lv v ≤ centralizer (t.Zv v : Set G) := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · exact absurd hv (Int.not_odd_iff_even.mpr (even_two_mul k))
  · have hbase : t.Lv 1 ≤ centralizer (t.Zv 1 : Set G) := by
      rw [t.Lv_one]
      refine sup_le ?_ ?_
      · simpa [t.Zv_one] using hZL
      · have hQ : t.Zv 1 ≤ centralizer (Q2 L1 L2 S : Set G) := by
          have h := t.Zv_le_centralizer 1
          rwa [t.Qv_one] at h
        exact Subgroup.le_centralizer_iff.mpr hQ
    have hZ : (t.Zv 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        t.Zv (1 + 2 * k) := by
      change (qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ 1).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ (1 + 2 * k)
      exact map_qv_tau_pow 1 k
    have hL : (t.Lv 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        t.Lv (1 + 2 * k) := by
      change (qv (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) t.x₁ t.x₂ 1).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        qv (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) t.x₁ t.x₂ (1 + 2 * k)
      exact map_qv_tau_pow 1 k
    have hmap : (t.Lv 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom ≤
        Subgroup.centralizer (t.Zv (1 + 2 * k) : Set G) := by
      have h := Subgroup.map_mono
        (f := (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) hbase
      rwa [CFSG.Goldschmidt.G54.map_conj_centralizer ((t.x₂ * t.x₁) ^ k) (t.Zv 1), hZ] at h
    rwa [hL, show (1 : ℤ) + 2 * k = 2 * k + 1 by ring] at hmap

private theorem szE1_base {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) :
    t.Zv 0 ⊓ centralizer (t.Lv 0 : Set G) = ⊥ := by
  set X₀ : Subgroup G := t.Zv 0 ⊓ centralizer (t.Lv 0 : Set G) with hX₀
  have hS : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hfr.hF.1 hfr.hN (Or.inl ⟨a, hfr.ha, hfr.hSz⟩)
  have hQ1S : Q1 L1 L2 S ≤ S := by
    have h : Q1 L1 L2 S ≤ (S ⊓ L1) ⊔ Q1 L1 L2 S := le_sup_right
    exact h.trans hS.symm.le
  have hXZ1 : X₀ ≤ Z1 L1 L2 S := by
    rw [← t.Zv_zero]
    exact hX₀.le.trans inf_le_left
  have hXQ1 : X₀ ≤ Q1 L1 L2 S :=
    (hX₀.le.trans inf_le_left).trans ((t.Zv_le_Qv 0).trans_eq t.Qv_zero)
  have hL1Lv : L1 ≤ t.Lv 0 := by
    rw [t.Lv_zero]
    exact le_sup_left
  have hXcL1 : X₀ ≤ centralizer (L1 : Set G) :=
    hX₀.le.trans (inf_le_right.trans (Subgroup.centralizer_le hL1Lv))
  have hXcQ1 : X₀ ≤ centralizer (Q1 L1 L2 S : Set G) := by
    have h := t.Zv_le_centralizer 0
    rw [t.Qv_zero] at h
    exact (hX₀.le.trans inf_le_left).trans h
  have hXcS : X₀ ≤ centralizer (S : Set G) := by
    refine Subgroup.le_centralizer_iff.mpr ?_
    refine hS.le.trans ?_
    exact sup_le (inf_le_right.trans (Subgroup.le_centralizer_iff.mp hXcL1))
      (Subgroup.le_centralizer_iff.mp hXcQ1)
  have hpc : pCoreOf 2 (bigB L1 L2 S) = S := by
    rw [← t.Gw_zero_one hfr.hF, t.pCoreOf_Gw_zero_one hfr]
  have hXZ2 : X₀ ≤ Z2 L1 L2 S := by
    have hpc' : Subgroup.centralizer (pCoreOf 2 (bigB L1 L2 S) : Set G) =
        Subgroup.centralizer (S : Set G) :=
      congrArg (fun T : Subgroup G => Subgroup.centralizer (T : Set G)) hpc
    exact (le_inf hXZ1 (hpc' ▸ hXcS)).trans (z1_inf_centralizer_le_z2 hfr.hF.1)
  have hXbigB : X₀ ≤ bigB L1 L2 S :=
    hXQ1.trans (hQ1S.trans (le_sup_right : S ≤ bigB L1 L2 S))
  have hL1cent : L1 ≤ centralizer (X₀ : Set G) := Subgroup.le_centralizer_iff.mp hXcL1
  have hL2cent : L2 ≤ centralizer (X₀ : Set G) := by
    refine Subgroup.le_centralizer_iff.mpr ?_
    refine hXZ2.trans ?_
    rw [show Z2 L1 L2 S = t.Zv 1 from t.Zv_one.symm]
    exact Subgroup.le_centralizer_iff.mp hZL
  have h1 : L1 ≤ (P1 L1 L2 S ⊓ normalizer (X₀ : Set G)) ⊔ Q1 L1 L2 S :=
    (le_inf le_sup_left (hL1cent.trans (Subgroup.centralizer_le_normalizer _))).trans le_sup_left
  have h2 : L2 ≤ (P2 L1 L2 S ⊓ normalizer (X₀ : Set G)) ⊔ Q2 L1 L2 S :=
    (le_inf le_sup_left (hL2cent.trans (Subgroup.centralizer_le_normalizer _))).trans le_sup_left
  exact eq_bot_of_le_bigB hfr.hF.1 hXbigB h1 h2

private theorem szEnd_Zv_inf_centralizer_Lv_eq_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) {v : ℤ}
    (hv : Even v) : t.Zv v ⊓ centralizer (t.Lv v : Set G) = ⊥ := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · have hbase := szE1_base t hfr hZL
    have hZ : t.Zv (2 * k) =
        (t.Zv 0).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
      change qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ (2 * k) =
        (qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ 0).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom
      have h := map_qv_tau_pow (Q₁ := Z1 L1 L2 S) (Q₂ := Z2 L1 L2 S)
        (x₁ := t.x₁) (x₂ := t.x₂) 0 k
      rw [show (0 : ℤ) + 2 * k = 2 * k by ring] at h
      exact h.symm
    have hL : t.Lv (2 * k) =
        (t.Lv 0).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
      change qv (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) t.x₁ t.x₂ (2 * k) =
        (qv (L1 ⊔ Q1 L1 L2 S) (L2 ⊔ Q2 L1 L2 S) t.x₁ t.x₂ 0).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom
      have h := map_qv_tau_pow (Q₁ := L1 ⊔ Q1 L1 L2 S) (Q₂ := L2 ⊔ Q2 L1 L2 S)
        (x₁ := t.x₁) (x₂ := t.x₂) 0 k
      rw [show (0 : ℤ) + 2 * k = 2 * k by ring] at h
      exact h.symm
    have hC : Subgroup.centralizer (t.Lv (2 * k) : Set G) =
        (Subgroup.centralizer (t.Lv 0 : Set G)).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
      rw [hL, ← CFSG.Goldschmidt.G54.map_conj_centralizer ((t.x₂ * t.x₁) ^ k) (t.Lv 0)]
    have hgoal : t.Zv (2 * k) ⊓ centralizer (t.Lv (2 * k) : Set G) =
        (t.Zv 0 ⊓ centralizer (t.Lv 0 : Set G)).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom := by
      rw [hZ, hC, Subgroup.map_inf _ _ _ (MulAut.conj _).injective]
    rw [hgoal, hbase, Subgroup.map_bot]
  · exact absurd hv (Int.not_even_two_mul_add_one k)

private theorem szE2_GL_tau {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (k : ℤ) :
    t.Zv (2 * k) ⊓ centralizer (pCoreOf 2 (t.Gw (2 * k) (2 * k + 1))) ≤
      t.Zv (2 * k + 1) := by
  classical
  let g : G := t.edgeElt (2 * k)
  have hbase : t.Zv 0 ⊓ centralizer (pCoreOf 2 (t.Gw 0 1)) ≤ t.Zv 1 := by
    rw [t.Zv_zero, t.Zv_one, t.Gw_zero_one hfr.hF]
    exact z1_inf_centralizer_le_z2 hfr.hF.1
  have hZ0 : (t.Zv 0).map (MulAut.conj g).toMonoidHom = t.Zv (2 * k) := by
    rw [show g = t.edgeElt (2 * k) from rfl, t.map_Zv_edgeElt (2 * k) 0,
      if_pos (even_two_mul k)]
    rw [show 2 * k + 0 = 2 * k by ring]
  have hZ1 : (t.Zv 1).map (MulAut.conj g).toMonoidHom = t.Zv (2 * k + 1) := by
    rw [show g = t.edgeElt (2 * k) from rfl, t.map_Zv_edgeElt (2 * k) 1,
      if_pos (even_two_mul k)]
  have hGw : (t.Gw 0 1).map (MulAut.conj g).toMonoidHom = t.Gw (2 * k) (2 * k + 1) := by
    rw [show g = t.edgeElt (2 * k) from rfl, t.map_Gw_edgeElt (2 * k) 0 1,
      if_pos (even_two_mul k)]
    rw [show 2 * k + 0 = 2 * k by ring]
  have hmap : pCoreOf 2 (t.Gw (2 * k) (2 * k + 1)) =
      (pCoreOf 2 (t.Gw 0 1)).map (MulAut.conj g).toMonoidHom := by
    rw [← hGw, pCoreOf_map_mulEquiv]
  intro x hx
  obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxZ' : g⁻¹ * x * g ∈ t.Zv 0 := by
    exact mem_map_conj_iff.mp (by rwa [hZ0])
  have hxC' : g⁻¹ * x * g ∈ centralizer (pCoreOf 2 (t.Gw 0 1)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG : g * y * g⁻¹ ∈ pCoreOf 2 (t.Gw (2 * k) (2 * k + 1)) := by
      rw [hmap]
      exact mem_map_conj_iff.mpr (by
        rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
        exact hy)
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC (g * y * g⁻¹) hyG
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * x * g) * y := by group
  have hx1 : g⁻¹ * x * g ∈ t.Zv 1 :=
    hbase (Subgroup.mem_inf.mpr ⟨hxZ', hxC'⟩)
  rw [← hZ1]
  exact mem_map_conj_iff.mpr hx1
private theorem szEnd_Zv_one_le_pCoreOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) :
    t.Zv 1 ≤ pCoreOf 2 (t.Gw (h - 1) h) := by
  have hwin : t.Gw (2 - h) h ≤ t.Gw (h - 1) h :=
    win_mono (a := 2 - h) (b := h) (a' := h - 1) (b' := h) (by omega) (le_refl h)
  exact t.le_pCoreOf_Gw hfr (show h - 1 < h by omega) (t.isPGroup_Zv 1) (hZ1.trans hwin)

private theorem szE1_not_Zv_one_le_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h : ℤ) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1)) :
    ¬ t.Zv 1 ≤ t.Qv h :=
  fun hle => hZ1' (hle.trans (t.Qv_le_Gv hfr h).2)

private theorem szE1_counting {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) {y : G}
    (hyGw : (t.Gw (h - 1) h).map (MulAut.conj y).toMonoidHom = t.Gw h (h + 1))
    (hyQ : (t.Qv h).map (MulAut.conj y).toMonoidHom = t.Qv h)
    (hyK : y ∈ normalizer (t.K : Set G))
    {X : Subgroup G} (hX : X ≤ t.Zv 1) (hXK : t.K ≤ normalizer (X : Set G))
    (hXQ : ¬ X ≤ t.Qv h) :
    2 ^ (2 * a + 1) ≤
      (t.Qv h ⊓ (X.map (MulAut.conj y).toMonoidHom : Subgroup G)).relIndex
        (X.map (MulAut.conj y).toMonoidHom) := by
  have hXR : X ≤ pCoreOf 2 (t.Gw (h - 1) h) :=
    hX.trans (szEnd_Zv_one_le_pCoreOf t hfr hh hZ1)
  have hX'R : (X.map (MulAut.conj y).toMonoidHom : Subgroup G) ≤
      pCoreOf 2 (t.Gw h (h + 1)) := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hXR
    rwa [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj y)
      (t.Gw (h - 1) h), hyGw] at hmap
  have hX'K : t.K ≤ normalizer ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) :=
    szE1_le_normalizer_map_conj t hXK hyK
  have hX'Q : ¬ (X.map (MulAut.conj y).toMonoidHom : Subgroup G) ≤ t.Qv h := by
    intro hle
    apply hXQ
    have hle' : X.map (MulAut.conj y).toMonoidHom ≤
        (t.Qv h).map (MulAut.conj y).toMonoidHom := by
      rwa [hyQ]
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj y).injective).mp hle'
  have hroot : t.rootOmega h ≤
      (X.map (MulAut.conj y).toMonoidHom : Subgroup G) ⊔ t.Qv h :=
    t.rootOmega_le_sup hfr h hX'R hX'K hX'Q
  have hX'N : (X.map (MulAut.conj y).toMonoidHom : Subgroup G) ≤
      normalizer (t.Qv h : Set G) :=
    hX'R.trans ((pCoreOf_le 2 (t.Gw h (h + 1))).trans
      ((win_le_qv (Q₁ := P1 L1 L2 S) (Q₂ := P2 L1 L2 S) (x₁ := t.x₁) (x₂ := t.x₂)
        (a := h) (b := h + 1) (i := h) le_rfl (by omega)).trans
        (t.Gv_le_normalizer_Qv h)))
  have hrel : (t.Qv h).relIndex
        ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) ⊔ t.Qv h) =
      ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) ⊓ t.Qv h).relIndex
        (X.map (MulAut.conj y).toMonoidHom) :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hX'N).2
  have hrootrel : (t.Qv h).relIndex (t.rootOmega h) = 2 ^ (2 * a + 1) := by
    rw [t.relIndex_rootOmega hfr h, if_pos hev]
  have hmono : (t.Qv h).relIndex (t.rootOmega h) ≤ (t.Qv h).relIndex
      ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) ⊔ t.Qv h) :=
    Subgroup.relIndex_le_of_le_right hroot (by
      intro hzero
      have hmul := (t.Qv h).relIndex_mul_card
        ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) ⊔ t.Qv h)
      rw [hzero, Nat.zero_mul] at hmul
      have hpos : 0 < Nat.card
          ↥((X.map (MulAut.conj y).toMonoidHom : Subgroup G) ⊔ t.Qv h) := Nat.card_pos
      omega)
  rw [hrootrel] at hmono
  refine hmono.trans ?_
  rw [hrel, inf_comm]

private theorem szE1_Zv_one_map_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) {y : G}
    (hyGw : (t.Gw (h - 1) h).map (MulAut.conj y).toMonoidHom = t.Gw h (h + 1)) :
    (t.Zv 1).map (MulAut.conj y).toMonoidHom ≤ pCoreOf 2 (t.Gw h (h + 1)) := by
  have hmap := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom)
    (szEnd_Zv_one_le_pCoreOf t hfr hh hZ1)
  rwa [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj y) (t.Gw (h - 1) h),
    hyGw] at hmap

private theorem szEnd_mem_Zv_one_sup_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h)
    (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1)) {x : G}
    (hx : x ∈ pCoreOf 2 (t.Gw (h - 1) h)) (hx2 : x ^ 2 ∈ t.Qv h) :
    x ∈ t.Zv 1 ⊔ t.Qv h := by
  obtain ⟨y, -, hyK, hyGw, hyQ, -⟩ := t.exists_reflection h
  have hyGwh : (t.Gw (h - 1) h).map (MulAut.conj y).toMonoidHom = t.Gw h (h + 1) :=
    szE1_reflect_Gw t hyGw
  have hyQh : (t.Qv h).map (MulAut.conj y).toMonoidHom = t.Qv h := szE1_reflect_Qv t hyQ
  have hZ'R : (t.Zv 1).map (MulAut.conj y).toMonoidHom ≤ pCoreOf 2 (t.Gw h (h + 1)) :=
    szE1_Zv_one_map_le t hfr hh hZ1 hyGwh
  have hZ'K : t.K ≤ normalizer ((t.Zv 1).map (MulAut.conj y).toMonoidHom : Set G) :=
    szE1_le_normalizer_map_conj t ((t.K_le_Gv 1).trans (t.Gv_le_normalizer_Zv 1)) hyK
  have hZ'Q : ¬ (t.Zv 1).map (MulAut.conj y).toMonoidHom ≤ t.Qv h := by
    intro hle
    exact szE1_not_Zv_one_le_Qv t hfr h hZ1' (by
      have hle' : (t.Zv 1).map (MulAut.conj y).toMonoidHom ≤
          (t.Qv h).map (MulAut.conj y).toMonoidHom := by
        rwa [hyQh]
      exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj y).injective).mp hle')
  have hroot := t.rootOmega_le_sup hfr h hZ'R hZ'K hZ'Q
  have hx'R : MulAut.conj y x ∈ pCoreOf 2 (t.Gw h (h + 1)) := by
    have hmap := Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hx
    rwa [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj y)
      (t.Gw (h - 1) h), hyGwh] at hmap
  have hx'2 : (MulAut.conj y x) ^ 2 ∈ t.Qv h := by
    have hconv : (MulAut.conj y x) ^ 2 = MulAut.conj y (x ^ 2) := by
      rw [pow_two, pow_two, map_mul]
    rw [hconv]
    have hmap := Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hx2
    rwa [hyQh] at hmap
  have hxroot : MulAut.conj y x ∈ t.rootOmega h :=
    (t.mem_rootOmega_iff hfr h).mpr ⟨hx'R, hx'2⟩
  have hmem : MulAut.conj y x ∈ (t.Zv 1).map (MulAut.conj y).toMonoidHom ⊔ t.Qv h :=
    hroot hxroot
  have hsup : (t.Zv 1).map (MulAut.conj y).toMonoidHom ⊔ t.Qv h =
      (t.Zv 1 ⊔ t.Qv h).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_sup, hyQh]
  rw [hsup] at hmem
  exact (Subgroup.mem_map_iff_mem (f := (MulAut.conj y).toMonoidHom)
    (MulAut.conj y).injective).mp hmem

private theorem szEnd_Zv_one_inf_Qv_and_card {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1)) :
    t.Zv 1 ⊓ t.Qv h = ⊥ ∧ Nat.card (t.Zv 1) = 2 ^ (2 * a + 1) := by
  obtain ⟨y, -, hyK, hyGw, hyQ, -⟩ := t.exists_reflection h
  have hyGwh : (t.Gw (h - 1) h).map (MulAut.conj y).toMonoidHom = t.Gw h (h + 1) :=
    szE1_reflect_Gw t hyGw
  have hyQh : (t.Qv h).map (MulAut.conj y).toMonoidHom = t.Qv h := szE1_reflect_Qv t hyQ
  have hcount := szE1_counting t hfr hh hev hZ1 hyGwh hyQh hyK (X := t.Zv 1) le_rfl
    ((t.K_le_Gv 1).trans (t.Gv_le_normalizer_Zv 1)) (szE1_not_Zv_one_le_Qv t hfr h hZ1')
  have hZcard : Nat.card ((t.Zv 1).map (MulAut.conj y).toMonoidHom) = Nat.card (t.Zv 1) :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hle : (t.Qv h ⊓ (t.Zv 1).map (MulAut.conj y).toMonoidHom).relIndex
      ((t.Zv 1).map (MulAut.conj y).toMonoidHom) ≤
        Nat.card ((t.Zv 1).map (MulAut.conj y).toMonoidHom) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)
  have hcard_ge : 2 ^ (2 * a + 1) ≤ Nat.card (t.Zv 1) := by
    rw [← hZcard]
    exact hcount.trans hle
  have hcard_eq : Nat.card (t.Zv 1) = 2 ^ (2 * a + 1) := le_antisymm hcard hcard_ge
  have hrelEq : (t.Qv h ⊓ (t.Zv 1).map (MulAut.conj y).toMonoidHom).relIndex
      ((t.Zv 1).map (MulAut.conj y).toMonoidHom) =
        Nat.card ((t.Zv 1).map (MulAut.conj y).toMonoidHom) := by
    refine le_antisymm hle ?_
    rw [hZcard, hcard_eq]
    exact hcount
  have hrelQ : (t.Qv h).relIndex ((t.Zv 1).map (MulAut.conj y).toMonoidHom) =
      Nat.card ((t.Zv 1).map (MulAut.conj y).toMonoidHom) := by
    rw [← Subgroup.inf_relIndex_right (t.Qv h) ((t.Zv 1).map (MulAut.conj y).toMonoidHom)]
    exact hrelEq
  have hZ'bot : t.Qv h ⊓ (t.Zv 1).map (MulAut.conj y).toMonoidHom = ⊥ := by
    have hmul := Subgroup.relIndex_mul_card (t.Qv h) ((t.Zv 1).map (MulAut.conj y).toMonoidHom)
    rw [hrelQ] at hmul
    exact Subgroup.eq_bot_of_card_eq _
      (Nat.eq_of_mul_eq_mul_left Nat.card_pos (hmul.trans (mul_one _).symm))
  refine ⟨?_, hcard_eq⟩
  have hyQinv : (t.Qv h).map (MulAut.conj y⁻¹).toMonoidHom = t.Qv h := by
    have hstep : ((t.Qv h).map (MulAut.conj y).toMonoidHom).map
        (MulAut.conj y⁻¹).toMonoidHom = (t.Qv h).map (MulAut.conj y⁻¹).toMonoidHom := by
      rw [hyQh]
    rw [← hstep, Subgroup.map_conj_map_conj, show y⁻¹ * y = 1 by group, map_conj_one]
  have hmap : (t.Qv h ⊓ (t.Zv 1).map (MulAut.conj y).toMonoidHom).map
      (MulAut.conj y⁻¹).toMonoidHom = ⊥ := by rw [hZ'bot, Subgroup.map_bot]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj _).injective, hyQinv] at hmap
  rw [Subgroup.map_conj_map_conj, show y⁻¹ * y = 1 by group, map_conj_one] at hmap
  rw [inf_comm]
  exact hmap

private theorem szE1_eq_Zv_one_of_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1)) {X : Subgroup G} (hX : X ≤ t.Zv 1)
    (hXne : X ≠ ⊥) (hXK : t.K ≤ normalizer (X : Set G)) : X = t.Zv 1 := by
  obtain ⟨hZQ, hcardZ⟩ := szEnd_Zv_one_inf_Qv_and_card t hfr hh hev hZ1 hZ1' hcard
  have hXQ : ¬ X ≤ t.Qv h := by
    intro hle
    have hbot : X ≤ (⊥ : Subgroup G) := by
      rw [← hZQ]
      exact le_inf hX hle
    exact hXne (le_bot_iff.mp hbot)
  obtain ⟨y, -, hyK, hyGw, hyQ, -⟩ := t.exists_reflection h
  have hyGwh : (t.Gw (h - 1) h).map (MulAut.conj y).toMonoidHom = t.Gw h (h + 1) :=
    szE1_reflect_Gw t hyGw
  have hyQh : (t.Qv h).map (MulAut.conj y).toMonoidHom = t.Qv h := szE1_reflect_Qv t hyQ
  have hcount := szE1_counting t hfr hh hev hZ1 hyGwh hyQh hyK hX hXK hXQ
  have hle : 2 ^ (2 * a + 1) ≤ Nat.card X := by
    refine hcount.trans ?_
    calc (t.Qv h ⊓ (X.map (MulAut.conj y).toMonoidHom : Subgroup G)).relIndex
          (X.map (MulAut.conj y).toMonoidHom)
        ≤ Nat.card (X.map (MulAut.conj y).toMonoidHom : Subgroup G) :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)
      _ = Nat.card X := Subgroup.card_map_of_injective (MulAut.conj y).injective
  refine Subgroup.eq_of_le_of_card_ge hX ?_
  rw [hcardZ]
  exact hle

private theorem szEnd_eq_Zv_of_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1)) {v : ℤ} (hv : Odd v) {X : Subgroup G}
    (hX : X ≤ t.Zv v) (hXne : X ≠ ⊥) (hXK : t.K ≤ normalizer (X : Set G)) :
    X = t.Zv v := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' v
  · exact absurd hv (Int.not_odd_iff_even.mpr (even_two_mul k))
  · have hZmap : (t.Zv (2 * k + 1)).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ (-k))).toMonoidHom = t.Zv 1 := by
      change (qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ (2 * k + 1)).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ (-k))).toMonoidHom =
        qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ 1
      have h := map_qv_tau_pow (Q₁ := Z1 L1 L2 S) (Q₂ := Z2 L1 L2 S)
        (x₁ := t.x₁) (x₂ := t.x₂) (2 * k + 1) (-k)
      rwa [show 2 * k + 1 + 2 * (-k) = 1 by ring] at h
    have hYle : (X.map (MulAut.conj ((t.x₂ * t.x₁) ^ (-k))).toMonoidHom : Subgroup G) ≤
        t.Zv 1 := by
      have hmap := Subgroup.map_mono
        (f := (MulAut.conj ((t.x₂ * t.x₁) ^ (-k))).toMonoidHom) hX
      rwa [hZmap] at hmap
    have hYne : (X.map (MulAut.conj ((t.x₂ * t.x₁) ^ (-k))).toMonoidHom : Subgroup G) ≠ ⊥ := by
      intro hbot
      exact hXne ((Subgroup.map_eq_bot_iff_of_injective _
        (MulAut.conj _).injective).mp hbot)
    have hYK : t.K ≤ normalizer
        ((X.map (MulAut.conj ((t.x₂ * t.x₁) ^ (-k))).toMonoidHom : Subgroup G) : Set G) :=
      szE1_le_normalizer_map_conj t hXK (zpow_mem t.track.tau_mem_normalizer (-k))
    have hY := szE1_eq_Zv_one_of_le t hfr hh hev hZ1 hZ1' hcard hYle hYne hYK
    have hmap : (X.map (MulAut.conj ((t.x₂ * t.x₁) ^ (-k))).toMonoidHom).map
        (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom = X := by
      rw [Subgroup.map_conj_map_conj,
        show (t.x₂ * t.x₁) ^ k * (t.x₂ * t.x₁) ^ (-k) = 1 by
          rw [← zpow_add, add_neg_cancel, zpow_zero],
        map_conj_one]
    have hZback : (t.Zv 1).map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        t.Zv (2 * k + 1) := by
      change (qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ 1).map
          (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom =
        qv (Z1 L1 L2 S) (Z2 L1 L2 S) t.x₁ t.x₂ (2 * k + 1)
      have h := map_qv_tau_pow (Q₁ := Z1 L1 L2 S) (Q₂ := Z2 L1 L2 S)
        (x₁ := t.x₁) (x₂ := t.x₂) 1 k
      rwa [show (1 : ℤ) + 2 * k = 2 * k + 1 by ring] at h
    rw [hY] at hmap
    rw [← hmap, hZback]

private theorem szEnd_commutator_le_Qv_three {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h)
    (hZh : t.Zv h ≤ t.Gw 3 4) : ⁅t.Zv h, t.Zv 1⁆ ≤ t.Qv 3 := by
  rw [Subgroup.commutator_le]
  intro z hz x hx
  rw [commutatorElement_def]
  have hxQ : x ∈ t.Qv 3 :=
    t.le_Qv_of_le_Gw hfr (by omega) (by omega) (t.isPGroup_Zv 1) hZ1 hx
  have hzGv : z ∈ t.Gv 3 :=
    mem_win_iff.mp (hZh hz) 3 (by norm_num) (by norm_num)
  have hzN : z ∈ normalizer (t.Qv 3 : Set G) := t.Gv_le_normalizer_Qv 3 hzGv
  have hzx : z * x * z⁻¹ ∈ t.Qv 3 := (Subgroup.mem_normalizer_iff.mp hzN x).mp hxQ
  exact (t.Qv 3).mul_mem hzx ((t.Qv 3).inv_mem hxQ)

private theorem szE2_pCoreOf_Gw_one_two_le_centralizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) :
    pCoreOf 2 (t.Gw 1 2) ≤ centralizer (t.Zv 1 : Set G) := by
  have hGv : pCoreOf 2 (t.Gw 1 2) ≤ t.Gv 1 :=
    fun x hx => mem_win_iff.mp (pCoreOf_le 2 _ hx) 1 le_rfl (by norm_num)
  have hLv : pCoreOf 2 (t.Gw 1 2) ≤ t.Lv 1 :=
    t.le_Lv hfr (pCoreOf_isPGroup 2 _) hGv
  exact hLv.trans (t.szEnd_Lv_le_centralizer_Zv hZL ⟨0, by norm_num⟩)

private theorem szE2_Qv_two_le_centralizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) :
    t.Qv 2 ≤ centralizer (t.Zv 1 : Set G) := by
  have hGv : t.Qv 2 ≤ t.Gv 1 := by simpa using (t.Qv_le_Gv hfr 2).1
  exact (t.le_Lv hfr (t.isPGroup_Qv 2) hGv).trans
    (t.szEnd_Lv_le_centralizer_Zv hZL ⟨0, by norm_num⟩)

private theorem szE2_Zv_one_le_Qv_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) :
    t.Zv 1 ≤ t.Qv 2 :=
  t.le_Qv_of_le_Gw hfr (by omega) (by omega) (t.isPGroup_Zv 1) hZ1

private theorem szE2_not_le_centralizer_singleton {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h)
    (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) {x : G} (hx : x ∈ t.Zv 1)
    (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) :
    ¬ t.Lv 2 ≤ Subgroup.centralizer ({x} : Set G) := by
  intro hLv
  have hxQ2 : x ∈ t.Qv 2 := szE2_Zv_one_le_Qv_two t hfr hh hZ1 hx
  have hQ2L : t.Qv 2 ≤ t.Lv 2 := by
    rw [← t.pCoreOf_Lv hfr 2]
    exact pCoreOf_le 2 _
  have hxZ2 : x ∈ t.Zv 2 := by
    rw [t.Zv_eq 2]
    refine CFSG.Quasithin.mem_omegaOneCenterOf hxQ2 (fun y hy => ?_) hx2
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLv (hQ2L hy))
  have hxcen : x ∈ centralizer (t.Lv 2 : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLv hy)
  have hbot := t.szEnd_Zv_inf_centralizer_Lv_eq_bot hfr hZL
    (show Even (2 : ℤ) from ⟨1, by norm_num⟩)
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hxZ2, hxcen⟩
  exact hx1 (Subgroup.mem_bot.mp hxbot)

private theorem szE2_commutator_mem_centralizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZh : t.Zv h ≤ t.Gw 3 4)
    (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) {z x : G} (hz : z ∈ t.Zv h)
    (hx : x ∈ t.Zv 1) (hx1 : x ≠ 1) :
    ⁅z, x⁆ ∈ centralizer (t.Zv 1 : Set G) := by
  classical
  set w : G := ⁅z, x⁆ with hwdef
  have hxGv : x ∈ t.Gv h := mem_win_iff.mp (hZ1 hx) h (by omega) (by omega)
  have hzGv : z ∈ t.Gv h := t.Qv_le_Gv_self h (t.Zv_le_Qv h hz)
  have hxN : x ∈ normalizer (t.Zv h : Set G) := t.Gv_le_normalizer_Zv h hxGv
  have hwZ : w ∈ t.Zv h := by
    rw [hwdef, commutatorElement_def]
    rw [show z * x * z⁻¹ * x⁻¹ = z * (x * z⁻¹ * x⁻¹) by group]
    exact Subgroup.mul_mem (t.Zv h) hz
      ((Subgroup.mem_normalizer_iff.mp hxN z⁻¹).mp (Subgroup.inv_mem (t.Zv h) hz))
  have hx2 : x ^ 2 = 1 :=
    CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf (R := t.Qv 1) (by
      rw [← t.Zv_eq 1]; exact hx)
  have hz2 : z ^ 2 = 1 :=
    CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf (R := t.Qv h) (by
      rw [← t.Zv_eq h]; exact hz)
  have hw2 : w ^ 2 = 1 :=
    CFSG.Quasithin.A4.sq_eq_one_of_mem_omegaOneCenterOf (R := t.Qv h) (by
      rw [← t.Zv_eq h]; exact hwZ)
  have hzw : z * w = w * z :=
    CFSG.Quasithin.A4.mul_comm_of_mem_omegaOneCenterOf
      (R := t.Qv h) (by rw [← t.Zv_eq h]; exact hz)
      (by rw [← t.Zv_eq h]; exact hwZ)
  have hwx : w * x = x * w := szE2_commutator_commute hx2 hz2 hwdef hzw
  have hwcent : w ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwx
  have hwQ3 : w ∈ t.Qv 3 := by
    rw [hwdef]
    exact szEnd_commutator_le_Qv_three t hfr hh hZ1 hZh
      (Subgroup.commutator_mem_commutator hz hx)
  have hPle : Subgroup.zpowers w ≤ t.Qv 3 := Subgroup.zpowers_le.mpr hwQ3
  have hP : IsPGroup 2 (Subgroup.zpowers w) := (t.isPGroup_Qv 3).to_le hPle
  have hPL : Subgroup.zpowers w ≤ t.Lv 2 :=
    t.le_Lv hfr hP (hPle.trans (by simpa using (t.Qv_le_Gv hfr 3).1))
  have hcentx : Subgroup.centralizer (t.Zv 1 : Set G) ≤
      Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hx)
  have hxT : pCoreOf 2 (t.Gw 1 2) ≤ Subgroup.centralizer ({x} : Set G) :=
    (szE2_pCoreOf_Gw_one_two_le_centralizer t hfr hZL).trans hcentx
  have hxQ : pCoreOf 2 (t.Lv 2) ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [t.pCoreOf_Lv hfr 2]
    exact (szE2_Qv_two_le_centralizer t hfr hZL).trans hcentx
  have hxL : ¬ t.Lv 2 ≤ Subgroup.centralizer ({x} : Set G) :=
    szE2_not_le_centralizer_singleton t hfr hh hZ1 hZL hx hx1 hx2
  have hT : IsSylowTwoOf (pCoreOf 2 (t.Gw 1 2)) (t.Lv 2) := by
    simpa using t.isSylowTwoOf_Lv_left hfr 2
  have hPT : Subgroup.zpowers w ≤ pCoreOf 2 (t.Gw 1 2) :=
    le_of_le_centralizer_of_sz hfr.ha (t.nonempty_mulEquiv_sz_Lv hfr ⟨1, by norm_num⟩)
      hT hxT hxQ hxL hP hPL (Subgroup.zpowers_le.mpr hwcent)
  exact szE2_pCoreOf_Gw_one_two_le_centralizer t hfr hZL
    (hPT (Subgroup.mem_zpowers w))

private theorem szEnd_commutator_le_centralizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZh : t.Zv h ≤ t.Gw 3 4)
    (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) :
    ⁅t.Zv h, t.Zv 1⁆ ≤ centralizer (t.Zv 1 : Set G) := by
  rw [Subgroup.commutator_le]
  intro z hz x hx
  by_cases hx1 : x = 1
  · subst hx1
    rw [commutatorElement_def]
    simp
  · exact szE2_commutator_mem_centralizer t hfr hh hZ1 hZh hZL hz hx hx1

private theorem szE2_Zv_one_le_Lv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) :
    t.Zv 1 ≤ t.Lv h := by
  refine t.le_Lv hfr (t.isPGroup_Zv 1) (fun x hx => ?_)
  exact mem_win_iff.mp (hZ1 hx) h (by omega) (by omega)

private theorem szE2_GL_reflect (v : ℤ)
    (hprev : t.Zv v ⊓ centralizer (pCoreOf 2 (t.Gw v (v + 1))) ≤ t.Zv (v + 1)) :
    t.Zv v ⊓ centralizer (pCoreOf 2 (t.Gw (v - 1) v)) ≤ t.Zv (v - 1) := by
  obtain ⟨y, -, -, hGwmap, -, hZmap⟩ := t.exists_reflection v
  intro x hx
  obtain ⟨hxZ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxZ' : y⁻¹ * x * y ∈ t.Zv v := by
    have hmap : (t.Zv v).map (MulAut.conj y).toMonoidHom = t.Zv v := by
      have h := hZmap v
      rwa [show 2 * v - v = v by ring] at h
    exact mem_map_conj_iff.mp (by rwa [hmap])
  have hxC' : y⁻¹ * x * y ∈ centralizer (pCoreOf 2 (t.Gw v (v + 1))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzG : y * z * y⁻¹ ∈ pCoreOf 2 (t.Gw (v - 1) v) := by
      have hGw : t.Gw (v - 1) v = (t.Gw v (v + 1)).map (MulAut.conj y).toMonoidHom := by
        have h := hGwmap v (v + 1)
        rw [show 2 * v - (v + 1) = v - 1 by ring, show 2 * v - v = v by ring] at h
        exact h.symm
      have hmap : pCoreOf 2 (t.Gw (v - 1) v) =
          (pCoreOf 2 (t.Gw v (v + 1))).map (MulAut.conj y).toMonoidHom := by
        rw [hGw, pCoreOf_map_mulEquiv]
      rw [hmap]
      exact mem_map_conj_iff.mpr (by
        rw [show y⁻¹ * (y * z * y⁻¹) * y = z by group]
        exact hz)
    have hcomm := Subgroup.mem_centralizer_iff.mp hxC (y * z * y⁻¹) hzG
    calc z * (y⁻¹ * x * y) = y⁻¹ * ((y * z * y⁻¹) * x) * y := by group
      _ = y⁻¹ * (x * (y * z * y⁻¹)) * y := by rw [hcomm]
      _ = (y⁻¹ * x * y) * z := by group
  have hx1 : y⁻¹ * x * y ∈ t.Zv (v + 1) :=
    hprev (Subgroup.mem_inf.mpr ⟨hxZ', hxC'⟩)
  have hmap : (t.Zv (v + 1)).map (MulAut.conj y).toMonoidHom = t.Zv (v - 1) := by
    have h := hZmap (v + 1)
    rw [show 2 * v - (v + 1) = v - 1 by ring] at h
    exact h
  rw [← hmap]
  exact mem_map_conj_iff.mpr hx1

private theorem szE2_GL_edge {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {h k : ℤ} (hk : h = 2 * k) :
    t.Zv h ⊓ centralizer (pCoreOf 2 (t.Gw (h - 1) h)) ≤ t.Zv (h - 1) := by
  rw [hk] at *
  exact szE2_GL_reflect t (2 * k) (szE2_GL_tau t hfr k)

private theorem szEnd_natural_contains {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ}
    {U : Subgroup G}
    (hUY : U ⊓ centralizer (pCoreOf 2 (t.Gw (h - 1) h)) = t.Zv (h - 1))
    (hUforall : ∀ g ∈ normalizer (t.Lv h : Set G), g ∈ normalizer (t.Zv h : Set G) →
      g ∈ normalizer (U : Set G)) :
    t.Zv (h + 1) ≤ U := by
  have hZY : t.Zv (h - 1) ≤ U := by
    rw [← hUY]
    exact inf_le_left
  obtain ⟨y, hyGv, -, -, -, hZmap⟩ := t.exists_reflection h
  have hyL : y ∈ normalizer (t.Lv h : Set G) := t.Gv_le_normalizer_Lv hfr h hyGv
  have hyZ : y ∈ normalizer (t.Zv h : Set G) := t.Gv_le_normalizer_Zv h hyGv
  have hyU : y ∈ normalizer (U : Set G) := hUforall y hyL hyZ
  have hmap : (t.Zv (h - 1)).map (MulAut.conj y).toMonoidHom = t.Zv (h + 1) := by
    have hmap' := hZmap (h - 1)
    rw [show 2 * h - (h - 1) = h + 1 by ring] at hmap'
    exact hmap'
  rw [← hmap]
  calc (t.Zv (h - 1)).map (MulAut.conj y).toMonoidHom ≤
        U.map (MulAut.conj y).toMonoidHom := Subgroup.map_mono hZY
    _ = U := Subgroup.mem_normalizer_iff_map_conj_eq.mp hyU

private theorem szEnd_exists_natural
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hZh : t.Zv h ≤ t.Gw 3 4) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G))
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1)) :
    ∃ U : Subgroup G, U ≤ t.Zv h ∧ t.Lv h ≤ normalizer (U : Set G) ∧
      IsSzNaturalSection (t.Lv h) U ⊥ a ∧ t.K ≤ normalizer (U : Set G) ∧
      t.Zv (h + 1) ≤ U := by
  classical
  obtain ⟨k, hk⟩ := hev
  have h2k : h = 2 * k := by rw [hk]; ring
  have hev2 : Even h := ⟨k, by rw [h2k]; ring⟩
  have hCH : t.Zv 1 ≤ t.Lv h := szE2_Zv_one_le_Lv t hfr hh hZ1
  have hC : ∀ x ∈ pCoreOf 2 (t.Gw (h - 1) h),
      x * x ∈ pCoreOf 2 (t.Lv h) → x ∈ t.Zv 1 ⊔ pCoreOf 2 (t.Lv h) := by
    intro x hxT hx2
    have hx2' : x ^ 2 ∈ t.Qv h := by
      rw [pow_two]
      have hq := hx2
      rwa [t.pCoreOf_Lv hfr h] at hq
    rw [t.pCoreOf_Lv hfr h]
    exact t.szEnd_mem_Zv_one_sup_Qv hfr hh hZ1 hZ1' hxT hx2'
  have hZQ : t.Zv h ≤ pCoreOf 2 (t.Lv h) := by
    rw [t.pCoreOf_Lv hfr h]
    exact t.Zv_le_Qv h
  have hHZ : t.Lv h ≤ normalizer (t.Zv h : Set G) :=
    (t.Lv_le_Gv h).trans (t.Gv_le_normalizer_Zv h)
  have hZ : t.Zv h ≠ ⊥ := t.Zv_ne_bot hfr.hF h
  have hquad : ⁅⁅t.Zv h, t.Zv 1⁆, t.Zv 1⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (szEnd_commutator_le_centralizer t hfr hh hZ1 hZh hZL)
  have hcen : t.Zv h ⊓ centralizer (t.Lv h : Set G) = ⊥ :=
    t.szEnd_Zv_inf_centralizer_Lv_eq_bot hfr hZL hev2
  have hY : t.Zv h ⊓ centralizer (pCoreOf 2 (t.Gw (h - 1) h)) ≤ t.Zv (h - 1) :=
    szE2_GL_edge t hfr h2k
  have hYc : Nat.card (t.Zv (h - 1)) ≤ 2 ^ (2 * a + 1) := by
    have hcs := t.szEnd_card_Zv_shift 1 ((h - 2) / 2)
    have hidx : 1 + 2 * ((h - 2) / 2) = h - 1 := by
      rw [h2k]
      rw [show 2 * k - 2 = 2 * (k - 1) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
      ring
    rw [hidx] at hcs
    exact hcs.le.trans hcard
  obtain ⟨U, hUZ, hUL, hUnat, hUY, hUforall⟩ :=
    exists_isSzNaturalSection_le_of_quadratic_of_sz hfr.ha
      (t.nonempty_mulEquiv_sz_Lv hfr hev2) (t.isSylowTwoOf_Lv_left hfr h)
      hCH hC hZQ hHZ hZ hquad hcen hY hYc
  refine ⟨U, hUZ, hUL, hUnat, ?_, szEnd_natural_contains t hfr hUY hUforall⟩
  · intro g hg
    exact hUforall g
      ((t.K_le_Gv h).trans (t.Gv_le_normalizer_Lv hfr h) hg)
      ((t.K_le_Gv h).trans (t.Gv_le_normalizer_Zv h) hg)
private theorem szE3_K_le_normalizer_Zv_inf_centralizer (j : ℤ) :
    t.K ≤ Subgroup.normalizer
      ((t.Zv j ⊓ Subgroup.centralizer (t.Zv 1 : Set G) : Subgroup G) : Set G) := by
  have h1 : t.K ≤ Subgroup.normalizer (t.Zv j : Set G) :=
    (t.K_le_Gv j).trans (t.Gv_le_normalizer_Zv j)
  have h2 : t.K ≤ Subgroup.normalizer
      (Subgroup.centralizer (t.Zv 1 : Set G) : Set G) :=
    (t.K_le_Gv 1).trans ((t.Gv_le_normalizer_Zv 1).trans
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup (t.Zv 1)))
  exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem szE3_Zv_add_one_le_centralizer_of_ne_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1))
    (hXne : t.Zv (h + 1) ⊓ Subgroup.centralizer (t.Zv 1 : Set G) ≠ ⊥) :
    t.Zv (h + 1) ≤ Subgroup.centralizer (t.Zv 1 : Set G) := by
  have hXK := szE3_K_le_normalizer_Zv_inf_centralizer (t := t) (h + 1)
  have hXeq : t.Zv (h + 1) ⊓ Subgroup.centralizer (t.Zv 1 : Set G) = t.Zv (h + 1) :=
    t.szEnd_eq_Zv_of_le hfr hh hev hZ1 hZ1' hcard (v := h + 1) hev.add_one
      inf_le_left hXne hXK
  rw [← hXeq]
  exact inf_le_right

private theorem szE3_exists_mul_of_mem_Gv
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ}
    (hh : 4 ≤ h) (hev : Even h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h)
    (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1)) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G))
    (hZvh1 : t.Zv (h + 1) ≤ centralizer (t.Zv 1 : Set G)) {y : G} (hyv : y ∈ t.Gv h) :
    ∃ m ∈ t.Gv h ⊓ Subgroup.centralizer (t.Zv (h + 1) : Set G),
      ∃ s ∈ t.Gw h (h + 1), y = m * s := by
  have hZ1_le_cent : t.Zv 1 ≤ Subgroup.centralizer (t.Zv (h + 1) : Set G) :=
    Subgroup.le_centralizer_iff.mp hZvh1
  let M : Subgroup G := t.Gv h ⊓ Subgroup.centralizer (t.Zv (h + 1) : Set G)
  have h₁ : ∀ x ∈ pCoreOf 2 (t.Gw h (h + 1)), x ^ 2 ∈ t.Qv h →
      x ∈ M ⊔ t.Qv h := by
    intro x hx _
    have hxGw : x ∈ t.Gw h (h + 1) := pCoreOf_le 2 _ hx
    have hxGv : x ∈ t.Gv h := (mem_win_iff.mp hxGw) h le_rfl (by omega)
    have hxLv : x ∈ t.Lv (h + 1) :=
      t.le_Lv hfr (pCoreOf_isPGroup 2 (t.Gw h (h + 1)))
        ((pCoreOf_le 2 (t.Gw h (h + 1))).trans fun z hz =>
          (mem_win_iff.mp hz) (h + 1) (by omega) le_rfl) hx
    have hxCent : x ∈ Subgroup.centralizer (t.Zv (h + 1) : Set G) :=
      t.szEnd_Lv_le_centralizer_Zv hZL hev.add_one hxLv
    exact (le_sup_left : M ≤ M ⊔ t.Qv h) (Subgroup.mem_inf.mpr ⟨hxGv, hxCent⟩)
  have hZ1M : t.Zv 1 ≤ M := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨?_, hZ1_le_cent hz⟩
    exact (mem_win_iff.mp (hZ1 hz)) h (by omega) le_rfl
  have h₂ : ∀ x ∈ pCoreOf 2 (t.Gw (h - 1) h), x ^ 2 ∈ t.Qv h →
      x ∈ M ⊔ t.Qv h := by
    intro x hx hx2
    have hxZ := t.szEnd_mem_Zv_one_sup_Qv hfr hh hZ1 hZ1' hx hx2
    exact (sup_le (hZ1M.trans le_sup_left) le_sup_right) hxZ
  exact t.exists_mul_of_mem_Gv hfr h (X := M) inf_le_left h₁ h₂ hyv

private theorem szE3_Zv_sub_one_eq_Zv_add_one
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ}
    (hh : 4 ≤ h) (hev : Even h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h)
    (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1)) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G))
    (hZvh1 : t.Zv (h + 1) ≤ centralizer (t.Zv 1 : Set G)) :
    t.Zv (h - 1) = t.Zv (h + 1) := by
  obtain ⟨y, hyv, -, -, -, hyZ⟩ := t.exists_reflection h
  obtain ⟨m, hmM, s, hsGw, hys⟩ :=
    szE3_exists_mul_of_mem_Gv t hfr hh hev hZ1 hZ1' hZL hZvh1 hyv
  have hmCent : m ∈ Subgroup.centralizer (t.Zv (h + 1) : Set G) :=
    (Subgroup.mem_inf.mp hmM).2
  have hsGv : s ∈ t.Gv (h + 1) := (mem_win_iff.mp hsGw) (h + 1) (by omega) le_rfl
  have hyNorm : y ∈ Subgroup.normalizer (t.Zv (h + 1) : Set G) := by
    rw [hys]
    exact mul_mem
      (Subgroup.centralizer_le_normalizer (t.Zv (h + 1) : Set G) hmCent)
      (t.Gv_le_normalizer_Zv (h + 1) hsGv)
  have hmap : (t.Zv (h + 1)).map (MulAut.conj y).toMonoidHom = t.Zv (h + 1) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hyNorm
  have hZh : t.Zv (2 * h - (h + 1)) = t.Zv (h + 1) :=
    (hyZ (h + 1)).symm.trans hmap
  simpa only [show 2 * h - (h + 1) = h - 1 by ring] using hZh

private theorem szEnd_Zv_add_one_inf_centralizer_eq_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h)
    (hev : Even h) (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hZL : L2 ≤ centralizer (t.Zv 1 : Set G)) (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1)) :
    t.Zv (h + 1) ⊓ centralizer (t.Zv 1 : Set G) = ⊥ := by
  obtain ⟨k, rfl⟩ := hev
  by_contra hXne
  have hZvh1 : t.Zv (k + k + 1) ≤ Subgroup.centralizer (t.Zv 1 : Set G) :=
    szE3_Zv_add_one_le_centralizer_of_ne_bot t hfr hh ⟨k, rfl⟩ hZ1 hZ1' hcard hXne
  have hZh : t.Zv (k + k - 1) = t.Zv (k + k + 1) :=
    szE3_Zv_sub_one_eq_Zv_add_one t hfr hh ⟨k, rfl⟩ hZ1 hZ1' hZL hZvh1
  have hleGw : t.Zv (k + k + 1) ≤ t.Gw 2 (2 * (k + k)) := by
    simpa only [show (1 : ℤ) + 2 * k = k + k + 1 by ring,
      show 2 - (k + k) + 2 * k = 2 by ring,
      show k + k + 2 * k = 2 * (k + k) by ring] using
      t.szEnd_Zv_le_Gw_shift hZ1 k
  have hleGv : t.Zv (k + k + 1) ≤ t.Gv (2 * (k + k) - 1) := fun z hz =>
    (mem_win_iff.mp (hleGw hz)) (2 * (k + k) - 1) (by omega) (by omega)
  have hnot : ¬ t.Zv (k + k - 1) ≤ t.Gv (2 * (k + k) - 1) := by
    simpa only [show (1 : ℤ) + 2 * (k - 1) = k + k - 1 by ring,
      show k + k + 1 + 2 * (k - 1) = 2 * (k + k) - 1 by ring] using
      t.szEnd_not_Zv_le_Gv_shift hZ1' (k - 1)
  exact hnot (hZh.symm ▸ hleGv)
private theorem szE4_mul_comm {h : ℤ} {U : Subgroup G} (hUZ : U ≤ t.Zv h) {x y : G}
    (hx : x ∈ U) (hy : y ∈ U) : x * y = y * x := by
  have hx' : x ∈ omegaOneCenterOf (t.Qv h) := by
    rw [← t.Zv_eq h]
    exact hUZ hx
  have hy' : y ∈ omegaOneCenterOf (t.Qv h) := by
    rw [← t.Zv_eq h]
    exact hUZ hy
  exact A4.mul_comm_of_mem_omegaOneCenterOf hx' hy'

private theorem szE4_exists_phi {h : ℤ} {U : Subgroup G} {a0 : G}
    (hUZ : U ≤ t.Zv h) (hUL : t.Lv h ≤ normalizer (U : Set G))
    (ha0L : a0 ∈ t.Lv h) :
    ∃ φ : ↥U →* ↥U,
      (∀ u : ↥U, (φ u : G) = ⁅(u : G), a0⁆) ∧
        φ.ker = (U ⊓ Subgroup.centralizer ({a0} : Set G)).subgroupOf U := by
  classical
  have hmem : ∀ u : ↥U, ⁅(u : G), a0⁆ ∈ U := fun u =>
    CFSG.ClassicalInvolution.commutatorElement_mem_of_mem_normalizer u.2 (hUL ha0L)
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    t.szE4_mul_comm hUZ hx hy
  let φ : ↥U →* ↥U :=
    { toFun := fun u => ⟨⁅(u : G), a0⁆, hmem u⟩
      map_one' := by
        apply Subtype.ext
        simp [commutatorElement_def]
      map_mul' := fun u v => by
        apply Subtype.ext
        show ⁅((u : G) * (v : G)), a0⁆ = ⁅(u : G), a0⁆ * ⁅(v : G), a0⁆
        rw [commutatorElement_mul_left_eq_conj_mul]
        have h1 : (u : G) * ⁅(v : G), a0⁆ * (u : G)⁻¹ = ⁅(v : G), a0⁆ := by
          rw [hcomm (u : G) u.2 ⁅(v : G), a0⁆ (hmem v)]
          group
        rw [h1]
        exact hcomm ⁅(v : G), a0⁆ (hmem v) ⁅(u : G), a0⁆ (hmem u) }
  refine ⟨φ, fun u => rfl, ?_⟩
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hu
    have hu1 : ⁅(u : G), a0⁆ = 1 := by
      simpa [φ] using congrArg Subtype.val hu
    refine ⟨u.2, ?_⟩
    change (u : G) ∈ Subgroup.centralizer ({a0} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp hu1
  · rintro ⟨-, huC⟩
    change (u : G) ∈ Subgroup.centralizer ({a0} : Set G) at huC
    apply Subtype.ext
    show ⁅(u : G), a0⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_singleton_iff.mp huC

private theorem szE4_sq_eq_one {h : ℤ} {U : Subgroup G} (hUZ : U ≤ t.Zv h) {x : G}
    (hx : x ∈ U) : x ^ 2 = 1 := by
  have hx' : x ∈ omegaOneCenterOf (t.Qv h) := by
    rw [← t.Zv_eq h]
    exact hUZ hx
  exact A4.sq_eq_one_of_mem_omegaOneCenterOf hx'

private theorem szE4_card_U {a : ℕ} {h : ℤ} {U : Subgroup G}
    (hnat : IsSzNaturalSection (t.Lv h) U ⊥ a) :
    Nat.card U = (2 ^ (2 * a + 1)) ^ 4 := by
  have h := relIndex_eq_of_isSzNaturalSection hnat
  rwa [Subgroup.relIndex_bot_left] at h

private theorem szE4_Zv_le_Gv_two {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) : t.Zv (h + 1) ≤ t.Gv 2 := by
  have h2 : 2 * (h / 2) = h := Int.two_mul_ediv_two_of_even hev
  have hshift := t.szEnd_Zv_le_Gw_shift hZ1 (h / 2)
  have harg1 : (1 : ℤ) + 2 * (h / 2) = h + 1 := by rw [h2]; ring
  have harg2 : (2 : ℤ) - h + 2 * (h / 2) = 2 := by rw [h2]; ring
  have harg3 : h + 2 * (h / 2) = 2 * h := by rw [h2]; ring
  rw [harg1, harg2, harg3] at hshift
  exact hshift.trans (win_le_qv (a := 2) (b := 2 * h) (i := 2) le_rfl (by omega))

private theorem szE4_card_Zv_succ {a : ℕ} {h : ℤ} (hev : Even h)
    (hZ1card : Nat.card (t.Zv 1) = 2 ^ (2 * a + 1)) :
    Nat.card (t.Zv (h + 1)) = 2 ^ (2 * a + 1) := by
  have h2 : 2 * (h / 2) = h := Int.two_mul_ediv_two_of_even hev
  have hval := t.szEnd_card_Zv_shift 1 (h / 2)
  have harg : (1 : ℤ) + 2 * (h / 2) = h + 1 := by rw [h2]; ring
  rw [harg] at hval
  rw [hval, hZ1card]

private theorem szE4_upper {a f : ℕ} {h : ℤ} {U : Subgroup G}
    {a0 : G} (hfr : Frame L1 L2 S a f) (hUZ : U ≤ t.Zv h) (hU2 : IsPGroup 2 U)
    (hUGw : U ≤ t.Gw 3 4) (hZL : L2 ≤ Subgroup.centralizer (t.Zv 1 : Set G))
    (ha0Z : a0 ∈ t.Zv 1)
    (hcardinf : Nat.card (U ⊓ Subgroup.centralizer ({a0} : Set G) : Subgroup G) =
      (2 ^ (2 * a + 1)) ^ 2) :
    Nat.card (U ⊓ t.Gv 2 : Subgroup G) ≤ (2 ^ (2 * a + 1)) ^ 3 := by
  classical
  let W : Subgroup G := U ⊓ t.Gv 2
  change Nat.card W ≤ (2 ^ (2 * a + 1)) ^ 3
  have hU3 : U ≤ t.Gv 3 :=
    hUGw.trans (win_le_qv (a := 3) (b := 4) (i := 3) le_rfl (by norm_num))
  have hW2 : IsPGroup 2 W := hU2.to_le inf_le_left
  have hW23 : W ≤ t.Gw 2 3 := by
    intro x hx
    rw [mem_win_iff]
    intro i h1 h2
    rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl
    · exact hx.2
    · exact hU3 hx.1
  have hWp : W ≤ pCoreOf 2 (t.Gw 2 3) :=
    t.le_pCoreOf_Gw hfr (by norm_num : (2 : ℤ) < 3) hW2 hW23
  have hWroot : W ≤ t.rootOmega 2 := by
    intro x hx
    rw [t.mem_rootOmega_iff hfr 2]
    refine ⟨hWp hx, ?_⟩
    rw [t.szE4_sq_eq_one hUZ hx.1]
    exact one_mem _
  have hrootrel : (t.Qv 2).relIndex (t.rootOmega 2) = 2 ^ (2 * a + 1) := by
    have h := t.relIndex_rootOmega hfr 2
    rwa [if_pos (show Even (2 : ℤ) from ⟨1, by norm_num⟩)] at h
  have hrel1 : (t.Qv 2).relIndex W ≤ 2 ^ (2 * a + 1) :=
    (Subgroup.relIndex_le_of_le_right hWroot (by rw [hrootrel]; positivity)).trans_eq hrootrel
  have hinfle : t.Qv 2 ⊓ W ≤ U ⊓ Subgroup.centralizer ({a0} : Set G) := by
    refine le_inf (le_trans inf_le_right inf_le_left) ?_
    intro x hx
    have hxQ2 : x ∈ t.Qv 2 := hx.1
    have hQ2G1 : t.Qv 2 ≤ t.Gv 1 := by
      simpa using (t.Qv_le_Gv hfr 2).1
    have hQ2L1 : t.Qv 2 ≤ t.Lv 1 := t.le_Lv hfr (t.isPGroup_Qv 2) hQ2G1
    have hL1cent : t.Lv 1 ≤ Subgroup.centralizer (t.Zv 1 : Set G) :=
      t.szEnd_Lv_le_centralizer_Zv hZL ⟨0, by norm_num⟩
    have hxcent : x ∈ Subgroup.centralizer (t.Zv 1 : Set G) := hL1cent (hQ2L1 hxQ2)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hxcent a0 ha0Z).symm
  have hcardinfle : Nat.card (t.Qv 2 ⊓ W : Subgroup G) ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← hcardinf]
    exact Subgroup.card_le_of_le hinfle
  have hcardW := Subgroup.relIndex_mul_card (H := t.Qv 2) (K := W)
  calc Nat.card W = (t.Qv 2).relIndex W * Nat.card (t.Qv 2 ⊓ W : Subgroup G) := hcardW.symm
    _ ≤ (2 ^ (2 * a + 1)) * (2 ^ (2 * a + 1)) ^ 2 := Nat.mul_le_mul hrel1 hcardinfle
    _ = (2 ^ (2 * a + 1)) ^ 3 := by ring

private theorem szE4_lower
    {a f : ℕ} {h : ℤ} {U I : Subgroup G}
    (hfr : Frame L1 L2 S a f) (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hZh : t.Zv h ≤ t.Gw 3 4) (hZL : L2 ≤ Subgroup.centralizer (t.Zv 1 : Set G))
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1))
    (hUZ : U ≤ t.Zv h) (hIU : I ≤ U) (hIcomm : I ≤ ⁅t.Zv h, t.Zv 1⁆)
    (hcardI : Nat.card I = (2 ^ (2 * a + 1)) ^ 2)
    (hZU : t.Zv (h + 1) ≤ U) (hZG2 : t.Zv (h + 1) ≤ t.Gv 2)
    (hcardZ : Nat.card (t.Zv (h + 1)) = 2 ^ (2 * a + 1)) :
    (2 ^ (2 * a + 1)) ^ 3 ≤ Nat.card (U ⊓ t.Gv 2 : Subgroup G) := by
  classical
  have hcommQ : ⁅t.Zv h, t.Zv 1⁆ ≤ t.Qv 3 :=
    t.szEnd_commutator_le_Qv_three hfr hh hZ1 hZh
  have hcommC : ⁅t.Zv h, t.Zv 1⁆ ≤ Subgroup.centralizer (t.Zv 1 : Set G) :=
    t.szEnd_commutator_le_centralizer hfr hh hZ1 hZh hZL
  have hZinfC : t.Zv (h + 1) ⊓ Subgroup.centralizer (t.Zv 1 : Set G) = ⊥ :=
    t.szEnd_Zv_add_one_inf_centralizer_eq_bot hfr hh hev hZ1 hZ1' hZL hcard
  have hI_le_Q3 : I ≤ t.Qv 3 := hIcomm.trans hcommQ
  have hI_le_G2 : I ≤ t.Gv 2 := hI_le_Q3.trans (by simpa using (t.Qv_le_Gv hfr 3).1)
  have hI_le_C : I ≤ Subgroup.centralizer (t.Zv 1 : Set G) := hIcomm.trans hcommC
  have hIinfZ : I ⊓ t.Zv (h + 1) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hxinf : x ∈ t.Zv (h + 1) ⊓ Subgroup.centralizer (t.Zv 1 : Set G) :=
      ⟨hx.2, hI_le_C hx.1⟩
    rwa [hZinfC] at hxinf
  have hI_le_centZ : I ≤ Subgroup.centralizer (t.Zv (h + 1) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (t.szE4_mul_comm hUZ (hIU hx) (hZU hz)).symm
  have hInormZ : I ≤ normalizer (t.Zv (h + 1) : Set G) :=
    hI_le_centZ.trans (Subgroup.centralizer_le_normalizer (t.Zv (h + 1) : Set G))
  have hjoin : I ⊔ t.Zv (h + 1) ≤ U ⊓ t.Gv 2 :=
    sup_le (le_inf hIU hI_le_G2) (le_inf hZU hZG2)
  have hcardJoin : Nat.card (I ⊔ t.Zv (h + 1) : Subgroup G) = (2 ^ (2 * a + 1)) ^ 3 := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := I) (K := t.Zv (h + 1)) hInormZ
    rw [hIinfZ, Subgroup.card_bot, mul_one] at h
    rw [h, hcardI, hcardZ]
    ring
  calc (2 ^ (2 * a + 1)) ^ 3 = Nat.card (I ⊔ t.Zv (h + 1) : Subgroup G) := hcardJoin.symm
    _ ≤ Nat.card (U ⊓ t.Gv 2 : Subgroup G) := Subgroup.card_le_of_le hjoin

private theorem szE4_relIndex_U {a f : ℕ} {h : ℤ} {U : Subgroup G}
    (hfr : Frame L1 L2 S a f) (hU34 : U ≤ pCoreOf 2 (t.Gw 3 (3 + 1)))
    (hUK : t.K ≤ normalizer (U : Set G)) (hU3Q : ¬ U ≤ t.Qv 3)
    (hUZ : U ≤ t.Zv h) :
    (U ⊓ t.Qv 3).relIndex U = 2 ^ f := by
  have hU3 : U ≤ t.Gv 3 :=
    hU34.trans ((pCoreOf_le 2 (t.Gw 3 (3 + 1))).trans
      (win_le_qv (a := 3) (b := 3 + 1) (i := 3) le_rfl (by omega)))
  have hUnorm : U ≤ normalizer (t.Qv 3 : Set G) := hU3.trans (t.Gv_le_normalizer_Qv 3)
  have hUroot : U ≤ t.rootOmega 3 := by
    intro x hx
    rw [t.mem_rootOmega_iff hfr 3]
    refine ⟨hU34 hx, ?_⟩
    rw [t.szE4_sq_eq_one hUZ hx]
    exact one_mem _
  have hroot_eq : t.rootOmega 3 = U ⊔ t.Qv 3 :=
    le_antisymm (t.rootOmega_le_sup hfr 3 hU34 hUK hU3Q)
      (sup_le hUroot (t.Qv_le_rootOmega hfr 3))
  have h3 : ¬ Even (3 : ℤ) := by
    rintro ⟨k, hk⟩
    omega
  have hrootrel : (t.Qv 3).relIndex (t.rootOmega 3) = 2 ^ f := by
    have h := t.relIndex_rootOmega hfr 3
    rwa [if_neg h3] at h
  rw [hroot_eq] at hrootrel
  rw [← (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := U) (K := t.Qv 3) hUnorm).2]
  exact hrootrel

private theorem szE4_conclude {a f : ℕ} {h : ℤ} {U : Subgroup G}
    (hfr : Frame L1 L2 S a f) (hU2 : IsPGroup 2 U)
    (hU34 : U ≤ pCoreOf 2 (t.Gw 3 (3 + 1))) (hUK : t.K ≤ normalizer (U : Set G))
    (hUZ : U ≤ t.Zv h)
    (hUcard : Nat.card U = (2 ^ (2 * a + 1)) ^ 4)
    (hcardW : Nat.card (U ⊓ t.Gv 2 : Subgroup G) = (2 ^ (2 * a + 1)) ^ 3) :
    f = 2 * a + 1 := by
  have hWrel_q : (U ⊓ t.Gv 2).relIndex U = 2 ^ (2 * a + 1) := by
    have h := Subgroup.relIndex_mul_card (H := U ⊓ t.Gv 2) (K := U)
    rw [inf_eq_left.mpr inf_le_left, hcardW, hUcard] at h
    have hpos : 0 < (2 ^ (2 * a + 1)) ^ 3 := by positivity
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h]
    ring
  have hW_eq_Q3 : U ⊓ t.Gv 2 = U ⊓ t.Qv 3 := by
    have hGw : U ≤ t.Gw 3 (3 + 1) := hU34.trans (pCoreOf_le 2 (t.Gw 3 (3 + 1)))
    have h := (t.inf_Gv_eq_inf_Qv hfr 3 hU2).2 hGw
    rwa [show (3 : ℤ) - 1 = 2 by norm_num] at h
  have hnotUQ : ¬ U ≤ t.Qv 3 := by
    intro hUQ
    have hUGv2 : U ≤ t.Gv 2 := hUQ.trans (by simpa using (t.Qv_le_Gv hfr 3).1)
    have hWU : U ⊓ t.Gv 2 = U := inf_eq_left.mpr hUGv2
    have h1 : (U ⊓ t.Gv 2).relIndex U = 1 := by
      rw [hWU, Subgroup.relIndex_self]
    rw [hWrel_q] at h1
    have hlt : 1 < 2 ^ (2 * a + 1) :=
      Nat.one_lt_pow (by omega) (by norm_num : 1 < 2)
    exact hlt.ne' h1
  have hrel3 : (U ⊓ t.Qv 3).relIndex U = 2 ^ f :=
    t.szE4_relIndex_U hfr hU34 hUK hnotUQ hUZ
  have hqr : 2 ^ (2 * a + 1) = 2 ^ f := by
    rw [← hWrel_q, hW_eq_Q3, hrel3]
  exact (Nat.pow_right_injective (a := 2) (by norm_num : 2 ≤ 2) hqr).symm

private theorem szE4_cardW
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hZh : t.Zv h ≤ t.Gw 3 4) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G))
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1))
    {U : Subgroup G} (hUZ : U ≤ t.Zv h) (hUL : t.Lv h ≤ normalizer (U : Set G))
    (hnat : IsSzNaturalSection (t.Lv h) U ⊥ a) (hZU : t.Zv (h + 1) ≤ U) :
    Nat.card (U ⊓ t.Gv 2 : Subgroup G) = (2 ^ (2 * a + 1)) ^ 3 := by
  classical
  have hU2 : IsPGroup 2 U := (t.isPGroup_Zv h).to_le hUZ
  have hUcard : Nat.card U = (2 ^ (2 * a + 1)) ^ 4 := t.szE4_card_U hnat
  obtain ⟨a0sub, ha0ne_sub⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (t.Zv_ne_bot hfr.hF 1)
  let a0 : G := a0sub
  have ha0Z : a0 ∈ t.Zv 1 := a0sub.2
  have ha0ne : a0 ≠ 1 := fun h1 => ha0ne_sub (Subtype.ext h1)
  have hZ1Gv : t.Zv 1 ≤ t.Gv h := by
    intro x hx
    exact mem_win_iff.mp (hZ1 hx) h (by omega) le_rfl
  have ha0L : a0 ∈ t.Lv h := t.le_Lv hfr (t.isPGroup_Zv 1) hZ1Gv ha0Z
  obtain ⟨hZ1infQ, hZ1card⟩ :=
    t.szEnd_Zv_one_inf_Qv_and_card hfr hh hev hZ1 hZ1' hcard
  have ha0sq : a0 * a0 ∈ pCoreOf 2 (t.Lv h) := by
    have hsq : a0 * a0 = 1 := by
      have ha0Ω : a0 ∈ omegaOneCenterOf (t.Qv 1) := by
        have h := ha0Z
        rwa [t.Zv_eq 1] at h
      simpa [pow_two] using A4.sq_eq_one_of_mem_omegaOneCenterOf ha0Ω
    rw [hsq]
    exact one_mem _
  have ha0Q : a0 ∉ pCoreOf 2 (t.Lv h) := by
    rw [t.pCoreOf_Lv hfr h]
    intro hQ
    have hmem : a0 ∈ t.Zv 1 ⊓ t.Qv h := ⟨ha0Z, hQ⟩
    rw [hZ1infQ] at hmem
    exact ha0ne (Subgroup.mem_bot.mp hmem)
  have hcardinf : Nat.card (U ⊓ Subgroup.centralizer ({a0} : Set G) : Subgroup G) =
      (2 ^ (2 * a + 1)) ^ 2 :=
    t.szE4_card_inf_centralizer hnat hUL ha0L ha0sq ha0Q
  obtain ⟨φ, hφ, hφker⟩ := t.szE4_exists_phi hUZ hUL ha0L
  let I : Subgroup G := φ.range.map U.subtype
  have hcardI : Nat.card I = (2 ^ (2 * a + 1)) ^ 2 :=
    szE4_card_image φ hφker hcardinf hUcard
  have hI_le_U : I ≤ U := Subgroup.map_subtype_le φ.range
  have hI_le_comm : I ≤ ⁅t.Zv h, t.Zv 1⁆ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hy
    rw [← hu]
    rw [show U.subtype (φ u) = ⁅(u : G), a0⁆ from hφ u]
    exact Subgroup.commutator_mem_commutator (hUZ u.2) ha0Z
  have hUGw : U ≤ t.Gw 3 4 := hUZ.trans hZh
  have hZ_G2 : t.Zv (h + 1) ≤ t.Gv 2 := t.szE4_Zv_le_Gv_two hh hev hZ1
  have hcardZ : Nat.card (t.Zv (h + 1)) = 2 ^ (2 * a + 1) :=
    t.szE4_card_Zv_succ hev hZ1card
  exact le_antisymm
    (t.szE4_upper hfr hUZ hU2 hUGw hZL ha0Z hcardinf)
    (t.szE4_lower hfr hh hev hZ1 hZ1' hZh hZL hcard hUZ hI_le_U hI_le_comm hcardI
      hZU hZ_G2 hcardZ)

theorem eq_two_mul_add_one_of_sz
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {h : ℤ} (hh : 4 ≤ h) (hev : Even h)
    (hZ1 : t.Zv 1 ≤ t.Gw (2 - h) h) (hZ1' : ¬ t.Zv 1 ≤ t.Gv (h + 1))
    (hZh : t.Zv h ≤ t.Gw 3 4) (hZL : L2 ≤ centralizer (t.Zv 1 : Set G))
    (hcard : Nat.card (t.Zv 1) ≤ 2 ^ (2 * a + 1)) :
    f = 2 * a + 1 := by
  classical
  obtain ⟨U, hUZ, hUL, hnat, hUK, hZU⟩ :=
    t.szEnd_exists_natural hfr hh hev hZ1 hZ1' hZh hZL hcard
  have hU2 : IsPGroup 2 U := (t.isPGroup_Zv h).to_le hUZ
  have hUGw : U ≤ t.Gw 3 4 := hUZ.trans hZh
  have hU34 : U ≤ pCoreOf 2 (t.Gw 3 (3 + 1)) := by
    rw [show (3 : ℤ) + 1 = 4 by norm_num]
    exact t.le_pCoreOf_Gw hfr (by norm_num : (3 : ℤ) < 4) hU2 hUGw
  have hcardW : Nat.card (U ⊓ t.Gv 2 : Subgroup G) = (2 ^ (2 * a + 1)) ^ 3 :=
    t.szE4_cardW hfr hh hev hZ1 hZ1' hZh hZL hcard hUZ hUL hnat hZU
  exact t.szE4_conclude hfr hU2 hU34 hUK hUZ (t.szE4_card_U hnat) hcardW

end Track

end CFSG.Quasithin.Stroth.Rq

end
