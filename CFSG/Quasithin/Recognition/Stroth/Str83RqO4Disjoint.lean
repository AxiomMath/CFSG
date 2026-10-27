module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Goldschmidt
import CFSG.Quasithin.Recognition.Stroth.Str83RqTools

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem Zv_zero_inf_QT {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hα : t.YX t.QT 1 ≤ centralizer (t.QT : Set G))
    (hcov : L2 ≤ t.YX t.QT 1 ⊔ t.Qv 1)
    (hS : ∀ R : Subgroup G, R ≤ t.Zv 0 → t.K ≤ normalizer (R : Set G) →
      t.x₁ ∈ normalizer (R : Set G) → CosetTrans (normalizer (R : Set G)) (t.Gv 1) (t.Gv 0) →
      R = ⊥) :
    t.Zv 0 ⊓ t.QT = ⊥ := by
  let R : Subgroup G := t.Zv 0 ⊓ t.QT
  have hR : R ≤ t.Zv 0 := inf_le_left
  have hK : t.K ≤ normalizer (R : Set G) :=
    (le_inf (t.K_le_normalizer_Zv 0) t.K_le_normalizer_pCoreOf_GT).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := t.Zv 0) (K := t.QT))
  have hxZ : t.x₁ ∈ normalizer (t.Zv 0 : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using t.map_Zv_x₁ 0)
  have hx : t.x₁ ∈ normalizer (R : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := t.Zv 0) (K := t.QT)
      (Subgroup.mem_inf.mpr ⟨hxZ, t.x₁_mem_normalizer_pCoreOf_GT⟩)
  have hYXG : t.YX t.QT 1 ≤ t.Gv 1 :=
    (oTwoRes_le (t.LX t.QT 1)).trans
      ((oTwoPrime_le (t.MX t.QT 1)).trans inf_le_right)
  have hcentR : centralizer (t.QT : Set G) ≤ centralizer (R : Set G) :=
    Subgroup.centralizer_le fun _ hx => hx.2
  have hYXN : t.YX t.QT 1 ≤ normalizer (R : Set G) :=
    hα.trans (hcentR.trans (Subgroup.centralizer_le_normalizer _))
  have hcov' : L2 ≤ (normalizer (R : Set G) ⊓ t.Gv 1) ⊔ t.Qv 1 :=
    hcov.trans (sup_le_sup (le_inf hYXN hYXG) le_rfl)
  have htr : CosetTrans (normalizer (R : Set G)) (t.Gv 1) (t.Gv 0) :=
    (t.cosetTrans_one_of_le_sup hfr inf_le_right hcov').mono inf_le_left
  have hbot : R = ⊥ := hS R hR hK hx htr
  exact hbot

theorem Zv_one_inf_QT {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hα : t.YX t.QT 1 ≤ centralizer (t.QT : Set G)) (hcov : L2 ≤ t.YX t.QT 1 ⊔ t.Qv 1)
    (h0 : t.Zv 0 ⊓ t.QT = ⊥) :
    t.Zv 1 ⊓ t.QT = ⊥ := by
  have hbig : pCoreOf 2 (bigB L1 L2 S) = S := by
    rw [← t.Gw_zero_one hfr.hF, t.pCoreOf_Gw_zero_one hfr]
  let R : Subgroup G := t.Zv 1 ⊓ t.QT
  have hRZ : R ≤ t.Zv 1 := inf_le_left
  have hRQ : R ≤ t.QT := inf_le_right
  have hRcentYX : R ≤ centralizer (t.YX t.QT 1 : Set G) :=
    hRQ.trans (Subgroup.le_centralizer_iff.mp hα)
  have hYXcent : t.YX t.QT 1 ≤ centralizer (R : Set G) :=
    Subgroup.le_centralizer_iff.mpr hRcentYX
  have hRcentQ : R ≤ centralizer (t.Qv 1 : Set G) :=
    hRZ.trans (t.Zv_le_centralizer 1)
  have hL2cent : L2 ≤ centralizer (R : Set G) :=
    hcov.trans (sup_le hYXcent (Subgroup.le_centralizer_iff.mp hRcentQ))
  have hRcentSup : R ≤ centralizer ((L2 ⊔ t.Qv 1 : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (sup_le hL2cent (Subgroup.le_centralizer_iff.mp hRcentQ))
  have hSle : S ≤ L2 ⊔ t.Qv 1 := by
    refine (le_of_eq (S_eq_sup_right hfr)).trans ?_
    rw [t.Qv_one]
    exact sup_le_sup inf_le_right le_rfl
  have hRcentS : R ≤ centralizer (S : Set G) :=
    hRcentSup.trans (Subgroup.centralizer_le hSle)
  have hz := z2_inf_centralizer_le_z1 (L1 := L1) (L2 := L2) (S := S) hfr.hF.1
  rw [hbig] at hz
  have hRZ2 : R ≤ Z2 L1 L2 S := by
    rw [← t.Zv_one]
    exact hRZ
  have hRZ1 : R ≤ Z1 L1 L2 S := (le_inf hRZ2 hRcentS).trans hz
  have hRZ0 : R ≤ t.Zv 0 := by
    rw [t.Zv_zero]
    exact hRZ1
  have hle : R ≤ t.Zv 0 ⊓ t.QT := le_inf hRZ0 hRQ
  rw [h0] at hle
  exact le_bot_iff.mp hle

end Track

end CFSG.Quasithin.Stroth.Rq

end
