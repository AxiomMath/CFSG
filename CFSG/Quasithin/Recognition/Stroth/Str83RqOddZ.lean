module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRoot
import CFSG.Quasithin.Recognition.Stroth.Str83Rq410a
import CFSG.Walter.Bender1970.S3.CoreExchangeTools

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem oddZ_K_le_normalizer_S {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer (S : Set G) :=
  ((le_sup_right : t.K ≤ S ⊔ t.K).trans t.sup_K_eq_bigB.le).trans hfr.hN

private theorem oddZ_not_S_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : ¬ S ≤ t.Qv 0 := by
  intro hSle
  have h9 := (t.relIndex_Qv_pCoreOf hfr 0).2
  rw [zero_add, t.pCoreOf_Gw_zero_one hfr, if_pos (by decide),
    Subgroup.relIndex_eq_one.mpr hSle] at h9
  have h4 : 4 ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (2 * a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (2 ^ (2 * a + 1)) ^ 2 := by rw [← pow_mul, mul_comm]
  omega

private theorem oddZ_not_S_le_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : ¬ S ≤ t.Qv 1 := by
  intro hSle
  have h := (t.relIndex_Qv_pCoreOf hfr 1).1
  rw [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg (by decide),
    Subgroup.relIndex_eq_one.mpr hSle] at h
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  omega

private theorem oddZ_S_le_centralizer_Zv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {i : ℤ} (hSG : S ≤ t.Gv i)
    (hmin : ∀ X : Subgroup G, X ≤ t.Zv i → X ≠ ⊥ →
      t.K ≤ normalizer (X : Set G) → X = t.Zv i) :
    S ≤ centralizer (t.Zv i : Set G) := by
  have hSN : S ≤ normalizer (t.Zv i : Set G) := hSG.trans (t.Gv_le_normalizer_Zv i)
  have hS2 : IsPGroup 2 S := by
    rw [← t.pCoreOf_Gw_zero_one hfr]
    exact pCoreOf_isPGroup 2 _
  have hXne : t.Zv i ⊓ centralizer (S : Set G) ≠ ⊥ :=
    CFSG.Walter.inf_centralizer_ne_bot_of_isPGroup Nat.prime_two hS2 (t.isPGroup_Zv i) hSN
      (t.Zv_ne_bot hfr.hF i)
  have hKX : t.K ≤ normalizer ((t.Zv i ⊓ centralizer (S : Set G) : Subgroup G) : Set G) :=
    (le_inf ((t.K_le_Gv i).trans (t.Gv_le_normalizer_Zv i))
      ((t.oddZ_K_le_normalizer_S hfr).trans
        (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup S))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hXeq := hmin (t.Zv i ⊓ centralizer (S : Set G)) inf_le_left hXne hKX
  rw [← hXeq]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp hz.2 s hs).symm

theorem IsMaxArc.Zv_eq_omegaOneCenterOf {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {u : ℤ} {n : ℕ} (hγ : t.IsMaxArc u n) {v : ℤ}
    (hZ : t.Zv v ≤ t.Gw u (u + n)) :
    t.Zv v = omegaOneCenterOf (pCoreOf 2 (t.Gw u (u + n))) := by
  have hn : 2 ≤ n := IsMaxArc.two_le t hfr hγ
  have hlt : u < u + (n : ℤ) := by omega
  have hZO : t.Zv v ≤ pCoreOf 2 (t.Gw u (u + n)) :=
    t.le_pCoreOf_Gw hfr hlt (t.isPGroup_Zv v) hZ
  refine le_antisymm ?_ ?_
  · intro z hz
    refine IsMaxArc.mem_omegaOneCenterOf t hfr hγ (hZO hz) ?_
    rw [t.Zv_eq v] at hz
    exact A4.sq_eq_one_of_mem_omegaOneCenterOf hz
  · exact IsMaxArc.omegaOneCenterOf_le t hfr hγ hZO (t.Zv_ne_bot hfr.hF v)
      ((t.K_le_Gv v).trans (t.Gv_le_normalizer_Zv v))

theorem L1_le_centralizer_Zv_zero_of_minimal {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hmin : ∀ X : Subgroup G, X ≤ t.Zv 0 → X ≠ ⊥ → t.K ≤ normalizer (X : Set G) → X = t.Zv 0) :
    L1 ≤ centralizer (t.Zv 0 : Set G) := by
  have hSG : S ≤ t.Gv 0 := by
    rw [t.Gv_zero]
    exact (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSle : S ≤ centralizer (t.Zv 0 : Set G) :=
    t.oddZ_S_le_centralizer_Zv hfr hSG hmin
  refine t.L1_le_centralizer_of_sz hfr (Y := S) (C := t.Zv 0) le_rfl ?_ ?_ le_rfl hSle ?_
  · exact (le_sup_left : t.D1 ≤ t.K).trans (t.oddZ_K_le_normalizer_S hfr)
  · exact t.oddZ_not_S_le_Qv_zero hfr
  · exact (Subgroup.map_mono hSle).trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup _
        (t.Gv_le_normalizer_Zv 0 (by rw [t.Gv_zero]; exact t.track.x₁_mem)))).le

theorem L2_le_centralizer_Zv_one_of_minimal {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hmin : ∀ X : Subgroup G, X ≤ t.Zv 1 → X ≠ ⊥ → t.K ≤ normalizer (X : Set G) → X = t.Zv 1) :
    L2 ≤ centralizer (t.Zv 1 : Set G) := by
  have hSG : S ≤ t.Gv 1 := by
    rw [t.Gv_one]
    exact (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hSle : S ≤ centralizer (t.Zv 1 : Set G) :=
    t.oddZ_S_le_centralizer_Zv hfr hSG hmin
  refine t.L2_le_centralizer_of_l2 hfr (Y := S) (C := t.Zv 1) le_rfl ?_ ?_ le_rfl hSle ?_
  · exact (le_sup_right : t.D2 ≤ t.K).trans (t.oddZ_K_le_normalizer_S hfr)
  · exact t.oddZ_not_S_le_Qv_one hfr
  · exact t.Gv_le_normalizer_Zv 1 (by rw [t.Gv_one]; exact t.track.x₂_mem)

end Track

end CFSG.Quasithin.Stroth.Rq

end
