module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
public import CFSG.Quasithin.Recognition.Stroth.Str83RqRoot
import CFSG.GroupTheory.DedekindNormalizer
import CFSG.Timmesfeld.RankOne.Basic
import CFSG.Quasithin.Vol2.Ch10SecQ3CQ

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem win_inf_of_le {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    t.Gw b c ⊓ t.Gw a b = t.Gw a c := by
  ext x
  rw [mem_inf, mem_win_iff, mem_win_iff, mem_win_iff]
  constructor
  · rintro ⟨h₁, h₂⟩ i hi₁ hi₂
    rcases le_total i b with hib | hbi
    · exact h₂ i hi₁ hib
    · exact h₁ i hbi hi₂
  · intro h
    exact ⟨fun i hi₁ hi₂ => h i (hab.trans hi₁) hi₂,
      fun i hi₁ hi₂ => h i hi₁ (hi₂.trans hbc)⟩

private theorem le_normalizer_map_conj_of_map_eq {H X : Subgroup G} {g : G}
    (hg : H.map (MulAut.conj g).toMonoidHom = H) (hX : H ≤ normalizer (X : Set G)) :
    H ≤ normalizer (X.map (MulAut.conj g).toMonoidHom : Set G) := by
  have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hX
  rw [hg, Subgroup.map_equiv_normalizer_eq] at h
  exact h

private theorem map_conj_eq_self_of_mem_GT {z : G} (hz : z ∈ t.GT) (u w : ℤ) :
    (t.Gw u w).map (MulAut.conj z).toMonoidHom = t.Gw u w :=
  CFSG.Timmesfeld.RankOne.map_conj_of_mem
    (mem_win_iff.mpr fun i _ _ => Subgroup.mem_iInf.mp hz i)

theorem exists_reflection_mem_sup
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (b : ℤ) {X Y : Subgroup G} (hX : IsPGroup 2 X)
    (hY : IsPGroup 2 Y) (hXb : X ≤ t.Gw (b - 1) b) (hYb : Y ≤ t.Gw b (b + 1))
    (hXn : ¬ X ≤ t.Gv (b + 1)) (hYn : ¬ Y ≤ t.Gv (b - 1)) :
    ∃ y ∈ X ⊔ Y ⊔ t.K, y ∈ normalizer (t.K : Set G) ∧
      ∀ u w : ℤ, (t.Gw u w).map (MulAut.conj y).toMonoidHom = t.Gw (2 * b - w) (2 * b - u) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := X ⊔ Y ⊔ t.K with hNdef
  set R : Subgroup G := pCoreOf 2 (t.Gw b (b + 1)) with hRdef
  set R' : Subgroup G := pCoreOf 2 (t.Gw (b - 1) b) with hR'def
  set Qb : Subgroup G := t.Qv b with hQbdef
  have hKN : t.K ≤ N := by
    rw [hNdef]
    exact (le_sup_right : t.K ≤ X ⊔ Y ⊔ t.K)
  have hNv : N ≤ t.Gv b := by
    rw [hNdef]
    have hXv : X ≤ t.Gv b := by
      have hwin : t.Gw (b - 1) b ≤ t.Gw b b := win_mono (by omega) le_rfl
      have h := hXb.trans hwin
      rwa [show t.Gw b b = t.Gv b from win_self b] at h
    have hYv : Y ≤ t.Gv b := by
      have hwin : t.Gw b (b + 1) ≤ t.Gw b b := win_mono le_rfl (by omega)
      have h := hYb.trans hwin
      rwa [show t.Gw b b = t.Gv b from win_self b] at h
    exact sup_le (sup_le hXv hYv) (t.K_le_Gv b)
  obtain ⟨y_b, hy_b_Gv, hy_b_K, hy_b_Gw, hy_b_Qv, hy_b_Zv⟩ := t.exists_reflection b
  have hy_b_Kmap : t.K.map (MulAut.conj y_b).toMonoidHom = t.K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hy_b_K
  have hQb : Qb.map (MulAut.conj y_b).toMonoidHom = Qb := by
    rw [hQbdef]
    have h := hy_b_Qv b
    rwa [show 2 * b - b = b by ring] at h
  have hY_R : Y ≤ R := by
    rw [hRdef]
    exact t.le_pCoreOf_Gw hfr (by omega) hY hYb
  have h₁ : ∀ x ∈ R, x ^ 2 ∈ Qb → x ∈ N ⊔ Qb := by
    intro x hxR hxQ
    set Yt : Subgroup G := (Y ⊔ t.K) ⊓ R with hYt
    have hYtR : Yt ≤ R := by rw [hYt]; exact inf_le_right
    have hKYt : t.K ≤ normalizer (Yt : Set G) := by
      rw [hYt]
      refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      · exact le_sup_right.trans Subgroup.le_normalizer
      · exact (t.K_le_Gw b (b + 1)).trans (le_normalizer_pCoreOf 2 _)
    have hYtQ : ¬ Yt ≤ Qb := by
      intro hle
      have hYle : Y ≤ Yt := by rw [hYt]; exact le_inf le_sup_left hY_R
      rw [hQbdef] at hle
      exact hYn (hYle.trans (hle.trans (t.Qv_le_Gv hfr b).1))
    have hroot := t.rootOmega_le_sup hfr b (X := Yt) hYtR hKYt hYtQ
    have hxroot : x ∈ t.rootOmega b := (t.mem_rootOmega_iff hfr b).mpr ⟨hxR, hxQ⟩
    have hYtN : Yt ≤ N := by
      rw [hYt, hNdef]
      exact inf_le_left.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    exact (sup_le (hYtN.trans le_sup_left) le_sup_right) (hroot hxroot)
  have hX_R' : X ≤ R' := by
    rw [hR'def]
    exact t.le_pCoreOf_Gw hfr (by omega) hX hXb
  have hR'_map : R'.map (MulAut.conj y_b).toMonoidHom = R := by
    rw [hR'def, hRdef, ← pCoreOf_map_mulEquiv 2 (MulAut.conj y_b) (t.Gw (b - 1) b)]
    have h := hy_b_Gw (b - 1) b
    rw [show 2 * b - b = b by ring, show 2 * b - (b - 1) = b + 1 by ring] at h
    rw [h]
  have hR_map : R.map (MulAut.conj y_b).toMonoidHom = R' := by
    rw [hRdef, hR'def, ← pCoreOf_map_mulEquiv 2 (MulAut.conj y_b) (t.Gw b (b + 1))]
    have h := hy_b_Gw b (b + 1)
    rw [show 2 * b - (b + 1) = b - 1 by ring, show 2 * b - b = b by ring] at h
    rw [h]
  have h₂ : ∀ x ∈ R', x ^ 2 ∈ Qb → x ∈ N ⊔ Qb := by
    intro x hxR' hxQ
    set Xt : Subgroup G := (X ⊔ t.K) ⊓ R' with hXt
    have hXtR' : Xt ≤ R' := by rw [hXt]; exact inf_le_right
    have hKXt : t.K ≤ normalizer (Xt : Set G) := by
      rw [hXt]
      refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
      · exact le_sup_right.trans Subgroup.le_normalizer
      · exact (t.K_le_Gw (b - 1) b).trans (le_normalizer_pCoreOf 2 _)
    have hXtQ : ¬ Xt ≤ Qb := by
      intro hle
      have hXle : X ≤ Xt := by rw [hXt]; exact le_inf le_sup_left hX_R'
      rw [hQbdef] at hle
      exact hXn (hXle.trans (hle.trans (t.Qv_le_Gv hfr b).2))
    have hXt_map_R : Xt.map (MulAut.conj y_b).toMonoidHom ≤ R := by
      rw [← hR'_map]
      exact Subgroup.map_mono hXtR'
    have hK_Xtmap : t.K ≤
        normalizer ((Xt.map (MulAut.conj y_b).toMonoidHom : Subgroup G) : Set G) :=
      le_normalizer_map_conj_of_map_eq (H := t.K) (X := Xt) (g := y_b) hy_b_Kmap hKXt
    have hXt_map_Q : ¬ Xt.map (MulAut.conj y_b).toMonoidHom ≤ Qb := by
      intro hle
      apply hXtQ
      have h := Subgroup.map_mono (f := (MulAut.conj y_b⁻¹).toMonoidHom) hle
      rw [CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj Xt y_b,
        (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQb).symm] at h
      exact h
    have hroot := t.rootOmega_le_sup hfr b
      (X := Xt.map (MulAut.conj y_b).toMonoidHom) hXt_map_R hK_Xtmap hXt_map_Q
    have hx'R : y_b * x * y_b⁻¹ ∈ R := by
      have hmem : (MulAut.conj y_b) x ∈ R'.map (MulAut.conj y_b).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj y_b).toMonoidHom hxR'
      rwa [hR'_map] at hmem
    have hx'Q : (y_b * x * y_b⁻¹) ^ 2 ∈ Qb := by
      have hmem : (MulAut.conj y_b) (x ^ 2) ∈ Qb.map (MulAut.conj y_b).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj y_b).toMonoidHom hxQ
      rw [hQb] at hmem
      simpa [MulAut.conj_apply, map_pow] using hmem
    have hx'root : y_b * x * y_b⁻¹ ∈ t.rootOmega b :=
      (t.mem_rootOmega_iff hfr b).mpr ⟨hx'R, hx'Q⟩
    have hx'mem : y_b * x * y_b⁻¹ ∈ Xt.map (MulAut.conj y_b).toMonoidHom ⊔ Qb :=
      hroot hx'root
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj y_b⁻¹).toMonoidHom hx'mem
    rw [Subgroup.map_sup, CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj Xt y_b,
      (CFSG.Timmesfeld.RankOne.map_conj_eq_iff.mp hQb).symm] at hmem
    have hxmem : x ∈ Xt ⊔ Qb := by
      simpa [MulAut.conj_apply, mul_assoc] using hmem
    have hXtN : Xt ≤ N := by
      rw [hXt, hNdef]
      exact inf_le_left.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
    exact (sup_le (hXtN.trans le_sup_left) le_sup_right) hxmem
  obtain ⟨m, hmN, s, hsGw, hms⟩ :=
    t.exists_mul_of_mem_Gv hfr b (X := N) hNv h₁ h₂ hy_b_Gv
  have hs_map : (t.Gw b (b + 1)).map (MulAut.conj s).toMonoidHom = t.Gw b (b + 1) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hsGw)
  have hy_b_win : (t.Gw b (b + 1)).map (MulAut.conj y_b).toMonoidHom = t.Gw (b - 1) b := by
    have h := hy_b_Gw b (b + 1)
    rw [show 2 * b - (b + 1) = b - 1 by ring, show 2 * b - b = b by ring] at h
    exact h
  have hmap_m : (t.Gw b (b + 1)).map (MulAut.conj m).toMonoidHom = t.Gw (b - 1) b := by
    calc
      (t.Gw b (b + 1)).map (MulAut.conj m).toMonoidHom
          = ((t.Gw b (b + 1)).map (MulAut.conj s).toMonoidHom).map
              (MulAut.conj m).toMonoidHom := by rw [hs_map]
      _ = (t.Gw b (b + 1)).map (MulAut.conj (m * s)).toMonoidHom :=
          Subgroup.map_conj_map_conj (t.Gw b (b + 1)) s m
      _ = (t.Gw b (b + 1)).map (MulAut.conj y_b).toMonoidHom := by rw [hms]
      _ = t.Gw (b - 1) b := hy_b_win
  set K₁ : Subgroup G := t.K.map (MulAut.conj m).toMonoidHom with hK₁def
  have hK₁N : K₁ ≤ N := by
    intro x hx
    have hxK : m⁻¹ * x * m ∈ t.K := by
      have h := hx
      rw [hK₁def, mem_map_conj_iff] at h
      exact h
    have hxN : m⁻¹ * x * m ∈ N := hKN hxK
    have hx' : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
    rw [hx']
    exact N.mul_mem (N.mul_mem hmN hxN) (N.inv_mem hmN)
  have hK₁Gw : K₁ ≤ t.Gw (b - 1) b := by
    rw [hK₁def, ← hmap_m]
    exact Subgroup.map_mono (t.K_le_Gw b (b + 1))
  have hK₁odd : Odd (Nat.card K₁) := by
    rw [hK₁def, Subgroup.card_map_of_injective (MulAut.conj m).injective]
    exact t.hHall.2.1
  set P : Subgroup G := N ⊓ R' with hPdef
  have hP2 : IsPGroup 2 P := by
    rw [hPdef]
    exact (pCoreOf_isPGroup 2 (t.Gw (b - 1) b)).to_le inf_le_right
  have hHnormP : t.K ≤ normalizer (P : Set G) := by
    rw [hPdef]
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact hKN.trans Subgroup.le_normalizer
    · exact (t.K_le_Gw (b - 1) b).trans (le_normalizer_pCoreOf 2 _)
  have hK₁normP : K₁ ≤ normalizer (P : Set G) := by
    rw [hPdef]
    refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact hK₁N.trans Subgroup.le_normalizer
    · exact hK₁Gw.trans (le_normalizer_pCoreOf 2 _)
  have hPK : P ⊓ t.K = ⊥ :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.inf_eq_bot_of_odd hP2 t.hHall.2.1
  have hPK₁ : P ⊓ K₁ = ⊥ :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.inf_eq_bot_of_odd hP2 hK₁odd
  have hGwK : t.Gw (b - 1) b = R' ⊔ t.K := by
    rw [hR'def]
    exact t.Gw_eq_sup hfr (by omega)
  have hRmap : R.map (MulAut.conj m).toMonoidHom = R' := by
    rw [hRdef, hR'def, ← pCoreOf_map_mulEquiv 2 (MulAut.conj m) (t.Gw b (b + 1))]
    rw [hmap_m]
  have hGwK₁ : t.Gw (b - 1) b = R' ⊔ K₁ := by
    calc
      t.Gw (b - 1) b = (t.Gw b (b + 1)).map (MulAut.conj m).toMonoidHom := hmap_m.symm
      _ = (R ⊔ t.K).map (MulAut.conj m).toMonoidHom := by
          rw [show t.Gw b (b + 1) = R ⊔ t.K from t.Gw_eq_sup hfr (by omega)]
      _ = R.map (MulAut.conj m).toMonoidHom ⊔ K₁ := by
          rw [Subgroup.map_sup, hK₁def]
      _ = R' ⊔ K₁ := by rw [hRmap]
  have hsup : P ⊔ t.K = P ⊔ K₁ := by
    have h1 : P ⊔ t.K = N ⊓ t.Gw (b - 1) b := by
      rw [hPdef, hGwK, sup_comm (N ⊓ R') t.K, sup_comm R' t.K]
      exact (CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer (S := t.K) (T := R')
        (U := N) hKN ((t.K_le_Gw (b - 1) b).trans (le_normalizer_pCoreOf 2 _))).symm
    have h2 : P ⊔ K₁ = N ⊓ t.Gw (b - 1) b := by
      rw [hPdef, hGwK₁, sup_comm (N ⊓ R') K₁, sup_comm R' K₁]
      exact (CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer (S := K₁) (T := R')
        (U := N) hK₁N (hK₁Gw.trans (le_normalizer_pCoreOf 2 _))).symm
    rw [h1, h2]
  obtain ⟨n, hnP, hn⟩ :=
    CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.exists_conj_of_complement
      (P := P) (H := t.K) (K := K₁) hP2 t.hHall.2.1 hHnormP hK₁normP hPK hPK₁ hsup
  have hnN : n ∈ N := by
    have h := hnP
    rw [hPdef] at h
    exact (Subgroup.mem_inf.mp h).1
  have hyN : n * m ∈ N := N.mul_mem hnN hmN
  have hmap_eq : t.K.map (MulAut.conj m).toMonoidHom =
      t.K.map (MulAut.conj n⁻¹).toMonoidHom := by
    rw [← hK₁def, hn]
  have hyK : n * m ∈ normalizer (t.K : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    calc
      t.K.map (MulAut.conj (n * m)).toMonoidHom
          = (t.K.map (MulAut.conj m).toMonoidHom).map
              (MulAut.conj n).toMonoidHom := (Subgroup.map_conj_map_conj t.K m n).symm
      _ = (t.K.map (MulAut.conj n⁻¹).toMonoidHom).map
              (MulAut.conj n).toMonoidHom := by rw [hmap_eq]
      _ = t.K.map (MulAut.conj (n * n⁻¹)).toMonoidHom :=
          Subgroup.map_conj_map_conj t.K n⁻¹ n
      _ = t.K := by
          rw [mul_inv_cancel]
          have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
            ext z
            simp [MulAut.conj_apply]
          rw [h1, Subgroup.map_id]
  have hzR : y_b⁻¹ * n * y_b ∈ R := by
    have hn_img : y_b * n * y_b⁻¹ ∈ R := by
      have hmem : (MulAut.conj y_b) n ∈ R'.map (MulAut.conj y_b).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj y_b).toMonoidHom (Subgroup.mem_inf.mp hnP).2
      rwa [hR'_map] at hmem
    have hsq_map : R.map (MulAut.conj (y_b * y_b)).toMonoidHom = R := by
      calc
        R.map (MulAut.conj (y_b * y_b)).toMonoidHom
            = (R.map (MulAut.conj y_b).toMonoidHom).map
                (MulAut.conj y_b).toMonoidHom :=
            (Subgroup.map_conj_map_conj R y_b y_b).symm
        _ = R'.map (MulAut.conj y_b).toMonoidHom := by rw [hR_map]
        _ = R := hR'_map
    have hsq_norm : y_b * y_b ∈ normalizer (R : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hsq_map
    have hysq_inv : (y_b * y_b)⁻¹ ∈ normalizer (R : Set G) := inv_mem hsq_norm
    have h := (Subgroup.mem_normalizer_iff.mp hysq_inv (y_b * n * y_b⁻¹)).mp hn_img
    convert h using 1 <;> group
  set z : G := y_b⁻¹ * (n * m) with hzdef
  have hz_eq : z = (y_b⁻¹ * n * y_b) * s⁻¹ := by
    rw [hzdef, hms]
    group
  have hzGw : z ∈ t.Gw b (b + 1) := by
    rw [hz_eq]
    exact (t.Gw b (b + 1)).mul_mem
      (SetLike.le_def.mp (pCoreOf_le 2 (t.Gw b (b + 1))) hzR)
      ((t.Gw b (b + 1)).inv_mem hsGw)
  have hzK : z ∈ normalizer (t.K : Set G) := by
    rw [hzdef]
    exact (normalizer (t.K : Set G)).mul_mem (inv_mem hy_b_K) hyK
  have hzGT : z ∈ t.GT := t.mem_GT_of_mem_normalizer hzGw hzK
  have hz_map : ∀ u w, (t.Gw u w).map (MulAut.conj z).toMonoidHom = t.Gw u w :=
    fun u w => t.map_conj_eq_self_of_mem_GT hzGT u w
  have hy_eq : n * m = y_b * z := by rw [hzdef]; group
  refine ⟨n * m, hyN, hyK, ?_⟩
  intro u w
  calc
    (t.Gw u w).map (MulAut.conj (n * m)).toMonoidHom
        = (t.Gw u w).map (MulAut.conj (y_b * z)).toMonoidHom := by rw [hy_eq]
    _ = ((t.Gw u w).map (MulAut.conj z).toMonoidHom).map
          (MulAut.conj y_b).toMonoidHom :=
        (Subgroup.map_conj_map_conj (t.Gw u w) z y_b).symm
    _ = (t.Gw u w).map (MulAut.conj y_b).toMonoidHom := by rw [hz_map u w]
    _ = t.Gw (2 * b - w) (2 * b - u) := hy_b_Gw u w

theorem IsMaxArc.false_of_isFixRadius
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε c : ℤ} {n ρ : ℕ}
    (h : t.IsMaxArc ε n) (hc : ε < c) (hρ : t.IsFixRadius c ρ)
    (hlong : (n : ℤ) < 2 * (ε + n - (c + ρ))) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := pCoreOf 2 (t.Gw ε (ε + n)) with hQdef
  have hQne : Q ≠ ⊥ := h.pCoreOf_ne_bot
  have hρ1 : 1 ≤ ρ := IsFixRadius.one_le t hfr hρ
  set b : ℤ := c + (ρ : ℤ) with hbdef
  set c' : ℤ := c + 2 * (ρ : ℤ) with hc'def
  have hρ' : t.IsFixRadius c' ρ := by
    rw [hc'def]
    exact IsFixRadius.shift t hρ (ρ : ℤ)
  have hcc' : c < c' := by rw [hc'def]; omega
  have hc'εn : c' < ε + n := by
    rw [hc'def, hbdef] at *
    omega
  have hεb : ε ≤ b := by rw [hbdef]; omega
  have hbεn : b ≤ ε + n := by rw [hbdef]; omega
  have hXb : t.Zv c ≤ t.Gw (b - 1) b := by
    refine hρ.le_Gw.trans (win_mono (a := c - (ρ : ℤ)) (b := c + (ρ : ℤ))
      (a' := b - 1) (b' := b) ?_ ?_)
    · rw [hbdef]; omega
    · omega
  have hYb : t.Zv c' ≤ t.Gw b (b + 1) := by
    refine hρ'.le_Gw.trans (win_mono (a := c' - (ρ : ℤ)) (b := c' + (ρ : ℤ))
      (a' := b) (b' := b + 1) ?_ ?_)
    · rw [hc'def, hbdef]; omega
    · rw [hc'def, hbdef]; omega
  have hXn : ¬ t.Zv c ≤ t.Gv (b + 1) := by
    rw [hbdef]
    exact hρ.not_le_Gv
  have hYn : ¬ t.Zv c' ≤ t.Gv (b - 1) := by
    have hidx : c' - (ρ : ℤ) - 1 = b - 1 := by rw [hc'def, hbdef]; ring
    rw [← hidx]
    exact IsFixRadius.not_le_Gv_sub t hρ'
  obtain ⟨y, hyN, hyK, hymap⟩ :=
    t.exists_reflection_mem_sup hfr b (X := t.Zv c) (Y := t.Zv c')
      (t.isPGroup_Zv c) (t.isPGroup_Zv c') hXb hYb hXn hYn
  have hQlew : Q ≤ t.Gw ε (ε + n) := pCoreOf_le 2 _
  have hQ_Qvc : Q ≤ t.Qv c :=
    t.le_Qv_of_le_Gw hfr (by omega) (by omega) (pCoreOf_isPGroup 2 _) hQlew
  have hQ_Qvc' : Q ≤ t.Qv c' :=
    t.le_Qv_of_le_Gw hfr (by omega) (by omega) (pCoreOf_isPGroup 2 _) hQlew
  have hZc_norm : t.Zv c ≤ normalizer (Q : Set G) :=
    (t.Zv_le_centralizer c).trans ((Subgroup.centralizer_le hQ_Qvc).trans
      (Subgroup.centralizer_le_normalizer (Q : Set G)))
  have hZc'_norm : t.Zv c' ≤ normalizer (Q : Set G) :=
    (t.Zv_le_centralizer c').trans ((Subgroup.centralizer_le hQ_Qvc').trans
      (Subgroup.centralizer_le_normalizer (Q : Set G)))
  have hK_norm : t.K ≤ normalizer (Q : Set G) :=
    (t.K_le_Gw ε (ε + n)).trans (le_normalizer_pCoreOf 2 _)
  have hN_norm : t.Zv c ⊔ t.Zv c' ⊔ t.K ≤ normalizer (Q : Set G) :=
    sup_le (sup_le hZc_norm hZc'_norm) hK_norm
  have hyQ : Q.map (MulAut.conj y).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN_norm hyN)
  have hQ_Gwb : Q ≤ t.Gw b (ε + n) :=
    hQlew.trans (win_mono (a := ε) (b := ε + n) (a' := b) (b' := ε + n)
      (by omega) le_rfl)
  have hQ_Gw2 : Q ≤ t.Gw (2 * b - ε - n) b := by
    have h := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hQ_Gwb
    rw [hyQ, hymap b (ε + n)] at h
    have h1 : 2 * b - (ε + n) = 2 * b - ε - n := by ring
    have h2 : 2 * b - b = b := by ring
    rwa [h1, h2] at h
  have hQ_Gwc : Q ≤ t.Gw (2 * b - ε - n) (ε + n) := by
    have hwin := t.win_inf_of_le (a := 2 * b - ε - n) (b := b) (c := ε + n)
      (by omega) hbεn
    rw [← hwin]
    exact le_inf hQ_Gwb hQ_Gw2
  have hlen : (n : ℤ) < (ε + n) - (2 * b - ε - n) := by
    rw [hbdef] at *
    omega
  have hbot := h.pCoreOf_eq_bot (2 * b - ε - n) (ε + n) hlen
  have hQle : Q ≤ pCoreOf 2 (t.Gw (2 * b - ε - n) (ε + n)) :=
    t.le_pCoreOf_Gw hfr (by omega) (pCoreOf_isPGroup 2 _) hQ_Gwc
  rw [hbot] at hQle
  exact hQne (le_bot_iff.mp hQle)

theorem IsMaxArc.fixRadius_add_one
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {m b : ℕ} (h : t.IsMaxArc ε (2 * m))
    (hb : t.IsFixRadius (ε + 1) b) : b + 1 = m ∨ b = m := by
  have hle : b ≤ m := by
    have := IsFixRadius.two_mul_le t hfr h hb
    omega
  by_cases h1 : b + 1 = m
  · exact Or.inl h1
  · right
    by_contra h2
    have hlt : b + 1 < m := by omega
    refine IsMaxArc.false_of_isFixRadius t hfr h (by omega) hb ?_
    push_cast
    omega

theorem IsMaxArc.fixRadius_self
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {m b : ℕ} (h : t.IsMaxArc ε (2 * m))
    (hb : t.IsFixRadius ε b) : m ≤ b + 2 ∧ b ≤ m := by
  have hle : b ≤ m := by
    have := IsFixRadius.two_mul_le t hfr h hb
    omega
  refine ⟨?_, hle⟩
  by_contra h2
  have hlt : b + 2 < m := by omega
  have hb' : t.IsFixRadius (ε + 2) b := by simpa using IsFixRadius.shift t hb 1
  refine IsMaxArc.false_of_isFixRadius t hfr h (by omega) hb' ?_
  push_cast
  omega

end Track

end CFSG.Quasithin.Stroth.Rq

end
