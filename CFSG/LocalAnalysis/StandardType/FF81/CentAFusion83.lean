module

public import CFSG.LocalAnalysis.StandardType.FF81.CentACore
public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.LocalAnalysis.StandardType.FF81.CentAFusLines
import CFSG.LocalAnalysis.StandardType.FF81.CentAFusSyl
import CFSG.LocalAnalysis.StandardType.FF81.CentAFusCen
import CFSG.LocalAnalysis.StandardType.FF81.CentAModelEmbed
import CFSG.LocalAnalysis.StandardType.FF81.LocalSetup
import CFSG.LocalAnalysis.StandardType.FF81.LocalSetupCen

public section

namespace CFSG.StandardType.FF81.CentA

open RootFusionLin

theorem centAFus_of_afterProp2 {G : Type} [Group G] [Finite G] {n : ℕ} {b t : G}
    {L Y R : Subgroup G} {φ : ↥Y ≃* GL (BlkIdx 1 (n + 1)) (ZMod 2)} (hA : HypA G n b L)
    {z : Fin 3 → ↥L} (hP2 : AfterProp2 b L z) (hS : CentASetting (n + 1) Y L R b t φ) :
    CentAFus Y b t φ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    rcases hA.n_cases with h | h
    · exact ⟨4, by omega⟩
    · exact ⟨5, by omega⟩
  have hset : GGFF.SettingCore b L z := hA.settingCore hP2.model
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have hφt : φ ⟨t, hS.t_mem⟩ = jGL 1 (k + 2) := hS.φ_t
  have hφb : φ ⟨b, hS.b_mem⟩ = betaStd (k + 2) := hS.φ_b
  have hφL : ∀ y : ↥Y, (y : G) ∈ L ↔ φ y ∈ leviB (k + 2) := hS.φ_L
  have hLH : L ≤ H := by
    intro l hl
    change l ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlY : l ∈ Y := hS.L_le hl
    have hlevi : φ ⟨l, hlY⟩ ∈ leviB (k + 2) := (hφL ⟨l, hlY⟩).mp hl
    have hcent : φ ⟨l, hlY⟩ ∈ Cent 1 (k + 2) := leviB_le_cent (k + 2) hlevi
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hcent
    have hcomm' : φ ⟨l, hlY⟩ * φ ⟨t, hS.t_mem⟩ = φ ⟨t, hS.t_mem⟩ * φ ⟨l, hlY⟩ := by
      rw [hφt]
      exact hcomm
    have hlt : (⟨l, hlY⟩ : ↥Y) * ⟨t, hS.t_mem⟩ = ⟨t, hS.t_mem⟩ * ⟨l, hlY⟩ :=
      φ.injective (by rw [map_mul, map_mul]; exact hcomm')
    simpa using congrArg Subtype.val hlt
  let yπ : G := ((φ.symm (piStd k) : ↥Y) : G)
  let bS : G := ((φ.symm (bStar (k + 2)) : ↥Y) : G)
  have hbSeq : bS = yπ * b * yπ⁻¹ := by
    have h : φ.symm (piStd k) * φ.symm (betaStd (k + 2)) * (φ.symm (piStd k))⁻¹ =
        φ.symm (bStar (k + 2)) := by
      simpa only [map_mul, map_inv] using congrArg (fun g => φ.symm g) (piStd_conj_betaStd k)
    have hb : φ.symm (betaStd (k + 2)) = ⟨b, hS.b_mem⟩ := by
      rw [← hφb, φ.symm_apply_apply]
    simpa [bS, yπ, hb] using (congrArg (fun y : ↥Y => (y : G)) h).symm
  have hbSL : bS ∈ L := by
    have hbY : bS ∈ Y := (φ.symm (bStar (k + 2)) : ↥Y).2
    have hmem : φ ⟨bS, hbY⟩ ∈ leviB (k + 2) := by
      have e : (⟨bS, hbY⟩ : ↥Y) = φ.symm (bStar (k + 2)) := by
        ext
        rfl
      rw [e, φ.apply_symm_apply]
      exact bStar_mem_leviB (k + 2)
    simpa using (hφL ⟨bS, hbY⟩).mpr hmem
  have hbSconj : IsConj b bS := isConj_iff.mpr ⟨yπ, hbSeq.symm⟩
  have hcj : ∀ i, IsConj b (GGFF.zs z i) :=
    isConj_zs hset hP2.out ⟨bS, hbSL, hbSconj⟩
  obtain ⟨w₀, hw₀⟩ := hP2.model.mono (finRotate 3) (fun _ => 1) (by decide)
  have hw₀' : ∀ i, w₀ * z i * w₀⁻¹ = z (finRotate 3 i) := fun i => by
    have h1 : (1 : ZMod 3).val = 1 := by decide
    simpa [h1] using hw₀ i
  let w : G := (w₀ : ↥L)
  have hw : ∀ i, w * GGFF.zs z i * w⁻¹ = GGFF.zs z (finRotate 3 i) := by
    intro i
    simpa [w, GGFF.zs] using congrArg (fun y : ↥L => (y : G)) (hw₀' i)
  have hw3 : w ^ 3 ∈ GGFF.tor (GGFF.zs z) := by
    have hrot : ∀ i : Fin 3, finRotate 3 (finRotate 3 (finRotate 3 i)) = i := by decide
    have hcomm : ∀ i, (w₀ ^ 3) * z i = z i * (w₀ ^ 3) := by
      intro i
      have h : (w₀ ^ 3) * z i * (w₀ ^ 3)⁻¹ = z i := by
        calc (w₀ ^ 3) * z i * (w₀ ^ 3)⁻¹
            = w₀ * (w₀ * (w₀ * z i * w₀⁻¹) * w₀⁻¹) * w₀⁻¹ := by
                rw [pow_succ, pow_succ, pow_succ, pow_zero, one_mul]
                group
          _ = w₀ * (w₀ * z (finRotate 3 i) * w₀⁻¹) * w₀⁻¹ := by rw [hw₀' i]
          _ = w₀ * z (finRotate 3 (finRotate 3 i)) * w₀⁻¹ := by rw [hw₀' (finRotate 3 i)]
          _ = z (finRotate 3 (finRotate 3 (finRotate 3 i))) := by
              rw [hw₀' (finRotate 3 (finRotate 3 i))]
          _ = z i := by rw [hrot i]
      exact mul_inv_eq_iff_eq_mul.mp h
    obtain ⟨v, hv⟩ := cen_of_model hA.n_cases hA.model hP2.model (w₀ ^ 3) hcomm
    rw [show w ^ 3 = ((w₀ ^ 3 : ↥L) : G) by simp [w]]
    rw [hv, ← GGFF.SettingCore.vecElt_zs]
    exact GGFF.vecElt_mem_tor _ v
  have hwH : w ∈ H := hLH w₀.2
  have hyH : ∀ i, GGFF.zs z i ∈ H := fun i => hLH (GGFF.SettingCore.zs_mem z i)
  have hlines : ∀ x ∈ H, (∀ β ∈ GGFF.tor (GGFF.zs z), x * β * x⁻¹ ∈ GGFF.tor (GGFF.zs z)) →
      ∀ i, ∃ j, x * GGFF.zs z i * x⁻¹ ∈ Subgroup.zpowers (GGFF.zs z j) := by
    intro x _ hxtor i
    have hmem : x * GGFF.zs z i * x⁻¹ ∈ GGFF.tor (GGFF.zs z) :=
      hxtor _ (Subgroup.subset_closure ⟨i, rfl⟩)
    have hne : x * GGFF.zs z i * x⁻¹ ≠ 1 := by
      intro h1
      have hzi : GGFF.zs z i = 1 := by
        calc GGFF.zs z i = x⁻¹ * (x * GGFF.zs z i * x⁻¹) * x := by group
          _ = 1 := by rw [h1]; group
      exact hP2.model.z_ne_one i (Subtype.ext (by simpa [GGFF.zs] using hzi))
    have hconj : IsConj b (x * GGFF.zs z i * x⁻¹) := by
      obtain ⟨c, hc⟩ := isConj_iff.mp (hcj i)
      exact isConj_iff.mpr ⟨x * c, by rw [← hc]; group⟩
    exact exists_mem_zpowers_zs_of_isConj hset hP2.out hmem hne hconj
  have hcen : ∀ x ∈ H, (∃ k' : ℕ, x ^ 3 ^ k' = 1) →
      (∀ i, x * GGFF.zs z i = GGFF.zs z i * x) → x ∈ GGFF.tor (GGFF.zs z) := by
    intro x hxH hxk hxz
    obtain ⟨l, hlL, hl⟩ :=
      exists_conj_eq_of_isConj hset hP2.out (GGFF.SettingCore.zs_mem z 0) hbSL (hcj 0) hbSconj
    let g : G := l⁻¹ * yπ
    have hgY : g ∈ Y := Y.mul_mem (Y.inv_mem (hS.L_le hlL)) (φ.symm (piStd k)).2
    have hz0 : GGFF.zs z 0 = g * b * g⁻¹ := by
      calc GGFF.zs z 0 = l⁻¹ * (l * GGFF.zs z 0 * l⁻¹) * l := by group
        _ = l⁻¹ * bS * l := by rw [hl]
        _ = l⁻¹ * (yπ * b * yπ⁻¹) * l := by rw [hbSeq]
        _ = g * b * g⁻¹ := by simp [g]; group
    obtain ⟨k', hxk'⟩ := hxk
    have hx'b : (g⁻¹ * x * g) * b = b * (g⁻¹ * x * g) := by
      have h := hxz 0
      rw [hz0] at h
      calc (g⁻¹ * x * g) * b = g⁻¹ * (x * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * x) * g := by rw [h]
        _ = b * (g⁻¹ * x * g) := by group
    have hx'pow : (g⁻¹ * x * g) ^ 3 ^ k' = 1 := by
      rw [show g⁻¹ * x * g = (MulAut.conj g⁻¹) x by simp [MulAut.conj_apply]]
      rw [← map_pow, hxk', map_one]
    have hx'sup : g⁻¹ * x * g ∈ Subgroup.zpowers b ⊔ L :=
      mem_zpowers_sup_of_pow_eq_one hset hP2.loc
        (Subgroup.mem_centralizer_singleton_iff.mpr hx'b) hx'pow
    have hx'Y : g⁻¹ * x * g ∈ Y :=
      (sup_le (Subgroup.zpowers_le.mpr hS.b_mem) hS.L_le) hx'sup
    have hxY : x ∈ Y := by
      have hx_eq : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [hx_eq]
      exact Y.mul_mem (Y.mul_mem hgY hx'Y) (Y.inv_mem hgY)
    exact mem_tor_of_mem_centralizer hS (cen_of_model hA.n_cases hA.model hP2.model)
      hxY (Subgroup.mem_centralizer_singleton_iff.mp hxH) hxz hxk'
  have hPL : GGFF.tor (GGFF.zs z) ⊔ Subgroup.zpowers w ≤ L :=
    sup_le (GGFF.SettingCore.tor_le z) (Subgroup.zpowers_le.mpr w₀.2)
  intro g hgH
  have hck : (g * b * g⁻¹) ^ 3 ^ 1 = 1 := by
    have hc3 : (g * b * g⁻¹) ^ 3 = 1 := by
      rw [show g * b * g⁻¹ = (MulAut.conj g) b by simp [MulAut.conj_apply]]
      rw [← map_pow, hset.b_cube, map_one]
    simpa using hc3
  obtain ⟨h₁, hh₁H, hconj⟩ := exists_conj_mem_sup hset.zs_pow hset.zs_comm hset.inj'
    hw hw3 hwH hyH hlines hcen hgH (k := 1) hck
  have hcL : h₁ * (g * b * g⁻¹) * h₁⁻¹ ∈ L := hPL hconj
  have hcj' : IsConj b (h₁ * (g * b * g⁻¹) * h₁⁻¹) :=
    isConj_iff.mpr ⟨h₁ * g, by group⟩
  obtain ⟨l, hlL, hl⟩ := exists_conj_eq_of_isConj hset hP2.out hcL hbSL hcj' hbSconj
  refine ⟨l * h₁, H.mul_mem (hLH hlL) hh₁H, Or.inl ?_⟩
  calc (l * h₁) * (g * b * g⁻¹) * (l * h₁)⁻¹
      = l * (h₁ * (g * b * g⁻¹) * h₁⁻¹) * l⁻¹ := by group
    _ = bS := hl

end CFSG.StandardType.FF81.CentA

end
