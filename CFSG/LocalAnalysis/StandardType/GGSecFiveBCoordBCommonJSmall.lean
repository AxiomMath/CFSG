module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJLink
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJLift
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeConj
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace CommonJ

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {R : Type} [Group R] {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {γ : ↥Bs →* R}

theorem not_largeEvenSmall_J (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) {m : ℕ} (hm : 3 ≤ m)
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (i0 : Fin (m + 1))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (m + 1) p i0)
    {H : Type} [Group H] (e : R ≃* H) (hsp : GGSecFiveBNativeSparseRow H p m) (hp3 : p = 3) :
    ¬ LargeEvenSmall J := by
  obtain ⟨hp, hBs, hxBs, hLx, h4⟩ := hcfg.tableB_facts
  let j : Fin (m + 1) := i0.succAbove ⟨0, by omega⟩
  let z₁ : ↥Bs := eta.symm (Pi.mulSingle j (Multiplicative.ofAdd 1))
  have hjne : j ≠ i0 := by
    simp [j]
  have hz₁j : eta z₁ j = Multiplicative.ofAdd 1 := by
    simp [z₁]
  have hz₁eq : eta z₁ =
      (Pi.mulSingle j (Multiplicative.ofAdd 1) : Fin (m + 1) → Multiplicative (ZMod p)) := by
    simp [z₁]
  have hz₁i0 : eta z₁ i0 = 1 := by
    rw [hz₁eq]
    simp [Pi.mulSingle, Function.update]
    intro h
    exact (hjne h.symm).elim
  have hz₁ne1 : z₁ ≠ 1 := by
    intro h
    have h1 : eta z₁ j = 1 := by rw [h]; simp
    rw [hz₁j] at h1
    have h1' : Multiplicative.ofAdd ((1 : ℕ) : ZMod p) = 1 := by simpa using h1
    have h2 : ((1 : ℕ) : ZMod p) = 0 := ofAdd_eq_one.mp h1'
    have h3 : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp h2
    exact hp.ne_one (Nat.dvd_one.mp h3)
  let xb : ↥Bs := ⟨x, hxBs⟩
  have hηxbj : eta xb j = 1 := eta_x_eq_one hcfg hB eta i0 hA xb rfl hjne
  have hz₁_not_mem : (z₁ : G) ∉ Subgroup.zpowers x := by
    intro h
    rw [Subgroup.mem_zpowers_iff] at h
    obtain ⟨k, hk⟩ := h
    have hk' : z₁ = xb ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa using hk.symm
    have h1 : eta z₁ j = 1 := by
      rw [hk']
      simp [hηxbj]
    rw [hz₁j] at h1
    have h1' : Multiplicative.ofAdd ((1 : ℕ) : ZMod p) = 1 := by simpa using h1
    have h2 : ((1 : ℕ) : ZMod p) = 0 := ofAdd_eq_one.mp h1'
    have h3 : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp h2
    exact hp.ne_one (Nat.dvd_one.mp h3)
  have hz₁_sparse : GGCoordSparse fun j' => eta z₁ (i0.succAbove j') := by
    refine ⟨⟨0, by omega⟩, ?_⟩
    intro j' hj'
    rw [hz₁eq]
    simp [Pi.mulSingle, Function.update]
    intro h
    have h' : i0.succAbove (⟨0, by omega⟩ : Fin m) = i0.succAbove j' := by
      simpa [j] using h.symm
    exact (hj' (Fin.succAbove_right_injective h').symm).elim
  let T : Subgroup H := γ.range.map e.toMonoidHom
  have hT_elem : IsElemAbelian p T := by
    have hTop : IsElemAbelian p (⊤ : Subgroup ↥Bs) := by
      simpa using CFSG.Open.IsElemAbelian.subgroupOf hBs Bs
    have hRange : IsElemAbelian p γ.range := by
      have h := CFSG.Open.IsElemAbelian.map hTop γ
      rwa [Subgroup.map_top] at h
    simpa [T] using CFSG.Open.IsElemAbelian.map hRange e.toMonoidHom
  have hTcard : Nat.card T = p ^ m := by
    rw [show T = γ.range.map e.toMonoidHom from rfl]
    rw [Subgroup.card_map_of_injective e.injective]
    simpa using card_range_gammaHat hcfg hB hBsN hR hγ eta
  obtain ⟨Θ, hΘ, hsparse_clause⟩ := hsp T hT_elem hTcard
  let t : ↥T := ⟨e (γ z₁),
    Subgroup.mem_map_of_mem e.toMonoidHom (MonoidHom.mem_range.mpr ⟨z₁, rfl⟩)⟩
  have ht_ne1 : t ≠ 1 := by
    intro h
    have h1 : e (γ z₁) = 1 := congrArg Subtype.val h
    have h2 : γ z₁ = 1 := e.injective (by simpa using h1)
    exact hz₁_not_mem ((gammaHat_eq_one_iff hcfg hB hBsN hR hγ z₁).mp h2)
  have hsparse_t : GGCoordSparse (Θ.symm t) := by
    have h := (ggCoord_iff_of_signedCoords hcfg hB hBsN hR hγ hm eta i0 hA e hΘ z₁ t rfl).2
    exact h.mpr hz₁_sparse
  obtain ⟨K, hK, hKuniq, hKT, h7K⟩ := hsparse_clause t ht_ne1 hsparse_t
  let K_R : Subgroup R := K.map e.symm.toMonoidHom
  have hK_R : CFSG.Assembly.IsComponentOf K_R (Subgroup.centralizer ({γ z₁} : Set R)) := by
    have h := isComponentOf_map_mulEquiv e.symm (isComponentOf_iff_open.mp hK)
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e.symm ({e (γ z₁)} : Set H)] at h
    simp only [Set.image_singleton, MulEquiv.symm_apply_apply, K_R, MulEquiv.coe_toMonoidHom] at h
    exact isComponentOf_iff_open.mpr h
  have hK_R_uniq : ∀ K'_R : Subgroup R,
      CFSG.Assembly.IsComponentOf K'_R (Subgroup.centralizer ({γ z₁} : Set R)) → K'_R = K_R := by
    intro K'_R hK'_R
    have hK' : CFSG.Assembly.IsComponentOf (K'_R.map e.toMonoidHom)
        (Subgroup.centralizer ({(t : H)} : Set H)) := by
      have h := isComponentOf_map_mulEquiv e (isComponentOf_iff_open.mp hK'_R)
      rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e ({γ z₁} : Set R)] at h
      exact isComponentOf_iff_open.mpr (by simpa [t] using h)
    have h_eq : K'_R.map e.toMonoidHom = K := hKuniq _ hK'
    have h_map : K'_R = K.map e.symm.toMonoidHom := by
      have h := congrArg (Subgroup.map e.symm.toMonoidHom) h_eq
      simpa [Subgroup.map_map] using h
    simpa [K_R] using h_map
  have hKT_R : γ.range ⊓ Subgroup.centralizer (K_R : Set R) = Subgroup.zpowers (γ z₁) := by
    have h := congrArg (Subgroup.map e.symm.toMonoidHom) hKT
    rw [Subgroup.map_inf _ _ _ e.symm.injective] at h
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id R := by
      ext x
      simp
    simp only [T, Subgroup.map_map, hcomp, Subgroup.map_id] at h
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv e.symm (↑K : Set H)] at h
    rw [MonoidHom.map_zpowers] at h
    simpa [K_R, t] using h
  have h7K_R : 7 ∣ Nat.card K_R := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact h7K
  obtain ⟨K₁, hK₁_pre, hK₁_le, hK₁_map⟩ :=
    exists_stdSubPre_of_component hcfg hB hBsN hR hγ hz₁_not_mem hK_R hK_R_uniq hKT_R
  have h7K₁ : 7 ∣ Nat.card K₁ := by
    have hcard : Nat.card ((K₁.subgroupOf L).map (ggQuotHom θ)) ∣ Nat.card K₁ := by
      have h1 : Nat.card ((K₁.subgroupOf L).map (ggQuotHom θ)) ∣ Nat.card (K₁.subgroupOf L) :=
        Subgroup.card_map_dvd _ _
      have h2 : Nat.card (K₁.subgroupOf L) = Nat.card K₁ :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₁_le).toEquiv
      rwa [h2] at h1
    rw [← hK₁_map] at h7K_R
    exact h7K_R.trans hcard
  have hnotsmall_K₁ : ¬ LargeEvenSmall K₁ :=
    CFSG.StandardType.IOneOrthEnd.not_largeEvenSmall_of_seven_dvd h7K₁
  exact hcfg.2.2.2 ⟨hp3, ⟨Subgroup.closure {x, (z₁ : G)}, K₁, hK₁_pre, hnotsmall_K₁⟩⟩

end CommonJ

end CFSG.StandardType

end
