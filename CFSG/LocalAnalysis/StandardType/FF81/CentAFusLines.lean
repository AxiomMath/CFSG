module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs

public section

namespace CFSG.StandardType.FF81.CentA

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt vecElt_single vecElt_single_one)
open CFSG.StandardType.FrameRoute.FS81 (IsConjLine)

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G} {z : Fin 3 → ↥L}

theorem exists_mem_zpowers_zs_of_isConj (h : GGFF.SettingCore b L z) (hout : PropTwoOut b L z)
    {x : G} (hx : x ∈ GGFF.tor (GGFF.zs z)) (hx1 : x ≠ 1) (hbx : IsConj b x) :
    ∃ i, x ∈ Subgroup.zpowers (GGFF.zs z i) := by
  classical
  set Z : Subgroup G := Subgroup.zpowers x with hZdef
  have hx3 : x ^ 3 = 1 :=
    h.isElemAbelian_Bt.2 x (GGFF.SettingCore.tor_le_Bt b z hx)
  have hZtor : Z ≤ GGFF.tor (GGFF.zs z) := by
    rw [hZdef]
    exact Subgroup.zpowers_le.mpr hx
  have hZle : Z ≤ GGFF.Bt b z := hZtor.trans (GGFF.SettingCore.tor_le_Bt b z)
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hZconj : IsConjLine b Z := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hbx
    exact ⟨g, by rw [hg, hZdef]⟩
  have hmem : Z ∈ coordLines b z ∪ weightFourLines b z := by
    rcases hout with ⟨-, hCL⟩ | ⟨-, -, hCL, -⟩
    · exact Or.inl ((hCL Z hZle hZcard).mp hZconj)
    · exact (hCL Z hZle hZcard).mp hZconj
  simp only [Set.mem_union, coordLines, weightFourLines, Set.mem_setOf_eq] at hmem
  rcases hmem with ⟨i, hi⟩ | ⟨eps, v, heps, -, hZeps⟩
  · have hxZ : x ∈ Subgroup.zpowers (xs b z i) := by
      rw [← hi]
      exact Subgroup.mem_zpowers x
    fin_cases i
    · exfalso
      have hbZ : b ∈ Z := by
        rw [hi]
        simpa [xs] using Subgroup.mem_zpowers b
      exact h.b_not_mem (GGFF.SettingCore.tor_le z (hZtor hbZ))
    · exact ⟨0, by simpa [xs] using hxZ⟩
    · exact ⟨1, by simpa [xs] using hxZ⟩
    · exact ⟨2, by simpa [xs] using hxZ⟩
  · exfalso
    have hyZ : b ^ eps.val * vecElt (GGFF.zs z) v ∈ Z := by
      rw [hZeps]
      exact Subgroup.mem_zpowers _
    have hyL : b ^ eps.val * vecElt (GGFF.zs z) v ∈ L :=
      GGFF.SettingCore.tor_le z (hZtor hyZ)
    have hvecL : vecElt (GGFF.zs z) v ∈ L :=
      GGFF.SettingCore.tor_le z (GGFF.vecElt_mem_tor (GGFF.zs z) v)
    have hbpowL : b ^ (eps.val : ℤ) ∈ L := by
      rw [zpow_natCast]
      have e : b ^ eps.val =
          (b ^ eps.val * vecElt (GGFF.zs z) v) * (vecElt (GGFF.zs z) v)⁻¹ := by
        group
      rw [e]
      exact L.mul_mem hyL (L.inv_mem hvecL)
    have hbpow1 : b ^ eps.val = 1 := by
      simpa only [zpow_natCast] using h.zpow_eq_one_of_mem hbpowL
    have hpos : 0 < eps.val := ZMod.val_pos.mpr heps
    have hlt : eps.val < 3 := ZMod.val_lt eps
    exact (pow_ne_one_of_lt_orderOf hpos.ne' (by rw [h.ord]; exact hlt)) hbpow1

private theorem cafLines_wt_single (i : Fin 3) (a : ZMod 3) (ha : a ≠ 0) :
    GGFF.wt (Pi.single i a) = 1 := by
  revert i a
  decide

private theorem cafLines_conj_single (h : GGFF.SettingCore b L z) (hout : PropTwoOut b L z)
    {x : G} (hx : x ∈ L) (hbx : IsConj b x) :
    ∃ (g : ↥L) (i : Fin 3) (a : ZMod 3), a ≠ 0 ∧
      (⟨x, hx⟩ : ↥L) = g * vecElt z (Pi.single i a) * g⁻¹ := by
  classical
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hbx
    rw [← hc, conj_pow, h.b_cube, mul_one, mul_inv_cancel]
  have hxH : (⟨x, hx⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  obtain ⟨g, v, hgv⟩ := h.model.fus ⟨x, hx⟩ hxH
  have hgvG : x = (g : G) * vecElt (GGFF.zs z) v * (g : G)⁻¹ := by
    have h := congrArg (fun y : ↥L => (y : G)) hgv
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ← GGFF.SettingCore.vecElt_zs] using h
  have hxu : IsConj (vecElt (GGFF.zs z) v) x :=
    isConj_iff.mpr ⟨(g : G), hgvG.symm⟩
  have hbu : IsConj b (vecElt (GGFF.zs z) v) := hbx.trans hxu.symm
  have hu1 : vecElt (GGFF.zs z) v ≠ 1 := by
    intro h1
    have hx1 : x = 1 := by rw [hgvG, h1]; group
    obtain ⟨c, hc⟩ := isConj_iff.mp hbx
    exact h.b_ne_one (by
      calc b = c⁻¹ * x * c := by rw [← hc]; group
        _ = 1 := by rw [hx1]; group)
  obtain ⟨i, hi⟩ :=
    exists_mem_zpowers_zs_of_isConj h hout (GGFF.vecElt_mem_tor (GGFF.zs z) v) hu1 hbu
  have hzi : GGFF.zs z i ≠ 1 := fun h1 =>
    h.model.z_ne_one i (Subtype.ext (by simpa using h1))
  have hord : orderOf (GGFF.zs z i) = 3 := orderOf_eq_prime (h.zs_pow i) hzi
  rcases GGFF.eq_or_eq_inv_of_mem_zpowers hord hi hu1 with he | he
  · refine ⟨g, i, 1, one_ne_zero, ?_⟩
    have hv1 : v = Pi.single i 1 := by
      refine GGFF.vecElt_injective h.zs_pow h.zs_comm h.inj' ?_
      rw [vecElt_single_one]
      exact he
    rw [← hv1]
    exact hgv
  · have h20 : (2 : ZMod 3) ≠ 0 := by
      intro h
      have h2 : (2 : ZMod 3).val = 2 := rfl
      rw [h, ZMod.val_zero] at h2
      omega
    refine ⟨g, i, (2 : ZMod 3), h20, ?_⟩
    have hneg : vecElt (GGFF.zs z) (Pi.single i (2 : ZMod 3)) = (GGFF.zs z i)⁻¹ := by
      rw [vecElt_single]
      exact h.zs_sq i
    have hv2 : v = Pi.single i (2 : ZMod 3) := by
      refine GGFF.vecElt_injective h.zs_pow h.zs_comm h.inj' ?_
      rw [hneg]
      exact he
    rw [← hv2]
    exact hgv

theorem exists_conj_eq_of_isConj (h : GGFF.SettingCore b L z) (hout : PropTwoOut b L z)
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) (hbx : IsConj b x) (hby : IsConj b y) :
    ∃ l ∈ L, l * x * l⁻¹ = y := by
  classical
  obtain ⟨gx, i, a, ha, hgx⟩ := cafLines_conj_single h hout hx hbx
  obtain ⟨gy, j, c, hc, hgy⟩ := cafLines_conj_single h hout hy hby
  have hza : (Pi.single i a : Fin 3 → ZMod 3) ≠ 0 :=
    fun h0 => ha (by simpa using congrFun h0 i)
  have hzc : (Pi.single j c : Fin 3 → ZMod 3) ≠ 0 :=
    fun h0 => hc (by simpa using congrFun h0 j)
  have huv : IsConj (vecElt z (Pi.single i a)) (vecElt z (Pi.single j c)) :=
    (h.model.conj_iff _ _ hza hzc).mpr
      (by rw [cafLines_wt_single i a ha, cafLines_wt_single j c hc])
  have hx' : IsConj (⟨x, hx⟩ : ↥L) (vecElt z (Pi.single i a)) :=
    IsConj.symm (isConj_iff.mpr ⟨gx, hgx.symm⟩)
  have hy' : IsConj (⟨y, hy⟩ : ↥L) (vecElt z (Pi.single j c)) :=
    IsConj.symm (isConj_iff.mpr ⟨gy, hgy.symm⟩)
  have hxy : IsConj (⟨x, hx⟩ : ↥L) (⟨y, hy⟩ : ↥L) :=
    (hx'.trans huv).trans (IsConj.symm hy')
  obtain ⟨l, hl⟩ := isConj_iff.mp hxy
  refine ⟨(l : G), l.2, ?_⟩
  have h := congrArg (fun y : ↥L => (y : G)) hl
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem isConj_zs (h : GGFF.SettingCore b L z) (hout : PropTwoOut b L z)
    (hmeet : ∃ x ∈ L, IsConj b x) (i : Fin 3) : IsConj b (GGFF.zs z i) := by
  classical
  obtain ⟨x, hx, hbx⟩ := hmeet
  obtain ⟨g, j, a, ha, hgx⟩ := cafLines_conj_single h hout hx hbx
  have hja : (Pi.single j a : Fin 3 → ZMod 3) ≠ 0 :=
    fun h0 => ha (by simpa using congrFun h0 j)
  have hi1 : (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) ≠ 0 :=
    fun h0 => (one_ne_zero : (1 : ZMod 3) ≠ 0) (by simpa using congrFun h0 i)
  have huv : IsConj (vecElt z (Pi.single j a)) (vecElt z (Pi.single i 1)) :=
    (h.model.conj_iff _ _ hja hi1).mpr
      (by rw [cafLines_wt_single j a ha, cafLines_wt_single i 1 (one_ne_zero : (1 : ZMod 3) ≠ 0)])
  have huvG : IsConj (vecElt (GGFF.zs z) (Pi.single j a))
      (vecElt (GGFF.zs z) (Pi.single i 1)) := by
    have h := MonoidHom.map_isConj (Subgroup.subtype L) huv
    simpa only [Subgroup.coe_subtype, ← GGFF.SettingCore.vecElt_zs] using h
  rw [vecElt_single_one] at huvG
  have hgxG : x = (g : G) * vecElt (GGFF.zs z) (Pi.single j a) * (g : G)⁻¹ := by
    have h := congrArg (fun y : ↥L => (y : G)) hgx
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ← GGFF.SettingCore.vecElt_zs] using h
  have hxu : IsConj (vecElt (GGFF.zs z) (Pi.single j a)) x :=
    isConj_iff.mpr ⟨(g : G), hgxG.symm⟩
  exact hbx.trans (hxu.symm.trans huvG)

end CFSG.StandardType.FF81.CentA

end
