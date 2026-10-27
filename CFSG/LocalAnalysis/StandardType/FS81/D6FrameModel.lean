module

public import CFSG.LocalAnalysis.StandardType.FS81.D6FrameAux
public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelRel
public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelTorus
public import CFSG.LocalAnalysis.StandardType.FS81.D6Plane

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld
open CFSG.SeitzReduction.OmegaPilot (plusNodeSet)

theorem support_split {Z o : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {P : Finset (Fin 6)}
    (hZ : Z ≤ Om12) (ho : o ≤ Om12) (hoR : IsRootS3Like Q12 o)
    (hoP : subCommSpace o = planeSpan P) (hP : Disjoint ({2, 3} : Finset (Fin 6)) P)
    (h₁ : ∃ W, LinearBlockStandardPair (ZMod 2) W Z (node 2))
    (h₂ : ∃ W, LinearBlockStandardPair (ZMod 2) W Z o) :
    IsHypPlane (subCommSpace Z ⊓ Y2) ∧ subCommSpace Z ≤ (subCommSpace Z ⊓ Y2) ⊔ planeSpan P := by
  obtain ⟨W₁, hW₁⟩ := h₁
  obtain ⟨W₂, hW₂⟩ := h₂
  have hW₁O : W₁ ≤ TauCeti.QuadraticMap.orthogonalGroup Q12 := by
    rw [CFSG.StandardType.linearBlockStandardPair_eq_sup hW₁]
    exact (sup_le hZ (node_le_Om12 2)).trans Om12_le_O12
  have hW₂O : W₂ ≤ TauCeti.QuadraticMap.orthogonalGroup Q12 := by
    rw [CFSG.StandardType.linearBlockStandardPair_eq_sup hW₂]
    exact (sup_le hZ ho).trans Om12_le_O12
  have hdim : Module.finrank (ZMod 2) (subCommSpace (node 2)) = 4 := by
    rw [subCommSpace_node2]
    exact finrank_Y2
  have horth : ∀ a ∈ subCommSpace (node 2), ∀ b ∈ subCommSpace o,
      QuadraticMap.polar Q12 a b = 0 := by
    rw [subCommSpace_node2, hoP]
    exact polar_Y2_disjoint hP
  have hnd : ∀ a ∈ subCommSpace (node 2),
      (∀ b ∈ subCommSpace (node 2), QuadraticMap.polar Q12 a b = 0) → a = 0 := by
    rw [subCommSpace_node2]
    exact Y2_nondeg
  obtain ⟨hdec, ⟨u, u', h1, hu, hu', huu'⟩, -⟩ :=
    subCommSpace_eq_sup_of_standardPairs nondegenerate_Q12 hW₁O hW₂O hW₁ hW₂
      (isRootS3Like_node 2) hoR hdim horth hnd
  rw [subCommSpace_node2] at hdec h1
  rw [hoP] at hdec
  refine ⟨⟨inf_le_right, u, u', h1, hu, hu', huu'⟩, ?_⟩
  calc subCommSpace Z = _ := hdec
    _ ≤ _ := sup_le_sup_left inf_le_right _

private theorem comm_n {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {m c : V12 ≃ₗ[ZMod 2] V12}
    (hm : ∀ x ∈ X, m * x = x * m) (hc : ∀ x ∈ X, c * x = x * c) :
    ∀ x ∈ X, (m * c) * x = x * (m * c) := by
  intro x hx
  rw [mul_assoc, hc x hx, ← mul_assoc, hm x hx, mul_assoc]

private theorem node2_comm {j : Fin 6} (h : (2 : Fin 6) ≠ j ∧ ¬ edgeD 6 2 j ∧ ¬ edgeD 6 j 2)
    {m : V12 ≃ₗ[ZMod 2] V12} (hm : m ∈ node 2) : ∀ x ∈ node j, m * x = x * m :=
  fun x hx => node_commute h.1 h.2.1 h.2.2 m hm x hx

private theorem flip2_comm {j : Fin 6} (h : j ≠ 1 ∧ j ≠ 3) {c : V12 ≃ₗ[ZMod 2] V12}
    (hc : c ∈ flip2) : ∀ x ∈ node j, c * x = x * c :=
  fun x hx => flip2_commute_node h.1 h.2 c hc x hx

theorem planeSpan_union_le (P P' : Finset (Fin 6)) :
    planeSpan (P ∪ P') ≤ planeSpan P ⊔ planeSpan P' := by
  classical
  intro v hv
  let v₁ : V12 := Sum.elim (fun i => if i ∈ P then v (Sum.inl i) else 0)
    (fun i => if i ∈ P then v (Sum.inr i) else 0)
  have h₁ : v₁ ∈ planeSpan P := fun i hi => by simp [v₁, hi]
  have h₂ : v - v₁ ∈ planeSpan P' := by
    intro i hi
    by_cases hiP : i ∈ P
    · simp [v₁, hiP]
    · have h := hv i (by simp [hiP, hi])
      simp [v₁, hiP, h.1, h.2]
  exact Submodule.mem_sup.mpr ⟨v₁, h₁, v - v₁, h₂, add_sub_cancel v₁ v⟩

theorem exists_Z6 {Z₄ : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hZ₄ : Z₄ ≤ Om12)
    (hp2 : ∃ W, LinearBlockStandardPair (ZMod 2) W Z₄ (node 2))
    (hp4 : ∃ W, LinearBlockStandardPair (ZMod 2) W Z₄ (node 4))
    {n n₅ n₄ γ : V12 ≃ₗ[ZMod 2] V12} (hn : n ∈ node 2) (hn₅ : n₅ ∈ node 5) (hn₄ : n₄ ∈ node 4)
    (hγ : γ ∈ flip2) (hγ1 : γ ≠ 1)
    (hg : ∀ z ∈ Z₄, (n * n₅ * n₄ * γ) * z * (n * n₅ * n₄ * γ)⁻¹ ∈ Z₄) :
    ∃ Z₆ : Subgroup (V12 ≃ₗ[ZMod 2] V12), Z₆ ≤ Om12 ∧
      (∃ W, LinearBlockStandardPair (ZMod 2) W Z₆ (node 2)) ∧
      (∃ W, LinearBlockStandardPair (ZMod 2) W flip0 Z₆) ∧
      (∀ a ∈ Z₆, ∀ c ∈ node 4, a * c = c * a) ∧ (∀ a ∈ Z₆, ∀ c ∈ node 5, a * c = c * a) ∧
      (∀ a ∈ Z₆, ∀ c ∈ Z₄, a * c = c * a) ∧
      ∃ m ∈ node 2, ∀ z ∈ Z₆,
        (wmu0 * wphi0 * m * γ) * z * (wmu0 * wphi0 * m * γ)⁻¹ ∈ Z₆ := by
  obtain ⟨hB4, hsupp4⟩ := support_split hZ₄ (node_le_Om12 4) (isRootS3Like_node 4)
    subCommSpace_node_four (by decide) hp2 hp4
  set B₄ := subCommSpace Z₄ ⊓ Y2 with hB₄
  have hsig4 : SigOf B₄ γ := by
    refine sigOf_of_normalizes hg hn hγ hγ1 fun v hv => ?_
    have hγv := mapsY2_flip2 hγ hv
    simp only [LinearEquiv.mul_apply]
    rw [fixY2_node4 hn₄ _ hγv, fixY2_node5 hn₅ _ hγv]
  obtain ⟨m, hm, c, hc, hmc⟩ := exists_map_eq_of_isHypPlane isHypPlane_planeSpan_two
    (isHypPlane_perpY2 hB4)
  have hcm : ∀ x ∈ node 2, c * x = x * c := flip2_comm (j := 2) (by decide) hc
  have hcwc : c * wc0 * c⁻¹ ∈ flip2 := flip2.mul_mem (flip2.mul_mem hc wc0_mem) (flip2.inv_mem hc)
  have hid : ∀ x ∈ node 2, (m * x * m⁻¹) * (c * wc0 * c⁻¹) * (m * c) = (m * c) * (x * wc0) := by
    intro x hx
    have h1 : c * x = x * c := hcm x hx
    have h2 : m⁻¹ * (c * wc0 * c⁻¹) = (c * wc0 * c⁻¹) * m⁻¹ :=
      (flip2_comm (j := 2) (by decide) hcwc m⁻¹ ((node 2).inv_mem hm)).symm
    calc (m * x * m⁻¹) * (c * wc0 * c⁻¹) * (m * c)
        = m * x * (m⁻¹ * (c * wc0 * c⁻¹)) * m * c := by group
      _ = m * x * ((c * wc0 * c⁻¹) * m⁻¹) * m * c := by rw [h2]
      _ = m * x * c * wc0 := by group
      _ = m * (c * x) * wc0 := by rw [h1]; group
      _ = (m * c) * (x * wc0) := by group
  have hsig' : SigOf (perpY2 B₄) (c * wc0 * c⁻¹) := by
    refine ⟨hcwc, fun h => wc0_ne_one ?_, m * wm2 * m⁻¹,
      (node 2).mul_mem ((node 2).mul_mem hm wm2_mem) ((node 2).inv_mem hm), fun v hv => ?_⟩
    · calc wc0 = c⁻¹ * (c * wc0 * c⁻¹) * c := by group
        _ = 1 := by rw [h]; group
    · rw [← hmc] at hv ⊢
      obtain ⟨w, hw, rfl⟩ := hv
      refine ⟨(wm2 * wc0) w, witness_plane w hw, ?_⟩
      change (m * c) ((wm2 * wc0) w) = (m * wm2 * m⁻¹ * (c * wc0 * c⁻¹)) ((m * c) w)
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hid wm2 wm2_mem]
  have hγc : γ = c * wc0 * c⁻¹ :=
    sigOf_unique (isHypPlane_perpY2 hB4) (sigOf_perpY2 hB4 hsig4) hsig'
  have hn₂O : m * c ∈ Om12 := Om12.mul_mem (node_le_Om12 2 hm) (flip2_le_Om12 hc)
  refine ⟨(node 1).map (MulAut.conj (m * c)).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact Om12.mul_mem (Om12.mul_mem hn₂O (node_le_Om12 1 hz)) (Om12.inv_mem hn₂O)
  · obtain ⟨W, hW⟩ := node_pair (show edgeD 6 1 2 by decide)
    have h := pair_map_conj hW (m * c)
    rw [map_conj_mul_eq hm hcm] at h
    exact ⟨_, h⟩
  · obtain ⟨W, hW⟩ := flip0_pair_node1
    have h := pair_map_conj hW (m * c)
    rw [map_conj_eq_of_commute (comm_n
      (fun x hx => (flip0_commute_node (by decide : (2 : Fin 6) ≠ 1) x hx m hm).symm)
      (fun x hx => (flip0_commute_flip2 x hx c hc).symm))] at h
    exact ⟨_, h⟩
  · exact commute_map_conj (node_commute (by decide) (by decide) (by decide))
      (comm_n (node2_comm (by decide) hm) (flip2_comm (by decide) hc))
  · exact commute_map_conj (node_commute (by decide) (by decide) (by decide))
      (comm_n (node2_comm (by decide) hm) (flip2_comm (by decide) hc))
  ·
    have hA : subCommSpace ((node 1).map (MulAut.conj (m * c)).toMonoidHom) ≤
        planeSpan {1} ⊔ perpY2 B₄ := by
      rw [subCommSpace_map_conj, subCommSpace_node_one]
      rintro _ ⟨v, hv, rfl⟩
      have hv' : v ∈ planeSpan {1} ⊔ planeSpan {2} :=
        planeSpan_union_le {1} {2} (by rwa [show ({1} : Finset (Fin 6)) ∪ {2} = {1, 2} by decide])
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv'
      have hv₁' : v₁ ∈ planeSpan ({2, 3} : Finset (Fin 6))ᶜ := planeSpan_mono (by decide) hv₁
      have hfix : (m * c) v₁ = v₁ := by
        rw [LinearEquiv.mul_apply, rootL_apply_eq_self (by decide : (2 : Fin 6) ≠ 3) hc hv₁',
          node_apply_eq_self 2 hm (by rwa [plusNodeSet_six.2.2.1])]
      change (m * c) (v₁ + v₂) ∈ _
      rw [map_add, hfix]
      exact Submodule.add_mem_sup hv₁ (hmc ▸ ⟨v₂, hv₂, rfl⟩)
    exact commute_of_polar_subCommSpace nondegenerate_Q12
      (fun z hz => Om12_le_O12 (by
        obtain ⟨y, hy, rfl⟩ := hz
        exact Om12.mul_mem (Om12.mul_mem hn₂O (node_le_Om12 1 hy)) (Om12.inv_mem hn₂O)))
      (hZ₄.trans Om12_le_O12)
      (polar_eq_zero_of_le_sup hA hsupp4
        (fun a ha b hb => polar_disjoint_Y2 (by decide) a ha b (hB4.1 hb))
        (polar_eq_zero_of_disjoint (by decide))
        polar_perpY2
        (fun a ha b hb => polar_Y2_disjoint (by decide) a (perpY2_le_Y2 _ ha) b hb))
  ·
    refine ⟨m * wm2 * m⁻¹, (node 2).mul_mem ((node 2).mul_mem hm wm2_mem) ((node 2).inv_mem hm),
      ?_⟩
    have hn0 : (m * c) * wmu0 = wmu0 * (m * c) :=
      comm_n (node2_comm (by decide) hm) (flip2_comm (by decide) hc) wmu0 wmu0_mem
    have hf0 : (m * c) * wphi0 = wphi0 * (m * c) :=
      comm_n (fun x hx => (flip0_commute_node (by decide : (2 : Fin 6) ≠ 1) x hx m hm).symm)
        (fun x hx => (flip0_commute_flip2 x hx c hc).symm) wphi0 wphi0_mem
    have hconj : wmu0 * wphi0 * (m * wm2 * m⁻¹) * γ =
        (m * c) * (wmu0 * wphi0 * wm2 * wc0) * (m * c)⁻¹ := by
      rw [hγc]
      calc wmu0 * wphi0 * (m * wm2 * m⁻¹) * (c * wc0 * c⁻¹)
          = wmu0 * wphi0 * ((m * wm2 * m⁻¹) * (c * wc0 * c⁻¹) * (m * c)) * (m * c)⁻¹ := by group
        _ = wmu0 * wphi0 * ((m * c) * (wm2 * wc0)) * (m * c)⁻¹ := by rw [hid wm2 wm2_mem]
        _ = wmu0 * (wphi0 * (m * c)) * (wm2 * wc0) * (m * c)⁻¹ := by group
        _ = wmu0 * ((m * c) * wphi0) * (wm2 * wc0) * (m * c)⁻¹ := by rw [hf0]
        _ = (wmu0 * (m * c)) * wphi0 * (wm2 * wc0) * (m * c)⁻¹ := by group
        _ = ((m * c) * wmu0) * wphi0 * (wm2 * wc0) * (m * c)⁻¹ := by rw [hn0]
        _ = (m * c) * (wmu0 * wphi0 * wm2 * wc0) * (m * c)⁻¹ := by group
    rw [hconj]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨(wmu0 * wphi0 * wm2 * wc0) * z * (wmu0 * wphi0 * wm2 * wc0)⁻¹, witness_node1 z hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_conj_commute {Z₂ Z₆ : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hZ₂ : Z₂ ≤ Om12)
    (hZ₆ : Z₆ ≤ Om12)
    (hp2 : ∃ W, LinearBlockStandardPair (ZMod 2) W Z₂ (node 2))
    (hp0 : ∃ W, LinearBlockStandardPair (ZMod 2) W Z₂ (node 0))
    (hq2 : ∃ W, LinearBlockStandardPair (ZMod 2) W Z₆ (node 2))
    (hq4 : ∃ W, LinearBlockStandardPair (ZMod 2) W Z₆ (node 4))
    {γ : V12 ≃ₗ[ZMod 2] V12} (hγ : γ ∈ flip2) (hγ1 : γ ≠ 1)
    {a₁ n₁ b₁ : V12 ≃ₗ[ZMod 2] V12} (ha₁ : a₁ ∈ node 0) (hn₁ : n₁ ∈ node 2) (hb₁ : b₁ ∈ flip0)
    (hg₁ : ∀ z ∈ Z₂, (a₁ * n₁ * b₁ * γ) * z * (a₁ * n₁ * b₁ * γ)⁻¹ ∈ Z₂)
    {a₆ n₆ b₆ : V12 ≃ₗ[ZMod 2] V12} (ha₆ : a₆ ∈ node 5) (hn₆ : n₆ ∈ node 2) (hb₆ : b₆ ∈ node 4)
    (hg₆ : ∀ z ∈ Z₆, (a₆ * n₆ * b₆ * γ) * z * (a₆ * n₆ * b₆ * γ)⁻¹ ∈ Z₆) :
    ∃ k ∈ node 2, (∀ a ∈ Z₆.map (MulAut.conj k).toMonoidHom, ∀ b ∈ Z₂, a * b = b * a) ∧
      ∀ a ∈ Z₆.map (MulAut.conj k).toMonoidHom, ∀ b ∈ node 0, a * b = b * a := by
  obtain ⟨hB2, hsupp2⟩ := support_split hZ₂ (node_le_Om12 0) (isRootS3Like_node 0)
    subCommSpace_node_zero (by decide) hp2 hp0
  obtain ⟨hB6, hsupp6⟩ := support_split hZ₆ (node_le_Om12 4) (isRootS3Like_node 4)
    subCommSpace_node_four (by decide) hq2 hq4
  have hsig2 := sigOf_of_normalizes hg₁ hn₁ hγ hγ1
    (apply_Y2_of_factors (fixY2_node0 ha₁) hn₁ (fixY2_flip0 hb₁) hγ)
  have hsig6 := sigOf_of_normalizes hg₆ hn₆ hγ hγ1
    (apply_Y2_of_factors (fixY2_node5 ha₆) hn₆ (fixY2_node4 hb₆) hγ)
  obtain ⟨k, hk, hkmap⟩ := exists_node2_map_eq_perpY2 hB6 hB2 hsig6 hsig2
  have hkO : k ∈ Om12 := node_le_Om12 2 hk
  have hZ6kO : Z₆.map (MulAut.conj k).toMonoidHom ≤ TauCeti.QuadraticMap.orthogonalGroup Q12 := by
    rintro _ ⟨z, hz, rfl⟩
    exact Om12_le_O12 (Om12.mul_mem (Om12.mul_mem hkO (hZ₆ hz)) (Om12.inv_mem hkO))
  have hA : subCommSpace (Z₆.map (MulAut.conj k).toMonoidHom) ≤
      perpY2 (subCommSpace Z₂ ⊓ Y2) ⊔ planeSpan {4, 5} := by
    rw [subCommSpace_map_conj]
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp (hsupp6 hv)
    have hfix : k v₂ = v₂ :=
      node_apply_eq_self 2 hk (by rw [plusNodeSet_six.2.2.1]; exact planeSpan_mono (by decide) hv₂)
    change k (v₁ + v₂) ∈ _
    rw [map_add, hfix]
    exact Submodule.add_mem_sup (hkmap ▸ ⟨v₁, hv₁, rfl⟩) hv₂
  refine ⟨k, hk, ?_, ?_⟩
  · exact commute_of_polar_subCommSpace nondegenerate_Q12 hZ6kO (hZ₂.trans Om12_le_O12)
      (polar_eq_zero_of_le_sup hA hsupp2 polar_perpY2
        (fun a ha b hb => polar_Y2_disjoint (by decide) a (perpY2_le_Y2 _ ha) b hb)
        (fun a ha b hb => polar_disjoint_Y2 (by decide) a ha b (hB2.1 hb))
        (polar_eq_zero_of_disjoint (by decide)))
  · refine commute_of_polar_subCommSpace nondegenerate_Q12 hZ6kO
      ((node_le_Om12 0).trans Om12_le_O12) ?_
    rw [subCommSpace_node_zero]
    exact polar_eq_zero_of_le_sup hA (le_sup_left : planeSpan {0, 1} ≤ planeSpan {0, 1} ⊔ ⊥)
      (fun a ha b hb => polar_Y2_disjoint (by decide) a (perpY2_le_Y2 _ ha) b hb)
      (fun a _ b hb => by rw [(Submodule.mem_bot _).mp hb, QuadraticMap.polar_zero_right])
      (polar_eq_zero_of_disjoint (by decide))
      (fun a _ b hb => by rw [(Submodule.mem_bot _).mp hb, QuadraticMap.polar_zero_right])

end CFSG.StandardType.FrameRoute.FS81.D6M
