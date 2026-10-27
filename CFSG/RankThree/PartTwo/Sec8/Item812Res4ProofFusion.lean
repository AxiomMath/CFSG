module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Final


open Item812Res4

@[expose] def Fin812FuseR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ P Q R V Pa : Subgroup G, Fin812Config A a X Y P Q R V Pa →
      ∀ z ∈ P, z ^ 3 = 1 → ∃ r ∈ R, r * z * r⁻¹ ∈ Pa

@[expose] def Fin812CentAx : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ P Q R V Pa : Subgroup G, Fin812Config A a X Y P Q R V Pa →
      ∀ x ∈ P ⊓ Y, x ∉ sec8B A X → x ^ 3 = 1 →
        Nat.card (P ⊓ Subgroup.centralizer {a * x} : Subgroup G) <
          Nat.card (P ⊓ Subgroup.centralizer {a} : Subgroup G)

theorem fin812FuseR_of (hW : KF812WreathCent) : Fin812FuseR := by
  intro G _ _ A c L a b X Y n h P Q R V Pa hc z hzP hz3
  have hp := pre_of_config hc
  exact exists_conj_mem_pa hW h.item89_Y hp h.mem_partTwoF.1 h.a_mem h.a_ne_one h.card_eq
    (le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y) hzP hz3

theorem fin812CentAx_of (hW : KF812WreathCent) : Fin812CentAx := by
  intro G _ _ A c L a b X Y n h P Q R V Pa hc x hxPY hxB _
  have hp := pre_of_config hc
  exact card_centralizer_mul_lt hW h.item89_Y hp h.mem_partTwoF.1 h.a_mem h.a_ne_one h.card_eq
    (le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y) hxPY hxB

theorem fin812FusionW_of (hW : KF812WreathCent) : Fin812FusionW := by
  intro G _ _ A c L a b X Y n h P Q R V Pa hc w hw
  have hp := pre_of_config hc
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have hYa := le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  have hwa : w * a * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw a).mp haA
  have hwB : w * a * w⁻¹ ∉ sec8B A X := by
    intro hB
    have hle : (sec8B A X).map (MulAut.conj w⁻¹).toMonoidHom ≤ A := by
      rintro _ ⟨x, hx, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) x).mp (b_le_a hx)
      simpa using this
    have heq := hc.b_weak w⁻¹ hle
    have haB : a ∈ sec8B A X := by
      rw [← heq]
      exact ⟨w * a * w⁻¹, hB, by simp [mul_assoc]⟩
    exact a_not_mem_b hp haB
  exact exists_conj_eq_zpow hW h.item89_Y hp hAab haA h.a_ne_one h.card_eq hYa hwa hwB

theorem fin812FusionV_of (hF : KF812E27Fuse) (hR : Fin812FuseR) : Fin812FusionV := by
  intro G _ _ A c L a b X Y n h P Q R V Pa hc z hzV hz3
  have hp := pre_of_config hc
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hYa := le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  obtain ⟨r, hr, hrz⟩ := hR G A c L a b X Y n h P Q R V Pa hc z (v_le_p hc hzV) hz3
  have hwV : r * z * r⁻¹ ∈ V :=
    V.mul_mem (V.mul_mem (r_le_v hc hr) hzV) (V.inv_mem (r_le_v hc hr))
  obtain ⟨i, y, hy, hw⟩ := exists_eq_zpow_mul_of_mem_pa hp hYa hrz
  have hyV : y ∈ V := p_inf_y_le_v hc ⟨pa_le_p hp hy.1, hy.2⟩
  have haiV : a ^ i ∈ V := by
    have e : a ^ i = r * z * r⁻¹ * y⁻¹ := by rw [hw]; group
    rw [e]
    exact V.mul_mem hwV (V.inv_mem hyV)
  rw [zpow_eq_one_of_mem ha3 (a_not_mem_v hc) haiV, one_mul] at hw
  have hy3 : y ^ 3 = 1 := by
    rw [← hw, conj_pow, hz3]
    group
  obtain ⟨g, -, hg⟩ := exists_conj_mem_of_fuse hF h.item89_Y (b_le_y hp)
    (isElemAbelian_of_le hAab b_le_a) (card_b hp hAab haA h.a_ne_one h.card_eq) hy.2 hy3
  refine ⟨g * r, ?_⟩
  have e : g * r * z * (g * r)⁻¹ = g * (r * z * r⁻¹) * g⁻¹ := by group
  rw [e, hw]
  exact hg

theorem fin812Extremal_of (hW : KF812WreathCent) (hR : Fin812FuseR) (hA : Fin812CentAx) :
    Fin812Extremal := by
  intro G _ _ A c L a b X Y n h P Q R V Pa hc z hzP hz3 hzV
  have hp := pre_of_config hc
  have hAab := h.mem_partTwoF.1
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hYa := le_centralizer_of_mem_thetaComponentsAt_three h.mem_thetaComponentsAt_Y
  obtain ⟨r, hr, hrz⟩ := hR G A c L a b X Y n h P Q R V Pa hc z hzP hz3
  obtain ⟨i, y, hy, hw⟩ := exists_eq_zpow_mul_of_mem_pa hp hYa hrz
  have hyPY : y ∈ P ⊓ Y := ⟨pa_le_p hp hy.1, hy.2⟩
  have hwV : r * z * r⁻¹ ∉ V := by
    intro h'
    apply hzV
    have e : z = r⁻¹ * (r * z * r⁻¹) * r := by group
    rw [e]
    exact V.mul_mem (V.mul_mem (V.inv_mem (r_le_v hc hr)) h') (r_le_v hc hr)
  have hya : Commute a y :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hYa hy.2)).symm
  have hy3 : y ^ 3 = 1 := by
    have h1 : (r * z * r⁻¹) ^ 3 = 1 := by
      rw [conj_pow, hz3]
      group
    rw [hw, (Commute.zpow_left hya i).mul_pow] at h1
    have h2 : (a ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
    rwa [h2, one_mul] at h1
  have hcaseB : y ∈ sec8B A X → r * z * r⁻¹ ∈ A → ∃ s ∈ R,
      s * z * s⁻¹ ∈ Subgroup.zpowers a ∨
        ∃ x ∈ P ⊓ Y, x ∉ sec8B A X ∧ x ^ 3 = 1 ∧
          Subgroup.zpowers (s * z * s⁻¹) = Subgroup.zpowers (a * x) ∧
          Nat.card (P ⊓ Subgroup.centralizer {a * x} : Subgroup G) <
            Nat.card (P ⊓ Subgroup.centralizer {a} : Subgroup G) := by
    intro _ hwA
    have hwB : r * z * r⁻¹ ∉ sec8B A X := fun hB => hwV (r_le_v hc (hc.b_le_r hB))
    obtain ⟨s, hs, k, hsk⟩ := exists_conj_eq_zpow hW h.item89_Y hp hAab haA h.a_ne_one
      h.card_eq hYa hwA hwB
    refine ⟨s⁻¹ * r, R.mul_mem (R.inv_mem hs) hr, Or.inl ?_⟩
    have e : s⁻¹ * r * z * (s⁻¹ * r)⁻¹ = s⁻¹ * (r * z * r⁻¹) * s := by group
    rw [e, hsk]
    have e' : s⁻¹ * (s * a ^ k * s⁻¹) * s = a ^ k := by group
    rw [e']
    exact Subgroup.zpow_mem_zpowers a k
  have hk : a ^ i = a ^ (i % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv i 3, zpow_add, zpow_mul]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ha3, one_zpow, mul_one]
  rw [hk] at hw
  obtain h0 | h1 | h2 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  · rw [h0, zpow_zero, one_mul] at hw
    exact absurd (hw ▸ p_inf_y_le_v hc hyPY) hwV
  · rw [h1, zpow_one] at hw
    by_cases hyB : y ∈ sec8B A X
    · exact hcaseB hyB (hw ▸ A.mul_mem haA (b_le_a hyB))
    · exact ⟨r, hr, Or.inr ⟨y, hyPY, hyB, hy3, by rw [hw],
        hA G A c L a b X Y n h P Q R V Pa hc y hyPY hyB hy3⟩⟩
  · rw [h2] at hw
    by_cases hyB : y ∈ sec8B A X
    · exact hcaseB hyB (hw ▸ A.mul_mem (A.zpow_mem haA 2) (b_le_a hyB))
    · have hyPY' : y⁻¹ ∈ P ⊓ Y := (P ⊓ Y).inv_mem hyPY
      have hyB' : y⁻¹ ∉ sec8B A X := fun h' => hyB (by simpa using (sec8B A X).inv_mem h')
      have hy3' : y⁻¹ ^ 3 = 1 := by rw [inv_pow, hy3, inv_one]
      refine ⟨r, hr, Or.inr ⟨y⁻¹, hyPY', hyB', hy3', ?_,
        hA G A c L a b X Y n h P Q R V Pa hc y⁻¹ hyPY' hyB' hy3'⟩⟩
      have e : a * y⁻¹ = (a ^ (2 : ℤ) * y)⁻¹ := by
        have hya' : a * y⁻¹ = y⁻¹ * a := hya.inv_right.eq
        have ha2 : (a ^ (2 : ℤ))⁻¹ = a := by
          have e2 : (a ^ (2 : ℤ))⁻¹ = a * (a ^ 3)⁻¹ := by group
          rw [e2, ha3, inv_one, mul_one]
        rw [mul_inv_rev, ha2, hya']
      rw [hw, e, Subgroup.zpowers_inv]

theorem fin812FusionV_of_kf (hF : KF812E27Fuse) (hW : KF812WreathCent) : Fin812FusionV :=
  fin812FusionV_of hF (fin812FuseR_of hW)

theorem fin812Extremal_of_kf (hW : KF812WreathCent) : Fin812Extremal :=
  fin812Extremal_of hW (fin812FuseR_of hW) (fin812CentAx_of hW)

end Final

end CFSG.RankThree.PartTwo.Sec8
