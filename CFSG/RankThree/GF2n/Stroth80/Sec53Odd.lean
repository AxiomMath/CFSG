module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SpConsumers

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix


theorem stroth53Odd_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t → Odd n := by
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane
  classical
  have hrM : r ∈ M := hc.Rt_le_M t hr
  obtain ⟨K, fK, finK, hK, m, hm, φ, u, u', hφ, hker, hact, huu', hL, hL'⟩ :=
    sec5NatPointsSp_of h34 hRoot G M Q Z B hc n t hs hsp r hr hplane
  letI := fK
  letI := finK
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hu0 : u ≠ 0 := fun h0 => huu' (by simp [h0])
  obtain ⟨-, hLL', hcen, hdec⟩ := h51 G M Q Z B hc n t hs (Or.inl hsp) r hr hplane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (hc.CN t) (Rt M (LB M Q B) t)
    rfl rfl rfl rfl rfl
  have hLeR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'eR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hr
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hL'
  have hNinv : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ hc.CN t, ρ * x * ρ⁻¹ ∈ hc.CN t :=
    fun ρ hρ x hx => hc.CN_conj_mem hs.mem hρ hx
  have hQ12 : Q ≤ LB M Q B ⊓ LB M Q (conjSubgroup r B) :=
    le_inf sec39_Q_le_LB sec39_Q_le_LB
  have hIinv : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B),
      ρ * x * ρ⁻¹ ∈ LB M Q B ⊓ LB M Q (conjSubgroup r B) := by
    intro ρ hρ x hx
    have e : ρ * x * ρ⁻¹ = ⁅ρ, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (LB M Q B ⊓ LB M Q (conjSubgroup r B)).mul_mem (hQ12 (hcen ρ hρ x hx)) hx
  obtain ⟨a, ha⟩ := stroth_2_1_ii_secSp (m := m) (by omega) φ hφ hker hNinv hIinv
    hdec.2.2.2.2.2.2.1 hdec hLeR hL'eR huu' hL hL2
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hcard1 := card_mul_card_isOppDecomp hdec
  have hNnorm : r ∈ Subgroup.normalizer ((hc.CN t : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun x hx => hc.CN_conj_mem hs.mem hr hx
  have hconj : LB M Q (conjSubgroup r B) ⊓ hc.CN t = conjSubgroup r (LB M Q B ⊓ hc.CN t) := by
    rw [conjSubgroup_inf, ← hc.LB_conj hrM, conjSubgroup_eq_self_iff.mpr hNnorm]
  have hcard2 : Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) =
      Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
    rw [hconj]
    exact card_conjSubgroup r _
  have hcard3 := card_inf_mul_card_map hLeR φ hker
  rw [hL, card_LspGL hu0, hK] at hcard3
  have hL35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.2.1
  rw [hL35] at hcard3
  rw [hcard2, hLL'] at hcard1
  rw [hLL', hK] at ha
  set y := Nat.card ↥(LB M Q B ⊓ hc.CN t) with hy
  set q := Nat.card Z with hq
  set P := Nat.card Q with hP
  have hPpos : 0 < P := Nat.card_pos
  have hqpos : 0 < q := by omega
  have hn3 := hs.n_gt
  have hm2 := hm
  have h5 : Nat.card ↥(hc.CN t) * (P * q * q ^ (2 * (2 * m - 1))) =
      P ^ 2 * q ^ (2 * (n - 1)) := by
    calc Nat.card ↥(hc.CN t) * (P * q * q ^ (2 * (2 * m - 1)))
        = (Nat.card ↥(hc.CN t) * (P * q)) * q ^ (2 * (2 * m - 1)) := by ring
      _ = (y * y) * q ^ (2 * (2 * m - 1)) := by rw [hcard1]
      _ = (y * q ^ (2 * m - 1)) ^ 2 := by ring
      _ = (P * q ^ (n - 1)) ^ 2 := by rw [hcard3]
      _ = P ^ 2 * q ^ (2 * (n - 1)) := by ring
  rw [ha] at h5
  have h6 : P ^ 2 * q ^ (2 ^ m * a + 4 * m) = P ^ 2 * q ^ (2 * (n - 1)) := by
    rw [← h5]
    have h7 : 2 * (2 * m - 1) + 2 = 4 * m := by omega
    calc P ^ 2 * q ^ (2 ^ m * a + 4 * m)
        = (P * q * q ^ (2 ^ m * a)) * (P * q * q ^ (2 * (2 * m - 1))) := by
          rw [show 2 ^ m * a + 4 * m = (2 ^ m * a) + (2 * (2 * m - 1) + 2) by omega]
          ring
      _ = _ := rfl
  have h8 := Nat.pow_right_injective hq2
    (Nat.eq_of_mul_eq_mul_left (pow_pos hPpos 2) h6)
  have h4 : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h4] at h8
  have h9 : 4 * 2 ^ (m - 2) * a = 4 * (2 ^ (m - 2) * a) := by ring
  rw [h9] at h8
  exact ⟨2 ^ (m - 2) * a + m, by omega⟩

end CFSG.RankThree.GF2n.Stroth80
