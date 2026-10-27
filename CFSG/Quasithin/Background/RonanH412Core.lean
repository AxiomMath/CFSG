module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrWreath

public section

namespace CFSG.Quasithin.RonanH412

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr CFSG.Quasithin.RonanH49
open scoped Matrix

theorem scenMat_mem_P1 (x y : ZMod 2) :
    scenMat x y 1 0 = 0 ∧ scenMat x y 2 0 = 0 ∧ scenMat x y 0 0 = 1 := by
  revert x y
  decide

theorem Scen_le_P1 : Scen ≤ P1 := by
  rintro s ⟨x, y, h⟩
  change mat s *ᵥ e0 = e0
  rw [mulVec_e0_iff, h]
  exact scenMat_mem_P1 x y

theorem conj_mem_Scen_aux {a s : ↥SL32} (ha : a ∈ P1) (hs : s ∈ Scen) :
    a * s * a⁻¹ ∈ Scen := by
  let a' : ↥P1 := ⟨a, ha⟩
  let s' : ↥P1 := ⟨s, Scen_le_P1 hs⟩
  have h1 : sigP1 s' = 1 := (sigP1_eq_one_iff s').2 hs
  have h2 : sigP1 (a' * s' * a'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
  exact (sigP1_eq_one_iff _).1 h2

theorem Scen_comm_aux {a b : ↥SL32} (ha : a ∈ Scen) (hb : b ∈ Scen) : a * b = b * a := by
  obtain ⟨x, y, hx⟩ := ha
  obtain ⟨x', y', hx'⟩ := hb
  apply eq_of_mat_eq
  rw [mat_mul, mat_mul, hx, hx', scenMat_mul, scenMat_mul, add_comm x x', add_comm y y']

theorem card_Scen_aux : Nat.card ↥Scen = 4 := by
  have h : Nat.card ↥Scen = Nat.card {a : ↥SL32 // ∃ x y : ZMod 2, mat a = scenMat x y} := rfl
  rw [h]
  exact (card_SL32_subtype (fun M => ∃ x y : ZMod 2, M = scenMat x y)).trans
    (by decide +kernel)

theorem Shat_le_stabE : Shat ≤ stabE := fun _ hs =>
  mem_stabE_iff.2 ⟨img_le_norm (Shat_le_img hs), Shat_fix_E00 hs⟩

theorem ronanH412_isPGroup_two {G : Type*} [Group G] {K : Subgroup G}
    (h : ∀ x ∈ K, x * x = 1) : IsPGroup 2 K := by
  intro g
  refine ⟨1, ?_⟩
  show g ^ 2 = 1
  rw [pow_two]
  exact Subtype.ext (h g g.2)

theorem fixed_free_aux : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), ∀ x y : ZMod 2,
    M *ᵥ e0 = e0 → M * M * M = 1 → M ≠ 1 → M * scenMat x y = scenMat x y * M →
      x = 0 ∧ y = 0 := by
  decide +kernel

theorem conj_mem_Shat {p : MulAut WMod} (hp : p ∈ stabE) {s : MulAut WMod} (hs : s ∈ Shat) :
    p * s * p⁻¹ ∈ Shat := by
  obtain ⟨hpn, hpE⟩ := mem_stabE_iff.1 hp
  obtain ⟨⟨s1, s2⟩, ⟨hs1, hs2⟩, rfl⟩ := hs
  obtain ⟨⟨a, b⟩, rfl | rfl⟩ := mem_norm_iff.1 hpn
  · obtain ⟨ha, hb⟩ := mem_P1_of_rho_E00 hpE
    rw [← rho_conj a b s1 s2]
    exact rho_mem_Shat (conj_mem_Scen_aux ha hs1) (conj_mem_Scen_aux hb hs2)
  · have hpE' : rho (a, b) (eW 0 0) = eW 0 0 := by
      rw [MulAut.mul_apply, tau_eW_diag] at hpE
      exact hpE
    obtain ⟨ha, hb⟩ := mem_P1_of_rho_E00 hpE'
    have h := tau_conj_rho (s1, s2)
    rw [Prod.swap_prod_mk] at h
    have e : rho (a, b) * tau * rho (s1, s2) * (rho (a, b) * tau)⁻¹ =
        rho (a, b) * (tau * rho (s1, s2) * tau⁻¹) * (rho (a, b))⁻¹ := by
      group
    rw [e, h, ← rho_conj a b s2 s1]
    exact rho_mem_Shat (conj_mem_Scen_aux ha hs2) (conj_mem_Scen_aux hb hs1)

theorem Shat_comm {s t : MulAut WMod} (hs : s ∈ Shat) (ht : t ∈ Shat) : s * t = t * s := by
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hs
  obtain ⟨⟨c, d⟩, ⟨hc, hd⟩, rfl⟩ := ht
  rw [← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (Scen_comm_aux ha hc) (Scen_comm_aux hb hd)

theorem card_Shat : Nat.card ↥Shat = 16 := by
  unfold Shat
  rw [Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_Scen_aux] <;>
    norm_num

theorem pCoreOf_stabE : CFSG.Open.pCoreOf 2 stabE = Shat := by
  apply le_antisymm
  ·
    have hPc : IsPGroup 2 (CFSG.pCore 2 ↥stabE) := CFSG.pCore_isPGroup
    have hNc : (CFSG.pCore 2 ↥stabE).Normal := CFSG.pCore_normal
    have hKst : (CFSG.pCore 2 ↥stabE).map stabE.subtype ≤ stabE := by
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hKE : ∀ p ∈ (CFSG.pCore 2 ↥stabE).map stabE.subtype, p (eW 0 0) = eW 0 0 :=
      fun p hp => (mem_stabE_iff.1 (hKst hp)).2
    have hconj : ∀ c : ↥stabE, ∀ p ∈ (CFSG.pCore 2 ↥stabE).map stabE.subtype,
        (c : MulAut WMod) * p * (c : MulAut WMod)⁻¹ ∈
          (CFSG.pCore 2 ↥stabE).map stabE.subtype := by
      rintro c p ⟨y, hy, rfl⟩
      exact Subgroup.mem_map.2 ⟨c * y * c⁻¹, hNc.conj_mem y hy c, rfl⟩
    have hc1 : rho (c3, 1) ∈ stabE :=
      mem_stabE_iff.2 ⟨img_le_norm (rho_mem_img _), rho_fix_E00 c3_mem_P1 P1.one_mem⟩
    have hc2 : rho (1, c3) ∈ stabE :=
      mem_stabE_iff.2 ⟨img_le_norm (rho_mem_img _), rho_fix_E00 P1.one_mem c3_mem_P1⟩
    exact le_Shat_of_normalized (hKst.trans stabE_le_norm) (hPc.map stabE.subtype) hKE
      (fun p hp => hconj ⟨rho (c3, 1), hc1⟩ p hp) (fun p hp => hconj ⟨rho (1, c3), hc2⟩ p hp)
  ·
    have hNmap : (Shat.subgroupOf stabE).map stabE.subtype = Shat :=
      Subgroup.map_subgroupOf_eq_of_le Shat_le_stabE
    have hNn : (Shat.subgroupOf stabE).Normal := ⟨fun n hn g =>
      Subgroup.mem_subgroupOf.2 (conj_mem_Shat g.2 (Subgroup.mem_subgroupOf.1 hn))⟩
    have hNp : IsPGroup 2 (Shat.subgroupOf stabE) := ronanH412_isPGroup_two (fun x hx =>
      Subtype.ext (mul_self_eq_one_of_mem_Shat (Subgroup.mem_subgroupOf.1 hx)))
    have hNle : Shat.subgroupOf stabE ≤ CFSG.pCore 2 ↥stabE := by
      unfold CFSG.pCore
      exact le_sSup ⟨hNn, hNp⟩
    exact hNmap.symm.le.trans (Subgroup.map_mono hNle)

theorem Shat_fixed_trivial {a b : ↥SL32} (ha : a ∈ P1) (hb : b ∈ P1) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) {s : MulAut WMod} (hs : s ∈ Shat)
    (hfix : rho (a, b) * s * (rho (a, b))⁻¹ = s) : s = 1 := by
  obtain ⟨⟨s1, s2⟩, ⟨hs1, hs2⟩, rfl⟩ := hs
  rw [← rho_conj a b s1 s2] at hfix
  have hp := rho_injective hfix
  have h1 : a * s1 * a⁻¹ = s1 := congrArg Prod.fst hp
  have h2 : b * s2 * b⁻¹ = s2 := congrArg Prod.snd hp
  obtain ⟨x1, y1, hx1⟩ := hs1
  obtain ⟨x2, y2, hx2⟩ := hs2
  have hA : mat a * scenMat x1 y1 = scenMat x1 y1 * mat a := by
    rw [← hx1, ← mat_mul, ← mat_mul, mul_inv_eq_iff_eq_mul.1 h1]
  have hB : mat b * scenMat x2 y2 = scenMat x2 y2 * mat b := by
    rw [← hx2, ← mat_mul, ← mat_mul, mul_inv_eq_iff_eq_mul.1 h2]
  have ha' : mat a *ᵥ e0 = e0 := ha
  have hb' : mat b *ᵥ e0 = e0 := hb
  have ha3' : mat a * mat a * mat a = 1 := by
    rw [← mat_mul, ← mat_mul, ← pow_three', ha3, mat_one]
  have hb3' : mat b * mat b * mat b = 1 := by
    rw [← mat_mul, ← mat_mul, ← pow_three', hb3, mat_one]
  have ea := fixed_free_aux (mat a) x1 y1 ha' ha3' (mat_ne_one ha1) hA
  have eb := fixed_free_aux (mat b) x2 y2 hb' hb3' (mat_ne_one hb1) hB
  have e1 : s1 = 1 := eq_of_mat_eq (by rw [mat_one, hx1, ea.1, ea.2, scenMat_zero])
  have e2 : s2 = 1 := eq_of_mat_eq (by rw [mat_one, hx2, eb.1, eb.2, scenMat_zero])
  subst e1
  subst e2
  exact map_one rho

end CFSG.Quasithin.RonanH412
