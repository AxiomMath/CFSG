module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDD9
public import CFSG.Milestones.ASVolI.C61.PAppDD8

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.burnsideC56_P.AppC
open CFSG.QuasithinUnique.AppC hiding Cfg Cfg.D_le_Q Cfg.Q_comm_U Cfg.Q_eq Cfg.S_le_N_D
  Cfg.UD_unique Cfg.U_comm_D Cfg.U_inf_D Cfg.aU_spec Cfg.blockU_le_baum Cfg.card_Q Cfg.card_U
  Cfg.conj_mem_blockD Cfg.exists_UD Cfg.hL Cfg.hQ Cfg.hQS Cfg.hSH Cfg.hSN Cfg.hU Cfg.hUQ Cfg.hUS
  Cfg.im_le_Dstd Cfg.mem_Q_iff Cfg.mem_Q_of_pf_eq_one Cfg.omegaOneCenter_le_pCoreOf
  Cfg.pf_eq_one_of_mem_Q Mate.B_eq Mate.B_eq_sup Mate.B_le_sup Mate.D_comm_V Mate.D_elem
  Mate.D_inf_conj Mate.D_le_B Mate.D_le_K Mate.D_le_of_isMax Mate.G_spec Mate.J_eq_B Mate.Q_elem
  Mate.Q_isMax Mate.Q_le_B Mate.Qx_isMax Mate.S_le_N_V Mate.V_comm Mate.V_conj Mate.V_elem
  Mate.V_inf_Q_le_U Mate.V_le_B Mate.V_le_S Mate.V_not_le_Q Mate.V_sq Mate.X'_spec Mate.Yv_isMax
  Mate.Yv_le Mate.baumD_eq Mate.card_V Mate.card_eq_Q Mate.card_symm Mate.cent_U_V Mate.conj_K
  Mate.eq_Q_of_type_bot Mate.eq_Yv_of_type_t1 Mate.exists_vud Mate.fixU_le_of_isMax Mate.fix_mem
  Mate.im_V Mate.pf_ne_one Mate.sqSub_D Mate.sqSub_K Mate.type_cases a5_core a5_core_std
  blockD_le_pCoreOf blockQ_comm_pCoreOf blockU_inf_blockD card_im_S exists_mem_thompsonJ_pi_ne_one
  exists_split exists_split' nonempty_cfg pCoreOf_comm_blockU pCoreOf_eq_blockU_sup_blockD
  swapGen_imJ

variable {G : Type} [Group G] [Finite G]

namespace GMate
open CFSG.QuasithinUnique.AppD.GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)
include C m

theorem card_S_eq : Nat.card S = 2 * Nat.card (baum S) := by
  have hQB := GMate.Q_le_B (m := m) C
  have hBS : baum S ≤ S := inf_le_left
  have hQC : pCoreOf 2 H ≤ Subgroup.centralizer (C.U : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U hq hu).symm
  have hinf : ∀ K : Subgroup G, K ≤ S → pCoreOf 2 H ≤ K →
      K ⊓ Subgroup.centralizer (C.U : Set G) = pCoreOf 2 H := fun K hKS hQK =>
    le_antisymm (fun a ha => by rw [← C.hQ]; exact ⟨C.hSH (hKS ha.1), ha.2⟩) (le_inf hQK hQC)
  have h1 := C.P.card_im_mul (A := S) le_rfl
  have h2 := C.P.card_im_mul (A := baum S) (hBS)
  rw [C.hS, Dstd_card, hinf S le_rfl C.hQS] at h1
  rw [C.hB, Estd_card, hinf (baum S) hBS hQB] at h2
  omega

theorem card_Γ_ge (hT : IsPGroup 2 T) (hne : M₀ ≠ T) :
    8 * Nat.card (baum S) ≤ Nat.card ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) := by
  obtain ⟨y, hyT, hyN, hyM⟩ := exists_mem_normalizer_not_mem hT m.hMT hne
  have hle : M₀ ≤ T ⊓ Subgroup.normalizer (M₀ : Set G) := le_inf m.hMT Subgroup.le_normalizer
  have hlt : Nat.card M₀ < Nat.card ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun h => ?_
    have := Subgroup.eq_of_le_of_card_ge hle h.ge
    exact hyM (this ▸ (⟨hyT, hyN⟩ : y ∈ T ⊓ Subgroup.normalizer (M₀ : Set G)))
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  have hMpos : 0 < Nat.card M₀ := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hk'
    push Not at hk'
    interval_cases k
    · omega
    · omega
  have hM₀ : Nat.card M₀ = 2 * Nat.card S := by
    have := Subgroup.relIndex_mul_card (H := S) (K := M₀)
    rw [m.h2, inf_eq_left.2 m.hSM] at this
    omega
  have hS := GMate.card_S_eq (m := m) C
  have h3 : Nat.card M₀ * 2 ≤ Nat.card M₀ * k := Nat.mul_le_mul_left _ hk2
  omega

theorem card_range_rho
    (F : GFour C x) (hT : IsPGroup 2 T) (hne : M₀ ≠ T) :
    Nat.card (GMate.rho (m := m) C F).range = 8 := by
  set ρ := GMate.rho (m := m) C F with hρ
  have hker : ρ.ker = (baum S).subgroupOf (T ⊓ Subgroup.normalizer (M₀ : Set G)) := by
    ext γ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρ]
    exact GMate.rho_eq_one_iff (m := m) C F γ
  have hkcard : Nat.card ρ.ker = Nat.card (baum S) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (m.baum_le_Γ)).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range ρ
  have h2 := GMate.card_Γ_ge (m := m) C hT hne
  have hΓ : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) := hT.to_le inf_le_left
  have hR : IsPGroup 2 ↥ρ.range := hΓ.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have h3 := card_le_eight hR
  have hBpos : 0 < Nat.card (baum S) := Nat.card_pos
  rw [hkcard] at h1
  have h4 : 8 ≤ Nat.card ρ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (baum S) * Nat.card ρ.range < Nat.card (baum S) * 8 :=
      Nat.mul_lt_mul_of_pos_left hlt hBpos
    omega
  omega

theorem rho_dihedral
    (F : GFour C x) (hT : IsPGroup 2 T) (hne : M₀ ≠ T) :
    ∃ f : ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) →* DihedralGroup 4,
      Function.Surjective f ∧
        f.ker = (baum S).subgroupOf (T ⊓ Subgroup.normalizer (M₀ : Set G)) := by
  obtain ⟨e⟩ := exists_mulEquiv_dihedral (GMate.card_range_rho (m := m) C F hT hne)
  refine ⟨e.symm.toMonoidHom.comp (GMate.rho (m := m) C F).rangeRestrict, ?_, ?_⟩
  · exact e.symm.surjective.comp (GMate.rho (m := m) C F).rangeRestrict_surjective
  · ext γ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show e.symm ((GMate.rho (m := m) C F).rangeRestrict γ) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← GMate.rho_eq_one_iff (m := m) C F γ]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h

theorem card_normalizer_pair
    (F : GFour C x) (hT : IsPGroup 2 T) (hne : M₀ ≠ T) {i : Fin 4}
    (hi : i ≠ 0) :
    Nat.card S ≤ Nat.card ↥(T ⊓ Subgroup.normalizer ((F.A4 i ⊔ pCoreOf 2 H : Subgroup G) :
      Set G)) := by
  obtain ⟨g, hgP, hg1, hg⟩ := exists_pair_stabilizer (GMate.card_range_rho (m := m) C F hT hne) hi.symm
  obtain ⟨γ, rfl⟩ := hgP
  have hγB : (γ : G) ∉ baum S := fun h => hg1 ((GMate.rho_eq_one_iff (m := m) C F γ).2 h)
  have hγN : (γ : G) ∈ Subgroup.normalizer ((F.A4 i ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    have hQ0 : F.A4 0 = pCoreOf 2 H := rfl
    have key : conjSubgroup (F.A4 i ⊔ F.A4 0) (γ : G)⁻¹ = F.A4 i ⊔ F.A4 0 := by
      rw [C5.conjSubgroup_sup, ← GMate.rho_apply (m := m) C F γ i, ← GMate.rho_apply (m := m) C F γ 0]
      rcases hg with ⟨h0, hi'⟩ | ⟨h0, hi'⟩
      · rw [h0, hi']
      · rw [h0, hi', sup_comm]
    rw [hQ0] at key
    have := conjSubgroup_eq_iff_mem_normalizer.1 key
    have := (Subgroup.normalizer _).inv_mem this
    rwa [inv_inv] at this
  set N := T ⊓ Subgroup.normalizer ((F.A4 i ⊔ pCoreOf 2 H : Subgroup G) : Set G) with hN
  have hBN : baum S ≤ N := by
    refine le_inf ((inf_le_left : baum S ≤ S).trans (m.hSM.trans m.hMT)) fun b hb => ?_
    exact mem_normalizer_sup_of (GMate.B_le_normalizer_A4 (m := m) C F i hb) (GMate.B_le_normalizer_A4 (m := m) C F 0 hb)
  have hγN' : (γ : G) ∈ N := ⟨γ.2.1, hγN⟩
  have hlt : Nat.card (baum S) < Nat.card N := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hBN) fun h => ?_
    have := Subgroup.eq_of_le_of_card_ge hBN h.ge
    exact hγB (this ▸ hγN')
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBN
  have hBpos : 0 < Nat.card (baum S) := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hk'
    push Not at hk'
    interval_cases k
    · omega
    · omega
  have hS := GMate.card_S_eq (m := m) C
  have h3 : Nat.card (baum S) * 2 ≤ Nat.card (baum S) * k := Nat.mul_le_mul_left _ hk2
  omega

end GMate

end CFSG.QuasithinUnique.burnsideC56_P.AppD
