module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDD8
public import CFSG.Milestones.ASVolI.C61.PAppDJ
public import CFSG.Milestones.ASVolI.C61.PAppDC61a

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

structure GFour {T M H S L : Subgroup G} (C : GCfg T M H S L) (x : G) where
  r : G
  hrS : r ∈ S
  hrB : r ∉ baum S
  v : G
  hv : v ∈ conjR (C.U) x
  hπ : C.P.pf v = swap 0 1

namespace GFour

variable {T M H S L : Subgroup G} {C : GCfg T M H S L} {x : G} (F : GFour C x)

@[expose] def Y : Subgroup G := GYv C.U (blockD S L) F.v

@[expose] def Y' : Subgroup G := conjR F.Y F.r

@[expose] def A4 : Fin 4 → Subgroup G :=
  ![pCoreOf 2 H, conjR (pCoreOf 2 H) x, F.Y, F.Y']

noncomputable def act (γ : G) (i : Fin 4) : Fin 4 :=
  Classical.epsilon fun j => F.A4 j = conjSubgroup (F.A4 i) γ

theorem A4_act {γ : G} {i : Fin 4} (h : ∃ j, F.A4 j = conjSubgroup (F.A4 i) γ) :
    F.A4 (F.act γ i) = conjSubgroup (F.A4 i) γ :=
  Classical.epsilon_spec h

end GFour

namespace GCfg

variable {T M H S L : Subgroup G} (C : GCfg T M H S L)
include C

theorem S_le_normalizer_Q {s : G} (hs : s ∈ S) :
    s ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H (C.hSH hs)

theorem mem_S_of_normalizer_Q {y : G} (hyT : y ∈ T)
    (hyN : y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G)) : y ∈ S := by
  have hHP : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have e := C.hcs.l244 (pCoreOf 2 H) (C56.pCoreOf_ne_bot C.hcs) C.hQS hHP
  have : y ∈ T ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) := ⟨hyT, hyN⟩
  rwa [e] at this

end GCfg

namespace GMate
open CFSG.QuasithinUnique.AppD.GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)
include C m

theorem Yv_decomp {v : G} (hv : v ∈ conjR (C.U) x) {y : G} (hy : y ∈ GYv C.U (blockD S L) v) :
    ∃ a ∈ pCoreOf 2 H, y = a ∨ y = a * v := by
  have hvS : v ∈ S := GMate.V_le_S (m := m) C hv
  have hv2 : v ^ 2 = 1 := V_sq (x := x) C hv
  set X' := (C.U ⊓ Subgroup.centralizer ({v} : Set G)) ⊔ blockD S L with hX'
  have hXQ : X' ≤ pCoreOf 2 H := sup_le (inf_le_left.trans C.hUQ) C.D_le_Q
  have hXv : ∀ a ∈ X', a * v = v * a := by
    intro a ha
    have hle : X' ≤ Subgroup.centralizer ({v} : Set G) := by
      refine sup_le inf_le_right fun d hd => ?_
      exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (GMate.D_comm_V (m := m) C hd hv).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle ha) v (Set.mem_singleton v)).symm
  have hzp : Subgroup.zpowers v ≤ Subgroup.centralizer (X' : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 hXv)
  have hcomm2 : ∀ a ∈ X', ∀ b ∈ Subgroup.zpowers v, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (hzp hb) a ha
  obtain ⟨a, ha, b, hb, rfl⟩ := C5.mem_sup_of_commute hcomm2 (show y ∈ X' ⊔ Subgroup.zpowers v from hy)
  refine ⟨a, hXQ ha, ?_⟩
  rcases eq_one_or_of_mem_zpowers hv2 hb with h | h
  · left; rw [h, mul_one]
  · right; rw [h]

theorem Yv_type {v : G} (hv : v ∈ conjR (C.U) x) (hπ : C.P.pf v = swap 0 1) :
    ∀ g, g ∈ C.P.im (GYv C.U (blockD S L) v) ↔ g = 1 ∨ g = swap 0 1 := by
  intro g
  have hvS : v ∈ S := GMate.V_le_S (m := m) C hv
  have hYS : GYv C.U (blockD S L) v ≤ S := (GMate.Yv_isMax (m := m) C hv hπ).1.1
  have hYN : GYv C.U (blockD S L) v ≤ S := hYS
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf hYN).1 hg
    obtain ⟨a, haQ, hya⟩ := GMate.Yv_decomp (m := m) C hv hy
    have haS := C.hQS haQ
    rcases hya with h | h
    · left; rw [h]; exact C.pf_eq_one_of_mem_Q haQ
    · right
      rw [h, C.P.pf_mul (haS) (hvS), C.pf_eq_one_of_mem_Q haQ, hπ, one_mul]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact (C.P.mem_im_pf hYN).2 ⟨v, Subgroup.mem_sup_right (Subgroup.mem_zpowers v), hπ⟩

theorem B_le_normalizer_Y
    {v : G} (hv : v ∈ conjR (C.U) x) (hπ : C.P.pf v = swap 0 1) :
    baum S ≤ Subgroup.normalizer (GYv C.U (blockD S L) v : Set G) := by
  intro b hb
  have hbS : b ∈ S := hb.1
  have hbE : C.P.pf b ∈ Eset := by
    have : C.P.pf b ∈ C.P.im (baum S) := (C.P.mem_im_pf (inf_le_left)).2 ⟨b, hb, rfl⟩
    rw [C.hB] at this
    exact (mem_Estd _).1 this
  have hYS : GYv C.U (blockD S L) v ≤ S := (GMate.Yv_isMax (m := m) C hv hπ).1.1
  have hA' : IsMaxElemAbelian S (conjSubgroup (GYv C.U (blockD S L) v) b) :=
    C56.isMaxElemAbelian_conjSubgroup (GMate.Yv_isMax (m := m) C hv hπ).1 (Subgroup.le_normalizer hbS)
  have hty : ∀ g, g ∈ C.P.im (conjSubgroup (GYv C.U (blockD S L) v) b) ↔ g = 1 ∨ g = swap 0 1 := by
    intro g
    have h := C.mem_im_conj_inv (inv_mem hbS) hYS (g := g)
    rw [inv_inv] at h
    rw [h, C.P.pf_inv (hbS), inv_inv, GMate.Yv_type (m := m) C hv hπ]
    exact conj_E_cases _ hbE g
  have heq := GMate.eq_Yv_of_type_t1 (m := m) C hA' hty hv hπ
  rw [← conjSubgroup_eq_iff_mem_normalizer, heq]

theorem nonempty_four : Nonempty (GFour C x) := by
  obtain ⟨r, hrS, hrB⟩ := C.exists_r
  have hVN : conjR (C.U) x ≤ S := (GMate.V_le_S (m := m) C)
  have ht1 : swap (0 : Fin 5) 1 ∈ C.P.im (conjR C.U x) := by
    rw [GMate.im_V (m := m) C]; exact (mem_Estd _).2 t1_mem_Eset
  obtain ⟨v, hv, hπ⟩ := (C.P.mem_im_pf hVN).1 ht1
  exact ⟨⟨r, hrS, hrB, v, hv, hπ⟩⟩

variable (F : GFour C x)

theorem isMax_A4 (i : Fin 4) : IsMaxElemAbelian S (F.A4 i) := by
  have hYm := (GMate.Yv_isMax (m := m) C F.hv F.hπ).1
  fin_cases i
  · exact GMate.Q_isMax (m := m) C
  · exact GMate.Qx_isMax (m := m) C
  · exact hYm
  · exact C56.isMaxElemAbelian_conjSubgroup hYm (Subgroup.le_normalizer F.hrS)

theorem members {A : Subgroup G} : IsMaxElemAbelian S A ↔ ∃ i, A = F.A4 i := by
  constructor
  · intro hA
    rcases (GMate.a5_members (m := m) C F.hrS F.hrB F.hv F.hπ A).1 hA with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · rintro ⟨i, rfl⟩
    exact GMate.isMax_A4 (m := m) C F i

omit m in
theorem type_Q : ∀ g, g ∈ C.P.im (pCoreOf 2 H) ↔ g = 1 := by
  intro g
  have hQN : pCoreOf 2 H ≤ S := C.hQS
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf hQN).1 hg
    exact C.pf_eq_one_of_mem_Q hy
  · rintro rfl
    exact one_mem _

theorem type_conj_Y {s : G} (hsS : s ∈ S) (hsB : s ∉ baum S) :
    ∀ g, g ∈ C.P.im (conjR F.Y s) ↔ g = 1 ∨ g = swap 2 3 := by
  intro g
  have hYS : F.Y ≤ S := (GMate.Yv_isMax (m := m) C F.hv F.hπ).1.1
  have hY : ∀ g, g ∈ C.P.im F.Y ↔ g = 1 ∨ g = swap 0 1 := GMate.Yv_type (m := m) C F.hv F.hπ
  have h := C.mem_im_conj_inv (inv_mem hsS) hYS (g := g)
  rw [inv_inv, C.P.pf_inv (hsS), inv_inv] at h
  show g ∈ C.P.im (conjSubgroup F.Y s) ↔ _
  rw [h, hY]
  have hD : C.P.pf s ∈ Dset := by
    have : C.P.pf s ∈ C.P.im S := (C.P.mem_im_pf le_rfl).2 ⟨s, hsS, rfl⟩
    rw [C.hS] at this
    exact (mem_Dstd _).1 this
  have hnE : C.P.pf s ∉ Eset := fun h => hsB (GMate.mem_B_of_pf (m := m) C hsS h)
  exact conj_D_cases _ hD hnE g

theorem type_Y' : ∀ g, g ∈ C.P.im F.Y' ↔ g = 1 ∨ g = swap 2 3 :=
  GMate.type_conj_Y (m := m) C F F.hrS F.hrB

theorem mem1_iff
    (i : Fin 4) : swap (0 : Fin 5) 1 ∈ C.P.im (F.A4 i) ↔ (i = 1 ∨ i = 2) := by
  fin_cases i
  · show swap (0 : Fin 5) 1 ∈ C.P.im (pCoreOf 2 H) ↔ _
    rw [type_Q C]
    simp
  · show swap (0 : Fin 5) 1 ∈ C.P.im (conjR (pCoreOf 2 H) x) ↔ _
    rw [GMate.Qx_type_E (m := m) C]
    simp [t1_mem_Eset]
  · show swap (0 : Fin 5) 1 ∈ C.P.im (GYv C.U (blockD S L) F.v) ↔ _
    rw [GMate.Yv_type (m := m) C F.hv F.hπ]
    simp
  · show swap (0 : Fin 5) 1 ∈ C.P.im F.Y' ↔ _
    rw [GMate.type_Y' (m := m) C F]
    simp [swap01_ne_swap23]

theorem mem2_iff
    (i : Fin 4) : swap (2 : Fin 5) 3 ∈ C.P.im (F.A4 i) ↔ (i = 1 ∨ i = 3) := by
  fin_cases i
  · show swap (2 : Fin 5) 3 ∈ C.P.im (pCoreOf 2 H) ↔ _
    rw [type_Q C]
    simp
  · show swap (2 : Fin 5) 3 ∈ C.P.im (conjR (pCoreOf 2 H) x) ↔ _
    rw [GMate.Qx_type_E (m := m) C]
    simp [t2_mem_Eset]
  · show swap (2 : Fin 5) 3 ∈ C.P.im (GYv C.U (blockD S L) F.v) ↔ _
    rw [GMate.Yv_type (m := m) C F.hv F.hπ]
    simp [swap01_ne_swap23.symm]
  · show swap (2 : Fin 5) 3 ∈ C.P.im F.Y' ↔ _
    rw [GMate.type_Y' (m := m) C F]
    simp

theorem A4_injective : Function.Injective F.A4 := by
  intro i j h
  apply fin4_eq i j
  · rw [← GMate.mem1_iff (m := m) C F i, ← GMate.mem1_iff (m := m) C F j, h]
  · rw [← GMate.mem2_iff (m := m) C F i, ← GMate.mem2_iff (m := m) C F j, h]

theorem isMax_conj_M₀ {γ : G} (hγ : γ ∈ Subgroup.normalizer (M₀ : Set G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) : IsMaxElemAbelian S (conjSubgroup A γ) := by
  have hiff := isMaxElemAbelian_M₀_iff C m.hSM m.hMT m.h2
  exact (hiff _).1 (C56.isMaxElemAbelian_conjSubgroup ((hiff A).2 hA) hγ)

theorem exists_act {γ : G} (hγ : γ ∈ Subgroup.normalizer (M₀ : Set G)) (i : Fin 4) :
    ∃ j, F.A4 j = conjSubgroup (F.A4 i) γ := by
  obtain ⟨j, hj⟩ := (GMate.members (m := m) C F).1 (GMate.isMax_conj_M₀ (m := m) C hγ (GMate.isMax_A4 (m := m) C F i))
  exact ⟨j, hj.symm⟩

theorem A4_act' {γ : G} (hγ : γ ∈ Subgroup.normalizer (M₀ : Set G)) (i : Fin 4) :
    F.A4 (F.act γ i) = conjSubgroup (F.A4 i) γ := F.A4_act (GMate.exists_act (m := m) C F hγ i)

theorem act_act
    {γ δ : G} (hγ : γ ∈ Subgroup.normalizer (M₀ : Set G))
    (hδ : δ ∈ Subgroup.normalizer (M₀ : Set G)) (i : Fin 4) :
    F.act δ (F.act γ i) = F.act (γ * δ) i := by
  apply GMate.A4_injective (m := m) C F
  rw [GMate.A4_act' (m := m) C F hδ, GMate.A4_act' (m := m) C F hγ, GMate.A4_act' (m := m) C F (mul_mem hγ hδ), conjSubgroup_conjSubgroup]

theorem act_one (i : Fin 4) : F.act 1 i = i := by
  apply GMate.A4_injective (m := m) C F
  rw [GMate.A4_act' (m := m) C F (one_mem _), conjSubgroup_one]

@[expose] noncomputable def rho :
    ↥(T ⊓ Subgroup.normalizer (M₀ : Set G)) →* Equiv.Perm (Fin 4) where
  toFun γ :=
    { toFun := F.act (γ : G)⁻¹
      invFun := F.act (γ : G)
      left_inv := fun i => by
        rw [GMate.act_act (m := m) C F (inv_mem γ.2.2) γ.2.2, inv_mul_cancel, GMate.act_one (m := m) C F]
      right_inv := fun i => by
        rw [GMate.act_act (m := m) C F γ.2.2 (inv_mem γ.2.2), mul_inv_cancel, GMate.act_one (m := m) C F] }
  map_one' := by
    refine Equiv.ext fun i => ?_
    show F.act ((1 : ↥(T ⊓ Subgroup.normalizer (M₀ : Set G))) : G)⁻¹ i = i
    rw [Subgroup.coe_one, inv_one, GMate.act_one (m := m) C F]
  map_mul' := fun γ δ => by
    refine Equiv.ext fun i => ?_
    show F.act (((γ * δ : ↥(T ⊓ Subgroup.normalizer (M₀ : Set G))) : G))⁻¹ i =
      F.act (γ : G)⁻¹ (F.act (δ : G)⁻¹ i)
    rw [GMate.act_act (m := m) C F (inv_mem δ.2.2) (inv_mem γ.2.2), Subgroup.coe_mul, mul_inv_rev]

theorem rho_apply
    (γ : ↥(T ⊓ Subgroup.normalizer (M₀ : Set G))) (i : Fin 4) :
    F.A4 (GMate.rho (m := m) C F γ i) = conjSubgroup (F.A4 i) (γ : G)⁻¹ :=
  GMate.A4_act' (m := m) C F (inv_mem γ.2.2) i

theorem B_le_normalizer_A4
    (i : Fin 4) : baum S ≤ Subgroup.normalizer (F.A4 i : Set G) := by
  intro b hb
  have hbS : b ∈ S := hb.1
  fin_cases i
  · exact C.S_le_normalizer_Q hbS
  · show b ∈ Subgroup.normalizer ((conjSubgroup (pCoreOf 2 H) x : Subgroup G) : Set G)
    exact mem_normalizer_conj_of (C.S_le_normalizer_Q (m.conj_mem_S hbS))
  · exact GMate.B_le_normalizer_Y (m := m) C F.hv F.hπ hb
  · show b ∈ Subgroup.normalizer ((conjSubgroup F.Y F.r : Subgroup G) : Set G)
    refine mem_normalizer_conj_of ?_
    have hr : F.r ∈ Subgroup.normalizer (baum S : Set G) :=
      normalizer_le_normalizer_baum S (Subgroup.le_normalizer F.hrS)
    exact GMate.B_le_normalizer_Y (m := m) C F.hv F.hπ ((Subgroup.mem_normalizer_iff.1 hr b).1 hb)

theorem rho_eq_one_iff
    (γ : ↥(T ⊓ Subgroup.normalizer (M₀ : Set G))) :
    GMate.rho (m := m) C F γ = 1 ↔ (γ : G) ∈ baum S := by
  constructor
  · intro h
    have hfix : ∀ i, conjSubgroup (F.A4 i) (γ : G)⁻¹ = F.A4 i := fun i => by
      rw [← GMate.rho_apply (m := m) C F γ i, h]
      rfl
    have hγ'S : (γ : G)⁻¹ ∈ S :=
      C.mem_S_of_normalizer_Q ((T).inv_mem γ.2.1) (conjSubgroup_eq_iff_mem_normalizer.1 (hfix 0))
    by_contra hB
    have hB' : (γ : G)⁻¹ ∉ baum S := fun h' => hB (by
      have := (baum S).inv_mem h'
      rwa [inv_inv] at this)
    have h01 : swap (0 : Fin 5) 1 ∈ C.P.im F.Y := (GMate.Yv_type (m := m) C F.hv F.hπ _).2 (Or.inr rfl)
    have h01' : swap (0 : Fin 5) 1 ∈ C.P.im (conjR F.Y (γ : G)⁻¹) := by
      have e : conjR F.Y (γ : G)⁻¹ = F.Y := hfix 2
      rw [e]
      exact h01
    rcases (GMate.type_conj_Y (m := m) C F hγ'S hB' _).1 h01' with h1 | h1
    · exact swap01_ne_one h1
    · exact swap01_ne_swap23 h1
  · intro hb
    refine Equiv.ext fun i => ?_
    apply GMate.A4_injective (m := m) C F
    rw [GMate.rho_apply (m := m) C F γ i]
    exact C5.conjSubgroup_eq_self (GMate.B_le_normalizer_A4 (m := m) C F i ((baum S).inv_mem hb))

end GMate

end CFSG.QuasithinUnique.burnsideC56_P.AppD
