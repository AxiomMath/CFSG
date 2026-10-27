module

public import CFSG.Milestones.ASVolI.C61.PAppDMax
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCAU
public import CFSG.Milestones.ASVolI.C61.PAppC54

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.burnsideC56_P.AppC
open CFSG.QuasithinUnique.AppC hiding Cfg Cfg.Q_comm_U Cfg.aU_spec Cfg.blockU_le_baum Cfg.card_U
  Cfg.hL Cfg.hQ Cfg.hQS Cfg.hSH Cfg.hSN Cfg.hU Cfg.hUQ Cfg.hUS Cfg.omegaOneCenter_le_pCoreOf a5_core
  a5_core_std blockD_le_pCoreOf blockQ_comm_pCoreOf blockU_inf_blockD card_im_S
  exists_mem_thompsonJ_pi_ne_one exists_split exists_split' nonempty_cfg pCoreOf_comm_blockU
  pCoreOf_eq_blockU_sup_blockD swapGen_imJ

variable {G : Type} [Group G] [Finite G]

namespace GCfg

variable {T M H S L : Subgroup G} (C : GCfg T M H S L)
include C

theorem UD_unique {u u' d d' : G} (hu : u ∈ C.U) (hu' : u' ∈ C.U)
    (hd : d ∈ blockD S L) (hd' : d' ∈ blockD S L) (h : u * d = u' * d') : u = u' ∧ d = d' := by
  have h1 : u'⁻¹ * u = d' * d⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * d) * d⁻¹ := by group
      _ = u'⁻¹ * (u' * d') * d⁻¹ := by rw [h]
      _ = d' * d⁻¹ := by group
  have hU : u'⁻¹ * u ∈ C.U := mul_mem (inv_mem hu') hu
  have hD : u'⁻¹ * u ∈ blockD S L := by
    rw [h1]
    exact mul_mem hd' (inv_mem hd)
  have h2 : u'⁻¹ * u ∈ C.U ⊓ blockD S L := ⟨hU, hD⟩
  rw [C.U_inf_D, Subgroup.mem_bot] at h2
  have hue : u = u' := by
    calc u = u' * (u'⁻¹ * u) := by group
      _ = u' := by rw [h2, mul_one]
  refine ⟨hue, ?_⟩
  subst hue
  exact mul_left_cancel h

theorem pf_eq_one_of_mem_Q {a : G} (ha : a ∈ pCoreOf 2 H) : C.P.pf a = 1 := by
  have haN : a ∈ S := (C.hQS ha)
  rw [C.P.pf_eq haN, C.P.hker ⟨a, haN⟩]
  intro u hu
  have := C.Q_comm_U ha hu
  calc a * u * a⁻¹ = (u * a) * a⁻¹ := by rw [this]
    _ = u := by group

theorem mem_Q_of_pf_eq_one {a : G} (haS : a ∈ S) (h : C.P.pf a = 1) : a ∈ pCoreOf 2 H := by
  have haN := haS
  rw [C.P.pf_eq haN] at h
  have h2 := (C.P.hker ⟨a, haN⟩).1 h
  rw [← C.hQ]
  refine ⟨C.hSH haS, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
  have := h2 u hu
  calc u * a = (a * u * a⁻¹) * a := by rw [this]
    _ = a * u := by group

theorem im_le_Dstd {A : Subgroup G} (hA : IsMaxElemAbelian S A) : C.P.im A ≤ Dstd := by
  rw [← C.hS]
  exact C.P.im_mono hA.1

end GCfg

namespace GMate
open CFSG.QuasithinUnique.AppD.GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)
include C m

theorem G_spec {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    A ⊓ pCoreOf 2 H = (C.U ⊓ Subgroup.centralizer (A : Set G)) ⊔ blockD S L ∧
      Nat.card ↥(C.P.im A) * Nat.card ↥(FixΔ (C.P.im A)) = 16 := by
  have hAS := hA.1
  have hAN : A ≤ S := hAS
  have hKX : A ⊓ pCoreOf 2 H ≤ (C.U ⊓ Subgroup.centralizer (A : Set G)) ⊔ blockD S L := by
    intro q hq
    obtain ⟨u, hu, d, hd, rfl⟩ := C.exists_UD hq.2
    have huC : u ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hcomm : a * (u * d) = (u * d) * a := B2F.isElemAbelian_comm hA.2.1 ha hq.1
      have h1 : (a * u * a⁻¹) * (a * d * a⁻¹) = u * d := by
        calc (a * u * a⁻¹) * (a * d * a⁻¹) = a * (u * d) * a⁻¹ := by group
          _ = u * d := by rw [hcomm]; group
      have h2 := C.UD_unique (C.P.conj_mem_U (hAS ha) hu) hu
        (GCfg.conj_mem_blockD (hAS ha) hd) hd h1
      calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [h2.1]
    exact mul_mem (Subgroup.mem_sup_left ⟨hu, huC⟩) (Subgroup.mem_sup_right hd)
  set X := (C.U ⊓ Subgroup.centralizer (A : Set G)) ⊔ blockD S L with hX
  have hKQ : A ⊓ Subgroup.centralizer (C.U : Set G) = A ⊓ pCoreOf 2 H := by
    ext a
    constructor
    · rintro ⟨haA, haC⟩
      exact ⟨haA, by rw [← C.hQ]; exact ⟨C.hSH (hAS haA), haC⟩⟩
    · rintro ⟨haA, haQ⟩
      exact ⟨haA, Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U haQ hu).symm⟩
  have h1 := C.P.card_im_mul hAN
  rw [hKQ] at h1
  have h2 := C.P.card_fix hAN
  have hcardA : Nat.card ↥A = 16 * Nat.card ↥(blockD S L) :=
    (GMate.card_eq_Q (m := m) C hA).trans C.card_Q
  have hf := card_mul_fix_le (C.P.im A) (C.P.im_elemAbelian hA.2.1).1
    (C.P.im_elemAbelian hA.2.1).2
  have hX1 := B2F.card_sup_mul_card_inf_of_commute
    (A := C.U ⊓ Subgroup.centralizer (A : Set G)) (B := blockD S L)
    (fun u hu d hd => C.U_comm_D hu.1 hd)
  have hinf : (C.U ⊓ Subgroup.centralizer (A : Set G)) ⊓ blockD S L = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    have : y ∈ C.U ⊓ blockD S L := ⟨hy.1.1, hy.2⟩
    rwa [C.U_inf_D] at this
  rw [hinf, Subgroup.card_bot, mul_one] at hX1
  have hkx : Nat.card ↥(A ⊓ pCoreOf 2 H) ≤ Nat.card ↥X := Subgroup.card_le_of_le hKX
  have hppos : 0 < Nat.card ↥(C.P.im A) := Nat.card_pos
  have hdpos : 0 < Nat.card ↥(blockD S L) := Nat.card_pos
  set p := Nat.card ↥(C.P.im A)
  set k := Nat.card ↥(A ⊓ pCoreOf 2 H)
  set f := Nat.card ↥(FixΔ (C.P.im A))
  set d := Nat.card ↥(blockD S L)
  set xx := Nat.card ↥X
  rw [h2] at hX1
  have hpk : p * k = 16 * d := by rw [← hcardA, ← h1]
  have hpx : p * xx = p * f * d := by rw [hX1]; ring
  have hchain : p * f * d ≤ 16 * d := Nat.mul_le_mul_right d hf
  have hpf : p * f = 16 := by
    have : p * k ≤ p * xx := Nat.mul_le_mul_left p hkx
    have h3 : 16 * d ≤ p * f * d := by rw [← hpx, ← hpk]; exact this
    have h4 : p * f * d = 16 * d := le_antisymm hchain h3
    exact Nat.eq_of_mul_eq_mul_right hdpos h4
  refine ⟨Subgroup.eq_of_le_of_card_ge hKX ?_, hpf⟩
  have h5 : p * xx = p * k := by rw [hpx, hpf, hpk]
  exact (Nat.eq_of_mul_eq_mul_left hppos h5).le

theorem D_le_of_isMax {A : Subgroup G} (hA : IsMaxElemAbelian S A) : blockD S L ≤ A := by
  intro d hd
  have h : d ∈ A ⊓ pCoreOf 2 H := by
    rw [(GMate.G_spec (m := m) C hA).1]
    exact Subgroup.mem_sup_right hd
  exact h.1

theorem fixU_le_of_isMax {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    C.U ⊓ Subgroup.centralizer (A : Set G) ≤ A := by
  intro u hu
  have h : u ∈ A ⊓ pCoreOf 2 H := by
    rw [(GMate.G_spec (m := m) C hA).1]
    exact Subgroup.mem_sup_left hu
  exact h.1

theorem type_cases {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    (∀ g, g ∈ C.P.im A ↔ g = 1) ∨ (∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = swap 0 1) ∨
      (∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = swap 2 3) ∨ (∀ g, g ∈ C.P.im A ↔ g ∈ Eset) :=
  classify_P (C.P.im A) (C.im_le_Dstd hA) (C.P.im_elemAbelian hA.2.1).1
    (C.P.im_elemAbelian hA.2.1).2 (GMate.G_spec (m := m) C hA).2

theorem eq_Q_of_type_bot {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (h : ∀ g, g ∈ C.P.im A ↔ g = 1) : A = pCoreOf 2 H := by
  have hle : A ≤ pCoreOf 2 H := by
    intro a ha
    have : C.P.pf a ∈ C.P.im A := (C.P.mem_im_pf (hA.1)).2 ⟨a, ha, rfl⟩
    exact C.mem_Q_of_pf_eq_one (hA.1 ha) ((h _).1 this)
  exact Subgroup.eq_of_le_of_card_ge hle (GMate.card_eq_Q (m := m) C hA).ge

theorem exists_vud {a : G} (haS : a ∈ S) (hπ : C.P.pf a ∈ Eset) :
    ∃ v ∈ conjR (C.U) x, ∃ u ∈ C.U, ∃ d ∈ blockD S L,
      a = v * u * d ∧ C.P.pf v = C.P.pf a := by
  have hVN : conjR (C.U) x ≤ S := (GMate.V_le_S (m := m) C)
  have hπ' : C.P.pf a ∈ C.P.im (conjR C.U x) := by
    rw [GMate.im_V (m := m) C]; exact (mem_Estd _).2 hπ
  obtain ⟨v, hv, hvπ⟩ := (C.P.mem_im_pf hVN).1 hπ'
  have hvS : v ∈ S := GMate.V_le_S (m := m) C hv
  have hqS : v⁻¹ * a ∈ S := mul_mem (inv_mem hvS) haS
  have hq1 : C.P.pf (v⁻¹ * a) = 1 := by
    rw [C.P.pf_mul (inv_mem (hvS)) (haS), C.P.pf_inv (hvS), hvπ, inv_mul_cancel]
  have hqQ := C.mem_Q_of_pf_eq_one hqS hq1
  obtain ⟨u, hu, d, hd, hud⟩ := C.exists_UD hqQ
  refine ⟨v, hv, u, hu, d, hd, ?_, hvπ⟩
  calc a = v * (v⁻¹ * a) := by group
    _ = v * (u * d) := by rw [hud]
    _ = v * u * d := by group

end GMate

end CFSG.QuasithinUnique.burnsideC56_P.AppD
