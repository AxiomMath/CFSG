module

public import CFSG.Milestones.ASVolI.C61.PAppCCls2

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppC

open CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G]

namespace Mate
open CFSG.QuasithinUnique.AppC.Mate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : Cfg T M H S L) (m : Mate S T M₀ x)
include C m

theorem V_inf_D : conjR (blockU L) x ⊓ blockD S L = ⊥ := by
  refine eq_bot_iff.2 fun y hy => ?_
  have hyU := Mate.V_inf_Q_le_U (m := m) C hy.1 (C.D_le_Q hy.2)
  have : y ∈ blockU L ⊓ blockD S L := ⟨hyU, hy.2⟩
  rwa [C.U_inf_D] at this

theorem mem_B_of_pf {a : G} (haS : a ∈ S) (hπ : C.P.pf a ∈ Eset) : a ∈ baum S := by
  obtain ⟨v, hv, u, hu, d, hd, rfl, -⟩ := Mate.exists_vud (m := m) C haS hπ
  exact mul_mem (mul_mem (Mate.V_le_B (m := m) C hv) (C.blockU_le_baum hu)) (Mate.D_le_B (m := m) C hd)

theorem card_VD : Nat.card ↥(conjR (blockU L) x ⊔ blockD S L) = 16 * Nat.card ↥(blockD S L) := by
  have h := B2F.card_sup_mul_card_inf_of_commute (A := conjR (blockU L) x) (B := blockD S L)
    (fun v hv d hd => (Mate.D_comm_V (m := m) C hd hv).symm)
  rw [Mate.V_inf_D (m := m) C, Subgroup.card_bot, card_V (x := x) C] at h
  omega

theorem eq_VD_of_type_E {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g ∈ Eset) : A = conjR (blockU L) x ⊔ blockD S L := by
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hA.1.trans C.hSN
  have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (L : Set G) := (Mate.V_le_S (m := m) C).trans C.hSN
  have hD := Mate.D_le_of_isMax (m := m) C hA
  have hex : ∀ g ∈ Eset, ∃ v ∈ conjR (blockU L) x, ∃ u ∈ blockU L,
      v * u ∈ A ∧ C.P.pf v = g := by
    intro g hg
    have hgA : g ∈ C.P.im A := (hty g).2 hg
    obtain ⟨a, haA, hpa⟩ := (C.P.mem_im_pf hAN).1 hgA
    obtain ⟨v, hv, u, hu, d, hd, hadec, hpv⟩ := Mate.exists_vud (m := m) C (hA.1 haA) (by rw [hpa]; exact hg)
    refine ⟨v, hv, u, hu, ?_, by rw [hpv, hpa]⟩
    have := mul_mem haA (inv_mem (hD hd))
    rw [hadec] at this
    simpa [mul_assoc] using this
  have hfixu : ∀ v ∈ conjR (blockU L) x, ∀ u ∈ blockU L, v * u ∈ A →
      vact (C.P.pf v) (C.P.bf u) = C.P.bf u := by
    intro v hv u hu hvu
    have hcom := comm_of_sq (hA.2.1.2 _ hvu) (V_sq (x := x) C hv) (C.hU.2 u hu)
    exact (C.P.comm_iff (hVN hv) hu).1 hcom
  obtain ⟨v₁, hv₁, u₁, hu₁, h₁A, hp₁⟩ := hex (swap 0 1) t1_mem_Eset
  obtain ⟨v₂, hv₂, u₂, hu₂, h₂A, hp₂⟩ := hex (swap 2 3) t2_mem_Eset
  have hf₁ := hfixu v₁ hv₁ u₁ hu₁ h₁A
  have hf₂ := hfixu v₂ hv₂ u₂ hu₂ h₂A
  rw [hp₁] at hf₁
  rw [hp₂] at hf₂
  have hcomm12 : (v₁ * u₁) * (v₂ * u₂) = (v₂ * u₂) * (v₁ * u₁) :=
    B2F.isElemAbelian_comm hA.2.1 h₁A h₂A
  have hrel := (C.P.comm_vu (hVN hv₁) (hVN hv₂) hu₁ hu₂ (V_comm (x := x) C hv₁ hv₂)).1 hcomm12
  rw [hp₁, hp₂, Equiv.swap_inv, Equiv.swap_inv] at hrel
  have hrel' : pact (swap 2 3) (C.P.bf u₁).1 + (C.P.bf u₂).1 =
      pact (swap 0 1) (C.P.bf u₂).1 + (C.P.bf u₁).1 := congrArg Subtype.val hrel
  obtain ⟨hF1, hF2⟩ := E_comm _ _ hrel'
  have hF1' : ∀ σ ∈ Eset, vact σ (C.P.bf u₁) = C.P.bf u₁ := fun σ hσ =>
    Subtype.ext (fixE_of _ (congrArg Subtype.val hf₁) hF1 σ hσ)
  have hF2' : ∀ σ ∈ Eset, vact σ (C.P.bf u₂) = C.P.bf u₂ := fun σ hσ =>
    Subtype.ext (fixE_of _ hF2 (congrArg Subtype.val hf₂) σ hσ)
  have hle : A ≤ conjR (blockU L) x ⊔ blockD S L := by
    intro a ha
    have hpa : C.P.pf a ∈ Eset := (hty _).1 ((C.P.mem_im_pf hAN).2 ⟨a, ha, rfl⟩)
    obtain ⟨v, hv, u, hu, d, hd, hadec, hpv⟩ := Mate.exists_vud (m := m) C (hA.1 ha) hpa
    have hvu : v * u ∈ A := by
      have := mul_mem ha (inv_mem (hD hd))
      rw [hadec] at this
      simpa [mul_assoc] using this
    have hpvE : C.P.pf v ∈ Eset := by rw [hpv]; exact hpa
    have hinvE : (C.P.pf v)⁻¹ ∈ Eset := by
      have := Eset_inv _ hpvE
      exact this
    have hfix1 : vact (swap 0 1) (C.P.bf u) = C.P.bf u := by
      have hcom : (v * u) * (v₁ * u₁) = (v₁ * u₁) * (v * u) :=
        B2F.isElemAbelian_comm hA.2.1 hvu h₁A
      have h := (C.P.comm_vu (hVN hv) (hVN hv₁) hu hu₁ (V_comm (x := x) C hv hv₁)).1 hcom
      rw [hp₁, Equiv.swap_inv, hF1' _ hinvE] at h
      rw [add_comm (C.P.bf u₁) (C.P.bf u)] at h
      exact add_right_cancel h
    have hfix2 : vact (swap 2 3) (C.P.bf u) = C.P.bf u := by
      have hcom : (v * u) * (v₂ * u₂) = (v₂ * u₂) * (v * u) :=
        B2F.isElemAbelian_comm hA.2.1 hvu h₂A
      have h := (C.P.comm_vu (hVN hv) (hVN hv₂) hu hu₂ (V_comm (x := x) C hv hv₂)).1 hcom
      rw [hp₂, Equiv.swap_inv, hF2' _ hinvE] at h
      rw [add_comm (C.P.bf u₂) (C.P.bf u)] at h
      exact add_right_cancel h
    have hallE : ∀ σ ∈ Eset, vact σ (C.P.bf u) = C.P.bf u := fun σ hσ =>
      Subtype.ext (fixE_of _ (congrArg Subtype.val hfix1) (congrArg Subtype.val hfix2) σ hσ)
    have huC : u ∈ Subgroup.centralizer (conjR (blockU L) x : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
      have hwE : C.P.pf w ∈ Eset := by
        have : C.P.pf w ∈ C.P.im (conjR (blockU L) x) := (C.P.mem_im_pf hVN).2 ⟨w, hw, rfl⟩
        rw [Mate.im_V (m := m) C] at this
        exact (mem_Estd _).1 this
      exact (C.P.comm_iff (hVN hw) hu).2 (hallE _ hwE)
    have huV : u ∈ conjR (blockU L) x := by
      have : u ∈ blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G) := ⟨hu, huC⟩
      rw [(Mate.cent_U_V (m := m) C).1] at this
      exact this.2
    rw [hadec]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hv huV)) (Subgroup.mem_sup_right hd)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Mate.card_VD (m := m) C, ← C.card_Q, ← Mate.card_eq_Q (m := m) C hA]

theorem Qx_type_E : ∀ g, g ∈ C.P.im (conjR (pCoreOf 2 H) x) ↔ g ∈ Eset := by
  have hQx := Mate.Qx_isMax (m := m) C
  have hVle : conjR (blockU L) x ≤ conjR (pCoreOf 2 H) x := C5.conjSubgroup_mono C.hUQ x
  have hmem : ∀ g ∈ Eset, g ∈ C.P.im (conjR (pCoreOf 2 H) x) := by
    intro g hg
    have : g ∈ C.P.im (conjR (blockU L) x) := by rw [Mate.im_V (m := m) C]; exact (mem_Estd g).2 hg
    exact C.P.im_mono hVle this
  have ht1 := hmem _ t1_mem_Eset
  have ht2 := hmem _ t2_mem_Eset
  rcases Mate.type_cases (m := m) C hQx with h | h | h | h
  · exact absurd ((h _).1 ht1) (by decide)
  · rcases (h _).1 ht2 with h' | h'
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · rcases (h _).1 ht1 with h' | h'
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · exact h

theorem Qx_eq : conjR (pCoreOf 2 H) x = conjR (blockU L) x ⊔ blockD S L :=
  Mate.eq_VD_of_type_E (m := m) C (Mate.Qx_isMax (m := m) C) (Mate.Qx_type_E (m := m) C)

theorem pf_r {r : G} (hrS : r ∈ S) (hrL : r ∈ L) (hrB : r ∉ baum S) :
    (C.P.pf r)⁻¹ * swap 0 1 * C.P.pf r = swap 2 3 ∧
      (C.P.pf r)⁻¹ * swap 2 3 * C.P.pf r = swap 0 1 := by
  have hrN : r ∈ Subgroup.normalizer (L : Set G) := C.hSN hrS
  have hD : C.P.pf r ∈ Dset := by
    have : C.P.pf r ∈ C.P.im S := (C.P.mem_im_pf C.hSN).2 ⟨r, hrS, rfl⟩
    rw [C.hS] at this
    exact (mem_Dstd _).1 this
  have hsign : Perm.sign (C.P.pf r) = 1 := by
    have h := C.P.hπα r hrL
    rw [C.P.pf_eq hrN]
    have h' : C.P.π ⟨r, hrN⟩ = ((C.P.α ⟨r, hrL⟩ : alternatingGroup (Fin 5)) : Perm (Fin 5)) := h
    rw [h']
    exact Equiv.Perm.mem_alternatingGroup.1 (C.P.α ⟨r, hrL⟩).2
  have hnE : C.P.pf r ∉ Eset := fun h => hrB (Mate.mem_B_of_pf (m := m) C hrS h)
  exact conj_swap_of _ hD hsign hnE

theorem eq_conj_Yv_of_type_t2 {r : G} (hrS : r ∈ S) (hrL : r ∈ L) (hrB : r ∉ baum S)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hty : ∀ g, g ∈ C.P.im A ↔ g = 1 ∨ g = swap 2 3) {v : G} (hv : v ∈ conjR (blockU L) x)
    (hπ : C.P.pf v = swap 0 1) : A = conjR (Yv S L v) r := by
  obtain ⟨hσ1, hσ2⟩ := Mate.pf_r (m := m) C hrS hrL hrB
  have hrN : r ∈ Subgroup.normalizer (L : Set G) := C.hSN hrS
  have hrNS : r⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem (Subgroup.le_normalizer hrS)
  have hA' : IsMaxElemAbelian S (conjSubgroup A r⁻¹) := C56.isMaxElemAbelian_conjSubgroup hA hrNS
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := hA.1.trans C.hSN
  have hA'N : conjSubgroup A r⁻¹ ≤ Subgroup.normalizer (L : Set G) := hA'.1.trans C.hSN
  have hty' : ∀ g, g ∈ C.P.im (conjSubgroup A r⁻¹) ↔ g = 1 ∨ g = swap 0 1 := by
    intro g
    constructor
    · intro hg
      obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf hA'N).1 hg
      have hy' : r⁻¹ * y * r ∈ A := by
        have := mem_conjSubgroup_iff.1 hy
        simpa using this
      have hyN : y ∈ Subgroup.normalizer (L : Set G) := hA'N hy
      have hb : C.P.pf (r⁻¹ * y * r) = (C.P.pf r)⁻¹ * C.P.pf y * C.P.pf r := by
        rw [C.P.pf_mul (mul_mem (inv_mem hrN) hyN) hrN, C.P.pf_mul (inv_mem hrN) hyN,
          C.P.pf_inv hrN]
      have hbA : C.P.pf (r⁻¹ * y * r) ∈ C.P.im A := (C.P.mem_im_pf hAN).2 ⟨_, hy', rfl⟩
      have e : C.P.pf y = C.P.pf r * C.P.pf (r⁻¹ * y * r) * (C.P.pf r)⁻¹ := by
        rw [hb]; group
      rcases (hty _).1 hbA with h | h
      · left
        rw [e, h]; group
      · right
        have e2 : swap (0 : Fin 5) 1 = C.P.pf r * swap 2 3 * (C.P.pf r)⁻¹ := by
          rw [← hσ1]; group
        rw [e, h, ← e2]
    · rintro (rfl | rfl)
      · exact one_mem _
      · have ht2 : swap (2 : Fin 5) 3 ∈ C.P.im A := (hty _).2 (Or.inr rfl)
        obtain ⟨b, hbA, hbp⟩ := (C.P.mem_im_pf hAN).1 ht2
        have hbN : b ∈ Subgroup.normalizer (L : Set G) := hAN hbA
        refine (C.P.mem_im_pf hA'N).2 ⟨r * b * r⁻¹, ?_, ?_⟩
        · rw [mem_conjSubgroup_iff]
          have : r⁻¹ * (r * b * r⁻¹) * r⁻¹⁻¹ = b := by group
          rw [this]; exact hbA
        · rw [C.P.pf_mul (mul_mem hrN hbN) (inv_mem hrN), C.P.pf_mul hrN hbN, C.P.pf_inv hrN, hbp,
            ← hσ1]
          group
  have heq := Mate.eq_Yv_of_type_t1 (m := m) C hA' hty' hv hπ
  rw [C56.conjR_eq, ← heq]
  exact (C5.conjSubgroup_inv_conjSubgroup A r).symm

end Mate

end CFSG.QuasithinUnique.burnsideC56_P.AppC
