module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T3a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T2b

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem exists_arm_hom_ker (F : FanTree Γ G) :
    ∃ Φ : ↥(nbrStab Γ G S.beta) →* (Fin 3 → (ZMod 5)ˣ),
      (∀ (g : ↥(nbrStab Γ G S.beta)) (i : Fin 3),
        Φ g i = 1 ↔ (g : G) ∈ nbrStab Γ G (S.alphaV i)) ∧
      Φ.ker = (ballStab Γ G 2 S.beta).subgroupOf (nbrStab Γ G S.beta) := by
  obtain ⟨Φ, hΦ⟩ := S.exists_arm_hom F
  refine ⟨Φ, hΦ, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, S.mem_ballStab_two_beta_iff F]
  exact ⟨fun h i => (hΦ g i).1 (congrFun h i), fun h => funext fun i => (hΦ g i).2 (h i)⟩

theorem arm_coords_w (F : FanTree Γ G) (h71c : Fan71c F L)
    (Φ : ↥(nbrStab Γ G S.beta) →* (Fin 3 → (ZMod 5)ˣ))
    (hΦ : ∀ (g : ↥(nbrStab Γ G S.beta)) (i : Fin 3),
      Φ g i = 1 ↔ (g : G) ∈ nbrStab Γ G (S.alphaV i))
    (W W₁ : ↥(nbrStab Γ G S.beta)) (hW : (W : G) = S.w) (hW₁ : (W₁ : G) = S.wA 1) :
    Φ W 0 * Φ W 0 ≠ 1 ∧ Φ W 2 = 1 ∧ Φ W₁ 0 = 1 ∧ Φ W₁ 2 * Φ W₁ 2 ≠ 1 := by
  have hsq : ∀ (x : ↥(nbrStab Γ G S.beta)) (i : Fin 3),
      (x : G) * x ∉ nbrStab Γ G (S.alphaV i) → Φ x i * Φ x i ≠ 1 := fun x i hx h =>
    hx ((hΦ (x * x) i).1 (by rw [map_mul, Pi.mul_apply]; exact h))
  refine ⟨hsq W 0 (by rw [hW]; exact S.w_sq_not_mem F h71c 0 (by decide)),
    (hΦ W 2).2 (by rw [hW]; exact S.w_mem_alphaV_two F), (hΦ W₁ 0).2 ?_, ?_⟩
  · rw [hW₁]
    have h := (S.wA_one_mem_iff F 2).2 (S.w_mem_alphaV_two F)
    rwa [show (2 : Fin 3) + 1 = 0 from rfl] at h
  · refine hsq W₁ 2 fun h => S.w_sq_not_mem F h71c 1 (by decide) ?_
    rw [hW₁] at h
    have h1 : S.wA 1 * S.wA 1 ∈ nbrStab Γ G (S.alphaV (1 + 1)) := h
    exact (S.wA_one_sq_mem_iff F 1).1 h1

theorem arm_coords_c (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h512 : Fan512 F L)
    (hc4 : Nat.card S.D.calpha = 4) (Φ : ↥(nbrStab Γ G S.beta) →* (Fin 3 → (ZMod 5)ˣ))
    (hΦ : ∀ (g : ↥(nbrStab Γ G S.beta)) (i : Fin 3),
      Φ g i = 1 ↔ (g : G) ∈ nbrStab Γ G (S.alphaV i))
    (Cc : ↥(nbrStab Γ G S.beta)) (hC : (Cc : G) = S.c) :
    Φ Cc 0 = 1 ∧ Φ Cc 2 = 1 ∧ Φ Cc 1 = -1 := by
  have h71c : Fan71c F L := h7.2.2.1
  have hsq : (Cc : G) * Cc ∈ nbrStab Γ G (S.alphaV 1) := by
    rw [hC, S.c_sq_eq F h71c h512 hc4]
    exact S.z_mem_nbrStab_alphaV F h71c 1
  have hne : (Cc : G) ∉ nbrStab Γ G (S.alphaV 1) := by
    rw [hC]
    exact S.c_not_mem_alphaV_one F h7 h81 h512 hc4
  have h1 : Φ Cc 1 * Φ Cc 1 = 1 := by
    have := (hΦ (Cc * Cc) 1).2 hsq
    rwa [map_mul, Pi.mul_apply] at this
  exact ⟨(hΦ Cc 0).2 (by rw [hC]; exact S.c_mem_alphaV_zero),
    (hΦ Cc 2).2 (by rw [hC]; exact S.c_mem_alphaV_two F h7),
    units_zmod_five_eq_neg_one _ h1 (fun h => hne ((hΦ Cc 1).1 h))⟩

theorem exists_top_iso_two (F : FanTree Γ G) (h7 : Fan7 F L) (_h81 : Fan81 F L)
    (_h512 : Fan512 F L)
    (hidx : (ballStab Γ G 2 S.beta).relIndex (nbrStab Γ G S.beta) = 8 * Nat.card S.D.calpha)
    (hC : Nat.card S.D.calpha = 2) :
    ∃ φ : ↥(nbrStab Γ G S.beta) →* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)),
      Function.Surjective φ ∧
        φ.ker = (ballStab Γ G 2 S.beta).subgroupOf (nbrStab Γ G S.beta) := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨Φ, hΦ, hker⟩ := S.exists_arm_hom_ker F
  let W : ↥(nbrStab Γ G S.beta) := ⟨S.w, S.w_mem_nbrStab_beta F h71c⟩
  let W₁ : ↥(nbrStab Γ G S.beta) := ⟨S.wA 1, S.wA_mem_nbrStab_beta F h71c 1⟩
  obtain ⟨ha0, ha2, hb0, hb2⟩ := S.arm_coords_w F h71c Φ hΦ W W₁ rfl rfl
  have hcard : Φ.ker.index = 16 := by
    rw [hker]
    show (ballStab Γ G 2 S.beta).relIndex (nbrStab Γ G S.beta) = 16
    omega
  obtain ⟨φ, hφ, hφk⟩ := exists_iso_two_of Φ W W₁ ha0 ha2 hb0 hb2 hcard
  exact ⟨φ, hφ, hφk.trans hker⟩

theorem exists_top_iso_four (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h512 : Fan512 F L)
    (hidx : (ballStab Γ G 2 S.beta).relIndex (nbrStab Γ G S.beta) = 8 * Nat.card S.D.calpha)
    (hC : Nat.card S.D.calpha = 4) :
    ∃ φ : ↥(nbrStab Γ G S.beta) →*
        (Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 2)),
      Function.Surjective φ ∧
        φ.ker = (ballStab Γ G 2 S.beta).subgroupOf (nbrStab Γ G S.beta) := by
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨Φ, hΦ, hker⟩ := S.exists_arm_hom_ker F
  let W : ↥(nbrStab Γ G S.beta) := ⟨S.w, S.w_mem_nbrStab_beta F h71c⟩
  let W₁ : ↥(nbrStab Γ G S.beta) := ⟨S.wA 1, S.wA_mem_nbrStab_beta F h71c 1⟩
  let Cc : ↥(nbrStab Γ G S.beta) := ⟨S.c, S.c_mem_nbrStab_beta F h71a h71c⟩
  obtain ⟨ha0, ha2, hb0, hb2⟩ := S.arm_coords_w F h71c Φ hΦ W W₁ rfl rfl
  obtain ⟨hc0, hc2, hc1⟩ := S.arm_coords_c F h7 h81 h512 hC Φ hΦ Cc rfl
  have hcard : Φ.ker.index = 32 := by
    rw [hker]
    show (ballStab Γ G 2 S.beta).relIndex (nbrStab Γ G S.beta) = 32
    omega
  obtain ⟨φ, hφ, hφk⟩ := exists_iso_three_of Φ W W₁ Cc ha0 ha2 hb0 hb2 hc0 hc2 hc1 hcard
  exact ⟨φ, hφ, hφk.trans hker⟩

end Sec9Cfg

end CFSG.Quasithin.Fan86
