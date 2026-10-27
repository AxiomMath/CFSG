module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T2b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KRed
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94T2a

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem top_lower (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) (h512 : Fan512 F L) :
    8 * Nat.card S.D.calpha ≤ (ballStab Γ G 2 S.beta).relIndex
      (Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta) := by
  classical
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  have h75 : Fan75 F L := h7.2.2.2.2.2.2.2.2
  obtain ⟨Φ, hΦ⟩ := S.exists_arm_hom F
  have hG2K : ballStab Γ G 2 S.beta ≤ nbrStab Γ G S.beta := fun g hg =>
    mem_nbrStab.2 fun u hu => mem_ballStab.1 hg u (by
      rw [SimpleGraph.dist_eq_one_iff_adj.2 hu]
      norm_num)
  have hHK : Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta ≤
      nbrStab Γ G S.beta := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) hG2K
    rintro x (rfl | rfl | rfl)
    exacts [S.w_mem_nbrStab_beta F h71c, S.wA_mem_nbrStab_beta F h71c 1,
      S.c_mem_nbrStab_beta F h71a h71c]
  have : Finite ↥(Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta) := by
    have : Finite ↥(MulAction.stabilizer G S.beta) := F.loc_finite S.beta
    exact Finite.of_injective
      (Subgroup.inclusion (hHK.trans (F.nbrStab_le_stabilizer S.beta)))
      (Subgroup.inclusion_injective _)
  let Ψ := Φ.comp (Subgroup.inclusion hHK)
  have hΨ : ∀ x i, Ψ x i = 1 ↔ (x : G) ∈ nbrStab Γ G (S.alphaV i) := fun x i =>
    hΦ (Subgroup.inclusion hHK x) i
  have hker : ∀ h : ↥(Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta),
      (h : G) ∈ ballStab Γ G 2 S.beta → Ψ h = 1 := fun h hh =>
    funext fun i => (hΨ h i).2 ((S.mem_ballStab_two_beta_iff F).1 hh i)
  have hmul : ∀ (x y : ↥(Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta))
      (i : Fin 3), Ψ (x * y) i = Ψ x i * Ψ y i := fun x y i => by simp [map_mul]
  have hsqne : ∀ (x : ↥(Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔
      ballStab Γ G 2 S.beta)) (i : Fin 3), (x : G) * x ∉ nbrStab Γ G (S.alphaV i) →
      Ψ x i * Ψ x i ≠ 1 := fun x i hx h =>
    hx ((hΨ (x * x) i).1 (by rw [hmul]; exact h))
  have hgen : ∀ y ∈ ({S.w, S.wA 1, S.c} : Set G), y ∈
      Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta := fun y hy =>
    Subgroup.mem_sup_left (Subgroup.subset_closure hy)
  let W : ↥(Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta) :=
    ⟨S.w, hgen _ (by simp)⟩
  let V : ↥(Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta) :=
    ⟨S.wA 1, hgen _ (by simp)⟩
  let Cc : ↥(Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta) :=
    ⟨S.c, hgen _ (by simp)⟩
  have ha0 : Ψ W 0 * Ψ W 0 ≠ 1 := hsqne W 0 (S.w_sq_not_mem F h71c 0 (by decide))
  have ha2 : Ψ W 2 = 1 := (hΨ W 2).2 (S.w_mem_alphaV_two F)
  have hb0 : Ψ V 0 = 1 := (hΨ V 0).2 (by
    have h := (S.wA_one_mem_iff F 2).2 (S.w_mem_alphaV_two F)
    rwa [show (2 : Fin 3) + 1 = 0 from rfl] at h)
  have hb2 : Ψ V 2 * Ψ V 2 ≠ 1 := by
    refine hsqne V 2 fun h => S.w_sq_not_mem F h71c 1 (by decide) ?_
    have h1 : S.wA 1 * S.wA 1 ∈ nbrStab Γ G (S.alphaV (1 + 1)) := h
    exact (S.wA_one_sq_mem_iff F 1).1 h1
  rcases Sec8P2K.card_calpha_two_or_four S.D F h71a h71c h75 with h2 | h4
  · have hinj : Function.Injective
        (fun p : Fin 4 × Fin 4 => Ψ (W ^ (p.1 : ℕ) * V ^ (p.2 : ℕ))) := by
      intro p q hpq
      apply pow_inj_two ha0 ha2 hb0 hb2
      simpa only [map_mul, map_pow] using hpq
    have := card_le_relIndex Ψ hker (fun p : Fin 4 × Fin 4 => W ^ (p.1 : ℕ) * V ^ (p.2 : ℕ)) hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin] at this
    omega
  · have hc0 : Ψ Cc 0 = 1 := (hΨ Cc 0).2 S.c_mem_alphaV_zero
    have hc2 : Ψ Cc 2 = 1 := (hΨ Cc 2).2 (S.c_mem_alphaV_two F h7)
    have hc1 : Ψ Cc 1 = -1 := by
      have hsq : (Cc : G) * Cc ∈ nbrStab Γ G (S.alphaV 1) := by
        show S.c * S.c ∈ nbrStab Γ G (S.alphaV 1)
        rw [S.c_sq_eq F h71c h512 h4]
        exact S.z_mem_nbrStab_alphaV F h71c 1
      have hne : (Cc : G) ∉ nbrStab Γ G (S.alphaV 1) := S.c_not_mem_alphaV_one F h7 h81 h512 h4
      have h1 : Ψ Cc 1 * Ψ Cc 1 = 1 := by
        rw [← hmul]
        exact (hΨ (Cc * Cc) 1).2 hsq
      exact units_zmod_five_eq_neg_one _ h1 (fun h => hne ((hΨ Cc 1).1 h))
    have hinj : Function.Injective (fun p : Fin 4 × Fin 4 × Fin 2 =>
        Ψ (W ^ (p.1 : ℕ) * V ^ (p.2.1 : ℕ) * Cc ^ (p.2.2 : ℕ))) := by
      intro p q hpq
      apply pow_inj_three ha0 ha2 hb0 hb2 hc0 hc2 hc1
      simpa only [map_mul, map_pow] using hpq
    have := card_le_relIndex Ψ hker (fun p : Fin 4 × Fin 4 × Fin 2 =>
      W ^ (p.1 : ℕ) * V ^ (p.2.1 : ℕ) * Cc ^ (p.2.2 : ℕ)) hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin] at this
    omega

end Sec9Cfg

end CFSG.Quasithin.Fan86
