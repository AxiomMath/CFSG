module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95abLab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95Sh
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Parts
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95abGeo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem f95a_one (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h512 : Fan512 F L)
    (hsq : S.w * S.w = S.zEta13 * L.z S.α) :
    ∃ e₁ e₂ e₃ e₄ : Fin 2, S.wA 1 = S.yEta 3 * S.yEta 4 * S.zMu1 3 * S.zMu1 0 ^ (e₁ : ℕ) *
      S.zMu1 1 ^ (e₂ : ℕ) * S.zMu1 2 ^ (e₃ : ℕ) * L.z S.α ^ (e₄ : ℕ) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hR := S.p1Rel_of F h71c h8.fan82.1 h8.fan83b h8.fan83d h8.fan85
  have hT := S.f95_labelTriple F h71c
  have hza : L.z S.α ≠ 1 := L.z_ne_one S.D.val
  have hsqA := S.f95_wA_sq_one F h512 hsq
  have hk : kstar (2 : Fin 5) 0 = 3 ∧ kstar (0 : Fin 5) 2 = 4 := by decide
  have hsqA' : S.wA 1 * S.wA 1 = L.z (S.D.alpha 2) ^ ((1 : Fin 2) : ℕ) *
      L.z (S.D.alpha 0) ^ ((1 : Fin 2) : ℕ) * L.z S.α ^ ((1 : Fin 2) : ℕ) := by
    simp only [Fin.val_one, pow_one]
    rw [hsqA]
    exact congrArg (· * L.z S.α) hT.pq
  rcases h8.fan87 S.α S.D S.η' S.isBeta.pair 2 0 (by decide) (S.wA 1)
      (S.f95_wA_fixes_path F) (S.f95_wA_orderOf F h71c) ⟨1, 1, 1, hsqA'⟩ with
    ⟨v, hv, e, hw, hww⟩ | ⟨v, hv, c', hc', ho, e, hw, hww⟩ | ⟨v, hv, c', hc', ho, e, hw, hww⟩ |
      ⟨v, hv, c', hc', ho, hw, hww⟩
  · have hE : L.zGroup 2 S.α ≤ Sec9P4F95Alg.Esub hR :=
      S.D.zGroup_two_le F h71c h512 (fun j => Sec9P4F95Alg.z_mem_Esub hR j)
        (Sec9P4F95Alg.za_mem_Esub hR)
    obtain ⟨a₀, a₁, a₂, a₃, b, rfl⟩ := (Sec9P4F95Alg.mem_Esub hR).1 (hE hv)
    rw [hk.1, hk.2] at hw
    rw [hw] at hsqA
    obtain ⟨e₁, e₂, e₃, e₄, he⟩ := Sec9P4F95Alg.shape_a hR hza hsqA
    exact ⟨e₁, e₂, e₃, e₄, hw.trans he⟩
  · exact (hT.ex1b e.2 (hww.symm.trans hsqA)).elim
  · exact (hT.ex1c e.2 (hww.symm.trans hsqA)).elim
  · exact (hT.ex1d (hww.symm.trans hsqA)).elim

theorem f95a_zero (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h512 : Fan512 F L)
    (hsq : S.w * S.w = S.zEta13) :
    Nat.card S.D.calpha = 4 ∧ ∃ e₁ e₂ e₃ e₄ : Fin 2, S.wA 1 = S.yEta 1 * S.yEta 4 * S.c *
      S.zMu1 0 ^ (e₁ : ℕ) * S.zMu1 2 ^ (e₂ : ℕ) * S.zMu1 3 ^ (e₃ : ℕ) * L.z S.α ^ (e₄ : ℕ) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hR := S.p1Rel_of F h71c h8.fan82.1 h8.fan83b h8.fan83d h8.fan85
  have hT := S.f95_labelTriple F h71c
  have hza : L.z S.α ≠ 1 := L.z_ne_one S.D.val
  have hsqA := S.f95_wA_sq_zero F hsq
  have hk : kstar (0 : Fin 5) 2 = 4 ∧ midlab (2 : Fin 5) 0 = 1 := by decide
  have hsqA' : S.wA 1 * S.wA 1 = L.z (S.D.alpha 2) ^ ((0 : Fin 2) : ℕ) *
      L.z (S.D.alpha 0) ^ ((1 : Fin 2) : ℕ) * L.z S.α ^ ((0 : Fin 2) : ℕ) := by
    simp only [Fin.val_one, Fin.val_zero, pow_one, pow_zero, one_mul, mul_one]
    exact hsqA
  rcases h8.fan87 S.α S.D S.η' S.isBeta.pair 2 0 (by decide) (S.wA 1)
      (S.f95_wA_fixes_path F) (S.f95_wA_orderOf F h71c) ⟨0, 1, 0, hsqA'⟩ with
    ⟨v, hv, e, hw, hww⟩ | ⟨v, hv, c', hc', ho, e, hw, hww⟩ | ⟨v, hv, c', hc', ho, e, hw, hww⟩ |
      ⟨v, hv, c', hc', ho, hw, hww⟩
  · exact (hT.ex0a e.2 (hww.symm.trans hsqA)).elim
  · exact (hT.ex0b e.2 (hww.symm.trans hsqA)).elim
  · have hc4 := S.f95_card_eq_four F h8.fan84a hc' ho
    refine ⟨hc4, ?_⟩
    have hC := S.p1cRel_of F h71c h7.1 h512 h8.fan83c hc4
    obtain ⟨m, rfl⟩ := S.f95_c_cases F h71c h512 hc4 hc' ho
    have hE : L.zGroup 2 S.α ≤ Sec9P4F95Alg.Esub hR :=
      S.D.zGroup_two_le F h71c h512 (fun j => Sec9P4F95Alg.z_mem_Esub hR j)
        (Sec9P4F95Alg.za_mem_Esub hR)
    obtain ⟨a₀, a₁, a₂, a₃, b, rfl⟩ := (Sec9P4F95Alg.mem_Esub hR).1 (hE hv)
    rw [hk.1, hk.2] at hw
    have hw' : S.wA 1 = S.yEta 4 * S.yEta 1 *
        Sec9P4F95Alg.Ee S.zMu1 (L.z S.α) a₀ a₁ a₂ a₃ (b + m) * S.c := by
      rw [hw, mul_assoc _ (Sec9P4F95Alg.Ee S.zMu1 (L.z S.α) a₀ a₁ a₂ a₃ b),
        Sec9P4F95Alg.absorb hC, ← mul_assoc]
      rfl
    rw [hw'] at hsqA
    obtain ⟨e₁, e₂, e₃, e₄, he⟩ := Sec9P4F95Alg.shape_c hR hC hza hsqA
    exact ⟨e₁, e₂, e₃, e₄, hw'.trans he⟩
  · exact (hT.pr' (hww.symm.trans hsqA).symm).elim

end Sec9Cfg

theorem fan_9_5a {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h8 : Fan8Parts F L)
    (h512 : Fan512 F L) : Fan95a F L := fun S =>
  ⟨S.f95a_one F h7 h8 h512, S.f95a_zero F h7 h8 h512⟩

end CFSG.Quasithin.Fan86
