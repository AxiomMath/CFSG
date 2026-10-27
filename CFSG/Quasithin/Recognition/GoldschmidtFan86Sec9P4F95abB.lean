module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F95abA

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem f95b (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L) (h512 : Fan512 F L)
    (hc4 : Nat.card S.D.calpha = 4) :
    ∃ d₁ d₂ d₃ d₄ : Fin 2, S.cA 1 = S.yEta 1 * S.yEta 3 * S.zMu1 3 * S.c *
      S.zMu1 0 ^ (d₁ : ℕ) * S.zMu1 2 ^ (d₂ : ℕ) * S.zMu1 4 ^ (d₃ : ℕ) * L.z S.α ^ (d₄ : ℕ) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hR := S.p1Rel_of F h71c h8.fan82.1 h8.fan83b h8.fan83d h8.fan85
  have hC := S.p1cRel_of F h71c h7.1 h512 h8.fan83c hc4
  have hT := S.f95_labelTriple F h71c
  have hza : L.z S.α ≠ 1 := L.z_ne_one S.D.val
  have hsqc := S.f95_cA_sq F h71c h512 hc4
  have hk : kstar (2 : Fin 5) 0 = 3 ∧ midlab (2 : Fin 5) 0 = 1 := by decide
  have hsqc' : S.cA 1 * S.cA 1 = L.z (S.D.alpha 2) ^ ((1 : Fin 2) : ℕ) *
      L.z (S.D.alpha 0) ^ ((0 : Fin 2) : ℕ) * L.z S.α ^ ((1 : Fin 2) : ℕ) := by
    simp only [Fin.val_one, Fin.val_zero, pow_one, pow_zero, mul_one]
    exact hsqc
  rcases h8.fan87 S.α S.D S.η' S.isBeta.pair 2 0 (by decide) (S.cA 1)
      (S.f95_cA_fixes_path F h7.1 h71c) (S.f95_cA_orderOf hc4) ⟨1, 0, 1, hsqc'⟩ with
    ⟨v, hv, e, hw, hww⟩ | ⟨v, hv, c', hc', ho, e, hw, hww⟩ | ⟨v, hv, c', hc', ho, e, hw, hww⟩ |
      ⟨v, hv, c', hc', ho, hw, hww⟩
  · exact (hT.excA e.2 (hww.symm.trans hsqc)).elim
  · obtain ⟨m, rfl⟩ := S.f95_c_cases F h71c h512 hc4 hc' ho
    have hE : L.zGroup 2 S.α ≤ Sec9P4F95Alg.Esub hR :=
      S.D.zGroup_two_le F h71c h512 (fun j => Sec9P4F95Alg.z_mem_Esub hR j)
        (Sec9P4F95Alg.za_mem_Esub hR)
    obtain ⟨a₀, a₁, a₂, a₃, b, rfl⟩ := (Sec9P4F95Alg.mem_Esub hR).1 (hE hv)
    rw [hk.1, hk.2] at hw
    have hw' : S.cA 1 = S.yEta 3 * S.yEta 1 *
        Sec9P4F95Alg.Ee S.zMu1 (L.z S.α) a₀ a₁ a₂ a₃ (b + m) * S.c := by
      rw [hw, mul_assoc _ (Sec9P4F95Alg.Ee S.zMu1 (L.z S.α) a₀ a₁ a₂ a₃ b),
        Sec9P4F95Alg.absorb hC, ← mul_assoc]
      rfl
    rw [hw'] at hsqc
    obtain ⟨d₁, d₂, d₃, d₄, he⟩ := Sec9P4F95Alg.shape_b hR hC hza hsqc
    exact ⟨d₁, d₂, d₃, d₄, hw'.trans he⟩
  · exact (hT.excC e.2 (hww.symm.trans hsqc)).elim
  · exact (hT.excD (hww.symm.trans hsqc)).elim

end Sec9Cfg

theorem fan_9_5b {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h8 : Fan8Parts F L)
    (h512 : Fan512 F L) : Fan95b F L := fun S hc4 => S.f95b F h7 h8 h512 hc4

theorem fan_9_5 {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h8 : Fan8Parts F L)
    (h512 : Fan512 F L) (h95c : Fan95c F L) (h95d : Fan95d F L) : Fan95 F L :=
  ⟨fan_9_5a h7 h8 h512, fan_9_5b h7 h8 h512, h95c, h95d⟩

end CFSG.Quasithin.Fan86
