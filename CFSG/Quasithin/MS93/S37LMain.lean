module

public import CFSG.Quasithin.MS93.S37LCase2
public import CFSG.Quasithin.MS93.S37QLine
public import CFSG.Quasithin.MS93.S37SQ

public section

namespace CFSG.Quasithin.MS93.S37L

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.Quasithin.MS93.S37
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def CaseIIQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (C : Cfg M T L F), critDist (puAmalgam C.h.le) = 2 → IsOddRadical M T → C.T0bar = Q₁ F →
      8 ≤ Nat.card F → ∀ ψ : MulAut ↥T, ¬ Uq M T L ≤ Qt M ψ → tImage ψ (T1 M T L) = T1 M T L →
        IsLine (fixSp (C.rhoIm (Ut M T L ψ))) → C.rhoIm (Qt M ψ) = C.rhoIm (Ut M T L ψ)

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  (C : Cfg M T L F)

theorem exists_critical_T1 (hT : C.T0bar = Q₁ F) (hb : critDist (puAmalgam C.h.le) = 2) :
    ∃ ψ : MulAut ↥T, ¬ Uq M T L ≤ Qt M ψ ∧ tImage ψ (T1 M T L) = T1 M T L := by
  obtain ⟨ψ, hcrit, hle⟩ := C.exists_critical_le hb
  obtain ⟨hU, hU'⟩ := C.Ut_le_T1 C.h.pCore_le le_rfl ψ hcrit hle
  have hab : ∀ a ∈ C.T0bar, ∀ b ∈ C.T0bar, a * b = b * a := by
    rw [hT]
    exact fun a ha b hb => Q₁_comm ha hb
  refine ⟨ψ, hcrit, (tImage_T1_eq ψ fun t ht => ?_).2⟩
  exact C.mem_T1_of_comm ψ hcrit hU' (T1_le_T ht) fun x hx => C.comm_of_abelian hab ht (hU hx)

theorem qLineCase_of (hII : CaseIIQ) : S37.QLineCase := by
  intro G _ _ M T L F _ _ C hb hodd hT
  by_contra hk
  have hk3 : 3 ≤ C.k := by have := C.hk; omega
  have hq : 8 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, C.hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ C.k := Nat.pow_le_pow_right (by norm_num) hk3
  obtain ⟨ψ, hcrit, hT1⟩ := exists_critical_T1 C hT hb
  set θ := restr ψ T1_le_T hT1 with hθ
  have hUθ : Ut M T L θ = Ut M T L ψ := tImage_restr ψ T1_le_T hT1 C.Uq_le_T1
  have hQθ : Qt M θ = Qt M ψ := tImage_restr ψ T1_le_T hT1 C.pCore_le_T1
  have hcritθ : ¬ Uq M T L ≤ Qt M θ := by
    rw [hQθ]
    exact hcrit
  rcases C.partner_cases θ hcritθ with ⟨p, hp, hpE⟩ | ⟨hIIθ, -⟩
  · exact C.false_of_caseI_Q₁ hT hq θ hcritθ hp hpE
  · have hNψ := hII G M T L F C hb hodd hT hq ψ hcrit hT1 (by rwa [hUθ] at hIIθ)
    have hNθ : C.rhoIm (Qt M θ) = C.rhoIm (Ut M T L θ) := by
      rw [hQθ, hUθ]
      exact hNψ
    obtain ⟨φ, hcritφ, p, hp, hpE⟩ := exists_caseI_of_caseII C hT θ hcritθ hIIθ hNθ
    exact C.false_of_caseI_Q₁ hT hq φ hcritφ hp hpE

end CFSG.Quasithin.MS93.S37L
