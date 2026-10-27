module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen
public import CFSG.CGT.PushingUpLit.BHS.GlaubOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 CFSG.LocalAnalysis.UniquenessCase.UC22.F14
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace SeventeenSixteen

theorem delta_le_M (D : Data G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) :
    (⨆ H ∈ Delta17_12 D 𝔉 r q L, H) ≤ D.M := by
  have hLM : L ≤ D.M := hC.memL.1.le
  unfold Delta17_12
  by_cases h1 : P17_12_1 r q L
  · rw [dif_pos h1]
    refine iSup₂_le ?_
    rintro H ⟨x, hx, rfl⟩
    exact sup_le D.sylowM.le (CFSG.CGT.PushingUpLit.BHS.Glauberman.map_conj_le hx hLM)
  · by_cases h2 : P17_12_2 q L
    · rw [dif_neg h1, dif_pos h2]
      refine iSup₂_le ?_
      rintro H ⟨X, hXL, -, -, rfl⟩
      exact sup_le D.sylowM.le (hXL.trans hLM)
    · rw [dif_neg h1, dif_neg h2]
      refine iSup₂_le ?_
      rintro H ⟨x, hx, X, hconj⟩
      obtain ⟨hXL, -, hH, -⟩ := hconj
      rw [hH]
      exact sup_le D.sylowM.le
        (hXL.trans (CFSG.CGT.PushingUpLit.BHS.Glauberman.map_conj_le hx hLM))

end SeventeenSixteen

theorem seventeen_sixteen_case_one (D : Data G)
    (𝔉 : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h1 : P17_12_1 r q L)
    (h17_7 : R17_7At D V₀ V L r q hC) :
    R17_16At D 𝔉 V₀ V L r q hC := by
  show UniqueMax D.M (⨆ H ∈ Delta17_12 D 𝔉 r q L, H)
  rw [Delta17_12, dif_pos h1]
  set S : Subgroup G :=
    ⨆ H ∈ {H : Subgroup G | ∃ x ∈ D.M, H = D.T ⊔ L.map (MulAut.conj x).toMonoidHom}, H
  have hLM : L ≤ D.M := hC.memL.1.le
  have hHle : ∀ H ∈ {H : Subgroup G |
      ∃ x ∈ D.M, H = D.T ⊔ L.map (MulAut.conj x).toMonoidHom}, H ≤ D.M := by
    rintro H ⟨x, hx, rfl⟩
    exact sup_le D.sylowM.le (CFSG.CGT.PushingUpLit.BHS.Glauberman.map_conj_le hx hLM)
  have hSM : S ≤ D.M := iSup₂_le hHle
  have hH0 : D.T ⊔ L.map (MulAut.conj (1 : G)).toMonoidHom ∈
      {H : Subgroup G | ∃ x ∈ D.M, H = D.T ⊔ L.map (MulAut.conj x).toMonoidHom} :=
    ⟨1, D.M.one_mem, by simp⟩
  have hLH0 : L ≤ D.T ⊔ L.map (MulAut.conj (1 : G)).toMonoidHom := by
    have hconj1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext l; simp [MulAut.conj_apply]
    rw [hconj1, Subgroup.map_id]
    exact le_sup_right
  have hLS : L ≤ S := hLH0.trans (le_iSup₂_of_le _ hH0 le_rfl)
  exact CFSG.LocalAnalysis.WeakClosure81.InCalU.mono D.maxLocal h17_7.1 hLS hSM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
