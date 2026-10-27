module

public import CFSG.Walter.J1Props.Elt
public import CFSG.Walter.J1Props.ConjCheck

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word

theorem elt_eq_one_iff (w : Word 5) : elt w = 1 ↔ matWord w = 1 := by
  rw [← mat_inj, mat_elt, mat_one]

theorem elt_eq_elt_iff (v w : Word 5) : elt v = elt w ↔ matWord v = matWord w := by
  rw [← mat_inj, mat_elt, mat_elt]

@[expose] def letterWord : ℕ → Word 5
  | 0 => wt
  | 1 => wn
  | 2 => Word.inv wn
  | 3 => wm
  | 4 => Word.inv wm
  | 5 => ws
  | _ => wu

theorem matWord_letterWord (l : ℕ) : matWord (letterWord l) = ConjData.letterMat l ∧
    matWord (Word.inv (letterWord l)) = ConjData.letterInv l := by
  match l with
  | 0 => exact ⟨by decide +kernel, by decide +kernel⟩
  | 1 => exact ⟨by decide +kernel, by decide +kernel⟩
  | 2 => exact ⟨by decide +kernel, by decide +kernel⟩
  | 3 => exact ⟨by decide +kernel, by decide +kernel⟩
  | 4 => exact ⟨by decide +kernel, by decide +kernel⟩
  | 5 => exact ⟨by decide +kernel, by decide +kernel⟩
  | _ + 6 =>
    show matWord wu = matU ∧ matWord (Word.inv wu) = matU
    exact ⟨by decide +kernel, by decide +kernel⟩

theorem exists_conj_eq (j : ℕ) (hj : j < 210) :
    ∃ g : walterJ1, mat (g * tJ * g⁻¹) = ConjData.mats.getD j 1 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · refine ⟨1, ?_⟩
      rw [one_mul, inv_one, mul_one, mat_tJ, ConjData.mats_zero]
    · obtain ⟨hlt, hstep⟩ := ConjData.step j hj hpos
      obtain ⟨g, hg⟩ := ih _ hlt (hlt.trans hj)
      obtain ⟨h1, h2⟩ := matWord_letterWord (ConjData.lab.getD j 0)
      set x := elt (letterWord (ConjData.lab.getD j 0))
      refine ⟨x * g, ?_⟩
      have key : x * g * tJ * (x * g)⁻¹ = x * (g * tJ * g⁻¹) * x⁻¹ := by group
      rw [key, mat_mul, mat_mul, hg, mat_elt, mat_elt_inv, h1, h2, hstep]

theorem le_index_centralizer_tJ : 210 ≤ (Subgroup.centralizer ({tJ} : Set walterJ1)).index := by
  choose g hg using exists_conj_eq
  set C := Subgroup.centralizer ({tJ} : Set walterJ1)
  let f : Fin 210 → walterJ1 ⧸ C := fun j => (g j j.2 : walterJ1 ⧸ C)
  have hf : Function.Injective f := by
    intro i j hij
    have hmem : (g i i.2)⁻¹ * g j j.2 ∈ C := QuotientGroup.eq.mp hij
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hmem
    have he : g i i.2 * tJ * (g i i.2)⁻¹ = g j j.2 * tJ * (g j j.2)⁻¹ := by
      calc g i i.2 * tJ * (g i i.2)⁻¹ =
            g i i.2 * (tJ * ((g i i.2)⁻¹ * g j j.2)) * (g j j.2)⁻¹ := by group
        _ = g i i.2 * (((g i i.2)⁻¹ * g j j.2) * tJ) * (g j j.2)⁻¹ := by rw [← hc]
        _ = g j j.2 * tJ * (g j j.2)⁻¹ := by group
    have hm := congrArg mat he
    rw [hg, hg, List.getD_eq_getElem _ _ (by rw [ConjData.length_mats]; exact i.2),
      List.getD_eq_getElem _ _ (by rw [ConjData.length_mats]; exact j.2)] at hm
    exact Fin.ext (ConjData.mats_nodup.getElem_inj_iff.mp hm)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, ← Subgroup.index_eq_card] at this

theorem card_centralizer_tJ_le :
    Nat.card (Subgroup.centralizer ({tJ} : Set walterJ1)) ≤ 836 := by
  have h := (Subgroup.centralizer ({tJ} : Set walterJ1)).card_mul_index
  rw [card_walterJ1] at h
  have h2 := le_index_centralizer_tJ
  by_contra hc
  have : 837 * 210 ≤ Nat.card (Subgroup.centralizer ({tJ} : Set walterJ1)) *
      (Subgroup.centralizer ({tJ} : Set walterJ1)).index := Nat.mul_le_mul (by omega) h2
  omega

end CFSG.Walter.J1Props
