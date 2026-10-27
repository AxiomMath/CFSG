module

public import CFSG.LocalAnalysis.StandardType.PhanELocalClsT
public import CFSG.LocalAnalysis.StandardType.PhanELocalLinkB

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

private lemma plh_inf_Vsub_eq_bot_iff_not_sup_le {p H : Submodule K (Fin 4 → K)}
    (hpH : p ≤ H) : H ⊓ Vsub 4 1 = ⊥ ↔ ¬ p ⊔ Vsub 4 1 ≤ H := by
  have hfin1 : finrank K (Vsub (K := K) 4 1) = 1 :=
    finrank_Vsub (K := K) (by norm_num : 1 ≤ 4)
  constructor
  · intro hbot hle
    have hVH : Vsub 4 1 ≤ H := le_trans le_sup_right hle
    have hle' : Vsub 4 1 ≤ H ⊓ Vsub 4 1 := le_inf hVH le_rfl
    rw [hbot, le_bot_iff] at hle'
    have h0 : finrank K (Vsub (K := K) 4 1) = 0 := by rw [hle', finrank_bot]
    omega
  · intro hnot
    by_contra hne
    have hle : H ⊓ Vsub 4 1 ≤ Vsub 4 1 := inf_le_right
    have hpos : finrank K ↥(H ⊓ Vsub 4 1) ≠ 0 := fun h0 =>
      hne (Submodule.finrank_eq_zero.mp h0)
    have hle1 : finrank K ↥(H ⊓ Vsub 4 1) ≤ 1 := by
      have h := Submodule.finrank_mono hle
      rwa [hfin1] at h
    have hfin : finrank K ↥(H ⊓ Vsub 4 1) = 1 := by omega
    have heq : H ⊓ Vsub 4 1 = Vsub 4 1 :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hfin1])
    exact hnot (by rw [← heq]; exact sup_le hpH inf_le_left)

theorem clsT_fibreConn_of_link (D : TData K)
    (hlink : ∀ p L, BFl p L → D.okL p L →
      ∃ L₂ L₃, L₂ ≠ L₃ ∧ BFl p L₂ ∧ BFl p L₃ ∧ D.okL p L₂ ∧ D.okL p L₃) :
    AdmFibreConn (AdmT D) := by
  refine admFibreConn_of_dual_pencil (AdmT D) (fun p => p ⊔ Vsub 4 1)
    (fun p T => D.okL (p.map tailProj) (T.map tailProj)) ?_ ?_ ?_
  · intro p L H hp
    obtain ⟨hflag, hH, -⟩ := hp
    have hpV : p ⊓ Vsub 4 1 = ⊥ := by
      rw [eq_bot_iff]
      calc p ⊓ Vsub 4 1 ≤ H ⊓ Vsub 4 1 := inf_le_inf_right _ (hflag.pL.trans hflag.LH)
        _ = ⊥ := hH
    refine ⟨?_, le_sup_left⟩
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq p (Vsub (K := K) 4 1)
    rw [hflag.p1, finrank_Vsub (K := K) (by norm_num : 1 ≤ 4), hpV, finrank_bot] at hdim
    omega
  · intro p L₀ H₀ _ L H hflag
    have himg : (L ⊔ (p ⊔ Vsub 4 1)).map tailProj = L.map tailProj := by
      rw [map_tailProj_sup, map_tailProj_sup, map_tailProj_Vsub, sup_bot_eq,
        sup_eq_left.mpr (Submodule.map_mono hflag.pL)]
    have hiff := plh_inf_Vsub_eq_bot_iff_not_sup_le (hflag.pL.trans hflag.LH)
    constructor
    · rintro ⟨hH, hok⟩
      exact ⟨hiff.mp hH, by rw [himg]; exact hok⟩
    · rintro ⟨hnot, hok⟩
      exact ⟨hiff.mpr hnot, by rw [himg] at hok; exact hok⟩
  · intro p L₀ H₀ hp
    obtain ⟨hf₀, hH₀, hok₀⟩ := hp
    have hfin1 : finrank K (Vsub (K := K) 4 1) = 1 :=
      finrank_Vsub (K := K) (by norm_num : 1 ≤ 4)
    have hpV : p ⊓ Vsub 4 1 = ⊥ := by
      rw [eq_bot_iff]
      calc p ⊓ Vsub 4 1 ≤ H₀ ⊓ Vsub 4 1 := inf_le_inf_right _ (hf₀.pL.trans hf₀.LH)
        _ = ⊥ := hH₀
    have hL₀V : L₀ ⊓ Vsub 4 1 = ⊥ := by
      rw [eq_bot_iff]
      calc L₀ ⊓ Vsub 4 1 ≤ H₀ ⊓ Vsub 4 1 := inf_le_inf_right _ hf₀.LH
        _ = ⊥ := hH₀
    have hp'1 : finrank K (p.map tailProj) = 1 := by
      rw [finrank_map_tailProj hpV, hf₀.p1]
    have hL₀'2 : finrank K (L₀.map tailProj) = 2 := by
      rw [finrank_map_tailProj hL₀V, hf₀.L2]
    have hL₀'V : L₀.map tailProj ≤ Vtail := by
      rw [Submodule.map_le_iff_le_comap]
      intro v _
      exact tailProj_mem v
    have hfl : BFl (p.map tailProj) (L₀.map tailProj) :=
      ⟨Submodule.map_mono hf₀.pL, hL₀'V, hp'1, hL₀'2⟩
    obtain ⟨L₂', L₃', hne, hfl₂, hfl₃, hok₂, hok₃⟩ :=
      hlink (p.map tailProj) (L₀.map tailProj) hfl hok₀
    have himg₂ : (L₂' ⊔ Vsub 4 1).map tailProj = L₂' := by
      rw [map_tailProj_sup, map_tailProj_Vsub, sup_bot_eq,
        map_tailProj_of_le (S := L₂') hfl₂.2.1]
    have himg₃ : (L₃' ⊔ Vsub 4 1).map tailProj = L₃' := by
      rw [map_tailProj_sup, map_tailProj_Vsub, sup_bot_eq,
        map_tailProj_of_le (S := L₃') hfl₃.2.1]
    have hdisj₂ : L₂' ⊓ Vsub 4 1 = ⊥ := by
      rw [eq_bot_iff]
      calc L₂' ⊓ Vsub 4 1 ≤ Vtail ⊓ Vsub 4 1 := inf_le_inf_right _ hfl₂.2.1
        _ = ⊥ := Vtail_inf_Vsub
    have hdisj₃ : L₃' ⊓ Vsub 4 1 = ⊥ := by
      rw [eq_bot_iff]
      calc L₃' ⊓ Vsub 4 1 ≤ Vtail ⊓ Vsub 4 1 := inf_le_inf_right _ hfl₃.2.1
        _ = ⊥ := Vtail_inf_Vsub
    have hT₂fin : finrank K ↥(L₂' ⊔ Vsub 4 1) = 3 := by
      have hd := Submodule.finrank_sup_add_finrank_inf_eq L₂' (Vsub (K := K) 4 1)
      rw [hdisj₂, finrank_bot, hfl₂.2.2.2, hfin1] at hd
      omega
    have hT₃fin : finrank K ↥(L₃' ⊔ Vsub 4 1) = 3 := by
      have hd := Submodule.finrank_sup_add_finrank_inf_eq L₃' (Vsub (K := K) 4 1)
      rw [hdisj₃, finrank_bot, hfl₃.2.2.2, hfin1] at hd
      omega
    have hpU₂ : p ⊔ Vsub 4 1 ≤ L₂' ⊔ Vsub 4 1 := by
      rw [sup_Vsub_eq_comap (S := p), sup_Vsub_eq_comap (S := L₂'),
        map_tailProj_of_le (S := L₂') hfl₂.2.1]
      exact Submodule.comap_mono hfl₂.1
    have hpU₃ : p ⊔ Vsub 4 1 ≤ L₃' ⊔ Vsub 4 1 := by
      rw [sup_Vsub_eq_comap (S := p), sup_Vsub_eq_comap (S := L₃'),
        map_tailProj_of_le (S := L₃') hfl₃.2.1]
      exact Submodule.comap_mono hfl₃.1
    refine ⟨L₂' ⊔ Vsub 4 1, L₃' ⊔ Vsub 4 1, ?_, ⟨hpU₂, hT₂fin, ?_⟩,
      ⟨hpU₃, hT₃fin, ?_⟩⟩
    · intro heq
      exact hne (by
        have hcongr := congrArg (fun T : Submodule K (Fin 4 → K) => T.map tailProj) heq
        rwa [himg₂, himg₃] at hcongr)
    · rw [himg₂]; exact hok₂
    · rw [himg₃]; exact hok₃

theorem clsT_fibreConn (D : TData K) (h : TBase D) : AdmFibreConn (AdmT D) :=
  clsT_fibreConn_of_link D h.link

end CFSG.ClassicalInvolution.Phan.PhanE

end
