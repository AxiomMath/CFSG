module

public import CFSG.Quasithin.Background.G93ApplyStmt
public import CFSG.Quasithin.Background.G93ApplyRestrict

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

theorem g93_apply (hG93 : G93StmtDimensionOnly) : G93ApplyStmt := by
  intro V _ _ _ Γ K H L A I m hKI hHI hq hKΓ hHK hHnorm hirr hfH hAK hAelem hAcard hfA hbound
    hL hLH hcomm hHeq
  have hAI : Invariant A I := hKI.mono hAK
  have hLI : Invariant L I := hHI.mono hLH
  have hLK : L ≤ K := hLH.trans hHK
  have hfL : FaithfulOn L I := faithfulOn_of_le hLH hfH
  refine hG93 ↥I (restrictRange K I hKI) (restrictRange A I hAI) (restrictRange L I hLI)
    (restrictRange H I hHI) m
    { quotient := isQuotientOfSQTKTauCeti_restrictRange hKI (hq.of_le hKΓ)
      A_le := restrictRange_mono hAI hKI hAK
      A_elem := isElemAbelian_restrictRange hAI hAelem
      A_card := by rw [natCard_restrictRange hAI hfA]; exact hAcard
      bound := hbound
      L_comp := isComponentOf_restrictRange hKI hLI hKΓ hLK hfL hL
      L_comm := ?_
      H_le := restrictRange_mono hHI hKI hHK
      H_normal := ?_
      H_irr := isIrr_restrictRange_top hirr
      H_eq := ?_ }
  ·
    obtain ⟨a, ha, l, hl, hne⟩ := hcomm
    refine ⟨restrictEquiv a I (hAI.conjSub_eq ha), restrictEquiv_mem_restrictRange hAI ha,
      restrictEquiv l I (hLI.conjSub_eq hl), restrictEquiv_mem_restrictRange hLI hl,
      fun heq => hne ?_⟩
    have hc : a * l * a⁻¹ * l⁻¹ ∈ H :=
      H.mul_mem (hHnorm a (hAK ha) l (hLH hl)) (H.inv_mem (hLH hl))
    have h1 : a * l * a⁻¹ * l⁻¹ = 1 := by
      refine faithfulOn_iff.1 hfH _ hc fun u hu => ?_
      have hu' : (l⁻¹ : GLV V) u ∈ I := hLI l⁻¹ (L.inv_mem hl) u hu
      have hu'' : (a⁻¹ : GLV V) ((l⁻¹ : GLV V) u) ∈ I := hAI a⁻¹ (A.inv_mem ha) _ hu'
      have h2 := congrArg (fun g : GLV ↥I => ((g ⟨_, hu''⟩ : ↥I) : V)) heq
      have h3 : a (l ((a⁻¹ : GLV V) ((l⁻¹ : GLV V) u))) = l (a ((a⁻¹ : GLV V) ((l⁻¹ : GLV V) u))) :=
        h2
      show a (l ((a⁻¹ : GLV V) ((l⁻¹ : GLV V) u))) = u
      rw [h3]
      simp
    have h2 : a * l * a⁻¹ = l := mul_inv_eq_one.1 h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  ·
    intro γ hγ h hh
    obtain ⟨k, hk, rfl⟩ := (mem_restrictRange_iff' hKI).1 hγ
    obtain ⟨h₀, hh₀, rfl⟩ := (mem_restrictRange_iff' hHI).1 hh
    refine (mem_restrictRange_iff' hHI).2 ⟨k * h₀ * k⁻¹, hHnorm k hk h₀ hh₀, ?_⟩
    ext i
    show k (h₀ ((k⁻¹ : GLV V) (i : V))) = (k * h₀ * k⁻¹) (i : V)
    rfl
  ·
    rcases hHeq with hHL | ⟨L₂, hL₂, hne, hHsup, hLI', hL₂I, hqe⟩
    · exact Or.inl (restrictRange_congr hHL hHI hLI)
    · have hL₂H : L₂ ≤ H := hHsup ▸ le_sup_right
      refine Or.inr ⟨restrictRange L₂ I hL₂I, ?_, ?_, ?_, hqe⟩
      · exact isComponentOf_restrictRange hKI hL₂I hKΓ (hL₂H.trans hHK)
          (faithfulOn_of_le hL₂H hfH) hL₂
      · intro h
        exact hne (eq_of_restrictRange_eq hfH hL₂H hLH hL₂I hLI h)
      · rw [restrictRange_congr hHsup hHI (hHsup ▸ hHI)]
        exact restrictRange_sup hLI hL₂I _

end G11

end CFSG.Quasithin
