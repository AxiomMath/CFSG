module

public import CFSG.LocalAnalysis.StandardType.PhanELocalCls
public import CFSG.LocalAnalysis.StandardType.PhanELocalLinkA

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K]

private lemma plh_sup_inf_Vsub {p M : Submodule K (Fin 4 → K)}
    (hp : p ⊓ Vsub 4 2 = ⊥) (hM : M ≤ Vsub 4 2) : (p ⊔ M) ⊓ Vsub 4 2 = M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hxV⟩ := Submodule.mem_inf.mp hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxW
    have haV : a ∈ Vsub 4 2 := by
      have hax : a = x - b := by rw [← hab]; abel
      rw [hax]
      exact Submodule.sub_mem _ hxV (hM hb)
    have ha0 : a = 0 := by
      have : a ∈ p ⊓ Vsub 4 2 := ⟨ha, haV⟩
      rw [hp, Submodule.mem_bot] at this
      exact this
    rw [← hab]
    simpa [ha0] using hb
  · exact le_inf le_sup_right hM

private lemma plh_inf_bot_iff_not_le {p L : Submodule K (Fin 4 → K)}
    (hp : finrank K p = 1) (hL : finrank K L = 2) (hpL : p ≤ L)
    (hpbot : p ⊓ Vsub 4 2 = ⊥) : L ⊓ Vsub 4 2 = ⊥ ↔ ¬ L ≤ p ⊔ Vsub 4 2 := by
  constructor
  · intro hLbot hle
    have h3 : finrank K ↥(p ⊔ Vsub 4 2) = 3 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq p (Vsub 4 2)
      rw [hp, finrank_Vsub (K := K) (by norm_num : 2 ≤ 4), hpbot, finrank_bot] at h
      omega
    have h4 : finrank K ↥(L ⊔ Vsub 4 2) = 4 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq L (Vsub 4 2)
      rw [hL, finrank_Vsub (K := K) (by norm_num : 2 ≤ 4), hLbot, finrank_bot] at h
      omega
    have hle' : L ⊔ Vsub 4 2 ≤ p ⊔ Vsub 4 2 := sup_le hle le_sup_right
    have hmono := Submodule.finrank_mono hle'
    omega
  · intro hnot
    by_contra hne
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (L ⊓ Vsub 4 2)).mp hne
    have hvL : v ∈ L := hv.1
    have hvV : v ∈ Vsub 4 2 := hv.2
    have hvp : v ∉ p := by
      intro hvp
      have hvbot : v ∈ p ⊓ Vsub 4 2 := ⟨hvp, hvV⟩
      rw [hpbot, Submodule.mem_bot] at hvbot
      exact hv0 hvbot
    have hspan : K ∙ v ≤ L := (Submodule.span_singleton_le_iff_mem v L).mpr hvL
    have hfin : finrank K ↥(p ⊔ K ∙ v) = 2 := by
      rw [Submodule.finrank_sup_span_singleton hvp, hp]
    have heq : p ⊔ K ∙ v = L :=
      Submodule.eq_of_le_of_finrank_eq (sup_le hpL hspan) (by rw [hfin, hL])
    apply hnot
    rw [← heq]
    exact sup_le_sup_left ((Submodule.span_singleton_le_iff_mem v (Vsub 4 2)).mpr hvV) p

theorem cls_fibreConn (D : ClsData K) {β : ℕ} (h : ClsHyp D β) : AdmFibreConn (AdmS D) := by
  refine admFibreConn_of_pencil (AdmS D) (fun p => p ⊔ Vsub 4 2)
    (fun p M => D.good (p.map rho) (M ⊓ Vsub 4 2)) ?_ ?_ ?_
  · intro p L H hp
    obtain ⟨hflag, hLbot, -, -⟩ := hp
    have hpbot : p ⊓ Vsub 4 2 = ⊥ := by
      rw [eq_bot_iff]
      calc p ⊓ Vsub 4 2 ≤ L ⊓ Vsub 4 2 := inf_le_inf_right _ hflag.pL
        _ = ⊥ := hLbot
    refine ⟨?_, le_sup_left⟩
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq p (Vsub 4 2)
    rw [hflag.p1, finrank_Vsub (K := K) (by norm_num : 2 ≤ 4), hpbot, finrank_bot] at hdim
    omega
  · intro p L₀ H₀ hp L H hflag
    obtain ⟨hflag₀, hLbot₀, hok, -⟩ := hp
    have hpbot : p ⊓ Vsub 4 2 = ⊥ := by
      rw [eq_bot_iff]
      calc p ⊓ Vsub 4 2 ≤ L₀ ⊓ Vsub 4 2 := inf_le_inf_right _ hflag₀.pL
        _ = ⊥ := hLbot₀
    have hiff := plh_inf_bot_iff_not_le hflag₀.p1 hflag.L2 hflag.pL hpbot
    have hgood_eq : (H ⊓ (p ⊔ Vsub 4 2)) ⊓ Vsub 4 2 = H ⊓ Vsub 4 2 := by
      rw [inf_assoc, inf_eq_right.2 (le_sup_right : Vsub 4 2 ≤ p ⊔ Vsub 4 2)]
    constructor
    · rintro ⟨hLb, -, hgood⟩
      exact ⟨hiff.mp hLb, hgood_eq.symm ▸ hgood⟩
    · rintro ⟨hnotle, hgood⟩
      exact ⟨hiff.mpr hnotle, hok, hgood_eq ▸ hgood⟩
  · intro p L₀ H₀ hp
    obtain ⟨hflag₀, hLbot₀, hok, -⟩ := hp
    have hpbot : p ⊓ Vsub 4 2 = ⊥ := by
      rw [eq_bot_iff]
      calc p ⊓ Vsub 4 2 ≤ L₀ ⊓ Vsub 4 2 := inf_le_inf_right _ hflag₀.pL
        _ = ⊥ := hLbot₀
    have hrank := finrank_map_rho hflag₀.p1 hpbot
    obtain ⟨M₁, M₂, hMne, hM1le, hM2le, hM1fin, hM2fin, hgood1, hgood2⟩ :=
      h.two (p.map rho) hok hrank
    have hdisj₁ : p ⊓ M₁ = ⊥ := by
      rw [eq_bot_iff]
      calc p ⊓ M₁ ≤ p ⊓ Vsub 4 2 := inf_le_inf_left _ hM1le
        _ = ⊥ := hpbot
    have hdisj₂ : p ⊓ M₂ = ⊥ := by
      rw [eq_bot_iff]
      calc p ⊓ M₂ ≤ p ⊓ Vsub 4 2 := inf_le_inf_left _ hM2le
        _ = ⊥ := hpbot
    have hdim₁ : finrank K ↥(p ⊔ M₁) = 2 := by
      have hd := Submodule.finrank_sup_add_finrank_inf_eq p M₁
      rw [hflag₀.p1, hM1fin, hdisj₁, finrank_bot] at hd
      omega
    have hdim₂ : finrank K ↥(p ⊔ M₂) = 2 := by
      have hd := Submodule.finrank_sup_add_finrank_inf_eq p M₂
      rw [hflag₀.p1, hM2fin, hdisj₂, finrank_bot] at hd
      omega
    refine ⟨p ⊔ M₁, p ⊔ M₂, ?_, ?_, ?_⟩
    · intro heq
      apply hMne
      calc M₁ = (p ⊔ M₁) ⊓ Vsub 4 2 := (plh_sup_inf_Vsub hpbot hM1le).symm
        _ = (p ⊔ M₂) ⊓ Vsub 4 2 := by rw [heq]
        _ = M₂ := plh_sup_inf_Vsub hpbot hM2le
    · exact ⟨le_sup_left, sup_le le_sup_left (hM1le.trans le_sup_right), hdim₁,
        by rw [plh_sup_inf_Vsub hpbot hM1le]; exact hgood1⟩
    · exact ⟨le_sup_left, sup_le le_sup_left (hM2le.trans le_sup_right), hdim₂,
        by rw [plh_sup_inf_Vsub hpbot hM2le]; exact hgood2⟩

end CFSG.ClassicalInvolution.Phan.PhanE

end
