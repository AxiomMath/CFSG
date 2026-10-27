module

public import CFSG.Sporadic.Th.KernelCentJ
public import CFSG.Certificates.Kernel.ThCent.OuterModel
import CFSG.Certificates.Kernel.Th.Spec.Dce
import CFSG.Certificates.Kernel.Th.Spec.DceHsw

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.ThCent CFSG.KC.Th.Spec.DceStr
  CFSG.KC.Th.Spec.Dce CFSG.KC.Th.Gen CFSG.KC.Th.Spec TauCeti Pointwise

theorem outer_P [Finite P] (hP : Nat.card P = thOrder) (hK : Nat.card K ≤ 634023936)
    (D : DceStructData) (hD : dceStructChk D = true) {CJ : ℕ → ℕ} {B MU o r : ℕ} {w : List ℕ}
    (hsh : sharedOK D.ThB_LT B D.ThA_CB CJ D.ThB_om = true) (hmu : muOK MU D.ThB_LT = true)
    (hw14 : ∀ c ∈ w, c < 14) (hTq : outerQ D.ThA_CB MU o r (wordM D.ThB_LT w) = true)
    (n : Fin 11 → ℕ) (hn : ∀ D' : Fin 11, D' ≠ 0 → ((Finset.range (mD D')).filter fun j =>
      outerQ D.ThA_CB MU o r (DceS.mat (tabB D (cosetOrder D')) j) = true).card ≤ n D') :
    ∃ ht : wval gen w ∈ K,
      (∀ g ∈ K, ∀ w' : List ℕ, (∀ c ∈ w', c < 14) →
        g * wval gen w * g⁻¹ = wval gen w' → jv2 MU (wordM D.ThB_LT w') = true) ∧
      ∀ c : ℕ, Nat.card (Subgroup.centralizer ({(⟨wval gen w, ht⟩ : K)} : Set K)) ≤ c →
        Nat.card {p : Om // (wval gen w : P) • p = p} ≤ ∑ D', fixB c n D' := by
  obtain ⟨h1, h2, h3⟩ := hsw_th
  have hrel := hsw_rel_of_pres _ h1 h2 h3
  have hgen := presGen_closure _ h1
  have hG : Nat.card P = 90745943887872000 := hP
  have key := outer_class gen hrel hgen D hD hG hsh hmu hw14 hTq
  rw [← K_eq] at key
  obtain ⟨ht, hinv, v, hv0, hcov, hstab, hcnt⟩ := key
  refine ⟨ht, hinv, fun c hc => ?_⟩
  refine card_fix_le_of hP hv0 hcov (fun D' => ?_) hK ⟨wval gen w, ht⟩ hc n fun D' hD0 => ?_
  · by_cases hD0 : D' = 0
    · subst hD0
      have : (1 : ℕ) ≤ Nat.card (stabK (v 0)) := Nat.card_pos
      exact this
    · exact (hstab D' hD0).ge
  · exact (hcnt D' hD0).trans (hn D' hD0)

end CFSG.Sporadic.Th.Kernel

end
