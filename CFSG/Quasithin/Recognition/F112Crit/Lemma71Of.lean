module

public import CFSG.Quasithin.Recognition.F112Crit.Lemma71
public import CFSG.Quasithin.MS93.ASGroup

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_oddGen (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oddGen X : Set G) :=
  F7.le_normalizer_closure (S := {x | x ∈ X ∧ Odd (orderOf x)}) fun g hg s hs =>
    ⟨(Subgroup.mem_normalizer_iff.mp hg s).mp hs.1, by
      have := MulEquiv.orderOf_eq (MulAut.conj g) s
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hs.2⟩

namespace Setting

private abbrev kerB (L₁ L₂ S : Subgroup G) : Subgroup G :=
  coreIn (bigB L₁ L₂ S) (P₁ L₁ L₂ S)

private abbrev locX (L₁ L₂ S : Subgroup G) : Subgroup G :=
  oddGen L₁ ⊔ kerB L₁ L₂ S

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

private theorem sylow_le_bigB (L₁ L₂ S : Subgroup G) : S ⊓ L₁ ≤ bigB L₁ L₂ S :=
  (F1.sylow_le_borelOf L₁ S).trans (le_sup_left.trans le_sup_left)

private theorem P₁_le_normalizer_left (h : Hyp111R L₁ L₂ S) :
    P₁ L₁ L₂ S ≤ Subgroup.normalizer (L₁ : Set G) :=
  sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left h).1

private theorem locX_le : locX L₁ L₂ S ≤ P₁ L₁ L₂ S :=
  sup_le ((MS93.oddGen_le L₁).trans le_sup_left) (coreIn_le_left _ _)

private theorem P₁_le_normalizer_locX (h : Hyp111R L₁ L₂ S) :
    P₁ L₁ L₂ S ≤ Subgroup.normalizer (locX L₁ L₂ S : Set G) :=
  F1.le_normalizer_sup ((P₁_le_normalizer_left h).trans (normalizer_le_normalizer_oddGen L₁))
    (le_normalizer_coreIn _ _)

private theorem pCoreOf_le_kerB (h : Hyp111R L₁ L₂ S) : pCoreOf 2 L₁ ≤ kerB L₁ L₂ S :=
  le_coreIn ((pCoreOf_le 2 L₁).trans le_sup_left)
    ((P₁_le_normalizer_left h).trans (normalizer_le_normalizer_pCoreOf 2 L₁))
    ((F7.isSylowTwoOf_pCoreOf_le h.hyp.h1.sylow).trans (sylow_le_bigB L₁ L₂ S))

private theorem locX_inf_le (h : Hyp111R L₁ L₂ S)
    (hQ : oddGen L₁ ⊓ borelOf L₁ S ≤ pCoreOf 2 L₁) :
    locX L₁ L₂ S ⊓ bigB L₁ L₂ S ≤ kerB L₁ L₂ S := by
  rintro z ⟨hzX, hzB⟩
  have hDN : oddGen L₁ ≤ Subgroup.normalizer (kerB L₁ L₂ S : Set G) :=
    (MS93.oddGen_le L₁).trans (le_sup_left.trans (le_normalizer_coreIn _ _))
  obtain ⟨y, hy, n, hn, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hDN).mp hzX
  have hyB : y ∈ bigB L₁ L₂ S := by
    simpa using (bigB L₁ L₂ S).mul_mem hzB ((bigB L₁ L₂ S).inv_mem (coreIn_le_right _ _ hn))
  have hyB₁ : y ∈ borelOf L₁ S := by
    rw [← F1.inf_bigB_eq_borelOf h]
    exact ⟨MS93.oddGen_le L₁ hy, hyB⟩
  exact Subgroup.mul_mem _ (pCoreOf_le_kerB h (hQ ⟨hy, hyB₁⟩)) hn

private theorem locX_sup_bigB (h : Hyp111R L₁ L₂ S) :
    locX L₁ L₂ S ⊔ bigB L₁ L₂ S = P₁ L₁ L₂ S := by
  refine le_antisymm (sup_le locX_le le_sup_right) (sup_le ?_ le_sup_right)
  have hL : L₁ ≤ oddGen L₁ ⊔ (S ⊓ L₁) :=
    F7.isSylowTwoOf_le_sup_of_two_power h.hyp.h1.sylow (MS93.le_normalizer_oddGen L₁)
      fun x hx => MS93.exists_pow_mem_oddGen hx
  exact hL.trans (sup_le (le_sup_left.trans le_sup_left)
    ((sylow_le_bigB L₁ L₂ S).trans le_sup_right))

private theorem relIndex_kerB_locX (h : Hyp111R L₁ L₂ S)
    (hQ : oddGen L₁ ⊓ borelOf L₁ S ≤ pCoreOf 2 L₁) :
    (kerB L₁ L₂ S).relIndex (locX L₁ L₂ S) = (borelOf L₁ S).relIndex L₁ := by
  have hXB : locX L₁ L₂ S ⊓ bigB L₁ L₂ S = kerB L₁ L₂ S :=
    le_antisymm (locX_inf_le h hQ) (le_inf le_sup_right (coreIn_le_right _ _))
  calc (kerB L₁ L₂ S).relIndex (locX L₁ L₂ S)
      = (locX L₁ L₂ S ⊓ bigB L₁ L₂ S).relIndex (locX L₁ L₂ S) := by rw [hXB]
    _ = (bigB L₁ L₂ S).relIndex (locX L₁ L₂ S ⊔ bigB L₁ L₂ S) :=
      (F112W.relIndex_sup_eq_relIndex_inf (le_sup_right.trans (P₁_le_normalizer_locX h))).symm
    _ = (bigB L₁ L₂ S).relIndex (P₁ L₁ L₂ S) := by rw [locX_sup_bigB h]
    _ = (borelOf L₁ S).relIndex L₁ := by
      rw [F112W.relIndex_sup_eq_relIndex_inf (F1.bigB_le_normalizer_left h).1,
        F1.inf_bigB_eq_borelOf h]

private theorem not_bigB_le_kerB (h : Hyp111R L₁ L₂ S) : ¬ bigB L₁ L₂ S ≤ kerB L₁ L₂ S := by
  intro hBN
  have hPB : P₁ L₁ L₂ S ≤ Subgroup.normalizer ((bigB L₁ L₂ S : Subgroup G) : Set G) := by
    have : kerB L₁ L₂ S = bigB L₁ L₂ S := le_antisymm (coreIn_le_right _ _) hBN
    rw [← this]
    exact le_normalizer_coreIn _ _
  have hL₁B : L₁ ≤ Subgroup.normalizer ((borelOf L₁ S : Subgroup G) : Set G) := by
    rw [← F1.inf_bigB_eq_borelOf h]
    exact F7.le_normalizer_inf Subgroup.le_normalizer (le_sup_left.trans hPB)
  have hL₁S : L₁ ≤ Subgroup.normalizer ((S ⊓ L₁ : Subgroup G) : Set G) := by
    have := hL₁B.trans (normalizer_le_normalizer_pCoreOf 2 (borelOf L₁ S))
    rwa [F1.pCoreOf_borelOf h.hyp.h1.sylow] at this
  exact (F1.lt_borelOf h).not_ge (le_inf le_rfl hL₁S)

private theorem relIndex_borelOf_ne_two (h : Hyp111R L₁ L₂ S) : (borelOf L₁ S).relIndex L₁ ≠ 2 :=
  fun h2 => F7.isSylowTwoOf_odd_relIndex h.hyp.h1.sylow
    (h2 ▸ Subgroup.relIndex_dvd_of_le_left L₁ (F1.sylow_le_borelOf L₁ S))

theorem isLocalRegGrp (hs : Setting L₁ L₂ S Z) (hQ : oddGen L₁ ⊓ borelOf L₁ S ≤ pCoreOf 2 L₁) :
    IsLocalRegGrp (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
      (oddGen L₁ ⊔ coreIn (P₂ L₁ L₂ S ⊓ P₁ L₁ L₂ S) (P₁ L₁ L₂ S))
      ((borelOf L₁ S).relIndex L₁) := by
  have h := hs.hyp
  have hinf : P₂ L₁ L₂ S ⊓ P₁ L₁ L₂ S = bigB L₁ L₂ S := F112W.inf_alpha_beta h
  refine ⟨hs.prime, relIndex_borelOf_ne_two h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hinf]
  · exact le_sup_right
  · exact locX_le
  · exact P₁_le_normalizer_locX h
  · exact relIndex_kerB_locX h hQ
  · exact locX_inf_le h hQ
  · exact locX_sup_bigB h
  · exact not_bigB_le_kerB h

end Setting

end CFSG.Quasithin.F112Crit

end
