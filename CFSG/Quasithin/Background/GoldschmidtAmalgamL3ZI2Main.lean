module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Pair
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3WEMod
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3ZI2Norm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem invLeZvProp (hU : Nat.card (conjClosure V B) = 16) : InvLeZvProp A B z V :=
  fun {_ _ _} hβ h1 h2 n {_} hX hinv => h.le_Zv_of_stab_invariant hU hβ h1 h2 n hX hinv

theorem EtilT_sup_le
    (hSw : SwapProp A B)
    {β a a' t' t'' : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (ha : (graph (A ⊔ B) A B).Adj β a) (ha' : (graph (A ⊔ B) A B).Adj β a') (haa' : a ≠ a')
    (ha't' : (graph (A ⊔ B) A B).Adj a' t') (ha't'' : (graph (A ⊔ B) A B).Adj a' t'')
    (nβt' : β ≠ t') (nβt'' : β ≠ t'') (nt't'' : t' ≠ t'')
    (hA : Theta z V a' t' ≤ EtilT V z a ⊔ Vv V β) :
    EtilT V z a' ⊔ Vv V β ≤ EtilT V z a ⊔ Vv V β := by
  have hau : vtype a = false := vtype_eq_false_of_adj ha hβ
  have ha'u : vtype a' = false := vtype_eq_false_of_adj ha' hβ
  obtain ⟨ρ, hρβ, hρa, hρa'⟩ :=
    hSw ha.symm hau ha' haa'.symm
  obtain ⟨g, hgρ, hga', hgβ, hgt⟩ := h.exists_smul_swap ha' ha't' ha't'' nβt' nβt'' nt't'' hρβ hρa'
  have hga : g • a = a := by
    have h1 : ((g : ↥(A ⊔ B)) : D) ∈ stab a := by
      rw [hgρ]
      exact ballStab_le_stab 1 a hρa
    exact smul_eq_of_mem_stab h1
  have hgM : conjSub (g : D) (EtilT V z a ⊔ Vv V β) = EtilT V z a ⊔ Vv V β := by
    rw [conjSub_sup, h.conjSub_EtilT, hga, ← Vv_smul h.natural.reduced.2.1, hgβ]
  have hΘ : Theta z V a' t'' ≤ EtilT V z a ⊔ Vv V β := by
    have e := h.Theta_smul g a' t'
    rw [hga', hgt] at e
    rw [e]
    exact (conjSub_mono _ hA).trans hgM.le
  refine sup_le ?_ le_sup_right
  unfold EtilT
  refine sup_le ?_ (iSup₂_le fun s hs => ?_)
  · exact (Vv_le_Vv_of_adj ha'.symm ha'u).trans le_sup_right
  · rcases h.eq_or_eq_of_adj ha'.symm ha't' ha't'' hs nβt' nβt'' nt't'' with e | e | e
    · subst e
      exact (h.Theta_le_Vv ha'u ha'.symm).trans le_sup_right
    · subst e
      exact hA
    · subst e
      exact hΘ

theorem Theta_le_M_of_class (hU : Nat.card (conjClosure V B) = 16)
    {β a a' t t' : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (ha' : (graph (A ⊔ B) A B).Adj β a')
    (hat : (graph (A ⊔ B) A B).Adj a t) (ha't' : (graph (A ⊔ B) A B).Adj a' t') {θ θ' : D}
    (hθ : θ ∈ Theta z V a t) (hθ' : θ' ∈ Theta z V a' t') (hθU : θ ∉ Vv V β)
    (hθθ' : θ⁻¹ * θ' ∈ Vv V β) : Theta z V a' t' ≤ EtilT V z a ⊔ Vv V β := by
  have ha'u : vtype a' = false := vtype_eq_false_of_adj ha' hβ
  have ht'B : vtype t' = true := vtype_eq_true_of_adj ha't' ha'u
  have hθ'U : θ' ∉ Vv V β := fun hm => hθU (by
    have := (Vv V β).mul_mem hm ((Vv V β).inv_mem hθθ')
    simpa [mul_assoc] using this)
  have hZV : Zv z t' ≤ Vv V β :=
    (h.Zv_le_Vv ha't' ha'u).trans (Vv_le_Vv_of_adj ha'.symm ha'u)
  have hnot : θ' ∉ Zv z t' := fun hm => hθ'U (hZV hm)
  have hU16 : Nat.card (Vv V t') = 16 := h.card_Vv_B_of_card hU ht'B
  have e : Theta z V a' t' = Zv z t' ⊔ Subgroup.zpowers θ' :=
    eq_sup_zpowers_of_card (le_sup_left : Zv z t' ≤ Theta z V a' t') (h.card_Zv ht'B)
      (h.card_Theta ha'u ha't' hU16) hθ' hnot
  rw [e]
  refine sup_le (hZV.trans le_sup_right) (Subgroup.zpowers_le.mpr ?_)
  have e2 : θ' = θ * (θ⁻¹ * θ') := by group
  rw [e2]
  exact (EtilT V z a ⊔ Vv V β).mul_mem (Subgroup.mem_sup_left (Theta_le_EtilT hat hθ))
    (Subgroup.mem_sup_right hθθ')

theorem false_of_pair_class {b : ℕ} (hb : critDist (A ⊔ B) A B V = b) (hb5 : 5 ≤ b)
    (hU : Nat.card (conjClosure V B) = 16)
    (hI1 : ∀ u β β' : CosetGeom (A ⊔ B) A B, vtype u = false →
      (graph (A ⊔ B) A B).Adj u β → (graph (A ⊔ B) A B).Adj u β' → β ≠ β' →
        Vv V β ⊓ Vv V β' ≤ Vv V u)
    (hSw : SwapProp A B)
    {β a a' t t' : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (ha : (graph (A ⊔ B) A B).Adj β a) (ha' : (graph (A ⊔ B) A B).Adj β a') (haa' : a ≠ a')
    (hat : (graph (A ⊔ B) A B).Adj a t) (ha't' : (graph (A ⊔ B) A B).Adj a' t')
    (nβt : β ≠ t) (nβt' : β ≠ t') {θ θ' : D} (hθ : θ ∈ Theta z V a t)
    (hθ' : θ' ∈ Theta z V a' t') (hθU : θ ∉ Vv V β) (hθθ' : θ⁻¹ * θ' ∈ Vv V β) : False := by
  have hau : vtype a = false := vtype_eq_false_of_adj ha hβ
  have hC2 : InvLeZvProp A B z V := h.invLeZvProp hU
  have hθ'U : θ' ∉ Vv V β := fun hm => hθU (by
    have := (Vv V β).mul_mem hm ((Vv V β).inv_mem hθθ')
    simpa [mul_assoc] using this)
  have hθ'θ : θ'⁻¹ * θ ∈ Vv V β := by simpa using (Vv V β).inv_mem hθθ'
  obtain ⟨s, hs, nβs, nts, -⟩ := h.exists_third_nbr (β := a) ha.symm hat nβt
  obtain ⟨s', hs', nβs', nts', -⟩ := h.exists_third_nbr (β := a') ha'.symm ha't' nβt'
  have hA := h.Theta_le_M_of_class hU hβ ha' hat ha't' hθ hθ' hθU hθθ'
  have hB := h.Theta_le_M_of_class hU hβ ha ha't' hat hθ' hθ hθ'U hθ'θ
  have h1 := h.EtilT_sup_le hSw hβ ha ha' haa' ha't' hs' nβt' nβs' nts' hA
  have h2 := h.EtilT_sup_le hSw hβ ha' ha haa'.symm hat hs nβt nβs nts hB
  have heq : EtilT V z a' ⊔ Vv V β = EtilT V z a ⊔ Vv V β := le_antisymm h1 h2
  obtain ⟨a'', ha'', naa'', na'a'', hall⟩ := h.exists_third_nbr ha ha' haa'
  obtain ⟨g₀, ⟨hg0a, hg0β⟩, hg0n⟩ := h.exists_swap_edge hau ha.symm
  have hG₀ : g₀ ∈ A ⊔ B := stab_le a hg0a
  set k : ↥(A ⊔ B) := ⟨g₀, hG₀⟩ with hk
  have hka : k • a = a := smul_eq_of_mem_stab hg0a
  have hkβ : k • β = β := smul_eq_of_mem_stab hg0β
  have hka' : k • a' = a'' := by
    refine h.smul_eq_third ha ha' ha'' haa' naa'' na'a'' hkβ hka fun hfix => hg0n ?_
    exact h.mem_ballStab_one_of_fix_two' ha ha' haa' hg0β hg0a (mem_stab_of_smul_eq hfix)
  have hM'' : EtilT V z a'' ⊔ Vv V β = EtilT V z a ⊔ Vv V β := by
    have e1 : conjSub (k : D) (EtilT V z a' ⊔ Vv V β) = EtilT V z a'' ⊔ Vv V β := by
      rw [conjSub_sup, h.conjSub_EtilT k a', ← Vv_smul h.natural.reduced.2.1, hka', hkβ]
    have e2 : conjSub (k : D) (EtilT V z a ⊔ Vv V β) = EtilT V z a ⊔ Vv V β := by
      rw [conjSub_sup, h.conjSub_EtilT k a, ← Vv_smul h.natural.reduced.2.1, hka, hkβ]
    rw [← e1, heq, e2]
  have hnorm : ∀ g ∈ stab β,
      conjSub g (EtilT V z a ⊔ Vv V β) ≤ EtilT V z a ⊔ Vv V β := by
    intro g hg
    have hG : g ∈ A ⊔ B := stab_le β hg
    set gg : ↥(A ⊔ B) := ⟨g, hG⟩ with hgg
    have hgβ : gg • β = β := smul_eq_of_mem_stab hg
    have hadj : (graph (A ⊔ B) A B).Adj β (gg • a) := by
      have := (smul_adj gg).mpr ha
      rwa [hgβ] at this
    have e : conjSub (gg : D) (EtilT V z a ⊔ Vv V β) = EtilT V z (gg • a) ⊔ Vv V β := by
      rw [conjSub_sup, h.conjSub_EtilT gg a, ← Vv_smul h.natural.reduced.2.1, hgβ]
    show conjSub (gg : D) (EtilT V z a ⊔ Vv V β) ≤ _
    rw [e]
    rcases hall _ hadj with e' | e' | e'
    · rw [e']
    · rw [e', heq]
    · rw [e', hM'']
  exact h.false_of_normal hb hb5 hU hI1 hSw hC2 hβ ha hnorm

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
