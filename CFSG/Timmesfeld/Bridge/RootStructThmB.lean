module

public import CFSG.Timmesfeld.Bridge.RootStructThmA
public import CFSG.Timmesfeld.Bridge.RootStructOD
public import CFSG.Timmesfeld.Bridge.RootStructQCenter
public import CFSG.Timmesfeld.Bridge.RootSetsGate

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem exists_special_of_mem_twoCore [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hOD : OppositeDetermines D) {d s : G} (hd : d ∈ D)
    (hs : s ∈ D) (hsQ : s ∈ Moufang.twoCore d) (hsT : s ∉ rootSet D d) :
    ∃ t ∈ D, t ∈ Moufang.twoCore d ∧ orderOf (s * t) = 4 := by
  by_contra! hall
  refine hsT (mem_rootSet_of_mem_twoCore_of_forall_commute hclass hD hOD hd hs hsQ
    fun t ht htQ => ?_)
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hs ht with h | h | ⟨h, h'⟩
  · exact h
  · exact absurd h (hall t ht htQ)
  · exact absurd ⟨h', h⟩ (not_opposite_of_mem_twoCore hsQ htQ)

theorem sq_mem_rootSet_of_mem_twoCore [Finite G] (hD : IsRootInvolutionSet D)
    (hc : RootClosure D) (hR : NCoreCommutatorInRoot D) {d s t : G} (hd : d ∈ D) (hs : s ∈ D)
    (ht : t ∈ D) (hsQ : s ∈ Moufang.twoCore d) (htQ : t ∈ Moufang.twoCore d)
    (h4 : orderOf (s * t) = 4) : (s * t) ^ 2 ∈ rootSet D d := by
  have hsqD := hD.sq_mem hs ht h4
  have hmem := hR d hd s (mem_nCore_of_mem_twoCore hs hsQ) t (mem_nCore_of_mem_twoCore ht htQ)
  rw [hD.inv_eq hs, hD.inv_eq ht, show s * t * s * t = (s * t) ^ 2 by rw [sq]; group] at hmem
  exact mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hd hmem (hD.ne_one hsqD)

theorem mem_rootSet_or_collinear_of_mem_twoCore [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hOD : OppositeDetermines D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hR : NCoreCommutatorInRoot D) {d s : G} (hd : d ∈ D) (hsD : s ∈ D)
    (hsQ : s ∈ Moufang.twoCore d) : s ∈ rootSet D d ∨ (Commute d s ∧ d * s ∈ D) := by
  by_cases hsT : s ∈ rootSet D d
  · exact Or.inl hsT
  right
  obtain ⟨t, ht, htQ, h4⟩ := exists_special_of_mem_twoCore hclass hD hOD hd hsD hsQ hsT
  have hw := sq_mem_rootSet_of_mem_twoCore hD hc hR hd hsD ht hsQ htQ h4
  obtain ⟨-, h2, -⟩ := hs.rootSet_of_special hclass hD hc hsD ht h4
  obtain ⟨b, hb, hsb⟩ := h2 s (mem_rootSet_self hsD) d (mem_rootSet_comm hd hw)
  have hs2 := hD.mul_self_eq_one hsD
  have hb2 := hD.mul_self_eq_one hb.1
  have hds : Commute d s := (Moufang.commute_of_mem_twoCore hsQ).symm
  refine ⟨hds, ?_⟩
  have hsd : s * d = b * s * b := by
    rw [← hsb, sq, show s * (s * b * (s * b)) = (s * s) * b * s * b by group, hs2, one_mul]
  rw [hds.eq, hsd]
  simpa [hD.inv_eq hb.1] using conj_mem_of_isClass hclass b hsD

theorem mul_mem_of_mem_rootGroup (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hR : NCoreCommutatorInRoot D) {b c : G} (hb : b ∈ D) (hcD : c ∈ D) (hbc : Commute b c)
    (hbcD : b * c ∈ D) (hcT : c ∉ rootSet D b) {β γ : G} (hβ : β ∈ rootGroup D b)
    (hγ : γ ∈ rootGroup D c) (hne : β ≠ 1 ∨ γ ≠ 1) : β * γ ∈ D := by
  have := h.finite
  have hD := h.root
  have hOD := oppositeDetermines_of_hyp h
  have hcQ : c ∈ Moufang.twoCore b :=
    mem_twoCore_of_collinear h.isClass hD hb hcD hbc.symm (by rw [← hbc.eq]; exact hbcD)
  obtain ⟨t, ht, htQ, h4⟩ := exists_special_of_mem_twoCore h.isClass hD hOD hb hcD hcQ hcT
  have hw := sq_mem_rootSet_of_mem_twoCore hD hc hR hb hcD ht hcQ htQ h4
  have hβ' : β ∈ rootGroup D ((c * t) ^ 2) := by rwa [rootGroup_eq_of_mem hw]
  have hγβ := mem_of_mem_line h hc hs hcD ht h4 hγ hβ' hne.symm
  rwa [(commute_of_mem_rootGroup_of_commute' hcD hβ hγ hbc).eq]

theorem exists_mul_eq_of_mem_sup {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, Commute h k)
    {x : G} (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, K.one_mem, (mul_one y).symm⟩
    · exact ⟨1, H.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := ihy
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := ihz
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    rw [mul_assoc, ← mul_assoc k₁, ← (hHK h₂ hh₂ k₁ hk₁).eq]
    group
  | inv y _ ihy =>
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := ihy
    refine ⟨h₁⁻¹, H.inv_mem hh₁, k₁⁻¹, K.inv_mem hk₁, ?_⟩
    rw [mul_inv_rev, ((hHK h₁ hh₁ k₁ hk₁).inv_inv).eq]

theorem rootSet_subset_twoCore_self [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) {b : G} (hb : b ∈ D) :
    ∀ e ∈ rootSet D b, e ∈ D ∧ e ∈ Moufang.twoCore b := by
  intro e he
  refine ⟨he.1, ?_⟩
  by_cases heb : e = b
  · rw [heb]
    exact self_mem_twoCore (hD.orderOf_eq_two hb)
  · exact mem_twoCore_of_collinear hclass hD hb he.1
      (commute_of_mem_rootSet hb he (mem_rootSet_self hb))
      (hc b hb e he b (mem_rootSet_self hb) heb).1

theorem rootSet_subset_twoCore_of_collinear (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hR : NCoreCommutatorInRoot D) {b c : G} (hb : b ∈ D) (hcD : c ∈ D)
    (hbc : Commute b c) (hbcD : b * c ∈ D) (hcT : c ∉ rootSet D b) :
    ∀ γ ∈ rootSet D c, γ ∈ D ∧ γ ∈ Moufang.twoCore b := by
  have := h.finite
  intro γ hγ
  have hγb : Commute γ b := (hγ.2 b hb).2 hbc.symm
  refine ⟨hγ.1, mem_twoCore_of_collinear h.isClass h.root hb hγ.1 hγb ?_⟩
  have := mul_mem_of_mem_rootGroup h hc hs hR hb hcD hbc hbcD hcT
    (rootSet_subset_rootGroup D b (mem_rootSet_self hb)) (rootSet_subset_rootGroup D c hγ)
    (Or.inl (h.root.ne_one hb))
  rwa [← hγb.eq] at this

theorem rootGroup_le_nCore {b c : G}
    (h : ∀ γ ∈ rootSet D c, γ ∈ D ∧ γ ∈ Moufang.twoCore b) : rootGroup D c ≤ nCore D b :=
  Subgroup.closure_mono fun γ hγ => h γ hγ

theorem oneOpposite_of_collinear_off_line (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hR : NCoreCommutatorInRoot D) {a b c c' x : G} (ha : a ∈ D)
    (hb : b ∈ D) (hcD : c ∈ D) (hc' : c' ∈ D) (hx : x ∈ D) (hab : Commute a b) (habD : a * b ∈ D)
    (hbc : Commute b c) (hbcD : b * c ∈ D) (hbc' : Commute b c') (hbc'D : b * c' ∈ D)
    (hcc' : Commute c c') (hcc'D : c * c' ∈ D) (hoff : c' ∉ rootGroup D b ⊔ rootGroup D c)
    (hbx : ¬ Commute b x) (hoddbx : Odd (orderOf (b * x))) (hax : ¬ Commute a x)
    (hoddax : Odd (orderOf (a * x))) (hxc : orderOf (x * c) = 4) : OneOpposite D a x := by
  have := h.finite
  have hD := h.root
  have hOD := oppositeDetermines_of_hyp h
  have hclass := h.isClass
  have hcT : c ∉ rootSet D b := fun hcT => by
    have h1 := (orderOf_mul_eq_four_iff_of_mem_rootSet hD hb hcT hx).1
      ((orderOf_mul_comm_eq x c).trans hxc)
    rw [h1] at hoddbx
    exact absurd hoddbx (by decide)
  have hoffb : ∀ y ∈ rootSet D b, c' ≠ y := fun y hy hc'y =>
    hoff (Subgroup.mem_sup_left (by rw [hc'y]; exact rootSet_subset_rootGroup D b hy))
  have hc'T : c' ∉ rootSet D c := fun h' =>
    hoff (Subgroup.mem_sup_right (rootSet_subset_rootGroup D c h'))
  have hc'Tb : c' ∉ rootSet D b := fun h' => hoffb c' h' rfl
  have hbT : b ∉ rootSet D c := fun h' => hcT (by
    rw [rootSet_eq_of_mem h']; exact mem_rootSet_self hcD)
  have hSb := rootSet_subset_twoCore_self hclass hD hc hb
  have hSc := rootSet_subset_twoCore_of_collinear h hc hs hR hb hcD hbc hbcD hcT
  have hSc' := rootSet_subset_twoCore_of_collinear h hc hs hR hb hc' hbc' hbc'D hc'Tb
  have hTb := rootSet_subset_twoCore_of_collinear h hc hs hR hcD hb hbc.symm
    (by rw [← hbc.eq]; exact hbcD) hbT
  have hTc := rootSet_subset_twoCore_self hclass hD hc hcD
  have hTc' := rootSet_subset_twoCore_of_collinear h hc hs hR hcD hc' hcc' hcc'D hc'T
  set Ab := rootGroup D b
  set Ac := rootGroup D c
  set Ac' := rootGroup D c'
  have hbc_comm : ∀ β ∈ Ab, ∀ γ ∈ Ac, Commute β γ := fun β hβ γ hγ =>
    commute_of_mem_rootGroup_of_commute' hcD hβ hγ hbc
  have hbc'_comm : ∀ β ∈ Ab, ∀ γ ∈ Ac', Commute β γ := fun β hβ γ hγ =>
    commute_of_mem_rootGroup_of_commute' hc' hβ hγ hbc'
  have hcc'_comm : ∀ β ∈ Ac, ∀ γ ∈ Ac', Commute β γ := fun β hβ γ hγ =>
    commute_of_mem_rootGroup_of_commute' hc' hβ hγ hcc'
  set S : Set G := (Ab : Set G) ∪ Ac ∪ Ac'
  have hSS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := by
    rintro s ((hs | hs) | hs) s' ((hs' | hs') | hs')
    · exact commute_of_mem_rootGroup hb hs hs'
    · exact hbc_comm s hs s' hs'
    · exact hbc'_comm s hs s' hs'
    · exact (hbc_comm s' hs' s hs).symm
    · exact commute_of_mem_rootGroup hcD hs hs'
    · exact hcc'_comm s hs s' hs'
    · exact (hbc'_comm s' hs' s hs).symm
    · exact (hcc'_comm s' hs' s hs).symm
    · exact commute_of_mem_rootGroup hc' hs hs'
  set E : Subgroup G := Subgroup.closure S
  have hEcomm : ∀ u ∈ E, ∀ v ∈ E, Commute u v := fun u hu v hv =>
    commute_of_mem_closure hSS hu hv
  have hEsup : E = Ab ⊔ Ac ⊔ Ac' := by
    simp only [E, S, Subgroup.closure_union, Subgroup.closure_eq]
  have hrep : ∀ u ∈ E, ∃ β ∈ Ab, ∃ γ ∈ Ac, ∃ γ' ∈ Ac', u = β * γ * γ' := by
    intro u hu
    rw [hEsup] at hu
    have hsupc : ∀ v ∈ Ab ⊔ Ac, ∀ γ' ∈ Ac', Commute v γ' := by
      intro v hv γ' hγ'
      rw [Subgroup.sup_eq_closure] at hv
      exact commute_of_mem_closure (S' := {γ'}) (fun s hs t ht => by
        rw [Set.mem_singleton_iff.1 ht]
        rcases hs with hs | hs
        · exact hbc'_comm s hs γ' hγ'
        · exact hcc'_comm s hs γ' hγ') hv (Subgroup.subset_closure rfl)
    obtain ⟨v, hv, γ', hγ', rfl⟩ := exists_mul_eq_of_mem_sup hsupc hu
    obtain ⟨β, hβ, γ, hγ, rfl⟩ := exists_mul_eq_of_mem_sup hbc_comm hv
    exact ⟨β, hβ, γ, hγ, γ', hγ', rfl⟩
  have hEb : E ≤ nCore D b := by
    rw [Subgroup.closure_le]
    rintro s ((hs | hs) | hs)
    · exact rootGroup_le_nCore hSb hs
    · exact rootGroup_le_nCore hSc hs
    · exact rootGroup_le_nCore hSc' hs
  have hEc : E ≤ nCore D c := by
    rw [Subgroup.closure_le]
    rintro s ((hs | hs) | hs)
    · exact rootGroup_le_nCore hTb hs
    · exact rootGroup_le_nCore hTc hs
    · exact rootGroup_le_nCore hTc' hs
  have hEQ : ∀ u ∈ E, u ∈ Moufang.twoCore b := fun u hu => nCore_le_twoCore D b (hEb hu)
  have hED : ∀ u ∈ E, u ≠ 1 → u ∈ D ∧ (u ∈ rootSet D b ∨ (Commute b u ∧ b * u ∈ D)) := by
    intro u hu hu1
    have huD : u ∈ D := by
      obtain ⟨β, hβ, γ, hγ, γ', hγ', rfl⟩ := hrep u hu
      by_cases hg1 : γ * γ' = 1
      · rw [mul_assoc, hg1, mul_one] at hu1 ⊢
        exact (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hb hβ hu1).1
      have hgD : γ * γ' ∈ D :=
        mul_mem_of_mem_rootGroup h hc hs hR hcD hc' hcc' hcc'D hc'T hγ hγ'
          (by by_contra! h'; exact hg1 (by rw [h'.1, h'.2, mul_one]))
      have hgE : γ * γ' ∈ E := E.mul_mem (Subgroup.subset_closure (Or.inl (Or.inr hγ)))
        (Subgroup.subset_closure (Or.inr hγ'))
      rw [mul_assoc]
      rcases mem_rootSet_or_collinear_of_mem_twoCore hclass hD hOD hc hs hR hb hgD
          (hEQ _ hgE) with hgT | ⟨hbg, hbgD⟩
      · have hmem : β * (γ * γ') ∈ Ab :=
          Ab.mul_mem hβ (rootSet_subset_rootGroup D b hgT)
        exact (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hb hmem
          (by rwa [mul_assoc] at hu1)).1
      · by_cases hgT : γ * γ' ∈ rootSet D b
        · have hmem : β * (γ * γ') ∈ Ab :=
            Ab.mul_mem hβ (rootSet_subset_rootGroup D b hgT)
          exact (mem_rootSet_of_mem_rootGroup_of_ne_one hD hc hb hmem
            (by rwa [mul_assoc] at hu1)).1
        · exact mul_mem_of_mem_rootGroup h hc hs hR hb hgD hbg hbgD hgT hβ
            (rootSet_subset_rootGroup D _ (mem_rootSet_self hgD)) (Or.inr hg1)
    exact ⟨huD, mem_rootSet_or_collinear_of_mem_twoCore hclass hD hOD hc hs hR hb huD
      (hEQ u hu)⟩
  have hBE : Ab ≤ E := fun β hβ => Subgroup.subset_closure (Or.inl (Or.inl hβ))
  have hCE : Ac ≤ E := fun γ hγ => Subgroup.subset_closure (Or.inl (Or.inr hγ))
  have hinf : Ab ⊓ Ac = ⊥ := rootGroup_inf_eq_bot_of_rootClosure hD hc hb hcD fun h' => hcT (by
    rw [h']; exact mem_rootSet_self hcD)
  have hle : Nat.card Ab * Nat.card Ac ≤ Nat.card (Ab ⊔ Ac : Subgroup G) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective (fun p => ⟨(p.1 : G) * p.2,
      (Ab ⊔ Ac).mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩) ?_
    rintro ⟨β₁, γ₁⟩ ⟨β₂, γ₂⟩ heq
    have heq' : (β₁ : G) * γ₁ = β₂ * γ₂ := congrArg Subtype.val heq
    have hm : (β₂ : G)⁻¹ * β₁ = γ₂ * (γ₁ : G)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
    have hm1 : (β₂ : G)⁻¹ * β₁ = 1 := by
      have : (β₂ : G)⁻¹ * β₁ ∈ Ab ⊓ Ac :=
        ⟨Ab.mul_mem (Ab.inv_mem β₂.2) β₁.2, by rw [hm]; exact Ac.mul_mem γ₂.2 (Ac.inv_mem γ₁.2)⟩
      rwa [hinf, Subgroup.mem_bot] at this
    have hβ : (β₁ : G) = β₂ := (inv_mul_eq_one.1 hm1).symm
    have hγ : (γ₁ : G) = γ₂ := by rw [hβ] at heq'; exact mul_left_cancel heq'
    exact Prod.ext (Subtype.ext hβ) (Subtype.ext hγ)
  have hlt : Ab ⊔ Ac < E := by
    refine lt_of_le_of_ne (sup_le hBE hCE) fun heq => hoff ?_
    rw [heq]
    exact Subgroup.subset_closure (Or.inr (rootSet_subset_rootGroup D c' (mem_rootSet_self hc')))
  have hcard : Nat.card Ab * Nat.card Ac < Nat.card E :=
    hle.trans_lt (Subgroup.card_lt_of_lt hlt)
  exact oneOpposite_of_plane hclass hD hR ha hb hcD hx hab habD hbx hoddbx hax hoddax hxc
    hEcomm hED hEb hEc hBE hCE hcard

end CFSG.Timmesfeld.Bridge
