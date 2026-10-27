module

public import CFSG.Monster.GMS.CommonNbr

public section

namespace CFSG.Monster.GMS.Fi23Fusion

open CFSG.Blueprint.NativeSporadic
open CFSG.Monster.GMS.Fi23Local

section Abstract

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem isConj_twoB_of_commuting_twoANbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {t f f' : G} (htA : IsConj a t) (hf : f ∈ twoANbr a t) (hf' : f' ∈ twoANbr a t)
    (hc : f * f' = f' * f) (hne : f ≠ f') (hne' : f ≠ t * f') (hA : IsConj a (f * f')) :
    IsConj z₀ (t * (f * f')) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  obtain ⟨b', z', u', hB⟩ := h.exists_of_isConj htA
  have hIV := I.tableIV t b' z' u' (isTwoBabyCentralizer_of_isConj I.sls hG htA) hB.tableV
  have hfC : f ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_twoANbr h htA hf).symm
  have hf'C : f' ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_twoANbr h htA hf').symm
  have htt : t * t = 1 := mul_self_eq_one_of_isConj_a h htA
  have hff : f * f = 1 := mul_self_eq_one_of_isConj_a h hf.1
  have hff' : f' * f' = 1 := mul_self_eq_one_of_isConj_a h hf'.1
  have hfC' : f * f' ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.mul_mem _ hfC hf'C
  have hsq : (f * f') * (f * f') = 1 := by
    calc (f * f') * (f * f') = f * (f' * f) * f' := by group
      _ = f * (f * f') * f' := by rw [hc]
      _ = (f * f) * (f' * f') := by group
      _ = 1 := by rw [hff, hff', one_mul]
  have hcancel : f = f * f' * f' := by rw [mul_assoc, hff', mul_one]
  have hne1 : f * f' ≠ 1 := fun e => hne (by rw [hcancel, e, one_mul])
  have hnet : f * f' ≠ t := fun e => hne' (by rw [hcancel, e])
  have hnotb : ¬ IsTwoACls t b' (f * f') :=
    hIV f hfC f' hf'C (CommonNbr.isTwoACls_of_mem_twoANbr htA hB hf)
      (CommonNbr.isTwoACls_of_mem_twoANbr htA hB hf') hc hne hne'
  obtain ⟨g, hg, hcase⟩ := hB.tableV.cover (f * f') hfC' (orderOf_eq_two_of_mul_self hsq hne1) hnet
  have hgA : ∀ y, g * (f * f') * g⁻¹ = y → IsConj t y := fun y e => by
    rw [← e]
    exact (htA.symm.trans hA).trans (isConj_conj_self g (f * f'))
  rcases hcase with e | e | e | e
  · exact absurd ⟨g, hg, Or.inl e⟩ hnotb
  · exact absurd ((hgA _ e).trans hB.isConj_z.symm) hB.not_isConj
  · have e' : g * (t * (f * f')) * g⁻¹ = z' := by
      rw [conj_mul_of_mem_centralizer hg, e, ← mul_assoc, htt, one_mul]
    exact hB.isConj_z.trans (isConj_iff.mpr ⟨g, e'⟩).symm
  · exact absurd ((hgA _ e).trans hB.isConj_u.symm) hB.not_isConj

theorem isConj_twoB_mul_of_commute
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {b x t : G}
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) (ht : IsConj z₀ t)
    (htb : b * t = t * b) (htx : x * t = t * x) : IsConj z₀ (b * t) := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hbb := mul_self_eq_one_of_isConj_a h hb
  have hxx := mul_self_eq_one_of_isConj_a h hx
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf (h.orderOf_of_isConj ht)
  have hbtC : b * t ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, ← htb]
  have hsq : (b * t) * (b * t) = 1 := by
    calc (b * t) * (b * t) = b * (t * b) * t := by group
      _ = b * (b * t) * t := by rw [htb]
      _ = (b * b) * (t * t) := by group
      _ = 1 := by rw [hbb, htt, one_mul]
  have hne1 : b * t ≠ 1 := by
    intro e
    have : t = b := by
      have := eq_inv_of_mul_eq_one_right e
      rwa [inv_eq_of_mul_eq_one_right hbb] at this
    rw [this] at ht
    exact h.not_isConj (hb.trans ht.symm)
  rcases h.isConj_or_isConj_of_mem_centralizer hb hbtC (orderOf_eq_two_of_mul_self hsq hne1) with
    hA | hB
  swap
  · exact hB
  exfalso
  have hbQ : b ∈ leechQ t := h.mem_leechQ_of_isConj_mul hb ht htb hA
  have hbxC : b * x ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc b * x * t = b * (x * t) := mul_assoc _ _ _
      _ = b * (t * x) := by rw [htx]
      _ = (b * t) * x := (mul_assoc _ _ _).symm
      _ = (t * b) * x := by rw [htb]
      _ = t * (b * x) := mul_assoc _ _ _
  have h3 : b * x * (b * x) * (b * x) = 1 := by
    have := pow_orderOf_eq_one (b * x)
    rw [hbx, pow_three'] at this
    exact this
  have key : b * x * b * x * b = x := by
    calc b * x * b * x * b = (b * x * (b * x) * (b * x)) * x⁻¹ := by group
      _ = x⁻¹ := by rw [h3, one_mul]
      _ = x := inv_eq_of_mul_eq_one_right hxx
  have hinv : (b * x)⁻¹ = x * b := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right hbb]
  have hxQ : x ∈ leechQ t := by
    have := conj_mem_leechQ hbxC hbQ
    rwa [hinv, show b * x * b * (x * b) = x from by
      calc b * x * b * (x * b) = b * x * b * x * b := by group
        _ = x := key] at this
  exact false_of_mem_leechQ hbQ hxQ hbx

end Abstract

section Order

variable {G : Type*} [Group G]

theorem orderOf_mul_comm_of_eq_three {b x : G} (hbb : b * b = 1) (hxx : x * x = 1)
    (hbx : orderOf (b * x) = 3) : orderOf (x * b) = 3 := by
  have : x * b = (b * x)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right hbb]
  rw [this, orderOf_inv, hbx]

end Order

section Members

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G} {b x : G}

theorem commute_mem_twoBNbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {f f' : G}
    (hf : f ∈ twoANbr a b ∩ twoANbr a x) (hf' : f' ∈ twoANbr a b ∩ twoANbr a x) (hne : f ≠ f')
    (hc : f * f' = f' * f) :
    f * f' ∈ twoBNbr a z₀ b ∩ twoBNbr a z₀ x := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hA : IsConj a (f * f') := commute_mem_twoANbr I hG hb hx hbx hf' hf hne hc
  have hncomm : b * x ≠ x * b := not_comm_of_orderOf_eq_three hbx
    (mul_self_eq_one_of_isConj_a h hb) (mul_self_eq_one_of_isConj_a h hx)
  have hff' := mul_self_eq_one_of_isConj_a h hf'.1.1
  have hH := Subgroup.mul_mem _ (mem_inf_of_mem h hb hx hf) (mem_inf_of_mem h hb hx hf')
  refine ⟨⟨hA, isConj_twoB_of_commuting_twoANbr I hG hb hf.1 hf'.1 hc hne ?_ hA⟩,
    ⟨hA, isConj_twoB_of_commuting_twoANbr I hG hx hf.2 hf'.2 hc hne ?_ hA⟩⟩
  · intro e
    have : f * f' = b := by rw [e, mul_assoc, hff', mul_one]
    rw [this] at hH
    exact false_of_mem_inf hncomm (Or.inl rfl) hH
  · intro e
    have : f * f' = x := by rw [e, mul_assoc, hff', mul_one]
    rw [this] at hH
    exact false_of_mem_inf hncomm (Or.inr rfl) hH

theorem mul_mul_mem_twoBBNbr
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hb : IsConj a b) (hx : IsConj a x) (hbx : orderOf (b * x) = 3) {f₁ f₂ f₃ : G}
    (h₁ : f₁ ∈ twoANbr a b ∩ twoANbr a x) (h₂ : f₂ ∈ twoANbr a b ∩ twoANbr a x)
    (h₃ : f₃ ∈ twoANbr a b ∩ twoANbr a x) (h12 : f₁ ≠ f₂) (h13 : f₁ ≠ f₃) (h23 : f₂ ≠ f₃)
    (c12 : f₁ * f₂ = f₂ * f₁) (c13 : f₁ * f₃ = f₃ * f₁) (c23 : f₂ * f₃ = f₃ * f₂) :
    f₁ * f₂ * f₃ ∈ twoBBNbr z₀ b ∩ twoBBNbr z₀ x := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  have hA12 : IsConj a (f₁ * f₂) := commute_mem_twoANbr I hG hb hx hbx h₂ h₁ h12 c12
  have hA13 : IsConj a (f₁ * f₃) := commute_mem_twoANbr I hG hb hx hbx h₃ h₁ h13 c13
  have hA23 : IsConj a (f₂ * f₃) := commute_mem_twoANbr I hG hb hx hbx h₃ h₂ h23 c23
  have hB23 := (commute_mem_twoBNbr I hG hb hx hbx h₂ h₃ h23 c23).1
  have hf₃ := mul_self_eq_one_of_isConj_a h h₃.1.1
  have hne' : f₂ ≠ f₁ * f₃ := by
    intro e
    have e' : f₂ * f₃ = f₁ := by rw [e, mul_assoc, hf₃, mul_one]
    rw [e'] at hB23
    exact h.not_isConj (h₁.1.2.trans hB23.2.symm)
  have ht2B : IsConj z₀ (f₁ * (f₂ * f₃)) :=
    isConj_twoB_of_commuting_twoANbr I hG h₁.1.1 ⟨h₂.1.1, hA12⟩ ⟨h₃.1.1, hA13⟩ c23 h23 hne' hA23
  rw [← mul_assoc] at ht2B
  have hH := Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_inf_of_mem h hb hx h₁)
    (mem_inf_of_mem h hb hx h₂)) (mem_inf_of_mem h hb hx h₃)
  obtain ⟨hHb, hHx⟩ := Subgroup.mem_inf.mp hH
  have htb : b * (f₁ * f₂ * f₃) = f₁ * f₂ * f₃ * b :=
    (Subgroup.mem_centralizer_singleton_iff.mp hHb).symm
  have htx : x * (f₁ * f₂ * f₃) = f₁ * f₂ * f₃ * x :=
    (Subgroup.mem_centralizer_singleton_iff.mp hHx).symm
  have hxx := mul_self_eq_one_of_isConj_a h hx
  have hbb := mul_self_eq_one_of_isConj_a h hb
  exact ⟨⟨ht2B, isConj_twoB_mul_of_commute I hG hb hx hbx ht2B htb htx⟩,
    ⟨ht2B, isConj_twoB_mul_of_commute I hG hx hb (orderOf_mul_comm_of_eq_three hbb hxx hbx) ht2B
      htx htb⟩⟩

end Members

section Disjoint

variable {G : Type*} [Group G] {a z₀ b : G}

theorem false_of_mem_twoANbr_twoBNbr (hn : ¬ IsConj a z₀) {t : G} (hA : t ∈ twoANbr a b)
    (hB : t ∈ twoBNbr a z₀ b) : False :=
  hn (hA.2.trans hB.2.symm)

theorem false_of_mem_twoANbr_twoBBNbr (hn : ¬ IsConj a z₀) {t : G} (hA : t ∈ twoANbr a b)
    (hB : t ∈ twoBBNbr z₀ b) : False :=
  hn (hA.1.trans hB.1.symm)

theorem false_of_mem_twoBNbr_twoBBNbr (hn : ¬ IsConj a z₀) {t : G} (hA : t ∈ twoBNbr a z₀ b)
    (hB : t ∈ twoBBNbr z₀ b) : False :=
  hn (hA.1.trans hB.1.symm)

end Disjoint

section Conj

variable {G : Type*} [Group G]

theorem conj_mem_twoBNbr_inter {a z₀ b x g t : G}
    (hg : g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G))
    (ht : t ∈ twoBNbr a z₀ b ∩ twoBNbr a z₀ x) : g * t * g⁻¹ ∈ twoBNbr a z₀ b ∩ twoBNbr a z₀ x := by
  obtain ⟨hgb, hgx⟩ := Subgroup.mem_inf.mp hg
  refine ⟨⟨ht.1.1.trans (isConj_conj_self g t), ?_⟩, ⟨ht.2.1.trans (isConj_conj_self g t), ?_⟩⟩
  · rw [← conj_mul_of_mem_centralizer hgb t]
    exact ht.1.2.trans (isConj_conj_self g _)
  · rw [← conj_mul_of_mem_centralizer hgx t]
    exact ht.2.2.trans (isConj_conj_self g _)

theorem conj_mem_twoBBNbr_inter {z₀ b x g t : G}
    (hg : g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G))
    (ht : t ∈ twoBBNbr z₀ b ∩ twoBBNbr z₀ x) : g * t * g⁻¹ ∈ twoBBNbr z₀ b ∩ twoBBNbr z₀ x := by
  obtain ⟨hgb, hgx⟩ := Subgroup.mem_inf.mp hg
  refine ⟨⟨ht.1.1.trans (isConj_conj_self g t), ?_⟩, ⟨ht.2.1.trans (isConj_conj_self g t), ?_⟩⟩
  · rw [← conj_mul_of_mem_centralizer hgb t]
    exact ht.1.2.trans (isConj_conj_self g _)
  · rw [← conj_mul_of_mem_centralizer hgx t]
    exact ht.2.2.trans (isConj_conj_self g _)

end Conj

end CFSG.Monster.GMS.Fi23Fusion
