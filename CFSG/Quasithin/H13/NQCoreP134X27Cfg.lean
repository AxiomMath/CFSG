module

public import CFSG.Quasithin.H13.NQCoreP134X27Descent
public import CFSG.Quasithin.Vol2.F134Basic

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Vol2Native

section E9

variable {A : Type} [Group A] {L P T : Subgroup A}

theorem E9Cfg.exists_subgroup (h : E9Cfg L P T) :
    ∃ Q : Subgroup L, Nat.card Q = 9 ∧ ∀ x ∈ Q, x ^ 3 = 1 :=
  ⟨P.subgroupOf L, by
    rw [← h.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv,
    fun x hx => Subtype.ext (by simpa using h.exp x (Subgroup.mem_subgroupOf.mp hx))⟩

theorem E9Cfg.isSylowTwoOf_inf [Finite A] (h : E9Cfg L P T) : IsSylowTwoOf (T ⊓ L) L :=
  have := h.normal
  RankOneRecog.isSylowTwoOf_inf_of_subnormal h.sylow le_top
    (Subgroup.Normal.isSubnormal inferInstance).subgroupOf

theorem E9Cfg.mul_inf (h : E9Cfg L P T) :
    ∀ t ∈ T ⊓ L, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T ⊓ L, t * x = y * s := by
  intro t ht x hx
  obtain ⟨y, hy, s, hs, he⟩ := h.mul t ht.1 x hx
  refine ⟨y, hy, s, ⟨hs, ?_⟩, he⟩
  have hs' : s = y⁻¹ * (t * x) := by rw [he]; group
  rw [hs']
  exact L.mul_mem (L.inv_mem (h.le hy)) (L.mul_mem ht.2 (h.le hx))

theorem E9Cfg.card_sup_inf [Finite A] (h : E9Cfg L P T) :
    Nat.card (P ⊔ (T ⊓ L) : Subgroup A) = 9 * Nat.card (T ⊓ L : Subgroup A) :=
  P134.card_sup_eq_of_mul h.card (h.sylow.2.1.to_le inf_le_left) (E9Cfg.mul_inf h)

theorem E9Cfg.sup_inf_le (h : E9Cfg L P T) : P ⊔ (T ⊓ L) ≤ L :=
  sup_le h.le inf_le_right

theorem E9Cfg.exists_model_sylow [Finite A] (h : E9Cfg L P T) {Y : Type*} [Group Y]
    (e : ↥L ≃* Y) :
    ∃ H S : Subgroup Y, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧ S ≤ H ∧ Nat.card H = 9 * Nat.card S := by
  have hS := E9Cfg.isSylowTwoOf_inf h
  refine ⟨((P ⊔ (T ⊓ L)).subgroupOf L).map e.toMonoidHom,
    ((T ⊓ L).subgroupOf L).map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map _
  · have := Subgroup.index_map_equiv ((T ⊓ L).subgroupOf L) e
    erw [this]
    exact hS.2.2
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right)
  · rw [← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      ← Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (E9Cfg.sup_inf_le h)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv]
    exact E9Cfg.card_sup_inf h

end E9

theorem noE9Cfg_of_noElemNine {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → F134.NoElemNine X) : NoE9Cfg F := by
  intro A _ _ L P T hL hcfg
  obtain ⟨Q, hQ, hexp⟩ := E9Cfg.exists_subgroup hcfg
  exact hF L hL Q hQ hexp

section X27

variable {A : Type} [Group A] {L P T : Subgroup A}

theorem OddConfig.twentyseven_dvd_card (h : OddConfig 3 L P T) (h27 : Nat.card P = 27) :
    27 ∣ Nat.card L :=
  h27 ▸ Subgroup.card_dvd_of_le h.le

theorem OddConfig.exists_subgroup_nine [Finite A] (h : OddConfig 3 L P T)
    (h27 : Nat.card P = 27) : ∃ Q : Subgroup L, Nat.card Q = 9 ∧ ∀ x ∈ Q, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEP, hE, hE9⟩ := exists_elemAbelian_sq h.exp (by rw [h27]; norm_num)
  refine ⟨E.subgroupOf L, ?_, fun x hx => Subtype.ext ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEP.trans h.le)).toEquiv, hE9]
    norm_num
  · simpa using h.exp x (hEP (Subgroup.mem_subgroupOf.mp hx))

theorem OddConfig.card_sup_inf_x27 [Finite A] (h : OddConfig 3 L P T) (h27 : Nat.card P = 27) :
    Nat.card (P ⊔ (T ⊓ L) : Subgroup A) = 27 * Nat.card (T ⊓ L : Subgroup A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (h.sylow.2.1.to_le (inf_le_left : T ⊓ L ≤ T))
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (T ⊓ L : Subgroup A)) := by
    rw [h27, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  rw [card_sup_eq_of_mul' hcop (OddConfig.mul_inf h), h27]

theorem OddConfig.exists_model_sylow_x27 [Finite A] (h : OddConfig 3 L P T)
    (h27 : Nat.card P = 27) {Y : Type*} [Group Y] (e : ↥L ≃* Y) :
    ∃ H S : Subgroup Y, IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧ S ≤ H ∧ Nat.card H = 27 * Nat.card S := by
  have hS := OddConfig.isSylowTwoOf_inf h
  refine ⟨((P ⊔ (T ⊓ L)).subgroupOf L).map e.toMonoidHom,
    ((T ⊓ L).subgroupOf L).map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map _
  · have := Subgroup.index_map_equiv ((T ⊓ L).subgroupOf L) e
    erw [this]
    exact hS.2.2
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right)
  · rw [← Nat.card_congr (((P ⊔ (T ⊓ L)).subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      ← Nat.card_congr (((T ⊓ L).subgroupOf L).equivMapOfInjective _ e.injective).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddConfig.sup_inf_le h)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv]
    exact OddConfig.card_sup_inf_x27 h h27

end X27

theorem noX27Simple_of_not_dvd {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → ¬ 27 ∣ Nat.card X) : NoX27Simple F := by
  intro A _ _ L P T hcfg h27 hL
  exact hF L hL (OddConfig.twentyseven_dvd_card hcfg h27)

theorem noX27Simple_of_noElemNine {F : ∀ (X : Type) [Group X], Prop}
    (hF : ∀ (X : Type) [Group X], F X → F134.NoElemNine X) : NoX27Simple F := by
  intro A _ _ L P T hcfg h27 hL
  obtain ⟨Q, hQ, hexp⟩ := OddConfig.exists_subgroup_nine hcfg h27
  exact hF L hL Q hQ hexp

end CFSG.Quasithin.H13.NQCore
