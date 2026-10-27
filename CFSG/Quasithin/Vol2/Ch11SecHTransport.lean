module

public import CFSG.Quasithin.Vol2.Ch11SecHFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open

theorem isSylowTwoOf_subgroupOf {X : Type*} [Group X] {A B : Subgroup X}
    (h : QuasithinUnique.IsSylowTwoOf A B) : QuasithinUnique.IsSylowTwoOf (A.subgroupOf B) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm
  · rw [show ((A.subgroupOf B).subgroupOf ⊤).index = (A.subgroupOf B).index from
      Subgroup.relIndex_top_right _]
    exact h.2.2

theorem isSylowTwoOf_map_equiv {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    {S : Subgroup X} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    QuasithinUnique.IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  refine ⟨le_top, hS.2.1.map _, ?_⟩
  have hc : Nat.card (S.map e.toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective e.injective
  have hXY : Nat.card X = Nat.card Y := Nat.card_congr e.toEquiv
  have h1 := Subgroup.index_mul_card S
  have h2 := Subgroup.index_mul_card (S.map e.toMonoidHom)
  have hpos : 0 < Nat.card S := Nat.card_pos
  have h3 : (S.map e.toMonoidHom).index = S.index :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [← hc, h2, hc, h1, hXY])
  have h4 := hS.2.2
  rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h4
  rw [show ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index from
    Subgroup.relIndex_top_right _, h3]
  exact h4

theorem map_mem_normalizer {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {A : Subgroup X}
    {g : X} (hg : g ∈ Subgroup.normalizer (A : Set X)) :
    e g ∈ Subgroup.normalizer ((A.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro t
  have hmem : ∀ x : X, e x ∈ A.map e.toMonoidHom ↔ x ∈ A := fun x =>
    ⟨fun ⟨a, ha, hax⟩ => e.injective hax ▸ ha, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨s, rfl⟩ := e.surjective t
  rw [show e g * e s * (e g)⁻¹ = e (g * s * g⁻¹) by simp [map_mul, map_inv], hmem, hmem]
  exact hg s

variable {X : Type*} [Group X] [Finite X]

theorem sup_eq_of_sylow (hKF5 : FactSL2TwoSylow) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {Ks A₁ A₂ : Subgroup X}
    (e : ↥Ks ≃* Matrix.SpecialLinearGroup (Fin 2) F) (h₁ : QuasithinUnique.IsSylowTwoOf A₁ Ks)
    (h₂ : QuasithinUnique.IsSylowTwoOf A₂ Ks) (hne : A₁ ≠ A₂) : A₁ ⊔ A₂ = Ks := by
  have hS₁ := isSylowTwoOf_map_equiv e (isSylowTwoOf_subgroupOf h₁)
  have hS₂ := isSylowTwoOf_map_equiv e (isSylowTwoOf_subgroupOf h₂)
  have hne' : (A₁.subgroupOf Ks).map e.toMonoidHom ≠ (A₂.subgroupOf Ks).map e.toMonoidHom := by
    intro heq
    apply hne
    have h := Subgroup.map_injective e.injective heq
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr h₁.1, inf_eq_left.mpr h₂.1] at h
    exact h
  have htop := hKF5 F n hn hF _ _ hS₁ hS₂ hne'
  refine le_antisymm (sup_le h₁.1 h₂.1) ?_
  intro x hx
  have hmem : e ⟨x, hx⟩ ∈ (A₁.subgroupOf Ks).map e.toMonoidHom ⊔
      (A₂.subgroupOf Ks).map e.toMonoidHom := htop ▸ Subgroup.mem_top _
  rw [← Subgroup.map_sup] at hmem
  obtain ⟨z, hz, hzx⟩ := hmem
  have hzx' : z = ⟨x, hx⟩ := e.injective hzx
  subst hzx'
  have hle : A₁.subgroupOf Ks ⊔ A₂.subgroupOf Ks ≤ (A₁ ⊔ A₂).subgroupOf Ks :=
    sup_le (fun z hz => Subgroup.mem_subgroupOf.mpr
        ((le_sup_left : A₁ ≤ A₁ ⊔ A₂) (Subgroup.mem_subgroupOf.mp hz)))
      (fun z hz => Subgroup.mem_subgroupOf.mpr
        ((le_sup_right : A₂ ≤ A₁ ⊔ A₂) (Subgroup.mem_subgroupOf.mp hz)))
  exact Subgroup.mem_subgroupOf.mp (hle hz)

theorem fpf_of_sylow (hKF6 : FactSL2BorelFPF) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {Ks A : Subgroup X}
    (e : ↥Ks ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hA : QuasithinUnique.IsSylowTwoOf A Ks)
    {y : X} (hyK : y ∈ Ks) (hyN : y ∈ Subgroup.normalizer (A : Set X)) (hodd : Odd (orderOf y))
    (hy1 : y ≠ 1) {a : X} (ha : a ∈ A) (hya : y * a * y⁻¹ = a) : a = 1 := by
  have hS := isSylowTwoOf_map_equiv e (isSylowTwoOf_subgroupOf hA)
  have hyN' : (⟨y, hyK⟩ : ↥Ks) ∈ Subgroup.normalizer ((A.subgroupOf Ks : Subgroup ↥Ks) :
      Set ↥Ks) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hyN t
  have hodd' : Odd (orderOf (e ⟨y, hyK⟩)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hodd
  have hy1' : e ⟨y, hyK⟩ ≠ 1 := by
    intro h
    apply hy1
    have := e.injective (h.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hmem : e ⟨a, hA.1 ha⟩ ∈ (A.subgroupOf Ks).map e.toMonoidHom :=
    ⟨⟨a, hA.1 ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hcomm : e ⟨y, hyK⟩ * e ⟨a, hA.1 ha⟩ * (e ⟨y, hyK⟩)⁻¹ = e ⟨a, hA.1 ha⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hya
  have h1 := hKF6 F n hn hF _ hS _ (map_mem_normalizer e hyN') hodd' hy1' _ hmem hcomm
  have := e.injective (h1.trans (map_one e).symm)
  exact congrArg Subtype.val this

end CFSG.Quasithin.Vol2.Ch11.SecH
