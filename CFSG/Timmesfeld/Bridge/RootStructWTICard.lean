module

public import CFSG.Timmesfeld.Bridge.RootStructWTILines

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem map_conj_mem_rootLines_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {x : G}
    {L : Subgroup G} (hL' : L ∈ rootLines D x) (g : G) :
    L.map (MulAut.conj g).toMonoidHom ∈ rootLines D (g * x * g⁻¹) := by
  obtain ⟨b, hb, hxb, hxbD, hbT, rfl⟩ := hL'
  refine ⟨g * b * g⁻¹, conj_mem_of_isClass hclass g hb, (Commute.conj_iff g).2 hxb, ?_, ?_, ?_⟩
  · rw [show g * x * g⁻¹ * (g * b * g⁻¹) = g * (x * b) * g⁻¹ by group]
    exact conj_mem_of_isClass hclass g hxbD
  · rw [rootSet_conj hclass]
    rintro ⟨e, he, he'⟩
    have hex : e = b := by simpa using he'
    exact hbT (hex ▸ he)
  · rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass]

namespace LineSetting

variable (hL : LineSetting G D)
include hL

theorem exists_mem_rootLines {x : G} (hx : x ∈ D) : ∃ L, L ∈ rootLines D x := by
  have hclass := hL.hyp.isClass
  obtain ⟨a, ha, d, hd, had, hadD, hdT, -⟩ := hL.line
  obtain ⟨g, hg⟩ := isConj_iff.1 (hL.hyp.isConj ha hx)
  have := map_conj_mem_rootLines_conj hclass (x := a) ⟨d, hd, had, hadD, hdT, rfl⟩ g
  rw [hg] at this
  exact ⟨_, this⟩

theorem exists_ne_mem_rootLines {a : G} (ha : a ∈ D) {T : Subgroup G} (hT : T ∈ rootLines D a) :
    ∃ L ∈ rootLines D a, L ≠ T := by
  have := hL.hyp.finite
  have hD := hL.hyp.root
  have hclass := hL.hyp.isClass
  by_contra! hone
  obtain ⟨d, hd, had, hadD, hdT, rfl⟩ := hT
  set T := rootGroup D a ⊔ rootGroup D d with hTdef
  have hTx : ∀ x ∈ D, x ∈ rootGroup D a ⊔ rootGroup D d →
      rootGroup D a ⊔ rootGroup D d ∈ rootLines D x := by
    intro x hx hxT
    have hx1 := hD.ne_one hx
    by_cases hxa : x ∈ rootSet D a
    · have hxd : Commute x d := (hxa.2 d hd).2 had
      have hxd1 : x * d ≠ 1 := fun h' => hdT (by
        rw [show d = x⁻¹ from eq_inv_of_mul_eq_one_right h', hD.inv_eq hx]; exact hxa)
      refine ⟨d, hd, hxd, mem_of_mem_sup_rootGroup hL.hyp hL.closure hL.special ha hd had hadD hdT
        (Subgroup.mul_mem _ hxT (right_mem_line hd)) hxd1, fun h' => hdT (by
          rw [← rootSet_eq_of_mem hxa]; exact h'), ?_⟩
      rw [rootGroup_eq_of_mem hxa]
    · have hax := commute_of_mem_sup_rootGroup ha hd had (left_mem_line ha) hxT
      have hxa1 : x * a ≠ 1 := fun h' => hxa (by
        rw [show x = a⁻¹ from eq_inv_of_mul_eq_one_left h', hD.inv_eq ha]
        exact mem_rootSet_self ha)
      refine ⟨a, ha, hax.symm, mem_of_mem_sup_rootGroup hL.hyp hL.closure hL.special ha hd had
        hadD hdT (Subgroup.mul_mem _ hxT (left_mem_line ha)) hxa1,
        fun h' => hxa (mem_rootSet_comm hx h'), ?_⟩
      rw [sup_comm (rootGroup D x)]
      exact (sup_rootGroup_eq_of_mem hL.hyp hL.closure hL.special ha hd had hadD hdT
        (left_mem_line ha) hxT (hD.ne_one ha) hx1 hxa).symm
  have hlines : ∀ x ∈ D, x ∈ rootGroup D a ⊔ rootGroup D d →
      ∀ L ∈ rootLines D x, L = rootGroup D a ⊔ rootGroup D d := by
    intro x hx hxT L hL'
    obtain ⟨h, hh⟩ := isConj_iff.1 (hL.hyp.isConj ha hx)
    have hconj : h⁻¹ * x * h⁻¹⁻¹ = a := by rw [← hh]; group
    have h1 := map_conj_mem_rootLines_conj hclass hL' h⁻¹
    have h3 := map_conj_mem_rootLines_conj hclass (hTx x hx hxT) h⁻¹
    rw [hconj] at h1 h3
    exact Subgroup.map_injective (MulAut.conj h⁻¹).injective ((hone _ h1).trans (hone _ h3).symm)
  have hsub := hL.conn {x | x ∈ D ∧ x ∈ rootGroup D a ⊔ rootGroup D d} (fun x hx => hx.1)
    ⟨a, ha, left_mem_line ha⟩ (fun x hx y hy hxy hxyD => ⟨hy, by
      by_cases hyT : y ∈ rootSet D x
      · exact rootGroup_le_sup_of_mem hL.hyp hL.closure hL.special ha hd had hadD hdT hx.2
          (hD.ne_one hx.1) (rootSet_subset_rootGroup D x hyT)
      · rw [← hlines x hx.1 hx.2 _ ⟨y, hy, hxy, hxyD, hyT, rfl⟩]
        exact Subgroup.mem_sup_right (rootSet_subset_rootGroup D y (mem_rootSet_self hy))⟩)
  obtain ⟨d₁, hd₁, e₁, he₁, h4⟩ := hL.hyp.nondeg
  exact not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hd₁) (hD.mul_self_eq_one he₁) h4
    (commute_of_mem_sup_rootGroup ha hd had (hsub hd₁).2 (hsub he₁).2)

theorem exists_ncard_rootLines {a : G} (ha : a ∈ D) :
    ∃ m : ℕ, (rootLines D a).ncard = 2 ^ m + 1 := by
  obtain ⟨T, hT⟩ := hL.exists_mem_rootLines ha
  obtain ⟨L, hL', hLT⟩ := hL.exists_ne_mem_rootLines ha hT
  obtain ⟨m, hm, -⟩ := hL.exists_ncard_rootLines_eq ha hT hL' hLT
  exact ⟨m, hm⟩

end LineSetting

end CFSG.Timmesfeld.Bridge
