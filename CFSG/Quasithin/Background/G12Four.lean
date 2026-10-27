module

public import CFSG.Quasithin.Background.G12FourHyp
public import CFSG.Quasithin.Background.G12Facts
public import CFSG.Quasithin.Background.G12FourTransport

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)}

theorem g12f_exists_marked (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {v : V}
    (hv : IsStarVec B Γ v) (hne : ¬ FourElliptic B Γ v) :
    ∃ a, B v a = 0 ∧ a ≠ 0 ∧ a ≠ v ∧ radE B v a 1 ∈ Γ := by
  have hv' := (isStarVec_iff_rad hB hΓ).1 hv
  simp only [FourElliptic, not_forall] at hne
  obtain ⟨b, hvb, hb0, hbv, hb1⟩ := hne
  have hbo : b ∉ B.orthogonal (perp B v) := by
    rw [hB.orthogonal_perp, Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    rcases g12_eq_zero_or_one c with rfl | rfl
    · exact hb0 (by rw [← hc, zero_smul])
    · exact hbv (by rw [← hc, one_smul])
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hbo
  simp only [not_forall] at hbo
  obtain ⟨y, hy, hyb⟩ := hbo
  have hyb1 : B y b = 1 := g12_eq_one_of_ne_zero _ hyb
  have hby : B b y = 1 := by rw [hB.symm']; exact hyb1
  have hvy : B v y = 0 := mem_perp_iff.1 hy
  obtain ⟨cb, hcb⟩ := hv'.2 b hvb
  obtain ⟨cy, hcy⟩ := hv'.2 y hvy
  have hcb0 : cb = 0 := by
    rcases g12_eq_zero_or_one cb with h | h
    · exact h
    · exact absurd (h ▸ hcb) hb1
  rcases g12_eq_zero_or_one cy with h | h
  · refine ⟨b + y, by rw [map_add, hvb, hvy, add_zero], fun h0 => ?_, fun h1 => ?_, ?_⟩
    · have e : y = b := by
        calc y = (b + b) + y := by rw [g12_vadd_self, zero_add]
          _ = b + (b + y) := by rw [add_assoc]
          _ = b := by rw [h0, add_zero]
      rw [e, hB.1 b] at hyb1
      exact absurd hyb1 (by decide)
    · have := hvb
      rw [← h1, map_add, LinearMap.add_apply, hB.1 b, hyb1] at this
      exact absurd this (by decide)
    · have := Γ.mul_mem hcb hcy
      rwa [radE_mul hB hvb hvy, hcb0, h, hby, show (0 + 0 + 1 : ZMod 2) = 1 from rfl] at this
  · refine ⟨y, hvy, fun h0 => ?_, fun h1 => ?_, h ▸ hcy⟩
    · rw [h0, map_zero, LinearMap.zero_apply] at hyb1
      exact absurd hyb1 (by decide)
    · rw [h1, hvb] at hyb1
      exact absurd hyb1 (by decide)

theorem g12f_exists_marked_perp (hB : IsSymplectic B) (hΓ : Γ ≤ spSub B) {v u : V}
    (hv : IsStarVec B Γ v) (hne : ¬ FourElliptic B Γ v) (hvu : B v u = 1) :
    ∃ a, B v a = 0 ∧ a ≠ 0 ∧ a ≠ v ∧ B a u = 0 ∧ radE B v a 1 ∈ Γ := by
  obtain ⟨a, hva, ha0, hav, ha1⟩ := g12f_exists_marked hB hΓ hv hne
  rcases g12_eq_zero_or_one (B a u) with h | h
  · exact ⟨a, hva, ha0, hav, h, ha1⟩
  · refine ⟨a + v, by rw [map_add, hva, hB.1 v, add_zero], fun h0 => hav ?_, fun h1 => ha0 ?_,
      ?_, by rw [g12f_radE_add_self hB hva]; exact ha1⟩
    · calc a = a + (v + v) := by rw [g12_vadd_self, add_zero]
        _ = (a + v) + v := by rw [add_assoc]
        _ = v := by rw [h0, zero_add]
    · calc a = a + (v + v) := by rw [g12_vadd_self, add_zero]
        _ = (a + v) + v := by rw [add_assoc]
        _ = 0 := by rw [h1, g12_vadd_self]
    · rw [map_add, LinearMap.add_apply, h, hvu]
      decide

omit [Finite V] in
theorem g12f_exists_y (hB : IsSymplectic B) {v a u : V} (hvu : B v u = 1) (hva : B v a = 0)
    (hau : B a u = 0) (ha0 : a ≠ 0) : ∃ y, B v y = 0 ∧ B a y = 1 ∧ B u y = 0 := by
  obtain ⟨y', hy'⟩ := hB.exists_B_eq_one ha0
  have hav : B a v = 0 := by rw [hB.symm']; exact hva
  have huv : B u v = 1 := by rw [hB.symm']; exact hvu
  refine ⟨y' + B y' u • v + B y' v • u, ?_, ?_, ?_⟩
  · rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hB.1 v, hvu, mul_zero,
      add_zero, mul_one, hB.symm' v y', g12_add_self]
  · rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hav, hau, mul_zero,
      mul_zero, add_zero, add_zero, hB.symm' a y', hy']
  · rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, huv, hB.1 u, mul_one,
      mul_zero, add_zero, hB.symm' u y', g12_add_self]

theorem g12f_hyp_case (hB : IsSymplectic B) (hd : Module.finrank (ZMod 2) V = 4)
    (hΓ : Γ ≤ spSub B) {v : V} (hv0 : v ≠ 0) (hstar : ∀ w, w ≠ 0 → IsStarVec B Γ w)
    (htv : ∀ w, w ≠ 0 → radE B w 0 1 ∉ Γ) (hnell : ∀ w, w ≠ 0 → ¬ FourElliptic B Γ w) :
    Nonempty (↥Γ ≃* Equiv.Perm (Fin 5)) ∧ ∃ A : Subgroup (GLV V), A ≤ Γ ∧ IsL24ModuleFor A := by
  obtain ⟨u, huv⟩ := hB.exists_B_eq_one hv0
  have hvu : B v u = 1 := by rw [hB.symm']; exact huv
  have hu0 : u ≠ 0 := fun h => by
    rw [h, map_zero, LinearMap.zero_apply] at huv
    exact absurd huv (by decide)
  obtain ⟨a, hva, ha0, -, hau, ha1⟩ :=
    g12f_exists_marked_perp hB hΓ (hstar v hv0) (hnell v hv0) hvu
  obtain ⟨y, hvy, hay, huy⟩ := g12f_exists_y hB hvu hva hau ha0
  have key : ∀ y1 : V, B v y1 = 0 → B a y1 = 1 → B u y1 = 0 → radE B u y1 1 ∈ Γ →
      Nonempty (↥Γ ≃* Equiv.Perm (Fin 5)) ∧
        ∃ A : Subgroup (GLV V), A ≤ Γ ∧ IsL24ModuleFor A := by
    intro y1 hvy1 hay1 huy1 hm2
    obtain ⟨φ, hφ, hφ0, hφ1, hφ2, hφ3⟩ := g12f_exists_isometry hB hd hva hvu hvy1 hau hay1 huy1
    have heq : fourConjSub φ Γ = fourM0 := g12f_eq_fourM0 (fourConjSub_le_spSub hφ hΓ)
      (isStarVec_fourConj hφ hB hΓ (by rw [hφ0]; exact hstar v hv0))
      (isStarVec_fourConj hφ hB hΓ (by rw [hφ2]; exact hstar u hu0))
      (by rw [radE_mem_fourConjSub_iff hφ hB (by simp) 1, hφ0, map_zero]; exact htv v hv0)
      (by rw [fourElliptic_fourConjSub_iff hφ hB, hφ0]; exact hnell v hv0)
      (by rw [fourElliptic_fourConjSub_iff hφ hB, hφ2]; exact hnell u hu0)
      (by rw [radE_mem_fourConjSub_iff hφ hB (by decide) 1, hφ0, hφ1]; exact ha1)
      (by rw [radE_mem_fourConjSub_iff hφ hB (by decide) 1, hφ2, hφ3]; exact hm2)
    exact ⟨nonempty_mulEquiv_of_fourConjSub ⟨(MulEquiv.subgroupCongr heq).trans fourRhoEquiv⟩,
      exists_isL24_of_fourConjSub (heq ▸ fourA0_le) isL24ModuleFor_fourA0⟩
  have hua : B u a = 0 := by rw [hB.symm']; exact hau
  have huya : B u (y + a) = 0 := by rw [map_add, huy, hua, add_zero]
  by_cases h1 : radE B u y 1 ∈ Γ
  · exact key y hvy hay huy h1
  by_cases h2 : radE B u (y + a) 1 ∈ Γ
  · exact key (y + a) (by rw [map_add, hvy, hva, add_zero]) (by rw [map_add, hay, hB.1 a, add_zero])
      huya h2
  exfalso
  have hu' := (isStarVec_iff_rad hB hΓ).1 (hstar u hu0)
  obtain ⟨c1, hc1⟩ := hu'.2 y huy
  obtain ⟨c2, hc2⟩ := hu'.2 (y + a) huya
  have hc1' : c1 = 0 := by
    rcases g12_eq_zero_or_one c1 with h | h
    · exact h
    · exact absurd (h ▸ hc1) h1
  have hc2' : c2 = 0 := by
    rcases g12_eq_zero_or_one c2 with h | h
    · exact h
    · exact absurd (h ▸ hc2) h2
  have hm3 : radE B u a 1 ∈ Γ := by
    have := Γ.mul_mem hc1 hc2
    rwa [radE_mul hB huy huya, hc1', hc2', show y + (y + a) = a by
      rw [← add_assoc, g12_vadd_self, zero_add], show B y (y + a) = 1 by
      rw [map_add, hB.1 y, hB.symm' y a, hay, zero_add], show (0 + 0 + 1 : ZMod 2) = 1 from rfl]
      at this
  obtain ⟨φ, hφ, hφ0, hφ1, hφ2, -⟩ := g12f_exists_isometry hB hd hva hvu hvy hau hay huy
  exact g12f_false_of_marked (fourConjSub_le_spSub hφ hΓ)
    (isStarVec_fourConj hφ hB hΓ (by rw [hφ1]; exact hstar a ha0))
    (by rw [fourElliptic_fourConjSub_iff hφ hB, hφ1]; exact hnell a ha0)
    (by rw [radE_mem_fourConjSub_iff hφ hB (by decide) 1, hφ0, hφ1]; exact ha1)
    (by rw [radE_mem_fourConjSub_iff hφ hB (by decide) 1, hφ2, hφ1]; exact hm3)

end NoInst

theorem g12_four_fact : G12FourFact := by
  intro V _ _ _ B Γ v hB hd hΓ hv0 hstar htv htr
  have htv' : ∀ w, w ≠ 0 → radE B w 0 1 ∉ Γ := fun w hw => g12f_tv_not_mem hB hΓ htv htr hw
  by_cases hell : FourElliptic B Γ v
  · left
    refine g12f_eq_commutator_of_elliptic hB hΓ hd.ge hv0 htv fun w hw => ?_
    obtain ⟨g, hg, rfl⟩ := htr w hw
    exact (g12f_elliptic_conj hB hΓ hg).2 hell
  · right
    refine g12f_hyp_case hB hd hΓ hv0 hstar htv' fun w hw h => hell ?_
    obtain ⟨g, hg, rfl⟩ := htr w hw
    exact (g12f_elliptic_conj hB hΓ hg).1 h

end CFSG.Quasithin.G11
