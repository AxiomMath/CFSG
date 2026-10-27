module

public import CFSG.Quasithin.Background.G12Orbit
public import CFSG.Quasithin.Background.G12Facts
public import CFSG.Quasithin.Background.G12Ortho

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem g12_orth_fact :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (q : V → ZMod 2) (Γ : Subgroup (GLV V)) (v : V),
      IsSymplectic B → 4 ≤ Module.finrank (ZMod 2) V → (∀ x y, q (x + y) = q x + q y + B x y) →
      Γ ≤ orthSub q → IsStarVec B Γ v → q v = 0 →
      (∀ w, (∃ g ∈ Γ, w = g v) ↔ (w ≠ 0 ∧ q w = 0)) → (Γ = orthSub q ∨ Γ = omegaSub B q) :=
  fun _ _ _ _ _ _ _ _ hB hd hq hΓq hv hqv horb => g12_orth_conclusion hB hd hq hΓq hv hqv horb

theorem g12_1_of_four (hF : G12FourFact) : G121Stmt := by
  have hO := g12_orth_fact
  intro V _ _ _ B Γ u v hB hΓ hu hv huv hd
  have huv1 : B u v = 1 := g12_eq_one_of_ne_zero _ huv
  have hv0 : v ≠ 0 := ((isStarVec_iff_rad hB hΓ).1 hv).1
  unfold G121Concl
  by_cases htv : radE B v 0 1 ∈ Γ
  · exact Or.inl (eq_spSub_of_tv_mem hB hΓ hv hu huv1 hd htv)
  by_cases htrans : ∀ x, x ≠ 0 → x ∈ orbitSet Γ v
  ·
    have hstar : ∀ w, w ≠ 0 → IsStarVec B Γ w := by
      intro w hw
      obtain ⟨g, hg, rfl⟩ := htrans w hw
      exact hv.conj hB hΓ hg
    have htv' : ∀ w, w ≠ 0 → radE B w 0 1 ∉ Γ := by
      intro w hw hmem
      obtain ⟨g, hg, rfl⟩ := htrans w hw
      apply htv
      have h1 := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) hmem) (Γ.inv_mem (Γ.inv_mem hg))
      rw [radE_conj hB (hΓ (Γ.inv_mem hg)) (show B (g v) 0 = 0 by simp)] at h1
      simpa using h1
    by_cases hd4 : Module.finrank (ZMod 2) V = 4
    · refine Or.inr (Or.inr ⟨hd4, hF V B Γ v hB hd4 hΓ hv0 hstar htv ?_⟩)
      intro w hw
      obtain ⟨g, hg, rfl⟩ := htrans w hw
      exact ⟨g, hg, rfl⟩
    · exfalso
      exact false_of_all_star_no_tv hB hΓ (by omega) hstar htv' hv0
  ·
    have hnt : ∃ x, x ≠ 0 ∧ x ∉ orbitSet Γ v := by
      by_contra h
      apply htrans
      intro x hx
      by_contra hxn
      exact h ⟨x, hx, hxn⟩
    obtain ⟨q, hq, hΓq, hqv, horb⟩ :=
      exists_quadratic_of_nontransitive hB hΓ hv hu huv1 hd hnt
    exact Or.inr (Or.inl ⟨q, hq, hO V B q Γ v hB hd hq hΓq hv hqv horb, horb⟩)

end NoInst

end CFSG.Quasithin.G11
