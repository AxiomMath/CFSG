module

public import CFSG.Quasithin.Background.B6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinPGL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2

public section

namespace CFSG.Quasithin

theorem card_le_two_of_normal_exp_two_of_injective_dihedral {Y : Type*} [Group Y] [Finite Y] {m : ℕ}
    (f : Y →* DihedralGroup (2 ^ m)) (hf : Function.Injective f) (h16 : 16 ≤ Nat.card Y)
    (E : Subgroup Y) [E.Normal] (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hnc : ¬ IsCyclic E := by
    intro hc
    have : Fintype E := Fintype.ofFinite E
    have hle := IsCyclic.card_pow_eq_one_le (α := E) (n := 2) two_pos
    have hall : (Finset.univ.filter (fun a : E => a ^ 2 = 1)) = Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact Subtype.ext (by simpa using hE x x.2)
    rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
    omega
  have hYnc : ¬ IsCyclic Y := fun hc => hnc (Subgroup.isCyclic E)
  let e₀ : Y ≃* f.range := MonoidHom.ofInjective hf
  have hrnc : ¬ IsCyclic f.range := fun hc => hYnc (e₀.isCyclic.mpr hc)
  obtain ⟨k, hk1, -, ⟨e'⟩⟩ := CFSG.GorensteinWalter.noncyclic_subgroup_dihedral_two_pow f.range hrnc
  let e : Y ≃* DihedralGroup (2 ^ k) := e₀.trans e'
  have hidx : E.index ≤ 2 :=
    CFSG.GorensteinWalter.normal_noncyclic_subgroup_dihedral_of_mulEquiv_index_le_two hk1 e E inferInstance hnc
  have hmul := E.index_mul_card
  have hE8 : 8 ≤ Nat.card E := by
    have : 16 ≤ E.index * Nat.card E := hmul ▸ h16
    nlinarith
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  have h4 := CFSG.QuasithinUnique.Setup.Family.dihedral_elemAbelian_card_le_four (E.map e.toMonoidHom)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← pow_two, hE x hx, map_one])
  rw [Subgroup.card_map_of_injective e.injective] at h4
  omega


theorem card_le_two_of_normal_exp_two_aut_psl2 {J : Type} [Group J] {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (hF : Nat.card F = p) (e : J ≃* CFSG.GorensteinWalter.PSL2 F)
    (D E : Subgroup (MulAut J)) (hD : IsPGroup 2 D) (h16 : 16 ≤ Nat.card D) (hED : E ≤ D)
    (hcl : ∀ d ∈ D, ∀ x ∈ E, d * x * d⁻¹ ∈ E) (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 2 := by
  classical
  have : Finite J := Finite.of_equiv _ e.symm.toEquiv
  have : Finite (MulAut J) := Finite.of_equiv _ (MulAut.congr e).symm.toEquiv
  let Φ : MulAut J ≃* MulAut (CFSG.GorensteinWalter.PSL2 F) := MulAut.congr e
  let P : Subgroup (MulAut (CFSG.GorensteinWalter.PSL2 F)) := D.map Φ.toMonoidHom
  let ι : ↥D ≃* ↥P := Subgroup.equivMapOfInjective D Φ.toMonoidHom Φ.injective
  have hP : IsPGroup 2 P := hD.of_equiv ι
  obtain ⟨m, f, hf⟩ := CFSG.QuasithinUnique.Out21.exists_injective_dihedral hp7 hF P hP
  have hn : (E.subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hcl g g.2 n hn
  have h := card_le_two_of_normal_exp_two_of_injective_dihedral (f.comp ι.toMonoidHom)
    (hf.comp ι.injective) h16 (E.subgroupOf D)
    (fun x hx => Subtype.ext (hE x hx))
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hED).toEquiv] at h


open B6 in
theorem relIndex_inf_centralizer_le_two {X : Type} [Group X] [Finite X] {J T₀ W : Subgroup X}
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (hF : Nat.card F = p)
    (e : J ≃* CFSG.GorensteinWalter.PSL2 F) (hT₀ : IsPGroup 2 T₀)
    (hJ : T₀ ≤ Subgroup.normalizer (J : Set X)) (hWT : W ≤ T₀)
    (hWn : ∀ t ∈ T₀, ∀ w ∈ W, t * w * t⁻¹ ∈ W) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (h16 : 16 ≤ (T₀ ⊓ Subgroup.centralizer (J : Set X)).relIndex T₀) :
    (W ⊓ Subgroup.centralizer (J : Set X)).relIndex W ≤ 2 := by
  classical
  have hDcard : Nat.card (autOn T₀ J) = (T₀ ⊓ Subgroup.centralizer (J : Set X)).relIndex T₀ :=
    card_autOn_eq_relIndex hJ
  have hEcard : Nat.card (autOn W J) = (W ⊓ Subgroup.centralizer (J : Set X)).relIndex W :=
    card_autOn_eq_relIndex (hWT.trans hJ)
  have hED : autOn W J ≤ autOn T₀ J := autOn_le_autOn_of_le hWT
  have hcl : ∀ d ∈ autOn T₀ J, ∀ x ∈ autOn W J, d * x * d⁻¹ ∈ autOn W J := by
    intro d hd x hx
    obtain ⟨t, htT, htN, rfl⟩ := mem_autOn_iff_indAut.mp hd
    obtain ⟨w, hwW, hwN, rfl⟩ := mem_autOn_iff_indAut.mp hx
    have htwN : t * w * t⁻¹ ∈ Subgroup.normalizer (J : Set X) :=
      mul_mem (mul_mem htN hwN) (inv_mem htN)
    rw [← indAut_inv htN, ← indAut_mul htN hwN, ← indAut_mul (mul_mem htN hwN) (inv_mem htN)]
    exact indAut_mem_autOn (hWn t htT w hwW) htwN
  have hE2 : ∀ x ∈ autOn W J, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨w, hwW, hwN, rfl⟩ := mem_autOn_iff_indAut.mp hx
    rw [← indAut_pow hwN, hW2 w hwW, indAut_one]
  have := card_le_two_of_normal_exp_two_aut_psl2 hp7 hF e (autOn T₀ J) (autOn W J)
    (isPGroup_autOn hT₀ J) (hDcard ▸ h16) hED hcl hE2
  rwa [hEcard] at this

end CFSG.Quasithin
