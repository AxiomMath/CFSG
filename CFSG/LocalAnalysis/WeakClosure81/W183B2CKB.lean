module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKSimple
public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKGraph
public import CFSG.LocalAnalysis.WeakClosure81.W183B2CKIndep

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

private theorem w183b2_caseB_not_iso_same {k : Type} [Field k] [IsAlgClosed k] [CharP k 2]
    {G : Type} [Group G] {Q : Type} [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]
    {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G} (h : CoreSetting ρ A₁ A₂ Δ)
    (hB : ∀ U : Submodule k Q, w183b2SimpleSub ρ (A₁ ⊔ A₂) U →
      ∃ d ∈ Δ, U.map (ρ d) ≠ U)
    {V : Submodule k Q} (hV : w183b2SimpleSub ρ (A₁ ⊔ A₂) V) {f : G} (hf : f ∈ Δ)
    (hf1 : f ≠ 1) : ¬ w183b2NIso ρ (A₁ ⊔ A₂) V (V.map (ρ f)) := by
  intro hiso
  have hVmove : V.map (ρ f) ≠ V := by
    intro hfix
    exact hf1 (w183b2_stab_triv h hV (hB V hV) f hf hfix)
  have hVf : w183b2SimpleSub ρ (A₁ ⊔ A₂) (V.map (ρ f)) :=
    w183b2_simple_translate h hV hf
  have hdisj : V.map (ρ f) ⊓ V = ⊥ :=
    w183b2_simple_inf_eq_bot hVf hV hVmove
  obtain ⟨Γ, hΓ, hΓfix⟩ := w183b2_graph_step h hV hf hdisj hiso
  exact hf1 (w183b2_stab_triv h hΓ (hB Γ hΓ) f hf hΓfix)

private theorem w183b2_caseB_not_iso {k : Type} [Field k] [IsAlgClosed k] [CharP k 2]
    {G : Type} [Group G] {Q : Type} [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]
    {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G} (h : CoreSetting ρ A₁ A₂ Δ)
    (hB : ∀ U : Submodule k Q, w183b2SimpleSub ρ (A₁ ⊔ A₂) U →
      ∃ d ∈ Δ, U.map (ρ d) ≠ U)
    {V : Submodule k Q} (hV : w183b2SimpleSub ρ (A₁ ⊔ A₂) V) {x y : G} (hx : x ∈ Δ)
    (hy : y ∈ Δ) (hxy : x ≠ y) :
    ¬ w183b2NIso ρ (A₁ ⊔ A₂) (V.map (ρ x)) (V.map (ρ y)) := by
  intro hiso
  have htwist : w183b2NIso ρ (A₁ ⊔ A₂) V (V.map (ρ (x⁻¹ * y))) :=
    w183b2_twist_iso h hV.2.1 hx hy hiso
  have hmem : x⁻¹ * y ∈ Δ := Δ.mul_mem (Δ.inv_mem hx) hy
  have hne1 : x⁻¹ * y ≠ 1 := fun h1 => hxy (inv_mul_eq_one.mp h1)
  exact w183b2_caseB_not_iso_same h hB hV hmem hne1 htwist

theorem w183b2_core_k_caseB {k : Type} [Field k] [IsAlgClosed k] [CharP k 2] {G : Type} [Group G]
    [Finite G] {Q : Type} [AddCommGroup Q] [Module k Q] [FiniteDimensional k Q]
    {ρ : Representation k G Q} {A₁ A₂ Δ : Subgroup G} (h : CoreSetting ρ A₁ A₂ Δ)
    (hB : ∀ U : Submodule k Q, w183b2SimpleSub ρ (A₁ ⊔ A₂) U → ∃ d ∈ Δ, U.map (ρ d) ≠ U) :
    Nat.card ↥Δ ≤ 2 := by
  classical
  haveI hnt : Nontrivial Q :=
    ((CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits.isIrreducible_iff ρ).1 h.irr).1
  by_contra hle
  have hgt : 2 < Nat.card ↥Δ := not_le.1 hle
  haveI : Finite ↥Δ := Finite.of_injective (Subtype.val : ↥Δ → G) Subtype.val_injective
  haveI : Fintype ↥Δ := Fintype.ofFinite ↥Δ
  have hcard : 2 < Fintype.card ↥Δ := by
    rwa [Nat.card_eq_fintype_card] at hgt
  have hscard : 1 < ((Finset.univ : Finset ↥Δ).erase 1).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥Δ)), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hscard
  have ha1 : a ≠ 1 := (Finset.mem_erase.1 ha).1
  have hb1 : b ≠ 1 := (Finset.mem_erase.1 hb).1
  let d : G := (a : G)
  let d' : G := (b : G)
  have hd : d ∈ Δ := a.2
  have hd' : d' ∈ Δ := b.2
  have hd1 : d ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  have hd'1 : d' ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  have hdd' : d ≠ d' := fun h1 => hab (Subtype.ext h1)
  obtain ⟨V, hV⟩ := w183b2_exists_simple ρ (A₁ ⊔ A₂)
  have hod : orderOf d = 2 := orderOf_eq_prime (h.elem.2 d hd) hd1
  have hod' : orderOf d' = 2 := orderOf_eq_prime (h.elem.2 d' hd') hd'1
  have hnot : d * d' ∉ ({d, d', 1} : Set G) :=
    mul_notMem_of_orderOf_eq_two hod hod' hdd'
  have hnot' : d * d' ≠ d ∧ d * d' ≠ d' ∧ d * d' ≠ 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hnot
  have hquad : ∀ v : Q, v + v = 0 := fun v => by
    rw [← two_smul (R := k) v, CharTwo.two_eq_zero, zero_smul]
  have hneg : ∀ v : Q, -v = v := fun v => neg_eq_of_add_eq_zero_left (hquad v)
  have hquad_rel : ∀ u ∈ V, u + ρ d u + ρ d' u + ρ (d * d') u = 0 := by
    intro u _
    have hq := h.quad d hd d' hd' u
    have hAB : ρ (d * d') u + ρ d u = ρ d' u + u := by
      have h1 : ρ d (ρ d' u) - ρ d u = ρ d' u - u := by
        simpa only [map_sub] using hq
      have h1' : ρ d (ρ d' u) + ρ d u = ρ d' u + u := by
        simpa [sub_eq_add_neg, hneg] using h1
      have hdd_app : ρ (d * d') u = ρ d (ρ d' u) := by
        rw [map_mul, Module.End.mul_apply]
      rw [hdd_app]
      exact h1'
    calc u + ρ d u + ρ d' u + ρ (d * d') u
        = (ρ (d * d') u + ρ d u) + (ρ d' u + u) := by abel
      _ = (ρ (d * d') u + ρ d u) + (ρ (d * d') u + ρ d u) := by rw [← hAB]
      _ = 0 := hquad (ρ (d * d') u + ρ d u)
  let e : Fin 4 → G := ![1, d, d', d * d']
  have he_mem : ∀ i, e i ∈ Δ := by
    intro i
    fin_cases i
    · simpa [e] using (Δ.one_mem : (1 : G) ∈ Δ)
    · simpa [e] using hd
    · simpa [e] using hd'
    · simpa [e] using Δ.mul_mem hd hd'
  have he_inj : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] at hij
    all_goals first
      | rfl
      | exact absurd hij hd1
      | exact absurd hij hd1.symm
      | exact absurd hij hd'1
      | exact absurd hij hd'1.symm
      | exact absurd hij hdd'
      | exact absurd hij hdd'.symm
      | exact absurd hij hnot'.1
      | exact absurd hij hnot'.1.symm
      | exact absurd hij hnot'.2.1
      | exact absurd hij hnot'.2.1.symm
      | exact absurd hij hnot'.2.2
      | exact absurd hij hnot'.2.2.symm
  let S : Fin 4 → Submodule k Q := fun i => V.map (ρ (e i))
  have hS : ∀ i, w183b2SimpleSub ρ (A₁ ⊔ A₂) (S i) := fun i =>
    w183b2_simple_translate h hV (he_mem i)
  have hne : ∀ i j, i ≠ j → ¬ w183b2NIso ρ (A₁ ⊔ A₂) (S i) (S j) := by
    intro i j hij
    change ¬ w183b2NIso ρ (A₁ ⊔ A₂) (V.map (ρ (e i))) (V.map (ρ (e j)))
    exact w183b2_caseB_not_iso h hB hV (he_mem i) (he_mem j)
      (fun heq => hij (he_inj heq))
  have hVbot : V = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    let x : Fin 4 → Q := fun i => ρ (e i) u
    have hx : ∀ i, x i ∈ S i := fun i => by
      change ρ (e i) u ∈ V.map (ρ (e i))
      exact Submodule.mem_map_of_mem hu
    have hsum : ∑ i, x i = 0 := by
      have h1 : (∑ i : Fin 4, x i) = u + ρ d u + ρ d' u + ρ (d * d') u := by
        change (∑ i : Fin 4, ρ (e i) u) = u + ρ d u + ρ d' u + ρ (d * d') u
        rw [Fin.sum_univ_four]
        simp [e, Matrix.cons_val_two, Matrix.cons_val_three, map_one]
      rw [h1]
      exact hquad_rel u hu
    have hx0 : x 0 = 0 :=
      w183b2_simple_indep ρ (A₁ ⊔ A₂) S hS hne x hx hsum 0
    simpa [x, e] using hx0
  exact hV.1 hVbot

end CFSG.LocalAnalysis.WeakClosure81

end
