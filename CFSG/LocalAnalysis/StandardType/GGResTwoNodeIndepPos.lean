module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepCore
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepRefl
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepWeyl

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggIndep_reflGenerated_of_closure {p : ℕ} {G : Type} [Group G] {Bs : Subgroup G} {Λ : Type}
    {φ : Λ → MulAut ↥Bs} (hrefl : ∀ i, GGIsReflection p (φ i)) {A : Subgroup (MulAut ↥Bs)}
    (hA : A = Subgroup.closure (Set.range φ)) : GGReflGenerated p A := by
  rw [GGReflGenerated]
  apply le_antisymm
  · calc A = Subgroup.closure (Set.range φ) := hA
      _ ≤ Subgroup.closure {ψ | ψ ∈ A ∧ GGIsReflection p ψ} := by
          apply Subgroup.closure_mono
          rintro _ ⟨i, rfl⟩
          exact ⟨hA ▸ Subgroup.subset_closure ⟨i, rfl⟩, hrefl i⟩
  · rw [Subgroup.closure_le]
    intro ψ hψ
    exact hψ.1

theorem ggIndep_reflGenerated_sup {p : ℕ} {G : Type} [Group G] {Bs : Subgroup G}
    {A B : Subgroup (MulAut ↥Bs)} (hA : GGReflGenerated p A) (hB : GGReflGenerated p B) :
    GGReflGenerated p (A ⊔ B) := by
  rw [GGReflGenerated] at hA hB ⊢
  apply le_antisymm
  · apply sup_le
    · calc A = Subgroup.closure {ψ | ψ ∈ A ∧ GGIsReflection p ψ} := hA
        _ ≤ Subgroup.closure {ψ | ψ ∈ A ⊔ B ∧ GGIsReflection p ψ} :=
            Subgroup.closure_mono fun ψ hψ => ⟨Subgroup.mem_sup_left hψ.1, hψ.2⟩
    · calc B = Subgroup.closure {ψ | ψ ∈ B ∧ GGIsReflection p ψ} := hB
        _ ≤ Subgroup.closure {ψ | ψ ∈ A ⊔ B ∧ GGIsReflection p ψ} :=
            Subgroup.closure_mono fun ψ hψ => ⟨Subgroup.mem_sup_right hψ.1, hψ.2⟩
  · rw [Subgroup.closure_le]
    intro ψ hψ
    exact hψ.1

theorem ggIndep_pos_prep {G : Type} [Group G] [Finite G] {p N : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (hNT : GGNoTransvection p Bs) {z : G} (hz : z ∈ Bs) {A₁ A₂ : Subgroup (MulAut ↥Bs)}
    (hA : A₁ ⊔ A₂ ≤ ggAutomizer ⊤ Bs) (hmove : ∃ t ∈ A₂, GGIsReflection p t ∧ t ⟨z, hz⟩ ≠ ⟨z, hz⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    (hA₁ : A₁ = Subgroup.closure (Set.range φ)) :
    ∃ (t : MulAut ↥Bs) (ha : V) (αa : Module.Dual (ZMod p) V), t ∈ A₂ ∧
      (∀ w, ggLin (p := p) ι t w = w - αa w • ha) ∧ αa ha = 2 ∧
      αa (ι (Additive.ofMul ⟨z, hz⟩)) ≠ 0 ∧
      ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (e i))) ∪
          {ggLin (p := p) ι t}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  obtain ⟨t, htA₂, htrefl, htz⟩ := hmove
  obtain ⟨ha, αa, hαaha, hform⟩ := exists_of_ggIsReflection (p := p) ι htrefl
  have hw : αa (ι (Additive.ofMul ⟨z, hz⟩)) ≠ 0 := by
    intro h0
    apply htz
    have hlin : ggLin (p := p) ι t (ι (Additive.ofMul ⟨z, hz⟩)) = ι (Additive.ofMul ⟨z, hz⟩) := by
      rw [hform, h0, zero_smul, sub_zero]
    exact (ggLin_fix_iff (p := p) ι t ⟨z, hz⟩).mpr hlin
  have hφsup : ∀ i, φ i ∈ A₁ ⊔ A₂ := fun i =>
    Subgroup.mem_sup_left (by rw [hA₁]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  exact ⟨t, ha, αa, htA₂, hform, hαaha, hw,
    ggIndep_nt hNT hA e hφsup (Subgroup.mem_sup_right htA₂) (ι := ι)⟩

theorem ggIndep_pos_branch (hKG : GGReflClassLargeInput') {G : Type} [Group G] [Finite G] {p N : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) (hN : 9 ≤ N) {Bs : Subgroup G} {z : G} (hz : z ∈ Bs)
    {A₁ A₂ : Subgroup (MulAut ↥Bs)} (hA : A₁ ⊔ A₂ ≤ ggAutomizer ⊤ Bs)
    (hstab : Nat.card ↥((A₁ ⊔ A₂) ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥A₁)
    (hgen₂ : GGReflGenerated p A₂) {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hA₁ : A₁ = Subgroup.closure (Set.range φ))
    (F : GGIndepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨z, hz⟩)))
    {t : MulAut ↥Bs} (htA₂ : t ∈ A₂) {ha : V} {αa : Module.Dual (ZMod p) V}
    (hform : ∀ w, ggLin (p := p) ι t w = w - αa w • ha) (hαa : αa ha = 2)
    (hw : αa (ι (Additive.ofMul ⟨z, hz⟩)) ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (e i))) ∪
          {ggLin (p := p) ι t}),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hnmem : ha ∉ Submodule.span (ZMod p) (Set.range fun i => h (e i)))
    (hpm1 : 5 ≤ p → GGIndepPm1 p N ι (A₁ ⊔ A₂)) :
    GGWeylReflectionGroup p (A₁ ⊔ A₂) := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hφsup : ∀ i, φ i ∈ A₁ ⊔ A₂ := fun i =>
    Subgroup.mem_sup_left (by rw [hA₁]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have htsup : t ∈ A₁ ⊔ A₂ := Subgroup.mem_sup_right htA₂
  have hr : ∀ (i : Fin (N - 1)) (v : V),
      ggLin (p := p) ι (φ (e i)) v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  have hcardV : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = p ^ Module.finrank (ZMod p) V := (FiniteField.pow_finrank_eq_natCard p V).symm
  have hVN : Module.finrank (ZMod p) V ≤ N := ggIndepFrame_finrank_le (by omega) F
  have hBs : Nat.card ↥Bs ≤ p ^ N := by
    rw [hcardV]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hVN
  obtain ⟨hdimV, hirrR⟩ := ggIndepA_top hp (by omega) F
    (fun i => ggLin (p := p) ι (φ (e i))) hr (ggLin (p := p) ι t) ha αa hform hαa hw hnt hnmem hVN
  have hRA : Subgroup.closure (Set.range (fun i : Fin (N - 1) => ggLin (p := p) ι (φ (e i))) ∪
      {ggLin (p := p) ι t}) ≤ (A₁ ⊔ A₂).map (ggLin (p := p) ι) := by
    rw [Subgroup.closure_le]
    rintro y (⟨i, rfl⟩ | hy)
    · exact Subgroup.mem_map.mpr ⟨φ (e i), hφsup (e i), rfl⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_map.mpr ⟨t, htsup, rfl⟩
  have hirrA := ggIndep_absIrred_mono hRA hirrR
  have hgen' : GGReflGenerated p (A₁ ⊔ A₂) :=
    ggIndep_reflGenerated_sup (ggIndep_reflGenerated_of_closure hrefl hA₁) hgen₂
  have hjoin := ggIndep_card_join_le (A₁ ⊔ A₂) ⟨z, hz⟩ hstab
  have hA1 := ggIndep_card_A1 hp (by omega) hz ι hφ hA₁ e F
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hsmall : 8 * Nat.card ↥(A₁ ⊔ A₂) < p ^ (N * (N - 1) / 2) := by
    calc 8 * Nat.card ↥(A₁ ⊔ A₂)
        ≤ 8 * (Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥A₁)) := Nat.mul_le_mul_left 8 hjoin
      _ ≤ 8 * (p ^ N * ((p - 1) * 6 * Nat.factorial N)) :=
          Nat.mul_le_mul_left 8 (Nat.mul_le_mul hBs (Nat.mul_le_mul_left _ hA1))
      _ = 8 * (p ^ N * (6 * (p - 1) * Nat.factorial N)) := by rw [Nat.mul_comm (p - 1) 6]
      _ < p ^ (N * (N - 1) / 2) := ggIndep_order_ineq_N hp3 hN
  exact ggIndep_weyl_of_classify hKG hp ι hdimV hN (A₁ ⊔ A₂) hgen' hirrA hsmall hpm1

theorem ggIndep_pos_weyl (hKG : GGReflClassLargeInput') {G : Type} [Group G] [Finite G] {p N : ℕ}
    [Fact p.Prime] (hp : 5 ≤ p) (hN : 10 ≤ N) {Bs : Subgroup G} (hNT : GGNoTransvection p Bs)
    {z : G} (hz : z ∈ Bs) {A₁ A₂ : Subgroup (MulAut ↥Bs)} (hA : A₁ ⊔ A₂ ≤ ggAutomizer ⊤ Bs)
    (hstab : Nat.card ↥((A₁ ⊔ A₂) ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨z, hz⟩ : ↥Bs)) ≤
      (p - 1) * 6 * Nat.card ↥A₁)
    (hgen₂ : GGReflGenerated p A₂)
    (hmove : ∃ t ∈ A₂, GGIsReflection p t ∧ t ⟨z, hz⟩ ≠ ⟨z, hz⟩)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (e : Fin (N - 1) ≃ Λ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hA₁ : A₁ = Subgroup.closure (Set.range φ))
    (F : GGIndepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨z, hz⟩)))
    (hpm1 : 5 ≤ p → GGIndepPm1 p N ι (A₁ ⊔ A₂)) :
    GGWeylReflectionGroup p (A₁ ⊔ A₂) := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨t, ha, αa, htA₂, hform, hαa, hw, hnt⟩ := ggIndep_pos_prep (N := N) hNT hz hA hmove e hA₁
    (ι := ι)
  by_cases hmem : ha ∈ Submodule.span (ZMod p) (Set.range fun i => h (e i))
  · exfalso
    have hcard := ggIndep_card (by omega) hz (A₁ := A₁) (A₂ := A₂) (by omega) e hφ hA₁ F htA₂ hform
      (Submodule.span (ZMod p) (Set.range fun i => h (e i)))
      (fun i => Submodule.subset_span ⟨i, rfl⟩) hmem hstab
    have hdim : Module.finrank (ZMod p)
        ↥(Submodule.span (ZMod p) (Set.range fun i => h (e i))) = N - 1 := by
      rw [finrank_span_eq_card F.indep]
      simp
    rw [hdim] at hcard
    exact ggIndepA_false_of_mem hKG hp hN F (fun i => ggLin (p := p) ι (φ (e i)))
      (fun i v => hφ (e i) v) (ggLin (p := p) ι t) ha αa hform hαa hw hnt hcard hmem
  · exact ggIndep_pos_branch hKG (by omega) (by omega) hz hA hstab hgen₂ e hφ hrefl hA₁ F htA₂
      hform hαa hw hnt hmem hpm1

end CFSG.StandardType

end
