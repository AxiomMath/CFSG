module

public import CFSG.RankThree.OddKernel.SectionRep

public section

namespace CFSG.RankThree.OddKernel

open Module

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def IsFlagBasis (G : Subgroup (V ≃ₗ[ZMod p] V)) (b : Basis (Fin 3) (ZMod p) V) : Prop :=
  ∀ g ∈ G, g (b 0) = b 0 ∧ g (b 1) - b 1 ∈ Submodule.span (ZMod p) {b 0} ∧
    g (b 2) - b 2 ∈ Submodule.span (ZMod p) {b 0, b 1}

theorem exists_flag_basis [FiniteDimensional (ZMod p) V] (hV : finrank (ZMod p) V = 3)
    (G : Subgroup (V ≃ₗ[ZMod p] V)) (hG : IsPGroup p G) : ∃ b, IsFlagBasis G b := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V)) DFunLike.coe_injective
  let ρ : Representation (ZMod p) G V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp G.subtype
  have hρ : ∀ (g : G) (v : V), ρ g v = (g : V ≃ₗ[ZMod p] V) v := fun _ _ => rfl
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
  obtain ⟨v₁, hv₁, hfix₁⟩ := exists_ne_zero_fixed hG ρ
  set L₁ := Submodule.span (ZMod p) {v₁} with hL₁def
  have hL₁ : ∀ g : G, L₁ ≤ L₁.comap (ρ g) := by
    intro g x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [Submodule.mem_comap, map_smul, hfix₁]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hL₁dim : finrank (ZMod p) L₁ = 1 := finrank_span_singleton hv₁
  have : Nontrivial (V ⧸ L₁) := by
    apply Module.nontrivial_of_finrank_pos (R := ZMod p)
    have := Submodule.finrank_quotient_add_finrank L₁
    omega
  obtain ⟨q₂, hq₂, hfix₂⟩ := exists_ne_zero_fixed hG (ρ.quotient L₁ hL₁)
  obtain ⟨v₂, rfl⟩ := Submodule.mkQ_surjective L₁ q₂
  have hv₂ : v₂ ∉ L₁ := fun h => hq₂ (by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h)
  have hfix₂' : ∀ g : G, (g : V ≃ₗ[ZMod p] V) v₂ - v₂ ∈ L₁ := by
    intro g
    have h := hfix₂ g
    change Submodule.Quotient.mk (ρ g v₂) = Submodule.Quotient.mk v₂ at h
    exact (Submodule.Quotient.eq L₁).1 h
  set L₂ := Submodule.span (ZMod p) {v₁, v₂} with hL₂def
  have hL₁L₂ : L₁ ≤ L₂ := Submodule.span_mono (by simp)
  have hL₂ : ∀ g : G, L₂ ≤ L₂.comap (ρ g) := by
    intro g x hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hx
    have hv1 : v₁ ∈ L₂ := Submodule.subset_span (Set.mem_insert _ _)
    have hv2 : v₂ ∈ L₂ := Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [Submodule.mem_comap, map_add, map_smul, map_smul, hfix₁, hρ]
    have hgv2 : (g : V ≃ₗ[ZMod p] V) v₂ ∈ L₂ := by
      have : (g : V ≃ₗ[ZMod p] V) v₂ = v₂ + ((g : V ≃ₗ[ZMod p] V) v₂ - v₂) := by abel
      rw [this]
      exact L₂.add_mem hv2 (hL₁L₂ (hfix₂' g))
    exact L₂.add_mem (L₂.smul_mem _ hv1) (L₂.smul_mem _ hgv2)
  have hL₂dim : finrank (ZMod p) L₂ ≤ 2 := by
    have := finrank_span_le_card (R := ZMod p) ({v₁, v₂} : Set V)
    exact this.trans (by simpa using Finset.card_le_two)
  have : Nontrivial (V ⧸ L₂) := by
    apply Module.nontrivial_of_finrank_pos (R := ZMod p)
    have := Submodule.finrank_quotient_add_finrank L₂
    omega
  obtain ⟨q₃, hq₃, hfix₃⟩ := exists_ne_zero_fixed hG (ρ.quotient L₂ hL₂)
  obtain ⟨v₃, rfl⟩ := Submodule.mkQ_surjective L₂ q₃
  have hv₃ : v₃ ∉ L₂ := fun h => hq₃ (by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h)
  have hfix₃' : ∀ g : G, (g : V ≃ₗ[ZMod p] V) v₃ - v₃ ∈ L₂ := by
    intro g
    have h := hfix₃ g
    change Submodule.Quotient.mk (ρ g v₃) = Submodule.Quotient.mk v₃ at h
    exact (Submodule.Quotient.eq L₂).1 h
  have hli : LinearIndependent (ZMod p) ![v₁, v₂, v₃] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hc
    have h2 : c 2 = 0 := by
      by_contra h2
      apply hv₃
      have h3 : c 2 • v₃ = -(c 0 • v₁ + c 1 • v₂) := eq_neg_of_add_eq_zero_right hc
      have : v₃ = (c 2)⁻¹ • -(c 0 • v₁ + c 1 • v₂) := by
        rw [← h3, smul_smul, inv_mul_cancel₀ h2, one_smul]
      rw [this]
      exact L₂.smul_mem _ (L₂.neg_mem (Submodule.mem_span_pair.2 ⟨c 0, c 1, rfl⟩))
    rw [h2, zero_smul, add_zero] at hc
    have h1 : c 1 = 0 := by
      by_contra h1
      apply hv₂
      have h3 : c 1 • v₂ = -(c 0 • v₁) := eq_neg_of_add_eq_zero_right hc
      have : v₂ = (c 1)⁻¹ • -(c 0 • v₁) := by
        rw [← h3, smul_smul, inv_mul_cancel₀ h1, one_smul]
      rw [this]
      exact L₁.smul_mem _ (L₁.neg_mem (L₁.smul_mem _ (Submodule.mem_span_singleton_self _)))
    rw [h1, zero_smul, add_zero] at hc
    have h0 : c 0 = 0 := (smul_eq_zero.1 hc).resolve_right hv₁
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have hb : ⇑b = ![v₁, v₂, v₃] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  refine ⟨b, fun g hg => ?_⟩
  simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  exact ⟨hfix₁ ⟨g, hg⟩, hfix₂' ⟨g, hg⟩, hfix₃' ⟨g, hg⟩⟩

@[expose] noncomputable def flagA (b : Basis (Fin 3) (ZMod p) V) (g : V ≃ₗ[ZMod p] V) : ZMod p :=
  b.coord 0 (g (b 1))

@[expose] noncomputable def flagB (b : Basis (Fin 3) (ZMod p) V) (g : V ≃ₗ[ZMod p] V) : ZMod p :=
  b.coord 1 (g (b 2))

@[expose] noncomputable def flagC (b : Basis (Fin 3) (ZMod p) V) (g : V ≃ₗ[ZMod p] V) : ZMod p :=
  b.coord 0 (g (b 2))

section Coordinates

variable {G : Subgroup (V ≃ₗ[ZMod p] V)} {b : Basis (Fin 3) (ZMod p) V}

theorem flag_apply_one (hb : IsFlagBasis G b) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ G) :
    g (b 1) = b 1 + flagA b g • b 0 := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (hb g hg).2.1
  have hg1 : g (b 1) = b 1 + t • b 0 := by rw [ht]; abel
  have : flagA b g = t := by
    rw [flagA, hg1, map_add, map_smul, Basis.coord_apply, Basis.coord_apply, Basis.repr_self,
      Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    simp
  rw [this, hg1]

theorem flag_apply_two (hb : IsFlagBasis G b) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ G) :
    g (b 2) = b 2 + flagB b g • b 1 + flagC b g • b 0 := by
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 (hb g hg).2.2
  have hg2 : g (b 2) = b 2 + t • b 1 + s • b 0 := by
    rw [add_assoc, add_comm (t • b 1), hst]
    abel
  have hB : flagB b g = t := by
    rw [flagB, hg2]
    simp [Basis.coord_apply]
  have hC : flagC b g = s := by
    rw [flagC, hg2]
    simp [Basis.coord_apply]
  rw [hB, hC, hg2]

theorem flag_mul (hb : IsFlagBasis G b) {g h : V ≃ₗ[ZMod p] V} (hg : g ∈ G) (hh : h ∈ G) :
    flagA b (g * h) = flagA b g + flagA b h ∧ flagB b (g * h) = flagB b g + flagB b h ∧
      flagC b (g * h) = flagC b g + flagC b h + flagA b g * flagB b h := by
  have h0 : g (b 0) = b 0 := (hb g hg).1
  have hgh1 : (g * h) (b 1) = b 1 + (flagA b g + flagA b h) • b 0 := by
    rw [LinearEquiv.mul_apply, flag_apply_one hb hh, map_add, map_smul, h0, flag_apply_one hb hg,
      add_smul]
    abel
  have hgh2 : (g * h) (b 2) = b 2 + (flagB b g + flagB b h) • b 1 +
      (flagC b g + flagC b h + flagA b g * flagB b h) • b 0 := by
    rw [LinearEquiv.mul_apply, flag_apply_two hb hh, map_add, map_add, map_smul, map_smul, h0,
      flag_apply_two hb hg, flag_apply_one hb hg, add_smul, add_smul, add_smul, smul_add,
      smul_smul, mul_comm (flagB b h)]
    abel
  refine ⟨?_, ?_, ?_⟩
  · rw [flagA, hgh1]
    simp [Basis.coord_apply]
  · rw [flagB, hgh2]
    simp [Basis.coord_apply]
  · rw [flagC, hgh2]
    simp [Basis.coord_apply]

theorem flag_eq_one (hb : IsFlagBasis G b) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ G)
    (ha : flagA b g = 0) (hb' : flagB b g = 0) (hc : flagC b g = 0) : g = 1 := by
  apply LinearEquiv.toLinearMap_injective
  refine b.ext fun i => ?_
  fin_cases i
  · exact (hb g hg).1
  · simp [flag_apply_one hb hg, ha]
  · simp [flag_apply_two hb hg, hb', hc]

theorem flag_transvection (hb : IsFlagBasis G b) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ G)
    (ha : flagA b g = 0) (hb' : flagB b g = 0) (x : V) :
    g x = x + (flagC b g • b.coord 2) x • b 0 := by
  have hlin : g.toLinearMap = LinearMap.id + (flagC b g • b.coord 2).smulRight (b 0) := by
    refine b.ext fun i => ?_
    fin_cases i
    · simp [(hb g hg).1, Basis.coord_apply]
    · simp [flag_apply_one hb hg, ha, Basis.coord_apply]
    · simp [flag_apply_two hb hg, hb', Basis.coord_apply]
  have := congrArg (fun f : V →ₗ[ZMod p] V => f x) hlin
  simpa using this

end Coordinates

end CFSG.RankThree.OddKernel
