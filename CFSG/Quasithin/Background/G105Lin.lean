module

public import CFSG.Quasithin.Background.G105Perm
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.G105

open CFSG.Open CFSG.Quasithin.G11 Equiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev NZ (U : Submodule (ZMod 2) V) : Type := {u : U // u ≠ 0}

@[expose] def actNZ (U : Submodule (ZMod 2) V) : (U ≃ₗ[ZMod 2] U) →* Perm (NZ U) where
  toFun g := g.toEquiv.subtypeEquiv fun u => by simp
  map_one' := by
    ext u
    simp
  map_mul' g h := by
    ext u
    simp

theorem zmod2_eq_zero_or_one (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s
  decide

theorem card_NZ [Finite V] (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 2) :
    Nat.card (NZ U) = 3 := by
  classical
  haveI : Fintype U := Fintype.ofFinite U
  have hcard : Fintype.card U = 4 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card, hU]
    norm_num
  have h1 : Fintype.card {u : U // ¬ (u = 0)} = Fintype.card U - Fintype.card {u : U // u = 0} :=
    Fintype.card_subtype_compl _
  rw [Fintype.card_subtype_eq (0 : U), hcard] at h1
  rw [Nat.card_eq_fintype_card]
  exact h1

noncomputable def nzEquiv [Finite V] (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 2) : NZ U ≃ Fin 3 := by
  classical
  haveI : Fintype (NZ U) := Fintype.ofFinite _
  exact Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact card_NZ U hU)

noncomputable def toPerm3 [Finite V] (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 2) : (U ≃ₗ[ZMod 2] U) →* Perm (Fin 3) :=
  (Equiv.permCongrHom (nzEquiv U hU)).toMonoidHom.comp (actNZ U)

theorem actNZ_injective (U : Submodule (ZMod 2) V) : Function.Injective (actNZ U) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  ext u
  by_cases hu : u = 0
  · simp [hu]
  · have := congrArg (fun σ : Perm (NZ U) => ((σ ⟨u, hu⟩ : NZ U) : U)) hg
    simpa [actNZ] using this

theorem toPerm3_injective [Finite V] (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 2) : Function.Injective (toPerm3 U hU) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : actNZ U g = 1 := by
    have h2 : (Equiv.permCongrHom (nzEquiv U hU)) (actNZ U g) = 1 := by
      simpa [toPerm3] using hg
    exact (Equiv.permCongrHom (nzEquiv U hU)).injective (h2.trans (map_one _).symm)
  exact (injective_iff_map_eq_one _).1 (actNZ_injective U) g h1

theorem exists_transvection_of_involution [Finite V] (U : Submodule (ZMod 2) V)
    (hU : Module.finrank (ZMod 2) U = 2) {g : U ≃ₗ[ZMod 2] U} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    ∃ c : V, (∀ u : U, ((g u : U) : V) - (u : V) ∈ Submodule.span (ZMod 2) {c}) ∧
      ∃ u : U, g u ≠ u := by
  have two : ∀ y : U, y + y = 0 := fun y => by
    rw [← two_smul (ZMod 2) y]
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, zero_smul]
  have hgg : ∀ x : U, g (g x) = x := fun x => by
    have := congrArg (fun h : U ≃ₗ[ZMod 2] U => h x) hg2
    simpa using this
  set T : U →ₗ[ZMod 2] U := (g : U →ₗ[ZMod 2] U) - LinearMap.id with hTdef
  have hT : ∀ x, T (T x) = 0 := by
    intro x
    simp only [hTdef, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub,
      hgg]
    have := two (g x - x)
    calc x - g x - (g x - x) = -((g x - x) + (g x - x)) := by abel
      _ = 0 := by rw [this, neg_zero]
  obtain ⟨f, hf0, hfg⟩ : ∃ f : U, f ≠ 0 ∧ g f = f := by
    by_contra H
    push Not at H
    have hTinj : ∀ x, T x = 0 → x = 0 := by
      intro x hx
      have hx' : g x = x := by
        simpa [hTdef, sub_eq_zero] using hx
      by_contra hx0
      exact H x hx0 hx'
    have hT0 : ∀ x, T x = 0 := fun x => hTinj _ (hT x)
    apply hg1
    ext x
    have := hT0 x
    simpa [hTdef, sub_eq_zero] using this
  obtain ⟨u₀, hu₀⟩ : ∃ u : U, g u ≠ u := by
    by_contra H
    push Not at H
    apply hg1
    ext x
    simpa using H x
  have hu0ne : u₀ ≠ 0 := by
    rintro rfl
    exact hu₀ (map_zero g)
  have hu0f : u₀ ≠ f := by
    rintro rfl
    exact hu₀ hfg
  have hli : LinearIndependent (ZMod 2) ![u₀, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases zmod2_eq_zero_or_one s with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp only [zero_smul, one_smul, zero_add] at hst
      exact absurd hst hf0
    · simp only [zero_smul, one_smul, add_zero] at hst
      exact absurd hst hu0ne
    · simp only [one_smul] at hst
      exact absurd (calc u₀ = u₀ + (f + f) := by rw [two f, add_zero]
          _ = (u₀ + f) + f := by abel
          _ = f := by rw [hst, zero_add]) hu0f
  have hspan : Submodule.span (ZMod 2) (Set.range ![u₀, f]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, Fintype.card_fin, hU]
  set c : V := ((g u₀ : U) : V) - (u₀ : V) with hc
  refine ⟨c, fun u => ?_, ⟨u₀, hu₀⟩⟩
  have hu : u ∈ Submodule.span (ZMod 2) (Set.range ![u₀, f]) := by rw [hspan]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hu
  have hgu : g u - u = a 0 • (g u₀ - u₀) := by
    rw [← ha]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, map_add, map_smul, hfg]
    module
  have hgV := congrArg (fun w : U => (w : V)) hgu
  simp only [Submodule.coe_sub, Submodule.coe_smul] at hgV
  rw [hgV, hc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end CFSG.Quasithin.G105
