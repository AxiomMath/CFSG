module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_dep_fixed_iff (D : GGQ2Lin 3) (S : Set D.ι) (v : D.V) :
    (∀ g ∈ D.parab S, g v = v) ↔ ∀ k ∈ S, D.root k v = 0 := by
  constructor
  · intro h k hk
    have hmem : D.simpleRefl k ∈ D.parab S :=
      Subgroup.subset_closure ⟨k, hk, rfl⟩
    have h2 : D.root k v • D.coroot k = 0 := by
      have h1 : D.simpleRefl k v = v := h (D.simpleRefl k) hmem
      rw [GGQ2Lin.simpleRefl, Module.reflection_apply] at h1
      exact sub_eq_self.mp h1
    have hc : D.coroot k ≠ 0 := by
      intro h0
      have h3 := D.root_coroot_self k
      rw [h0, map_zero] at h3
      exact (by decide : (0 : ZMod 3) ≠ 2) h3
    exact (smul_eq_zero.mp h2).resolve_right hc
  · intro h
    show ∀ g ∈ Subgroup.closure (D.simpleRefl '' S), g v = v
    intro g hg
    exact Subgroup.closure_induction (k := D.simpleRefl '' S) (p := fun g _ => g v = v)
      (fun x hx => by
        rcases hx with ⟨k, hk, rfl⟩
        rw [GGQ2Lin.simpleRefl, Module.reflection_apply, h k hk, zero_smul, sub_zero])
      rfl
      (fun x y _ _ hx hy => by rw [LinearEquiv.mul_apply, hy, hx])
      (fun x _ hx => by
        have h1 : x.symm (x v) = v := x.symm_apply_apply v
        rw [hx] at h1
        exact h1)
      hg

private theorem lr7db_ker_pi (D : GGQ2Lin 3) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x}) :
    LinearMap.ker (LinearMap.pi fun k : {k // k ≠ D.a} => D.root k.1) =
      Submodule.span (ZMod 3) {x} := by
  ext v
  rw [LinearMap.mem_ker]
  constructor
  · intro hv
    rw [← hx v]
    refine (ggQ2_dep_fixed_iff D {k | k ≠ D.a} v).mpr ?_
    intro k hk
    have := congrFun hv ⟨k, hk⟩
    simpa [LinearMap.pi_apply] using this
  · intro hv
    have hroot : ∀ k ∈ {k | k ≠ D.a}, D.root k v = 0 :=
      (ggQ2_dep_fixed_iff D {k | k ≠ D.a} v).mp ((hx v).mpr hv)
    funext i
    simpa [LinearMap.pi_apply] using hroot i.1 i.2

private theorem lr7db_finrank_range_pi (D : GGQ2Lin 3) :
    Module.finrank (ZMod 3)
        (LinearMap.range (LinearMap.pi fun k : {k // k ≠ D.a} => D.root k.1)) =
      Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range fun k : {k // k ≠ D.a} => D.root k)) := by
  classical
  let ev : D.V →ₗ[ZMod 3] ({k // k ≠ D.a} → ZMod 3) := LinearMap.pi fun k => D.root k.1
  have hroot : ∀ i : {k // k ≠ D.a}, ev.dualMap (LinearMap.proj i) = D.root i.1 := by
    intro i
    ext v
    simp [ev, LinearMap.dualMap_apply, LinearMap.proj_apply, LinearMap.pi_apply]
  have hproj : Submodule.span (ZMod 3)
      (Set.range fun i : {k // k ≠ D.a} =>
        (LinearMap.proj i : ({k // k ≠ D.a} → ZMod 3) →ₗ[ZMod 3] ZMod 3)) = ⊤ := by
    have hb : (Pi.basisFun (ZMod 3) {k // k ≠ D.a}).dualBasis =
        (fun i : {k // k ≠ D.a} =>
          (LinearMap.proj i : ({k // k ≠ D.a} → ZMod 3) →ₗ[ZMod 3] ZMod 3)) := by
      funext i
      apply LinearMap.ext
      intro f
      rw [Basis.dualBasis_apply, Pi.basisFun_repr, LinearMap.proj_apply]
    rw [← hb, (Pi.basisFun (ZMod 3) {k // k ≠ D.a}).dualBasis.span_eq]
  have hrange : ev.dualMap.range =
      Submodule.span (ZMod 3) (Set.range fun k : {k // k ≠ D.a} => D.root k) := by
    rw [LinearMap.range_eq_map, ← hproj, Submodule.map_span]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨a, ha, rfl⟩
      obtain ⟨i, rfl⟩ := ha
      rw [hroot i]
      exact Submodule.subset_span ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change D.root i.1 ∈ _
      rw [← hroot i]
      exact Submodule.subset_span ⟨LinearMap.proj i, ⟨i, rfl⟩, rfl⟩
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range ev, hrange]

theorem ggQ2_dep_finrank_eq (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V] (x : D.V)
    (hx0 : x ≠ 0)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x}) :
    Module.finrank (ZMod 3) D.V =
      Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range (fun k : {k // k ≠ D.a} => D.root k))) + 1 := by
  classical
  let ev : D.V →ₗ[ZMod 3] ({k // k ≠ D.a} → ZMod 3) := LinearMap.pi fun k => D.root k.1
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  dsimp only [ev] at hrn
  rw [lr7db_ker_pi D x hx, finrank_span_singleton hx0, lr7db_finrank_range_pi D] at hrn
  exact hrn.symm

theorem ggQ2_dep_finrank_le (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V] (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x}) :
    Module.finrank (ZMod 3) D.V ≤ Fintype.card D.ι := by
  classical
  by_cases hx0 : x = 0
  · let ev : D.V →ₗ[ZMod 3] ({k // k ≠ D.a} → ZMod 3) := LinearMap.pi fun k => D.root k.1
    have hker : LinearMap.ker ev = ⊥ := by
      dsimp only [ev]
      rw [lr7db_ker_pi D x hx, hx0, Submodule.span_zero_singleton]
    have hrn := LinearMap.finrank_range_add_finrank_ker ev
    rw [hker, finrank_bot, add_zero] at hrn
    have hrange : Module.finrank (ZMod 3) (LinearMap.range ev) ≤
        Fintype.card {k // k ≠ D.a} := by
      have h := Submodule.finrank_le (LinearMap.range ev)
      rwa [Module.finrank_fintype_fun_eq_card] at h
    calc Module.finrank (ZMod 3) D.V
        = Module.finrank (ZMod 3) (LinearMap.range ev) := hrn.symm
      _ ≤ Fintype.card {k // k ≠ D.a} := hrange
      _ ≤ Fintype.card D.ι := Fintype.card_subtype_le _
  · have h2 := ggQ2_dep_finrank_eq D x hx0 hx
    have hle : Module.finrank (ZMod 3)
        (Submodule.span (ZMod 3) (Set.range fun k : {k // k ≠ D.a} => D.root k)) ≤
        Fintype.card {k // k ≠ D.a} := by
      rw [← lr7db_finrank_range_pi D]
      have h := Submodule.finrank_le
        (LinearMap.range (LinearMap.pi fun k : {k // k ≠ D.a} => D.root k.1))
      rwa [Module.finrank_fintype_fun_eq_card] at h
    have hcard : Fintype.card {k // k ≠ D.a} + 1 = Fintype.card D.ι := by
      change Fintype.card {k // ¬ k = D.a} + 1 = Fintype.card D.ι
      have h := Fintype.card_subtype_compl (α := D.ι) (fun k => k = D.a)
      rw [Fintype.card_subtype_eq] at h
      have h' : Fintype.card {k // ¬ k = D.a} = Fintype.card D.ι - 1 := h
      rw [h']
      exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨D.a⟩)
    omega

private theorem lr7db_pairing_sum (D : GGQ2Lin 3) (c : D.ι → ZMod 3)
    (hc : ∑ k, c k • D.coroot k = 0) (i : D.ι) :
    ∑ j, (D.cartan i j : ZMod 3) * c j = 0 := by
  have happ : (∑ k, c k • D.root i (D.coroot k)) = 0 := by
    have h : D.root i (∑ k, c k • D.coroot k) = 0 := by rw [hc, map_zero]
    rw [map_sum] at h
    simpa only [map_smul] using h
  calc ∑ j, (D.cartan i j : ZMod 3) * c j
      = ∑ j, c j • D.root i (D.coroot j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [D.pairing i j, smul_eq_mul, mul_comm]
    _ = 0 := happ

theorem ggQ2_dep_relation (D : GGQ2Lin 3) [FiniteDimensional (ZMod 3) D.V] (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hB : ¬ D.Basis) :
    ∃ c : D.ι → ZMod 3, c ≠ 0 ∧ (∑ k, c k • D.coroot k = 0) ∧
      ∀ i, ∑ j, (D.cartan i j : ZMod 3) * c j = 0 := by
  classical
  have hnotLI : ¬ LinearIndependent (ZMod 3) D.coroot := by
    intro hLI
    have hcard := LinearIndependent.fintype_card_le_finrank hLI
    have hle := ggQ2_dep_finrank_le D x hx
    exact hB ⟨hLI, le_antisymm hcard hle⟩
  obtain ⟨c, hc, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hnotLI
  refine ⟨c, ?_, hc, fun i => lr7db_pairing_sum D c hc i⟩
  intro hc0
  exact hi0 (by rw [hc0]; rfl)

end CFSG.StandardType

end
