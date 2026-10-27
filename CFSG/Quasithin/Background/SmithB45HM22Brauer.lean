module

public import CFSG.CharacterTheory.SteinbergBYModularRealization

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY Module

variable {k G : Type*} [Field k] [Group G]

theorem trace_rep_mul_of_scalar {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) {z : G} {c : k} (hz : ρ z = c • LinearMap.id) (g : G) :
    LinearMap.trace k V (ρ (z * g)) = c * LinearMap.trace k V (ρ g) := by
  rw [ρ.map_mul, hz, smul_mul_assoc, Module.End.one_eq_id.symm, one_mul, map_smul, smul_eq_mul]

theorem card_le_of_central [IsAlgClosed k] [Finite G] (p : ℕ) [Fact p.Prime] [CharP k p]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (ρ : ∀ i, Representation k G (V i))
    [∀ i, (ρ i).IsIrreducible] (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j)))
    {z : G} (hz : z ∈ Subgroup.center G) {c : k} (hc : c ≠ 1)
    (hρz : ∀ i, ρ i z = c • LinearMap.id) {N : ℕ} (r : Fin N → G)
    (hcov : ∀ g : G, CFSG.IsPRegular p g →
      (∃ j : Fin N, ∃ e : ℕ, IsConj g (r j * z ^ e)) ∨ IsConj g (z * g)) :
    Fintype.card ι ≤ N := by
  classical
  set χ : ι → G → k := fun i g => LinearMap.trace k (V i) (ρ i g) with hχ
  have hli : LinearIndependent k χ := linearIndependent_trace_of_irreducible ρ hne
  set Res : (G → k) →ₗ[k] (Fin N → k) := LinearMap.funLeft k k r with hRes
  have hprop : ∀ f ∈ Submodule.span k (Set.range χ),
      (∀ g h : G, f (h * g * h⁻¹) = f g) ∧ (∀ g : G, f g = f (Group.pRegular p g)) ∧
        ∀ g : G, f (z * g) = c * f g := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨fun g h => trace_rep_conj (ρ i) g h,
        fun g => trace_rep_eq_trace_pRegular p (ρ i) g,
        fun g => trace_rep_mul_of_scalar (ρ i) (hρz i) g⟩
    | zero => exact ⟨fun _ _ => rfl, fun _ => rfl, fun _ => by simp⟩
    | add x y _ _ hx hy =>
      exact ⟨fun g h => by simp only [Pi.add_apply, hx.1, hy.1],
        fun g => by simp only [Pi.add_apply, ← hx.2.1, ← hy.2.1],
        fun g => by simp only [Pi.add_apply, hx.2.2, hy.2.2, mul_add]⟩
    | smul a x _ hx =>
      exact ⟨fun g h => by simp only [Pi.smul_apply, hx.1],
        fun g => by simp only [Pi.smul_apply, ← hx.2.1],
        fun g => by simp only [Pi.smul_apply, hx.2.2, smul_eq_mul, mul_left_comm]⟩
  have hdisj : Disjoint (Submodule.span k (Set.range χ)) (LinearMap.ker Res) := by
    rw [Submodule.disjoint_def]
    intro f hf hker
    obtain ⟨hcl, hreg, hzf⟩ := hprop f hf
    have hconj : ∀ g g' : G, IsConj g g' → f g = f g' := by
      intro g g' hgg'
      obtain ⟨h, hh⟩ := isConj_iff.mp hgg'
      rw [← hh, hcl]
    have hpow : ∀ (g : G) (e : ℕ), f (g * z ^ e) = c ^ e * f g := by
      intro g e
      induction e with
      | zero => simp
      | succ e ih =>
        have hcomm : g * z ^ (e + 1) = z * (g * z ^ e) := by
          rw [pow_succ', ← mul_assoc, ← mul_assoc, (Subgroup.mem_center_iff.mp hz g).symm]
        rw [hcomm, hzf, ih, pow_succ', mul_assoc]
    have hres : ∀ j, f (r j) = 0 := fun j => congrFun (LinearMap.mem_ker.mp hker) j
    funext g
    rw [Pi.zero_apply, hreg g]
    have hgreg : CFSG.IsPRegular p (Group.pRegular p g) :=
      Group.isPRegular_pRegular p (isOfFinOrder_of_finite g)
    rcases hcov _ hgreg with ⟨j, e, hj⟩ | hfix
    · rw [hconj _ _ hj, hpow, hres, mul_zero]
    · have h1 := hconj _ _ hfix
      rw [hzf] at h1
      have h2 : (1 - c) * f (Group.pRegular p g) = 0 := by
        rw [sub_mul, one_mul, ← h1, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc.symm)
  have hli' : LinearIndependent k (Res ∘ χ) := hli.map hdisj
  have h := hli'.fintype_card_le_finrank
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h

theorem exists_equiv_of_central [IsAlgClosed k] [Finite G] (p : ℕ) [Fact p.Prime] [CharP k p]
    {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (ρ : ∀ i, Representation k G (Fin (d i) → k)) [∀ i, (ρ i).IsIrreducible]
    (hne : ∀ i j, i ≠ j → IsEmpty ((ρ i).Equiv (ρ j)))
    {z : G} (hz : z ∈ Subgroup.center G) {c : k} (hc : c ≠ 1)
    (hρz : ∀ i, ρ i z = c • LinearMap.id) {N : ℕ} (r : Fin N → G)
    (hcov : ∀ g : G, CFSG.IsPRegular p g →
      (∃ j : Fin N, ∃ e : ℕ, IsConj g (r j * z ^ e)) ∨ IsConj g (z * g))
    (hN : N ≤ Fintype.card ι)
    (W : Type*) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k G W) [σ.IsIrreducible] (hσz : σ z = c • LinearMap.id) :
    ∃ i, Nonempty (σ.Equiv (ρ i)) := by
  classical
  by_contra hcon
  push Not at hcon
  let eW : W ≃ₗ[k] (Fin (finrank k W) → k) := (Module.finBasis k W).equivFun
  let d' : Option ι → ℕ := fun o => Option.elim o (finrank k W) d
  let ρ' : ∀ o : Option ι, Representation k G (Fin (d' o) → k) := fun o =>
    match o with
    | none => transportRep eW σ
    | some i => ρ i
  have hirr : ∀ o, (ρ' o).IsIrreducible := by
    intro o
    cases o with
    | none => exact isIrreducible_of_equiv (transportRepEquiv eW σ) inferInstance
    | some i => exact (inferInstance : (ρ i).IsIrreducible)
  have hne' : ∀ o o', o ≠ o' → IsEmpty ((ρ' o).Equiv (ρ' o')) := by
    intro o o' hoo'
    refine ⟨fun φ => ?_⟩
    cases o with
    | none =>
      cases o' with
      | none => exact hoo' rfl
      | some j => exact (hcon j).false ((transportRepEquiv eW σ).trans φ)
    | some i =>
      cases o' with
      | none => exact (hcon i).false (φ.trans (transportRepEquiv eW σ).symm).symm
      | some j =>
        have hij : i ≠ j := fun h => hoo' (h ▸ rfl)
        exact (hne i j hij).false φ
  have hρz' : ∀ o, ρ' o z = c • LinearMap.id := by
    intro o
    cases o with
    | none =>
      apply LinearMap.ext
      intro x
      change eW (σ z (eW.symm x)) = c • x
      rw [hσz, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
      exact congrArg (fun y => c • y) (eW.apply_symm_apply x)
    | some i => exact hρz i
  have h := card_le_of_central p ρ' hne' hz hc hρz' r hcov
  rw [Fintype.card_option] at h
  omega

end CFSG.Quasithin.HM22
