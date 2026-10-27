module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenElt
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Torus

public section

namespace CFSG.StandardType

open Multiplicative

section Reflection

variable {p k : ℕ}

@[expose] noncomputable def torusReflAut (c : (Fin k → ZMod p) →ₗ[ZMod p] ZMod p)
    (δ : Fin k → ZMod p) (h : c δ = 2) : MulAut (Multiplicative (Fin k → ZMod p)) :=
  AddEquiv.toMultiplicative (Module.reflection h).toAddEquiv

theorem torusReflAut_apply (c : (Fin k → ZMod p) →ₗ[ZMod p] ZMod p) (δ : Fin k → ZMod p)
    (h : c δ = 2) (v : Fin k → ZMod p) :
    torusReflAut c δ h (ofAdd v) = ofAdd (v - c v • δ) := by
  simp [torusReflAut, Module.reflection_apply]

theorem torusReflAut_mul_self (c : (Fin k → ZMod p) →ₗ[ZMod p] ZMod p) (δ : Fin k → ZMod p)
    (h : c δ = 2) : torusReflAut c δ h * torusReflAut c δ h = 1 := by
  refine MulEquiv.ext fun v => ?_
  have := Module.involutive_reflection h (toAdd v)
  simpa [torusReflAut] using congrArg ofAdd this

theorem torusReflAut_pow_pred (hp : p.Prime) (hp2 : p ≠ 2)
    (c : (Fin k → ZMod p) →ₗ[ZMod p] ZMod p) (δ : Fin k → ZMod p) (h : c δ = 2) :
    torusReflAut c δ h ^ (p - 1) = 1 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have h1 : p - 1 = 2 * m := by omega
  rw [h1, pow_mul, sq, torusReflAut_mul_self, one_pow]

theorem card_fix_torusReflAut (hp : p.Prime) (hp2 : p ≠ 2)
    (c : (Fin k → ZMod p) →ₗ[ZMod p] ZMod p) (δ : Fin k → ZMod p) (h : c δ = 2) :
    Nat.card {f : Multiplicative (Fin k → ZMod p) // torusReflAut c δ h f = f} * p =
      Nat.card (Multiplicative (Fin k → ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h1))
  have hδ : ∀ a : ZMod p, a • δ = 0 → a = 0 := fun a ha => by
    have h3 := congrArg c ha
    rw [map_smul, h, map_zero, smul_eq_mul] at h3
    exact (mul_eq_zero.mp h3).resolve_right h2
  have hsurj : Function.Surjective c.toAddMonoidHom := fun a =>
    ⟨(a / 2) • δ, by
      show c ((a / 2) • δ) = a
      rw [map_smul, h, smul_eq_mul]
      field_simp⟩
  have hker : ∀ f : Multiplicative (Fin k → ZMod p),
      torusReflAut c δ h f = f ↔ toAdd f ∈ c.toAddMonoidHom.ker := by
    intro f
    have h1 : torusReflAut c δ h f = ofAdd (toAdd f - c (toAdd f) • δ) := by
      rw [← torusReflAut_apply c δ h (toAdd f), ofAdd_toAdd]
    rw [h1, AddMonoidHom.mem_ker]
    constructor
    · intro h3
      have h4 := congrArg toAdd h3
      simp only [toAdd_ofAdd] at h4
      exact hδ _ (sub_eq_self.mp h4)
    · intro h3
      have h4 : c (toAdd f) = 0 := h3
      rw [h4, zero_smul]
      simp
  rw [Nat.card_congr (Equiv.subtypeEquiv (Multiplicative.toAdd (α := Fin k → ZMod p)) hker),
    Nat.card_congr (Multiplicative.toAdd (α := Fin k → ZMod p))]
  have h5 := AddSubgroup.card_ker_mul_card_of_surjective hsurj
  rwa [Nat.card_zmod] at h5

theorem torusReflAut_mem_inducedReflSet (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    (τ : Multiplicative (Fin k → ZMod p) →* R) (c : (Fin k → ZMod p) →ₗ[ZMod p] ZMod p)
    (δ : Fin k → ZMod p) (h : c δ = 2) (w : R)
    (hw : ∀ v : Fin k → ZMod p, w * τ (ofAdd v) * w⁻¹ = τ (ofAdd (v - c v • δ))) :
    torusReflAut c δ h ∈ ggTorusInducedReflSet p τ := by
  refine ⟨torusReflAut_pow_pred hp hp2 c δ h, card_fix_torusReflAut hp hp2 c δ h, w, fun f => ?_⟩
  have h1 := hw (toAdd f)
  rw [ofAdd_toAdd] at h1
  rw [h1, ← torusReflAut_apply c δ h (toAdd f), ofAdd_toAdd]

end Reflection

section Section

theorem exists_torus_section_of_reflections {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type}
    [Group R] (e : Multiplicative (Fin d → ZMod p) →* R)
    (c : Fin d → (Fin d → ZMod p) →ₗ[ZMod p] ZMod p) (hc : ∀ i, c i (Pi.single i 1) = 2)
    (n : Fin d → R)
    (hn : ∀ i v, n i * e (ofAdd v) * (n i)⁻¹ = e (ofAdd (v - c i v • Pi.single i 1)))
    {L' : Type} [Group L'] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') :
    ∃ σ : Multiplicative (Fin d → ZMod p) →* L', ψ.comp σ = e := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  set τ := TableBF4.piTorus e with hτdef
  have hcomm : ∀ x ∈ τ.range.comap ψ, ∀ y ∈ τ.range.comap ψ, x * y = y * x := by
    rw [hτdef, TableBF4.range_piTorus]
    exact CFSG.RankThree.CentralCover.reflection_comap_comm hψ hker hp hp2 e c hc n hn
  have hinv : ∀ i : Fin d, ∃ w : R,
      w * TableBSymp.torusBasis τ i * w⁻¹ = (TableBSymp.torusBasis τ i)⁻¹ := by
    intro i
    refine ⟨n i, ?_⟩
    rw [hτdef, TableBF4.torusBasis_piTorus, hn, hc, ← map_inv, ← ofAdd_neg]
    congr 2
    rw [two_smul]
    abel
  obtain ⟨σ, hσ⟩ := TableBF4.exists_torus_section_of_comm hψ hker hodd τ hcomm hinv
  refine ⟨σ.comp (MulEquiv.piMultiplicative fun _ : Fin d => ZMod p).toMonoidHom, ?_⟩
  rw [← MonoidHom.comp_assoc, hσ, hτdef]
  ext f
  simp [TableBF4.piTorus]

end Section

section Closure

theorem exists_mem_closure_of_conj_mem_closure {M V ι : Type*} [Group M] [Group V] (T : V →* M)
    (x : ι → M) (s : ι → MulAut V) (hx : ∀ i v, x i * T v * (x i)⁻¹ = T (s i v)) {y : M}
    (hy : y ∈ Subgroup.closure (Set.range x)) :
    ∃ u ∈ Subgroup.closure (Set.range s), ∀ v, y * T v * y⁻¹ = T (u v) := by
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨s i, Subgroup.subset_closure ⟨i, rfl⟩, hx i⟩
  | one => exact ⟨1, one_mem _, fun v => by simp⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨u, hu, huy⟩ := ihy
    obtain ⟨u', hu', hu'z⟩ := ihz
    refine ⟨u * u', mul_mem hu hu', fun v => ?_⟩
    calc y * z * T v * (y * z)⁻¹ = y * (z * T v * z⁻¹) * y⁻¹ := by group
      _ = y * T (u' v) * y⁻¹ := by rw [hu'z]
      _ = T (u (u' v)) := huy _
  | inv y _ ih =>
    obtain ⟨u, hu, huy⟩ := ih
    refine ⟨u⁻¹, inv_mem hu, fun v => ?_⟩
    have h1 := huy (u⁻¹ v)
    rw [MulAut.apply_inv_self] at h1
    calc y⁻¹ * T v * y⁻¹⁻¹ = y⁻¹ * (y * T (u⁻¹ v) * y⁻¹) * y := by rw [h1]; group
      _ = T (u⁻¹ v) := by group

end Closure

end CFSG.StandardType

end
