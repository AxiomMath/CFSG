module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.Quasithin.Kleidman

variable {ι X J : Type*} [Group X] [Group J]

theorem lift_pair_fst (e : ι → X) (j : ι → J) (u : FreeGroup ι) :
    (FreeGroup.lift (fun i => (e i, j i)) u).1 = FreeGroup.lift e u := by
  have : (MonoidHom.fst X J).comp (FreeGroup.lift fun i => (e i, j i)) = FreeGroup.lift e := by
    ext i
    simp
  exact congrArg (fun φ => φ u) this

theorem lift_pair_snd (e : ι → X) (j : ι → J) (u : FreeGroup ι) :
    (FreeGroup.lift (fun i => (e i, j i)) u).2 = FreeGroup.lift j u := by
  have : (MonoidHom.snd X J).comp (FreeGroup.lift fun i => (e i, j i)) = FreeGroup.lift j := by
    ext i
    simp
  exact congrArg (fun φ => φ u) this

theorem lift_eq_one_of_lift_eq_one [Finite X] [Finite J] (e : ι → X) (j : ι → J)
    (hj : Subgroup.closure (Set.range j) = ⊤) {c : ℕ}
    (hD : Nat.card (Subgroup.closure (Set.range fun i => (e i, j i))) ≤ c * Nat.card J)
    (hK : ∀ K : Subgroup X, (∀ m ∈ Subgroup.closure (Set.range e), ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K ≤ c → K = ⊥)
    {u : FreeGroup ι} (hu : FreeGroup.lift j u = 1) : FreeGroup.lift e u = 1 := by
  set φ := FreeGroup.lift fun i => (e i, j i) with hφ
  set D := φ.range with hDdef
  have hDcl : D = Subgroup.closure (Set.range fun i => (e i, j i)) :=
    FreeGroup.range_lift_eq_closure
  set ψ : D →* J := (MonoidHom.snd X J).comp D.subtype with hψ
  have hψs : Function.Surjective ψ := by
    intro y
    have hy : y ∈ (FreeGroup.lift j).range := by
      rw [FreeGroup.range_lift_eq_closure, hj]
      trivial
    obtain ⟨v, rfl⟩ := hy
    exact ⟨⟨φ v, v, rfl⟩, lift_pair_snd e j v⟩
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hkerc : Nat.card ψ.ker ≤ c := by
    have h1 : Nat.card D = Nat.card J * Nat.card ψ.ker := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card D ≤ c * Nat.card J := by rw [hDcl]; exact hD
    rw [h1, mul_comm] at h2
    exact Nat.le_of_mul_le_mul_right h2 hJpos
  set f : D →* X := (MonoidHom.fst X J).comp D.subtype with hf
  set K : Subgroup X := ψ.ker.map f with hKdef
  have hKc : Nat.card K ≤ c := by
    refine le_trans (Nat.card_le_card_of_surjective
      (fun d : ψ.ker => (⟨f d, Subgroup.mem_map_of_mem f d.2⟩ : K)) ?_) hkerc
    rintro ⟨_, d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩
  have hKn : ∀ m ∈ Subgroup.closure (Set.range e), ∀ k ∈ K, m * k * m⁻¹ ∈ K := by
    intro m hm k hk
    rw [← FreeGroup.range_lift_eq_closure] at hm
    obtain ⟨v, rfl⟩ := hm
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hk
    set dv : D := ⟨φ v, v, rfl⟩ with hdv
    refine Subgroup.mem_map.mpr ⟨dv * d * dv⁻¹, ?_, ?_⟩
    · rw [MonoidHom.mem_ker] at hd ⊢
      rw [map_mul, map_mul, hd, mul_one, map_inv, mul_inv_cancel]
    · have hfv : f dv = FreeGroup.lift e v := lift_pair_fst e j v
      rw [map_mul, map_mul, map_inv, hfv]
  have hK0 := hK K hKn hKc
  have hdu : (⟨φ u, u, rfl⟩ : D) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact (lift_pair_snd e j u).trans hu
  have : f ⟨φ u, u, rfl⟩ ∈ K := Subgroup.mem_map_of_mem f hdu
  rw [hK0, Subgroup.mem_bot] at this
  exact (lift_pair_fst e j u).symm.trans this

theorem lift_eq_one_iff [Finite X] [Finite J] [IsSimpleGroup J] (e : ι → X) (j : ι → J)
    (hj : Subgroup.closure (Set.range j) = ⊤) {c : ℕ}
    (hD : Nat.card (Subgroup.closure (Set.range fun i => (e i, j i))) ≤ c * Nat.card J)
    (hK : ∀ K : Subgroup X, (∀ m ∈ Subgroup.closure (Set.range e), ∀ k ∈ K, m * k * m⁻¹ ∈ K) →
      Nat.card K ≤ c → K = ⊥)
    (he : ∃ i, e i ≠ 1) (u : FreeGroup ι) :
    FreeGroup.lift e u = 1 ↔ FreeGroup.lift j u = 1 := by
  have hsurj : Function.Surjective (FreeGroup.lift j) :=
    FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr hj
  refine ⟨fun hu => ?_, lift_eq_one_of_lift_eq_one e j hj hD hK⟩
  set N : Subgroup J := (FreeGroup.lift e).ker.map (FreeGroup.lift j) with hN
  have hNn : N.Normal := Subgroup.Normal.map inferInstance _ hsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · have : FreeGroup.lift j u ∈ N := Subgroup.mem_map_of_mem _ ((MonoidHom.mem_ker).mpr hu)
    rwa [h, Subgroup.mem_bot] at this
  · exfalso
    obtain ⟨i, hi⟩ := he
    apply hi
    have hji : j i ∈ N := by rw [h]; trivial
    obtain ⟨v, hv, hvj⟩ := Subgroup.mem_map.mp hji
    have h1 : FreeGroup.lift j (v * (FreeGroup.of i)⁻¹) = 1 := by
      rw [map_mul, map_inv, hvj, FreeGroup.lift_apply_of, mul_inv_cancel]
    have h2 := lift_eq_one_of_lift_eq_one e j hj hD hK h1
    rw [map_mul, map_inv, FreeGroup.lift_apply_of, (MonoidHom.mem_ker).mp hv, one_mul,
      inv_eq_one] at h2
    exact h2

theorem lift_eq_lift_iff {e : ι → X} {j : ι → J}
    (htr : ∀ u : FreeGroup ι, FreeGroup.lift e u = 1 ↔ FreeGroup.lift j u = 1)
    (a b : FreeGroup ι) :
    FreeGroup.lift e a = FreeGroup.lift e b ↔ FreeGroup.lift j a = FreeGroup.lift j b := by
  rw [← mul_inv_eq_one, ← mul_inv_eq_one (a := FreeGroup.lift j a), ← map_inv, ← map_mul,
    ← map_inv, ← map_mul]
  exact htr _

theorem lift_pair_eq_one {e : ι → X} {j : ι → J} {u : FreeGroup ι}
    (he : FreeGroup.lift e u = 1) (hj : FreeGroup.lift j u = 1) :
    FreeGroup.lift (fun i => (e i, j i)) u = 1 :=
  Prod.ext ((lift_pair_fst e j u).trans he) ((lift_pair_snd e j u).trans hj)

end CFSG.Quasithin.Kleidman
