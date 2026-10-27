module

public import CFSG.LocalAnalysis.StandardType.GGTWLowPZAux

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nPA_submonoid_inv_mem {P : Type*} [Group P] [Finite P] (T : Submonoid P)
    {g : P} (hg : g ∈ T) : g⁻¹ ∈ T := by
  have h1 : g ^ (orderOf g - 1) * g = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
  have h2 : g⁻¹ = g ^ (orderOf g - 1) := (eq_inv_of_mul_eq_one_left h1).symm
  rw [h2]
  exact T.pow_mem hg _

private lemma l05nPA_card_subgroup {M : Type*} [Monoid M] {S : Set M}
    (hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1)
    (H : Subgroup Mˣ)
    (hH : ∀ u : Mˣ, u ∈ H ↔ (u : M) ∈ Submonoid.closure S) :
    Nat.card ↥H = Nat.card ↥(Submonoid.closure S) := by
  apply Nat.card_eq_of_bijective
    (fun u : ↥H => (⟨(u.1 : M), (hH u.1).mp u.2⟩ : ↥(Submonoid.closure S)))
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Units.ext
    simpa using congrArg Subtype.val hab
  · intro g
    obtain ⟨g', hg'mem, hg'1, hg'2⟩ := hinv (g : M) g.2
    refine ⟨⟨(⟨(g : M), g', hg'1, hg'2⟩ : Mˣ), ?_⟩, ?_⟩
    · exact (hH _).mpr g.2
    · apply Subtype.ext
      rfl

private lemma l05nPA_sub_inv {S S' : Set (Module.End (ZMod 3) (GGDepAE 3 6))}
    (hS : ∀ s ∈ S, s * s = 1) (hsub : S' ⊆ Submonoid.closure S) :
    ∀ g ∈ Submonoid.closure S', ∃ g' ∈ Submonoid.closure S', g * g' = 1 ∧ g' * g = 1 := by
  let M := Module.End (ZMod 3) (GGDepAE 3 6)
  haveI : Finite M :=
    Finite.of_injective (fun f : M => (f : GGDepAE 3 6 → GGDepAE 3 6)) LinearMap.coe_injective
  have hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1 :=
    l05nDA_inv_mem (T := S) (fun t ht =>
      ⟨t, Submonoid.subset_closure ht, hS t ht, hS t ht⟩)
  intro g hg'
  have hg : g ∈ Submonoid.closure S := Submonoid.closure_le.mpr hsub hg'
  obtain ⟨g', hg'mem, hgg', hg'g⟩ := hinv g hg
  let P : Submonoid Mˣ :=
    { carrier := {u | (u : M) ∈ Submonoid.closure S'}
      one_mem' := by
        show ((1 : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_one]
        exact Submonoid.one_mem _
      mul_mem' := by
        intro u v hu hv
        show ((u * v : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_mul]
        exact Submonoid.mul_mem _ hu hv }
  let u : Mˣ := ⟨g, g', hgg', hg'g⟩
  have hu : u ∈ P := by
    change (u : M) ∈ Submonoid.closure S'
    exact hg'
  have huinv : ((u⁻¹ : Mˣ) : M) ∈ Submonoid.closure S' :=
    l05nPA_submonoid_inv_mem P hu
  have hval : ((u⁻¹ : Mˣ) : M) = g' := rfl
  exact ⟨g', hval ▸ huinv, hgg', hg'g⟩

theorem ggDepEL_card_dvd {S S' : Set (Module.End (ZMod 3) (GGDepAE 3 6))}
    (hS : ∀ s ∈ S, s * s = 1) (hsub : S' ⊆ Submonoid.closure S) :
    Nat.card ↥(Submonoid.closure S') ∣ Nat.card ↥(Submonoid.closure S) := by
  let M := Module.End (ZMod 3) (GGDepAE 3 6)
  haveI : Finite M :=
    Finite.of_injective (fun f : M => (f : GGDepAE 3 6 → GGDepAE 3 6)) LinearMap.coe_injective
  have hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1 :=
    l05nDA_inv_mem (T := S) (fun t ht =>
      ⟨t, Submonoid.subset_closure ht, hS t ht, hS t ht⟩)
  have hinv' := l05nPA_sub_inv hS hsub
  let H : Subgroup Mˣ :=
    { carrier := {u | (u : M) ∈ Submonoid.closure S}
      one_mem' := by
        show ((1 : Mˣ) : M) ∈ Submonoid.closure S
        rw [Units.val_one]
        exact Submonoid.one_mem _
      mul_mem' := by
        intro u v hu hv
        show ((u * v : Mˣ) : M) ∈ Submonoid.closure S
        rw [Units.val_mul]
        exact Submonoid.mul_mem _ hu hv
      inv_mem' := by
        intro u hu
        obtain ⟨g', hg'mem, hg'1, hg'2⟩ := hinv (u : M) hu
        have hunit : ((u⁻¹ : Mˣ) : M) * (u : M) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have hcalc : ((u⁻¹ : Mˣ) : M) = g' := by
          calc ((u⁻¹ : Mˣ) : M) = ((u⁻¹ : Mˣ) : M) * 1 := (mul_one _).symm
            _ = ((u⁻¹ : Mˣ) : M) * ((u : M) * g') := by rw [hg'1]
            _ = (((u⁻¹ : Mˣ) : M) * (u : M)) * g' := (mul_assoc _ _ _).symm
            _ = 1 * g' := by rw [hunit]
            _ = g' := one_mul g'
        change ((u⁻¹ : Mˣ) : M) ∈ Submonoid.closure S
        rw [hcalc]
        exact hg'mem }
  let P : Submonoid Mˣ :=
    { carrier := {u | (u : M) ∈ Submonoid.closure S'}
      one_mem' := by
        show ((1 : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_one]
        exact Submonoid.one_mem _
      mul_mem' := by
        intro u v hu hv
        show ((u * v : Mˣ) : M) ∈ Submonoid.closure S'
        rw [Units.val_mul]
        exact Submonoid.mul_mem _ hu hv }
  let H' : Subgroup Mˣ :=
    { carrier := P.carrier
      one_mem' := P.one_mem
      mul_mem' := P.mul_mem
      inv_mem' := fun {u} hu => l05nPA_submonoid_inv_mem P hu }
  have hle : H' ≤ H := by
    intro u hu
    exact Submonoid.closure_le.mpr hsub (show (u : M) ∈ Submonoid.closure S' from hu)
  have hcard : Nat.card ↥H = Nat.card ↥(Submonoid.closure S) :=
    l05nPA_card_subgroup hinv H (fun u => Iff.rfl)
  have hcard' : Nat.card ↥H' = Nat.card ↥(Submonoid.closure S') :=
    l05nPA_card_subgroup hinv' H' (fun u => Iff.rfl)
  have hdv := Subgroup.card_dvd_of_le hle
  rwa [hcard', hcard] at hdv

theorem ggDepEL_center_of_card {S S' : Set (Module.End (ZMod 3) (GGDepAE 3 6))}
    (hsub : S' ⊆ Submonoid.closure S)
    (hcard : Nat.card ↥(Submonoid.closure S) = Nat.card ↥(Submonoid.closure S'))
    (a : Module.End (ZMod 3) (GGDepAE 3 6)) (hcomm : ∀ t ∈ S', a * t = t * a) :
    ∀ g ∈ Submonoid.closure S, a * g = g * a := by
  let M := Module.End (ZMod 3) (GGDepAE 3 6)
  haveI : Finite M :=
    Finite.of_injective (fun f : M => (f : GGDepAE 3 6 → GGDepAE 3 6)) LinearMap.coe_injective
  have hle : Submonoid.closure S' ≤ Submonoid.closure S := Submonoid.closure_le.mpr hsub
  have hset : (Submonoid.closure S' : Set M) = (Submonoid.closure S : Set M) :=
    Set.Finite.eq_of_subset_of_card_le (Set.toFinite (Submonoid.closure S : Set M))
      (fun x hx => hle hx) (le_of_eq hcard)
  intro g hg
  have hg' : g ∈ (Submonoid.closure S' : Set M) := by
    rw [hset]
    exact hg
  refine Submonoid.closure_induction (fun t ht => hcomm t ht) ?_ ?_ hg'
  · rw [mul_one, one_mul]
  · intro x y _ _ hx hy
    calc a * (x * y) = (a * x) * y := (mul_assoc a x y).symm
      _ = (x * a) * y := by rw [hx]
      _ = x * (a * y) := mul_assoc x a y
      _ = x * (y * a) := by rw [hy]
      _ = (x * y) * a := (mul_assoc x y a).symm

end CFSG.StandardType

end
