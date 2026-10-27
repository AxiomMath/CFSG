module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.InvariantOrder
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.NaturalCover

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

theorem card_section_pow {A V Z D : Subgroup G} {α : ↥A →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModulesVia A V Z α dual k) (hDV : D ≤ V) (hZD : Z ≤ D)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) :
    ∃ r s : ℕ, Nat.card D = Nat.card Z * (Nat.card F ^ 3) ^ r ∧
      Nat.card V = Nat.card D * (Nat.card F ^ 3) ^ s := by
  obtain ⟨hAN, hZV, β, hβs, hβk, hβact⟩ := h
  have hAV : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V := fun a ha v hv =>
    (Subgroup.mem_normalizer_iff.mp (hAN ha) v).mp hv
  set φ : ↥D →* Multiplicative (Fin k → Fin 3 → F) := β.comp (Subgroup.inclusion hDV) with hφ
  have hφker : φ.ker = Z.subgroupOf D := by
    ext x
    rw [MonoidHom.mem_ker]
    show β (Subgroup.inclusion hDV x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hβk]
    rfl
  have hcZ : ∀ {W : Subgroup G}, Z ≤ W → Nat.card ↥(Z.subgroupOf W) = Nat.card ↥Z := by
    intro W hZW
    rw [← Subgroup.card_map_of_injective W.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hZW]
  have hD : Nat.card ↥D = Nat.card ↥Z * Nat.card ↥φ.range := by
    have := Subgroup.card_ker_mul_card_range φ
    rw [hφker, hcZ hZD] at this
    exact this.symm
  have hV : Nat.card ↥V = Nat.card ↥Z * Nat.card (Multiplicative (Fin k → Fin 3 → F)) := by
    have := Subgroup.card_ker_mul_card_range β
    rw [hβk, hcZ hZV, MonoidHom.range_eq_top_of_surjective β hβs, Subgroup.card_top] at this
    exact this.symm
  have hT : Nat.card (Multiplicative (Fin k → Fin 3 → F)) = (Nat.card F ^ 3) ^ k := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin]
  let e := MulEquiv.piMultiplicative (fun _ : Fin k => Fin 3 → F)
  have hUc : Nat.card (Multiplicative (Fin 3 → F)) = Nat.card F ^ 3 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin]
  have hinv : ∀ f ∈ tvActs F, ∀ w ∈ φ.range.map e.toMonoidHom, (fun i => f (w i)) ∈ φ.range.map e.toMonoidHom := by
    rintro f ⟨l, j, hlj, t, rfl⟩ _ ⟨x, ⟨d, rfl⟩, rfl⟩
    obtain ⟨γ, hγ⟩ := exists_moduleAct_eq dual l j hlj t
    obtain ⟨a, ha⟩ := hα γ
    have hdV : (d : G) ∈ V := hDV d.2
    have hmem : (a : G) * d * (a : G)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hAD a.2) d).mp d.2
    refine ⟨φ ⟨_, hmem⟩, ⟨⟨_, hmem⟩, rfl⟩, ?_⟩
    funext i
    have h1 := hβact a ⟨d, hdV⟩ ⟨_, hAV a a.2 d hdV⟩ rfl i
    rw [ha, hγ] at h1
    show Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨(a : G) * d * (a : G)⁻¹, hAV a a.2 d hdV⟩) i) =
      matAct (transvection l j t) (Multiplicative.ofAdd (Multiplicative.toAdd (β ⟨d, hdV⟩) i))
    rw [h1]
    rfl
  obtain ⟨r, hr⟩ := card_invariant_pow (tvActs F) (fun W hW => irreducible_tv W hW) k _ hinv
  have hrc : Nat.card ↥φ.range = (Nat.card F ^ 3) ^ r := by
    rw [← hUc, ← hr]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv)
  have hF1 : 1 < Nat.card F := Finite.one_lt_card
  have hq1 : 1 < Nat.card F ^ 3 := Nat.one_lt_pow (by norm_num) hF1
  have hdvd : (Nat.card F ^ 3) ^ r ∣ (Nat.card F ^ 3) ^ k := by
    have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [hrc, hT] at this
  have hrk : r ≤ k := (Nat.pow_dvd_pow_iff_le_right hq1).mp hdvd
  refine ⟨r, k - r, by rw [hD, hrc], ?_⟩
  rw [hV, hT, hD, hrc, mul_assoc, ← pow_add, Nat.add_sub_cancel' hrk]

end Stellmacher.CD.L3YC

end CFSG.Quasithin
