module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeNorm
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly TableB

section Count

variable {G0 : Type} [Group G0]

@[expose] def NodeCount (p : ℕ) (B : Subgroup G0) (x : G0) : Prop :=
  IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({x} : Set G0)))
      (Subgroup.centralizer ({x} : Set G0)) →
    (∀ s ∈ B, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({x} : Set G0)), s * j = j * s) ↔
      s ∈ Subgroup.zpowers x)) →
    p ^ 3 ≤ Nat.card ((B ⊓ LargeEvenLayer (Subgroup.centralizer ({x} : Set G0)) : Subgroup G0))

@[expose] def NormalizesTwoGroup (B : Subgroup G0) : Prop :=
  ∃ U : Subgroup G0, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set G0)

theorem mem_zpowers_map_iff {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Injective f) (a b : M) :
    f a ∈ Subgroup.zpowers (f b) ↔ a ∈ Subgroup.zpowers b := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, hf (by rw [map_zpow, hk])⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← map_zpow, hk]⟩

theorem conj_injective_of_center_bot (hZ : Subgroup.center G0 = ⊥) :
    Function.Injective (MulAut.conj : G0 →* MulAut G0) := by
  rw [injective_iff_map_eq_one]
  intro r hr
  have hc : r ∈ Subgroup.center G0 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut G0 => φ g) hr
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * r = r * g * r⁻¹ * r := by rw [this]
      _ = r * g := by group
  rw [hZ] at hc
  exact Subgroup.mem_bot.mp hc

end Count

theorem isElemAbelian_of_le' {p : ℕ} {G : Type*} [Group G] {V W : Subgroup G}
    (hV : IsElemAbelian p V) (hW : W ≤ V) : IsElemAbelian p W :=
  ⟨⟨⟨fun a b => Subtype.ext (TableB.IsElemAbelian.comm hV (hW a.2) (hW b.2))⟩⟩,
    fun x hx => hV.2 x (hW hx)⟩

section Iso

variable {p : ℕ} {G H : Type} [Group G] [Group H]

theorem nodeCount_of_map (e : G ≃* H) {B : Subgroup G} {x : G}
    (h : NodeCount p (B.map e.toMonoidHom) (e x)) : NodeCount p B x := by
  intro hcomp hcent
  have hC : (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set H) := TableBSymp.map_centralizer_singleton e x
  have hL : LargeEvenLayer (Subgroup.centralizer ({e x} : Set H)) =
      (LargeEvenLayer (Subgroup.centralizer ({x} : Set G))).map e.toMonoidHom := by
    rw [← hC]
    exact largeEvenLayer_map_of_injective _ e.injective _
  have hcomp' : IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({e x} : Set H)))
      (Subgroup.centralizer ({e x} : Set H)) := by
    rw [hL, ← hC]
    exact isComponentOf_map_of_injective _ e.injective hcomp
  have hcent' : ∀ s' ∈ B.map e.toMonoidHom,
      ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({e x} : Set H)), s' * j = j * s') ↔
        s' ∈ Subgroup.zpowers (e x)) := by
    rintro _ ⟨s, hs, rfl⟩
    have h1 : (∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({e x} : Set H)),
        e.toMonoidHom s * j = j * e.toMonoidHom s) ↔
        (∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({x} : Set G)), s * j = j * s) := by
      rw [hL]
      constructor
      · intro hh j hj
        apply e.injective
        simpa using hh (e j) ⟨j, hj, rfl⟩
      · rintro hh _ ⟨j, hj, rfl⟩
        simpa using congrArg e (hh j hj)
    rw [h1]
    exact (hcent s hs).trans (mem_zpowers_map_iff e.toMonoidHom e.injective s x).symm
  have h2 := h hcomp' hcent'
  rw [hL, ← Subgroup.map_inf_eq _ _ _ e.injective, Subgroup.card_map_of_injective e.injective]
    at h2
  exact h2

theorem nodeCount_of_normalizer {B : Subgroup G} {g x y : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) (hxy : g * x * g⁻¹ = y)
    (h : NodeCount p B x) : NodeCount p B y := by
  refine nodeCount_of_map (MulAut.conj g⁻¹) ?_
  have hB : B.map (MulAut.conj g⁻¹).toMonoidHom = B := by
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * w * g⁻¹⁻¹)).mpr (by
        simpa [mul_assoc] using hw)
      simpa [MulAut.conj_apply] using this
    · intro hz
      refine ⟨g * z * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg z).mp hz, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hy : (MulAut.conj g⁻¹) y = x := by
    rw [← hxy]
    simp [MulAut.conj_apply, mul_assoc]
  rw [hB, hy]
  exact h

end Iso

end CFSG.StandardType.SmallExc

end
