module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.Quasithin.H13.L828T

variable {W : Type*} [CommGroup W]

@[expose] abbrev QMod (B U : Subgroup W) : Type _ := Additive (↥B ⧸ U.subgroupOf B)

@[expose] def QMod.mk (B U : Subgroup W) (b : ↥B) : QMod B U := Additive.ofMul (QuotientGroup.mk b)

theorem QMod.mk_surjective (B U : Subgroup W) : Function.Surjective (QMod.mk B U) :=
  fun q => by
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (Additive.toMul q)
    exact ⟨b, by simp [QMod.mk, hb]⟩

theorem QMod.mk_add (B U : Subgroup W) (a b : ↥B) :
    QMod.mk B U (a * b) = QMod.mk B U a + QMod.mk B U b := by
  unfold QMod.mk
  rw [QuotientGroup.mk_mul]
  exact ofMul_mul _ _

theorem QMod.mk_one (B U : Subgroup W) : QMod.mk B U 1 = 0 := by
  unfold QMod.mk
  rw [QuotientGroup.mk_one]
  exact ofMul_one

theorem QMod.mk_eq_mk_iff (B U : Subgroup W) (a b : ↥B) :
    QMod.mk B U a = QMod.mk B U b ↔ (a : W) * (b : W)⁻¹ ∈ U := by
  have key : (a : W) * (b : W)⁻¹ = ((a : W)⁻¹ * (b : W))⁻¹ := by
    rw [mul_inv, inv_inv]
  unfold QMod.mk
  rw [Additive.ofMul.injective.eq_iff, QuotientGroup.eq, Subgroup.mem_subgroupOf, key,
    inv_mem_iff]
  exact Iff.rfl

@[expose] def Induces {B U : Subgroup W} (γ : AddMonoid.End (QMod B U)) (f : W → W) : Prop :=
  ∀ b : ↥B, ∃ b' : ↥B, (b' : W) = f b ∧ γ (QMod.mk B U b) = QMod.mk B U b'

theorem exists_induces {B U : Subgroup W} (f : W → W)
    (hmul : ∀ a ∈ B, ∀ b ∈ B, f (a * b) = f a * f b) (hB : ∀ b ∈ B, f b ∈ B)
    (hU : ∀ u ∈ U, f u ∈ U) : ∃ γ : AddMonoid.End (QMod B U), Induces γ f := by
  have hf1 : f 1 = 1 := by
    have h := hmul 1 B.one_mem 1 B.one_mem
    rw [mul_one] at h
    exact mul_eq_left.mp h.symm
  let F : ↥B →* ↥B :=
    { toFun := fun b => ⟨f b, hB b b.2⟩
      map_one' := Subtype.ext hf1
      map_mul' := fun x y => Subtype.ext (hmul x x.2 y y.2) }
  have hle : U.subgroupOf B ≤ (U.subgroupOf B).comap F := by
    intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hU _ (Subgroup.mem_subgroupOf.mp hu)
  refine ⟨MonoidHom.toAdditive (QuotientGroup.map (U.subgroupOf B) (U.subgroupOf B) F hle), ?_⟩
  intro b
  exact ⟨F b, rfl, rfl⟩

theorem Induces.ext_of {B U : Subgroup W} {γ γ' : AddMonoid.End (QMod B U)} {f f' : W → W}
    (h : Induces γ f) (h' : Induces γ' f') (hff : ∀ b ∈ B, f b * (f' b)⁻¹ ∈ U) : γ = γ' := by
  refine AddMonoid.End.ext _ fun x => ?_
  obtain ⟨b, rfl⟩ := QMod.mk_surjective B U x
  obtain ⟨b1, hb1, hγ⟩ := h b
  obtain ⟨b2, hb2, hγ'⟩ := h' b
  rw [hγ, hγ', QMod.mk_eq_mk_iff, hb1, hb2]
  exact hff _ b.2

theorem Induces.mul {B U : Subgroup W} {γ γ' : AddMonoid.End (QMod B U)} {f f' : W → W}
    (h : Induces γ f) (h' : Induces γ' f') : Induces (γ' * γ) (f' ∘ f) := by
  intro b
  obtain ⟨b1, hb1, hγ⟩ := h b
  obtain ⟨b2, hb2, hγ'⟩ := h' b1
  refine ⟨b2, ?_, ?_⟩
  · rw [Function.comp_apply, hb2, hb1]
  · show γ' (γ (QMod.mk B U b)) = QMod.mk B U b2
    rw [hγ, hγ']

theorem induces_one (B U : Subgroup W) : Induces (1 : AddMonoid.End (QMod B U)) id := by
  intro b
  exact ⟨b, rfl, rfl⟩

theorem Induces.pow {B U : Subgroup W} {γ : AddMonoid.End (QMod B U)} {f : W → W}
    (h : Induces γ f) (n : ℕ) : Induces (γ ^ n) (f^[n]) := by
  induction n with
  | zero => rw [pow_zero, Function.iterate_zero]; exact induces_one B U
  | succ n ih => rw [pow_succ, Function.iterate_succ]; exact Induces.mul h ih

theorem Induces.mul_inv_mem_of_eq_one {B U : Subgroup W} {γ : AddMonoid.End (QMod B U)}
    {f : W → W} (h : Induces γ f) (h1 : γ = 1) : ∀ b ∈ B, f b * b⁻¹ ∈ U := by
  intro b hb
  obtain ⟨b', hb', hγ⟩ := h ⟨b, hb⟩
  rw [h1, AddMonoid.End.one_apply, QMod.mk_eq_mk_iff, hb'] at hγ
  have hinv := U.inv_mem hγ
  rwa [mul_inv, inv_inv, mul_comm] at hinv

@[expose] def indSet (B U : Subgroup W) (S : Set (MulAut W)) : Set (AddMonoid.End (QMod B U)) :=
  {γ | ∃ g ∈ S, Induces γ ⇑g}

@[expose] def commutant (B U : Subgroup W) (S : Set (MulAut W)) : Subring (AddMonoid.End (QMod B U)) :=
  Subring.centralizer (indSet B U S)

theorem mem_commutant_iff {B U : Subgroup W} {S : Set (MulAut W)}
    {φ : AddMonoid.End (QMod B U)} :
    φ ∈ commutant B U S ↔ ∀ γ ∈ indSet B U S, γ * φ = φ * γ := by
  unfold commutant
  exact Subring.mem_centralizer_iff

end CFSG.Quasithin.H13.L828T
