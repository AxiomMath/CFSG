module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSLBasic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

section Invol

variable {R : Type*} [Ring R]

structure IsInvol (T : R → R) : Prop where
  map_add : ∀ x y, T (x + y) = T x + T y
  map_mul : ∀ x y, T (x * y) = T y * T x
  map_one : T 1 = 1
  invol : ∀ x, T (T x) = x

@[expose] def unitaryOf {T : R → R} (hT : IsInvol T) : Subgroup Rˣ where
  carrier := {g | T (g : R) * (g : R) = 1}
  one_mem' := by
    show T ((1 : Rˣ) : R) * _ = 1
    rw [Units.val_one, hT.map_one, one_mul]
  mul_mem' {g h} hg hh := by
    have hg' : T (g : R) * (g : R) = 1 := hg
    have hh' : T (h : R) * (h : R) = 1 := hh
    show T ((g * h : Rˣ) : R) * _ = 1
    rw [Units.val_mul, hT.map_mul]
    calc T (h : R) * T (g : R) * ((g : R) * (h : R))
        = T (h : R) * (T (g : R) * (g : R)) * (h : R) := by simp only [mul_assoc]
      _ = 1 := by rw [hg', mul_one, hh']
  inv_mem' {g} hg := by
    show T ((g⁻¹ : Rˣ) : R) * _ = 1
    have hg' : T (g : R) * (g : R) = 1 := hg
    have h1 : T (g : R) = ((g⁻¹ : Rˣ) : R) := by
      calc T (g : R) = T (g : R) * ((g * g⁻¹ : Rˣ) : R) := by
            rw [mul_inv_cancel, Units.val_one, mul_one]
        _ = _ := by rw [Units.val_mul, ← mul_assoc, hg', one_mul]
    have h2 : T ((g⁻¹ : Rˣ) : R) * T (g : R) = 1 := by
      rw [← hT.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, hT.map_one]
    rwa [h1] at h2

theorem mem_unitaryOf {T : R → R} {hT : IsInvol T} {g : Rˣ} :
    g ∈ unitaryOf hT ↔ T (g : R) * (g : R) = 1 :=
  Iff.rfl

theorem IsInvol.map_zero {T : R → R} (hT : IsInvol T) : T 0 = 0 := by
  have h := hT.map_add 0 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

theorem IsInvol.injective {T : R → R} (hT : IsInvol T) : Function.Injective T :=
  fun x y h => by rw [← hT.invol x, h, hT.invol]

theorem IsInvol.surjective {T : R → R} (hT : IsInvol T) : Function.Surjective T :=
  fun x => ⟨T x, hT.invol x⟩

end Invol

section MatInvol

variable {D : Type*} [Field D] {d : ℕ}

abbrev matUnitary {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D}
    (hT : IsInvol T) : Subgroup (GL (Fin d) D) :=
  unitaryOf hT

theorem mem_matUnitary {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D}
    {hT : IsInvol T} {g : GL (Fin d) D} :
    g ∈ matUnitary hT ↔
      T (g : Matrix (Fin d) (Fin d) D) * (g : Matrix (Fin d) (Fin d) D) = 1 :=
  Iff.rfl

end MatInvol

section Core

variable {G : Type*} [Group G]

@[expose] def HasCore (U : Subgroup G) : Prop :=
  ∃ S : Subgroup G, S ≤ U ∧ (∀ u ∈ U, ∀ s ∈ S, u * s * u⁻¹ ∈ S) ∧
    (∃ k, LayerFacts.ggDer U k ≤ S) ∧
    (S = ⊥ ∨ (CFSG.IsQuasisimple S ∧
      ∀ z ∈ S, (∀ y ∈ S, z * y = y * z) → z ^ 2 = 1 → z = 1))

theorem ggDer_eq_map_derivedSeries (U : Subgroup G) (k : ℕ) :
    LayerFacts.ggDer U k = (derivedSeries U k).map U.subtype := by
  induction k with
  | zero => rw [LayerFacts.ggDer_zero, derivedSeries_zero, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  | succ k ih => rw [LayerFacts.ggDer_succ, ih, derivedSeries_succ, Subgroup.map_commutator]

theorem exists_ggDer_eq_bot {U : Subgroup G} (hU : Group.IsSolvable U) :
    ∃ k, LayerFacts.ggDer U k = ⊥ := by
  obtain ⟨k, hk⟩ := hU.solvable
  exact ⟨k, by rw [ggDer_eq_map_derivedSeries, hk, Subgroup.map_bot]⟩

theorem hasCore_of_isSolvable {U : Subgroup G} (hU : Group.IsSolvable U) : HasCore U := by
  obtain ⟨k, hk⟩ := exists_ggDer_eq_bot hU
  refine ⟨⊥, bot_le, fun u _ s hs => ?_, ⟨k, hk.le⟩, Or.inl rfl⟩
  rw [Subgroup.mem_bot.mp hs, mul_one, mul_inv_cancel]
  exact Subgroup.one_mem _

end Core

end LayerCores

end CFSG.StandardType
