module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocQG
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocGeomD

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

namespace Ctx

variable {G : Type} [Group G]
  (C : Ctx G)

@[expose] noncomputable def pre1 (A : Subgroup G) : Subgroup Y := (A.comap C.φ1).map P1.subtype

theorem mem_pre1 {A : Subgroup G} {y : Y} : y ∈ C.pre1 A ↔ y ∈ P1 ∧ C.Φ1 y ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show C.Φ1 (x : Y) ∈ A
    rw [C.Φ1_of_mem x.2]
    exact hx
  · rintro ⟨hy, hA⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    show C.φ1 ⟨y, hy⟩ ∈ A
    rw [← C.Φ1_of_mem hy]
    exact hA

theorem pre1_le {A : Subgroup G} : C.pre1 A ≤ P1 := fun _ hy => (C.mem_pre1.1 hy).1

theorem card_pre1 {A : Subgroup G} (hA : A ≤ C.φ1.range) :
    Nat.card (C.pre1 A) = Nat.card A := by
  rw [pre1, Subgroup.card_map_of_injective P1.subtype_injective]
  have := Subgroup.card_map_of_injective C.inj1 (K := A.comap C.φ1)
  rw [Subgroup.map_comap_eq_self hA] at this
  exact this.symm

@[expose] def IsPt (u : G) : Prop := ∃ g : G, u = g * C.z * g⁻¹

@[expose] def IsLn (W : Subgroup G) : Prop :=
  ∃ g : G, W = C.V2.map (MulAut.conj g).toMonoidHom

theorem z_sq : C.z * C.z = 1 := by
  rw [z_def, ← C.Φ1_mul mem_P1_xY mem_P1_xY, xY_sq, C.Φ1_one]

theorem tG_sq : C.tG * C.tG = 1 := by
  rw [tG_def, ← C.Φ2_mul (Vsub_le_P2 tPrime_mem_Vsub) (Vsub_le_P2 tPrime_mem_Vsub), tPrime_sq,
    C.Φ2_one]

theorem isPt_sq {u : G} (hu : C.IsPt u) : u * u = 1 := by
  obtain ⟨g, rfl⟩ := hu
  calc g * C.z * g⁻¹ * (g * C.z * g⁻¹) = g * (C.z * C.z) * g⁻¹ := by group
    _ = 1 := by rw [C.z_sq]; group

theorem isPt_ne_one {u : G} (hu : C.IsPt u) : u ≠ 1 := by
  obtain ⟨g, rfl⟩ := hu
  intro h
  apply C.z_ne_one
  calc C.z = g⁻¹ * (g * C.z * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

theorem isPt_conj {u : G} (hu : C.IsPt u) (h : G) : C.IsPt (h * u * h⁻¹) := by
  obtain ⟨g, rfl⟩ := hu
  exact ⟨h * g, by group⟩

theorem isLn_conj {W : Subgroup G} (hW : C.IsLn W) (h : G) :
    C.IsLn (W.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨g, rfl⟩ := hW
  exact ⟨h * g, map_conj_map_conj _ _ _⟩

theorem comm_z_conj {g x : G} (h : (g * C.z * g⁻¹) * x = x * (g * C.z * g⁻¹)) :
    (g⁻¹ * x * g) * C.z = C.z * (g⁻¹ * x * g) := by
  calc g⁻¹ * x * g * C.z = g⁻¹ * (x * (g * C.z * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * C.z * g⁻¹) * x) * g := by rw [h]
    _ = C.z * (g⁻¹ * x * g) := by group

theorem exists_pull {g x : G} (h : (g * C.z * g⁻¹) * x = x * (g * C.z * g⁻¹)) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) :
    ∃ a ∈ P1, C.Φ1 a = g⁻¹ * x * g ∧ a * a = 1 ∧ a ≠ 1 := by
  obtain ⟨a, haP, ha⟩ := C.exists_of_comm_z (C.comm_z_conj h)
  refine ⟨a, haP, ha, ?_, ?_⟩
  · apply C.Φ1_inj (P1.mul_mem haP haP) P1.one_mem
    rw [C.Φ1_mul haP haP, ha, C.Φ1_one]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hx2]; group
  · intro h1
    apply hx1
    rw [h1, C.Φ1_one] at ha
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [← ha]; group

end Ctx

end CFSG.Quasithin.H13.F431.U42
