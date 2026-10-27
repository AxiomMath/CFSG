module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Ag2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocSyl

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem mem_P1_xY : xY ∈ P1 := B0_le_P1 (T_le_B0 xY_mem_T)

theorem mem_P2_xY : xY ∈ P2 := B0_le_P2 (T_le_B0 xY_mem_T)

theorem Vsub_le_P2 : Vsub ≤ P2 :=
  (Vsub_le_T).trans (T_le_B0.trans B0_le_P2)

theorem Vsub_le_P1 : Vsub ≤ P1 := (Vsub_le_T).trans T_le_P1

structure Ctx (G : Type) [Group G] where
  φ1 : ↥P1 →* G
  φ2 : ↥P2 →* G
  inj1 : Function.Injective φ1
  inj2 : Function.Injective φ2
  agree : ∀ (b : Y) (h1 : b ∈ P1) (h2 : b ∈ P2), φ1 ⟨b, h1⟩ = φ2 ⟨b, h2⟩
  cent : ∀ g : G, g * φ1 ⟨xY, mem_P1_xY⟩ = φ1 ⟨xY, mem_P1_xY⟩ * g → g ∈ φ1.range
  norm : ∀ g : G, g ∈ Subgroup.normalizer
    ((Subgroup.map φ2 (Vsub.subgroupOf P2) : Subgroup G) : Set G) → g ∈ φ2.range

namespace Ctx

variable {G : Type} [Group G] (C : Ctx G)

open Classical in
@[expose] noncomputable def Φ1 (y : Y) : G := if h : y ∈ P1 then C.φ1 ⟨y, h⟩ else 1

open Classical in
@[expose] noncomputable def Φ2 (y : Y) : G := if h : y ∈ P2 then C.φ2 ⟨y, h⟩ else 1

theorem Φ1_of_mem {y : Y} (h : y ∈ P1) : C.Φ1 y = C.φ1 ⟨y, h⟩ := by simp [Φ1, h]

theorem Φ2_of_mem {y : Y} (h : y ∈ P2) : C.Φ2 y = C.φ2 ⟨y, h⟩ := by simp [Φ2, h]

theorem Φ1_mul {x y : Y} (hx : x ∈ P1) (hy : y ∈ P1) : C.Φ1 (x * y) = C.Φ1 x * C.Φ1 y := by
  rw [C.Φ1_of_mem (P1.mul_mem hx hy), C.Φ1_of_mem hx, C.Φ1_of_mem hy, ← map_mul]
  rfl

theorem Φ2_mul {x y : Y} (hx : x ∈ P2) (hy : y ∈ P2) : C.Φ2 (x * y) = C.Φ2 x * C.Φ2 y := by
  rw [C.Φ2_of_mem (P2.mul_mem hx hy), C.Φ2_of_mem hx, C.Φ2_of_mem hy, ← map_mul]
  rfl

theorem Φ1_one : C.Φ1 1 = 1 := by
  rw [C.Φ1_of_mem P1.one_mem]
  exact map_one _

theorem Φ2_one : C.Φ2 1 = 1 := by
  rw [C.Φ2_of_mem P2.one_mem]
  exact map_one _

theorem Φ1_inv {x : Y} (hx : x ∈ P1) : C.Φ1 x⁻¹ = (C.Φ1 x)⁻¹ := by
  rw [C.Φ1_of_mem (P1.inv_mem hx), C.Φ1_of_mem hx, ← map_inv]
  rfl

theorem Φ2_inv {x : Y} (hx : x ∈ P2) : C.Φ2 x⁻¹ = (C.Φ2 x)⁻¹ := by
  rw [C.Φ2_of_mem (P2.inv_mem hx), C.Φ2_of_mem hx, ← map_inv]
  rfl

theorem Φ1_inj {x y : Y} (hx : x ∈ P1) (hy : y ∈ P1) (h : C.Φ1 x = C.Φ1 y) : x = y := by
  rw [C.Φ1_of_mem hx, C.Φ1_of_mem hy] at h
  exact congrArg Subtype.val (C.inj1 h)

theorem Φ2_inj {x y : Y} (hx : x ∈ P2) (hy : y ∈ P2) (h : C.Φ2 x = C.Φ2 y) : x = y := by
  rw [C.Φ2_of_mem hx, C.Φ2_of_mem hy] at h
  exact congrArg Subtype.val (C.inj2 h)

theorem Φ1_eq_Φ2 {b : Y} (hb : b ∈ B0) : C.Φ1 b = C.Φ2 b := by
  rw [C.Φ1_of_mem (B0_le_P1 hb), C.Φ2_of_mem (B0_le_P2 hb)]
  exact C.agree b _ _

theorem Φ1_conj {m a : Y} (hm : m ∈ P1) (ha : a ∈ P1) :
    C.Φ1 (m * a * m⁻¹) = C.Φ1 m * C.Φ1 a * (C.Φ1 m)⁻¹ := by
  rw [C.Φ1_mul (P1.mul_mem hm ha) (P1.inv_mem hm), C.Φ1_mul hm ha, C.Φ1_inv hm]

theorem Φ2_conj {m a : Y} (hm : m ∈ P2) (ha : a ∈ P2) :
    C.Φ2 (m * a * m⁻¹) = C.Φ2 m * C.Φ2 a * (C.Φ2 m)⁻¹ := by
  rw [C.Φ2_mul (P2.mul_mem hm ha) (P2.inv_mem hm), C.Φ2_mul hm ha, C.Φ2_inv hm]

@[expose] noncomputable def z : G := C.Φ1 xY

@[expose] noncomputable def V2 : Subgroup G := Subgroup.map C.φ2 (Vsub.subgroupOf P2)

theorem z_def : C.z = C.Φ1 xY := rfl

theorem mem_V2 {g : G} : g ∈ C.V2 ↔ ∃ v ∈ Vsub, C.Φ2 v = g := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, C.Φ2_of_mem x.2⟩
  · rintro ⟨v, hv, rfl⟩
    have hvP : v ∈ P2 := B0_le_P2 (T_le_B0 (Vsub_le_T hv))
    exact ⟨⟨v, hvP⟩, hv, (C.Φ2_of_mem hvP).symm⟩

theorem Φ2_mem_V2 {v : Y} (hv : v ∈ Vsub) : C.Φ2 v ∈ C.V2 := C.mem_V2.2 ⟨v, hv, rfl⟩

theorem Φ1_mem_V2 {v : Y} (hv : v ∈ Vsub) : C.Φ1 v ∈ C.V2 := by
  rw [C.Φ1_eq_Φ2 (T_le_B0 (Vsub_le_T hv))]
  exact C.Φ2_mem_V2 hv

theorem z_eq : C.z = C.Φ2 xY := C.Φ1_eq_Φ2 (T_le_B0 xY_mem_T)

theorem z_mem_V2 : C.z ∈ C.V2 := by
  rw [C.z_eq, ← sY_zero]
  exact C.Φ2_mem_V2 (sY_mem_Vsub zero_mem_L0S)

theorem V2_comm {a b : G} (ha : a ∈ C.V2) (hb : b ∈ C.V2) : a * b = b * a := by
  obtain ⟨v, hv, rfl⟩ := C.mem_V2.1 ha
  obtain ⟨w, hw, rfl⟩ := C.mem_V2.1 hb
  rw [← C.Φ2_mul (Vsub_le_P2 hv) (Vsub_le_P2 hw), ← C.Φ2_mul (Vsub_le_P2 hw)
    (Vsub_le_P2 hv), Vsub_comm hv hw]

theorem V2_sq {a : G} (ha : a ∈ C.V2) : a * a = 1 := by
  obtain ⟨v, hv, rfl⟩ := C.mem_V2.1 ha
  rw [← C.Φ2_mul (Vsub_le_P2 hv) (Vsub_le_P2 hv), Vsub_sq hv, C.Φ2_one]

theorem card_V2 : Nat.card C.V2 = Nat.card Vsub := by
  rw [V2, Subgroup.card_map_of_injective C.inj2]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Vsub_le_P2).toEquiv

end Ctx

end CFSG.Quasithin.H13.F431.U42
