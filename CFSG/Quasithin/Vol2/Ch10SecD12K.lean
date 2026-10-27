module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_mem_inf_centralizer {V : Subgroup G} (hV : IsElemAbelian 2 V) {b v : G}
    (hb : b ^ 2 = 1) (hbN : b ∈ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) :
    b⁻¹ * v * b * v⁻¹ ∈ V ⊓ Subgroup.centralizer ({b} : Set G) := by
  have hbinv : b⁻¹ = b := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hb]
  have hp : b⁻¹ * v * b ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hbN) v).mp hv
    simpa using this
  have hvinv : v⁻¹ = v := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hV.2 v hv]
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb
  refine ⟨V.mul_mem hp (V.inv_mem hv), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hc := B2F.isElemAbelian_comm hV hp (V.inv_mem hv)
  calc b⁻¹ * v * b * v⁻¹ * b = (b⁻¹ * v * b * v⁻¹) * b := rfl
    _ = (v⁻¹ * (b⁻¹ * v * b)) * b := by rw [hc]
    _ = v⁻¹ * b⁻¹ * v * (b * b) := by group
    _ = v⁻¹ * b⁻¹ * v := by rw [hbb, mul_one]
    _ = v * b * v := by rw [hbinv, hvinv]
    _ = v * b * v⁻¹ := by rw [hvinv]
    _ = b * (b⁻¹ * v * b * v⁻¹) := by group

theorem false_of_isPGroup_sup {V1 W A : Subgroup G} (hV1 : IsElemAbelian 2 V1)
    (hW : IsElemAbelian 2 W) (hAW : A ≤ W) (hAN : A ≤ Subgroup.normalizer (V1 : Set G))
    (hUN : V1 ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hb : ∀ b ∈ A, b ≠ 1 →
      V1 ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.centralizer (A : Set G))
    (hCu : ∀ u ∈ V1 ⊓ Subgroup.centralizer (A : Set G), u ≠ 1 →
      W ⊓ Subgroup.centralizer ({u} : Set G) ≤ A)
    (hA1 : A ≠ ⊥) {v0 w0 : G} (hv0 : v0 ∈ V1) (hv0A : v0 ∉ Subgroup.centralizer (A : Set G))
    (hw0 : w0 ∈ W) (hw0A : w0 ∉ A) (hP : IsPGroup 2 ↥(V1 ⊔ W)) : False := by
  set U1 := V1 ⊓ Subgroup.centralizer (A : Set G) with hU1
  set Y := U1 ⊔ A with hY
  have hUA : U1 ≤ Subgroup.normalizer (A : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hprod : ∀ y ∈ Y, ∃ u ∈ U1, ∃ b ∈ A, u * b = y := by
    intro y hy
    have hy' : y ∈ ((U1 ⊔ A : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right U1 A hUA] at hy'
    obtain ⟨u, hu, b, hb, rfl⟩ := Set.mem_mul.mp hy'
    exact ⟨u, hu, b, hb, rfl⟩
  have hsqV : ∀ v ∈ V1, v ^ 2 = 1 := hV1.2
  have hsqW : ∀ w ∈ W, w ^ 2 = 1 := hW.2
  have hV1Y : ∀ v ∈ V1, ∀ y ∈ Y, v * y * v⁻¹ ∈ Y := by
    intro v hv y hy
    obtain ⟨u, hu, b, hbA, rfl⟩ := hprod y hy
    have hbN : b ∈ Subgroup.normalizer (V1 : Set G) := hAN hbA
    have he := commutator_mem_inf_centralizer hV1 (hsqW b (hAW hbA)) hbN hv
    have heU : b⁻¹ * v * b * v⁻¹ ∈ U1 := by
      by_cases hb1 : b = 1
      · subst hb1
        have : (1 : G)⁻¹ * v * 1 * v⁻¹ = 1 := by group
        rw [this]
        exact U1.one_mem
      · exact ⟨he.1, hb b hbA hb1 he⟩
    have hvu : v * u = u * v := B2F.isElemAbelian_comm hV1 hv hu.1
    have e : v * (u * b) * v⁻¹ = u * b * (b⁻¹ * v * b * v⁻¹) := by
      calc v * (u * b) * v⁻¹ = (v * u) * b * v⁻¹ := by group
        _ = (u * v) * b * v⁻¹ := by rw [hvu]
        _ = u * b * (b⁻¹ * v * b * v⁻¹) := by group
    rw [e]
    exact Y.mul_mem (Y.mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hbA))
      (Subgroup.mem_sup_left heU)
  have hWY : ∀ w ∈ W, ∀ y ∈ Y, w * y * w⁻¹ ∈ Y := by
    intro w hw y hy
    obtain ⟨u, hu, b, hbA, rfl⟩ := hprod y hy
    have hf := commutator_mem_inf_centralizer hW (hsqV u hu.1) (hUN hu) hw
    have hfA : u⁻¹ * w * u * w⁻¹ ∈ A := by
      by_cases hu1 : u = 1
      · subst hu1
        have : (1 : G)⁻¹ * w * 1 * w⁻¹ = 1 := by group
        rw [this]
        exact A.one_mem
      · exact hCu u hu hu1 hf
    have hwb : w * b = b * w := B2F.isElemAbelian_comm hW hw (hAW hbA)
    have hwb' : w * b * w⁻¹ = b := by rw [hwb]; group
    have e : w * (u * b) * w⁻¹ = u * (u⁻¹ * w * u * w⁻¹) * b := by
      calc w * (u * b) * w⁻¹ = (w * u * w⁻¹) * (w * b * w⁻¹) := by group
        _ = (w * u * w⁻¹) * b := by rw [hwb']
        _ = u * (u⁻¹ * w * u * w⁻¹) * b := by group
    rw [e]
    exact Y.mul_mem (Y.mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hfA))
      (Subgroup.mem_sup_right hbA)
  have hnorm : ∀ x : G, (∀ y ∈ Y, x * y * x⁻¹ ∈ Y) → (∀ y ∈ Y, x⁻¹ * y * x⁻¹⁻¹ ∈ Y) →
      x ∈ Subgroup.normalizer (Y : Set G) := by
    intro x h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨h1 y, fun hy => ?_⟩
    have := h2 _ hy
    simpa [mul_assoc] using this
  have hXY : V1 ⊔ W ≤ Subgroup.normalizer (Y : Set G) := by
    refine sup_le (fun v hv => hnorm v (hV1Y v hv) (hV1Y v⁻¹ (V1.inv_mem hv)))
      (fun w hw => hnorm w (hWY w hw) (hWY w⁻¹ (W.inv_mem hw)))
  have hYX : Y ≤ V1 ⊔ W := sup_le (inf_le_left.trans le_sup_left) (hAW.trans le_sup_right)
  have : (Y.subgroupOf (V1 ⊔ W)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXY
  have : Group.IsNilpotent ↥(V1 ⊔ W) := hP.isNilpotent
  have hH : Y.subgroupOf (V1 ⊔ W) ≠ ⊥ := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    intro hbot
    have : (⟨a, hAW.trans le_sup_right ha⟩ : ↥(V1 ⊔ W)) ∈ Y.subgroupOf (V1 ⊔ W) :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right ha)
    rw [hbot, Subgroup.mem_bot] at this
    exact ha1 (Subtype.ext (show a = 1 from congrArg Subtype.val this))
  obtain ⟨⟨⟨y0, hy0X⟩, hy0Y, hy0Z⟩, hy01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH)
  have hy01' : y0 ≠ 1 := fun h1 => hy01 (Subtype.ext (Subtype.ext h1))
  have hcomm : ∀ x ∈ V1 ⊔ W, x * y0 = y0 * x := by
    intro x hx
    have := Subgroup.mem_center_iff.mp hy0Z ⟨x, hx⟩
    exact congrArg Subtype.val this
  obtain ⟨u, hu, b, hbA, rfl⟩ := hprod y0 (Subgroup.mem_subgroupOf.mp hy0Y)
  have hb1 : b = 1 := by
    by_contra hb1
    apply hv0A
    refine hb b hbA hb1 ⟨hv0, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hcomm v0 (Subgroup.mem_sup_left hv0)
    have hvu : v0 * u = u * v0 := B2F.isElemAbelian_comm hV1 hv0 hu.1
    have h2 : u * (v0 * b) = u * (b * v0) := by
      calc u * (v0 * b) = v0 * (u * b) := by rw [← mul_assoc, ← hvu, mul_assoc]
        _ = u * b * v0 := h1
        _ = u * (b * v0) := by group
    exact mul_left_cancel h2
  subst hb1
  rw [mul_one] at hy01'
  apply hw0A
  refine hCu u hu hy01' ⟨hw0, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have := hcomm w0 (Subgroup.mem_sup_right hw0)
  rw [mul_one] at this
  exact this

end CFSG.Quasithin.Vol2.Ch10.SecD
